module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalFrob

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem closure_le_centralizer {S : Set G} {z : G} (h : ∀ s ∈ S, s * z = z * s) :
    Subgroup.closure S ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  intro s hs
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact (h s hs).symm

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem edgeTransitive_of_locTr {M : Subgroup G} (hM : ∀ v, LocTr Γ M v) :
    EdgeTransitive Γ M := by
  intro u v u' v' huv hu'v'
  obtain ⟨p⟩ := F.isTree.connected.preconnected u u'
  have key : ∀ (a b a' b' : V), Γ.Adj a b → Γ.Adj a' b' → (∃ g ∈ M, g • a = a') →
      ∃ g ∈ M, g • a = a' ∧ g • b = b' := by
    rintro a b a' b' hab ha'b' ⟨g, hgM, hg⟩
    have h1 : Γ.Adj a' (g • b) := by
      have := (F.adj_smul g a b).2 hab
      rwa [hg] at this
    obtain ⟨k, hk, hka, hkb⟩ := hM a' _ _ h1 ha'b'
    exact ⟨k * g, M.mul_mem hk hgM, by rw [mul_smul, hg, hka], by rw [mul_smul, hkb]⟩
  rcases Nat.even_or_odd p.length with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨g, hgM, hg⟩ := exists_mem_smul_of_walk hM n p (by omega)
    obtain ⟨g', hg'M, h1, h2⟩ := key u v u' v' huv hu'v' ⟨g, hgM, hg⟩
    exact ⟨g', hg'M, Or.inl ⟨h1, h2⟩⟩
  · obtain ⟨g, hgM, hg⟩ := exists_mem_smul_of_walk hM (n + 1) (p.concat hu'v') (by
      rw [SimpleGraph.Walk.length_concat]; omega)
    have hg' : g • u = v' := by simpa using hg
    obtain ⟨g', hg'M, h1, h2⟩ := key u v v' u' huv hu'v'.symm ⟨g, hgM, hg'⟩
    exact ⟨g', hg'M, Or.inr ⟨h1, h2⟩⟩

theorem locTr_of_pow {M : Subgroup G} {v : V} {y : G} (hyM : y ∈ M)
    (hy : y ∈ MulAction.stabilizer G v) (hyo : orderOf y = Fan86.valence Γ v) : LocTr Γ M v := by
  intro p q hp hq
  obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hy hyo hp hq
  exact ⟨y ^ i, M.pow_mem hyM i,
    MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G v).pow_mem hy i), hi⟩

theorem eq_one_of_locTr_centralizer {z : G} {u w : V} (huw : Γ.Adj u w) (hzu : z • u = u)
    (hzw : z • w = w) (hu : LocTr Γ (Subgroup.centralizer ({z} : Set G)) u)
    (hw : LocTr Γ (Subgroup.centralizer ({z} : Set G)) w) : z = 1 := by
  have hET := F.edgeTransitive_of_locTr (F.locTr_all huw hu hw)
  have hN : EdgeTransitive Γ
      (Subgroup.normalizer ((Subgroup.closure ({z} : Set G) : Subgroup G) : Set G)) := by
    intro a b a' b' hab hab'
    obtain ⟨h, hh, hr⟩ := hET a b a' b' hab hab'
    refine ⟨h, ?_, hr⟩
    have := Subgroup.centralizer_le_normalizer
      ((Subgroup.closure ({z} : Set G) : Subgroup G) : Set G)
    rw [Subgroup.centralizer_closure] at this
    exact this hh
  have hle : Subgroup.closure ({z} : Set G) ≤
      MulAction.stabilizer G u ⊓ MulAction.stabilizer G w := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact ⟨MulAction.mem_stabilizer_iff.2 hzu, MulAction.mem_stabilizer_iff.2 hzw⟩
  have hbot := F.eq_bot_of_edgeTransitive huw (U := Subgroup.closure ({z} : Set G))
    (fun g hg => ⟨MulAction.mem_stabilizer_iff.1 (hle hg).1,
      MulAction.mem_stabilizer_iff.1 (hle hg).2⟩) hN
  have hz : z ∈ Subgroup.closure ({z} : Set G) := Subgroup.subset_closure rfl
  rw [hbot] at hz
  exact Subgroup.mem_bot.1 hz

theorem pclosed_of_central {v : V}
    (h : ∀ x ∈ MulAction.stabilizer G v, orderOf x = Fan86.valence Γ v →
      ∀ k ∈ nbrStab Γ G v, x * k = k * x) : PClosed Γ G v := by
  intro x hx hxo g hg
  obtain ⟨i, k, hk, hgx⟩ := F.conj_mem_pow_mul_nbrStab hx hxo hg
  have hp := F.valence_isPrime v
  have hodd : Fan86.valence Γ v ≠ 2 := by
    have h35 : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
    omega
  have hxp : x ^ Fan86.valence Γ v = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hcomm : Commute (x ^ i) k := (show Commute x k from h x hx hxo k hk).pow_left i
  have hkp : k ^ Fan86.valence Γ v = 1 := by
    have h1 : (g * x * g⁻¹) ^ Fan86.valence Γ v = 1 := by
      rw [conj_pow, hxp]
      group
    rw [hgx, hcomm.mul_pow, ← pow_mul, mul_comm i, pow_mul, hxp, one_pow, one_mul] at h1
    exact h1
  have hk1 : k = 1 := by
    obtain ⟨n, hn⟩ := F.nbrStab_isPGroup v ⟨k, hk⟩
    have h2 : k ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have hcop : Nat.Coprime (2 ^ n) (Fan86.valence Γ v) :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hodd))
    have := pow_gcd_eq_one.2 ⟨h2, hkp⟩
    rwa [hcop, pow_one] at this
  rw [hgx, hk1, mul_one]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i

end FanTree

end CFSG.Quasithin.Fan86
