module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgIso
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCore
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieL3
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCfgForward

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Transport

variable {S T : Type} [Group S] [Group T]

theorem CfgSEps.map [Finite S] [Finite T] {A : Subgroup (MulAut S)} {σ : MulAut S}
    {K : Subgroup S} (h : CfgSEps S A σ K) (e : S ≃* T) :
    CfgSEps T (A.map (MulAut.congr e).toMonoidHom) (MulAut.congr e σ) (K.map e.toMonoidHom) := by
  have hfix := autFix_congr e σ
  refine
    { isE27 := h.isE27.map (MulAut.congr e)
      mem := Subgroup.mem_map_of_mem _ h.mem
      ne_one := fun h1 => h.ne_one ((MulAut.congr e).injective (by rw [h1, map_one]))
      le_autFix := by rw [hfix]; exact Subgroup.map_mono h.le_autFix
      isSubnormal := ?_
      isPerfect := ?_
      map_mem := ?_
      isType := ?_
      faithful := ?_ }
  · rw [hfix, ← map_subgroupOf_equivMap]
    exact h.isSubnormal.map (MulEquiv.surjective _)
  · haveI := h.isPerfect
    exact Group.IsPerfect.map _
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨a k, h.map_mem a ha k hk, ?_⟩
    change e (a k) = e (a (e.symm (e k)))
    rw [MulEquiv.symm_apply_apply]
  · exact isTypeEps_of_mulEquiv
      (quotPCoreTwoCongr (K.equivMapOfInjective e.toMonoidHom e.injective)).symm h.isType
  · rintro _ ⟨a, ha, rfl⟩ hK
    have hinj : Function.Injective (e.toMonoidHom.comp K.subtype) :=
      e.injective.comp K.subtype_injective
    have ha' : a ∈ Subgroup.zpowers σ := by
      refine h.faithful a ha fun k hk => ?_
      have h1 := hK (e k) ⟨k, hk, rfl⟩
      have h2 : ((MulAut.congr e).toMonoidHom a) (e k) * (e k)⁻¹ =
          e.toMonoidHom (a k * k⁻¹) := by
        change e (a (e.symm (e k))) * (e k)⁻¹ = e (a k * k⁻¹)
        rw [MulEquiv.symm_apply_apply, map_mul, map_inv]
      rw [h2] at h1
      exact (map_mem_pCoreOf_map_iff 2 e.toMonoidHom hinj
        (Subgroup.mul_mem _ (h.map_mem a ha k hk) (Subgroup.inv_mem _ hk))).mp h1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    change (MulAut.congr e).toMonoidHom (σ ^ m) ∈ _
    rw [map_zpow]
    exact Subgroup.zpow_mem_zpowers _ m

theorem NoCfgSEps.of_mulEquiv [Finite S] [Finite T] (e : S ≃* T) (h : NoCfgSEps T) :
    NoCfgSEps S :=
  fun _ _ _ hc => h _ _ _ (hc.map e)

end Transport

section Component

variable {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)} {σ : MulAut S}
  {K : Subgroup S}

theorem CfgSEps.pow_three (hc : CfgSEps S A σ K) : σ ^ 3 = 1 :=
  hc.isE27.1.2 σ hc.mem

theorem CfgSEps.center_quot (hc : CfgSEps S A σ K) :
    Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ :=
  center_eq_bot_of_isTypeEps hc.isType

theorem CfgSEps.nontrivial (hc : CfgSEps S A σ K) : Nontrivial K := by
  have h1 := le_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)
  have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card K :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

theorem CfgSEps.eq_of_le_quasisimple (hc : CfgSEps S A σ K) {N : Subgroup S} (hKN : K ≤ N)
    (hNC : N ≤ autFix σ) (hN : IsQuasisimple N) : K = N :=
  Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hKN hN hc.isPerfect hc.nontrivial
    (RonanK429H.isSubnormal_subgroupOf_of_le hNC hKN hc.isSubnormal)

theorem CfgSEps.false_of_le_quasisimple_central (hc : CfgSEps S A σ K) {N : Subgroup S}
    (hKN : K ≤ N) (hNC : N ≤ autFix σ) (hN : IsQuasisimple N) {z : S} (hzN : z ∈ N)
    (hz : ∀ n ∈ N, n * z = z * n) (hz3 : orderOf z = 3) : False := by
  have hKeq := hc.eq_of_le_quasisimple hKN hNC hN
  subst hKeq
  set k : K := ⟨z, hzN⟩ with hk
  have hkc : ∀ k' : K, k * k' = k' * k := fun k' =>
    Subtype.ext (hz k' k'.2).symm
  have hko : orderOf k = 3 := by
    rw [← hz3]
    exact Subgroup.orderOf_mk z hzN
  have hcen : (QuotientGroup.mk' (CFSG.pCore 2 K) k : K ⧸ CFSG.pCore 2 K) ∈
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
    rw [← map_mul, ← map_mul, hkc k']
  rw [hc.center_quot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨_, hcen⟩
  have hn' : k ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hd : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  rw [hko] at hd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)) hd

theorem CfgSEps.isTypeEpsCube_of_le (hc : CfgSEps S A σ K) {N : Subgroup S} (hKN : K ≤ N)
    (hNC : N ≤ autFix σ) (hN : IsQuasisimple N) (hZ : Subgroup.center N = ⊥) :
    IsTypeEpsCube N := by
  have hKeq := hc.eq_of_le_quasisimple hKN hNC hN
  subst hKeq
  have hO2 : CFSG.pCore 2 K = ⊥ :=
    eq_bot_iff.mpr (hZ ▸ pCore_two_le_center hN)
  have e : K ⧸ CFSG.pCore 2 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  exact isTypeEpsCube_of_mulEquiv e.symm (isTypeEpsCube_of_cfgSEps hc)

theorem CfgSEps.le_perfectResidual (hc : CfgSEps S A σ K) :
    K ≤ inSubgroup perfectResidual (autFix σ) :=
  le_inSubgroup_perfectResidual hc.isPerfect hc.le_autFix

end Component

section Orders

theorem card_of_isTypeEpsCube_prime {X : Type} [Group X] (h : IsTypeEpsCube X) :
    ∃ p g : ℕ, p.Prime ∧ p ≠ 3 ∧ 1 ≤ g ∧
      ((p ^ g % 3 = 2 ∧ Nat.card X = (p ^ g) ^ 9 * (((p ^ g) ^ 6 - 1) * ((p ^ g) ^ 9 - 1))) ∨
       (p ^ g % 3 = 1 ∧ Nat.card X = (p ^ g) ^ 9 * (((p ^ g) ^ 6 - 1) * ((p ^ g) ^ 9 + 1)))) := by
  obtain ⟨p, f, hp, hp3, hf, ⟨g, rfl⟩, ⟨hq, ⟨ψ⟩⟩ | ⟨hq, -, ⟨ψ⟩⟩⟩ := h
  · have hpp : p.Prime := hp.out
    have hg : 1 ≤ g := by omega
    have hqr : p ^ (3 * g) = (p ^ g) ^ 3 := by rw [← pow_mul, mul_comm]
    have hr3 : (p ^ g) % 3 = 2 := by rw [← cube_mod_three, ← hqr, hq]
    have hc := KS14.card_projSL_three_mul_gcd (GaloisField p (3 * g))
    rw [GaloisField.card p (3 * g) (by omega), ← Nat.card_congr ψ.toEquiv, hqr] at hc
    have hgcd : Nat.gcd 3 ((p ^ g) ^ 3 - 1) = 1 := by
      have h1 : 1 ≤ (p ^ g) ^ 3 := Nat.one_le_pow _ _ (pow_pos hpp.pos _)
      have h2 : ((p ^ g) ^ 3 - 1) % 3 = 1 := by
        have := cube_mod_three (p ^ g)
        omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
    rw [hgcd, mul_one] at hc
    refine ⟨p, g, hpp, hp3, hg, Or.inl ⟨hr3, ?_⟩⟩
    rw [hc]
    ring_nf
  · have hpp : p.Prime := hp.out
    have hg : 1 ≤ g := by omega
    have hqr : p ^ (3 * g) = (p ^ g) ^ 3 := by rw [← pow_mul, mul_comm]
    have hr3 : (p ^ g) % 3 = 1 := by rw [← cube_mod_three, ← hqr, hq]
    have hc := KS14.card_projSU_three_mul_gcd p (3 * g) hf
    rw [← Nat.card_congr ψ.toEquiv, hqr] at hc
    have hgcd : Nat.gcd 3 ((p ^ g) ^ 3 + 1) = 1 := by
      have h2 : ((p ^ g) ^ 3 + 1) % 3 = 2 := by
        have := cube_mod_three (p ^ g)
        omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
    rw [hgcd, mul_one] at hc
    refine ⟨p, g, hpp, hp3, hg, Or.inr ⟨hr3, ?_⟩⟩
    rw [hc]
    ring_nf

theorem eq_of_two_pow_mul_odd {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have key : ∀ {a b u v : ℕ}, Odd u → Odd v → 2 ^ a * u = 2 ^ b * v → a ≤ b := by
    intro a b u v hu hv h
    by_contra hab
    push Not at hab
    obtain ⟨c, rfl⟩ : ∃ c, a = b + c + 1 := ⟨a - b - 1, by omega⟩
    have h' : 2 ^ b * (2 ^ (c + 1) * u) = 2 ^ b * v := by
      rw [← h, ← mul_assoc, ← pow_add]
      ring_nf
    have hv' : v = 2 ^ (c + 1) * u := (Nat.eq_of_mul_eq_mul_left (by positivity) h').symm
    rw [hv', pow_succ] at hv
    exact (Nat.not_even_iff_odd.mpr hv) (by
      rw [mul_comm (2 ^ c) 2, mul_assoc]
      exact even_two_mul _)
  have hab := key hu hv h
  have hba := key hv hu h.symm
  have hab' : a = b := le_antisymm hab hba
  subst hab'
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem two_pow_le_of_dvd_cube_odd_minus {r a : ℕ} (hr : Odd r) (h2 : 2 ≤ r)
    (h : 2 ^ a ∣ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1))) : 2 ^ a ≤ (r ^ 2 - 1) * (r + 1) := by
  have e6 : r ^ 6 - 1 = (r ^ 2 - 1) * (r ^ 4 + r ^ 2 + 1) := by
    have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h6]
    ring
  have e9 : r ^ 9 - 1 =
      (r - 1) * (r ^ 8 + r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) := by
    have h9 : 1 ≤ r ^ 9 := Nat.one_le_pow _ _ (by omega)
    zify [h9, (by omega : 1 ≤ r)]
    ring
  have hodd1 : Odd (r ^ 4 + r ^ 2 + 1) := (hr.pow.add_odd hr.pow).add_one
  have hodd2 : Odd (r ^ 8 + r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) :=
    ((((((((hr.pow.add_odd hr.pow).add_odd hr.pow).add_odd hr.pow).add_odd hr.pow).add_odd
      hr.pow).add_odd hr.pow).add_odd hr).add_one)
  have hcop : Nat.Coprime (2 ^ a) (r ^ 9 * ((r ^ 4 + r ^ 2 + 1) *
      (r ^ 8 + r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1))) := by
    refine Nat.Coprime.pow_left a ?_
    rw [Nat.coprime_two_left]
    exact hr.pow.mul (hodd1.mul hodd2)
  have h' : 2 ^ a ∣ (r ^ 2 - 1) * (r - 1) * (r ^ 9 * ((r ^ 4 + r ^ 2 + 1) *
      (r ^ 8 + r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1))) := by
    have : r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) = (r ^ 2 - 1) * (r - 1) * (r ^ 9 *
        ((r ^ 4 + r ^ 2 + 1) * (r ^ 8 + r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1))) := by
      rw [e6, e9]
      ring
    rwa [this] at h
  have h'' := hcop.dvd_of_dvd_mul_right h'
  have hpos : 0 < (r ^ 2 - 1) * (r - 1) := by
    have : 4 ≤ r ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  exact (Nat.le_of_dvd hpos h'').trans (Nat.mul_le_mul_left _ (by omega))

theorem two_pow_le_of_dvd_cube_odd_plus {r a : ℕ} (hr : Odd r) (h2 : 2 ≤ r)
    (h : 2 ^ a ∣ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1))) : 2 ^ a ≤ (r ^ 2 - 1) * (r + 1) := by
  have e6 : r ^ 6 - 1 = (r ^ 2 - 1) * (r ^ 4 + r ^ 2 + 1) := by
    have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h6]
    ring
  set c : ℕ := (r - 1) * (r ^ 7 + r ^ 5 + r ^ 3 + r) + 1 with hc
  have e9 : r ^ 9 + 1 = (r + 1) * c := by
    rw [hc]
    zify [(by omega : 1 ≤ r)]
    ring
  have hodd1 : Odd (r ^ 4 + r ^ 2 + 1) := (hr.pow.add_odd hr.pow).add_one
  have hodd2 : Odd c := by
    rw [hc]
    refine Even.add_one (Even.mul_right ?_ _)
    obtain ⟨k, hk⟩ := hr
    exact ⟨k, by omega⟩
  have hcop : Nat.Coprime (2 ^ a) (r ^ 9 * ((r ^ 4 + r ^ 2 + 1) * c)) := by
    refine Nat.Coprime.pow_left a ?_
    rw [Nat.coprime_two_left]
    exact hr.pow.mul (hodd1.mul hodd2)
  have h' : 2 ^ a ∣ (r ^ 2 - 1) * (r + 1) * (r ^ 9 * ((r ^ 4 + r ^ 2 + 1) * c)) := by
    have : r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1)) =
        (r ^ 2 - 1) * (r + 1) * (r ^ 9 * ((r ^ 4 + r ^ 2 + 1) * c)) := by
      rw [e6, e9]
      ring
    rwa [this] at h
  have h'' := hcop.dvd_of_dvd_mul_right h'
  have hpos : 0 < (r ^ 2 - 1) * (r + 1) := by
    have : 4 ≤ r ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  exact Nat.le_of_dvd hpos h''

theorem not_isTypeEpsCube_of_two_adic {X : Type} [Group X] {a u : ℕ} (hu : Odd u)
    (hX : Nat.card X = 2 ^ a * u) (hsmall : u < 2 ^ (5 * a))
    (hne : ∀ g : ℕ, 1 ≤ g → a = 9 * g →
      u ≠ (2 ^ (6 * g) - 1) * (2 ^ (9 * g) - 1) ∧ u ≠ (2 ^ (6 * g) - 1) * (2 ^ (9 * g) + 1)) :
    ¬ IsTypeEpsCube X := by
  intro h
  obtain ⟨p, g, hp, hp3, hg, hcase⟩ := card_of_isTypeEpsCube_prime h
  by_cases hp2 : p = 2
  · subst hp2
    have h6 : (2 ^ g) ^ 6 = 2 ^ (6 * g) := by rw [← pow_mul, mul_comm]
    have h9 : (2 ^ g) ^ 9 = 2 ^ (9 * g) := by rw [← pow_mul, mul_comm]
    have hodd6 : Odd (2 ^ (6 * g) - 1) := by
      have : 2 ≤ 2 ^ (6 * g) := Nat.le_self_pow (by omega) 2
      exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have hoddm : Odd (2 ^ (9 * g) - 1) := by
      have : 2 ≤ 2 ^ (9 * g) := Nat.le_self_pow (by omega) 2
      exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have hoddp : Odd (2 ^ (9 * g) + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    rcases hcase with ⟨-, hc⟩ | ⟨-, hc⟩
    · rw [h6, h9, hX] at hc
      obtain ⟨ha, hu'⟩ := eq_of_two_pow_mul_odd hu (hodd6.mul hoddm) hc
      exact (hne g hg ha).1 hu'
    · rw [h6, h9, hX] at hc
      obtain ⟨ha, hu'⟩ := eq_of_two_pow_mul_odd hu (hodd6.mul hoddp) hc
      exact (hne g hg ha).2 hu'
  ·
    set r := p ^ g with hr
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hrodd : Odd r := hpodd.pow
    have hr2 : 2 ≤ r := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have hr5 : 5 ≤ r := by
      have hr3 : r % 3 ≠ 0 := by rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      obtain ⟨k, hk⟩ := hrodd
      omega
    have hdvd : 2 ^ a ∣ Nat.card X := hX ▸ dvd_mul_right _ _
    have h2a : 2 ^ a ≤ (r ^ 2 - 1) * (r + 1) := by
      rcases hcase with ⟨-, hc⟩ | ⟨-, hc⟩
      · exact two_pow_le_of_dvd_cube_odd_minus hrodd hr2 (hc ▸ hdvd)
      · exact two_pow_le_of_dvd_cube_odd_plus hrodd hr2 (hc ▸ hdvd)
    have hlt : Nat.card X < (2 ^ a) ^ 6 := by
      rw [hX]
      calc 2 ^ a * u < 2 ^ a * 2 ^ (5 * a) := Nat.mul_lt_mul_of_pos_left hsmall (by positivity)
        _ = (2 ^ a) ^ 6 := by rw [← pow_mul, ← pow_add]; ring_nf
    have h2r : 2 ^ a ≤ 2 * r ^ 3 := by
      refine h2a.trans ?_
      have : r ^ 2 - 1 ≤ r ^ 2 := Nat.sub_le _ _
      nlinarith
    have hle6 : (2 ^ a) ^ 6 ≤ 64 * r ^ 18 := by
      calc (2 ^ a) ^ 6 ≤ (2 * r ^ 3) ^ 6 := Nat.pow_le_pow_left h2r 6
        _ = 64 * r ^ 18 := by ring
    have hge : 64 * r ^ 18 ≤ Nat.card X := by
      have h6 : 128 ≤ r ^ 6 - 1 := by
        have : 5 ^ 6 ≤ r ^ 6 := Nat.pow_le_pow_left hr5 6
        omega
      have h9 : r ^ 9 ≤ 2 * (r ^ 9 - 1) := by
        have : 2 ≤ r ^ 9 := le_trans hr2 (Nat.le_self_pow (by norm_num) r)
        omega
      have hmin : r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) ≤ Nat.card X := by
        rcases hcase with ⟨-, hc⟩ | ⟨-, hc⟩
        · rw [hc]
        · rw [hc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      calc 64 * r ^ 18 = r ^ 9 * (64 * r ^ 9) := by ring
        _ ≤ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          calc 64 * r ^ 9 ≤ 64 * (2 * (r ^ 9 - 1)) := Nat.mul_le_mul_left _ h9
            _ = 128 * (r ^ 9 - 1) := by ring
            _ ≤ (r ^ 6 - 1) * (r ^ 9 - 1) := Nat.mul_le_mul_right _ h6
        _ ≤ Nat.card X := hmin
    omega

theorem card_SL_two (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 2)]
  simp

theorem not_isTypeEpsCube_of_card_sl2_even {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1)) : ¬ IsTypeEpsCube X := by
  have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
  refine not_isTypeEpsCube_of_two_adic (a := n) (u := (2 ^ n) ^ 2 - 1) ?_ hX ?_ ?_
  · exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩,
      by norm_num⟩) odd_one
  · calc (2 ^ n) ^ 2 - 1 < (2 ^ n) ^ 2 := by omega
      _ = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
      _ < 2 ^ (5 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rintro g hg rfl
    set x := 2 ^ (3 * g) with hx
    have hx8 : 8 ≤ x := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ x := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : (2 ^ (9 * g)) ^ 2 = x ^ 6 := by rw [hx, ← pow_mul, ← pow_mul]; ring_nf
    have e6 : 2 ^ (6 * g) = x ^ 2 := by rw [hx, ← pow_mul]; ring_nf
    have e9 : 2 ^ (9 * g) = x ^ 3 := by rw [hx, ← pow_mul]; ring_nf
    rw [e1, e6, e9]
    have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hx3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hx6 : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hlt : (x ^ 2 - 1) * (x ^ 3 + 1) < x ^ 6 - 1 := by
      zify [hx2, hx6]
      nlinarith [hx8]
    have hlt' : (x ^ 2 - 1) * (x ^ 3 - 1) < x ^ 6 - 1 :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hlt
    exact ⟨hlt'.ne', hlt.ne'⟩

end Orders

theorem false_of_isTypeEps_of_isoLThreePi {X : Type} [Group X] (h1 : IsTypeEps X) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (h2 : IsoLThreePi X p e) : False := by
  obtain ⟨E, hE, hE9⟩ := Sec15.exists_e9_of_isLThreePi ⟨p, e, inferInstance, he, h2⟩
  obtain ⟨p', f, hp', -, hf, ⟨hq, ⟨ψ⟩⟩ | ⟨hq, -, ⟨ψ⟩⟩⟩ := h1
  · haveI : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
    have hcyc := isCyclic_sylow_three_of_mulEquiv_projSL
      (by rw [GaloisField.card p' f (by omega)]; exact hq) ψ
    exact RonanK429Lie.false_of_e9_of_isCyclic_sylow hcyc hE.2 hE9
  · haveI : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
    have hcyc := isCyclic_sylow_three_of_mulEquiv_projSU (by omega) hq ψ
    exact RonanK429Lie.false_of_e9_of_isCyclic_sylow hcyc hE.2 hE9

end CFSG.RankThree.PartTwo.Sec4.RonanEps
