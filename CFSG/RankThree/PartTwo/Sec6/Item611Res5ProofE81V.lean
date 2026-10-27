module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL9Lift
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43Cent

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res611Res5

theorem four_le_card_sq_eq_one {B : Type*} [CommGroup B] [Finite B] (hB : IsPGroup 2 B)
    (hnc : ¬ IsCyclic B) : 4 ≤ Nat.card {x : B // x ^ 2 = 1} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite B
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (G := B)
    ⟨_, Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite, Monoid.pow_exponent_eq_one⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hB) g
  have hexp : Monoid.exponent B = 2 ^ k := hg ▸ hk
  have hgB : Subgroup.zpowers g ≠ ⊤ := by
    intro h
    apply hnc
    rw [IsCyclic.iff_exponent_eq_card, ← hg, ← Nat.card_zpowers, h, Subgroup.card_top]
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hgB
    rw [eq_top_iff]
    intro x _
    have hx : x ^ Monoid.exponent B = 1 := Monoid.pow_exponent_eq_one x
    rw [hexp, pow_zero, pow_one] at hx
    rw [hx]
    exact Subgroup.one_mem _
  set Q := B ⧸ Subgroup.zpowers g
  have hQ2 : 2 ∣ Nat.card Q := by
    have hQp : IsPGroup 2 Q := hB.to_quotient _
    obtain ⟨m, hm⟩ := hQp.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hgB
      have h1 : (Subgroup.zpowers g).index = 1 := by
        change Nat.card Q = 1
        rw [hm, pow_zero]
      exact Subgroup.index_eq_one.mp h1
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨ybar, hybar⟩ := exists_prime_orderOf_dvd_card' 2 hQ2
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ybar
  have hy : y ∉ Subgroup.zpowers g := by
    intro h
    have : (y : Q) = 1 := (QuotientGroup.eq_one_iff y).mpr h
    rw [this, orderOf_one] at hybar
    exact absurd hybar (by norm_num)
  have hy2 : y ^ 2 ∈ Subgroup.zpowers g := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hybar, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy2)
  have hk' : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hj2 : 2 ∣ j := by
    have h1 : g ^ (j * 2 ^ (k - 1)) = 1 := by
      rw [pow_mul, hj, ← pow_mul, mul_comm, ← hk', ← hexp, Monoid.pow_exponent_eq_one]
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hk, hk', mul_comm j] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h3
  obtain ⟨i, rfl⟩ := hj2
  set z := y * (g ^ i)⁻¹ with hz
  set w := g ^ (2 ^ (k - 1)) with hw
  have hz2 : z ^ 2 = 1 := by
    rw [hz, mul_pow, inv_pow, ← hj, ← pow_mul, mul_comm i 2, mul_inv_cancel]
  have hw2 : w ^ 2 = 1 := by
    rw [hw, ← pow_mul, ← hk', ← hexp, Monoid.pow_exponent_eq_one]
  have hw1 : w ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hwg : w ∈ Subgroup.zpowers g := Subgroup.npow_mem_zpowers g _
  have hzg : z ∉ Subgroup.zpowers g := by
    intro h
    apply hy
    have : y = z * g ^ i := by rw [hz]; group
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.npow_mem_zpowers g i)
  have hzwg : z * w ∉ Subgroup.zpowers g := by
    intro h
    apply hzg
    have : z = z * w * w⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hwg)
  have hzw2 : (z * w) ^ 2 = 1 := by rw [mul_pow, hz2, hw2, one_mul]
  have h1z : (1 : B) ≠ z := fun h => hzg (h ▸ Subgroup.one_mem _)
  have h1zw : (1 : B) ≠ z * w := fun h => hzwg (h ▸ Subgroup.one_mem _)
  have hwz : w ≠ z := fun h => hzg (h ▸ hwg)
  have hwzw : w ≠ z * w := fun h => hzwg (h ▸ hwg)
  have hzzw : z ≠ z * w := fun h => hw1 (by simpa using h.symm)
  have hcard : ({1, w, z, z * w} : Finset B).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hw1.symm, h1z, h1zw]),
      Finset.card_insert_of_notMem (by simp [hwz, hwzw]),
      Finset.card_insert_of_notMem (by simp [hzzw]), Finset.card_singleton]
  have hsub : ({1, w, z, z * w} : Finset B) ⊆ Finset.univ.filter fun x : B => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hw2, hz2, hzw2]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hcard]
  exact Finset.card_le_card hsub

variable {G : Type} [Group G]

@[expose] def omegaOneIn {F : Subgroup G} (A : Subgroup F) (hA : IsMulCommutative A) :
    Subgroup G where
  carrier := {x | ∃ a : F, a ∈ A ∧ (a : G) = x ∧ a ^ 2 = 1}
  one_mem' := ⟨1, A.one_mem, rfl, one_pow 2⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl, ha2⟩ ⟨b, hb, rfl, hb2⟩
    have hab : a * b = b * a :=
      congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact ⟨a * b, A.mul_mem ha hb, rfl, by rw [(Commute.mul_pow hab 2), ha2, hb2, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl, ha2⟩
    exact ⟨a⁻¹, A.inv_mem ha, rfl, by rw [inv_pow, ha2, inv_one]⟩

theorem isElemAbelian_omegaOneIn {F : Subgroup G} (A : Subgroup F) (hA : IsMulCommutative A) :
    CFSG.Assembly.IsElemAbelian 2 (omegaOneIn A hA) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax, -⟩ := x.2
    obtain ⟨b, hb, hby, -⟩ := y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [← hax, ← hby]
    exact congrArg (fun u : F => (u : G)) (congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, -, rfl, ha2⟩
    rw [← Subgroup.coe_pow, ha2, Subgroup.coe_one]

theorem four_le_card_omegaOneIn [Finite G] {F : Subgroup G} (A : Subgroup F)
    (hA : IsMulCommutative A) (hA2 : IsPGroup 2 A) (hnc : ¬ IsCyclic A) :
    4 ≤ Nat.card (omegaOneIn A hA) := by
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  have h4 := four_le_card_sq_eq_one hA2 (fun h => hnc h)
  refine h4.trans (Nat.card_le_card_of_injective
    (fun x => ⟨((x.1 : A) : F), ⟨(x.1 : F), (x.1 : A).2, rfl, by
      simpa using congrArg Subtype.val x.2⟩⟩) fun x y hxy => ?_)
  have := congrArg (fun u : omegaOneIn A hA => (u : G)) hxy
  exact Subtype.ext (Subtype.ext (Subtype.ext this))

theorem centralizer_eq_normalizer_zpowers {t : G} (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) = Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  apply le_antisymm
  · intro g hg
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) n).eq.symm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
      (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
    have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    have hmem : ∀ x ∈ Subgroup.zpowers t, x = 1 ∨ x = t := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_mod_orderOf, ht]
      have : n % (2 : ℕ) = 0 ∨ n % (2 : ℕ) = 1 := by omega
      rcases this with h | h <;> rw [h]
      · left; exact zpow_zero t
      · right; exact zpow_one t
    rcases hmem _ h1 with h | h
    · exfalso
      have : t = 1 := by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h]

theorem isTwoLocal_centralizer {t : G} (ht : orderOf t = 2) :
    CFSG.Assembly.IsTwoLocal (Subgroup.centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.zpowers t, fun h => ?_, IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one]), centralizer_eq_normalizer_zpowers ht⟩
  have h1 : t ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers t
  rw [Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem le_normalizer_inSubgroup_pCore (C : Subgroup G) :
    C ≤ Subgroup.normalizer (inSubgroup (CFSG.pCore 2) C : Set G) :=
  (Subgroup.le_normalizer).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 C))

theorem le_normalizer_omegaOneIn {C : Subgroup G} (A : Subgroup (inSubgroup (CFSG.pCore 2) C))
    (hA : IsMulCommutative A) [hAc : A.Characteristic] :
    C ≤ Subgroup.normalizer (omegaOneIn A hA : Set G) := by
  intro g hg
  have hgF : (inSubgroup (CFSG.pCore 2) C).map (MulAut.conj g).toMonoidHom =
      inSubgroup (CFSG.pCore 2) C := by
    have h := le_normalizer_inSubgroup_pCore C hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    exact h
  let ψ : inSubgroup (CFSG.pCore 2) C ≃* inSubgroup (CFSG.pCore 2) C :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hgF)
  have hψv : ∀ x : inSubgroup (CFSG.pCore 2) C,
      ((ψ x : inSubgroup (CFSG.pCore 2) C) : G) = g * x * g⁻¹ := fun x => rfl
  have hfix : A.comap ψ.symm.toMonoidHom = A := hAc.fixed ψ.symm
  have hψA : ∀ a ∈ A, ψ a ∈ A := by
    intro a ha
    rw [← hfix]
    change ψ.symm (ψ a) ∈ A
    rw [MulEquiv.symm_apply_apply]
    exact ha
  have hψA' : ∀ a ∈ A, ψ.symm a ∈ A := by
    intro a ha
    rw [← hfix] at ha
    exact ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, ha, rfl, ha2⟩
    exact ⟨ψ a, hψA a ha, hψv a, by rw [← map_pow, ha2, map_one]⟩
  · rintro ⟨b, hb, hbx, hb2⟩
    refine ⟨ψ.symm b, hψA' b hb, ?_, by rw [← map_pow, hb2, map_one]⟩
    have h1 := hψv (ψ.symm b)
    rw [MulEquiv.apply_symm_apply, hbx] at h1
    calc ((ψ.symm b : inSubgroup (CFSG.pCore 2) C) : G) =
        g⁻¹ * (g * ((ψ.symm b : inSubgroup (CFSG.pCore 2) C) : G) * g⁻¹) * g := by group
      _ = x := by rw [← h1]; group

end Res611Res5

open Res611Res5

end CFSG.RankThree.PartTwo.Sec6
