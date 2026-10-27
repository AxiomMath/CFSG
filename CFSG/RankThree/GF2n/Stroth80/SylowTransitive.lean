module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Pointwise

variable {K : Type*} [Group K] [Finite K]

@[instance_reducible] def conjActionOnNontrivial (F : Subgroup K) (P : Subgroup K)
    (hP : P ≤ Subgroup.normalizer (F : Set K)) :
    MulAction P {a : K // a ∈ F ∧ a ≠ 1} where
  smul p a := ⟨(p : K) * a * (p : K)⁻¹, by
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hP p.2) (a : K)).mp a.2.1
    · intro h
      apply a.2.2
      have h1 : (p : K)⁻¹ * ((p : K) * a * (p : K)⁻¹) * (p : K) = 1 := by rw [h]; group
      simpa [mul_assoc] using h1⟩
  one_smul a := by
    apply Subtype.ext
    show ((1 : P) : K) * (a : K) * ((1 : P) : K)⁻¹ = a
    simp
  mul_smul p q a := by
    apply Subtype.ext
    show ((p * q : P) : K) * (a : K) * ((p * q : P) : K)⁻¹ =
      (p : K) * ((q : K) * (a : K) * (q : K)⁻¹) * (p : K)⁻¹
    simp [mul_assoc]

theorem exists_sylow_normalizer_of_trans (F Zs : Subgroup K) (hZF : Zs ≤ F)
    (hF : ∀ x ∈ F, x ^ 2 = 1) {s : K} (hs : s ∈ Zs) (hs1 : s ≠ 1)
    (hTI : ∀ g : K, ∀ u ∈ Zs, u ≠ 1 → g * u * g⁻¹ ∈ Zs → g ∈ Subgroup.normalizer (Zs : Set K))
    (hTrans : ∀ a ∈ F, a ≠ 1 → ∃ k ∈ Subgroup.normalizer (F : Set K), k * s * k⁻¹ = a)
    (P : Sylow 2 K) (hP : P.toSubgroup ≤ Subgroup.normalizer (F : Set K)) :
    ∃ P' : Sylow 2 K, P'.toSubgroup ≤ Subgroup.normalizer (Zs : Set K) := by
  classical
  letI : MulAction P.toSubgroup {a : K // a ∈ F ∧ a ≠ 1} := conjActionOnNontrivial F _ hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥F := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hF x x.2⟩
  obtain ⟨k0, hk0⟩ := (IsPGroup.iff_card).mp hpg
  have hk0pos : k0 ≠ 0 := by
    rintro rfl
    have h1 : Nat.card ↥F = 1 := by simpa using hk0
    have hFbot : F = ⊥ := Subgroup.card_eq_one.mp h1
    exact hs1 (by have := hZF hs; rw [hFbot] at this; simpa using this)
  have hcardF : Even (Nat.card ↥F) := by
    rw [hk0]
    exact (Nat.even_pow.mpr ⟨even_two, hk0pos⟩)
  have hcardX : Nat.card {a : K // a ∈ F ∧ a ≠ 1} = Nat.card ↥F - 1 := by
    let e : {a : K // a ∈ F ∧ a ≠ 1} ≃ {x : ↥F // x ≠ 1} :=
      { toFun := fun a => ⟨⟨a, a.2.1⟩, fun h => a.2.2 (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨x.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr e]
    haveI : Fintype ↥F := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  have hnot : ¬ 2 ∣ Nat.card {a : K // a ∈ F ∧ a ≠ 1} := by
    rw [hcardX]
    have hpos : 0 < Nat.card ↥F := Nat.card_pos
    obtain ⟨r, hr⟩ := hcardF
    omega
  have hmod := (P.isPGroup').card_modEq_card_fixedPoints {a : K // a ∈ F ∧ a ≠ 1}
  have hfix : 0 < Nat.card ↑(MulAction.fixedPoints P.toSubgroup {a : K // a ∈ F ∧ a ≠ 1}) := by
    by_contra h0
    have h0' : Nat.card ↑(MulAction.fixedPoints P.toSubgroup {a : K // a ∈ F ∧ a ≠ 1}) = 0 := by
      omega
    rw [h0'] at hmod
    exact hnot (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨⟨a, ha⟩⟩ := (Nat.card_pos_iff.mp hfix).1
  have hfixed : ∀ p : P.toSubgroup, (p : K) * a.1 * (p : K)⁻¹ = a.1 := fun p =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp ha p)
  obtain ⟨k, hkF, hka⟩ := hTrans a.1 a.2.1 a.2.2
  refine ⟨k⁻¹ • P, ?_⟩
  intro x hx
  rw [Sylow.coe_subgroup_smul] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
  apply hTI _ s hs hs1
  have e1 : (MulAut.conj k⁻¹ • y : K) = k⁻¹ * y * k := by
    simp [MulAut.smul_def, MulAut.conj_apply]
  rw [e1]
  have e2 : k⁻¹ * y * k * s * (k⁻¹ * y * k)⁻¹ = k⁻¹ * (y * (k * s * k⁻¹) * y⁻¹) * k := by group
  rw [e2, hka, hfixed ⟨y, hy⟩]
  have e3 : k⁻¹ * a.1 * k = s := by rw [← hka]; group
  rw [e3]
  exact hs

end CFSG.RankThree.GF2n.Stroth80
