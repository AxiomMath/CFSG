module

public import CFSG.RankThree.GF2n.Parrott.XAbelianCrux
public import CFSG.RankThree.GF2n.Parrott.XAbelianTools
public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped commutatorElement Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}

section Final

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem X_abelian_of_qH_eq (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3) (hρq : qH D ρ = xabRho)
    {x : G} (hxH : x ∈ H z) (hxρ : x ∈ centralizer ({(ρ : G)} : Set G)) (hxx : x * x = 1)
    (hxv : IsConj (qH D ⟨x, hxH⟩) vA) {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({(ρ : G)} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := by
    intro hx1
    have h1 : qH D ⟨x, hxH⟩ = 1 := by
      have : (⟨x, hxH⟩ : ↥(H z)) = 1 := Subtype.ext hx1
      rw [this, map_one]
    rw [h1] at hxv
    have h2 : vA = 1 := isConj_one_right.mp hxv
    exact v_ne_one (by simpa using congrArg Subtype.val h2)
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hxX : x ∈ X := mem_isSylowOf_centralizer_inf_of_orderOf_two hxρ hxH hx2 hX
  have hXH : X ≤ H z := hX.le.trans (inf_le_left.trans inf_le_right)
  have hXρ : ∀ g ∈ X, g ∈ centralizer ({(ρ : G)} : Set G) := fun g hg =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hX.le hg)).1).1
  set S : Subgroup A45 := (X.subgroupOf (H z)).map (qH D) with hS
  have hSle : S ≤ Subgroup.centralizer ({xabRho} : Set A45) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hρq, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hXρ _ (Subgroup.mem_subgroupOf.mp he))
  have hSp : IsPGroup 2 S := (hX.isPGroup.comap_subtype).map (qH D)
  have hy : qH D ⟨x, hxH⟩ ∈ S := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩
  obtain ⟨c, hc, hcy, hcS⟩ := xab_normalize S hSle hSp hy hxv
  obtain ⟨s, hsq, hsρ⟩ := exists_lift_centralizer D hρ3 (g := c)
    (by rw [hρq]; exact mem_centralizer_singleton_iff.mp hc)
  have hsH : (s : G) ∈ H z := s.2
  have hρs : (s : G) * ρ * (s : G)⁻¹ = ρ := by
    have h1 : (s : G) * ρ = ρ * s := congrArg Subtype.val hsρ
    calc (s : G) * ρ * (s : G)⁻¹ = ρ * s * (s : G)⁻¹ := by rw [h1]
      _ = ρ := by group
  have hX2 := isSylowOf_map_conj_centralizer hsH hX
  rw [hρs] at hX2
  have hx2H : (s : G) * x * (s : G)⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem hsH hxH) ((H z).inv_mem hsH)
  refine commute_of_map_conj (s : G) ?_
  refine xab_std D h hZ P hP hρ3 hρq hx2H ?_ ?_ ?_ hX2.le ?_ ?_
  · rw [mem_centralizer_singleton_iff]
    have h1 : x * (ρ : G) = ρ * x := mem_centralizer_singleton_iff.mp hxρ
    calc (s : G) * x * (s : G)⁻¹ * ρ
        = (s : G) * x * (s : G)⁻¹ * ((s : G) * ρ * (s : G)⁻¹) := by rw [hρs]
      _ = (s : G) * (x * ρ) * (s : G)⁻¹ := by group
      _ = (s : G) * (ρ * x) * (s : G)⁻¹ := by rw [h1]
      _ = ((s : G) * ρ * (s : G)⁻¹) * ((s : G) * x * (s : G)⁻¹) := by group
      _ = ρ * ((s : G) * x * (s : G)⁻¹) := by rw [hρs]
  · have e : (s : G) * x * (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) =
        (s : G) * (x * x) * (s : G)⁻¹ := by group
    rw [e, hxx]
    group
  · have e1 : (⟨(s : G) * x * (s : G)⁻¹, hx2H⟩ : ↥(H z)) = s * ⟨x, hxH⟩ * s⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, hsq]
    exact hcy
  · exact Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩
  · intro g' hg' hmem
    obtain ⟨g, hgX, rfl⟩ := Subgroup.mem_map.mp hmem
    have hgH := hXH hgX
    have e1 : (⟨(MulAut.conj (s : G)).toMonoidHom g, hg'⟩ : ↥(H z)) = s * ⟨g, hgH⟩ * s⁻¹ :=
      Subtype.ext rfl
    have e2 : qH D ⟨(MulAut.conj (s : G)).toMonoidHom g, hg'⟩ = c * qH D ⟨g, hgH⟩ * c⁻¹ := by
      rw [e1, map_mul, map_mul, map_inv, hsq]
    rw [e2]
    exact hcS _ ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩

theorem X_abelian_of_spin (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3)
    (hρ : IsConj (qH D ρ) (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : A45))
    {x : G} (hxH : x ∈ H z) (hxρ : x ∈ centralizer ({(ρ : G)} : Set G)) (hxx : x * x = 1)
    (hxv : IsConj (qH D ⟨x, hxH⟩) vA) {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({(ρ : G)} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  obtain ⟨c₁, hc₁⟩ := isConj_iff.mp hρ
  obtain ⟨g₁, hg₁⟩ := qH_surjective D c₁
  refine commute_of_map_conj (g₁ : G) ?_
  have hX1 := isSylowOf_map_conj_centralizer g₁.2 hX
  have hx₁H : (g₁ : G) * x * (g₁ : G)⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem g₁.2 hxH) ((H z).inv_mem g₁.2)
  have hρ₁q : qH D (g₁ * ρ * g₁⁻¹) = xabRho := by
    rw [map_mul, map_mul, map_inv, hg₁]
    exact hc₁
  have hρ₁3 : orderOf (g₁ * ρ * g₁⁻¹) = 3 := by
    rw [← hρ3]
    exact (SemiconjBy.orderOf_eq g₁ (show g₁ * ρ = (g₁ * ρ * g₁⁻¹) * g₁ by group)).symm
  refine X_abelian_of_qH_eq D h hZ P hP hρ₁3 hρ₁q hx₁H ?_ ?_ ?_ hX1
  · rw [mem_centralizer_singleton_iff]
    have h1 : x * (ρ : G) = ρ * x := mem_centralizer_singleton_iff.mp hxρ
    show (g₁ : G) * x * (g₁ : G)⁻¹ * ((g₁ : G) * ρ * (g₁ : G)⁻¹) =
      ((g₁ : G) * ρ * (g₁ : G)⁻¹) * ((g₁ : G) * x * (g₁ : G)⁻¹)
    calc (g₁ : G) * x * (g₁ : G)⁻¹ * ((g₁ : G) * ρ * (g₁ : G)⁻¹)
        = (g₁ : G) * (x * ρ) * (g₁ : G)⁻¹ := by group
      _ = (g₁ : G) * (ρ * x) * (g₁ : G)⁻¹ := by rw [h1]
      _ = ((g₁ : G) * ρ * (g₁ : G)⁻¹) * ((g₁ : G) * x * (g₁ : G)⁻¹) := by group
  · have e : (g₁ : G) * x * (g₁ : G)⁻¹ * ((g₁ : G) * x * (g₁ : G)⁻¹) =
        (g₁ : G) * (x * x) * (g₁ : G)⁻¹ := by group
    rw [e, hxx]
    group
  · have e1 : (⟨(g₁ : G) * x * (g₁ : G)⁻¹, hx₁H⟩ : ↥(H z)) = g₁ * ⟨x, hxH⟩ * g₁⁻¹ :=
      Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, hg₁]
    exact (isConj_iff.mpr ⟨c₁, rfl⟩ : IsConj (qH D ⟨x, hxH⟩) (c₁ * qH D ⟨x, hxH⟩ * c₁⁻¹)).symm.trans
      hxv

theorem X_abelian (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3)
    (hρ : IsConj (qH D ρ) (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : A45))
    {x : G} (hx : x ∈ H z) (hxρ : x ∈ centralizer ({(ρ : G)} : Set G)) (hxx : x * x = 1)
    (hxv : IsConj (qH D ⟨x, hx⟩) vA) {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({(ρ : G)} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  exact X_abelian_of_spin D h hZ P (fun a => by simpa [rhoA, toQAct] using hP a) hρ3 hρ hx hxρ hxx
    hxv hX

end Final

end CFSG.RankThree.GF2n.Parrott
