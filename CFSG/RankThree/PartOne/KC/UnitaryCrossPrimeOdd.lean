module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeFixed

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {x : gramSU h (idGram K n)}

theorem conj_mem_inSubgroup_core {G : Type*} [Group G] (q : ℕ) (C : Subgroup G) {g s : G}
    (hg : g ∈ C) (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C) :
    g * s * g⁻¹ ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C := by
  obtain ⟨s', hs', rfl⟩ := hs
  refine ⟨⟨g, hg⟩ * s' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (inferInstance : (CFSG.RankThree.LocalRank.aschbacherSolvableCore q C).Normal).conj_mem
    s' hs' ⟨g, hg⟩

theorem inSubgroup_core_le {G : Type*} [Group G] (q : ℕ) (C : Subgroup G) :
    CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C ≤ C :=
  Subgroup.map_subtype_le _

section Odd

variable (L : LiftData h n p x)

include L in
theorem LiftData.idCenterN_eq_center :
    idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
      (Subgroup.center ↥((Subgroup.centralizer ({liftUnitary x} :
        Set (primeFormUnitary h (idGram K n)))).map (primeFormConjHom h (idGram K n)))).map
          ((Subgroup.centralizer ({liftUnitary x} :
            Set (primeFormUnitary h (idGram K n)))).map
              (primeFormConjHom h (idGram K n))).subtype := by
  have hC1 : idCentralizerD h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
      (Subgroup.centralizer ({liftUnitary x} :
        Set (primeFormUnitary h (idGram K n)))).map (primeFormConjHom h (idGram K n)) :=
    L.centralizer_image
  have key : ∀ N' : Subgroup (MulAut (primeFormP h (idGram K n))),
      idCentralizerD h (primeFormConjHom h (idGram K n) (liftUnitary x)) = N' →
      idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
        (Subgroup.center ↥N').map N'.subtype := by
    intro N' hN'
    subst hN'
    rfl
  exact key _ hC1

include L in
theorem LiftData.Q0_comm {a b : MulAut (primeFormP h (idGram K n))}
    (ha : a ∈ idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)))
    (hb : b ∈ idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x))) : a * b = b * a := by
  rw [L.idCenterN_eq_center] at ha hb
  exact ProjSetting.center_inf_comm ha hb

include L in
theorem LiftData.commutator_mem_odd [DecidableEq (primaryFactors (idEnd x))] (hp2 : p ≠ 2)
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B)
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hAB : A ≤ B ⊓ idStab x)
    (hA : IsPGroup p ↥A) (hfix : ∀ a : ↥A, L.FixesIdempotents (hAB.trans inf_le_right) a)
    {s a : MulAut (primeFormP h (idGram K n))}
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ idStab x)) (ha : a ∈ A) :
    ⁅s, a⁆ ∈ idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) ⊓ (B ⊓ idStab x) ∧
      Odd (orderOf ⁅s, a⁆) := by
  have hfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have S := L.projSetting B hB
  have haCB : a ∈ B ⊓ idStab x := hAB ha
  have hsCB : s ∈ B ⊓ idStab x := inSubgroup_core_le p _ hs
  have hsa : ⁅s, a⁆ ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ idStab x) := by
    have h1 := conj_mem_inSubgroup_core p _ haCB (inv_mem hs)
    have h2 : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [h2]
    exact mul_mem hs h1
  have hsaCB : ⁅s, a⁆ ∈ B ⊓ idStab x := inSubgroup_core_le p _ hsa
  have hsaD : ⁅s, a⁆ ∈ primeFormD h (idGram K n) :=
    commutator_mem_primeFormD L.three_le L.four_le s a
  have hC1 : idCentralizerD h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
      (Subgroup.centralizer ({liftUnitary x} :
        Set (primeFormUnitary h (idGram K n)))).map (primeFormConjHom h (idGram K n)) :=
    L.centralizer_image
  have hsaN : ⁅s, a⁆ ∈ (Subgroup.centralizer ({liftUnitary x} :
      Set (primeFormUnitary h (idGram K n)))).map (primeFormConjHom h (idGram K n)) := by
    rw [← hC1]
    exact Subgroup.mem_inf.mpr ⟨hsaD, (Subgroup.mem_inf.mp hsaCB).2⟩
  have hcent := S.core_le_centralizer_derived L.prime hsa
  have hcQ : ⁅s, a⁆ ∈ idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) := by
    rw [L.idCenterN_eq, ← S.inf_centralizer_derived_eq]
    exact Subgroup.mem_inf.mpr ⟨hsaN, hcent⟩
  refine ⟨Subgroup.mem_inf.mpr ⟨hcQ, hsaCB⟩, ?_⟩
  let Q₀ : Subgroup (MulAut (primeFormP h (idGram K n))) :=
    idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) ⊓ (B ⊓ idStab x)
  have hfinQ : Finite ↥Q₀ := inferInstance
  have hcomm : ∀ z₁ ∈ Q₀, ∀ z₂ ∈ Q₀, z₁ * z₂ = z₂ * z₁ := fun z₁ h₁ z₂ h₂ =>
    L.Q0_comm (Subgroup.mem_inf.mp h₁).1 (Subgroup.mem_inf.mp h₂).1
  have hσQ : ∀ z ∈ Q₀, (MulAut.conj a) z ∈ Q₀ := by
    intro z hz
    have hz' := Subgroup.mem_inf.mp hz
    set CB := B ⊓ idStab x with hCB
    have hnorm := S.center_inf_normal
    have h2 := hnorm.conj_mem (⟨z, hz'.2⟩ : CB)
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
        ⟨by rw [← L.idCenterN_eq_center]; exact hz'.1, hz'.2⟩)) ⟨a, haCB⟩
    have h3 := Subgroup.mem_subgroupOf.mp h2
    rw [← L.idCenterN_eq_center] at h3
    exact h3
  have hfixσ : ∀ z ∈ Q₀, ∀ k : ℕ, z ^ 2 ^ k = 1 → (MulAut.conj a) z = z := by
    intro z hz k hk
    exact L.conj_eq_of_fix hp2 hA (hAB.trans inf_le_right) ⟨a, ha⟩ (hfix ⟨a, ha⟩)
      (Subgroup.mem_inf.mp hz).1 hk
  have hm : Odd (orderOf a) := by
    have hord : orderOf (⟨a, ha⟩ : ↥A) = orderOf a := Subgroup.orderOf_mk a ha
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow L.prime).mp (orderOf_dvd_of_pow_eq_one hk)
    rw [← hord, hj]
    exact (L.prime.odd_of_ne_two hp2).pow
  have hσm : (MulAut.conj a) ^ orderOf a = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hc : s * ((MulAut.conj a) s)⁻¹ ∈ Q₀ := by
    have : s * ((MulAut.conj a) s)⁻¹ = ⁅s, a⁆ := by
      simp only [MulAut.conj_apply, commutatorElement_def]
      group
    rw [this]
    exact Subgroup.mem_inf.mpr ⟨hcQ, hsaCB⟩
  have hodd := odd_orderOf_of_fixed_two_part (MulAut.conj a) Q₀
    (fun z₁ h₁ z₂ h₂ => (hcomm z₁ h₁ z₂ h₂ : z₁ * z₂ = z₂ * z₁)) hσQ hfixσ hm hσm s hc
  have : s * ((MulAut.conj a) s)⁻¹ = ⁅s, a⁆ := by
    simp only [MulAut.conj_apply, commutatorElement_def]
    group
  rwa [this] at hodd

include L in
theorem LiftData.Q0_normal (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B) :
    ((idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) ⊓ (B ⊓ idStab x)).subgroupOf
      (B ⊓ idStab x)).Normal := by
  have hfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have S := L.projSetting B hB
  rw [L.idCenterN_eq_center]
  exact S.center_inf_normal

end Odd

end CFSG.RankThree.PartOne.KCUnitaryModel
