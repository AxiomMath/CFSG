module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Sp
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenCover
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem f4_sum_cartan_three (x : Fin Tag.F4.rank → ℤ) :
    (∑ j, Tag.cartan .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank) j * x j) =
      - x ⟨2, by decide⟩ + 2 * x ⟨3, by decide⟩ := by
  have e0 : Tag.cartan .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank)
      (0 : Fin Tag.F4.rank) = 0 := by decide
  have e1 : Tag.cartan .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank)
      (⟨1, by decide⟩) = 0 := by decide
  have e2 : Tag.cartan .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank)
      (⟨2, by decide⟩) = -1 := by decide
  have e3 : Tag.cartan .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank)
      (⟨3, by decide⟩) = 2 := by decide
  have h02 : (0 : Fin Tag.F4.rank) ≠ (⟨2, by decide⟩ : Fin Tag.F4.rank) := by decide
  have h03 : (0 : Fin Tag.F4.rank) ≠ (⟨3, by decide⟩ : Fin Tag.F4.rank) := by decide
  have h12 : (⟨1, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨2, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h13 : (⟨1, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨3, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h23 : (⟨3, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨2, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h : ∀ j : Fin Tag.F4.rank, Tag.cartan .F4 (⟨3, by decide⟩) j * x j =
      (if j = (⟨2, by decide⟩ : Fin Tag.F4.rank) then - x (⟨2, by decide⟩) else 0) +
        (if j = (⟨3, by decide⟩ : Fin Tag.F4.rank) then 2 * x (⟨3, by decide⟩) else 0) := by
    intro j
    fin_cases j <;> simp [e0, e1, e2, e3, h02, h03, h12, h13, h23]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private theorem f4_sum_cartan_two (x : Fin Tag.F4.rank → ℤ) :
    (∑ j, Tag.cartan .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank) j * x j) =
      -2 * x ⟨1, by decide⟩ + 2 * x ⟨2, by decide⟩ - x ⟨3, by decide⟩ := by
  have e0 : Tag.cartan .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank)
      (0 : Fin Tag.F4.rank) = 0 := by decide
  have e1 : Tag.cartan .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank)
      (⟨1, by decide⟩) = -2 := by decide
  have e2 : Tag.cartan .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank)
      (⟨2, by decide⟩) = 2 := by decide
  have e3 : Tag.cartan .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank)
      (⟨3, by decide⟩) = -1 := by decide
  have h01 : (0 : Fin Tag.F4.rank) ≠ (⟨1, by decide⟩ : Fin Tag.F4.rank) := by decide
  have h02 : (0 : Fin Tag.F4.rank) ≠ (⟨2, by decide⟩ : Fin Tag.F4.rank) := by decide
  have h03 : (0 : Fin Tag.F4.rank) ≠ (⟨3, by decide⟩ : Fin Tag.F4.rank) := by decide
  have h12 : (⟨1, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨2, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h13 : (⟨1, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨3, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h21 : (⟨2, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨1, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h23 : (⟨2, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨3, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h31 : (⟨3, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨1, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h32 : (⟨3, by decide⟩ : Fin Tag.F4.rank) ≠ (⟨2, by decide⟩ : Fin Tag.F4.rank) := by
    decide
  have h : ∀ j : Fin Tag.F4.rank, Tag.cartan .F4 (⟨2, by decide⟩) j * x j =
      (if j = (⟨1, by decide⟩ : Fin Tag.F4.rank) then -2 * x (⟨1, by decide⟩) else 0) +
        ((if j = (⟨2, by decide⟩ : Fin Tag.F4.rank) then 2 * x (⟨2, by decide⟩) else 0) +
          (if j = (⟨3, by decide⟩ : Fin Tag.F4.rank) then - x (⟨3, by decide⟩) else 0)) := by
    intro j
    fin_cases j <;> simp [e0, e1, e2, e3, h01, h02, h03, h12, h13, h21, h23, h31, h32]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  ring

private theorem f4_reflect_three_three (x : Fin Tag.F4.rank → ℤ) :
    (reflect .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank) x) ⟨3, by decide⟩ =
      x ⟨2, by decide⟩ - x ⟨3, by decide⟩ := by
  rw [reflect]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  rw [f4_sum_cartan_three]
  ring

private theorem f4_reflect_two_two (x : Fin Tag.F4.rank → ℤ) :
    (reflect .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank) x) ⟨2, by decide⟩ =
      2 * x ⟨1, by decide⟩ - x ⟨2, by decide⟩ + x ⟨3, by decide⟩ := by
  rw [reflect]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  rw [f4_sum_cartan_two]
  ring

private theorem f4_reflect_two_three (x : Fin Tag.F4.rank → ℤ) :
    (reflect .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank) x) ⟨3, by decide⟩ =
      x ⟨3, by decide⟩ := by
  rw [reflect]
  simp only [Pi.sub_apply, Pi.smul_apply,
    Pi.single_eq_of_ne (by decide : (⟨3, by decide⟩ : Fin Tag.F4.rank) ≠ ⟨2, by decide⟩),
    smul_eq_mul, mul_zero, sub_zero]

private theorem f4_simple_three_two_three (x : Fin Tag.F4.rank → ℤ) :
    ((simple .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank) *
      simple .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank)) • x) ⟨3, by decide⟩ =
      2 * x ⟨1, by decide⟩ - x ⟨2, by decide⟩ := by
  rw [mul_smul, simple_smul, simple_smul, f4_reflect_three_three, f4_reflect_two_two,
    f4_reflect_two_three]
  ring

private theorem f4_simple_three_three (x : Fin Tag.F4.rank → ℤ) :
    ((simple .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank)) • x) ⟨3, by decide⟩ =
      x ⟨2, by decide⟩ - x ⟨3, by decide⟩ := by
  rw [simple_smul, f4_reflect_three_three]

theorem exists_B4_cover_F4 {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) :
    ∃ (v : WeylGroup .F4) (S : Set (Fin Tag.F4.rank → ℤ)), γ ∈ S ∧ kernelRoots f4D4Char ⊆ S ∧
      ∀ δ ∈ S, IsRoot .F4 δ ∧ Even ((v⁻¹ • δ) ⟨3, by decide⟩) := by
  have hkerRoot : ∀ δ ∈ kernelRoots f4D4Char, IsRoot .F4 δ := fun δ hδ => hδ.1
  have hker3 : ∀ δ ∈ kernelRoots f4D4Char, Even (δ ⟨3, by decide⟩) := by
    intro δ hδ
    rw [kernelRoots, Set.mem_ofPred_eq] at hδ
    obtain ⟨hroot, hchar⟩ := hδ
    rw [f4D4Char] at hchar
    simp only [MonoidHom.prod_apply, Prod.mk_eq_one] at hchar
    obtain ⟨-, h3⟩ := hchar
    have h3ker : δ ∈ kernelRoots (maskChar (τ := .F4)
        CFSG.ComponentClassification.CatLeafProof.f4BitsB4) := ⟨hroot, h3⟩
    have h3even : Even (maskPairing
        CFSG.ComponentClassification.CatLeafProof.f4BitsB4 δ) :=
      (mem_kernelRoots_maskChar.1 h3ker).2
    rwa [CFSG.ComponentClassification.CatLeafProof.maskPairing_f4BitsB4] at h3even
  have hker2 : ∀ δ ∈ kernelRoots f4D4Char, Even (δ ⟨2, by decide⟩) := by
    intro δ hδ
    rw [kernelRoots, Set.mem_ofPred_eq] at hδ
    obtain ⟨hroot, hchar⟩ := hδ
    rw [f4D4Char] at hchar
    simp only [MonoidHom.prod_apply, Prod.mk_eq_one] at hchar
    obtain ⟨h2, -⟩ := hchar
    have h2ker : δ ∈ kernelRoots (maskChar (τ := .F4)
        (listMask [false, false, true, false])) := ⟨hroot, h2⟩
    have h2even : Even (maskPairing (listMask [false, false, true, false]) δ) :=
      (mem_kernelRoots_maskChar.1 h2ker).2
    have hpair : maskPairing (listMask [false, false, true, false]) δ =
        δ ⟨2, by decide⟩ := by
      rw [maskPairing, Finset.sum_eq_single (⟨2, by decide⟩ : Fin Tag.F4.rank)]
      · simp [listMask]
      · intro j _ hj
        fin_cases j <;> simp [listMask] at hj ⊢
      · intro h
        exact absurd (Finset.mem_univ _) h
    rwa [hpair] at h2even
  by_cases h3 : Even (γ ⟨3, by decide⟩)
  · refine ⟨1, {δ : Fin Tag.F4.rank → ℤ | IsRoot .F4 δ ∧ Even (δ ⟨3, by decide⟩)},
      ⟨hγ, h3⟩, ?_, ?_⟩
    · intro δ hδ
      exact ⟨hkerRoot δ hδ, hker3 δ hδ⟩
    · intro δ hδ
      exact ⟨hδ.1, by simpa using hδ.2⟩
  · by_cases h2 : Even (γ ⟨2, by decide⟩)
    · refine ⟨((simple .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank) *
        simple .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank))⁻¹),
        {δ : Fin Tag.F4.rank → ℤ | IsRoot .F4 δ ∧ Even (δ ⟨2, by decide⟩)},
        ⟨hγ, h2⟩, ?_, ?_⟩
      · intro δ hδ
        exact ⟨hkerRoot δ hδ, hker2 δ hδ⟩
      · intro δ hδ
        refine ⟨hδ.1, ?_⟩
        have hfin : (((simple .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank) *
            simple .F4 (⟨2, by decide⟩ : Fin Tag.F4.rank))⁻¹)⁻¹ • δ) ⟨3, by decide⟩ =
            2 * δ ⟨1, by decide⟩ - δ ⟨2, by decide⟩ := by
          rw [inv_inv, f4_simple_three_two_three]
        rw [hfin]
        exact Even.sub (even_two_mul (δ ⟨1, by decide⟩)) hδ.2
    · refine ⟨(simple .F4 (⟨3, by decide⟩ : Fin Tag.F4.rank))⁻¹,
        {δ : Fin Tag.F4.rank → ℤ | IsRoot .F4 δ ∧
          Even (δ ⟨2, by decide⟩ + δ ⟨3, by decide⟩)},
        ⟨hγ, ?_⟩, ?_, ?_⟩
      · refine Int.even_add.mpr ⟨?_, ?_⟩
        · intro h2'; exact (h2 h2').elim
        · intro h3'; exact (h3 h3').elim
      · intro δ hδ
        exact ⟨hkerRoot δ hδ, Even.add (hker2 δ hδ) (hker3 δ hδ)⟩
      · intro δ hδ
        refine ⟨hδ.1, ?_⟩
        rw [inv_inv, f4_simple_three_three]
        exact Int.even_sub.mpr (Int.even_add.mp hδ.2)

theorem iSup_phiTwoComp_eq_top_F4
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup .F4} (hneg : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ → w • γ = -γ)
    {g0 : ModGL .F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w) :
    (⨆ γ : {γ : Fin Tag.F4.rank → ℤ // IsRoot .F4 γ}, phiTwoComp g0 γ.1) = ⊤ := by
  have hw : w = CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg := by
    refine ext_single fun i => ?_
    rw [hneg _ (IsRoot.basis i), CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul]
  subst w
  refine iSup_phiTwoComp_eq_top_of_kernelRoots_cover f4D4Char hFr
    (fun x hx hfix => mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr hx hfix)
    (fun v => ext_single fun i => by
      rw [mul_smul, mul_smul, CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul,
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul, smul_neg])
    f4Neg_mem_closure_rootReflection_kernelRoots_f4D4Char
    (Φ₁ := {γ : Fin Tag.F4.rank → ℤ | IsRoot .F4 γ ∧ Even (γ ⟨3, by decide⟩)})
    (fun g hgC hgFr x hx => mem_iSup_phiTwoComp_of_mem_phiTwoB4 hK4 hFr
      (fun γ _ => CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul γ) hgC hgFr hx)
    (fun γ hγ => ?_) hg0C hg0
  obtain ⟨v, S, hγS, hDS, hS⟩ := exists_B4_cover_F4 hγ
  exact ⟨v, S, hγS, hDS, fun δ hδ => ⟨(hS δ hδ).1, IsRoot.smul (hS δ hδ).1 v⁻¹, (hS δ hδ).2⟩⟩

end CFSG.StandardType.PhiTwoRootGen

end
