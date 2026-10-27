module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLComp
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix
open CFSG.SeitzReduction.LinearPilot

theorem perm_fixes_compl_of_block_intertwines
    {d : ℕ} {K : Type} [Field K] {S : Finset (Fin d)}
    {M : Matrix (Fin d) (Fin d) K} (hM : ∀ i ∉ S, M i i = 1)
    {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ u : Fin d → K, M * diagonal u =
      diagonal (u ∘ (σ⁻¹ : Equiv.Perm (Fin d))) * M) :
    ∀ i ∉ S, σ i = i := by
  classical
  intro i hi
  have h := congrFun (congrFun (hσ (Pi.single i 1)) i) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hM i hi, one_mul, mul_one,
    Pi.single_eq_same] at h
  have hfix : σ⁻¹ i = i := by
    by_contra hn
    rw [Function.comp_apply, Pi.single_eq_of_ne hn] at h
    exact one_ne_zero h
  have heq := congrArg σ hfix
  simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using heq.symm

theorem isDiag_mul_permSL_of_intertwines
    {d : ℕ} {K : Type} [Field K] [CharP K 2]
    {s : SpecialLinearGroup (Fin d) K} {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ u : Fin d → K, (s : Matrix (Fin d) (Fin d) K) * diagonal u =
      diagonal (u ∘ (σ⁻¹ : Equiv.Perm (Fin d))) * (s : Matrix (Fin d) (Fin d) K)) :
    ((s * TypeA.permSL σ : SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K).IsDiag := by
  have hcomm : ∀ u : Fin d → K,
      ((s * TypeA.permSL σ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * diagonal u = diagonal u *
          ((s * TypeA.permSL σ : SpecialLinearGroup (Fin d) K) :
            Matrix (Fin d) (Fin d) K) := by
    intro u
    rw [Matrix.SpecialLinearGroup.coe_mul, TypeA.coe_permSL,
      Matrix.mul_assoc, TypeA.permMatrix_mul_diagonal, ← Matrix.mul_assoc,
      hσ (u ∘ σ)]
    have hc : (u ∘ σ) ∘ (σ⁻¹ : Equiv.Perm (Fin d)) = u := by
      funext i
      simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    rw [hc, Matrix.mul_assoc]
  rw [TypeA.eq_diagonal_of_commute_diagonal _ hcomm]
  exact Matrix.isDiag_diagonal _

theorem GGActsVec.apply_of_isDiag
    {d : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    {φ : SpecialLinearGroup (Fin d) K →* G} {b : G} {t : Fin d → Kˣ}
    (hb : GGActsVec φ b t) {s : SpecialLinearGroup (Fin d) K}
    (hs : (s : Matrix (Fin d) (Fin d) K).IsDiag) : b * φ s * b⁻¹ = φ s := by
  rw [hb s]
  congr 1
  apply Subtype.ext
  ext i j
  rw [ggDiagConj_apply]
  by_cases hij : i = j
  · subst hij
    rw [mul_comm (t i : K) _, mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, mul_one]
  · rw [hs hij, mul_zero, zero_mul]

theorem permSL_mem_blockSpecialLinear_of_fixes_compl
    {d : ℕ} {K : Type} [Field K] [CharP K 2] {S : Finset (Fin d)}
    {σ : Equiv.Perm (Fin d)} (hσ : ∀ i ∉ S, σ i = i) :
    TypeA.permSL (K := K) σ ∈ blockSpecialLinear S := by
  classical
  rw [mem_blockSpecialLinear, TypeA.coe_permSL]
  intro i j hij
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  have heq : σ i = j ↔ i = j := by
    rcases hij with hi | hj
    · rw [hσ i hi]
    · have hjfix : σ j = j := hσ j hj
      exact ⟨fun h => σ.injective (h.trans hjfix.symm), fun h => by rw [h, hjfix]⟩
  simp only [heq, Matrix.one_apply]

namespace TypeANbrDvd

theorem ggAutomizer_blockSpecialLinear_eq
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ')
    (hker : ∀ g, φ' g = 1 → g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t)
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈
      Subgroup.normalizer (A : Set (MulAut L'))) (S : Finset (Fin d)) :
    ggAutomizer (((blockSpecialLinear S).map φ').map (MulAut.conj : L' →* MulAut L')) A =
      (fixingSubgroup (Equiv.Perm (Fin d)) ((S : Set (Fin d))ᶜ)).map (permAut φ' A hN) := by
  classical
  apply le_antisymm
  · intro a ha
    obtain ⟨g, hg, hgN, hga⟩ := mem_ggAutomizer_iff.mp ha
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨σ, hcoord, -, hσ⟩ :=
      exists_perm_of_conj_mem_normalizer_with_coordinates hp hp2 hpK hφs hker hA hsc hdiag hgN
    have hσfix : ∀ i ∉ S, σ i = i :=
      perm_fixes_compl_of_block_intertwines
        (fun i hi => (mem_blockSpecialLinear.mp hs) i i (Or.inl hi) |>.trans
          (Matrix.one_apply_eq i)) hcoord
    refine Subgroup.mem_map.mpr ⟨σ, (mem_fixingSubgroup_iff (Equiv.Perm (Fin d))).mpr (fun i hi => hσfix i hi), ?_⟩
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [permAut_apply, ggConjAut_apply, hga b]
    exact (hσ b b.2).symm
  · intro a ha
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp ha
    have hσfix : ∀ i ∉ S, σ i = i := (mem_fixingSubgroup_iff (Equiv.Perm (Fin d))).mp hσ
    have hinv : ∀ i ∉ S, σ⁻¹ i = i := by
      intro i hi
      have h := congrArg (σ⁻¹ : Equiv.Perm (Fin d)) (hσfix i hi)
      simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using h.symm
    have hperm : TypeA.permSL (K := K) σ⁻¹ ∈ blockSpecialLinear S :=
      permSL_mem_blockSpecialLinear_of_fixes_compl hinv
    refine mem_ggAutomizer_iff.mpr ⟨NbrInnerWeylA.permConj φ' σ, ?_, hN σ, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨φ' (TypeA.permSL σ⁻¹),
        Subgroup.mem_map.mpr ⟨TypeA.permSL σ⁻¹, hperm, rfl⟩, rfl⟩
    · intro b
      rw [permAut_apply, ggConjAut_apply]

theorem ggAutomizer_blockSpecialLinear_ambient_eq
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {φ : SpecialLinearGroup (Fin d) K →* X} (hφs : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars d K)
    (hdiag : ∀ a ∈ (ggGamma X hBsN).range, ∃ t : Fin d → K, ActsDiag φ a t)
    (hN : ∀ σ, (φ (TypeA.permSL σ⁻¹) : G) ∈ Subgroup.normalizer (Bs : Set G))
    (ρ : Equiv.Perm (Fin d) →* MulAut Bs)
    (hρ : ∀ σ b, (ρ σ b : G) = (φ (TypeA.permSL σ⁻¹) : G) * b *
      (φ (TypeA.permSL σ⁻¹) : G)⁻¹) (S : Finset (Fin d)) :
    ggAutomizer (((blockSpecialLinear S).map φ).map X.subtype) Bs =
      (fixingSubgroup (Equiv.Perm (Fin d)) ((S : Set (Fin d))ᶜ)).map ρ := by
  classical
  let A := (ggGamma X hBsN).range
  have hAe : IsElemAbelian p A := ggTD_elemAb hBsN hBs
  have hsc : GGTorusSelfCent p A := ggTorusSelfCent_ggGamma hBsN hSC
  let n : Equiv.Perm (Fin d) → G := fun σ => φ (TypeA.permSL σ⁻¹)
  apply le_antisymm
  · intro c hc
    obtain ⟨g, hg, hgN, hgc⟩ := mem_ggAutomizer_iff.mp hc
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hl
    have hgA : MulAut.conj (φ s) ∈ Subgroup.normalizer (A : Set (MulAut X)) :=
      conj_mem_normalizer_range_ggGamma hBsN (φ s).2 hgN
    obtain ⟨σ, hcoord, -, -⟩ :=
      exists_perm_of_conj_mem_normalizer_with_coordinates hp hp2 hpK hφs hker hAe hsc hdiag hgA
    have hσfix : ∀ i ∉ S, σ i = i :=
      perm_fixes_compl_of_block_intertwines
        (fun i hi => ((mem_blockSpecialLinear.mp hs) i i (Or.inl hi)).trans
          (Matrix.one_apply_eq i)) hcoord
    refine Subgroup.mem_map.mpr ⟨σ,
      (mem_fixingSubgroup_iff (Equiv.Perm (Fin d))).mpr hσfix, ?_⟩
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hρ σ b, hgc b]
    let u := s * TypeA.permSL σ
    have hu : (u : Matrix (Fin d) (Fin d) K).IsDiag := isDiag_mul_permSL_of_intertwines hcoord
    have hbu : ∀ b' : Bs, (b' : G) * (φ u : G) * (b' : G)⁻¹ = φ u := by
      intro b'
      obtain ⟨t, ht⟩ := hdiag (ggGamma X hBsN b') ⟨b', rfl⟩
      have h := congrArg Subtype.val (ht.apply_of_isDiag hu)
      rw [ggGamma_coe] at h
      exact h
    have hsu : (φ u : G) * n σ = (φ s : G) := by
      dsimp only [u, n]
      rw [← TypeA.permSL_inv σ]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    let b' : Bs := ⟨n σ * b * (n σ)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hN σ) (b : G)).mp b.2⟩
    have hc' : (φ u : G) * (b' : G) * (φ u : G)⁻¹ = b' := by
      have h := hbu b'
      have hcomm : (b' : G) * (φ u : G) = (φ u : G) * b' := by
        calc
          (b' : G) * (φ u : G) = ((b' : G) * (φ u : G) * (b' : G)⁻¹) * b' := by group
          _ = (φ u : G) * b' := by rw [h]
      rw [← hcomm]
      group
    calc
      n σ * b * (n σ)⁻¹ = (φ u : G) * (n σ * b * (n σ)⁻¹) * (φ u : G)⁻¹ := hc'.symm
      _ = ((φ u : G) * n σ) * b * ((φ u : G) * n σ)⁻¹ := by group
      _ = (φ s : G) * b * (φ s : G)⁻¹ := by rw [hsu]
  · intro c hc
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hc
    have hσfix : ∀ i ∉ S, σ i = i := (mem_fixingSubgroup_iff (Equiv.Perm (Fin d))).mp hσ
    have hinv : ∀ i ∉ S, σ⁻¹ i = i := by
      intro i hi
      have h := congrArg (σ⁻¹ : Equiv.Perm (Fin d)) (hσfix i hi)
      simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using h.symm
    have hperm : TypeA.permSL (K := K) σ⁻¹ ∈ blockSpecialLinear S :=
      permSL_mem_blockSpecialLinear_of_fixes_compl hinv
    exact mem_ggAutomizer_iff.mpr ⟨n σ,
      Subgroup.mem_map.mpr ⟨φ (TypeA.permSL σ⁻¹),
        Subgroup.mem_map.mpr ⟨TypeA.permSL σ⁻¹, hperm, rfl⟩, rfl⟩,
      hN σ, hρ σ⟩

end TypeANbrDvd

end CFSG.StandardType

end
