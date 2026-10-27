module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore
public import CFSG.LocalAnalysis.StandardType.GGTDModelUPerm
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG Assembly TableB Matrix
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.TableBUE CFSG.StandardType.UnitTB CFSG.StandardType.UnitAct
open CFSG.StandardType.LineU

namespace UnitAct

theorem isDiag_mul_permSU_of_intertwines
    {K : Type} [Field K] [CharP K 2] {n d : ℕ}
    {hK : UnitaryFieldData 2 n K} {s : ↥(unitarySU 2 n K d)}
    {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ u : Fin d → K,
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal u =
        diagonal (u ∘ σ) * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    (((s * permSU hK σ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).IsDiag := by
  classical
  have hcomm : ∀ u : Fin d → K,
      (((s * permSU hK σ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * diagonal u = diagonal u *
          (((s * permSU hK σ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
            Matrix (Fin d) (Fin d) K) := by
    intro u
    rw [Subgroup.coe_mul, Units.val_mul, LineU.coe_permSU, LineU.coe_permGL_matrix,
      Matrix.mul_assoc, TypeA.permMatrix_mul_diagonal (τ := σ⁻¹) u,
      ← Matrix.mul_assoc, hσ (u ∘ (σ⁻¹ : Equiv.Perm (Fin d)))]
    have hc : (u ∘ (σ⁻¹ : Equiv.Perm (Fin d))) ∘ σ = u := by
      funext i
      simp
    rw [hc, Matrix.mul_assoc]
  rw [TypeA.eq_diagonal_of_commute_diagonal _ hcomm]
  exact Matrix.isDiag_diagonal _

theorem permSU_mem_blockSU_of_fixes_compl
    {K : Type} [Field K] {n d : ℕ} {hK : UnitaryFieldData 2 n K}
    {S : Finset (Fin d)} {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ i ∉ S, σ i = i) :
    permSU hK σ ∈ blockSU S := by
  classical
  rw [TableBUE.mem_blockSU, LineU.coe_permSU]
  intro i j hij
  simp only [TableBUE.permGL_apply]
  have heq : σ⁻¹ i = j ↔ i = j := by
    rcases hij with hi | hj
    · have hsi : σ i = i := hσ i hi
      have hsinv : σ⁻¹ i = i := by
        apply σ.injective
        simpa [hsi] using σ.apply_symm_apply i
      rw [hsinv]
    · have hsj : σ j = j := hσ j hj
      have hsinv : σ⁻¹ j = j := by
        apply σ.injective
        simpa [hsj] using σ.apply_symm_apply j
      constructor
      · intro h
        have := congrArg σ h
        simpa [hsj] using this
      · intro h
        subst h
        simpa [hsinv]
  simp only [heq, Matrix.one_apply]

end UnitAct

open UnitAct

theorem UnitAct.ggAutomizer_blockSU_ambient_eq_four
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n d p : ℕ} {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {ψ : ↥(unitarySU 2 n K d) →* X} (hM : UnitTB.Model ψ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hdiag : ∀ a ∈ (ggGamma X hBsN).range, ∃ t : Fin d → K, LineU.ActsDiagU ψ a t)
    (hN : ∀ σ : Equiv.Perm (Fin d),
      ((ψ (LineU.permSU hM.field σ) : X) : G) ∈ Subgroup.normalizer (Bs : Set G))
    (ρ : Equiv.Perm (Fin d) →* MulAut ↥Bs)
    (hρ : ∀ σ (b : ↥Bs),
      ((ρ σ b : ↥Bs) : G) = ((ψ (LineU.permSU hM.field σ) : X) : G) * (b : G) *
        (((ψ (LineU.permSU hM.field σ) : X) : G))⁻¹)
    (S : Finset (Fin d)) :
    ggAutomizer ((blockSU S).map (X.subtype.comp ψ)) Bs =
      (fixingSubgroup (Equiv.Perm (Fin d)) ((S : Set (Fin d))ᶜ)).map ρ := by
  classical
  rw [← Subgroup.map_map]
  let A := (ggGamma X hBsN).range
  have hAe : IsElemAbelian p A := ggTD_elemAb hBsN hBs
  have hsc : GGTorusSelfCent p A := ggTorusSelfCent_ggGamma hBsN hSC
  let nAct : Equiv.Perm (Fin d) → G := fun σ => ((ψ (LineU.permSU hM.field σ) : X) : G)
  apply le_antisymm
  · intro c hc
    obtain ⟨g, hg, hgN, hgc⟩ := mem_ggAutomizer_iff.mp hc
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hl
    have hgA : MulAut.conj (ψ s) ∈
        Subgroup.normalizer (A : Set (MulAut ↥X)) := by
      have h := conj_mem_normalizer_range_ggGamma hBsN
        (X := X) (Bs := Bs) (g := ((ψ s : X) : G)) (ψ s).2 hgN
      simpa [A] using h
    obtain ⟨π, hπ⟩ :=
      exists_perm_of_normalizes hM hK hp hp2 hpq hd hAe hsc hdiag hgA
    have hfixInv : ∀ i ∉ S, π⁻¹ i = i := by
      refine perm_fixes_compl_of_block_intertwines (S := S)
        (M := ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ?_ ?_
      · intro i hi
        have hb := (TableBUE.mem_blockSU.mp hs) i i (Or.inl hi)
        simpa using hb
      · intro u
        simpa [Equiv.Perm.coe_inv] using hπ u
    have hperm : LineU.permSU hM.field π⁻¹ ∈ blockSU S :=
      UnitAct.permSU_mem_blockSU_of_fixes_compl hfixInv
    refine Subgroup.mem_map.mpr ⟨π⁻¹,
      (mem_fixingSubgroup_iff (Equiv.Perm (Fin d))).mpr hfixInv, ?_⟩
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hρ π⁻¹ b, hgc b]
    let u : ↥(unitarySU 2 n K d) := s * LineU.permSU hM.field π
    have hu : (((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).IsDiag :=
      UnitAct.isDiag_mul_permSU_of_intertwines (hK := hM.field) (σ := π) hπ
    have hbu : ∀ b' : ↥Bs,
        (b' : G) * ((ψ u : X) : G) * (b' : G)⁻¹ = ((ψ u : X) : G) := by
      intro b'
      obtain ⟨t, ht⟩ := hdiag (ggGamma X hBsN b') ⟨b', rfl⟩
      have hu_diag : (((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
          diagonal (fun i => (((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i i) :=
        (isDiag_iff_diagonal_diag _).mp hu |>.symm
      have h := congrArg Subtype.val (ht.fix_of_diagonal u hu_diag)
      rw [ggGamma_coe] at h
      exact h
    have hsuX : ψ u * ψ (LineU.permSU hM.field π⁻¹) = ψ s := by
      rw [← map_mul]
      congr 1
      simp only [u]
      rw [← UnitAct.permSU_inv]
      group
    have hsu : ((ψ u : X) : G) * nAct π⁻¹ = ((ψ s : X) : G) := by
      simpa [nAct] using congrArg (fun x : ↥X => (x : G)) hsuX
    let b' : ↥Bs := ⟨nAct π⁻¹ * (b : G) * (nAct π⁻¹)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hN π⁻¹) (b : G)).mp b.2⟩
    have hcomm : (b' : G) * ((ψ u : X) : G) = ((ψ u : X) : G) * (b' : G) := by
      calc (b' : G) * ((ψ u : X) : G)
          = (((b' : G) * ((ψ u : X) : G) * (b' : G)⁻¹) * (b' : G)) := by group
        _ = ((ψ u : X) : G) * (b' : G) := by rw [hbu b']
    have hc' : ((ψ u : X) : G) * (b' : G) * (((ψ u : X) : G))⁻¹ = (b' : G) := by
      rw [← hcomm]
      group
    calc
      nAct π⁻¹ * (b : G) * (nAct π⁻¹)⁻¹ =
          ((ψ u : X) : G) * (nAct π⁻¹ * (b : G) * (nAct π⁻¹)⁻¹) *
            (((ψ u : X) : G))⁻¹ := hc'.symm
      _ = (((ψ u : X) : G) * nAct π⁻¹) * (b : G) *
            ((((ψ u : X) : G) * nAct π⁻¹))⁻¹ := by group
      _ = ((ψ s : X) : G) * (b : G) * (((ψ s : X) : G))⁻¹ := by rw [hsu]
  · intro c hc
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hc
    have hσfix : ∀ i ∉ S, σ i = i :=
      (mem_fixingSubgroup_iff (Equiv.Perm (Fin d))).mp hσ
    have hperm : LineU.permSU hM.field σ ∈ blockSU S :=
      UnitAct.permSU_mem_blockSU_of_fixes_compl hσfix
    exact mem_ggAutomizer_iff.mpr ⟨((ψ (LineU.permSU hM.field σ) : X) : G),
      Subgroup.mem_map.mpr ⟨ψ (LineU.permSU hM.field σ),
        Subgroup.mem_map.mpr ⟨LineU.permSU hM.field σ, hperm, rfl⟩, rfl⟩,
      hN σ, hρ σ⟩

theorem UnitAct.ggAutomizer_blockSU_ambient_eq
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n d p : ℕ} {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {ψ : ↥(unitarySU 2 n K d) →* X} (hM : UnitTB.Model ψ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hdiag : ∀ a ∈ (ggGamma X hBsN).range, ∃ t : Fin d → K, LineU.ActsDiagU ψ a t)
    (hN : ∀ σ : Equiv.Perm (Fin d),
      ((ψ (LineU.permSU hM.field σ) : X) : G) ∈ Subgroup.normalizer (Bs : Set G))
    (ρ : Equiv.Perm (Fin d) →* MulAut ↥Bs)
    (hρ : ∀ σ (b : ↥Bs),
      ((ρ σ b : ↥Bs) : G) = ((ψ (LineU.permSU hM.field σ) : X) : G) * (b : G) *
        (((ψ (LineU.permSU hM.field σ) : X) : G))⁻¹)
    (S : Finset (Fin d)) :
    ggAutomizer ((blockSU S).map (X.subtype.comp ψ)) Bs =
      (fixingSubgroup (Equiv.Perm (Fin d)) ((S : Set (Fin d))ᶜ)).map ρ :=
  UnitAct.ggAutomizer_blockSU_ambient_eq_four hM hK hp hp2 hpq (by omega) hBsN hBs hSC hdiag hN
    ρ hρ S

end CFSG.StandardType

end
