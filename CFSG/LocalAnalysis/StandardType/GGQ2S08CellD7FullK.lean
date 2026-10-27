module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCertD7K
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA6FullK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

theorem ggQ2s08_cellK_twD7 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08CellK .twD 7 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl
    g φ hInd hRefl _ _ hnE y K hnb hFix _ _
  have hW' : ∃ e : Fin 7 ≃ M.Λ, M.coxeter = (ggCoxeterMatrixD 7).reindex e := by
    have key : ∀ m : ℕ, m = 7 → (∃ e : Fin m ≃ M.Λ, M.coxeter = (ggCoxeterMatrixD m).reindex e) →
        ∃ e : Fin 7 ≃ M.Λ, M.coxeter = (ggCoxeterMatrixD 7).reindex e := by
      rintro m rfl h
      exact h
    exact key _ hrank (by simpa only [GGQ2LabelWeyl, htag] using hWeyl)
  obtain ⟨e, he⟩ := hW'
  obtain ⟨κ, hκx, hκs⟩ := ggQ2_fullCoords_D 7 (by norm_num) (by norm_num) M hShape.2.2.1 e
    (ggQ2_cartan_D e he M.isCartan)
  have hκx' : κ M.xV = xLast 7 := hκx
  have hW := ggQ2Cell_map_automizer_L M κ e (dFullS 7) hκs
  refine ggQ2s08_cell_of_test_P hLB hP hΓi hTBN hS hI1 hCav M κ hκx' hW
    d7fK d7f_test_K g φ hInd hRefl ?_
  obtain ⟨N, -⟩ : ∃ N : GGQ2NbrDatum 3 Bs K, 3 ≤ Fintype.card N.Λ :=
    hTBN (p := 3) hS rfl hI1 hnb
  let R : Set (Vn 8 ≃ₗ[ZMod 3] Vn 8) := ggQ2CellLin M κ '' Set.range N.simple
  have hR_closure : Subgroup.closure R = (ggAutomizer K Bs).map (ggQ2CellLin M κ) := by
    rw [N.automizer_K, ← MonoidHom.map_closure]
  have hBstar : GGBstar 3 B Bs := hS.1.1.2.1
  have hBsabel : IsElemAbelian 3 Bs := hBstar.2.1
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBsabel.1.is_comm.comm a b
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hJK : J ≤ K := le_of_ggNbr hLB hI hDJ (hP G 3 B x L D J hI hDJ) hnb
  have hdisp : ∀ (ψ : MulAut ↥Bs) (b : ↥Bs),
      ggQ2CellLin M κ ψ (κ (M.model (Additive.ofMul b))) - κ (M.model (Additive.ofMul b)) =
        κ (M.model (Additive.ofMul (ψ b * b⁻¹))) := by
    intro ψ b
    rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply, ggLin_apply_ofMul (p := 3), ← map_sub]
    congr 1
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, sub_eq_add_neg]
  have hfixed : ∀ (ψ : MulAut ↥Bs) (c : ↥Bs),
      ggQ2CellLin M κ ψ (κ (M.model (Additive.ofMul c))) = κ (M.model (Additive.ofMul c)) →
        ψ c = c := by
    intro ψ c h
    rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply, ggLin_apply_ofMul (p := 3)] at h
    exact Additive.ofMul.injective (M.model.injective (κ.injective h))
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases hs with ⟨a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := ha
    exact ggQ2Cell_isRefl M κ (by
      have hα : N.root i (N.coroot i) = 2 := by
        rw [N.pairing i i, N.isCartan.1 i]
        norm_num
      exact ggIsReflection_of_eq_reflection (p := 3) (by norm_num) N.model hα
        (ggLin_eq_reflection N.model hα (N.simple_apply i)))
  · rw [hR_closure]
    apply Subgroup.map_mono
    exact ggAutomizer_mono Bs ((le_ggG0_of_ggNbr (L := L) hnb).trans Subgroup.le_normalizer)
  · intro h hh
    rw [hR_closure] at hh
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
    rw [hR_closure]
    rw [← map_mul, ← map_inv, ← map_mul]
    apply Subgroup.mem_map_of_mem
    have hBstar : GGBstar 3 B Bs := hS.1.1.2.1
    have hyBs : y ∈ Bs := hBstar.1 hnb.1.2.1
    have hfix_c : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := hFix ⟨y, hyBs⟩ rfl
    have hconj : ((φ ⟨y, hyBs⟩ : ↥Bs) : G) = g * y * g⁻¹ := hInd.2 ⟨y, hyBs⟩
    have hgy : g * y * g⁻¹ = y := by
      rw [← hconj, hfix_c]
    have hgy_zp : g * y * g⁻¹ ∈ Subgroup.zpowers y := by
      rw [hgy]
      exact Subgroup.mem_zpowers y
    have hgK : g ∈ Subgroup.normalizer (K : Set G) :=
      ggQ2s08_nbr_normalizes_K hLB hP hS.1 rfl hCav hnb hInd.1 hgy_zp
    have hφg : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := hInd.2
    have hφi := inv_apply_of_forall hφg
    have hφNorm : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro ψ
      constructor
      · intro hψ
        obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
        refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹,
          (Subgroup.mem_normalizer_iff.mp hgK l).mp hl,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hInd.1 hlN) (Subgroup.inv_mem _ hInd.1),
          fun b => ?_⟩
        rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hψl, hφi]
        group
      · intro hψ
        obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
        have hgK' := Subgroup.inv_mem _ hgK
        have hgN' := Subgroup.inv_mem _ hInd.1
        refine mem_ggAutomizer_iff.mpr ⟨g⁻¹ * l * g, ?_, ?_, fun b => ?_⟩
        · simpa using (Subgroup.mem_normalizer_iff.mp hgK' l).mp hl
        · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN' hlN) hInd.1
        · have hψeq : ψ = φ⁻¹ * (φ * ψ * φ⁻¹) * φ := by group
          rw [hψeq, MulAut.mul_apply, MulAut.mul_apply, hφi, hψl, hφg]
          group
    exact (Subgroup.mem_normalizer_iff.mp hφNorm a).mp ha
  · rintro ⟨h1, h2⟩
    apply hnE
    refine ⟨fun b => ?_, fun h hJ hN b c hc => ?_⟩
    ·
      have hfixK : ∀ a ∈ ggAutomizer K Bs, a (φ b * b⁻¹) = φ b * b⁻¹ := by
        intro a ha
        apply hfixed
        rw [← hdisp φ b]
        refine h2 _ _ ?_
        rw [hR_closure]
        exact Subgroup.mem_map_of_mem _ ha
      have hbBC : ((φ b * b⁻¹ : ↥Bs) : G) ∈ ggBarCentralizer 3 Bs K := by
        apply (N.fixed_ZK (φ b * b⁻¹)).mp
        rw [mem_ggFixedSubmodule_iff (p := 3)]
        intro a ha
        rw [ggLin_apply_ofMul (p := 3) N.model a, hfixK a ha]
      have hc := ggQ2_barCentralizer_le_centralizer_J hLB hP hS hnb hbBC
      rwa [show b⁻¹ * φ b = φ b * b⁻¹ from hcomm _ _]
    ·
      have hα : ggConjAut Bs hN ∈ ggAutomizer K Bs :=
        mem_ggAutomizer_iff.mpr ⟨h, hJK hJ, hN, fun _ => rfl⟩
      have hcα : c = ggConjAut Bs hN b * b⁻¹ := by
        apply Subtype.ext
        rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply]
        have := congrArg Subtype.val (hcomm b⁻¹ (ggConjAut Bs hN b))
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply] at this
        exact this
      apply hfixed
      rw [hcα, ← hdisp]
      refine h1 _ ?_ _
      rw [hR_closure]
      exact Subgroup.mem_map_of_mem _ hα

end CFSG.StandardType

end
