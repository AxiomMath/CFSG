module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCertK
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA6Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08ReflBasics
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

theorem ggQ2_barCentralizer_le_centralizer_J (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {B D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) {b : G} (hb : b ∈ ggBarCentralizer 3 Bs K) :
    b ∈ Subgroup.centralizer (J : Set G) := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hpJ : 3 ∣ Nat.card J := hP G 3 B x L D J hI hDJ
  have hJY : J ≤ K := le_of_ggNbr hLB hI hDJ hpJ hnb
  have hJq : IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp
      hDJ.1.2.2.2.2.2.1.2.2
  have hBstar : GGBstar 3 B Bs := hS.1.1.2.1
  have hIDAll : GGInnerDiagAll 3 B Bs x L D J := hS.1.2.2.1
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hIDAll.1
  have hBsabel : IsElemAbelian 3 Bs := hBstar.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBstar.1 hDJ.1 hBsL
  have hbBs : b ∈ Bs := hb.1
  have hcommK : ⁅K, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf 3 K := hb.2.2
  have hbJ : b ∈ Subgroup.normalizer (J : Set G) := hBsJ hbBs
  have hcommJ : ⁅J, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf 3 K :=
    le_trans (Subgroup.commutator_mono hJY le_rfl) hcommK
  exact ggF1 Nat.prime_three hJq hpJ hJY hbJ hcommJ

theorem ggQ2s08_cellK_twA6
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) :
    GGQ2S08CellK .twA 6 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl
    g φ hInd hRefl _ _ _ y K hnb hFix _ _
  have hW' : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 6).reindex e := by
    have key : ∀ m : ℕ, m = 6 → (∃ e : Fin m ≃ M.Λ, M.coxeter = (CoxeterMatrix.A m).reindex e) →
        ∃ e : Fin 6 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 6).reindex e := by
      rintro m rfl h
      exact h
    exact key _ hrank (by simpa only [GGQ2LabelWeyl, htag] using hWeyl)
  obtain ⟨e, he⟩ := hW'
  obtain ⟨κ, hκx, hκs⟩ := ggQ2_fullCoords_A7 M hShape.2.2.1 e
    (ggQ2_cartan_A e he M.isCartan)
  have hκx' : κ M.xV = oneN 7 := by
    rw [hκx]
    rfl
  have hW := ggQ2Cell_map_automizer_L M κ e (aFullS 7) hκs
  rw [← a7fS_eq] at hW
  have hJ := ggQ2s08_a6f_jPos hRig hS M hMark ⟨htag, hrank, hq⟩ hWeyl κ hκx
    (hW ▸ closure_a7fS_le_permGroup)
  refine ggQ2s08_cell_of_test_P hLB hP hΓi hTBN hS hI1 hCav M κ hκx hW
    a7fK a7f_test_K g φ hInd hRefl ?_
  obtain ⟨N, hNrank⟩ : ∃ N : GGQ2NbrDatum 3 Bs K, 3 ≤ Fintype.card N.Λ :=
    hTBN (p := 3) hS rfl hI1 hnb
  let R : Set (Vn 7 ≃ₗ[ZMod 3] Vn 7) := ggQ2CellLin M κ '' Set.range N.simple
  have hR_closure : Subgroup.closure R = (ggAutomizer K Bs).map (ggQ2CellLin M κ) := by
    rw [N.automizer_K, ← MonoidHom.map_closure]
  let Mg₀ : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7) :=
    (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
      (ggQ2CellLin M κ)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
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
  · have hNotCentral : x ∉ ggBarCentralizer 3 Bs K := by
      intro hx
      have hxcomm : ⁅K, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf 3 K := hx.2.2
      exact hnb.2.2.2 hxcomm
    have hNotFixed : N.model (Additive.ofMul ⟨x, M.hx⟩) ∉
        ggFixedSubmodule (p := 3) N.model (ggAutomizer K Bs) := by
      intro h
      exact hNotCentral ((N.fixed_ZK ⟨x, M.hx⟩).mp h)
    rw [mem_ggFixedSubmodule_iff (p := 3)] at hNotFixed
    push Not at hNotFixed
    obtain ⟨a, ha, hxa⟩ := hNotFixed
    refine ⟨ggQ2CellLin M κ a, ?_, ?_⟩
    · rw [hR_closure]
      exact Subgroup.mem_map_of_mem (ggQ2CellLin M κ) ha
    · intro h
      rw [ggQ2CellLin_apply, ← hκx', LinearEquiv.symm_apply_apply, GGQ2LDatum.xV,
        ggLin_apply_ofMul] at h
      have h_eq : M.model (Additive.ofMul (a ⟨x, M.hx⟩)) = M.xV := by
        apply κ.injective
        rw [h, ← GGQ2LDatum.xV]
      have h_eq' : a ⟨x, M.hx⟩ = ⟨x, M.hx⟩ := by
        apply Additive.ofMul.injective
        apply M.model.injective
        rw [h_eq, GGQ2LDatum.xV]
      exact hxa (by
        rw [ggLin_apply_ofMul, h_eq'])
  · obtain ⟨S, hS5, hSJ⟩ := hJ
    refine ⟨S, hS5, fun v hv a ha a' ha' => ?_⟩
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, κ (M.model (Additive.ofMul b)) = v := by
      refine ⟨Additive.toMul (M.model.symm (κ.symm v)), ?_⟩
      rw [ofMul_toMul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hv_fixed : ∀ h ∈ Subgroup.closure R,
        h (κ (M.model (Additive.ofMul b))) = κ (M.model (Additive.ofMul b)) := hv
    have hfix_b : ∀ a ∈ ggAutomizer K Bs,
        ggLin (p := 3) M.model a (M.model (Additive.ofMul b)) = M.model (Additive.ofMul b) := by
      intro a ha
      have h1 : ggQ2CellLin M κ a (κ (M.model (Additive.ofMul b))) =
          κ (M.model (Additive.ofMul b)) := by
        rw [hR_closure] at hv_fixed
        exact hv_fixed (ggQ2CellLin M κ a) (Subgroup.mem_map_of_mem (ggQ2CellLin M κ) ha)
      rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply] at h1
      exact κ.injective h1
    have hbBC : (b : G) ∈ ggBarCentralizer 3 Bs K := by
      apply (N.fixed_ZK b).mp
      rw [mem_ggFixedSubmodule_iff (p := 3)]
      intro a ha
      have h1 : ggLin (p := 3) M.model a (M.model (Additive.ofMul b)) =
          M.model (Additive.ofMul b) :=
        hfix_b a ha
      have h2 : M.model (Additive.ofMul (a b)) = M.model (Additive.ofMul b) := by
        rw [← ggLin_apply_ofMul (p := 3) M.model a b]
        exact h1
      have h3 : a b = b := M.model.injective (Additive.ofMul.injective h2)
      rw [ggLin_apply_ofMul (p := 3) N.model a b, h3]
    have hbCen : (b : G) ∈ Subgroup.centralizer (J : Set G) :=
      ggQ2_barCentralizer_le_centralizer_J hLB hP hS hnb hbBC
    exact hSJ b hbCen a ha a' ha'

end CFSG.StandardType

end
