module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSpecialForm
public import CFSG.LocalAnalysis.StandardType.ZS.MonomialKlein

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
  {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}

theorem exists_mem_forall_apply_eq_of_mem_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X} (ht : t ∈ movedGroup X) :
    ∃ g ∈ X, ∀ v : HardMathSupport.Kantor79.commutatorSpace X, g (v : U) = (t v : U) := by
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp ht
  refine ⟨g, g.2, fun v => ?_⟩
  rw [← hg, restrictHom_apply]

theorem exists_mem_centralizerSpace_of_lemmaTwoSevenData (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) :
    ∃ y : U, y ≠ 0 ∧ y ∈ centralizerSpace H ∧ y ∈ HardMathSupport.Kantor79.commutatorSpace B := by
  have h4 := hD.setting.four_le
  have hs : SplitSupport H (Module.finrank (ZMod p) U - 1) := hD.setting.sub.2.1
  obtain ⟨y, hy, hy0⟩ := hs.exists_mem_centralizerSpace_ne_zero (by omega)
  have hVB : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    (commutatorSpace_eq_ker_of_isCentralizingSplit hp (by omega) hD.split hD.isRefl).1
  refine ⟨y, hy0, hy, ?_⟩
  rw [hVB, LinearMap.mem_ker]
  have hyh : h y = y := mem_centralizerSpace.mp hy h hD.mem
  simpa using sub_eq_zero.mpr hyh

theorem mem_commutatorSpace_of_isCyclicRootTriple (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {i : Fin 3} (hi : i ≠ 0) :
    e i ∈ HardMathSupport.Kantor79.commutatorSpace B := by
  obtain ⟨-, -, -, -, -, -, -, hrmem, -⟩ :=
    exists_frame_of_isCyclicRootTriple hp hD h4 hr hT
  have hiB : r i ∈ B := hD.split.2.2.2.2 (hrmem i hi)
  refine HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hiB ?_
  exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
    (ZMod.prime_ne_zero p 2 hp) (hT.1 i).2.2

theorem apply_eq_self_of_isCyclicRootTriple (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hr : r 0 = h) (hT : IsCyclicRootTriple p H r e s)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ B) : g (e 0) = e 0 := by
  have h3 : 3 ≤ Module.finrank (ZMod p) U := by have := hD.setting.four_le; omega
  have hCB : centralizerSpace B = HardMathSupport.Kantor79.movedSpace h :=
    (commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl).2
  have hne : h (e 0) = -e 0 := hr ▸ (hT.1 0).2.2
  have he0 : e 0 ∈ centralizerSpace B := by
    rw [hCB]
    exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
      (ZMod.prime_ne_zero p 2 hp) hne
  exact mem_centralizerSpace.mp he0 g hg

theorem commutatorSpace_eq_span_of_isCyclicRootTriple (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hT : IsCyclicRootTriple p H r e s) :
    HardMathSupport.Kantor79.commutatorSpace H = Submodule.span (ZMod p) {e 0, e 1, e 2} := by
  have hle : Submodule.span (ZMod p) ({e 0, e 1, e 2} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl | rfl)
    · exact isCyclicRootTriple_root_mem_commutatorSpace hp hT 0
    · exact isCyclicRootTriple_root_mem_commutatorSpace hp hT 1
    · exact isCyclicRootTriple_root_mem_commutatorSpace hp hT 2
  have hrange : Set.range e = ({e 0, e 1, e 2} : Set U) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hfinspan : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) ({e 0, e 1, e 2} : Set U)) = 3 := by
    rw [← hrange, finrank_span_eq_card hT.2.2.1, Fintype.card_fin]
  have hfinVH : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H) = 3 := by
    have := hD.setting.sub.2.1.2.1
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinspan, hfinVH])).symm

theorem map_commutatorSpace_eq_of_isCyclicRootTriple (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hT : IsCyclicRootTriple p H r e s) {g : U ≃ₗ[ZMod p] U}
    (hg : ∀ i, g (e i) ∈ HardMathSupport.Kantor79.commutatorSpace H) :
    (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hspan := commutatorSpace_eq_span_of_isCyclicRootTriple hp hD h4 hT
  rw [hspan]
  have hle : (Submodule.span (ZMod p) ({e 0, e 1, e 2} : Set U)).map (g : U →ₗ[ZMod p] U) ≤
      Submodule.span (ZMod p) ({e 0, e 1, e 2} : Set U) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro x ⟨y, (rfl | rfl | rfl), rfl⟩
    · rw [← hspan]; exact hg 0
    · rw [← hspan]; exact hg 1
    · rw [← hspan]; exact hg 2
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearEquiv.finrank_map_eq]

private theorem linearIndependent_e1_e2_y [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (hT : IsCyclicRootTriple p H r e s)
    (hcomm : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) {e 1, e 2}) {y : U} (hy0 : y ≠ 0)
    (hyH : y ∈ centralizerSpace H) :
    LinearIndependent (ZMod p) ![e 1, e 2, y] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : c 0 • e 1 + c 1 • e 2 + c 2 • y = 0 := by
    rw [← hc, Fin.sum_univ_three]
    simp
  have hy : y ∉ Submodule.span (ZMod p) ({e 1, e 2} : Set U) := by
    have hsplitH : SplitSupport H (Module.finrank (ZMod p) U - 1) := hD.setting.sub.2.1
    rw [← hcomm]
    intro hy'
    have hle := HardMathSupport.Kantor79.commutatorSpace_mono
      (H := reflStab p H h) (H' := H) (reflSubgroupIn_le H _)
    have hbot : y ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hsplitH.1.inf_eq_bot]
      exact ⟨hle hy', hyH⟩
    exact hy0 (by simpa using hbot)
  by_cases hc2 : c 2 = 0
  · have hzero : ∑ i, ![0, c 0, c 1] i • e i = 0 := by
      rw [Fin.sum_univ_three]
      simpa [hc2] using hc'
    have hcoef := (Fintype.linearIndependent_iff.mp hT.2.2.1) ![0, c 0, c 1] hzero
    intro i
    fin_cases i
    · simpa using hcoef 1
    · simpa using hcoef 2
    · exact hc2
  · exfalso
    apply hy
    have h2 : c 2 • y = -(c 0 • e 1 + c 1 • e 2) := eq_neg_of_add_eq_zero_right hc'
    have h3 : y = -((c 2)⁻¹ • (c 0 • e 1 + c 1 • e 2)) := by
      calc y = (c 2)⁻¹ • (c 2 • y) := by rw [smul_smul, inv_mul_cancel₀ hc2, one_smul]
        _ = (c 2)⁻¹ • (-(c 0 • e 1 + c 1 • e 2)) := by rw [h2]
        _ = -((c 2)⁻¹ • (c 0 • e 1 + c 1 • e 2)) := by rw [smul_neg]
    rw [h3, smul_add, smul_smul, smul_smul]
    exact Submodule.neg_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

private theorem linearIndependent_e1_e2_y_subtype [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hT : IsCyclicRootTriple p H r e s)
    (hcomm : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) {e 1, e 2}) {y : U} (hy0 : y ≠ 0)
    (hyH : y ∈ centralizerSpace H) (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (he₁ : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (he₂ : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    LinearIndependent (ZMod p)
      (![⟨e 1, he₁⟩, ⟨e 2, he₂⟩, ⟨y, hyB⟩] : Fin 3 →
        HardMathSupport.Kantor79.commutatorSpace B) := by
  have hLI := linearIndependent_e1_e2_y hD hT hcomm hy0 hyH
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcoeffun : ∀ i,
      ((![⟨e 1, he₁⟩, ⟨e 2, he₂⟩, ⟨y, hyB⟩] i :
        HardMathSupport.Kantor79.commutatorSpace B) : U) = ![e 1, e 2, y] i := by
    intro i
    fin_cases i <;> rfl
  have hc' : (∑ i, c i • ![e 1, e 2, y] i) = 0 := by
    have := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace B => (w : U)) hc
    simpa [hcoeffun] using this
  exact (Fintype.linearIndependent_iff.mp hLI) c hc'

theorem isKleinFrame_of_isCyclicRootTriple (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) {y : U} (hy0 : y ≠ 0) (hyH : y ∈ centralizerSpace H)
    (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (he₁ : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (he₂ : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace B)
    {t₁ t₂ : HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace B}
    (ht₁ : ∀ v : HardMathSupport.Kantor79.commutatorSpace B, (t₁ v : U) = r 1 v)
    (ht₂ : ∀ v : HardMathSupport.Kantor79.commutatorSpace B, (t₂ v : U) = r 2 v) :
    IsKleinFrame t₁ t₂ ⟨e 1, he₁⟩ ⟨e 2, he₂⟩ ⟨y, hyB⟩ := by
  obtain ⟨-, -, -, -, -, -, hrapp, -, hcomm⟩ :=
    exists_frame_of_isCyclicRootTriple hp hD h4 hr hT
  have hLI := linearIndependent_e1_e2_y hD hT hcomm hy0 hyH
  have hLIW := linearIndependent_e1_e2_y_subtype hD hT hcomm hy0 hyH hyB he₁ he₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β γ hzero
    have hzero' : (∑ i, ![α, β, γ] i • ![e 1, e 2, y] i) = 0 := by
      have h := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace B => (w : U)) hzero
      simp at h
      rw [Fin.sum_univ_three]
      simpa using h
    have hcoef := (Fintype.linearIndependent_iff.mp hLI) ![α, β, γ] hzero'
    exact ⟨by simpa using hcoef 0, by simpa using hcoef 1, by simpa using hcoef 2⟩
  · intro v
    have htop := hLIW.span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_fin]
      have := hD.split.2.2.1.2.1
      omega)
    have hv : v ∈ Submodule.span (ZMod p)
        (Set.range (![⟨e 1, he₁⟩, ⟨e 2, he₂⟩, ⟨y, hyB⟩] : Fin 3 →
          HardMathSupport.Kantor79.commutatorSpace B)) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hv
    refine ⟨c 0, c 1, c 2, ?_⟩
    rw [← hc, Fin.sum_univ_three]
    simp
  · ext; rw [ht₁]; change r 1 (e 1) = -e 1; rw [hrapp, if_pos rfl]
  · ext; rw [ht₁]; change r 1 (e 2) = e 2; rw [hrapp, if_neg (by decide)]
  · ext; rw [ht₁]; change r 1 y = y
    exact mem_centralizerSpace.mp hyH (r 1) (hT.1 1).1
  · ext; rw [ht₂]; change r 2 (e 1) = e 1; rw [hrapp, if_neg (by decide)]
  · ext; rw [ht₂]; change r 2 (e 2) = -e 2; rw [hrapp, if_pos rfl]
  · ext; rw [ht₂]; change r 2 y = y
    exact mem_centralizerSpace.mp hyH (r 2) (hT.1 2).1

theorem exists_isKleinFrame_of_le_g2mmn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (h2 : movedGroup B ≤ g2mmn p f i₀ i₁ ζ)
    {y : U} (hy0 : y ≠ 0) (hyH : y ∈ centralizerSpace H)
    (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (he₁ : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace B)
    (he₂ : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    ∃ (d₁ d₂ : Fin 3 → (ZMod p)ˣ) (σ₁ σ₂ : Equiv.Perm (Fin 3)),
      IsKleinFrame (diagMap p f d₁ * permMap p f σ₁) (diagMap p f d₂ * permMap p f σ₂)
        ⟨e 1, he₁⟩ ⟨e 2, he₂⟩ ⟨y, hyB⟩ := by
  obtain ⟨-, -, -, -, -, -, -, hrmem, -⟩ :=
    exists_frame_of_isCyclicRootTriple hp hD h4 hr hT
  have h1B : r 1 ∈ B := hD.split.2.2.2.2 (hrmem 1 (by decide))
  have h2B : r 2 ∈ B := hD.split.2.2.2.2 (hrmem 2 (by decide))
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let φ : B →* (V ≃ₗ[ZMod p] V) :=
    restrictHom B V fun _ hh _ hv => apply_mem_commutatorSpace hh hv
  have hg1 : φ ⟨r 1, h1B⟩ ∈ movedGroup B := MonoidHom.mem_range.mpr ⟨⟨r 1, h1B⟩, rfl⟩
  have hg2 : φ ⟨r 2, h2B⟩ ∈ movedGroup B := MonoidHom.mem_range.mpr ⟨⟨r 2, h2B⟩, rfl⟩
  obtain ⟨d₁, σ₁, -, -, hdσ₁⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi (h2 hg1)
  obtain ⟨d₂, σ₂, -, -, hdσ₂⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi (h2 hg2)
  refine ⟨d₁, d₂, σ₁, σ₂, isKleinFrame_of_isCyclicRootTriple hp hD h4 hr hT hy0 hyH hyB
    he₁ he₂ ?_ ?_⟩
  · intro v
    rw [← hdσ₁]
    exact restrictHom_apply B V _ ⟨r 1, h1B⟩ v
  · intro v
    rw [← hdσ₂]
    exact restrictHom_apply B V _ ⟨r 2, h2B⟩ v

theorem centralizerSpace_inf_le_span_of_isCyclicRootTriple (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4) (hr : r 0 = h) (hT : IsCyclicRootTriple p H r e s)
    {y : U} (hy0 : y ≠ 0) (hyH : y ∈ centralizerSpace H)
    (hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B) :
    centralizerSpace (reflStab p H h) ⊓ HardMathSupport.Kantor79.commutatorSpace B ≤
      Submodule.span (ZMod p) {y} := by
  obtain ⟨-, -, -, -, -, -, -, hrmem, -⟩ :=
    exists_frame_of_isCyclicRootTriple hp hD h4 hr hT
  have h1B : r 1 ∈ B := hD.split.2.2.2.2 (hrmem 1 (by decide))
  have h2B : r 2 ∈ B := hD.split.2.2.2.2 (hrmem 2 (by decide))
  have he₁ := mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 1) (by decide)
  have he₂ := mem_commutatorSpace_of_isCyclicRootTriple hp hD h4 hr hT (i := 2) (by decide)
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let φ : B →* (V ≃ₗ[ZMod p] V) :=
    restrictHom B V fun _ hh _ hv => apply_mem_commutatorSpace hh hv
  have ht₁ : ∀ v : V, ((φ ⟨r 1, h1B⟩) v : U) = r 1 v :=
    fun v => restrictHom_apply B V _ ⟨r 1, h1B⟩ v
  have ht₂ : ∀ v : V, ((φ ⟨r 2, h2B⟩) v : U) = r 2 v :=
    fun v => restrictHom_apply B V _ ⟨r 2, h2B⟩ v
  have hK : IsKleinFrame (φ ⟨r 1, h1B⟩) (φ ⟨r 2, h2B⟩)
      ⟨e 1, he₁⟩ ⟨e 2, he₂⟩ ⟨y, hyB⟩ :=
    isKleinFrame_of_isCyclicRootTriple hp hD h4 hr hT hy0 hyH hyB he₁ he₂ ht₁ ht₂
  intro v hv
  obtain ⟨hvC, hvB⟩ := hv
  have hv1 : φ ⟨r 1, h1B⟩ ⟨v, hvB⟩ = ⟨v, hvB⟩ := by
    refine Subtype.ext ?_
    rw [ht₁]
    exact mem_centralizerSpace.mp hvC (r 1) (hrmem 1 (by decide))
  have hv2 : φ ⟨r 2, h2B⟩ ⟨v, hvB⟩ = ⟨v, hvB⟩ := by
    refine Subtype.ext ?_
    rw [ht₂]
    exact mem_centralizerSpace.mp hvC (r 2) (hrmem 2 (by decide))
  obtain ⟨γ, hγ⟩ := hK.eq_smul_of_apply_eq_self hp hv1 hv2
  refine Submodule.mem_span_singleton.mpr ⟨γ, ?_⟩
  simpa using (congrArg (fun w : V => (w : U)) hγ).symm

end CFSG.StandardType.ZS

end
