module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroDataDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxSat
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

private theorem closure_range_simple_coe_eq_top {ι : Type} {M : CoxeterMatrix ι}
    {E : Type} [Group E] {A : Subgroup E} (e : M.Group ≃* ↥A) :
    Subgroup.closure (Set.range fun i => ((e (M.simple i) : ↥A) : E)) = A := by
  have hgen := (M.toCoxeterSystem).subgroup_closure_range_simple
  have himg : Subgroup.map e.toMonoidHom
      (Subgroup.closure (Set.range M.toCoxeterSystem.simple)) =
      Subgroup.closure (Set.range fun i => e (M.simple i)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [CoxeterMatrix.toCoxeterSystem_simple]; rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.toCoxeterSystem.simple i, ⟨i, rfl⟩,
        by rw [CoxeterMatrix.toCoxeterSystem_simple]; rfl⟩
  have hmap : Subgroup.map e.toMonoidHom (⊤ : Subgroup M.Group) = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
  rw [hgen, hmap] at himg
  have hsub : Subgroup.map (Subgroup.subtype A)
      (Subgroup.closure (Set.range fun i => e (M.simple i))) =
      Subgroup.closure (Set.range fun i => ((e (M.simple i) : ↥A) : E)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e (M.simple i), ⟨i, rfl⟩, rfl⟩
  rw [← himg, Subgroup.map_top, Subgroup.range_subtype] at hsub
  exact hsub.symm

theorem ggCZ_data_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hFix : GGSecFiveFixInput)
    (hRootGenL : GGSecFiveRootGenLInput)
    (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) (hxBs : x ∈ Bs)
    (hfix : ∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩) :
    GGCaseZeroData p B Bs x L D J 𝒦 := by
  obtain ⟨ιL, instL, ML, hML, hAL, -, -⟩ := ggRM_frame_L hFix hcfg hsplit
  exact ⟨hcfg, hxBs, hfix, ggRM_saturated hL hP hRootGenL hcfg hsplit hxBs,
    ⟨ιL, instL, ML, hML, hAL⟩, hFix G p B Bs x L D J 𝒦 hcfg hsplit⟩

theorem GGCaseZeroData.basic (h : GGCaseZeroData p B Bs x L D J 𝒦) :
    p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧ GGNoTransvection p Bs := by
  obtain ⟨hp, hBs, -, -, -⟩ := h.cfg.1.1.tableB_facts
  exact ⟨hp, h.cfg.1.1.1.2.2.2.2.2.1.2.1, hBs, h.cfg.1.2.2.2.1⟩

theorem GGCaseZeroData.join_le_ainf (h : GGCaseZeroData p B Bs x L D J 𝒦) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J :=
  GGNbrSet.automizerJoin_le_ggAInf h.cfg.2.2.2.1

theorem GGCaseZeroData.normal (h : GGCaseZeroData p B Bs x L D J 𝒦) :
    ∀ g ∈ ggAInf p B Bs x L D J, ∀ a ∈ ggAutomizer L Bs, g * a * g⁻¹ ∈ ggAutomizer L Bs := by
  have hLA : ggAutomizer L Bs ≤ ggAInf p B Bs x L D J := by
    rw [ggAInf]
    exact le_sup_left
  obtain ⟨ιL, instL, ML, -, ⟨e, he⟩⟩ := h.frame
  have hclosure := closure_range_simple_coe_eq_top (A := ggAutomizer L Bs) e
  intro g hg a ha
  rw [← hclosure] at ha
  refine Subgroup.closure_induction
    (p := fun a _ => g * a * g⁻¹ ∈ ggAutomizer L Bs) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨i, rfl⟩
    set r : MulAut ↥Bs := ((e (ML.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) with hr
    have hrefl : GGIsReflection p r := he i
    have hrA : r ∈ ggAutomizer L Bs := (e (ML.simple i)).2
    have hconj : GGIsReflection p (g * r * g⁻¹) := GGIsReflection.conj hrefl g
    have hconjA : g * r * g⁻¹ ∈ ggAInf p B Bs x L D J :=
      (ggAInf p B Bs x L D J).mul_mem
        ((ggAInf p B Bs x L D J).mul_mem hg (hLA hrA))
        ((ggAInf p B Bs x L D J).inv_mem hg)
    have hfix : (g * r * g⁻¹) ⟨x, h.mem⟩ = ⟨x, h.mem⟩ := by
      simp only [MulAut.mul_apply]
      rw [h.fix g⁻¹ ((ggAInf p B Bs x L D J).inv_mem hg), h.fix r (hLA hrA), h.fix g hg]
    exact h.sat (g * r * g⁻¹) hconjA hconj hfix ⟨g, hg, r, hrA, hrefl, rfl⟩
  · simp
  · intro a b _ _ ha hb
    have h : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h]
    exact (ggAutomizer L Bs).mul_mem ha hb
  · intro a _ ha
    have h : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [h]
    exact (ggAutomizer L Bs).inv_mem ha

theorem GGCaseZeroData.AL_noncomm (h : GGCaseZeroData p B Bs x L D J 𝒦) :
    ∃ r ∈ ggAutomizer L Bs, ∃ r' ∈ ggAutomizer L Bs, GGIsReflection p r ∧ GGIsReflection p r' ∧
      r * r' ≠ r' * r := by
  obtain ⟨ιL, instL, ML, hML, hAL⟩ := h.frame
  obtain ⟨e, he⟩ := hAL
  have hW : GGIsWeylMatrix ML := hML.elim GGIsWeylMatrixAD.isWeylMatrix
    GGIsWeylMatrixE.isWeylMatrix
  have h3 : ∀ i j : ιL, i ≠ j → ML.M i j ≤ 3 := hML.elim
    (fun h' => GGIsWeylMatrixAD.le_three h') (fun h' => GGIsWeylMatrixE.le_three h')
  have hSL : GGSimplyLaced ML := (ggSimplyLacedConnected_of_weyl hW h3).1
  have hlabel : ∃ i j : ιL, ML.M i j = 3 := by
    rcases hML with hAD | hE
    · rcases hAD with ⟨n, en, hn, hMeq⟩ | ⟨n, en, hn, hMeq⟩
      · refine ⟨en ⟨0, by omega⟩, en ⟨1, by omega⟩, ?_⟩
        rw [hMeq, coxeterMatrix_reindex_apply_equiv]
        exact coxeterMatrixA_eq_three n ⟨0, by omega⟩ ⟨1, by omega⟩ rfl
      · have h1n : 1 < n := by omega
        have h2n : 2 < n := by omega
        refine ⟨en ⟨0, by omega⟩, en ⟨1, h1n⟩, ?_⟩
        rw [hMeq, coxeterMatrix_reindex_apply_equiv]
        exact ggCoxeterMatrixD_eq_three hn ⟨0, by omega⟩ ⟨1, h1n⟩ (Or.inl ⟨rfl, h2n⟩)
    · rcases hE with ⟨en, hMeq⟩ | ⟨en, hMeq⟩ | ⟨en, hMeq⟩
      · refine ⟨en ⟨2, by omega⟩, en ⟨3, by omega⟩, ?_⟩
        rw [hMeq, coxeterMatrix_reindex_apply_equiv]
        exact coxeterMatrixE6_eq_three ⟨2, by omega⟩ ⟨3, by omega⟩
          (Or.inr (Or.inr ⟨le_rfl, rfl⟩))
      · refine ⟨en ⟨2, by omega⟩, en ⟨3, by omega⟩, ?_⟩
        rw [hMeq, coxeterMatrix_reindex_apply_equiv]
        exact coxeterMatrixE7_eq_three ⟨2, by omega⟩ ⟨3, by omega⟩
          (Or.inr (Or.inr ⟨le_rfl, rfl⟩))
      · refine ⟨en ⟨2, by omega⟩, en ⟨3, by omega⟩, ?_⟩
        rw [hMeq, coxeterMatrix_reindex_apply_equiv]
        exact coxeterMatrixE8_eq_three ⟨2, by omega⟩ ⟨3, by omega⟩
          (Or.inr (Or.inr ⟨le_rfl, rfl⟩))
  obtain ⟨i, j, hij⟩ := hlabel
  have hnoncomm : ML.simple i * ML.simple j ≠ ML.simple j * ML.simple i :=
    ggSimplyLaced_simple_noncomm hSL hij
  refine ⟨((e (ML.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs), (e (ML.simple i)).2,
    ((e (ML.simple j) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs), (e (ML.simple j)).2, he i, he j, ?_⟩
  intro hcomm
  apply hnoncomm
  apply e.injective
  apply Subtype.val_injective
  simpa [map_mul] using hcomm

theorem GGCaseZeroData.le_AL_of_simplyLaced (h : GGCaseZeroData p B Bs x L D J 𝒦)
    {H : Subgroup (MulAut ↥Bs)} (hLH : ggAutomizer L Bs ≤ H) (hHA : H ≤ ggAInf p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) (hSL : GGSimplyLacedConnected M)
    (f : M.Group ≃* ↥H) (hf : ∀ i, GGIsReflection p ((f (M.simple i) : ↥H) : MulAut ↥Bs)) :
    H ≤ ggAutomizer L Bs := by
  obtain ⟨hp, hp2, hEl, hNT⟩ := h.basic
  obtain ⟨r, hrA, -, -, hrrefl, -, -⟩ := h.AL_noncomm
  have hHind : (H : Set (MulAut ↥Bs)) ⊆ ggInduced ⊤ Bs :=
    fun φ hφ => ggRM_ainf_le_induced (hHA hφ)
  have hnotG2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨en, rfl⟩
    have hne : en 0 ≠ en 1 := by
      intro hh
      have hv := congrArg Fin.val (en.injective hh)
      norm_num at hv
    have hlab := hSL.1 (en 0) (en 1) hne
    have h6 : (CoxeterMatrix.G₂.reindex en).M (en 0) (en 1) = 6 := by
      rw [CoxeterMatrix.reindex_apply]
      simp [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
    rw [h6] at hlab
    rcases hlab with hlab | hlab <;> omega
  obtain ⟨i, g, hg⟩ :=
    SecFiveRootRefl.ggSecFiveRootReflInput_holds (G := G) (p := p) (Bs := Bs)
      hp hp2 hEl hNT H hHind ι M hM hnotG2 f hf ⟨r, hLH hrA⟩ hrrefl
  have hmem : ∀ j : ι, ((f (M.simple j) : ↥H) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
    intro j
    obtain ⟨w, hw⟩ := ggSimplyLaced_simple_conj hSL i j
    let F : M.Group →* MulAut ↥Bs := (Subgroup.subtype H).comp f.toMonoidHom
    have hrF : r = F (g * M.simple i * g⁻¹) := by
      have h := congrArg Subtype.val hg
      simpa [F] using h
    have hkey : F (M.simple j) = F (w * g⁻¹) * r * F (w * g⁻¹)⁻¹ := by
      rw [hrF, hw]
      simp only [map_mul, map_inv]
      group
    have hmemA : F (M.simple j) ∈ ggAInf p B Bs x L D J := hHA (f (M.simple j)).2
    have hfix : F (M.simple j) ⟨x, h.mem⟩ = ⟨x, h.mem⟩ := h.fix _ hmemA
    have hrefl : GGIsReflection p (F (M.simple j)) := by simpa [F] using hf j
    refine h.sat (F (M.simple j)) hmemA hrefl hfix
      ⟨F (w * g⁻¹), hHA (f (w * g⁻¹)).2, r, hrA, hrrefl, ?_⟩
    simpa [F] using hkey
  rw [← closure_range_simple_coe_eq_top (A := H) f]
  intro y hy
  refine Subgroup.closure_induction
    (p := fun y _ => y ∈ ggAutomizer L Bs) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨j, rfl⟩
    exact hmem j
  · exact (ggAutomizer L Bs).one_mem
  · intro a b _ _ ha hb
    exact (ggAutomizer L Bs).mul_mem ha hb
  · intro a _ ha
    exact (ggAutomizer L Bs).inv_mem ha

theorem GGCaseZeroData.nbr_le_of_join_eq (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (hEq : ggAutomizerJoin L Bs 𝒦 = ggAutomizer L Bs) :
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizer L Bs := by
  intro y K hK
  have hW : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    h.cfg.1.2.2.2.2.1 y K hK (h.cfg.2.1 y K hK) (Or.inr h.cfg.2.1)
  have hset : GGNbrSet p B x D J {K} := by
    refine ⟨by simp, fun K' hK' => ⟨y, ?_⟩⟩
    rw [Finset.mem_singleton.mp hK']
    exact hK
  have hcard := h.cfg.2.2.2.2.2 {K} hset (by rwa [ggAutomizerJoin_singleton])
  rw [ggAutomizerJoin_singleton, hEq] at hcard
  have hle : ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := le_sup_left
  rw [Subgroup.eq_of_le_of_card_ge hle hcard]
  exact le_sup_right

theorem GGCaseZeroData.witness_of_refl_mem (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (hrefl : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ∀ t ∈ ggAutomizer K Bs,
      GGIsReflection p t → t ∈ ggAutomizerJoin L Bs 𝒦) :
    GGSecFiveInfWitness p B Bs x L D J := by
  have hle : ggAInf p B Bs x L D J ≤ ggAutomizerJoin L Bs 𝒦 := by
    rw [ggAInf]
    refine sup_le (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)) ?_
    refine iSup_le fun y => iSup_le fun K => iSup_le fun hK => ?_
    exact (h.cfg.2.1 y K hK).le.trans
      ((Subgroup.closure_le _).mpr fun t ht => hrefl y K hK t ht.1 ht.2)
  have heq : ggAutomizerJoin L Bs 𝒦 = ggAInf p B Bs x L D J := le_antisymm h.join_le_ainf hle
  exact ⟨heq ▸ h.cfg.2.2.2.2.1, 𝒦, h.cfg.2.2.2.1, heq⟩

end

end CFSG.StandardType

end
