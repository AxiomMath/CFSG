module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
public import CFSG.RankThree.PartTwo.KFacts.KS21L44
import CFSG.RankThree.PartTwo.KFacts.KS21SylowL44
import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeL44
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.SL44

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedSL StatedProj)
open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4 card_units_F4 units_pow_three)
open Matrix

theorem transvection_mul_diagonal {n : ℕ} {K : Type*} [Field K] {d : Fin n → K} {i j : Fin n}
    (hij : i ≠ j) (hd : d i = d j) (c : K) :
    Matrix.transvection i j c * diagonal d = diagonal d * Matrix.transvection i j c := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hd, mul_comm]
  · have h' : ¬ (i = a ∧ j = b) := fun h2 => h ⟨h2.1.symm, h2.2.symm⟩
    by_cases hab : a = b
    · subst hab
      simp [h']
    · simp [h', hab]

@[expose] noncomputable def prodHom : (Fin 4 → F4ˣ) →* F4ˣ where
  toFun t := ∏ k, t k
  map_one' := by simp
  map_mul' s t := by simp [Finset.prod_mul_distrib]

theorem prodHom_mulSingle (i : Fin 4) (y : F4ˣ) : prodHom (Pi.mulSingle i y) = y := by
  simp [prodHom]

@[expose] noncomputable def torus : Subgroup (Fin 4 → F4ˣ) := prodHom.ker

theorem mem_torus {t : Fin 4 → F4ˣ} : t ∈ torus ↔ ∏ k, t k = 1 := MonoidHom.mem_ker

theorem card_torus : Nat.card torus = 27 := by
  have h1 := Subgroup.card_mul_index prodHom.ker
  have h2 : prodHom.ker.index = 3 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr fun y => ⟨_, prodHom_mulSingle 0 y⟩,
      Subgroup.card_top, card_units_F4]
  have h3 : Nat.card (Fin 4 → F4ˣ) = 3 ^ 4 := by
    rw [Nat.card_fun, card_units_F4, Nat.card_fin]
  have h4 : (3 : ℕ) ^ 4 = 81 := by norm_num
  rw [h2, h3, h4] at h1
  change Nat.card prodHom.ker = 27
  omega

theorem det_diagonal_torus (t : torus) :
    (diagonal fun k => ((t : Fin 4 → F4ˣ) k : F4)).det = 1 := by
  rw [det_diagonal, ← Units.coe_prod, mem_torus.mp t.2, Units.val_one]

@[expose] noncomputable def diagSL : torus →* SpecialLinearGroup (Fin 4) F4 where
  toFun t := ⟨diagonal fun k => ((t : Fin 4 → F4ˣ) k : F4), det_diagonal_torus t⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' s t := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1

theorem coe_diagSL (t : torus) :
    ((diagSL t : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
      diagonal fun k => ((t : Fin 4 → F4ˣ) k : F4) := rfl

theorem diagSL_injective : Function.Injective diagSL := by
  intro s t hst
  have h := congrArg (fun g : SpecialLinearGroup (Fin 4) F4 =>
    (g : Matrix (Fin 4) (Fin 4) F4)) hst
  simp only [coe_diagSL] at h
  apply Subtype.ext
  funext k
  apply Units.ext
  simpa using congrFun₂ h k k

@[expose] noncomputable def D₀ : Subgroup (SpecialLinearGroup (Fin 4) F4) := diagSL.range

theorem card_D₀ : Nat.card D₀ = 27 := by
  rw [D₀, ← Nat.card_congr (MonoidHom.ofInjective diagSL_injective).toEquiv, card_torus]

theorem isElemAbelian_D₀ : CFSG.Assembly.IsElemAbelian 3 D₀ := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    change (a : SpecialLinearGroup (Fin 4) F4) * b = b * a
    rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm s t]
  · intro x hx
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_pow]
    have h3 : t ^ 3 = 1 := by
      apply Subtype.ext
      funext k
      simp [units_pow_three]
    rw [h3, map_one]

@[expose] noncomputable def ratio (i j : Fin 4) : torus →* F4ˣ :=
  MonoidHom.mk' (fun t => (t : Fin 4 → F4ˣ) i * ((t : Fin 4 → F4ˣ) j)⁻¹) fun s t => by
    simp only [Subgroup.coe_mul, Pi.mul_apply, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem ratio_apply (i j : Fin 4) (t : torus) :
    ratio i j t = (t : Fin 4 → F4ˣ) i * ((t : Fin 4 → F4ˣ) j)⁻¹ := rfl

theorem ratio_surjective {i j : Fin 4} (hij : i ≠ j) : Function.Surjective (ratio i j) := by
  have hk : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hk i j
  intro y
  refine ⟨⟨Pi.mulSingle i y * Pi.mulSingle k y⁻¹, MonoidHom.mem_ker.mpr ?_⟩, ?_⟩
  · rw [map_mul, prodHom_mulSingle, prodHom_mulSingle, mul_inv_cancel]
  · rw [ratio_apply]
    simp [hij.symm, hki.symm, hkj.symm]

theorem card_ker_ratio {i j : Fin 4} (hij : i ≠ j) : Nat.card (ratio i j).ker = 9 := by
  have h1 := Subgroup.card_mul_index (ratio i j).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ratio_surjective hij), Subgroup.card_top,
    card_units_F4, card_torus] at h1
  omega

theorem transvection_mem_hyperCent (t : TransvectionStruct (Fin 4) F4) :
    t.toSpecialLinearGroup ∈ hyperCent D₀ := by
  refine ⟨(ratio t.i t.j).ker.map diagSL, Subgroup.map_le_range _ _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective diagSL_injective, card_ker_ratio t.hij, card_D₀]
  · rintro _ ⟨s, hs, rfl⟩
    have hs1 : ratio t.i t.j s = 1 := hs
    rw [ratio_apply, mul_inv_eq_one] at hs1
    have hd := transvection_mul_diagonal (d := fun k => ((s : Fin 4 → F4ˣ) k : F4)) t.hij
      (congrArg Units.val hs1) t.c
    exact Subtype.ext hd.symm

theorem closure_hyperCent_D₀ : Subgroup.closure (hyperCent D₀) = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 4) (K := F4), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact Subgroup.subset_closure (transvection_mem_hyperCent t)

theorem map_mem_hyperCent {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) {P : Subgroup X}
    {x : X} (hx : x ∈ hyperCent P) : ψ x ∈ hyperCent (P.map ψ.toMonoidHom) := by
  obtain ⟨R, hRP, hR3, hRx⟩ := hx
  refine ⟨R.map ψ.toMonoidHom, Subgroup.map_mono hRP, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective ψ.injective, Subgroup.card_map_of_injective ψ.injective,
      hR3]
  · rintro _ ⟨r, hr, rfl⟩
    change ψ r * ψ x = ψ x * ψ r
    rw [← map_mul, ← map_mul, hRx r hr]

theorem closure_hyperCent_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    {P : Subgroup X} (hP : Subgroup.closure (hyperCent P) = ⊤) :
    Subgroup.closure (hyperCent (P.map ψ.toMonoidHom)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : ψ.symm y ∈ Subgroup.closure (hyperCent P) := by
    rw [hP]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem ψ.toMonoidHom hy
  rw [MonoidHom.map_closure] at h1
  have h2 : ψ.toMonoidHom (ψ.symm y) = y := ψ.apply_symm_apply y
  rw [h2] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_hyperCent ψ hx

theorem center_projSL : Subgroup.center (projSL 4 F4) = ⊥ :=
  KFacts.KS21.center_eq_bot_of_mulEquiv KFacts.KS21.L44.equivSL.symm KFacts.KS21.L44.center_M

theorem mem_range_conj_projSL (φ : MulAut (projSL 4 F4)) (hφ : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : projSL 4 F4 →* MulAut (projSL 4 F4)).range := by
  set ψ := CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 4 F4 with hψ
  have hα : ∃ k : ℕ, MulAut.congr ψ φ ^ 3 ^ k = 1 :=
    ⟨1, by rw [pow_one, ← map_pow, hφ, map_one]⟩
  obtain ⟨y, hy⟩ := KFacts.KS21.L44.mem_range_conj_of_pow _ hα
  refine ⟨ψ.symm y, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun β : MulAut _ => β (ψ x)) hy
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply ψ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem statedScalars_subgroupOf_eq_bot :
    (StatedScalars (Fin 4) F4).subgroupOf (StatedSL 4 F4) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hdet : GeneralLinearGroup.det (x : GL (Fin 4) F4) = 1 :=
    MonoidHom.mem_ker.mp ((CFSG.RankThree.PartTwo.Census.statedSL_eq_ker_det 4 F4).le x.2)
  rw [← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc1 : c = 1 := by
    rw [show c ^ 4 = c ^ 3 * c by rw [pow_succ], units_pow_three c, one_mul] at hdet
    exact hdet
  rw [Subgroup.mem_bot, Subtype.ext_iff, Subgroup.coe_one, ← hc, hc1, map_one]

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 4 F4) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨φ, -, -, hD⟩ := CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map
    (K := F4) (n := 4) (by norm_num) hodd
    (e.trans ((MulEquiv.subgroupCongr
      (CFSG.RankThree.PartTwo.Census.projImage_statedSL 4 F4)).symm.trans
      (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSL 4 F4)).symm))
  rw [← hD, statedScalars_subgroupOf_eq_bot, Subgroup.map_bot]

theorem false_of_ctx (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 4 F4) : False := by
  have hZ := center_layer_eq_bot h e
  set ψ : SpecialLinearGroup (Fin 4) F4 ≃* projSL 4 F4 := KFacts.KS21.L44.equivSL.symm with hψ
  have hDe : CFSG.Assembly.IsElemAbelian 3 (D₀.map ψ.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ D₀ isElemAbelian_D₀
  have hD27 : Nat.card (D₀.map ψ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective ψ.injective, card_D₀]
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · exact Item434Spor.false_of_card_nine h hZ e hDe hD27 h9
  · refine false_of_gen_of_inner h hZ e mem_range_conj_projSL center_projSL fun P hP hPc => ?_
    rw [h27] at hPc
    obtain ⟨g, rfl⟩ := exists_map_conj_of_maxEA KFacts.KS21.L44.maxEA_projSL hDe hD27 hP hPc
    exact closure_hyperCent_map_conj (closure_hyperCent_map_mulEquiv ψ closure_hyperCent_D₀) g

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.SL44

namespace CFSG.RankThree.PartTwo.Sec4

section Families


theorem item434SmallTwoOtherAtL44 : Item434SmallTwoOtherAtL44 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.SL44.false_of_ctx hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
