module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.ClassicalInvolution.WeakCT.Exceptional
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeCentralCover

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem weakCT_of_frame_pinned {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k ∧
        (D.rootGroup (sroot k)).map Ψ = Subgroup.closure (Set.range fun c => ρ k (tv 0 1 c)) ∧
        (D.rootGroup (-sroot k)).map Ψ = Subgroup.closure (Set.range fun c => ρ k (tv 1 0 c)) := by
  classical
  have hρU : ∀ k c, ρ k (tv 0 1 c) ∈ U k ∧ ρ k (tv 1 0 c) ∈ U k := fun k c => by
    rw [← (hρ k).2]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  have hfr : SimplyLacedFrame D F adj (fun k c => ρ k (tv 0 1 c)) (fun k c => ρ k (tv 1 0 c)) := by
    refine ⟨fun i j h => ?_, fun k => ⟨ρ k, fun c => ⟨rfl, rfl⟩⟩, fun i j hne h1 h2 c d => ?_⟩
    · obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j h
      refine ⟨ψ, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
      · show ψ (tv 0 1 c) = ρ i (tv 0 1 c)
        rw [← hψ0, MonoidHom.comp_apply, blk_zero_tv01]
      · show ψ (tv 1 0 c) = ρ i (tv 1 0 c)
        rw [← hψ0, MonoidHom.comp_apply, blk_zero_tv10]
      · show ψ (tv 1 2 c) = ρ j (tv 0 1 c)
        rw [← hψ1, MonoidHom.comp_apply, blk_one_tv01]
      · show ψ (tv 2 1 c) = ρ j (tv 1 0 c)
        rw [← hψ1, MonoidHom.comp_apply, blk_one_tv10]
    · have hc := hcomm i j hne h1 h2
      exact ⟨hc _ (hρU i c).1 _ (hρU j d).1, hc _ (hρU i c).1 _ (hρU j d).2,
        hc _ (hρU i c).2 _ (hρU j d).1, hc _ (hρU i c).2 _ (hρU j d).2⟩
  have hgen' : Subgroup.closure (⋃ k, Set.range (fun c => ρ k (tv 0 1 c)) ∪
      Set.range (fun c => ρ k (tv 1 0 c))) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← (hρ k).2]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl ⟨c, rfl⟩⟩)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr ⟨c, rfl⟩⟩)
  have hnt : ∃ k c, ρ k (tv 0 1 c) ≠ 1 := ⟨k₀, 1, fun h =>
    tv_zero_one_one_ne_one ((hρ k₀).1 (h.trans (map_one _).symm))⟩
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    exists_surjective_of_simplyLacedFrame hCT hL hD hfr hgen' hnt
  have hk : ∀ k, sroot k ∈ D.roots ∧ -sroot k ∈ D.roots := fun k =>
    ⟨single_mem_roots k, neg_mem_roots (single_mem_roots k)⟩
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ⟨?_, ?_, ?_⟩⟩
  · rw [CurtisTits.rankOne, Subgroup.map_sup]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨c, rfl⟩ := hD.surj _ (hk k).1 g hg
        rw [hΨu]
        exact (hρU k c).1
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨c, rfl⟩ := hD.surj _ (hk k).2 g hg
        rw [hΨv]
        exact (hρU k c).2
    · rw [← (hρ k).2]
      refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
      · refine Subgroup.mem_sup_left ⟨x (sroot k) c, hD.mem _ (hk k).1 c, ?_⟩
        exact hΨu k c
      · refine Subgroup.mem_sup_right ⟨x (-sroot k) c, hD.mem _ (hk k).2 c, ?_⟩
        exact hΨv k c
  · apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨g, hg, hgy⟩ := hy
      obtain ⟨c, hc⟩ := hD.surj _ (hk k).1 g hg
      rw [← hgy, ← hc, hΨu]
      exact Subgroup.subset_closure ⟨c, rfl⟩
    · rw [Subgroup.closure_le]
      rintro y ⟨c, rfl⟩
      show ρ k (tv 0 1 c) ∈ Subgroup.map Ψ (D.rootGroup (sroot k))
      rw [← hΨu]
      exact Subgroup.mem_map_of_mem Ψ (hD.mem _ (hk k).1 c)
  · apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨g, hg, hgy⟩ := hy
      obtain ⟨c, hc⟩ := hD.surj _ (hk k).2 g hg
      rw [← hgy, ← hc, hΨv]
      exact Subgroup.subset_closure ⟨c, rfl⟩
    · rw [Subgroup.closure_le]
      rintro y ⟨c, rfl⟩
      show ρ k (tv 1 0 c) ∈ Subgroup.map Ψ (D.rootGroup (-sroot k))
      rw [← hΨv]
      exact Subgroup.mem_map_of_mem Ψ (hD.mem _ (hk k).2 c)

theorem weakCT_of_frame_of_equiv_pinned {F₀ : Type} [Field F₀] (e : F₀ ≃+* F)
    {t : StatedLieTag} {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f)
    (hL : LeviConePresented D) (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin D.rank → SL(2, F₀) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F₀) →* X,
      ψ.comp (blk F₀ 0) = ρ i ∧ ψ.comp (blk F₀ 1) = ρ j) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k ∧
        (D.rootGroup (sroot k)).map Ψ =
          Subgroup.closure (Set.range fun c : F₀ => ρ k (tv 0 1 c)) ∧
        (D.rootGroup (-sroot k)).map Ψ =
          Subgroup.closure (Set.range fun c : F₀ => ρ k (tv 1 0 c)) := by
  let φ₂ : SL(2, F) →* SL(2, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F₀), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  have hmap01 : ∀ c : F, φ₂ (tv 0 1 c) = tv 0 1 (e.symm c) := by
    intro c
    show Matrix.SpecialLinearGroup.map e.symm.toRingHom (tv 0 1 c) = tv 0 1 (e.symm c)
    rw [tv_of_ne (by decide : (0 : Fin 2) ≠ 1) c,
      tv_of_ne (by decide : (0 : Fin 2) ≠ 1) (e.symm c),
      Matrix.SpecialLinearGroup.map_transvection]
    rfl
  have hmap10 : ∀ c : F, φ₂ (tv 1 0 c) = tv 1 0 (e.symm c) := by
    intro c
    show Matrix.SpecialLinearGroup.map e.symm.toRingHom (tv 1 0 c) = tv 1 0 (e.symm c)
    rw [tv_of_ne (by decide : (1 : Fin 2) ≠ 0) c,
      tv_of_ne (by decide : (1 : Fin 2) ≠ 0) (e.symm c),
      Matrix.SpecialLinearGroup.map_transvection]
    rfl
  have hrange01 : ∀ k, Set.range (fun c : F => (ρ k).comp φ₂ (tv 0 1 c)) =
      Set.range (fun c : F₀ => ρ k (tv 0 1 c)) := by
    intro k
    have h1 : Set.range (fun c : F => φ₂ (tv 0 1 c)) = Set.range (fun c : F₀ => tv 0 1 c) := by
      ext A
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨e.symm c, (hmap01 c).symm⟩
      · rintro ⟨c, rfl⟩
        refine ⟨e c, ?_⟩
        show φ₂ (tv 0 1 (e c)) = tv 0 1 c
        rw [hmap01 (e c)]
        simp
    calc Set.range (fun c : F => (ρ k).comp φ₂ (tv 0 1 c))
        = Set.range ((ρ k) ∘ (fun c : F => φ₂ (tv 0 1 c))) := rfl
      _ = (ρ k) '' Set.range (fun c : F => φ₂ (tv 0 1 c)) := Set.range_comp _ _
      _ = (ρ k) '' Set.range (fun c : F₀ => tv 0 1 c) := by rw [h1]
      _ = Set.range ((ρ k) ∘ (fun c : F₀ => tv 0 1 c)) := (Set.range_comp _ _).symm
      _ = Set.range (fun c : F₀ => ρ k (tv 0 1 c)) := rfl
  have hrange10 : ∀ k, Set.range (fun c : F => (ρ k).comp φ₂ (tv 1 0 c)) =
      Set.range (fun c : F₀ => ρ k (tv 1 0 c)) := by
    intro k
    have h1 : Set.range (fun c : F => φ₂ (tv 1 0 c)) = Set.range (fun c : F₀ => tv 1 0 c) := by
      ext A
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨e.symm c, (hmap10 c).symm⟩
      · rintro ⟨c, rfl⟩
        refine ⟨e c, ?_⟩
        show φ₂ (tv 1 0 (e c)) = tv 1 0 c
        rw [hmap10 (e c)]
        simp
    calc Set.range (fun c : F => (ρ k).comp φ₂ (tv 1 0 c))
        = Set.range ((ρ k) ∘ (fun c : F => φ₂ (tv 1 0 c))) := rfl
      _ = (ρ k) '' Set.range (fun c : F => φ₂ (tv 1 0 c)) := Set.range_comp _ _
      _ = (ρ k) '' Set.range (fun c : F₀ => tv 1 0 c) := by rw [h1]
      _ = Set.range ((ρ k) ∘ (fun c : F₀ => tv 1 0 c)) := (Set.range_comp _ _).symm
      _ = Set.range (fun c : F₀ => ρ k (tv 1 0 c)) := rfl
  have hρ' : ∀ k, Function.Injective ((ρ k).comp φ₂) ∧ ((ρ k).comp φ₂).range = U k := by
    intro k
    refine ⟨(hρ k).1.comp hφ₂inj, ?_⟩
    rw [← (hρ k).2]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  have hψ' : ∀ i j, adj i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = (ρ i).comp φ₂ ∧ ψ.comp (blk F 1) = (ρ j).comp φ₂ := by
    intro i j hij
    obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
    refine ⟨ψ.comp φ₃, ?_, ?_⟩
    · ext A
      show ψ (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 0 A)
    · ext A
      show ψ (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 1 A)
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, hpin⟩ :=
    weakCT_of_frame_pinned hCT hL hD k₀ hgen hcomm hρ' hψ'
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ⟨(hpin k).1, ?_, ?_⟩⟩
  · rw [(hpin k).2.1, hrange01 k]
  · rw [(hpin k).2.2, hrange10 k]

end CFSG.ClassicalInvolution.WeakCT

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.Chevalley
open scoped MatrixGroups

theorem weakCT_e6_of_frame_pinned (p f : ℕ) [Fact p.Prime]
    (hadm : StatedLieAdmissible .E6 0 p f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (U : Fin 6 → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin 6 → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin 6, edgeE 6 i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E6 0 p f ∧
      ∀ k : Fin 6,
        ((Steinberg.Minuscule.e6Datum (GaloisField p f)).rootGroup (sroot k)).map Ψ =
            Subgroup.closure (Set.range fun c : F => ρ k (tv 0 1 c)) ∧
        ((Steinberg.Minuscule.e6Datum (GaloisField p f)).rootGroup (-sroot k)).map Ψ =
            Subgroup.closure (Set.range fun c : F => ρ k (tv 1 0 c)) := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e6Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Minuscule.e6Datum (GaloisField p f)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E6) (Or.inl rfl)
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
    (Steinberg.Minuscule.e6_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC (GaloisField p f)
        Steinberg.Minuscule.posDef_cartan_E6 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e6Data_valid.commC_natAbs (GaloisField p f) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e6Datum_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 6) => by
      have h := (Steinberg.Minuscule.e6Datum_isCTGroupDatum (GaloisField p f)).sq_mem k
      have e := Steinberg.Minuscule.e6Data_valid.weylElement_xm (GaloisField p f) k 1
      rw [e]
      exact h)
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, hpin⟩ := weakCT_of_frame_of_equiv_pinned e
    (CurtisTits.curtisTitsConclusion_e6 p f hadm) (leviConePresented_e6 _) hD
    (⟨0, by norm_num⟩ : Fin 6) hgen hcomm hρ hψ
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ⟨(hpin k).2.1, (hpin k).2.2⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
