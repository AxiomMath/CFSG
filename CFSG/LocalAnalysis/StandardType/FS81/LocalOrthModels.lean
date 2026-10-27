module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthCore
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth
public import CFSG.LieType.ChevTwo.Orthogonal
public import CFSG.LieType.ChevTwo.OrthogonalAutEquiv
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.LieType.Universal.Spin

private theorem conjugation_transfer {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 2) → ZMod 2} {q : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    (e : ↥(StatedOmega Q₀) ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup q,
      TauCeti.QuadraticMap.orthogonalGroup q⁆)
    (hcoe : ∀ y : StatedOmega Q₀,
      ((e y : ↥⁅TauCeti.QuadraticMap.orthogonalGroup q,
        TauCeti.QuadraticMap.orthogonalGroup q⁆) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) (y : GL ι (ZMod 2)))
    {g : GL ι (ZMod 2)} {β : MulAut ↥(StatedOmega Q₀)}
    (hconj : ∀ y : StatedOmega Q₀,
      ((β y : StatedOmega Q₀) : GL ι (ZMod 2)) = g * (y : GL ι (ZMod 2)) * g⁻¹)
    (α : MulAut ↥⁅TauCeti.QuadraticMap.orthogonalGroup q,
      TauCeti.QuadraticMap.orthogonalGroup q⁆)
    (hα : α = MulAut.congr e β) :
    ∀ x, ((α x : ↥⁅TauCeti.QuadraticMap.orthogonalGroup q,
        TauCeti.QuadraticMap.orthogonalGroup q⁆) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g *
        (x : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) *
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g)⁻¹ := by
  intro x
  have hx : ((e (e.symm x) : _) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) =
      (x : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) := by
    rw [MulEquiv.apply_symm_apply]
  calc ((α x : ↥⁅TauCeti.QuadraticMap.orthogonalGroup q,
        TauCeti.QuadraticMap.orthogonalGroup q⁆) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))
      = ((e (β (e.symm x)) : _) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) := by
        conv_lhs => rw [hα]
        rfl
    _ = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
          ((β (e.symm x) : StatedOmega Q₀) : GL ι (ZMod 2)) := hcoe _
    _ = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
          (g * (((e.symm x : StatedOmega Q₀) : GL ι (ZMod 2))) * g⁻¹) := by
        rw [hconj (e.symm x)]
    _ = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g *
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)
            ((e.symm x : StatedOmega Q₀) : GL ι (ZMod 2)) *
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g)⁻¹ := by
        simp
    _ = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g *
          (x : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) *
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g)⁻¹ := by
        rw [← hcoe (e.symm x), hx]

theorem omegaAutIsometric_of_omegaTwoAutInduced {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 2) → ZMod 2} {q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hq : ⇑q = Q₀)
    (h : CFSG.LieType.ChevTwo.OmegaTwoAutInduced Q₀) : OmegaAutIsometric q := by
  intro α
  let e := CFSG.RankThree.PartOne.statedOmegaOrthEquiv (Q := q) (Q₀ := Q₀) hq
  have hcoe : ∀ y : StatedOmega Q₀,
      ((e y : ↥⁅TauCeti.QuadraticMap.orthogonalGroup q,
        TauCeti.QuadraticMap.orthogonalGroup q⁆) : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) (y : GL ι (ZMod 2)) :=
    CFSG.RankThree.PartOne.coe_statedOmegaOrthEquiv hq
  set β := (MulAut.congr e).symm α with hβ
  obtain ⟨g, hg, hconj⟩ := h β
  have hα : α = MulAut.congr e β := by
    rw [hβ]
    exact (MulEquiv.apply_symm_apply (MulAut.congr e) α).symm
  refine ⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) g, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hq]
    exact hg v
  · exact conjugation_transfer e hcoe hconj α hα

theorem omegaAutIsometric_quadPlus_six : OmegaAutIsometric (quadPlus 6 (ZMod 2)) :=
  omegaAutIsometric_of_omegaTwoAutInduced
    (CFSG.LieType.Universal.Spin.coe_quadPlus 6 (ZMod 2))
    (CFSG.LieType.ChevTwo.omegaTwoAutInduced.2 5 (by norm_num) (by norm_num))

theorem omegaAutIsometric_quadMinus {n : ℕ} (hn : 1 ≤ n) :
    OmegaAutIsometric (quadMinus (n + 1) (ZMod 2) 1 1) :=
  omegaAutIsometric_of_omegaTwoAutInduced
    (CFSG.LieType.Universal.Spin.coe_quadMinus (n + 1) (ZMod 2) 1 1)
    (CFSG.LieType.ChevTwo.omegaTwoAutInduced.1 n hn)

theorem omegaAutIsometric_quadMinus_seven : OmegaAutIsometric (quadMinus 7 (ZMod 2) 1 1) :=
  omegaAutIsometric_quadMinus (n := 6) (by norm_num)

theorem exists_totallySingular_three_quadPlus_six :
    ∃ T : Submodule (ZMod 2) (Fin 6 ⊕ Fin 6 → ZMod 2), finrank (ZMod 2) T = 3 ∧
      ∀ v ∈ T, quadPlus 6 (ZMod 2) v = 0 := by
  let f : Fin 3 → Fin 6 ⊕ Fin 6 := fun k => Sum.inl (Fin.castLE (by norm_num : 3 ≤ 6) k)
  let v : Fin 3 → (Fin 6 ⊕ Fin 6 → ZMod 2) := fun k => Pi.single (f k) 1
  have hf : Function.Injective f := by
    intro a b hab
    exact Fin.castLE_injective (by norm_num) (Sum.inl_injective hab)
  have hli : LinearIndependent (ZMod 2) v :=
    (Pi.linearIndependent_single_one (Fin 6 ⊕ Fin 6) (ZMod 2)).comp f hf
  refine ⟨Submodule.span (ZMod 2) (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · intro x hx
    refine CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span
      (Q := quadPlus 6 (ZMod 2)) ?_ ?_ hx
    · rintro u ⟨k, rfl⟩
      simp [v, f, quadPlus_apply, Pi.single_apply]
    · rintro u ⟨k, rfl⟩ w ⟨l, rfl⟩
      rw [polar_quadPlus]
      simp [v, f, Pi.single_apply]

private theorem quadMinus_single_inl (n : ℕ) (j : Fin n) :
    quadMinus (n + 1) (ZMod 2) 1 1
      (Pi.single (Sum.inl j) 1 : Fin n ⊕ Fin n ⊕ Fin 2 → ZMod 2) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

theorem exists_totallySingular_three_quadMinus {n : ℕ} (hn : 3 ≤ n) :
    ∃ T : Submodule (ZMod 2) (Fin n ⊕ Fin n ⊕ Fin 2 → ZMod 2), finrank (ZMod 2) T = 3 ∧
      ∀ v ∈ T, quadMinus (n + 1) (ZMod 2) 1 1 v = 0 := by
  let f : Fin 3 → Fin n ⊕ Fin n ⊕ Fin 2 := fun k => Sum.inl (Fin.castLE hn k)
  let v : Fin 3 → (Fin n ⊕ Fin n ⊕ Fin 2 → ZMod 2) := fun k => Pi.single (f k) 1
  have hf : Function.Injective f := by
    intro a b hab
    exact Fin.castLE_injective hn (Sum.inl_injective hab)
  have hli : LinearIndependent (ZMod 2) v :=
    (Pi.linearIndependent_single_one (Fin n ⊕ Fin n ⊕ Fin 2) (ZMod 2)).comp f hf
  refine ⟨Submodule.span (ZMod 2) (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · intro x hx
    refine CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span
      (Q := quadMinus (n + 1) (ZMod 2) 1 1) ?_ ?_ hx
    · rintro u ⟨k, rfl⟩
      exact quadMinus_single_inl n (Fin.castLE hn k)
    · rintro u ⟨k, rfl⟩ w ⟨l, rfl⟩
      rw [polar_quadMinus]
      simp [v, f, Pi.single_apply]

theorem exists_totallySingular_three_quadMinus_seven :
    ∃ T : Submodule (ZMod 2) (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2), finrank (ZMod 2) T = 3 ∧
      ∀ v ∈ T, quadMinus 7 (ZMod 2) 1 1 v = 0 :=
  exists_totallySingular_three_quadMinus (n := 6) (by norm_num)

theorem isSimpleGroup_and_mulEquiv_of_isRow_D6 {G : Type} [Group G] {K : Subgroup G}
    (hK : IsRow Row.D6 K) (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup ↥K ∧
      Nonempty (↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (ZMod 2)),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (ZMod 2))⁆) := by
  have hm : LargeEvenMarking K
      (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
    refine CFSG.StandardType.largeEvenMarking_mono (fun lab R _ I F θ hlab => ?_) hK
    obtain ⟨hn, h | h | h⟩ := hlab
    · exact ⟨h.2.1, h.2.2, hn⟩
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
  obtain ⟨e⟩ := CFSG.StandardType.FrameRoute.nonempty_mulEquiv_omegaPlusSix_of_marking hm hZ
  have hQ : CFSG.LieType.ChevTwo.GoodQ (StatedQuadPlus 6 (ZMod 2)) :=
    CFSG.LieType.ChevTwo.goodQ_plus (n := 5) (by norm_num)
  have : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 6 (ZMod 2))) := hQ.simple
  exact ⟨e.isSimpleGroup, ⟨e.trans (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
    (Q := quadPlus 6 (ZMod 2)) (Q₀ := StatedQuadPlus 6 (ZMod 2))
    (CFSG.LieType.Universal.Spin.coe_quadPlus 6 (ZMod 2)))⟩⟩

theorem isSimpleGroup_and_mulEquiv_of_isRow_twD {G : Type} [Group G] {K : Subgroup G} {r : ℕ}
    (hr : 4 ≤ r)
    (hm : LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = r ∧ lab.n = 1))
    (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup ↥K ∧
      Nonempty (↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus r (ZMod 2) 1 1),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus r (ZMod 2) 1 1)⁆) := by
  obtain ⟨-, lab, hlab, R, hR, I, F, θ, hs, hna, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists hm
  let : Group R := hR
  have : IsSimpleGroup R := hs
  have hq : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := θ.isSimpleGroup
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq
  have hsimple : IsSimpleGroup ↥K :=
    CFSG.RankThree.Classical2.isSimpleGroup_of_center_eq_bot hZ
  obtain ⟨e⟩ := CFSG.StandardType.FrameRoute.nonempty_mulEquiv_omegaMinus_of_marking hr hm hZ
  exact ⟨hsimple, ⟨e.trans (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
    (Q := quadMinus r (ZMod 2) 1 1) (Q₀ := StatedQuadMinus r (ZMod 2) 1 1)
    (CFSG.LieType.Universal.Spin.coe_quadMinus r (ZMod 2) 1 1))⟩⟩

theorem isSimpleGroup_and_mulEquiv_of_isRow_twD7 {G : Type} [Group G] {K : Subgroup G}
    (hK : IsRow Row.twD7 K) (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup ↥K ∧
      Nonempty (↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 (ZMod 2) 1 1),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 (ZMod 2) 1 1)⁆) := by
  have hm : LargeEvenMarking K
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) := by
    refine CFSG.StandardType.largeEvenMarking_mono (fun lab R _ I F θ hlab => ?_) hK
    obtain ⟨hn, h | h | h⟩ := hlab
    · exact absurd h.1 (by decide)
    · exact ⟨h.2.1, h.2.2, hn⟩
    · exact absurd h.1 (by decide)
  exact isSimpleGroup_and_mulEquiv_of_isRow_twD (r := 7) (by norm_num) hm hZ

end CFSG.StandardType.FrameRoute.FS81
