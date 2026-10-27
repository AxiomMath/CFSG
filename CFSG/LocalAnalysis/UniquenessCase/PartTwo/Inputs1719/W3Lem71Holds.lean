module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwoUncond
public import CFSG.RepresentationTheory.SzMartineau.MartineauInput
public import CFSG.CGT.Timmesfeld75.BenderInputs3
public import CFSG.GroupTheory.SubgroupOfSupIndep

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

section Transfer

open Matrix

variable {G : Type} [Group G]

theorem isNaturalSum_subgroupOf {X M : Subgroup G} {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (act : ↥X → Matrix ι ι F) (s : Finset (Subgroup G)) (hs : s.SupIndep id)
    (hsM : s.sup id = M) (hMX : M ≤ X)
    (hsW : ∀ W ∈ s, W ≤ M ∧ X ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
        ∀ U : Subgroup G, U ≤ W → X ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = W)
    (hθ : ∀ W ∈ s, ∃ θ : (ι → F) → G, (∀ v v', θ (v + v') = θ v * θ v') ∧
        Function.Injective θ ∧ Set.range θ = W ∧
        ∀ (x : ↥X) (v : ι → F), θ (act x *ᵥ v) = x * θ v * x⁻¹) :
    IsNaturalSum act (M.subgroupOf X) := by
  classical
  refine ⟨s.image fun W => W.subgroupOf X, CFSG.GroupTheory.supIndep_image_subgroupOf hs, ?_, ?_⟩
  · rw [CFSG.GroupTheory.sup_image_subgroupOf s (fun W hW => (hsW W hW).1.trans hMX), hsM]
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hW'
    obtain ⟨hWM, hXW, hW1, hirr⟩ := hsW W hW
    have hWX : W ≤ X := hWM.trans hMX
    refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hXW, ?_, ?_, ?_⟩
    · intro h
      apply hW1
      rw [← Subgroup.map_subgroupOf_eq_of_le hWX, h, Subgroup.map_bot]
    · intro U' hU'W hU'n
      have hmapW : U'.map X.subtype ≤ W := by
        intro y hy
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_subgroupOf.mp (hU'W hu)
      have hXn : X ≤ Subgroup.normalizer ((U'.map X.subtype : Subgroup G) : Set G) := by
        have h1 := Subgroup.le_normalizer_map (H := U') X.subtype
        rw [Subgroup.normalizer_eq_top_iff.mpr hU'n] at h1
        intro x hx
        exact h1 (Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩)
      rcases hirr _ hmapW hXn with h | h
      · left
        exact (Subgroup.map_eq_bot_iff_of_injective U' X.subtype_injective).mp h
      · right
        apply Subgroup.map_injective X.subtype_injective
        rw [h, Subgroup.map_subgroupOf_eq_of_le hWX]
    · obtain ⟨θ, hadd, hinj, hrange, hconj⟩ := hθ W hW
      have hmem : ∀ v, θ v ∈ W := fun v => by
        have h : θ v ∈ Set.range θ := Set.mem_range_self v
        rw [hrange] at h
        exact h
      refine ⟨fun v => ⟨θ v, hWX (hmem v)⟩, ?_, ?_, ?_, ?_⟩
      · intro v v'
        exact Subtype.ext (hadd v v')
      · intro v v' h
        exact hinj (congrArg Subtype.val h)
      · ext y
        constructor
        · rintro ⟨v, rfl⟩
          exact Subgroup.mem_subgroupOf.mpr (hmem v)
        · intro hy
          have hy' : (y : G) ∈ Set.range θ := by
            rw [hrange]
            exact Subgroup.mem_subgroupOf.mp hy
          obtain ⟨v, hv⟩ := hy'
          exact ⟨v, Subtype.ext hv⟩
      · intro x v
        exact Subtype.ext (hconj x v)

end Transfer

section Main

variable {G : Type} [Group G] [Finite G]


open Matrix in
theorem w3Lem71_holds : W3Lem71 G := by
  intro V g hV7 hg
  dsimp only
  intro hU hUV _hcomm
  obtain ⟨hV, -, hTI⟩ := hV7
  have hgV : conjSubgroup V g ≠ V := fun h => hg (conjSubgroup_eq_iff_mem_normalizer.mp h)
  have hO : pCoreOf 2 (V ⊔ conjSubgroup V g) = nVSub V g ⊔ bSub V g := by
    have h := pCoreOf_sup_conj_eq hV hTI (a := 1) (b := g)
      (by rw [conjSubgroup_one]; exact hgV.symm) (by rw [conjSubgroup_one]; exact hU)
      (by
        rw [conjSubgroup_one]
        intro hle
        exact hUV (le_antisymm inf_le_left (le_inf le_rfl hle)))
    rw [conjSubgroup_one] at h
    exact h
  have S := prop24Setup hV hTI hU hUV
  obtain ⟨hN, -, hshape⟩ := S.tim77_2_4_one CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  obtain ⟨s, hs, hsM, hsW, hmod⟩ := S.tim77_2_4_two CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
    CFSG.RepresentationTheory.SzMartineau.martineauSzInput_holds
  have hMX : nVSub V g ⊔ bSub V g ≤ V ⊔ conjSubgroup V g :=
    sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hker : ∀ k : ↥(V ⊔ conjSubgroup V g),
      k ∈ (nVSub V g ⊔ bSub V g).subgroupOf (V ⊔ conjSubgroup V g) ↔
        (k : G) ∈ pCoreOf 2 (V ⊔ conjSubgroup V g) := by
    intro k
    rw [hO, Subgroup.mem_subgroupOf]
  have hmQ : ∀ n : ℕ, (nVSub V g).relIndex V = 2 ^ n → E3.mQuot V (nVSub V g) = n := by
    intro n h
    show padicValNat 2 ((nVSub V g).relIndex V) = n
    rw [h, padicValNat.prime_pow]
  have hmQ1 : (nVSub V g).relIndex V = 2 → E3.mQuot V (nVSub V g) = 1 := by
    intro h
    show padicValNat 2 ((nVSub V g).relIndex V) = 1
    rw [h, padicValNat_self]
  refine ⟨hO, nVSub_inf_bSub_eq_bot hTI hgV, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (nVSub_comm_bSub hTI hgV hu hb).symm
  · refine ⟨_, inferInstance,
      QuotientGroup.mk' ((nVSub V g ⊔ bSub V g).subgroupOf (V ⊔ conjSubgroup V g)),
      QuotientGroup.mk'_surjective _, fun k => ?_, ?_⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hker k
    · rcases hshape with ⟨f, hf, hrel, ⟨e⟩⟩ | ⟨a, ha, hrel, ⟨e⟩⟩ | ⟨m, hm, -, hrel, ⟨e⟩⟩
      · exact Or.inl ⟨f, Or.inl ⟨by decide,
          CFSG.CGT.Timmesfeld75.statedClassicalModel_psl2_of_mulEquiv hf e⟩, hmQ f hrel⟩
      · exact Or.inr (Or.inl ⟨2 * a + 1,
          CFSG.CGT.Timmesfeld75.lieModel_twistedB2_of_mulEquiv_szModel ha
            (e.trans (MulEquiv.subgroupCongr
              (CFSG.GH74.Uniqueness.Bender.szModel_eq_open_sz a).symm)), hmQ _ hrel⟩)
      · exact Or.inr (Or.inr ⟨m, hm, ⟨e⟩, hmQ1 hrel⟩)
  · intro v hv hvU x hx hxB
    exact odd_orderOf_mul hV hTI hU hv hvU hx hxB
  · rcases hmod with ⟨f, hf, hrel, F, hF, hFin, hchar, ψ, hcard, hψs, hψk, hθ⟩ |
      ⟨a, ha, hrel, ψ, hψr, hψk, hθ⟩ | ⟨m, hm, -, hrel, hN', ⟨e⟩⟩
    · let act : ↥(V ⊔ conjSubgroup V g) →* Matrix (Fin 2) (Fin 2) F :=
        { toFun := fun x =>
            ((ψ x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          map_one' := by simp
          map_mul' := fun x y => by simp }
      refine Or.inl ⟨f, F, hF, hFin, hchar, hcard, hmQ f hrel, act, ?_, ?_⟩
      · intro x
        rw [← hker x, ← hψk, MonoidHom.mem_ker]
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      · rw [hO]
        exact isNaturalSum_subgroupOf (fun x => act x) s hs hsM hMX hsW hθ
    · let act : ↥(V ⊔ conjSubgroup V g) →* Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)) :=
        (Units.coeHom _).comp ψ
      refine Or.inr (Or.inl ⟨a, GaloisField 2 (2 * a + 1), inferInstance, inferInstance,
        inferInstance, GaloisField.card 2 (2 * a + 1) (by omega), hmQ _ hrel, act, ?_, ?_⟩)
      · intro x
        rw [← hker x, ← hψk, MonoidHom.mem_ker]
        exact Units.val_eq_one
      · rw [hO]
        exact isNaturalSum_subgroupOf (fun x => act x) s hs hsM hMX hsW hθ
    · refine Or.inr (Or.inr ⟨m, hm, hmQ1 hrel, ⟨_, inferInstance,
        QuotientGroup.mk' ((nVSub V g ⊔ bSub V g).subgroupOf (V ⊔ conjSubgroup V g)),
        QuotientGroup.mk'_surjective _, fun k => ?_, ⟨e⟩⟩, s, hs, hsM.trans hO.symm,
        fun W hW => ?_⟩)
      · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hker k
      · rw [hO]
        exact hsW W hW

end Main

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
