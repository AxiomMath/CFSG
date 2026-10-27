module

public import CFSG.Milestones.ASVolI.F4TISets
import all CFSG.Milestones.ASVolI.F4

public noncomputable section

namespace CFSG.ASVolI

open CFSG.Open

section BurnsideF4jbCoords

open Matrix CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem burnsideF4jb_coords {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (chart : NativeChart .Sp4 2 f Gp) (hM : chart.Matches M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (φ : StatedSp 2 K →* E),
      Function.Injective φ ∧ (⊤ : Subgroup (StatedSp 2 K)).map φ = Gp ∧
      Gp ⊓ M₁ = (Q2 K 0).map φ ∧ Gp ⊓ M₂ = (Q2 K 1).map φ ∧
      chart.shortRoot = (burnsideF4gSpInv_Xs K).map φ := by
  obtain ⟨marking, hpts, hlines, -, hshort⟩ := burnsideF4gSpInv_marking_of_chart chart
  have hK : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let φ : StatedSp 2 marking.field →* E := Gp.subtype.comp marking.transport
  have hφinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun a ha => ?_
    have h1 : marking.transport a = 1 := Subtype.ext ha
    have h2 := (burnsideF4f_transport_eq_one_iff marking a).1 h1
    exact Subtype.ext (burnsideF4gSpInv_scalar_eq_one h2 a.2)
  have hφrange : (⊤ : Subgroup (StatedSp 2 marking.field)).map φ = Gp := by
    ext e
    constructor
    · rintro ⟨g, -, rfl⟩
      exact (marking.transport g).2
    · intro he
      obtain ⟨g, hg⟩ := burnsideF4f_transport_surjective marking ⟨e, he⟩
      exact ⟨g, Subgroup.mem_top g, congrArg Subtype.val hg⟩
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : ∀ b : Bool, nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    intro b
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSp_mem_rawStabilizer, burnsideF4gSp_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSp_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).2)
  have hpar : ∀ b : Bool, (marking.parabolic b).map Gp.subtype =
      (Q2 marking.field (if b then 1 else 0)).map φ := by
    intro b
    have e1 : marking.parabolic b =
        (Q2 marking.field (if b then 1 else 0)).map marking.transport :=
      congrArg (Subgroup.map marking.transport) (key b)
    calc (marking.parabolic b).map Gp.subtype
        = ((Q2 marking.field (if b then 1 else 0)).map marking.transport).map
            Gp.subtype := by rw [e1]
      _ = (Q2 marking.field (if b then 1 else 0)).map
            (Gp.subtype.comp marking.transport) := Subgroup.map_map _ _ _
      _ = (Q2 marking.field (if b then 1 else 0)).map φ := rfl
  have hM₁ : Gp ⊓ M₁ = (Q2 marking.field 0).map φ := by
    rw [hM.2.1, hpts]
    simpa using hpar false
  have hM₂ : Gp ⊓ M₂ = (Q2 marking.field 1).map φ := by
    rw [hM.2.2, hlines]
    simpa using hpar true
  have hXs : nativeRoot .Sp4 (2 ^ f) marking.basis .sum false =
      burnsideF4gSpInv_Xs marking.field := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨-, t, c, -, hg⟩
      refine (burnsideF4gSpInv_mem_Xs (K := marking.field) (g := g)).2 ⟨t, ?_⟩
      apply statedSp_ext
      rw [← burnsideF4gSpInv_matrixUnit_short, hg, hbasis]
      simp [markedMatrix, positiveMatrix, symplecticRoot]
    · intro g hg
      obtain ⟨t, ht⟩ := (burnsideF4gSpInv_mem_Xs (K := marking.field) (g := g)).1 hg
      subst ht
      refine Subgroup.subset_closure ⟨Or.inr (Or.inl rfl), t, 0, trivial, ?_⟩
      rw [hbasis, ← burnsideF4gSpInv_matrixUnit_short]
      simp [markedMatrix, positiveMatrix, symplecticRoot]
  have hsh : chart.shortRoot = (burnsideF4gSpInv_Xs marking.field).map φ := by
    have e1 : marking.root .sum false =
        (burnsideF4gSpInv_Xs marking.field).map marking.transport :=
      congrArg (Subgroup.map marking.transport) hXs
    calc chart.shortRoot = (marking.root .sum false).map Gp.subtype := hshort
      _ = ((burnsideF4gSpInv_Xs marking.field).map marking.transport).map Gp.subtype := by
          rw [e1]
      _ = (burnsideF4gSpInv_Xs marking.field).map
            (Gp.subtype.comp marking.transport) := Subgroup.map_map _ _ _
      _ = (burnsideF4gSpInv_Xs marking.field).map φ := rfl
  exact ⟨marking.field, inferInstance, inferInstance, inferInstance, φ, hφinj, hφrange, hM₁, hM₂,
    hsh⟩

end BurnsideF4jbCoords

section BurnsideF4jbF442

open CFSG.ASVolI.ChF CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.RankTwoAmalgam.Completion

theorem burnsideF4jb_F_4_42_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : ChF.Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : ChF.HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) :
    ∃ t : ↥M₂, (t : E) ∈ CFSG.Open.pCoreOf 2 (Gp ⊓ M₂) ∧
      ChF.IsShortRootInv .Sp4 Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({ChF.epsG β ε (CFSG.Quasithin.RankTwoAmalgam.Completion.f2 (c := β) t)} :
        Set M) ≤ ChF.MiTwo β ε := by
  have hM : hyp.amalgam.toHypF_4_4g.chart.Matches M₁ M₂ :=
    hyp.amalgam.toHypF_4_4g.chart_matches
  obtain ⟨K, _, _, _, φ, hφinj, -, -, hM₂, hshort⟩ :=
    burnsideF4jb_coords hyp.amalgam.toHypF_4_4g.chart hM
  have htGM : φ (burnsideF4gSpInv_xs 1) ∈ Gp ⊓ M₂ := by
    rw [hM₂]
    exact Subgroup.mem_map_of_mem φ (burnsideF4jb_xs_mem_Q2_one 1)
  obtain ⟨t, ht⟩ : ∃ t : ↥M₂, (t : E) = φ (burnsideF4gSpInv_xs 1) := ⟨⟨_, htGM.2⟩, rfl⟩
  have ht1 : (t : E) ≠ 1 := by
    rw [ht]
    intro h
    exact burnsideF4gSpInv_xs_ne_one (K := K) one_ne_zero (hφinj (h.trans (map_one φ).symm))
  have ht1' : t ≠ 1 := fun h => ht1 (by rw [h]; rfl)
  have htsq : (t : E) * (t : E) = 1 := by
    rw [ht, ← map_mul, burnsideF4gSpInv_xs_sq, map_one]
  have htE : (t : E) ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) := by
    rw [ht, hM₂, burnsideF4d_oPPrime_map φ hφinj, burnsideF4jb_ctr_map φ hφinj,
      burnsideF4jb_ctr_oPPrime_Q2_one]
    exact Subgroup.mem_map_of_mem φ (burnsideF4gSpInv_mem_Xs.2 ⟨1, rfl⟩)
  refine ⟨t, ?_, ?_, ?_⟩
  ·
    rw [ht, hM₂, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective φ hφinj]
    exact Subgroup.mem_map_of_mem φ (burnsideF4gSpInv_xs_mem_pCoreOf 1)
  ·
    refine ⟨f, hyp.amalgam.toHypF_4_4g.chart, hM, ?_, ht1, htsq, fun h => absurd h (by decide),
      1, Gp.one_mem, ?_⟩
    · rw [ht]
      exact (Subgroup.mem_inf.1 htGM).1
    · rw [if_pos rfl, one_mul, inv_one, mul_one, hshort, ht]
      exact Subgroup.mem_map_of_mem φ (burnsideF4gSpInv_mem_Xs.2 ⟨1, rfl⟩)
  ·
    have hψ : Function.Injective (burnsideF4d_bTwo β ε) :=
      hyp.inj.comp (f2_injective β hyp.faithful)
    have hG2 : GiTwo Gp β ε = ((Gp ⊓ M₂).subgroupOf M₂).map (burnsideF4d_bTwo β ε) :=
      burnsideF4d_GiTwo_eq Gp β ε
    have hsub : ((Gp ⊓ M₂).subgroupOf M₂).map M₂.subtype = Gp ⊓ M₂ :=
      Subgroup.map_subgroupOf_eq_of_le inf_le_right
    have htc2 : t ∈ ctr (oPPrime 2 ((Gp ⊓ M₂).subgroupOf M₂)) := by
      have h : (t : E) ∈ (ctr (oPPrime 2 ((Gp ⊓ M₂).subgroupOf M₂))).map M₂.subtype := by
        rw [← burnsideF4jb_ctr_map M₂.subtype M₂.subtype_injective,
          ← burnsideF4d_oPPrime_map M₂.subtype M₂.subtype_injective, hsub]
        exact htE
      obtain ⟨y, hy, hyt⟩ := h
      rwa [show y = t from Subtype.ext hyt] at hy
    refine (hyp.hc rfl).1 _ ?_ ?_
    · rw [hG2, burnsideF4d_oPPrime_map _ hψ, burnsideF4jb_ctr_map _ hψ]
      exact Subgroup.mem_map_of_mem (burnsideF4d_bTwo β ε) htc2
    · intro h
      exact ht1' (hψ (h.trans (map_one (burnsideF4d_bTwo β ε)).symm))

end BurnsideF4jbF442

section BurnsideF4jbGen

open Matrix CFSG.ASVolI.ChF CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

theorem burnsideF4jb_pairRootElt_sq [CharP K 2] {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b) (t : K) :
    pairRootElt hab t * pairRootElt hab t = 1 := by
  rw [((root_matrix_data (r := 2) (K := K)).1 a b hab t t).2.1, CharTwo.add_self_eq_zero]
  exact statedSp_ext (by rw [coe_pairRootElt, pairRootMat_zero]; rfl)

theorem burnsideF4jb_mem_oPPrime_top_of_sq {x : StatedSp 2 K} (h : x * x = 1) :
    x ∈ oPPrime 2 (⊤ : Subgroup (StatedSp 2 K)) := by
  refine Subgroup.subset_closure ⟨Subgroup.mem_top x, ?_⟩
  by_cases h1 : x = 1
  · exact ⟨0, by simp [h1]⟩
  · exact ⟨1, by rw [pow_one]; exact orderOf_eq_prime (by rwa [sq]) h1⟩

theorem burnsideF4jb_oPPrime_top [Finite K] [CharP K 2] :
    oPPrime 2 (⊤ : Subgroup (StatedSp 2 K)) = ⊤ := by
  apply eq_top_of_borelCuts_eq_empty
  · intro u hu
    refine Subgroup.subset_closure ⟨Subgroup.mem_top u, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 burnsideF4gSpInv_unipotent_isPGroup ⟨u, hu⟩
    exact ⟨k, by rw [← hk]; exact Subgroup.orderOf_coe (⟨u, hu⟩ : unipotent 2 K)⟩
  · refine Set.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨k, rfl, hk⟩ := hi
    apply hk
    unfold weylRep
    exact mul_mem (mul_mem (burnsideF4jb_mem_oPPrime_top_of_sq (burnsideF4jb_pairRootElt_sq _ _))
      (burnsideF4jb_mem_oPPrime_top_of_sq (burnsideF4jb_pairRootElt_sq _ _)))
      (burnsideF4jb_mem_oPPrime_top_of_sq (burnsideF4jb_pairRootElt_sq _ _))

theorem burnsideF4jb_oPPrime_Gp_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .Sp4 2 f Gp M₁ M₂) : ChF.oPPrime 2 Gp = Gp := by
  obtain ⟨K, _, _, _, φ, hφinj, hrange, -, -, -⟩ :=
    burnsideF4jb_coords hyp.toHypF_4_4g.chart hyp.toHypF_4_4g.chart_matches
  rw [← hrange, burnsideF4d_oPPrime_map φ hφinj, burnsideF4jb_oPPrime_top]

end BurnsideF4jbGen

end CFSG.ASVolI
