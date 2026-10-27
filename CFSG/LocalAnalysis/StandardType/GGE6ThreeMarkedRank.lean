module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCoverComponent
public import CFSG.LocalAnalysis.StandardType.GGE6ThreePointwise
public import CFSG.LocalAnalysis.StandardType.GGInnerD4NoD4Table
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRowCover1585Holds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632RatOpp
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632RatOne
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632B1Rows

public section

namespace CFSG.StandardType.E6MarkedRank

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.S2MathAs1E6Companion1625


theorem exists_marked_cover_position
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hE6 : RationalProducerOn Omega .E6) (hTwE6 : RationalProducerOn Omega .twE6)
    {L : Type} [Group L] [Finite L] (J : Subgroup L) (y : MulAut L)
    (E : Subgroup (MulAut L)) (labL labJ : LargeEvenLabel)
    (hL : LargeEvenInLambda2 labL) (hJ : LargeEvenInLambda2 labJ)
    (hpair : GGPairE6Three 3 labL labJ)
    (hhL : GGHasLabel labL (L ⧸ Subgroup.center L))
    (hhJ : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hy : y ≠ 1) (hy3 : y ^ 3 = 1) (hyE : y ∈ E)
    (hcomp : IsComponentOf J (ggAutFixedSubgroup y))
    (hmark : LargeEvenMarking L (fun _ _ _ I _ theta => GGInducedInn E theta I)) :
    commutator L = ⊤ ∧ ∃ (R : Type) (_ : Group R) (I : Set (MulAut R))
      (theta : L ⧸ Subgroup.center L ≃* R), GGInducedInn E theta I ∧
      ∃ M : MarkedRationalKacRealization Omega labL 3 R I (ggInducedAut theta y),
        ∃ j : Fin M.row.D.orbits.length, M.row.D.orbits[j].qs = true ∧
          J.map (theta.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) =
            component M j ∧
          M.row.D.orbits[j].lab = labJ ∧ ∀ k, k = j := by
  have hb := s2_1586_three_dvd labL.n
  have hKac : GGKacExcPair labL 3 :=
    ⟨Nat.prime_three, by decide, hb,
      hpair.2.1.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  have hProducer : LargeEvenLabelAll labL (fun R _ I _ =>
      ∀ phi : MulAut R, phi ∈ I → orderOf phi = 3 →
        Nonempty (MarkedRationalKacRealization Omega labL 3 R I phi)) :=
    hpair.2.1.elim (hE6 3 labL hL hKac) (hTwE6 3 labL hL hKac)
  obtain ⟨hperf, lab', hLab', hRaw⟩ := hmark
  have hHasLab' : GGHasLabel lab' (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun theta _ => ⟨theta⟩)) hRaw
  have hIso : GGLabelIso lab' labL := ggLabelRigidInput_holds _ _ _ hLab' hL hHasLab' hhL
  have hRawL := largeEvenRawDatum_of_ggLabelIso hIso hRaw
  obtain ⟨R, hR, I, F, hdata⟩ := largeEvenRawDatum_exists (hProducer _ hRawL)
  letI : Group R := hR
  obtain ⟨⟨_, _, theta, hInd⟩, hProd⟩ := hdata
  have hOrderY : orderOf y = 3 := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hy3 hy
  have hOrder : orderOf (ggInducedAut theta y) = 3 := by
    rw [orderOf_injective (ggInducedAut theta)
      (ggInducedAut_injective_of_perfect hperf theta), hOrderY]
  obtain ⟨M⟩ := hProd (ggInducedAut theta y) (hInd y hyE) hOrder
  obtain ⟨j, hqs, hJmap, hlabel, hj⟩ := E6CoverComponent.exists_unique_position
    theta M hL hJ hpair hb J hcomp hhJ
  exact ⟨hperf, R, hR, I, theta, hInd, M, j, hqs, hJmap, hlabel, hj⟩

theorem cyclicOn_of_producers_and_cuts
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {row : LargeEvenLabel → LargeEvenLabel → Prop}
    (hE6 : RationalProducerOn Omega .E6) (hTwE6 : RationalProducerOn Omega .twE6)
    (hQ2 : B2SatQ2On Omega row)
    (hOuterQ2 : B3On Omega (fun lab labJ => row lab labJ ∧ lab.n = 1))
    (hCyc : GGE6ThreeFullCentreCyclicOn1585 Omega row) : GGE6ThreeCyclicOn1585 row := by
  intro L _ _ J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark hrow
  obtain ⟨hperf, R, hR, I, theta, hInd, M, j, hqs, hJmap, hlabel, hj⟩ :=
    exists_marked_cover_position hE6 hTwE6 J y E labL labJ hL hJ hpair hhL hhJ
      hy hy3 hyE hcomp hmark
  letI : Group R := hR

  have hrow' : row labL M.row.D.orbits[j].lab := by rw [hlabel]; exact hrow
  have htau : M.tau = CFSG.Blueprint.Chevalley.Tag.E6 := by
    have htype := M.row.type_eq
    obtain htag | htag := hpair.2.1
    · rw [ggKacTypeOfLabel, htag] at htype
      simp only [Option.some.injEq, Prod.mk.injEq] at htype
      rw [← M.tau_eq, ← htype.1]
      rfl
    · rw [ggKacTypeOfLabel, htag] at htype
      simp only [Option.some.injEq, Prod.mk.injEq] at htype
      rw [← M.tau_eq, ← htype.1]
      rfl
  exact E6Pointwise.isCyclic_of_marked_cover_row_of_cuts hQ2 hOuterQ2 hCyc hperf theta labL I y M j
    hL hj hqs hrow' htau E hInd hcomm J hJmap hfix


theorem rowCover_of_producers
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hE6 : RationalProducerOn Omega .E6) (hTwE6 : RationalProducerOn Omega .twE6) :
    GGE6ThreeRowCover1585 := by
  intro L _ _ J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark
  obtain ⟨hperf, R, hR, I, theta, hInd, M, j, hqs, hJmap, hlabel, hj⟩ :=
    exists_marked_cover_position hE6 hTwE6 J y E labL labJ hL hJ hpair hhL hhJ
      hy hy3 hyE hcomp hmark
  letI : Group R := hR
  have hdvd : labL.n ∣ M.row.D.orbits[j].lab.n := by
    rw [M.field_exp]
    exact dvd_mul_left labL.n (M.orbitNodes j).length
  exact ggE6Three_rows_of_datum hL hpair M.row.valid (List.getElem_mem j.2) hdvd hlabel

section

theorem b3On_of_ratIndex_one
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {row : LargeEvenLabel → LargeEvenLabel → Prop} (h : B1RatOn Omega row 1) :
    B3On Omega row := by
  intro lab R _ I phi M j hL hj hqs hrow u hu hnot
  have hle : centralizerGroup M ≤ conn M :=
    Subgroup.relIndex_eq_one.mp
      (h lab R I phi M j hL hj hqs hrow)
  exact (hnot (hle hu)).elim

theorem b3On_mono {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {row row' : LargeEvenLabel → LargeEvenLabel → Prop}
    (hsub : ∀ lab labJ, row' lab labJ → row lab labJ) (h : B3On Omega row) :
    B3On Omega row' :=
  fun lab R _ I phi M j hL hj hqs hrow => h lab R I phi M j hL hj hqs (hsub _ _ hrow)

theorem b3On_of_b1On_rat_one {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {row : LargeEvenLabel → LargeEvenLabel → Prop} {g : ℕ}
    (h : B1On Omega row g 1) : B3On Omega row :=
  b3On_of_ratIndex_one (fun lab R _ I phi M j hL hj hqs hrow =>
    (h lab R I phi M j hL hj hqs hrow).1.rational_relIndex)

end

theorem b3On_r1 (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B3On Omega GGE6ThreeR1Labels1585 := b3On_of_b1On_rat_one (b1On_r1_holds Omega)

theorem b3On_r4 (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B3On Omega GGE6ThreeR4Labels1585 := b3On_of_b1On_rat_one (b1On_r4_holds Omega)

theorem b3On_r4Opp (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B3On Omega GGE6ThreeR4OppLabels1585 := b3On_of_b1On_rat_one (b1On_r4Opp_holds Omega)

theorem b3On_r16Opp
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B3On Omega GGE6ThreeR16OppLabels1585 :=
  b3On_of_ratIndex_one (b1RatOn_r16Opp_holds Omega)

theorem i1Rank_of_producers_and_cuts
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hE6 : RationalProducerOn Omega .E6) (hTwE6 : RationalProducerOn Omega .twE6)
    (hQ2R1 : B2SatQ2On Omega GGE6ThreeR1Labels1585)
    (hQ2R4 : B2SatQ2On Omega GGE6ThreeR4Labels1585)
    (hQ2R16 : B2SatQ2On Omega GGE6ThreeR16Labels1585)
    (hInnerR4Opp : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R))
      (phi : MulAut R) (M : MarkedRationalKacRealization Omega lab 3 R I phi)
      (j : Fin M.row.D.orbits.length),
      LargeEvenInLambda2 lab → (∀ k, k = j) → M.row.D.orbits[j].qs = true →
      GGE6ThreeR4OppLabels1585 lab M.row.D.orbits[j].lab → lab.n = 1 →
      CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom M.a) (M.repr j))
        ((M.setup.ρ : (Fin M.tau.rank → ℤ) → _)^[
          CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength M.setup.ρ
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom M.a) (M.repr j))]))
    (hQ2R16Opp : B2SatQ2On Omega GGE6ThreeR16OppLabels1585)
    (hOuterR3Q2 : B3On Omega (fun lab labJ => GGE6ThreeR3Labels1585 lab labJ ∧ lab.n = 1))
    (hOuterR16Q2 : B3On Omega (fun lab labJ => GGE6ThreeR16Labels1585 lab labJ ∧ lab.n = 1)) : GGE6ThreeI1Rank := by
  exact ggE6ThreeI1Rank_of_rows1585 (rowCover_of_producers hE6 hTwE6)
    (cyclicOn_of_producers_and_cuts hE6 hTwE6
      hQ2R1 (b3On_mono (fun _ _ h => h.1) (b3On_r1 Omega)) (e6FullCentreCyclicR1_holds Omega))
    (cyclicOn_of_producers_and_cuts hE6 hTwE6
      (E6Pointwise.b2SatQ2On_r3_holds Omega) hOuterR3Q2 (e6FullCentreCyclicR3_holds Omega))
    (cyclicOn_of_producers_and_cuts hE6 hTwE6
      hQ2R4 (b3On_mono (fun _ _ h => h.1) (b3On_r4 Omega)) (e6FullCentreCyclicR4_holds Omega))
    (cyclicOn_of_producers_and_cuts hE6 hTwE6
      hQ2R16 hOuterR16Q2 (e6FullCentreCyclicR16_holds Omega))
    (cyclicOn_of_producers_and_cuts hE6 hTwE6
      (E6Pointwise.b2SatQ2On_r4Opp_of_inner Omega hInnerR4Opp)
      (b3On_mono (fun _ _ h => h.1) (b3On_r4Opp Omega))
      (e6FullCentreCyclicR4Opp_holds Omega))
    (cyclicOn_of_producers_and_cuts hE6 hTwE6
      hQ2R16Opp (b3On_mono (fun _ _ h => h.1) (b3On_r16Opp Omega))
      (e6FullCentreCyclicR16Opp_holds Omega))

end CFSG.StandardType.E6MarkedRank
