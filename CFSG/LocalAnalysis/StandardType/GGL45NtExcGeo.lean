module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcAbs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtGeoNorm

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly CFSG.StandardType


@[expose] def ExcAlgGeoStd
                                      : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    (letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (τ : Tag),
    (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) → (τ = .D4 → p ≠ 3) →
    (τ = .E8 → p ≠ 5) → ∀ (e : ℕ) (Q : ModGL τ L), 1 ≤ e → IsDiagramTwistMatrix τ L Q →
      IsSteinbergEnd τ L ((2 ^ e) ^ p) (endPow (frobTwistGL τ L 2 e Q) p) →
      Finite ↥(ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)) →
      AbsGeoAt p (ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)) (frobTwistGL τ L 2 e Q)

@[expose] def ExcAlgGeoRee :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L CFSG.LieType.Ree.ReeTag.F4.prime]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L] (p : ℕ), p.Prime → p ≠ 2 → p ≠ 3 →
    ∀ (hf : CFSG.LieType.Ree.ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
      Finite ↥((endPow (CFSG.LieType.Ree.ReeTag.F4.reeEndo L hf a₀) p).eqLocus
        (MonoidHom.id (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag L))) →
      AbsGeoAt p ((endPow (CFSG.LieType.Ree.ReeTag.F4.reeEndo L hf a₀) p).eqLocus
        (MonoidHom.id (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag L)))
        (CFSG.LieType.Ree.ReeTag.F4.reeEndo L hf a₀)

@[expose] def ExcBridgeStmtU
                                      : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    GGL45NtOn (fun _ lab => lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
      fun p lab => ExcBridgeCont p L lab.tag

@[expose] def ExcBridgeStmtE6
                                      : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    GGL45NtOn (fun _ lab => lab.tag = .E6) fun p lab => ExcBridgeCont p L lab.tag

@[expose] def ExcBridgeStmtTwE6
                                      : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    GGL45NtOn (fun _ lab => lab.tag = .twE6) fun p lab => ExcBridgeCont p L lab.tag

@[expose] def ExcBridgeStmtTriD4
                                      : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    GGL45NtOn (fun p lab => GGL45NtFamExTw p lab ∧ lab.tag = .triD4)
      fun p lab => ExcBridgeCont p L lab.tag

@[expose] def ExcBridgeStmtTwF4 :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L CFSG.LieType.Ree.ReeTag.F4.prime]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L],
    GGL45NtOn (fun p lab => GGL45NtFamExTw p lab ∧ lab.tag = .twF4)
      fun p _ R _ I F => IsSimpleGroup R → (∃ f ∈ F, orderOf f = p) →
        ∃ (hf : CFSG.LieType.Ree.ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
          IsExcBridgeSub p I F CFSG.LieType.Ree.ReeTag.F4.tag L
            (CFSG.LieType.Ree.ReeTag.F4.reeEndo L hf a₀)

theorem algClosure_zmod_isAlgebraic
                                      :
    letI := ZMod.algebra (AlgebraicClosure (ZMod 2)) 2
    Algebra.IsAlgebraic (ZMod 2) (AlgebraicClosure (ZMod 2)) := by
  have h : ZMod.algebra (AlgebraicClosure (ZMod 2)) 2 =
      (inferInstance : Algebra (ZMod 2) (AlgebraicClosure (ZMod 2))) := Subsingleton.elim _ _
  rw [h]
  exact AlgebraicClosure.isAlgebraic (ZMod 2)

theorem nonTorsion_excTag
    {p : ℕ} {lab : LargeEvenLabel} (hnt : GGL45FamNonTorsion p lab)
    (hexc : GGL45NtExcLabel lab) :
    (excTagOf lab.tag = .F4 ∨ excTagOf lab.tag = .E6 ∨ excTagOf lab.tag = .E7 ∨
        excTagOf lab.tag = .E8 → p ≠ 3) ∧
      (excTagOf lab.tag = .D4 → p ≠ 3) ∧ (excTagOf lab.tag = .E8 → p ≠ 5) := by
  unfold GGL45NtExcLabel at hexc
  rcases hexc with h | h | h | h | h | h | h | h <;>
    simp only [GGL45FamNonTorsion, h, excTagOf] at hnt ⊢ <;> simp [hnt]

theorem geoNormRaw_of_excBridgeCont
                                      {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hnt : GGL45FamNonTorsion p lab) (hexc : GGL45NtExcLabel lab) (hStd : ExcAlgGeoStd)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) {R : Type} [Group R]
    {I F : Set (MulAut R)}
    (hbr : ExcBridgeCont p L lab.tag R I F) (hrec : GGL45NtRec p R I F) :
    GGL45NtGeoNormRaw p R I F := by
  intro hsimple hnonab Ebar f hfF hfp hEab hEcard hEI hcomm hsat
  dsimp only [ExcBridgeCont] at hbr
  obtain ⟨e, Q, he, hQ, hbridge, hSt, hFin⟩ := hbr hsimple ⟨f, hfF, hfp⟩
  obtain ⟨h3, h3D, h5⟩ := nonTorsion_excTag hnt hexc
  exact geo_of_absBridge hp hbridge.stab (fun g hg => ratPts_fix hg) hbridge.absBridge
    (hrec hsimple hnonab).2.1 (hStd L hL p hp hp2 _ h3 h3D h5 e Q he hQ hSt hFin) Ebar f hfF hfp hEab
    hEcard hEI hcomm hsat

theorem geoNormRaw_of_excBridgeSub
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hnt : GGL45FamNonTorsion p lab) (htw : lab.tag = .twF4) (hRee : ExcAlgGeoRee)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L CFSG.LieType.Ree.ReeTag.F4.prime]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L] {R : Type} [Group R] [Finite R]
    {I F : Set (MulAut R)}
    (hbr : IsSimpleGroup R → (∃ f ∈ F, orderOf f = p) →
      ∃ (hf : CFSG.LieType.Ree.ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
        IsExcBridgeSub p I F CFSG.LieType.Ree.ReeTag.F4.tag L
          (CFSG.LieType.Ree.ReeTag.F4.reeEndo L hf a₀))
    (hrec : GGL45NtRec p R I F) : GGL45NtGeoNormRaw p R I F := by
  intro hsimple hnonab Ebar f hfF hfp hEab hEcard hEI hcomm hsat
  obtain ⟨hf, a₀, hbridge⟩ := hbr hsimple ⟨f, hfF, hfp⟩
  have hp3 : p ≠ 3 := by
    have h := hnt
    simp only [GGL45FamNonTorsion, htw] at h
    exact h
  have habs := hbridge.absBridge
  obtain ⟨ρ, Θ, hρ, hρG, hΘ, hI, hconj, hF⟩ := habs
  haveI : Finite (MulAut R) := Finite.of_injective (fun φ : MulAut R => (φ : R → R))
    (fun a b h => MulEquiv.ext (congrFun h))
  haveI : Finite ↥((endPow (CFSG.LieType.Ree.ReeTag.F4.reeEndo L hf a₀) p).eqLocus
      (MonoidHom.id (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag L))) := Finite.of_injective Θ hΘ
  exact geo_of_absBridge hp (eqLocus_endPow_stab _ _) (fun g hg => hg) hbridge.absBridge
    (hrec hsimple hnonab).2.1 (hRee L p hp hp2 hp3 hf a₀ inferInstance) Ebar f hfF hfp hEab hEcard
    hEI hcomm hsat

end CFSG.HardMathSupport.C14Exc

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.HardMathSupport.C14Exc


theorem ggL45NtGeoNormOn_exU
    (hbr : ExcBridgeStmtU) (hrec : GGL45NtRecOn GGL45NtFamExU)
    (hStd : ExcAlgGeoStd) : GGL45NtGeoNormOn GGL45NtFamExU := by
  intro p hp hp2 lab hlab hkg hS
  exact (largeEvenLabelAll_and (hbr (AlgebraicClosure (ZMod 2)) p hp hp2 lab hlab hkg hS.2)
    (hrec p hp hp2 lab hlab hkg hS)).mono fun R _ I F ⟨h1, h2⟩ =>
      geoNormRaw_of_excBridgeCont hp hp2 hS.1.1 hS.1.2.2 hStd algClosure_zmod_isAlgebraic h1 h2

theorem ggL45NtGeoNormOn_e6
    (hbr : ExcBridgeStmtE6) (hrec : GGL45NtRecOn GGL45NtFamExE6)
    (hStd : ExcAlgGeoStd) : GGL45NtGeoNormOn GGL45NtFamExE6 := by
  intro p hp hp2 lab hlab hkg hS
  exact (largeEvenLabelAll_and (hbr (AlgebraicClosure (ZMod 2)) p hp hp2 lab hlab hkg hS.2)
    (hrec p hp hp2 lab hlab hkg hS)).mono fun R _ I F ⟨h1, h2⟩ =>
      geoNormRaw_of_excBridgeCont hp hp2 hS.1.1 hS.1.2.2 hStd algClosure_zmod_isAlgebraic h1 h2

theorem ggL45NtGeoNormOn_twE6
    (hbr : ExcBridgeStmtTwE6) (hrec : GGL45NtRecOn GGL45NtFamExTwE6)
    (hStd : ExcAlgGeoStd) : GGL45NtGeoNormOn GGL45NtFamExTwE6 := by
  intro p hp hp2 lab hlab hkg hS
  exact (largeEvenLabelAll_and (hbr (AlgebraicClosure (ZMod 2)) p hp hp2 lab hlab hkg hS.2)
    (hrec p hp hp2 lab hlab hkg hS)).mono fun R _ I F ⟨h1, h2⟩ =>
      geoNormRaw_of_excBridgeCont hp hp2 hS.1.1 hS.1.2.2 hStd algClosure_zmod_isAlgebraic h1 h2

theorem ggL45NtGeoNormOn_exTw
    (hD4 : ExcBridgeStmtTriD4) (hF4 : ExcBridgeStmtTwF4)
    (hrec : GGL45NtRecOn GGL45NtFamExTw) (hstruct : GGL45NtStructOn GGL45NtFamExTw)
    (hStd : ExcAlgGeoStd) (hRee : ExcAlgGeoRee) : GGL45NtGeoNormOn GGL45NtFamExTw := by
  intro p hp hp2 lab hlab hkg hS
  rcases hS.2 with htri | htw
  · exact (largeEvenLabelAll_and
      (hD4 (AlgebraicClosure (ZMod 2)) p hp hp2 lab hlab hkg ⟨hS, htri⟩)
      (hrec p hp hp2 lab hlab hkg hS)).mono fun R _ I F ⟨h1, h2⟩ =>
        geoNormRaw_of_excBridgeCont hp hp2 hS.1.1 hS.1.2.2 hStd algClosure_zmod_isAlgebraic h1 h2
  · exact (largeEvenLabelAll_and
      (largeEvenLabelAll_and (hF4 (AlgebraicClosure (ZMod 2)) p hp hp2 lab hlab hkg ⟨hS, htw⟩)
        (hstruct p hp hp2 lab hlab hkg hS))
      (hrec p hp hp2 lab hlab hkg hS)).mono fun R _ I F ⟨⟨h1, hfin, _⟩, h2⟩ => by
        haveI := hfin
        exact geoNormRaw_of_excBridgeSub hp hp2 hS.1.1 htw hRee h1 h2

end CFSG.StandardType
