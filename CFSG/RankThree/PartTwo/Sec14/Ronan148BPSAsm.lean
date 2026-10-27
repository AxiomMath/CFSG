module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSFin
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSA7

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (thL)

section Aut

variable {Γ : Type} [Group Γ] [Finite Γ] {A L : Subgroup Γ} {b : Γ}

theorem autThetaQuot_e9 (hA : Late.IsE27 A) (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hsec : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers b : Set Γ)) :
    CFSG.Assembly.IsElemAbelian 3 (Sec4.autThetaQuot A L) ∧
      Nat.card (Sec4.autThetaQuot A L) = 9 := by
  have hsec' : Late.sectionCentralizer A L (thL L) = (Subgroup.zpowers b : Set Γ) := hsec
  have hP : Sec4.autThetaQuot A L = PS.bar L A := by
    rw [Sec4.autThetaQuot, Sec4.autIn, Subgroup.map_map, inf_eq_left.mpr hAL]
    rfl
  rw [hP]
  refine ⟨?_, PS.card_bar_A hA hbA hb1 hAL hsec'⟩
  rw [PS.bar_eq_map_phiA hAL le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := u.2
    obtain ⟨y, hy⟩ := v.2
    change (u : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) * v = v * u
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact hA.1.1.is_comm.comm x y
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (hA.1.2 x x.2)
    rw [this, map_one]

end Aut

@[expose] def KF148PointSigInspL3 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L : Subgroup Γ) (b : Γ),
    Late.IsE27 A → b ∈ A → b ≠ 1 → L ≤ Subgroup.centralizer ({b} : Set Γ) →
    A ≤ Subgroup.normalizer (L : Set Γ) →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers b : Set Γ) →
    (∀ x ∈ Subgroup.centralizer (A : Set Γ), x ^ 3 = 1 → x ∈ A) →
    ((b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × Sec12.lBar b L) ∧
        ((IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∧
            (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
              Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∧
            Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
            Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)))) ∨
      (b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        (Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
        Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      (b ∉ L ∧ Sec8.IsZ3PGLThreePi (lBarA b L A) ∧
        Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧
        ∃ x ∈ A, Sec4.InducesTypeOn L x 3)) →
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    (∃ (X' : Type) (_ : Group X') (_ : Finite X'), Sec4.IsList46 X' ∧
      Nonempty (X' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
    L3PointFacts A L b →
    ¬ Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    ThreeSolvInv148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L) ∧
      RankTwo148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      SigGen148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L)

theorem kf148PointSigInsp_of (hJ2 : InspIn148 CFSG.Blueprint.NativeSporadic.J2)
    (hM22 : InspIn148 CFSG.Blueprint.NativeSporadic.M22)
    (hM12 : InspIn148 CFSG.Blueprint.NativeSporadic.M12) (hL3 : KF148PointSigInspL3) :
    KF148PointSigInsp := by
  intro Γ _ _ A L b hA hbA hb1 hLb hAL hsec hF h131 hT h46 hloc hsol
  obtain ⟨hPe, hP9⟩ := autThetaQuot_e9 hA hbA hb1 hAL hsec
  rcases hT with ⟨⟨e⟩⟩ | hL | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact (hJ2.of_mulEquiv e).insp hPe hP9
  · exact hL3 Γ A L b hA hbA hb1 hLb hAL hsec hF h131 hL h46 (hloc hL) hsol
  · exact (A7.inspIn148_alt7.of_mulEquiv e).insp hPe hP9
  · exact (hM22.of_mulEquiv e).insp hPe hP9
  · exact (hM12.of_mulEquiv e).insp hPe hP9

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
