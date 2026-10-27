module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSAsm
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13

theorem rankTwo_of_isLThreePi {X : Type} [Group X] [Finite X] (h : IsLThreePi X) :
    RankTwo148 X := by
  obtain ⟨p, e, hp, he, hiso⟩ := h
  intro E hE hE27
  have := Ronan148T.oddThreeRank X p e he hiso E hE
  omega

theorem isSolvable_inSubgroup_theta {Y : Type} [Group Y] [Finite Y] (H : Subgroup Y) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) H) := by
  have hs := (solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three).1
  exact Group.isSolvable_of_surjective
    (f := (H.subtype.subgroupMap (aschbacherSolvableCore 3 ↥H)))
    (MonoidHom.subgroupMap_surjective _ _)

theorem threeSolvInv_of_locA {Γ : Type} [Group Γ] [Finite Γ] {A L : Subgroup Γ}
    (hloc : Ronan148T.LocA A L) :
    ThreeSolvInv148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L) := by
  intro V hV3 hVinv
  have h3 : ¬ 3 ∣ Nat.card V := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hV3
  have hmap : ∀ σ ∈ Sec4.autThetaQuot A L, V.map σ.toMonoidHom ≤ V := by
    rintro σ hσ _ ⟨v, hv, rfl⟩
    exact hVinv σ hσ v hv
  obtain ⟨a, -, haN, -, hle⟩ := hloc V h3 hmap
  haveI := isSolvable_inSubgroup_theta (Res5Types.fixSubgroup (L3PGL.sigmaOf L haN))
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

@[expose] def KF148SigGenL3 : Prop :=
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
    SigGen148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L)

theorem kf148PointSigInspL3_of (hG : KF148SigGenL3) : KF148PointSigInspL3 := by
  intro Γ _ _ A L b hA hbA hb1 hLb hAL hsec hF h131 hL h46 hpt hsol
  exact ⟨threeSolvInv_of_locA hpt.1, rankTwo_of_isLThreePi hL,
    hG Γ A L b hA hbA hb1 hLb hAL hsec hF h131 hL h46 hpt hsol⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
