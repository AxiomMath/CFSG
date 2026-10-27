module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSInsp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSRed

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (thL)


@[expose] def KF148PointSigInsp : Prop :=
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
    (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) →
    (∃ (X' : Type) (_ : Group X') (_ : Finite X'), Sec4.IsList46 X' ∧
      Nonempty (X' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
    (IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) → L3PointFacts A L b) →
    ¬ Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    ThreeSolvInv148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L) ∧
      RankTwo148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      SigGen148 (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L)

theorem sigImg148_of_solvable {X : Type} [Group X] [Finite X] (hX : Group.IsSolvable X)
    {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) : SigImg148 X P := by
  intro W Q D hWinn hPW hD hQWD hQinv hQP hsig hQO
  exfalso
  apply hQO
  have hQOD := hsig D hD Q hQWD hQinv hQP
  have hsolI : Group.IsSolvable (MulAut.conj : X →* MulAut X).range :=
    Group.isSolvable_of_surjective (f := (MulAut.conj : X →* MulAut X).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hsolW : Group.IsSolvable ↥W :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hWinn)
  refine PS.le_pPrimeCoreOf_of_hom_solvable (hP.to_le hD.1) (hD.1.trans hPW)
    (hQWD.trans inf_le_left) hQOD (MonoidHom.id ↥W) ?_ ?_
  · exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  · rw [MonoidHom.ker_id, Subgroup.card_bot]
    exact Nat.coprime_one_right 3

section Certs


theorem kf148PointSigImg_of_insp (h : KF148PointSigInsp) : KF148PointSigImg := by
  intro Γ _ _ A L b hA hbA hb1 hLb hAL hsec hF h131 hT h46 hloc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsec' : Late.sectionCentralizer A L (thL L) = (Subgroup.zpowers b : Set Γ) := hsec
  have hP : Sec4.autThetaQuot A L = PS.bar L A := by
    rw [Sec4.autThetaQuot, Sec4.autIn, Subgroup.map_map, inf_eq_left.mpr hAL]
    rfl
  have hPe : CFSG.Assembly.IsElemAbelian 3 (PS.bar L A) := by
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
  have hP9 := PS.card_bar_A hA hbA hb1 hAL hsec'
  rw [hP]
  by_cases hsolX : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L)
  · exact sigImg148_of_solvable hsolX (fun g => ⟨1, Subtype.ext (by simpa using hPe.2 g g.2)⟩)
  · obtain ⟨ha, hb, hc⟩ := h Γ A L b hA hbA hb1 hLb hAL hsec hF h131 hT h46 hloc hsolX
    rw [hP] at ha hc
    have hs := PS.isSimpleGroup_of_types148 hT hsolX
    have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
      haveI := hs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) with hZ | hZ
      · exact hZ
      · exfalso
        apply hsolX
        have hcomm : ∀ x y : ↥L ⧸ aschbacherSolvableCore 3 ↥L, x * y = y * x := by
          intro x y
          have hx : x ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
            rw [hZ]; exact Subgroup.mem_top x
          exact (Subgroup.mem_center_iff.mp hx y).symm
        exact Group.isSolvable_of_comm hcomm
    exact sigImg148_of_insp hZ hPe hP9 ha hb hc

theorem kf148PointSigF_of_insp (h : KF148PointSigInsp) : KF148PointSigF :=
  kf148PointSigF_of_img (kf148PointSigImg_of_insp h)

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
