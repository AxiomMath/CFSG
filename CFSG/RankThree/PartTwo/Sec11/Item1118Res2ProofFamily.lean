module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2ProofSL3
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofInvElt
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofComm

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def SL3Model1118For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z v : Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) → v ∈ J → v ^ 3 = 1 → v ≠ 1 →
        z ^ 3 = 1 ∧ ∃ (L : Type) (_ : Field L)
          (ρ : Subgroup.centralizer ({v} : Set Z) →* Matrix.SpecialLinearGroup (Fin 3) L),
          Item1118Res2Proof.IsSL3Model ρ

namespace Item1118Res2Proof

variable {F : ∀ (X : Type) [Group X], Prop}

theorem comm_of_mem {Z : Type} [Group Z] {z : Z} {J : Subgroup Z}
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z))) {x : Z} (hx : x ∈ J) :
    x * z = z * x := by
  have h1 := le_of_mem_thetaComponentsIn hJ hx
  rw [Item426.mem_fixSub, MulAut.conj_apply] at h1
  calc x * z = z * x * z⁻¹ * z := by rw [h1]
    _ = z * x := by group

theorem invElt1118For_of_sl3Model (h : SL3Model1118For F) : InvElt1118For F := by
  intro Z _ _ hZ z v g J hz3 hJ hJT hvJ hv3 hv1 hg3 hgv hgz hgz'
  obtain ⟨hz3', L, _, ρ, hρ⟩ := h Z hZ z v J hz3 hJ hJT hvJ hv3 hv1
  have hzv : z * v = v * z := (comm_of_mem hJ hvJ).symm
  exact ⟨g, pow_three_eq_one_of_isSL3Model hρ hv3 hzv hgv hz3' hgz hgz' hg3, rfl, hgv⟩

theorem comm1119For_of_sl3Model (h : SL3Model1118For F) : Comm1119For F := by
  intro Z _ _ hZ z y δ g J hz3 hJ hJT hyJ hyk hy3 hδ hδ3 hδ1 _ hgδ hgz hgz'
  have hδJ : δ ∈ J := (Subgroup.zpowers_le.mpr hyJ) hδ
  obtain ⟨hz3', L, _, ρ, hρ⟩ := h Z hZ z δ J hz3 hJ hJT hδJ hδ3 hδ1
  have hzδ : z * δ = δ * z := (comm_of_mem hJ hδJ).symm
  have hyz : y * z = z * y := comm_of_mem hJ hyJ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
  have hyδ : y * y ^ k = y ^ k * y := ((Commute.refl y).zpow_right k).eq
  obtain ⟨h1, h2⟩ := rel_of_isSL3Model hρ hδ3 hzδ hgδ hz3' hgz hgz' hyδ hyz hyk
  refine ⟨h1, h2, fun w hwk hwy hwg => ?_⟩
  have hwδ : w * y ^ k = y ^ k * w := ((Commute.zpow_right (hwy : Commute w y)) k).eq
  exact mem_zpowers_of_isSL3Model hρ hδ3 hzδ hgδ hz3' hgz hgz' hyδ hyz hyk hy3 hwδ hwk hwy hwg

end Item1118Res2Proof

end CFSG.RankThree.PartTwo.Sec11
