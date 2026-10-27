module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3Steps1To5
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma63Step6Aligned
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3Step7
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma63Step8

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Glauberman

universe u

open scoped commutatorElement IsMulCommutative

/-- The eight-step minimal-counterexample core of Glauberman Lemma 6.3:
every finite minimal non-`p`-stable group for odd `p` is isomorphic to
`Qd(p)`. -/
public theorem minimal_bad_group_equiv_qd
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {Q : Type u} [Group Q] [Finite Q]
    (hbad : ¬ pStable p Q)
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B)) :
    Nonempty (Q ≃* Qd p) := by
  classical
  obtain ⟨H, hHnormal, hHelem, x, hHne, hHminimal, hHp, hCp,
      hcomm, hxout, w, rho, hrhoinj, hrhoirr, hrhoeval,
      xq, yq, hxq, hyq, hgen, hx2, hxn, hy2, hyn⟩ :=
    lemma6_3_steps1_to5 hbad hmin
  let : H.Normal := hHnormal
  let : IsElementaryAbelian p H := hHelem
  let : IsMulCommutative H := hHelem.toIsMulCommutative
  let : Module (ZMod p) (Additive H) :=
    IsElementaryAbelian.isVectorSpace p
  have hminSub : ∀ B : Subgroup Q,
      Nat.card B < Nat.card Q → pStable p B := by
    intro B hBcard
    have hquotCard : Nat.card (B ⧸ (⊥ : Subgroup B)) < Nat.card Q := by
      calc
        Nat.card (B ⧸ (⊥ : Subgroup B)) = Nat.card B :=
          Nat.card_congr (QuotientGroup.quotientBot (G := B)).toEquiv
        _ < Nat.card Q := hBcard
    have hstableQuot : pStable p (B ⧸ (⊥ : Subgroup B)) :=
      hmin B (⊥ : Subgroup B) hquotCard
    exact (pStable_iso (QuotientGroup.quotientBot (G := B))).mp hstableQuot
  have hgenSwap : Subgroup.closure ({yq, xq} : Set
      (Q ⧸ Subgroup.centralizer (H : Set Q))) = ⊤ := by
    simpa [Set.pair_comm] using hgen
  let D : Lemma62Data p hpodd (Additive H)
      (Q ⧸ Subgroup.centralizer (H : Set Q)) :=
    { ρ := rho
      faithful := hrhoinj
      irreducible := hrhoirr
      two_generators := ⟨yq, xq, hgenSwap, hy2, hyn, hx2, hxn⟩ }
  obtain ⟨coord, e, hintertwine⟩ :=
    lemma63_step6_aligned hpodd hminSub H hHnormal hHne hHp
      (inferInstance : IsMulCommutative H) x hcomm D yq xq hxq hgenSwap
      hy2 hyn hx2 hxn
  have hHleC : H ≤ Subgroup.centralizer (H : Set Q) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := H)).2 inferInstance
  obtain ⟨T2, _hT2p, _hCNtop, htop, hEbot, hCeq, _hcomp⟩ :=
    lemma6_3_step7_centralizer_eq hpodd hmin H hHnormal hHp hHne
      hHleC hCp x hcomm hxout rho hrhoeval coord e hintertwine
  exact qd_equiv_of_step7_complement_data
    H (Subgroup.centralizer (H : Set Q))
      (Subgroup.normalizer (T2 : Set Q)) hHnormal
      htop hEbot hCeq rho hrhoeval coord e hintertwine

end CFSG.Glauberman
