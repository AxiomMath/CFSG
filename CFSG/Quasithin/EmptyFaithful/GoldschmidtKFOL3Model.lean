module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AutTransport
public import CFSG.RankThree.SubgroupLists.LinearThreeFamily
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.SBd18Out

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GorensteinWalter.FieldTransport
  CFSG.RankThree.SubgroupLists CFSG.QuasithinUnique.Ch1
open scoped MatrixGroups

theorem exists_mulEquiv_projectiveSL_zmod {S : Type} [Group S] {p : ℕ} [Fact p.Prime]
    (h : IsPSL 3 p 1 S) : Nonempty (S ≃* projectiveSL 3 (ZMod p)) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hKF : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card, hcard, pow_one]
  have : CharP F p := charP_of_card_eq_prime hKF
  let σ : ZMod p ≃+* F := ZMod.ringEquiv F hKF
  exact ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
    ((projectiveSpecialLinearGroupMulEquiv σ.symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod p))))⟩

theorem exists_equiv_quotient_center (p : ℕ) [Fact p.Prime] :
    ∃ H : Subgroup (GL (Fin 3) (ZMod p)),
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) ∧
        Nat.card (Subgroup.center H) ∣ 3 ∧
        Nonempty (projectiveSL 3 (ZMod p) ≃* H ⧸ Subgroup.center H) := by
  let eH : SL(3, ZMod p) ≃*
      (SpecialLinearGroup.toGL : SL(3, ZMod p) →* GL (Fin 3) (ZMod p)).range :=
    MonoidHom.ofInjective SpecialLinearGroup.toGL_injective
  refine ⟨_, fun x hx => (mem_range_toGL_iff x).mp hx, ?_,
    ⟨(LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod p)).symm.trans
      (quotientCenterMulEquiv eH)⟩⟩
  rw [Nat.card_congr (Subgroup.centerCongr eH).toEquiv.symm, card_center_sl3, Nat.card_zmod]
  exact Nat.gcd_dvd_right _ _

theorem fixed_transAut_map {S X : Type} [Group S] [Group X] (ψ : S ≃* X) (w : MulAut S)
    {K : Subgroup S} (hK : K ≤ SBd18.fixedSub w) :
    ∀ x ∈ K.map ψ.toMonoidHom, transAut ψ w x = x := by
  rintro _ ⟨s, hs, rfl⟩
  change transAut ψ w (ψ s) = ψ s
  rw [transAut_apply, SBd18.mem_fixedSub.mp (hK hs)]

theorem transAut_ne_one {S X : Type} [Group S] [Group X] (ψ : S ≃* X) {w : MulAut S}
    (hw : w ≠ 1) : transAut ψ w ≠ 1 := by
  intro h
  apply hw
  ext s
  have h1 := congrArg (fun f : MulAut X => f (ψ s)) h
  simp only [transAut_apply, MulAut.one_apply] at h1
  exact ψ.injective h1

end CFSG.Quasithin.SBd19F
