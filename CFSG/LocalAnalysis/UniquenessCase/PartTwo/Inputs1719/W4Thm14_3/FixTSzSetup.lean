module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtHolds
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTop
public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Quasithin.JonesParshall CFSG.LieType.Ree
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem exists_szSection_data {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {n : ℕ} (hL : IsSz ↥L n)
    {J : Subgroup W} (hJ : J ∈ irrSet L) (hJC : J ⊓ fixV L ≠ ⊥) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2)
      (_ : Nat.card K = 2 ^ (2 * a + 1)) (π : ↥(CFSG.Blueprint.suzukiGroup a K) ≃* ↥L)
      (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod 2) M) (_ : Finite M)
      (ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a K) M)
      (β : ↥J →* Multiplicative M),
      ρ.IsIrreducible ∧ (∃ g, ρ g ≠ 1) ∧ Function.Surjective β ∧
        (∀ w : ↥J, β w = 1 ↔ (w : W) ∈ J ⊓ fixV L) ∧
        (∀ (γ : ↥(CFSG.Blueprint.suzukiGroup a K)) (w : ↥J)
          (hw : ((π γ : ↥L) : MulAut W) (w : W) ∈ J),
          β ⟨_, hw⟩ = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (β w)))) ∧
        ∃ c : ↥(CFSG.Blueprint.suzukiGroup a K) → Module.Dual (ZMod 2) M,
          c ∈ Z1 ρ.dual ∧ c ∉ B1 ρ.dual := by
  classical
  have hsimple : IsSimpleGroup ↥L :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hL
  obtain ⟨-, a, -, K, hKfield, hKfin, hn_eq, hKcard, ⟨eL⟩⟩ :=
    (CFSG.Blueprint.LieModel.suzukiModel hL).2
  subst n
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := CFSG.QuasithinUnique.Setup.X7b.charP_two_of_card_pow hKcard
  have hLW : L ≤ stabSub J := CFSG.Quasithin.B1.le_stabSub_of_invariant hJ.2.2.1
  have hLC : L ≤ stabSub (J ⊓ fixV L) :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant hJ.2.2.2.1
  have hfaith : L ⊓ centSec J (J ⊓ fixV L) = ⊥ :=
    inf_centSec_eq_bot_of_mem_irrSet hsimple hJ hLW hLC
  obtain ⟨M, hMadd, hMmod, hMfin, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary
      (V := Sec J (J ⊓ fixV L)) fun v => QuotientGroup.induction_on v fun w => by
        rw [← QuotientGroup.mk_mul,
          show w * w = 1 from Subtype.ext (by simpa [pow_two] using hW w),
          QuotientGroup.mk_one]
  letI : AddCommGroup M := hMadd
  letI : Module (ZMod 2) M := hMmod
  letI : Finite M := hMfin
  let θL : ↥(autSec L J (J ⊓ fixV L)) ≃* ↥(CFSG.Blueprint.suzukiGroup a K) :=
    (B5.secEquiv L hLW hLC hfaith).symm.trans eL
  let π : ↥(CFSG.Blueprint.suzukiGroup a K) ≃* ↥L :=
    θL.symm.trans (B5.secEquiv L hLW hLC hfaith).symm
  let ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a K) M :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf θ θL.symm.toMonoidHom
  have hntM : Nontrivial M := by
    obtain ⟨v, hvI, hvI0⟩ := IsConcreteLE.exists_of_lt hJ.2.1
    refine ⟨⟨Multiplicative.toAdd (θ (QuotientGroup.mk ⟨v, hvI⟩)), 0, fun h => hvI0 ?_⟩⟩
    have h1 : θ (QuotientGroup.mk ⟨v, hvI⟩) = 1 :=
      Multiplicative.toAdd.injective (by simpa using h)
    have h2 : (QuotientGroup.mk ⟨v, hvI⟩ : Sec J (J ⊓ fixV L)) = 1 :=
      θ.injective (by rw [h1, map_one])
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  haveI : Nontrivial M := hntM
  have hIrrSec := B5.isIrrSec_autSec hJ.2.1 hJ.2.2.2.2 hLW hLC
  have hIrr : ρ.IsIrreducible :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf_irreducible θ
      (fun J' hJ' => hIrrSec.2 J'
        (fun a' l hl => hJ' (a' : MulAut (Sec J (J ⊓ fixV L))) a'.2 l hl) bot_le le_top)
      θL.symm.surjective
  have hnt : ∃ g, ρ g ≠ 1 := by
    refine ⟨CFSG.LieType.Ree.suzukiSElt a K 1 0, fun h => ?_⟩
    have h1 : θL.symm.toMonoidHom (CFSG.LieType.Ree.suzukiSElt a K 1 0) = 1 :=
      CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf_ker θ θL.symm.toMonoidHom _ h
    have h2 : CFSG.LieType.Ree.suzukiSElt a K 1 0 = 1 :=
      θL.symm.injective (by simpa using h1)
    rw [show (1 : ↥(CFSG.Blueprint.suzukiGroup a K)) =
      CFSG.LieType.Ree.suzukiSElt a K 0 0 from
        (CFSG.LieType.Ree.suzukiSElt_zero_zero hKcard).symm] at h2
    exact one_ne_zero (CFSG.LieType.Ree.suzukiSElt_inj.mp h2).1
  let Z : Subgroup ↥J := (J ⊓ fixV L).subgroupOf J
  let β : ↥J →* Multiplicative M := dualSectionMap θ
  have hβs : Function.Surjective β := dualSectionMap_surjective θ
  have hβk : ∀ w : ↥J, β w = 1 ↔ (w : W) ∈ J ⊓ fixV L :=
    dualSectionMap_eq_one_iff θ
  have hβe : ∀ (γ : ↥(CFSG.Blueprint.suzukiGroup a K)) (w : ↥J)
      (hw : ((π γ : ↥L) : MulAut W) (w : W) ∈ J),
      β ⟨_, hw⟩ = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (β w))) := by
    intro γ w hw
    have hsymm : (((θL.symm.toMonoidHom γ : ↥(autSec L J (J ⊓ fixV L)))) :
        MulAut (Sec J (J ⊓ fixV L))) = B5.secHom L hLW hLC (π γ) := by
      have h1 : (B5.secEquiv L hLW hLC hfaith) (π γ) = θL.symm γ := by
        show (B5.secEquiv L hLW hLC hfaith)
          ((B5.secEquiv L hLW hLC hfaith).symm (θL.symm γ)) = θL.symm γ
        rw [MulEquiv.apply_symm_apply]
      calc ↑(θL.symm.toMonoidHom γ)
          = ↑(θL.symm γ) := rfl
        _ = ↑((B5.secEquiv L hLW hLC hfaith) (π γ)) := by rw [h1]
        _ = B5.secHom L hLW hLC (π γ) := B5.secEquiv_apply L hLW hLC hfaith (π γ)
    have hsec : B5.secHom L hLW hLC (π γ) (QuotientGroup.mk' Z w) =
        QuotientGroup.mk' Z ((resHom J) (Subgroup.inclusion hLW (π γ)) w) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, B5.secHom_mk]
      rfl
    have hR : ρ γ (Multiplicative.toAdd (β w)) =
        Multiplicative.toAdd
          (θ (B5.secHom L hLW hLC (π γ) (QuotientGroup.mk' Z w))) := by
      rw [show ρ = CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf θ
          θL.symm.toMonoidHom from rfl,
        CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf_apply, hsymm]
      rw [show β w = θ (QuotientGroup.mk' Z w) from rfl]
      exact B15P4.binPsi_apply_toAdd θ (B5.secHom L hLW hLC (π γ)) (QuotientGroup.mk' Z w)
    have hge : (⟨((π γ : ↥L) : MulAut W) (w : W), hw⟩ : ↥J) =
        (resHom J) (Subgroup.inclusion hLW (π γ)) w := by
      apply Subtype.ext
      rw [resHom_apply]
      rfl
    show θ (QuotientGroup.mk' Z ⟨_, hw⟩) =
      Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (β w)))
    rw [hge, ← hsec, hR]
    rfl
  obtain ⟨c, hc, hnc⟩ :=
    exists_dual_cocycle_section_of_mulEquiv hW hJ hJC hLW hLC hfaith θ θL
  exact ⟨a, K, hKfield, inferInstance, inferInstance, hKcard, π,
    M, hMadd, hMmod, hMfin, ρ, β, hIrr, hnt, hβs, hβk, hβe, c, hc, hnc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
