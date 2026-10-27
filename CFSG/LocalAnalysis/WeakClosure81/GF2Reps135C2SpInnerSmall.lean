module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpSmallRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInner
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w135c2_sp_inner_small_natural
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htL : t ∈ L) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ} (hn : 3 ≤ n)
    (hf : f = 2 ∨ f = 3) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) :
    IsSpn ↥L (2 * n) f ∧ NatSpn L ⊤ ⊥ (2 * n) f := by
  classical
  have hZ : Subgroup.center ↥L = ⊥ := w135c2_center_eq_bot_of_lieModel_psp hctx hlie
  have hL' : LieModel ↥L .PSp n 2 f := LieModel.of_quotient_center hZ hlie
  obtain ⟨F, instF, instFin, hF, ⟨e⟩⟩ := w135c2_nonempty_equiv_statedSp_of_lieModel_psp hL'
  let hField : Field F := instF
  let hFinite : Finite F := instFin
  let hFintype : Fintype F := Fintype.ofFinite F
  let hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hCharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hS : IsSpn ↥L (2 * n) f := by
    unfold IsSpn
    rw [show 2 * n / 2 = n by exact Nat.mul_div_cancel_left n (by norm_num)]
    exact ⟨⟨n, by omega⟩, F, instF, instFin, hF, ⟨e.symm⟩⟩
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  obtain ⟨V, _, _, _, ρ, θ, hρ, hθ⟩ := cu_binModel hW hirr e
  let y : StatedSp n F := e.symm ⟨t, htL⟩
  have hey : e y = ⟨t, htL⟩ := e.apply_symm_apply _
  have hge : ((e y : ↥L) : MulAut W) = t := by rw [hey]
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  have hy2 : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey]
    exact Subtype.ext htt
  have hy1 : y ≠ 1 := by
    intro h1
    have h2 : e y = 1 := by rw [h1, map_one]
    have h3 : (⟨t, htL⟩ : ↥L) = 1 := by rw [← hey]; exact h2
    have ht1 : t = 1 := by simpa using congrArg Subtype.val h3
    rw [ht1, orderOf_one] at ht2
    omega
  have hρy : ρ y ≠ 1 := rho_ne_one_of_conj e hθ hge ht2
  refine ⟨hS, ?_⟩
  rcases sp_small_natural_or_four_le (K := F) (n := n) (f := f) (V := V) (ρ := ρ) (y := y)
      hn hf hF hρ ⟨y, hρy⟩ hy2 hy1 with ⟨β, hβ⟩ | hrank
  · exact natSpn_of_linearizes (F := F) (f := f) hF e hθ (β := β) hβ
  · exact absurd (four_le_mQuot_of_rank e hθ hge hrank) (by omega)

end CFSG.LocalAnalysis.WeakClosure81
