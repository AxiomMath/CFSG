module

public import CFSG.Quasithin.Background.SmithB45MatQ
public import Certificates.Certificate7190

public section

namespace CFSG.Quasithin.H13.Prop329

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.B45Mat

variable {V : Type*} [CommGroup V] [Finite V]

theorem two_le_qhatOf_of_forall' {X : Subgroup (MulAut V)}
    (h : ∀ A, IsA2 X A → commSeries A 3 = ⊥ → 2 * rk ↥A ≤ rkIdx (fixV A)) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf X := by
  refine le_kq_iff.mpr fun A hA hA3 => ?_
  have hpos := hA.isElemAbelian2.rk_pos hA.ne_bot
  have h2 := h A hA hA3
  unfold rAV
  rw [le_div_iff₀ (by exact_mod_cast hpos)]
  exact_mod_cast h2

theorem two_le_qhatOf_m12Ten
    {L G : Subgroup (MulAut V)} (hLG : IsOver L G) (h : M12Ten L ⊤ ⊥)
    (hrk : ∀ A : Subgroup (MulAut V), A ≤ G → IsElemAbelian2 A → rk ↥A ≤ 3) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf G := by
  obtain ⟨e, he⟩ := m12_std h
  refine two_le_qhatOf_of_forall' fun A hA _ => ?_
  have hc := B45Mat.card_eq_two_pow_rk hA.isElemAbelian2
  have hk := hrk A hA.1 hA.isElemAbelian2
  have hsearch : forallGreedyAll pos12s2 inv12s2 (predR 10 act12s2) 3 [] = true :=
    Certificates.certificate7190
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psi12 rhoC12_m24Pair_injective phi12
    (T12s2.toSub_injective _ _) card_T12s2 (fun _ h1 h2 => T12s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos12s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 3 [] hsearch _ hk)) e
    (map_le_of_normalizer hLG he normalizer_rhoC12 hA.1) hA.isElemAbelian2 hc
  rw [rk_of_chain hchain (chainAut_injective rhoC12_m24Pair_injective
      (T12s2.toSub_injective _ _) g) hind, rkIdx_fixV_of_chain (chainAct12 e g) hchain]
  have hne : l.isEmpty = false :=
    List.isEmpty_eq_false_iff.2 (ne_nil_of_chainSub hchain hA.ne_bot)
  simpa [predR, hne] using hpred

end CFSG.Quasithin.H13.Prop329
