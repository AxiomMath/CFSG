module

public import CFSG.Quasithin.Background.F918M6
public import CFSG.Quasithin.Background.F918H4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Glued

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

@[expose] def D36QhatGlued : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ¬ IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)

theorem d36_part2_direct (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hd : IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V)) :
    qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hD := n.std.hyp
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    hD.Mp_eq ▸ le_normalizer_conjClosure L T
  have hMpM : Mp ≤ M := by
    rw [hD.Mp_eq]
    exact conjClosure_le fun s hs z hz =>
      M.mul_mem (M.mul_mem (hD.sylow.1 hs) (le_of_mem_cComp hD.comp hz)) (M.inv_mem (hD.sylow.1 hs))
  have hSyl : IsSylowTwoOf T (Mp ⊔ T) :=
    F7.isSylowTwoOf_mono_right hD.sylow le_sup_right (sup_le hMpM hD.sylow.1)
  have hVinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := fun x hx v hv => n.std.irrT.1.2.1 ⟨x, hx⟩ v hv
  have hMpS : Mp ≤ stabSub (orbSup T V) := D36.le_stabSub_orbSup_Mp hTn hVinv
  have hLMp : L ≤ Mp := by
    rw [n.Mp_eq]
    exact le_sup_left
  have hVU : V ≤ commSub (orbSup T V) L :=
    D36.le_commSub_of_commOf n.Mp_eq (le_orbSup T V) hVinv n.triv n.std.irrT.1.2.2.1
  have hUV : commSub (orbSup T V) L ≤ orbSup T V :=
    commSub_le_of_invariant fun x hx w hw => ((hMpS (hLMp hx)) w).mpr hw
  exact D36.part2_aux hD.exp rfl le_sup_right (sup_le hMpS (le_stabSub_orbSup T V)) hSyl
    n.std.qhat hVU hUV fun D hDT hDm => d36ActsDirect_of hL38 W M Mp T L V t n hd D hDT hDm

theorem d36_part2_q (hL38 : D3L38) (hQ : D36QhatGlued) (n : D36Norm M Mp T L V t) :
    qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  by_cases hd : IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V)
  · exact d36_part2_direct hL38 n hd
  · exact hQ W M Mp T L V t n hd

theorem d36c_of_named_inputs_q (h35 : D35) (hQ : D36QhatGlued)
    (hA38 : D36A38) (hL38 : D3L38) : D36c := by
  intro W _ _ M Mp T L V std hlt t ht htn hMp
  have key : ∀ {L : Subgroup (MulAut W)} {t : MulAut W}, D36Norm M Mp T L V t →
      D36cConcl Mp T L V t := by
    intro L t n
    have h2 := d36_part2_q hL38 hQ n
    exact ⟨n.triv, d36_part1 hL38 n, h2, d36_part3 h35 hA38 hL38 n h2⟩
  rcases d36_reduce h35 hL38 std hlt ht htn hMp with n | n
  · exact Or.inl (key n)
  · exact Or.inr (key n)

end Glued

end CFSG.Quasithin
