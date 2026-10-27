module

public import CFSG.Quasithin.Background.D36Support
public import CFSG.Quasithin.Background.F918H0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique


section Main

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d36_part2 (_hL38 : D3L38) (hA : D36Acts) (n : D36Norm M Mp T L V t) :
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
    n.std.qhat hVU hUV fun D hDT hDm => hA W M Mp T L V t n D hDT hDm

end Main

end CFSG.Quasithin
