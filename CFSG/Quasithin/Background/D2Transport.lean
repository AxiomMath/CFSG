module

public import CFSG.Quasithin.Background.D2Params
public import CFSG.Quasithin.Background.FixVTransport

public section

namespace CFSG.Quasithin

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

theorem commSub_map_mulAutCongr (W : Subgroup V) (A : Subgroup (MulAut V)) :
    commSub (W.map e.toMonoidHom) (A.map (MulAut.congr e).toMonoidHom) =
      (commSub W A).map e.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, w', ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, ?_⟩
    simp
  · rintro ⟨c₀, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨(MulAut.congr e).toMonoidHom x, ⟨x, hx, rfl⟩, e w, ⟨w, hw, rfl⟩, ?_⟩
    simp

theorem commIter_map_mulAutCongr (W : Subgroup V) (A : Subgroup (MulAut V)) (k : ℕ) :
    commIter (W.map e.toMonoidHom) (A.map (MulAut.congr e).toMonoidHom) k =
      (commIter W A k).map e.toMonoidHom := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [commIter]; rw [ih, commSub_map_mulAutCongr]

theorem commSeries_map_mulAutCongr (A : Subgroup (MulAut V)) (k : ℕ) :
    commSeries (A.map (MulAut.congr e).toMonoidHom) k = (commSeries A k).map e.toMonoidHom := by
  unfold commSeries
  rw [← commIter_map_mulAutCongr]
  congr 1
  exact (Subgroup.map_top_of_surjective _ e.surjective).symm

theorem rAV_map_mulAutCongr (A : Subgroup (MulAut V)) :
    rAV (A.map (MulAut.congr e).toMonoidHom) = rAV A := by
  unfold rAV
  have h1 : rkIdx ((fixV A).map e.toMonoidHom) = rkIdx (fixV A) := by
    unfold rkIdx
    congr 1
    exact Subgroup.index_map_equiv (fixV A) e
  have h2 : rk ↥(A.map (MulAut.congr e).toMonoidHom) = rk ↥A := by
    unfold rk
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
  rw [fixV_map_congr_equiv, h1, h2]

theorem isA2_map_mulAutCongr {X A : Subgroup (MulAut V)} (h : IsA2 X A) :
    IsA2 (X.map (MulAut.congr e).toMonoidHom) (A.map (MulAut.congr e).toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_, ?_⟩
  · intro hb
    exact h.2.1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr e).injective).mp hb)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.2.2.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h.2.2.2 a ha, map_one]

theorem kq_map_mulAutCongr_le [Finite V] [Finite V'] (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (MulAut.congr e).toMonoidHom) k ≤ kq X k := by
  rcases hx : kq X k with _ | r
  · exact le_top
  · have hr : kq X k ≤ (r : WithTop ℚ) := by rw [hx]; exact le_rfl
    obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp hr
    refine kq_le_iff.mpr ⟨A.map ((MulAut.congr e).toMonoidHom), isA2_map_mulAutCongr e hA, ?_,
      by rw [rAV_map_mulAutCongr]; exact hAr⟩
    rw [commSeries_map_mulAutCongr, hAk, Subgroup.map_bot]

end CFSG.Quasithin
