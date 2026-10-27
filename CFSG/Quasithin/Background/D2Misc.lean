module

public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commSeries_eq_bot_of_le {A : Subgroup (MulAut V)} {k k' : ℕ} (hk : k ≤ k')
    (h : commSeries A k = ⊥) : commSeries A k' = ⊥ := by
  induction k', hk using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
    have : commSeries A (m + 1) = commSub (commSeries A m) A := rfl
    rw [this, ih]
    exact commSub_eq_bot_iff.mpr bot_le

theorem kq_anti (X : Subgroup (MulAut V)) {k k' : ℕ} (hk : k ≤ k') : kq X k' ≤ kq X k := by
  unfold kq
  refine Finset.min_mono ?_
  intro s hs
  rw [Set.Finite.mem_toFinset] at hs ⊢
  obtain ⟨A, hA, hAk, rfl⟩ := hs
  exact ⟨A, hA, commSeries_eq_bot_of_le hk hAk, rfl⟩

theorem qhatOf_le_qOf (X : Subgroup (MulAut V)) : qhatOf X ≤ qOf X := kq_anti X (by norm_num)

theorem QhatStar_nonempty {X : Subgroup (MulAut V)} {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) : (QhatStar X).Nonempty := by
  obtain ⟨⟨A₀, hA₀, hA₀k, hA₀r⟩, hle⟩ := kq_eq_coe_iff.mp hr
  have hne : (kRle X 3 r).Nonempty := ⟨A₀, ⟨hA₀, hA₀r.le⟩, hA₀k⟩
  obtain ⟨A, hA, hmin⟩ := (wellFounded_lt (α := Subgroup (MulAut V))).has_min (kRle X 3 r) hne
  refine ⟨A, r, hr, hr2, hA, fun B hB hBA => ?_⟩
  by_contra hne'
  exact hmin B hB (lt_of_le_of_ne hBA hne')

theorem Jhat_le (X : Subgroup (MulAut V)) : Jhat X ≤ X := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  exact hA2.le

theorem le_Jhat {X A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) : A ≤ Jhat X :=
  le_iSup₂_of_le A hA le_rfl

end CFSG.Quasithin
