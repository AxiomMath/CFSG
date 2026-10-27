module

public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem commHom_comp_self (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) (v : V) :
    commHom g (commHom g v) = commHom (g ^ 2) v := by
  have h1 : ∀ x : V, x⁻¹ = x := inv_eq_self_of_sq_eq_one hV
  have h2 : g v * g v = 1 := by rw [← pow_two]; exact hV _
  simp only [commHom_apply, map_mul, pow_two, MulAut.mul_apply, h1 (g v), h1 v]
  calc g (g v) * g v * (g v * v) = g (g v) * (g v * g v) * v := by ac_rfl
    _ = g (g v) * v := by rw [h2, mul_one]

theorem comp_commHom_self (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) :
    (commHom g).comp (commHom g) = commHom (g ^ 2) :=
  MonoidHom.ext fun v => commHom_comp_self hV g v

theorem commSeries_invariant (g : MulAut V) (k : ℕ) :
    ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ commSeries (Subgroup.zpowers g) k,
      x w ∈ commSeries (Subgroup.zpowers g) k := by
  have hE : ∀ a ∈ Subgroup.zpowers g, ∀ b ∈ Subgroup.zpowers g, a * b = b * a := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ((Commute.refl g).zpow_zpow m n).eq
  induction k with
  | zero => exact fun _ _ w _ => Subgroup.mem_top w
  | succ k ih => exact commSub_invariant hE le_rfl ih

variable [Finite V]

theorem commSeries_succ_eq_map (g : MulAut V) (k : ℕ) :
    commSeries (Subgroup.zpowers g) (k + 1) =
      (commSeries (Subgroup.zpowers g) k).map (commHom g) :=
  commSub_zpowers_eq_map (commSeries_invariant g k)

theorem commSeries_two (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) :
    commSeries (Subgroup.zpowers g) 2 = commV (Subgroup.zpowers (g ^ 2)) := by
  have h0 : commSeries (Subgroup.zpowers g) 0 = ⊤ := rfl
  rw [commSeries_succ_eq_map g 1, commSeries_succ_eq_map g 0, h0, Subgroup.map_map,
    comp_commHom_self hV, commV_zpowers_eq_map]

theorem commSeries_add_two (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) (k : ℕ) :
    commSeries (Subgroup.zpowers g) (k + 2) =
      (commSeries (Subgroup.zpowers g) k).map (commHom (g ^ 2)) := by
  rw [commSeries_succ_eq_map g (k + 1), commSeries_succ_eq_map g k, Subgroup.map_map,
    comp_commHom_self hV]

theorem commSeries_four_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} (hg : g ^ 4 = 1) :
    commSeries (Subgroup.zpowers g) 4 = ⊥ := by
  have h0 : commSeries (Subgroup.zpowers g) 0 = ⊤ := rfl
  have h4 : commHom ((g ^ 2) ^ 2) = commHom (1 : MulAut V) := by
    rw [← pow_mul, show 2 * 2 = 4 from rfl, hg]
  rw [commSeries_add_two hV g 2, commSeries_add_two hV g 0, h0, Subgroup.map_map,
    comp_commHom_self hV, h4]
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  rintro _ ⟨v, -, rfl⟩
  simp [commHom_apply]

theorem commSeries_succ_succ_of_eq (g : MulAut V) {k : ℕ}
    (h : commSeries (Subgroup.zpowers g) (k + 1) = commSeries (Subgroup.zpowers g) k) :
    commSeries (Subgroup.zpowers g) (k + 1 + 1) = commSeries (Subgroup.zpowers g) (k + 1) := by
  rw [commSeries_succ_eq_map g (k + 1), h, ← commSeries_succ_eq_map g k, h]

omit [Finite V] in
theorem eq_one_of_commV_eq_bot {g : MulAut V} (h : commV (Subgroup.zpowers g) = ⊥) : g = 1 := by
  rw [commV_eq_commSub, commSub_eq_bot_iff] at h
  ext v
  exact mem_fixV_zpowers_iff.mp (h (Subgroup.mem_top v))

end CFSG.Quasithin
