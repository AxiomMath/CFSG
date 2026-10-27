module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase
public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ} (M : Model n)

theorem fixW_zpowers_eq_ker (σ : Perm (Fin n)) :
    fixW M (Subgroup.zpowers σ) = (delHom (M.act σ)).ker := by
  ext w
  rw [mem_fixW_zpowers, mem_ker_delHom]

theorem act_pow_eq (σ : Perm (Fin n)) (k : ℕ) : M.act (σ ^ k) = M.act σ ^ k := map_pow _ _ _

theorem isInvSub_zpowers_iff (σ : Perm (Fin n)) (U : Subgroup M.W) :
    IsInvSub M (Subgroup.zpowers σ) U ↔ ∀ u ∈ U, M.act σ u ∈ U := by
  refine ⟨fun h u hu => h σ (Subgroup.mem_zpowers σ) u hu, fun h => ?_⟩
  have hpow : ∀ k : ℕ, ∀ u ∈ U, M.act (σ ^ k) u ∈ U := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [pow_succ', act_mul_apply]
      exact h _ (ih u hu)
  intro b hb u hu
  rw [Subgroup.mem_zpowers_iff] at hb
  obtain ⟨z, rfl⟩ := hb
  have hz : σ ^ z = σ ^ (z % (orderOf σ : ℤ)).toNat := by
    have hpos : 0 < (orderOf σ : ℤ) := by exact_mod_cast orderOf_pos σ
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), zpow_mod_orderOf]
  rw [hz]
  exact hpow _ u hu

theorem commW_zpowers_eq_map (σ : Perm (Fin n)) {U : Subgroup M.W}
    (hU : IsInvSub M (Subgroup.zpowers σ) U) :
    commW M (Subgroup.zpowers σ) U = U.map (delHom (M.act σ)) := by
  apply le_antisymm
  · unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨b, hb, u, hu, rfl⟩
    have key : ∀ b ∈ Subgroup.zpowers σ, ∀ u ∈ U,
        M.act b u * u⁻¹ ∈ U.map (delHom (M.act σ)) := by
      intro b hb
      rw [Subgroup.zpowers_eq_closure] at hb
      induction hb using Subgroup.closure_induction with
      | mem x hx =>
        intro u hu
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨u, hu, rfl⟩
      | one => intro u hu; simp
      | mul x y hx' hy' hx hy =>
        intro u hu
        have e : M.act (x * y) u * u⁻¹ =
            (M.act x (M.act y u) * (M.act y u)⁻¹) * (M.act y u * u⁻¹) := by
          rw [act_mul_apply]; group
        rw [e]
        have hyu : M.act y u ∈ U := hU y (by rwa [Subgroup.zpowers_eq_closure]) u hu
        exact Subgroup.mul_mem _ (hx _ hyu) (hy u hu)
      | inv x hx' hx =>
        intro u hu
        have hxu : M.act x⁻¹ u ∈ U :=
          hU x⁻¹ (Subgroup.inv_mem _ (by rwa [Subgroup.zpowers_eq_closure])) u hu
        have e : M.act x⁻¹ u * u⁻¹ = (M.act x (M.act x⁻¹ u) * (M.act x⁻¹ u)⁻¹)⁻¹ := by
          rw [act_act_inv]; group
        rw [e]
        exact Subgroup.inv_mem _ (hx _ hxu)
    exact key b hb u hu
  · rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.subset_closure ⟨σ, Subgroup.mem_zpowers σ, u, hu, rfl⟩

theorem commW_top_zpowers_eq_range (σ : Perm (Fin n)) :
    commW M (Subgroup.zpowers σ) ⊤ = (delHom (M.act σ)).range := by
  rw [commW_zpowers_eq_map M σ (fun _ _ _ _ => Subgroup.mem_top _), MonoidHom.range_eq_map]

theorem bf1 (b : Perm (Fin n)) :
    (fixW M (Subgroup.zpowers b)).index = Nat.card (commW M (Subgroup.zpowers b) ⊤) := by
  rw [fixW_zpowers_eq_ker, commW_top_zpowers_eq_range, Subgroup.index_ker]

theorem act_mul_act_eq_one {b : Perm (Fin n)} (hb : b * b = 1) : M.act b * M.act b = 1 := by
  rw [← map_mul, hb, map_one]

theorem commW_le_fixW_of_sq {b : Perm (Fin n)} (hb : b * b = 1) :
    commW M (Subgroup.zpowers b) ⊤ ≤ fixW M (Subgroup.zpowers b) := by
  rw [fixW_zpowers_eq_ker, commW_top_zpowers_eq_range]
  rintro _ ⟨y, rfl⟩
  exact delHom_delHom_eq_one (hsq := M.sq) (act_mul_act_eq_one M hb) y

theorem commW_commW_eq_bot_of_sq {b : Perm (Fin n)} (hb : b * b = 1) :
    commW M (Subgroup.zpowers b) (commW M (Subgroup.zpowers b) ⊤) = ⊥ := by
  rw [commW_zpowers_eq_map M b (isInvSub_commW M (fun _ _ _ _ => Subgroup.mem_top _)),
    commW_top_zpowers_eq_range, eq_bot_iff]
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact delHom_delHom_eq_one (hsq := M.sq) (act_mul_act_eq_one M hb) y

theorem odd_orderOf_act {g : Perm (Fin n)} (hg : Odd (orderOf g)) : Odd (orderOf (M.act g)) :=
  Odd.of_dvd_nat hg (orderOf_map_dvd M.act g)

theorem bf3_isCompl {g : Perm (Fin n)} (hg : Odd (orderOf g)) :
    IsCompl (fixW M (Subgroup.zpowers g)) (commW M (Subgroup.zpowers g) ⊤) := by
  rw [fixW_zpowers_eq_ker, commW_top_zpowers_eq_range]
  refine isCompl_ker_range_delHom_of_odd M.sq (m := orderOf (M.act g)) (odd_orderOf_act M hg)
    (pow_orderOf_eq_one _)

theorem bf3_commW_commW {g : Perm (Fin n)} (hg : Odd (orderOf g)) :
    commW M (Subgroup.zpowers g) (commW M (Subgroup.zpowers g) ⊤) =
      commW M (Subgroup.zpowers g) ⊤ := by
  rw [commW_zpowers_eq_map M g (isInvSub_commW M (fun _ _ _ _ => Subgroup.mem_top _)),
    commW_top_zpowers_eq_range]
  exact map_delHom_range_of_odd M.sq (m := orderOf (M.act g)) (odd_orderOf_act M hg)
    (pow_orderOf_eq_one _)

theorem bf3_split {g : Perm (Fin n)} (hg : Odd (orderOf g)) {U : Subgroup M.W}
    (hU : IsInvSub M (Subgroup.zpowers g) U) {u : M.W} (hu : u ∈ U) :
    ∃ c ∈ U ⊓ fixW M (Subgroup.zpowers g), ∃ r ∈ U ⊓ commW M (Subgroup.zpowers g) ⊤, c * r = u := by
  rw [fixW_zpowers_eq_ker, commW_top_zpowers_eq_range]
  exact exists_mem_ker_range_of_odd M.sq (m := orderOf (M.act g)) (odd_orderOf_act M hg)
    (pow_orderOf_eq_one _) U (fun x hx => hU g (Subgroup.mem_zpowers g) x hx) hu

theorem bf3_sup_eq {g : Perm (Fin n)} (hg : Odd (orderOf g)) {U : Subgroup M.W}
    (hU : IsInvSub M (Subgroup.zpowers g) U) :
    (U ⊓ fixW M (Subgroup.zpowers g)) ⊔ (U ⊓ commW M (Subgroup.zpowers g) ⊤) = U := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro u hu
    obtain ⟨c, hc, r, hr, rfl⟩ := bf3_split M hg hU hu
    exact Subgroup.mul_mem_sup hc hr

theorem ml0 {B : Subgroup (Perm (Fin n))} {Γ : Set (Perm (Fin n))} (hΓB : Γ ⊆ B)
    (hΓodd : ∀ γ ∈ Γ, Odd (orderOf γ)) (hgen : B ≤ Subgroup.closure Γ) {U : Subgroup M.W}
    (hU : U ≤ fixW M B) {v : M.W} (hv : ∀ b ∈ B, M.act b v * v⁻¹ ∈ U) : v ∈ fixW M B := by
  have hΓ : ∀ γ ∈ Γ, M.act γ v = v := by
    intro γ hγ
    have hmem : delHom (M.act γ) v ∈ fixW M B := hU (hv γ (hΓB hγ))
    have h2 : delHom (M.act γ) (delHom (M.act γ) v) = 1 := by
      rw [delHom_apply (M.act γ) (delHom (M.act γ) v)]
      rw [hmem γ (hΓB hγ)]
      exact mul_inv_cancel _
    refine eq_of_iterate_delHom_eq_one_of_odd M.sq (odd_orderOf_act M (hΓodd γ hγ)) (k := 2) ?_
    simpa using h2
  intro b hb
  have : v ∈ fixW M (Subgroup.closure Γ) := (mem_fixW_closure M).mpr hΓ
  exact this b (hgen hb)

theorem ml0_fixW {B : Subgroup (Perm (Fin n))}
    (hgen : B ≤ Subgroup.closure {x | x ∈ B ∧ Odd (orderOf x)}) {v : M.W}
    (hv : ∀ b ∈ B, M.act b v * v⁻¹ ∈ fixW M B) : v ∈ fixW M B :=
  ml0 M (Γ := {x | x ∈ B ∧ Odd (orderOf x)}) (fun _ h => h.1) (fun _ h => h.2) hgen le_rfl hv

end CFSG.Quasithin.F53Mod
