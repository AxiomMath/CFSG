module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModG

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Quasithin.F53Mod Equiv

theorem pow_val_add {W : Type} [CommGroup W] (hsq : ∀ w : W, w * w = 1) (u : W)
    (a b : ZMod 2) : u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  have key : ∀ a b : ZMod 2, (a + b).val = (a.val + b.val) % 2 := by decide
  have h2 : u ^ 2 = 1 := by rw [pow_two]; exact hsq u
  rw [key, ← pow_eq_pow_mod _ h2, pow_add]

theorem coord_act (σ : Perm (Fin 5)) (v : orth.W) (j : Fin 5) :
    coord (orth.act σ v) j = coord v (σ⁻¹ j) := rfl

theorem coord_mul (v v' : orth.W) (i : Fin 5) :
    coord (v * v') i = (Multiplicative.toAdd ((v : ↥(G6.coreMod 5)).1) i +
      Multiplicative.toAdd ((v' : ↥(G6.coreMod 5)).1) i).val := rfl

theorem coord_one (i : Fin 5) : coord (1 : orth.W) i = 0 := rfl

theorem act_swap_of_fixed {W : Model 5} {u : W.W}
    (hu : ∀ σ : Perm (Fin 5), σ 4 = 4 → W.act σ u = u) (σ : Perm (Fin 5)) (i : Fin 5) :
    W.act σ (W.act (swap 4 i) u) = W.act (swap 4 (σ i)) u := by
  have h4 : (swap 4 (σ i) * σ * swap 4 i) 4 = 4 := by
    simp only [Perm.mul_apply, swap_apply_left, swap_apply_right]
  have h1 := hu _ h4
  rw [act_mul_apply, act_mul_apply] at h1
  rw [← act_mul_apply]
  calc W.act (σ * swap 4 i) u = W.act (swap 4 (σ i) * swap 4 (σ i)) (W.act (σ * swap 4 i) u) := by
        rw [swap_mul_self, map_one]; rfl
    _ = W.act (swap 4 (σ i)) (W.act (swap 4 (σ i)) (W.act σ (W.act (swap 4 i) u))) := by
        rw [act_mul_apply, act_mul_apply]
    _ = W.act (swap 4 (σ i)) u := by rw [h1]

theorem exists_section (W : Model 5) (π : W.W →* orth.W)
    (hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w)) {u : W.W}
    (hu : ∀ σ : Perm (Fin 5), σ 4 = 4 → W.act σ u = u) (hπu : π u ≠ 1) :
    ∃ ι : orth.W →* W.W, (∀ (σ : Perm (Fin 5)) (v : orth.W), W.act σ (ι v) = ι (orth.act σ v)) ∧
      ∀ v, π (ι v) = v := by
  set ui : Fin 5 → W.W := fun i => W.act (swap 4 i) u with hui
  let ι : orth.W →* W.W :=
    { toFun := fun v => ∏ i : Fin 5, ui i ^ coord v i
      map_one' := by simp only [coord_one, pow_zero, Finset.prod_const_one]
      map_mul' := fun v v' => by
        simp only [coord_mul, pow_val_add W.sq, Finset.prod_mul_distrib]
        rfl }
  have hι : ∀ v, ι v = ∏ i : Fin 5, ui i ^ coord v i := fun _ => rfl
  refine ⟨ι, fun σ v => ?_, fun v => ?_⟩
  · rw [hι, hι, map_prod]
    simp only [map_pow, hui, act_swap_of_fixed hu]
    refine Fintype.prod_equiv σ _ _ fun i => ?_
    rw [coord_act]
    simp
  · have hc : ∀ σ : Perm (Fin 5), σ 4 = 4 → orth.act σ (π u) = π u := fun σ hσ => by
      rw [← hπe, hu σ hσ]
    rw [hι, map_prod]
    simp only [map_pow, hui, hπe]
    exact section_eq hπu hc v

theorem isInvSub_ker {W : Model 5} {π : W.W →* orth.W}
    (hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w)) :
    IsInvSub W ⊤ π.ker := fun σ _ w hw => by
  rw [MonoidHom.mem_ker] at hw ⊢
  rw [hπe, hw, map_one]

theorem idx_quot_ker {W : Model 5} {π : W.W →* orth.W} (hπs : Function.Surjective π)
    (hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w))
    (t : Perm (Fin 5)) : idx (W.quot π.ker (isInvSub_ker hπe)) t = idx orth t := by
  rw [idx_quot]
  have e : fixQ W (Subgroup.zpowers t) π.ker = (fixW orth (Subgroup.zpowers t)).comap π := by
    ext w
    rw [mem_fixQ, Subgroup.mem_comap, mem_fixW]
    refine forall₂_congr fun b _ => ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπe, mul_inv_eq_one]
  rw [e, Subgroup.index_comap_of_surjective _ hπs]
  rfl

theorem idx_restrict_ker_le {W : Model 5} {π : W.W →* orth.W} (hπs : Function.Surjective π)
    (hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w))
    {t : Perm (Fin 5)} (ht : t.IsSwap) (h7 : idx W t ≤ 4) :
    idx (W.restrict π.ker (isInvSub_ker hπe)) t ≤ 2 := by
  have h1 := idx_restrict_mul_idx_quot_le W π.ker (isInvSub_ker hπe) t
  rw [idx_quot_ker hπs hπe] at h1
  have ht1 : t ≠ 1 := by
    rintro rfl
    obtain ⟨a, b, hab, hs⟩ := ht
    have := congrArg (fun f => f a) hs
    simp only [Perm.coe_one, id_eq, swap_apply_left] at this
    exact hab this
  have h2 : idx orth t = 2 := ((transvections t ht1).2).mpr ht
  rw [h2] at h1
  omega

theorem eq_one_of_cube {W : Model 5} {d : Perm (Fin 5)} (hd : d ^ 3 = 1) {u c : W.W}
    (h1 : W.act d u = c * u) (h2 : W.act d c = c) : c = 1 := by
  have e1 : W.act d (W.act d (W.act d u)) = c * (c * (c * u)) := by
    simp only [map_mul, h1, h2]
  have e2 : W.act (d ^ 3) u = W.act d (W.act d (W.act d u)) := by
    rw [pow_succ, pow_two, act_mul_apply, act_mul_apply]
  rw [hd, map_one, e1] at e2
  have e3 : c * (c * (c * u)) = c * u := by
    calc c * (c * (c * u)) = (c * c) * (c * u) := by group
      _ = c * u := by rw [W.sq c, one_mul]
  have e4 : (1 : W.W) * u = c * u := by
    rw [one_mul, ← e3]
    exact e2
  exact (mul_right_cancel e4).symm

theorem exists_S4_fixed (W : Model 5) (π : W.W →* orth.W)
    (hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w))
    (V : Subgroup W.W) (hVY : V.map π = fixW orth S5That)
    (hVT : ∀ σ ∈ S5That, ∀ v ∈ V, W.act σ v = v) (hVS : ∀ σ ∈ S5Syl, ∀ v ∈ V, W.act σ v ∈ V)
    (hdd : ∀ e ∈ π.ker, (∀ τ ∈ S5T, W.act τ e = e) → W.act dd e = e) :
    ∃ u : W.W, (∀ σ : Perm (Fin 5), σ 4 = 4 → W.act σ u = u) ∧ π u ≠ 1 := by
  obtain ⟨y, hy, hqy⟩ := exists_Y_moved
  have hyV : y ∈ V.map π := hVY ▸ hy
  obtain ⟨v₀, hv₀, rfl⟩ := hyV
  set u := W.act qq v₀ * v₀⁻¹ with hu
  have huV : u ∈ V := V.mul_mem (hVS qq qq_mem v₀ hv₀) (V.inv_mem hv₀)
  have hπu : π u = orth.act qq (π v₀) * (π v₀)⁻¹ := by rw [hu, map_mul, map_inv, hπe]
  obtain ⟨hc1, hc4⟩ := qq_sub_fixed hy hqy
  rw [← hπu] at hc1 hc4
  have huS : ∀ s ∈ S5Syl, W.act s u = u := by
    intro s hs
    have hfix : u ∈ fixW W S5Syl := by
      rw [S5Syl_eq_closure, mem_fixW_closure]
      intro s hs
      rcases hs with rfl | rfl
      · have h1 : W.act (qq * qq) v₀ = v₀ := hVT _ qq_sq_mem v₀ hv₀
        rw [act_mul_apply] at h1
        rw [hu, map_mul, map_inv, h1, inv_eq_self_of_sq W.sq (W.act qq v₀),
          inv_eq_self_of_sq W.sq v₀, mul_comm]
      · exact hVT _ (Subgroup.subset_closure (by simp)) u huV
    exact hfix s hs
  set e := W.act dd u * u⁻¹ with he
  have heK : e ∈ π.ker := by
    rw [MonoidHom.mem_ker, he, map_mul, map_inv, hπe, hc4 dd dd_four, mul_inv_cancel]
  have heT : ∀ τ ∈ S5T, W.act τ e = e := by
    intro τ hτ
    have h1 : W.act τ (W.act dd u) = W.act dd u := by
      rw [← act_mul_apply]
      have e1 : τ * dd = dd * (dd⁻¹ * τ * dd) := by group
      rw [e1, act_mul_apply, huS _ (S5T_le_S5Syl (dd_norm_T hτ))]
    rw [he, map_mul, map_inv, h1, huS τ (S5T_le_S5Syl hτ)]
  have hde := hdd e heK heT
  have hdu : W.act dd u = e * u := by rw [he]; group
  have he1 := eq_one_of_cube dd_cube hdu hde
  have hdu' : W.act dd u = u := by rw [hdu, he1, one_mul]
  have hdu'' : W.act dd⁻¹ u = u := by
    calc W.act dd⁻¹ u = W.act dd⁻¹ (W.act dd u) := by rw [hdu']
      _ = u := act_inv_act W dd u
  refine ⟨u, fun σ hσ => ?_, hc1⟩
  rcases stab_four_cover σ hσ with h | h | h
  · exact huS σ h
  · have e1 : σ = dd * (dd⁻¹ * σ) := by group
    rw [e1, act_mul_apply, huS _ h, hdu']
  · have e1 : σ = dd * (dd * (dd⁻¹ * dd⁻¹ * σ)) := by group
    rw [e1, act_mul_apply, act_mul_apply, huS _ h, hdu', hdu']

section Endgame

variable {W : Model 5} {π : W.W →* orth.W}
  (hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w))
  {V : Subgroup W.W} (hVinj : ∀ v ∈ V, π v = 1 → v = 1)
  (hVY : V.map π = fixW orth S5That)
  (hVS : ∀ σ ∈ S5Syl, ∀ v ∈ V, W.act σ v ∈ V)
  {t : Perm (Fin 5)} (ht : t.IsSwap) (ht4 : t 4 ≠ 4)

include hπe hVS ht ht4 in
theorem fix_of_card_le_two (h6 : Nat.card (commW W (Subgroup.zpowers t) V) ≤ 2)
    {y₀ : orth.W} (hy₀ : y₀ ∈ fixW orth S5That) (hy₀1 : y₀ ≠ 1) (hty₀ : orth.act t y₀ = y₀)
    {v₀ : W.W} (hv₀ : v₀ ∈ V) (hπv₀ : π v₀ = y₀) : W.act t v₀ = v₀ := by
  by_contra hne
  have hmem : ∀ v ∈ V, W.act t v * v⁻¹ ∈ commW W (Subgroup.zpowers t) V := fun v hv =>
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, hv, rfl⟩
  have hc₀ : W.act t v₀ * v₀⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hv₁ : W.act qq v₀ ∈ V := hVS qq qq_mem v₀ hv₀
  have hπc₁ : π (W.act t (W.act qq v₀) * (W.act qq v₀)⁻¹) ≠ 1 := by
    rw [map_mul, map_inv, hπe, hπe, hπv₀, ne_eq, mul_inv_eq_one]
    exact (swap_facts ht ht4).2.1 y₀ hy₀ hy₀1 hty₀
  have hc₁ : W.act t (W.act qq v₀) * (W.act qq v₀)⁻¹ ≠ 1 := fun h => hπc₁ (by rw [h, map_one])
  have heq := eq_of_card_le_two h6 (hmem v₀ hv₀) hc₀ (hmem _ hv₁) hc₁
  apply hπc₁
  rw [heq, map_mul, map_inv, hπe, hπv₀, hty₀, mul_inv_cancel]

include hπe hVinj hVY hVS ht ht4 in
theorem V_cases {y₀ : orth.W} (hy₀ : y₀ ∈ fixW orth S5That) (hy₀1 : y₀ ≠ 1)
    (hty₀ : orth.act t y₀ = y₀) {v₀ : W.W} (hv₀ : v₀ ∈ V) (hπv₀ : π v₀ = y₀) :
    ∀ v ∈ V, v = 1 ∨ v = v₀ ∨ v = W.act qq v₀ ∨ v = v₀ * W.act qq v₀ := by
  have hv₁ : W.act qq v₀ ∈ V := hVS qq qq_mem v₀ hv₀
  have heq : ∀ v ∈ V, ∀ c ∈ V, π v = π c → v = c := fun v hv c hc h =>
    mul_inv_eq_one.mp (hVinj _ (V.mul_mem hv (V.inv_mem hc)) (by rw [map_mul, map_inv, h,
      mul_inv_cancel]))
  intro v hv
  have hπv : π v ∈ fixW orth S5That := hVY ▸ ⟨v, hv, rfl⟩
  rcases (swap_facts ht ht4).2.2.2 y₀ hy₀ hy₀1 hty₀ (π v) hπv with h | h | h | h
  · exact Or.inl (hVinj v hv h)
  · exact Or.inr (Or.inl (heq v hv v₀ hv₀ (h.trans hπv₀.symm)))
  · exact Or.inr (Or.inr (Or.inl (heq v hv _ hv₁ (by rw [h, hπe, hπv₀]))))
  · exact Or.inr (Or.inr (Or.inr (heq v hv _ (V.mul_mem hv₀ hv₁)
      (by rw [h, map_mul, hπe, hπv₀]))))

end Endgame

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
