module

public import CFSG.Quasithin.H13.U3S1348L

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W] {J : Subgroup (MulAut W)}
  {𝓗 : Finset (Subgroup (MulAut W))}

omit [Finite W] in
theorem fix_of_cube_of_card_four {U : Subgroup W} (hU : Nat.card U = 4)
    (hU2 : ∀ w ∈ U, w ^ 2 = 1) {y : MulAut W} (hyU : ∀ w ∈ U, y w ∈ U) (hy3 : y ^ 3 = 1)
    {u : W} (hu : u ∈ U) (hu1 : u ≠ 1) (hyu : y u = u) : ∀ w ∈ U, y w = w := by
  have hu2 : u ^ 2 = 1 := hU2 u hu
  have hzU : zpowers u ≤ U := zpowers_le.2 hu
  have hidx : ((zpowers u).subgroupOf U).index = 2 := by
    have h1 := ((zpowers u).subgroupOf U).index_mul_card
    have h2 : Nat.card ↥((zpowers u).subgroupOf U) = 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hzU).toEquiv, Nat.card_zpowers]
      exact orderOf_eq_prime hu2 hu1
    rw [hU, h2] at h1
    omega
  have hyz : ∀ w ∈ zpowers u, y w = w := fun w hw => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    rw [map_zpow, hyu]
  intro w hw
  by_cases hwz : w ∈ zpowers u
  · exact hyz w hwz
  have hywz : y w ∉ zpowers u := by
    intro h
    have h2 : y w = w := y.injective (hyz _ h)
    exact hwz (h2 ▸ h)
  have hmem := (mul_mem_iff_of_index_two hidx (a := ⟨y w, hyU w hw⟩)
    (b := ⟨w⁻¹, inv_mem hw⟩)).2 (by
      simp only [mem_subgroupOf]
      exact ⟨fun h => absurd h hywz, fun h => absurd (by simpa using inv_mem h) hwz⟩)
  rw [mem_subgroupOf, Subgroup.coe_mul] at hmem
  rcases IsTransvectionBlocks.eq_one_or_eq_of_sq_eq_one hu2 hmem with h | h
  · exact mul_inv_eq_one.1 h
  · exfalso
    have hyw : y w = u * w := by
      calc y w = (y w * w⁻¹) * w := by group
        _ = u * w := by rw [h]
    have hy2 : y (y w) = w := by
      rw [hyw, map_mul, hyu, hyw, ← mul_assoc, ← pow_two, hu2, one_mul]
    have hy3w : (y ^ 3) w = y w := by
      rw [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply, hy2]
    rw [hy3, MulAut.one_apply] at hy3w
    apply hu1
    have h3 : u * w = w := hyw.symm.trans hy3w.symm
    exact mul_eq_right.1 h3

omit [Finite W] in
theorem blk_eq_one_of_fix (hb : IsTransvectionBlocks J 𝓗) {K : Subgroup (MulAut W)}
    (hK : K ∈ 𝓗) {k : MulAut W} (hk : k ∈ K)
    (hfix : ∀ u ∈ commSub (⊤ : Subgroup W) K, k u = u) : k = 1 := by
  obtain ⟨C, -, hCU, hC⟩ := hb.exists_compl K hK
  ext w
  have hw : w ∈ C ⊔ commSub (⊤ : Subgroup W) K := by
    rw [hCU]
    exact mem_top w
  obtain ⟨c, hc, v, hv, rfl⟩ := mem_sup.1 hw
  rw [MulAut.one_apply, map_mul, hC k hk c hc, hfix v hv]

omit [Finite W] in
theorem blk_eq_one_of_cube_fix (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    {K : Subgroup (MulAut W)} (hK : K ∈ 𝓗) {y : MulAut W} (hy : y ∈ K) (hy3 : y ^ 3 = 1)
    {u : W} (hu : u ∈ commSub (⊤ : Subgroup W) K) (hu1 : u ≠ 1) (hyu : y u = u) : y = 1 :=
  blk_eq_one_of_fix hb hK hy (fix_of_cube_of_card_four (hb.card_comm K hK) (fun w _ => hW w)
    (hb.stab K hK y hy) hy3 hu hu1 hyu)

theorem exists_fixed_of_isPGroup {U : Subgroup W} (hU : Nat.card U = 4)
    {P : Subgroup (MulAut W)} (hP : IsPGroup 2 P) (hPU : ∀ p ∈ P, ∀ w ∈ U, p w ∈ U) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ p ∈ P, p u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction ↥P ↥U :=
    { smul := fun p w => ⟨(p : MulAut W) w, hPU p p.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun p q w => Subtype.ext rfl }
  have h1 : (1 : ↥U) ∈ MulAction.fixedPoints ↥P ↥U := fun p =>
    Subtype.ext (map_one (p : MulAut W))
  obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥U
    (by rw [hU]; norm_num) h1
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), fun p hp => ?_⟩
  exact congrArg Subtype.val (hb ⟨p, hp⟩)

omit [Finite W] in
theorem blk_exists_res (hb : IsTransvectionBlocks J 𝓗) {K : Subgroup (MulAut W)}
    (hK : K ∈ 𝓗) {g : MulAut W} (hg : ∀ w ∈ commSub (⊤ : Subgroup W) K, g w ∈ commSub ⊤ K)
    (hg' : ∀ w ∈ commSub (⊤ : Subgroup W) K, g⁻¹ w ∈ commSub ⊤ K) :
    ∃ k ∈ K, ∀ u ∈ commSub (⊤ : Subgroup W) K, g u = k u := by
  set U := commSub (⊤ : Subgroup W) K with hU
  have hgs : g ∈ stabSub U := fun w =>
    ⟨fun h => by simpa using hg' _ h, fun h => hg w h⟩
  have hmem : resHom U ⟨g, hgs⟩ ∈ autSub K U := by
    rw [hb.autSub_eq_top K hK]
    exact mem_top _
  obtain ⟨g', hg'K, hg'eq⟩ := mem_autSub.1 hmem
  refine ⟨g', hg'K, fun u hu => ?_⟩
  have := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : W)) hg'eq
  simp only [resHom_apply] at this
  exact this.symm

theorem blk_exists_adjust (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    {K : Subgroup (MulAut W)} (hK : K ∈ 𝓗) {g y τ : MulAut W}
    (hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hy : y ∈ K) (hy3 : orderOf y = 3) (hgy : g * y = y * g)
    (hτ : τ ∈ K) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1) :
    ∃ j : ℕ, (y ^ j)⁻¹ * g * τ = τ * ((y ^ j)⁻¹ * g) := by
  have h6 := hb.card_eq K hK
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hzK : zpowers y ≤ K := zpowers_le.2 hy
  have hidx : ((zpowers y).subgroupOf K).index = 2 := by
    have h1 := ((zpowers y).subgroupOf K).index_mul_card
    have h2 : Nat.card ↥((zpowers y).subgroupOf K) = 3 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hzK).toEquiv, Nat.card_zpowers, hy3]
    rw [h6, h2] at h1
    omega
  have hτz : τ ∉ zpowers y := by
    intro h
    have h3 : τ ^ 3 = 1 := by
      have := orderOf_dvd_natCard (⟨τ, h⟩ : ↥(zpowers y))
      rw [Subgroup.orderOf_mk, Nat.card_zpowers, hy3] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hτ2]; group
  have hgc : Commute g y := hgy
  have hσz : g * τ * g⁻¹ ∉ zpowers y := by
    intro h
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h
    apply hτz
    have e : τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
    rw [e, ← hi]
    have e2 : g⁻¹ * y ^ i * g = y ^ i := by
      rw [mul_assoc, ← (hgc.zpow_right i).eq]
      group
    rw [e2]
    exact zpow_mem_zpowers y i
  have hmem := (mul_mem_iff_of_index_two hidx (a := ⟨τ⁻¹, inv_mem hτ⟩)
    (b := ⟨g * τ * g⁻¹, hgK τ hτ⟩)).2 (by
      simp only [mem_subgroupOf]
      exact ⟨fun h => absurd (by simpa using inv_mem h) hτz, fun h => absurd h hσz⟩)
  rw [mem_subgroupOf, Subgroup.coe_mul] at hmem
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hmem
  set j := (m % 3).toNat with hj
  have hyj : y ^ j = y ^ m := by
    rw [hj, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num)),
      ← zpow_mod_orderOf y m, hy3]
    norm_num
  refine ⟨j, ?_⟩
  have hσ : g * τ * g⁻¹ = τ * y ^ j := by
    rw [hyj, hm]
    group
  have hinv := block_conj_eq_inv hW hb hK hy hy3 hτ hτ2 hτ1
  have hinvj : τ * y ^ j * τ⁻¹ = (y ^ j)⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hyτ : (y ^ j)⁻¹ * τ = τ * y ^ j := by
    rw [← hinvj]
    group
  have hy3j : y ^ j * y ^ j * y ^ j = 1 := by
    rw [← pow_add, ← pow_add, show j + j + j = 3 * j by ring, pow_mul, hy3', one_pow]
  calc (y ^ j)⁻¹ * g * τ = (y ^ j)⁻¹ * (g * τ * g⁻¹) * g := by group
    _ = (y ^ j)⁻¹ * τ * y ^ j * g := by rw [hσ]; group
    _ = τ * y ^ j * y ^ j * g := by rw [hyτ]
    _ = τ * (y ^ j * y ^ j * y ^ j) * ((y ^ j)⁻¹ * g) := by group
    _ = τ * ((y ^ j)⁻¹ * g) := by rw [hy3j, mul_one]

end CFSG.Quasithin.H13.U3
