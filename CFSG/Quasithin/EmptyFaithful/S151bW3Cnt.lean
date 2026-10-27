module

public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

variable {W : Type*} [CommGroup W] [Finite W]

theorem card_modEq_card_inf_fixV151b {U : Subgroup W} {q : ℕ} [Fact q.Prime]
    {Y : Subgroup (MulAut W)} (hY : IsPGroup q Y) (hU : ∀ g ∈ Y, ∀ u ∈ U, g u ∈ U) :
    Nat.card U ≡ Nat.card ↥(U ⊓ fixV Y) [MOD q] := by
  classical
  let s : SubMulAction Y W :=
    { carrier := (U : Set W)
      smul_mem' := fun g v hv => hU g g.2 v hv }
  have h1 := hY.card_modEq_card_fixedPoints s
  have e1 : Nat.card s = Nat.card U := rfl
  have e2 : Nat.card (MulAction.fixedPoints Y s) = Nat.card ↥(U ⊓ fixV Y) := by
    refine Nat.card_congr
      { toFun := fun ω => ⟨(ω.1 : W), ω.1.2, fun g hg => congrArg Subtype.val (ω.2 ⟨g, hg⟩)⟩
        invFun := fun u => ⟨⟨(u : W), u.2.1⟩, fun g => Subtype.ext (u.2.2 g g.2)⟩
        left_inv := fun ω => rfl
        right_inv := fun u => rfl }
  rw [e1, e2] at h1
  exact h1


omit [Finite W] in
theorem inv_eq_self_of_sq151b (hW : ∀ w : W, w ^ 2 = 1) (w : W) : w⁻¹ = w := by
  have := hW w
  rw [pow_two, mul_eq_one_iff_eq_inv] at this
  exact this.symm

theorem avgMap_conj151b {a s : MulAut W} (hs : s ^ 2 = 1) (hsa : s * a * s⁻¹ = a⁻¹) (v : W) :
    avgMap (Subgroup.zpowers a) (s v) = s (avgMap (Subgroup.zpowers a) v) := by
  classical
  have hs1 : s⁻¹ = s := by
    have : s * s = 1 := by rw [← pow_two]; exact hs
    exact inv_eq_of_mul_eq_one_right this
  have hss : s * s = 1 := by rw [← pow_two]; exact hs
  have hmem : ∀ g ∈ Subgroup.zpowers a, s * g * s ∈ Subgroup.zpowers a := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h0 : s * a ^ k * s⁻¹ = (a⁻¹) ^ k := by
      rw [← hsa]
      exact conj_zpow.symm
    rw [hs1] at h0
    rw [h0]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) k
  have := Fintype.ofFinite (Subgroup.zpowers a)
  let φ : Subgroup.zpowers a ≃ Subgroup.zpowers a :=
    { toFun := fun g => ⟨s * g * s, hmem g g.2⟩
      invFun := fun g => ⟨s * g * s, hmem g g.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        show s * (s * (g : MulAut W) * s) * s = g
        calc s * (s * (g : MulAut W) * s) * s = (s * s) * g * (s * s) := by simp only [mul_assoc]
          _ = g := by rw [hss]; simp
      right_inv := fun g => by
        apply Subtype.ext
        show s * (s * (g : MulAut W) * s) * s = g
        calc s * (s * (g : MulAut W) * s) * s = (s * s) * g * (s * s) := by simp only [mul_assoc]
          _ = g := by rw [hss]; simp }
  rw [avgMap_apply, avgMap_apply]
  have h1 : ∀ g : Subgroup.zpowers a, (g : MulAut W) (s v) = s ((φ g : MulAut W) v) := by
    intro g
    show (g * s : MulAut W) v = (s * (s * g * s)) v
    congr 1
    calc (g : MulAut W) * s = (s * s) * g * s := by rw [hss]; simp
      _ = s * (s * g * s) := by simp only [mul_assoc]
  simp only [h1]
  rw [map_prod]
  exact Fintype.prod_equiv φ (fun x => s ((φ x : MulAut W) v)) (fun y => s ((y : MulAut W) v))
    (fun x => rfl)


theorem fixV_inf_eq_bot_of_commSub151b (hW : ∀ w : W, w ^ 2 = 1) {a s : MulAut W}
    {A : Subgroup (MulAut W)} {U : Subgroup W}
    (ha : Odd (orderOf a)) (hs : s ^ 2 = 1) (hsa : s * a * s⁻¹ = a⁻¹)
    (hAgen : ∀ x ∈ A, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * s)
    (haA : a ∈ A) (hUinv : ∀ x ∈ A, ∀ u ∈ U, x u ∈ U) (hcomm : commSub U A = U) :
    U ⊓ fixV (Subgroup.zpowers a) = ⊥ := by
  classical
  set P := Subgroup.zpowers a with hP
  have hPodd : Odd (Nat.card P) := by rw [hP, Nat.card_zpowers]; exact ha
  have hPA : P ≤ A := Subgroup.zpowers_le.mpr haA
  have hπU : ∀ u ∈ U, avgMap P u ∈ U := by
    intro u hu
    have := Fintype.ofFinite P
    rw [avgMap_apply]
    exact Subgroup.prod_mem _ fun g _ => hUinv g (hPA g.2) u hu
  have hss : ∀ v : W, s (s v) = v := by
    intro v
    have : (s * s) v = v := by
      rw [← pow_two, hs]; rfl
    exact this
  have hinv := inv_eq_self_of_sq151b hW
  set F := U ⊓ fixV P with hF
  set N : Subgroup W := Subgroup.closure {x | ∃ v ∈ F, s v * v⁻¹ = x} with hN
  have c1 : ∀ f ∈ commSub U A, avgMap P f ∈ N := by
    intro f hf
    refine Subgroup.closure_induction (p := fun f _ => avgMap P f ∈ N) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨x, hx, u, hu, rfl⟩
      obtain ⟨k, hk | hk⟩ := hAgen x hx
      · subst hk
        rw [map_mul, avgMap_smul P (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k) u, map_inv,
          mul_inv_cancel]
        exact N.one_mem
      · subst hk
        have e : (a ^ k * s) u = (a ^ k) (s u) := rfl
        rw [e, map_mul, avgMap_smul P (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k) (s u),
          avgMap_conj151b hs hsa, map_inv]
        exact Subgroup.subset_closure ⟨avgMap P u, ⟨hπU u hu, avgMap_mem_fixV P u⟩, rfl⟩
    · rw [map_one]; exact N.one_mem
    · intro x y _ _ hx hy
      rw [map_mul]; exact N.mul_mem hx hy
    · intro x _ hx
      rw [map_inv]; exact N.inv_mem hx
  have c2 : ∀ f ∈ F, f ∈ N := by
    intro f hf
    have hfU : f ∈ commSub U A := by rw [hcomm]; exact hf.1
    have := c1 f hfU
    rwa [avgMap_of_mem_fixV hPodd hW hf.2] at this
  have c3 : N ≤ fixV (Subgroup.zpowers s) := by
    rw [hN, Subgroup.closure_le]
    rintro _ ⟨v, -, rfl⟩
    show s v * v⁻¹ ∈ fixV (Subgroup.zpowers s)
    rw [mem_fixV_zpowers_iff, map_mul, map_inv, hss v, hinv v, hinv (s v), mul_comm]
  have c4 : N ≤ ⊥ := by
    rw [hN, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : s v = v := mem_fixV_zpowers_iff.mp (c3 (c2 v hv))
    show s v * v⁻¹ ∈ (⊥ : Subgroup W)
    rw [h1, mul_inv_cancel]
    exact Subgroup.one_mem _
  exact eq_bot_iff.mpr fun f hf => c4 (c2 f hf)


section Counting

omit [CommGroup W] [Finite W] in
theorem isPGroup_zpowers_of_pow_eq_one151b {Γ : Type*} [Group Γ] [Finite Γ] {a : Γ} {q : ℕ} [Fact q.Prime]
    (h : a ^ q = 1) : IsPGroup q (Subgroup.zpowers a) := by
  have hd : orderOf a ∣ q := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hd with h1 | h1
  · exact IsPGroup.iff_card.mpr ⟨0, by rw [Nat.card_zpowers, h1]; simp⟩
  · exact IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, h1]; simp⟩

theorem invariant_zpowers151b {a : MulAut W} {U : Subgroup W} (h : ∀ w ∈ U, a w ∈ U) :
    ∀ g ∈ Subgroup.zpowers a, ∀ w ∈ U, g w ∈ U := by
  intro g hg w hw
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff g a).mp
    ((mem_powers_iff_mem_zpowers (x := a) (y := g)).mpr hg)
  have key : ∀ n : ℕ, ∀ w ∈ U, (a ^ n) w ∈ U := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih => intro w hw; rw [pow_succ]; exact ih (a w) (h w hw)
  rw [← hn]
  exact key n w hw

omit [CommGroup W] [Finite W] in
theorem mem_zpowers_of_sq151b {Γ : Type*} [Group Γ] {u g : Γ} (hu : u ^ 2 = 1)
    (hg : g ∈ Subgroup.zpowers u) : g = 1 ∨ g = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hu
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.mul_ediv_add_emod k 2, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem commSub_le_fixV_of_sq151b (hW : ∀ w : W, w ^ 2 = 1) {u : MulAut W} (hu : u ^ 2 = 1)
    {U : Subgroup W} (hUu : ∀ w ∈ U, u w ∈ U) :
    commSub U (Subgroup.zpowers u) ≤ U ⊓ fixV (Subgroup.zpowers u) := by
  have hinv := inv_eq_self_of_sq151b hW
  have huu : ∀ v : W, u (u v) = v := by
    intro v
    have : (u * u) v = v := by rw [← pow_two, hu]; rfl
    exact this
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  have hxU : x w ∈ U := invariant_zpowers151b hUu x hx w hw
  refine ⟨U.mul_mem hxU (U.inv_mem hw), mem_fixV_zpowers_iff.mpr ?_⟩
  rcases mem_zpowers_of_sq151b hu hx with rfl | rfl
  · simp
  · rw [map_mul, map_inv, huu, hinv w, hinv (x w), mul_comm]


theorem rk_eq_four_of_card_sixteen151b (hW : ∀ w : W, w ^ 2 = 1) {U : Subgroup W}
    (hU16 : Nat.card U = 16) : rk U = 4 := by
  have h1 := card_eq_two_pow hW U
  rw [hU16] at h1
  have : (2 : ℕ) ^ 4 = 2 ^ rk U := by rw [← h1]; norm_num
  exact (Nat.pow_right_injective (le_refl 2) this).symm

theorem fixV_of_commute_involution151b (hW : ∀ w : W, w ^ 2 = 1) {U : Subgroup W}
    (hU16 : Nat.card U = 16) {a u : MulAut W} (ha5 : a ^ 5 = 1)
    (hfree : U ⊓ fixV (Subgroup.zpowers a) = ⊥) (hu2 : u ^ 2 = 1) (hau : a * u = u * a)
    (hUa : ∀ w ∈ U, a w ∈ U) (hUu : ∀ w ∈ U, u w ∈ U) :
    U ≤ fixV (Subgroup.zpowers u) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set F' := U ⊓ fixV (Subgroup.zpowers u) with hF'
  have hF'a : ∀ w ∈ F', a w ∈ F' := by
    intro w hw
    refine ⟨hUa w hw.1, mem_fixV_zpowers_iff.mpr ?_⟩
    have hwu : u w = w := mem_fixV_zpowers_iff.mp hw.2
    calc u (a w) = (u * a) w := rfl
      _ = (a * u) w := by rw [hau]
      _ = a (u w) := rfl
      _ = a w := by rw [hwu]
  have hmod := card_modEq_card_inf_fixV151b (U := F') (isPGroup_zpowers_of_pow_eq_one151b ha5)
    (invariant_zpowers151b hF'a)
  have hcard1 : Nat.card ↥(F' ⊓ fixV (Subgroup.zpowers a)) = 1 := by
    apply Subgroup.card_eq_one.mpr
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ U ⊓ fixV (Subgroup.zpowers a) := ⟨hx.1.1, hx.2⟩
    rw [hfree] at this
    exact this
  rw [hcard1] at hmod
  have hrkU : rk U = 4 := rk_eq_four_of_card_sixteen151b hW hU16
  have hcs : rk (commSub U (Subgroup.zpowers u)) + rk F' = rk U :=
    rk_commSub_add_rk_inf_fixV (g := u) (W := U) (invariant_zpowers151b hUu)
  have hle : rk (commSub U (Subgroup.zpowers u)) ≤ rk F' :=
    rk_mono (commSub_le_fixV_of_sq151b hW hu2 hUu)
  have hF'rk : rk F' ≤ 4 := hrkU ▸ rk_mono inf_le_left
  have hF'rk2 : 2 ≤ rk F' := by omega
  have hcF' : Nat.card F' = 2 ^ rk F' := card_eq_two_pow hW F'
  rw [hcF'] at hmod
  have h4 : rk F' = 4 := by
    generalize rk F' = r at hF'rk hF'rk2 hmod
    interval_cases r <;> simp [Nat.ModEq] at hmod ⊢
  have hFU : F' = U := eq_of_le_of_rk_le hW (inf_le_left : F' ≤ U) (by omega)
  intro w hw
  have : w ∈ F' := by rw [hFU]; exact hw
  exact this.2


theorem fix_of_prime_ge_five151b (hW : ∀ w : W, w ^ 2 = 1) {U : Subgroup W}
    (hU16 : Nat.card U = 16) {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {c : MulAut W}
    (hcq : c ^ q = 1) (hUc : ∀ w ∈ U, c w ∈ U)
    (h5 : q = 5 → ∃ u : MulAut W, u ^ 2 = 1 ∧ c * u = u * c ∧ (∀ w ∈ U, u w ∈ U) ∧
      ¬ U ≤ fixV (Subgroup.zpowers u))
    (h7 : q = 7 → ∃ a : MulAut W, c * a = a * c ∧ (∀ w ∈ U, a w ∈ U) ∧
      U ⊓ fixV (Subgroup.zpowers a) = ⊥) :
    U ≤ fixV (Subgroup.zpowers c) := by
  have hqp : q.Prime := Fact.out
  set F := U ⊓ fixV (Subgroup.zpowers c) with hF
  have hmod := card_modEq_card_inf_fixV151b (U := U) (isPGroup_zpowers_of_pow_eq_one151b hcq)
    (invariant_zpowers151b hUc)
  have hrkU : rk U = 4 := rk_eq_four_of_card_sixteen151b hW hU16
  have hFle : rk F ≤ 4 := hrkU ▸ rk_mono inf_le_left
  have hcF : Nat.card F = 2 ^ rk F := card_eq_two_pow hW F
  rw [hU16, hcF] at hmod
  have hcases : rk F = 0 ∨ rk F = 1 ∨ rk F = 2 ∨ rk F = 3 ∨ rk F = 4 := by omega
  rcases hcases with h | h | h | h | h
  ·
    rw [h] at hmod
    have hdvd : q ∣ 16 - 2 ^ 0 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    have hq : q = 5 := by
      have : q ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases q <;> first | rfl | (exfalso; omega) | (exfalso; norm_num at hqp)
    obtain ⟨u, hu2, hcu, hUu, hnot⟩ := h5 hq
    have hFbot : U ⊓ fixV (Subgroup.zpowers c) = ⊥ :=
      Subgroup.card_eq_one.mp (by rw [hcF, h]; rfl)
    subst hq
    exact absurd (fixV_of_commute_involution151b hW hU16 (a := c) (u := u) hcq hFbot hu2 hcu hUc hUu)
      hnot
  ·
    rw [h] at hmod
    have hdvd : q ∣ 16 - 2 ^ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    have hq : q = 7 := by
      have : q ≤ 14 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases q <;> first | rfl | (exfalso; omega) | (exfalso; norm_num at hqp)
    obtain ⟨a, hca, hUa, hfree⟩ := h7 hq
    have hcard2 : Nat.card F = 2 := by rw [hcF, h]; rfl
    have hFne : F ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hcard2
      omega
    obtain ⟨⟨f, hfF⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hFne
    have hf1' : f ≠ 1 := fun e => hf1 (Subtype.ext e)
    have hafF : a f ∈ F := by
      refine ⟨hUa f hfF.1, mem_fixV_zpowers_iff.mpr ?_⟩
      have hcf : c f = f := mem_fixV_zpowers_iff.mp hfF.2
      calc c (a f) = (c * a) f := rfl
        _ = (a * c) f := by rw [hca]
        _ = a (c f) := rfl
        _ = a f := by rw [hcf]
    have haf1 : a f ≠ 1 := fun e => hf1' (a.injective (by rw [e, map_one]))
    have hfa : a f = f := by
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥F)).mp hcard2
      have h1 : (⟨a f, hafF⟩ : ↥F) = ⟨f, hfF⟩ := by
        have e1 := hy ⟨a f, hafF⟩ (fun e => haf1 (congrArg Subtype.val e))
        have e2 := hy ⟨f, hfF⟩ (fun e => hf1' (congrArg Subtype.val e))
        exact e1.trans e2.symm
      exact congrArg Subtype.val h1
    have : f ∈ U ⊓ fixV (Subgroup.zpowers a) := ⟨hfF.1, mem_fixV_zpowers_iff.mpr hfa⟩
    rw [hfree] at this
    exact absurd (Subgroup.mem_bot.mp this) hf1'
  ·
    exfalso
    rw [h] at hmod
    have hdvd : q ∣ 16 - 2 ^ 2 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    have : q ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases q <;> first | (omega) | (norm_num at hqp)
  ·
    exfalso
    rw [h] at hmod
    have hdvd : q ∣ 16 - 2 ^ 3 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    have : q ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases q <;> first | (omega) | (norm_num at hqp)
  · have hFU : F = U := eq_of_le_of_rk_le hW (inf_le_left : F ≤ U) (by omega)
    intro w hw
    have : w ∈ F := by rw [hFU]; exact hw
    exact this.2

end Counting

end CFSG.Quasithin
