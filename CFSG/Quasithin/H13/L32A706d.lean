module

public import CFSG.Quasithin.H13.L32A511Qb
public import CFSG.Quasithin.H13.L32ATJ1a
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.H13.L32A.M76

open CFSG.Quasithin CFSG.Quasithin.H13.Q511

section Group

variable {M : Type} [Group M]

theorem eq_one_of_pow_cube {e : M} (he5 : e ^ 5 = 1) (he1 : e ≠ 1) {j : ℕ} (hj : j < 5)
    (h : e ^ (j ^ 3) = e) : j = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf e = 5 := orderOf_eq_prime he5 he1
  have h' : e ^ (j ^ 3 % 5) = e := by rw [← hord, pow_mod_orderOf, h]
  interval_cases j
  · simp at h'; exact absurd h'.symm he1
  · rfl
  · norm_num at h'
    have : e ^ 2 = 1 := by
      calc e ^ 2 = e ^ 3 * e⁻¹ := by group
        _ = 1 := by rw [h', mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one this
    rw [hord] at this
    norm_num at this
  · norm_num at h'
    have : e = 1 := by
      calc e = e ^ 2 * e⁻¹ := by group
        _ = 1 := by rw [h', mul_inv_cancel]
    exact absurd this he1
  · norm_num at h'
    have : e ^ 3 = 1 := by
      calc e ^ 3 = e ^ 4 * e⁻¹ := by group
        _ = 1 := by rw [h', mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one this
    rw [hord] at this
    norm_num at this

theorem exists_pow_of_mem_zpowers {x y : M} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hy : y ∈ Subgroup.zpowers x) : ∃ j < 5, x ^ j = y := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hx5⟩
  have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hy)
  rw [Finset.mem_range, hord] at hj
  exact ⟨j, hj, hjy⟩

theorem conj_eq_of_mem_zpowers {l e : M} (hl3 : l ^ 3 = 1) (he5 : e ^ 5 = 1) (he1 : e ≠ 1)
    (hle : l * e * l⁻¹ ∈ Subgroup.zpowers e) : l * e * l⁻¹ = e := by
  obtain ⟨j, hj, hje⟩ := exists_pow_of_mem_zpowers he5 he1 hle
  have hn : ∀ n : ℕ, l ^ n * e * (l ^ n)⁻¹ = e ^ (j ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc l ^ (n + 1) * e * (l ^ (n + 1))⁻¹ = l * (l ^ n * e * (l ^ n)⁻¹) * l⁻¹ := by group
        _ = (l * e * l⁻¹) ^ (j ^ n) := by rw [ih, conj_pow]
        _ = e ^ (j ^ (n + 1)) := by rw [← hje, ← pow_mul, pow_succ, mul_comm]
  have h3 := hn 3
  rw [hl3, one_mul, inv_one, mul_one] at h3
  have hj1 := eq_one_of_pow_cube he5 he1 hj h3.symm
  rw [← hje, hj1, pow_one]

theorem conj_eq_of_normalizes_line [Finite M] {E : Subgroup M}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE5 : ∀ e ∈ E, e ^ 5 = 1) (hEcard : Nat.card E = 25) {l : M} (hl3 : l ^ 3 = 1)
    (hlE : ∀ e ∈ E, l * e * l⁻¹ ∈ E) {e₀ : M} (he₀ : e₀ ∈ E) (he₀1 : e₀ ≠ 1)
    (hle₀ : l * e₀ * l⁻¹ ∈ Subgroup.zpowers e₀) {e : M} (he : e ∈ E) : l * e * l⁻¹ = e := by
  have h0 := conj_eq_of_mem_zpowers hl3 (hE5 e₀ he₀) he₀1 hle₀
  have hfix0 : ∀ c ∈ Subgroup.zpowers e₀, l * c * l⁻¹ = c := fun c hc => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← conj_zpow, h0]
  by_cases heZ : e ∈ Subgroup.zpowers e₀
  · exact hfix0 e heZ
  have he1 : e ≠ 1 := fun h => heZ (h ▸ Subgroup.one_mem _)
  have hE5e := hE5 e he
  have hcomm : ∀ x ∈ Subgroup.zpowers e₀, ∀ y ∈ Subgroup.zpowers e, x * y = y * x := by
    intro x hx y hy
    exact hEc x (Subgroup.zpowers_le.mpr he₀ hx) y (Subgroup.zpowers_le.mpr he hy)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hinf : Subgroup.zpowers e₀ ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨j, hj, hjx⟩ := exists_pow_of_mem_zpowers hE5e he1 hx.2
    have hj0 : j ≠ 0 := fun h => hx1 (by rw [← hjx, h, pow_zero])
    apply heZ
    have hxe : e ∈ Subgroup.zpowers x := by
      rw [← hjx]
      have hcop : Nat.Coprime j (orderOf e) := by
        rw [orderOf_eq_prime hE5e he1]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr fun h =>
          absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) h) (by omega))
      exact A4.mem_zpowers_pow_of_coprime hcop
    exact (Subgroup.zpowers_le.mpr hx.1) hxe
  have hn : Subgroup.zpowers e₀ ≤ Subgroup.normalizer (Subgroup.zpowers e : Set M) :=
    TJ1.le_normalizer_of_commute hcomm
  have hsup : Subgroup.zpowers e₀ ⊔ Subgroup.zpowers e = E := by
    have hle : Subgroup.zpowers e₀ ⊔ Subgroup.zpowers e ≤ E :=
      sup_le (Subgroup.zpowers_le.mpr he₀) (Subgroup.zpowers_le.mpr he)
    have hc := TJ1.card_sup_mul_card_inf hn
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime (hE5 e₀ he₀) he₀1, orderOf_eq_prime hE5e he1] at hc
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hEcard, hc])
  have hleE : l * e * l⁻¹ ∈ Subgroup.zpowers e₀ ⊔ Subgroup.zpowers e := by
    rw [hsup]; exact hlE e he
  obtain ⟨c, hc, y, hy, hcy⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (TJ1.le_normalizer_of_commute
      fun y hy x hx => (hcomm x hx y hy).symm)).mp hleE
  obtain ⟨j, hj, rfl⟩ := exists_pow_of_mem_zpowers hE5e he1 hy
  have hlc : l * c * l⁻¹ = c := hfix0 c hc
  have hce' : Commute c e := hcomm c hc e (Subgroup.mem_zpowers e)
  have hit : ∀ n : ℕ, ∃ m : ℕ, l ^ n * e * (l ^ n)⁻¹ = c ^ m * e ^ (j ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨m + j ^ n, ?_⟩
      calc l ^ (n + 1) * e * (l ^ (n + 1))⁻¹ = l * (l ^ n * e * (l ^ n)⁻¹) * l⁻¹ := by group
        _ = (l * c * l⁻¹) ^ m * (l * e * l⁻¹) ^ (j ^ n) := by
          rw [hm, conj_pow, conj_pow]; group
        _ = c ^ m * (c * e ^ j) ^ (j ^ n) := by rw [hlc, hcy]
        _ = c ^ m * (c ^ (j ^ n) * e ^ (j * j ^ n)) := by
          rw [(hce'.pow_right j).mul_pow, ← pow_mul]
        _ = c ^ (m + j ^ n) * e ^ (j ^ (n + 1)) := by
          rw [← mul_assoc, ← pow_add, pow_succ, mul_comm (j ^ n) j]
  obtain ⟨m, hm⟩ := hit 3
  rw [hl3, one_mul, inv_one, mul_one] at hm
  have hcm : c ^ m ∈ Subgroup.zpowers e₀ ⊓ Subgroup.zpowers e := by
    refine ⟨Subgroup.pow_mem _ hc m, ?_⟩
    rw [eq_mul_inv_of_mul_eq hm.symm]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers e)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers e) _))
  rw [hinf, Subgroup.mem_bot] at hcm
  rw [hcm, one_mul] at hm
  have hj1 := eq_one_of_pow_cube hE5e he1 hj hm.symm
  subst hj1
  rw [pow_one] at hcy
  have hit' : ∀ n : ℕ, l ^ n * e * (l ^ n)⁻¹ = c ^ n * e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc l ^ (n + 1) * e * (l ^ (n + 1))⁻¹ = l * (l ^ n * e * (l ^ n)⁻¹) * l⁻¹ := by group
        _ = (l * c * l⁻¹) ^ n * (l * e * l⁻¹) := by rw [ih, conj_pow]; group
        _ = c ^ (n + 1) * e := by rw [hlc, hcy, ← mul_assoc, ← pow_succ]
  have h3 := hit' 3
  rw [hl3, one_mul, inv_one, mul_one] at h3
  have hc3 : c ^ 3 = 1 := by
    have := congrArg (· * e⁻¹) h3
    simpa using this.symm
  have hc5 : c ^ 5 = 1 := hE5 c (Subgroup.zpowers_le.mpr he₀ hc)
  have hc1 : c = 1 := by
    calc c = (c ^ 5) ^ 2 * ((c ^ 3) ^ 3)⁻¹ := by group
      _ = 1 := by rw [hc5, hc3]; group
  rw [hcy, hc1, one_mul]

end Group

section Module

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem map_commHom_invariant {U : Subgroup W} {g h : MulAut W} (hgh : g * h = h * g)
    (hU : ∀ u ∈ U, h u ∈ U) : ∀ w ∈ U.map (commHom g), h w ∈ U.map (commHom g) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨h u, hU u hu, ?_⟩
  rw [commHom_apply, commHom_apply, map_mul, map_inv]
  have := congrArg (fun φ : MulAut W => φ u) hgh
  simp only [MulAut.mul_apply] at this
  rw [this]

theorem false_of_inverted_three (hV : ∀ w : W, w ^ 2 = 1) {u l y : MulAut W} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hu2 : u ^ 2 = 1) (hl3 : l ^ 3 = 1) (hinv : u * l * u⁻¹ = l⁻¹)
    (hlfix : fixV (Subgroup.zpowers l) = ⊥)
    (hrk : rk ((⊤ : Subgroup W).map (commHom u)) ≤ 2) (hyp : y ^ p = 1) (hy1 : y ≠ 1)
    (hyl : y * l = l * y) (hyu : y * u = u * y) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hlfix' : (⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers l) = ⊥ := by rw [hlfix, inf_bot_eq]
  have h1 := Q511.rk_eq_two_mul_of_inverts hV (hT l) (hT u) hlfix' hu2 hinv
  have h2 := Q511.rk_map_add_rk_inf (⊤ : Subgroup W) u
  set W' := (⊤ : Subgroup W).map (commHom y) with hW'
  have hW'y : ∀ w ∈ W', y w ∈ W' := map_commHom_invariant rfl (hT y)
  have hW'l : ∀ w ∈ W', l w ∈ W' := map_commHom_invariant hyl (hT l)
  have hW'fix : W' ⊓ fixV (Subgroup.zpowers y) = ⊥ :=
    Q511.map_commHom_inf_fix_eq_bot hV (hp.odd_of_ne_two (by omega)) hyp ⊤
  have hW'lfix : W' ⊓ fixV (Subgroup.zpowers l) = ⊥ := by rw [hlfix, inf_bot_eq]
  have hd5 := Q511.dvd_two_pow_rk_sub_one hV hW'y hyp hW'fix
  have hd3 := Q511.dvd_two_pow_rk_sub_one hV hW'l hl3 hW'lfix
  have hW'le : rk W' ≤ rk (⊤ : Subgroup W) := rk_mono le_top
  have hW'ne : W' ≠ ⊥ := Q511.map_commHom_ne_bot hy1
  have hpos : rk W' ≠ 0 := fun h => hW'ne ((rk_eq_zero_iff hV).mp h)
  have hk4 : rk W' = 4 := by
    generalize hk : rk W' = k at *
    have hle4 : k ≤ 4 := by omega
    interval_cases k
    · omega
    · norm_num at hd3
    · have := Nat.le_of_dvd (by norm_num) hd5; omega
    · norm_num at hd3
    · rfl
  have hW'top : W' = ⊤ := eq_of_le_of_rk_le hV le_top (by omega)
  set C := (⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers u) with hC
  have hCy : ∀ w ∈ C, y w ∈ C := fun w hw => by
    obtain ⟨-, hwu⟩ := Q511.mem_inf_fix.mp hw
    refine Q511.mem_inf_fix.mpr ⟨Subgroup.mem_top _, ?_⟩
    have := congrArg (fun φ : MulAut W => φ w) hyu.symm
    simp only [MulAut.mul_apply] at this
    rw [this, hwu]
  have hCfix : C ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ W' ⊓ fixV (Subgroup.zpowers y) :=
      ⟨by rw [hW'top]; exact Subgroup.mem_top w, hw.2⟩
    rw [hW'fix] at this
    exact this
  have hdC := Q511.dvd_two_pow_rk_sub_one hV hCy hyp hCfix
  have hrkC : rk C = 2 := by omega
  rw [hrkC] at hdC
  have := Nat.le_of_dvd (by norm_num) hdC
  omega

theorem exists_pow_mul_fix (hV : ∀ w : W, w ^ 2 = 1) {d e : MulAut W} (hd5 : d ^ 5 = 1)
    (he5 : e ^ 5 = 1) (hde : d * e = e * d) (hrk : rk ((⊤ : Subgroup W).map (commHom d)) = 4) :
    ∃ i < 5, ∀ w ∈ (⊤ : Subgroup W).map (commHom d), (e * d ^ i) w = w := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set U := (⊤ : Subgroup W).map (commHom d) with hU
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hUd : ∀ u ∈ U, d u ∈ U := map_commHom_invariant rfl (hT d)
  have hUe : ∀ u ∈ U, e u ∈ U := map_commHom_invariant hde (hT e)
  have hfix : U ⊓ fixV (Subgroup.zpowers d) = ⊥ :=
    Q511.map_commHom_inf_fix_eq_bot hV (by decide) hd5 ⊤
  have hgen := fun u (hu : u ∈ U) =>
    Q511.mem_iSup_inf_fix hV (by norm_num) (by norm_num) hd5 he5 hde hUd hUe hfix hu
  by_contra hcon
  push Not at hcon
  have hbot : ∀ i ∈ Finset.range 5, U ⊓ fixV (Subgroup.zpowers (e * d ^ i)) = ⊥ := by
    intro i hi
    have hi5 : i < 5 := Finset.mem_range.mp hi
    set S := U ⊓ fixV (Subgroup.zpowers (e * d ^ i)) with hS
    have hcomm : d * (e * d ^ i) = (e * d ^ i) * d := by
      rw [← mul_assoc, hde, mul_assoc, mul_assoc, ← pow_succ', ← pow_succ]
    have hSd : ∀ w ∈ S, d w ∈ S := fun w hw =>
      ⟨hUd w hw.1, Q511.mem_fix_of_comm hcomm hw.2⟩
    have hSfix : S ⊓ fixV (Subgroup.zpowers d) = ⊥ :=
      le_bot_iff.mp (hfix ▸ inf_le_inf_right _ inf_le_left)
    have hdS := Q511.dvd_two_pow_rk_sub_one hV hSd hd5 hSfix
    have hSle : rk S ≤ 4 := hrk ▸ rk_mono inf_le_left
    rcases Q511.rk_of_dvd_five hdS hSle with h | h
    · exact (rk_eq_zero_iff hV).mp h
    · exfalso
      have hSU : S = U := eq_of_le_of_rk_le hV inf_le_left (by omega)
      obtain ⟨w, hw, hne⟩ := hcon i hi5
      apply hne
      have : w ∈ S := hSU ▸ hw
      exact mem_fixV_zpowers_iff.mp this.2
  have hUbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have := hgen u hu
    rw [iSup₂_eq_bot.mpr hbot] at this
    exact this
  rw [hUbot, rk_bot] at hrk
  omega

theorem fix_eq_bot_of_not_fix (hV : ∀ w : W, w ^ 2 = 1) {d e : MulAut W} (hd5 : d ^ 5 = 1)
    (he5 : e ^ 5 = 1) (hde : d * e = e * d) (hrk : rk ((⊤ : Subgroup W).map (commHom d)) = 4)
    (hne : ¬ ∀ w ∈ (⊤ : Subgroup W).map (commHom d), e w = w) :
    (⊤ : Subgroup W).map (commHom d) ⊓ fixV (Subgroup.zpowers e) = ⊥ := by
  set U := (⊤ : Subgroup W).map (commHom d) with hU
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hUd : ∀ u ∈ U, d u ∈ U := map_commHom_invariant rfl (hT d)
  have hfix : U ⊓ fixV (Subgroup.zpowers d) = ⊥ :=
    Q511.map_commHom_inf_fix_eq_bot hV (by decide) hd5 ⊤
  obtain ⟨i, hi, hfi⟩ := exists_pow_mul_fix hV hd5 he5 hde hrk
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hne fun w hw => by simpa using hfi w hw
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwU, hwe⟩ := Q511.mem_inf_fix.mp hw
  have hw'U : (d ^ i)⁻¹ w ∈ U :=
    Q511.zpowers_invariant hUd _
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) i))
      w hwU
  have h1 := hfi _ hw'U
  rw [MulAut.mul_apply, show (d ^ i) ((d ^ i)⁻¹ w) = w by simp, hwe] at h1
  have h2 : (d ^ i) w = w := by
    have := congrArg (d ^ i) h1
    simpa using this
  have h3 : d w = w :=
    Q511.apply_eq_of_pow_apply_eq (by norm_num) hd5 (Nat.pos_of_ne_zero hi0) hi h2
  have : w ∈ U ⊓ fixV (Subgroup.zpowers d) := Q511.mem_inf_fix.mpr ⟨hwU, h3⟩
  rwa [hfix] at this

theorem map_commHom_eq_of_not_fix (hV : ∀ w : W, w ^ 2 = 1) {d e : MulAut W} (hd5 : d ^ 5 = 1)
    (he5 : e ^ 5 = 1) (hde : d * e = e * d) (hrk : rk ((⊤ : Subgroup W).map (commHom d)) = 4)
    (hrke : rk ((⊤ : Subgroup W).map (commHom e)) = 4)
    (hne : ¬ ∀ w ∈ (⊤ : Subgroup W).map (commHom d), e w = w) :
    (⊤ : Subgroup W).map (commHom d) = (⊤ : Subgroup W).map (commHom e) := by
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hUe : ∀ u ∈ (⊤ : Subgroup W).map (commHom d), e u ∈ (⊤ : Subgroup W).map (commHom d) :=
    map_commHom_invariant hde (hT e)
  have hfix := fix_eq_bot_of_not_fix hV hd5 he5 hde hrk hne
  have h1 := Q511.map_commHom_eq_of_fix_eq_bot hV hUe hfix
  have hle : (⊤ : Subgroup W).map (commHom d) ≤ (⊤ : Subgroup W).map (commHom e) := by
    rw [← h1]
    exact Subgroup.map_mono le_top
  exact eq_of_le_of_rk_le hV hle (by omega)

theorem commute_of_rank_four (hV : ∀ w : W, w ^ 2 = 1) {E : Subgroup (MulAut W)}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE5 : ∀ e ∈ E, e ^ 5 = 1)
    (hEcard : Nat.card E = 25) {l : MulAut W} (hl3 : l ^ 3 = 1)
    (hlE : ∀ e ∈ E, l * e * l⁻¹ ∈ E) {d : MulAut W} (hdE : d ∈ E) (hd1 : d ≠ 1)
    (hrk : rk ((⊤ : Subgroup W).map (commHom d)) = 4) {e : MulAut W} (he : e ∈ E) :
    l * e * l⁻¹ = e := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set U := (⊤ : Subgroup W).map (commHom d) with hU
  have hd5 := hE5 d hdE
  have hdord : orderOf d = 5 := orderOf_eq_prime hd5 hd1
  obtain ⟨e₁, he₁, he₁d⟩ : ∃ e₁ ∈ E, e₁ ∉ Subgroup.zpowers d := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers d from h)
    rw [hEcard, Nat.card_zpowers, hdord] at this
    omega
  obtain ⟨i, -, hfi⟩ := exists_pow_mul_fix hV hd5 (hE5 e₁ he₁) (hEc d hdE e₁ he₁) hrk
  set f := e₁ * d ^ i with hfdef
  have hfE : f ∈ E := E.mul_mem he₁ (E.pow_mem hdE i)
  have hfd : f ∉ Subgroup.zpowers d := fun h => he₁d (by
    have := Subgroup.mul_mem _ h
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) i))
    simpa [hfdef] using this)
  have hf1 : f ≠ 1 := fun h => hfd (h ▸ Subgroup.one_mem _)
  set K := E ⊓ centSub U with hK
  have hfK : f ∈ K := ⟨hfE, mem_centSub.mpr hfi⟩
  have hdK : d ∉ K := by
    intro h
    have hfix : U ⊓ fixV (Subgroup.zpowers d) = ⊥ :=
      Q511.map_commHom_inf_fix_eq_bot hV (by decide) hd5 ⊤
    have hUne : U ≠ ⊥ := fun hb => by rw [hb, rk_bot] at hrk; omega
    apply hUne
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ U ⊓ fixV (Subgroup.zpowers d) :=
      Q511.mem_inf_fix.mpr ⟨hw, mem_centSub.mp h.2 w hw⟩
    rwa [hfix] at this
  have hKline : ∀ g ∈ K, g ∈ Subgroup.zpowers f := by
    have hKE : K ≤ E := inf_le_left
    have hdvd : Nat.card K ∣ 25 := hEcard ▸ Subgroup.card_dvd_of_le hKE
    have hKne : Nat.card K ≠ 25 := fun h => hdK (by
      have : K = E := Subgroup.eq_of_le_of_card_ge hKE (by rw [h, hEcard])
      rw [this]; exact hdE)
    have hK5 : Nat.card K ≤ 5 := by
      have : Nat.card K ∈ Nat.divisors 25 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have h25 : Nat.divisors 25 = {1, 5, 25} := by decide
      rw [h25] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    have hfle : Subgroup.zpowers f ≤ K := Subgroup.zpowers_le.mpr hfK
    have hzf : Nat.card (Subgroup.zpowers f) = 5 := by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime (hE5 f hfE) hf1
    have : Subgroup.zpowers f = K := Subgroup.eq_of_le_of_card_ge hfle (by omega)
    intro g hg
    rw [this]
    exact hg
  have hlEk : ∀ k : ℕ, ∀ e ∈ E, l ^ k * e * (l ^ k)⁻¹ ∈ E := by
    intro k
    induction k with
    | zero => intro e he; simpa using he
    | succ k ih =>
      intro e he
      rw [show l ^ (k + 1) * e * (l ^ (k + 1))⁻¹ = l * (l ^ k * e * (l ^ k)⁻¹) * l⁻¹ by group]
      exact hlE _ (ih e he)
  have hkey : ∀ k : ℕ, U.map ((l ^ k : MulAut W) : W →* W) = U →
      l ^ k * f * (l ^ k)⁻¹ ∈ Subgroup.zpowers f := by
    intro k hk
    refine hKline _ ⟨hlEk k f hfE, mem_centSub.mpr fun w hw => ?_⟩
    rw [← hk] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    change (l ^ k * f * (l ^ k)⁻¹) ((l ^ k) v) = (l ^ k) v
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfi v hv]
  have hl4 : l = l ^ 2 * l ^ 2 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hl3, one_mul]
  set d₁ := l * d * l⁻¹ with hd₁
  have hd₁E : d₁ ∈ E := hlE d hdE
  have hd₁U : (⊤ : Subgroup W).map (commHom d₁) = U.map (l : W →* W) :=
    (Q511.map_map_commHom l d).symm
  have hrk₁ : rk ((⊤ : Subgroup W).map (commHom d₁)) = 4 := by
    rw [hd₁U, Q511.rk_map_aut, hrk]
  by_cases h1 : ∀ w ∈ U, d₁ w = w
  · have hd₁K : d₁ ∈ Subgroup.zpowers f := hKline d₁ ⟨hd₁E, mem_centSub.mpr h1⟩
    set d₂ := l * d₁ * l⁻¹ with hd₂
    have hd₂E : d₂ ∈ E := hlE d₁ hd₁E
    have e2 : d₂ = l ^ 2 * d * (l ^ 2)⁻¹ := by rw [hd₂, hd₁, pow_two]; group
    have hd₂U : (⊤ : Subgroup W).map (commHom d₂) = U.map ((l ^ 2 : MulAut W) : W →* W) := by
      rw [Q511.map_map_commHom (l ^ 2) d, ← e2]
    have hrk₂ : rk ((⊤ : Subgroup W).map (commHom d₂)) = 4 := by
      rw [hd₂U, Q511.rk_map_aut, hrk]
    have hd₁1 : d₁ ≠ 1 := fun h => hd1 (by
      have := congrArg (fun x => l⁻¹ * x * l) h
      simpa [hd₁, mul_assoc] using this)
    by_cases h2 : ∀ w ∈ U, d₂ w = w
    · have hd₂K : d₂ ∈ Subgroup.zpowers f := hKline d₂ ⟨hd₂E, mem_centSub.mpr h2⟩
      have hzd : Subgroup.zpowers d₁ = Subgroup.zpowers f := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd₁K) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hE5 f hfE) hf1,
          orderOf_eq_prime (hE5 d₁ hd₁E) hd₁1]
      exact conj_eq_of_normalizes_line hEc hE5 hEcard hl3 hlE hd₁E hd₁1 (hzd ▸ hd₂K) he
    · have hU2 := map_commHom_eq_of_not_fix hV hd5 (hE5 d₂ hd₂E) (hEc d hdE d₂ hd₂E) hrk hrk₂ h2
      have hl2f := hkey 2 (by rw [← hd₂U, ← hU2])
      have hlf : l * f * l⁻¹ ∈ Subgroup.zpowers f := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hl2f
        rw [hl4, show l ^ 2 * l ^ 2 * f * (l ^ 2 * l ^ 2)⁻¹ =
          l ^ 2 * (l ^ 2 * f * (l ^ 2)⁻¹) * (l ^ 2)⁻¹ by group, ← hk, ← conj_zpow]
        exact Subgroup.zpow_mem _ hl2f k
      exact conj_eq_of_normalizes_line hEc hE5 hEcard hl3 hlE hfE hf1 hlf he
  · have hU1 := map_commHom_eq_of_not_fix hV hd5 (hE5 d₁ hd₁E) (hEc d hdE d₁ hd₁E) hrk hrk₁ h1
    have hlf := hkey 1 (by rw [pow_one, ← hd₁U, ← hU1])
    rw [pow_one] at hlf
    exact conj_eq_of_normalizes_line hEc hE5 hEcard hl3 hlE hfE hf1 hlf he

theorem map_commHom_pow_eq {d : MulAut W} (hd5 : d ^ 5 = 1) (hd1 : d ≠ 1) {j : ℕ} (hj0 : j ≠ 0)
    (hj : j < 5) :
    (⊤ : Subgroup W).map (commHom (d ^ j)) = (⊤ : Subgroup W).map (commHom d) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [← commV_zpowers_eq_map, ← commV_zpowers_eq_map]
  congr 1
  apply le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j))
  rw [Subgroup.zpowers_le]
  have hcop : Nat.Coprime j (orderOf d) := by
    rw [orderOf_eq_prime hd5 hd1]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr fun h =>
      absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) h) (by omega))
  exact A4.mem_zpowers_pow_of_coprime hcop

theorem conj_eq_on_of_rank_four (hV : ∀ w : W, w ^ 2 = 1) {d l s : MulAut W} (hd5 : d ^ 5 = 1)
    (hd1 : d ≠ 1) (hl3 : l ^ 3 = 1) (hdl : d * l = l * d)
    (hrk : rk ((⊤ : Subgroup W).map (commHom d)) = 4)
    (hlfix : (⊤ : Subgroup W).map (commHom d) ⊓ fixV (Subgroup.zpowers l) = ⊥)
    (hs2 : s ^ 2 = 1) (hsd : s * d * s⁻¹ ∈ Subgroup.zpowers d)
    (hsl : s * l * s⁻¹ = l ∨ s * l * s⁻¹ = l⁻¹) :
    ∀ w ∈ (⊤ : Subgroup W).map (commHom d), (s * l * s⁻¹) w = l w := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases hsl with h | h
  · intro w _; rw [h]
  set U := (⊤ : Subgroup W).map (commHom d) with hU
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hUd : ∀ u ∈ U, d u ∈ U := map_commHom_invariant rfl (hT d)
  have hUl : ∀ u ∈ U, l u ∈ U := map_commHom_invariant hdl (hT l)
  have hdfix : U ⊓ fixV (Subgroup.zpowers d) = ⊥ :=
    Q511.map_commHom_inf_fix_eq_bot hV (by decide) hd5 ⊤
  obtain ⟨j, hj, hjd⟩ := exists_pow_of_mem_zpowers hd5 hd1 hsd
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hd1
    have := congrArg (fun x => s⁻¹ * x * s) hjd
    simpa [mul_assoc] using this.symm
  have hUs : ∀ u ∈ U, s u ∈ U := by
    intro u hu
    have h1 : s u ∈ U.map (s : W →* W) := ⟨u, hu, rfl⟩
    rwa [Q511.map_map_commHom, ← hjd, map_commHom_pow_eq hd5 hd1 hj0 hj] at h1
  have hjj : d ^ (j * j) = d := by
    have e1 : d = s * (s * d * s⁻¹) * s⁻¹ := by
      rw [show s * (s * d * s⁻¹) * s⁻¹ = (s * s) * d * (s * s)⁻¹ by group, ← pow_two, hs2]
      group
    calc d ^ (j * j) = (d ^ j) ^ j := by rw [pow_mul]
      _ = (s * d * s⁻¹) ^ j := by rw [hjd]
      _ = s * d ^ j * s⁻¹ := by rw [conj_pow]
      _ = s * (s * d * s⁻¹) * s⁻¹ := by rw [hjd]
      _ = d := e1.symm
  have hord : orderOf d = 5 := orderOf_eq_prime hd5 hd1
  have hfour : d ^ 4 ≠ d := fun h4 => by
    have h3 : d ^ 3 = 1 := by
      calc d ^ 3 = d ^ 4 * d⁻¹ := by group
        _ = 1 := by rw [h4, mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at this
    norm_num at this
  have hj14 : j = 1 ∨ j = 4 := by
    have h' : d ^ (j * j % 5) = d := by rw [← hord, pow_mod_orderOf, hjj]
    interval_cases j
    · exact absurd rfl hj0
    · left; rfl
    · norm_num at h'; exact absurd h' hfour
    · norm_num at h'; exact absurd h' hfour
    · right; rfl
  rcases hj14 with rfl | rfl
  ·
    rw [pow_one] at hjd
    have hsdc : d * s = s * d := by
      calc d * s = (s * d * s⁻¹) * s := by rw [← hjd]
        _ = s * d := by group
    have hle := rk_mono (Q511.map_commHom_le_inf_fix hV hUs hs2)
    have hrn := Q511.rk_map_add_rk_inf U s
    set C := U ⊓ fixV (Subgroup.zpowers s) with hC
    have hCd : ∀ w ∈ C, d w ∈ C := fun w hw => ⟨hUd w hw.1, Q511.mem_fix_of_comm hsdc hw.2⟩
    have hCfix : C ⊓ fixV (Subgroup.zpowers d) = ⊥ :=
      le_bot_iff.mp (hdfix ▸ inf_le_inf_right _ inf_le_left)
    have hdC := Q511.dvd_two_pow_rk_sub_one hV hCd hd5 hCfix
    have hCle : rk C ≤ 4 := hrk ▸ rk_mono inf_le_left
    have hC4 : rk C = 4 := by
      rcases Q511.rk_of_dvd_five hdC hCle with h0 | h4
      · omega
      · exact h4
    have hCU : C = U := eq_of_le_of_rk_le hV inf_le_left (by omega)
    have hsw : ∀ v ∈ U, s v = v := fun v hv => by
      have : v ∈ C := hCU ▸ hv
      exact (Q511.mem_inf_fix.mp this).2
    intro w hw
    have hsinv : s⁻¹ w = w := by
      calc s⁻¹ w = s⁻¹ (s w) := by rw [hsw w hw]
        _ = w := by simp
    rw [MulAut.mul_apply, MulAut.mul_apply, hsinv, hsw _ (hUl w hw)]
  ·
    exfalso
    have hsd' : s * d * s⁻¹ = d⁻¹ := by
      rw [← hjd]
      calc d ^ 4 = d ^ 5 * d⁻¹ := by group
        _ = d⁻¹ := by rw [hd5, one_mul]
    have hD := Q511.rk_eq_two_mul_of_inverts hV hUd hUs hdfix hs2 hsd'
    set C := U ⊓ fixV (Subgroup.zpowers s) with hC
    have hrkC : rk C = 2 := by omega
    obtain ⟨c, hc⟩ : ∃ c, c = d * l := ⟨_, rfl⟩
    have hsc : s * c * s⁻¹ = c⁻¹ := by
      calc s * c * s⁻¹ = (s * d * s⁻¹) * (s * l * s⁻¹) := by rw [hc]; group
        _ = d⁻¹ * l⁻¹ := by rw [hsd', h]
        _ = c⁻¹ := by rw [hc, ← mul_inv_rev, hdl]
    have hl1 : l ≠ 1 := by
      intro hl
      have hU0 : U = ⊥ := by
        rw [← hlfix, hl]
        refine le_antisymm (le_inf le_rfl fun w _ => mem_fixV.mpr fun x hx => ?_) inf_le_left
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        simp
      rw [hU0, rk_bot] at hrk
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hlord : orderOf l = 3 := orderOf_eq_prime hl3 hl1
    have hlfix' : ∀ w ∈ U, l w = w → w = 1 := fun w hw hlw => by
      have : w ∈ U ⊓ fixV (Subgroup.zpowers l) := Q511.mem_inf_fix.mpr ⟨hw, hlw⟩
      rw [hlfix] at this
      exact this
    have hdfix' : ∀ w ∈ U, d w = w → w = 1 := fun w hw hdw => by
      have : w ∈ U ⊓ fixV (Subgroup.zpowers d) := Q511.mem_inf_fix.mpr ⟨hw, hdw⟩
      rw [hdfix] at this
      exact this
    have hcn : ∀ n : ℕ, c ^ n = d ^ n * l ^ n := fun n => by
      rw [hc]; exact (show Commute d l from hdl).mul_pow n
    have hreg : ∀ n : ℕ, ∀ w ∈ U, w ≠ 1 → (c ^ n) w = w → 15 ∣ n := by
      intro n w hw hw1 hcw
      have h5 : 5 ∣ n := by
        by_contra h5
        have h1 : (c ^ n) ^ 3 = d ^ (n * 3) := by
          rw [hcn, (Commute.pow_pow (show Commute d l from hdl) n n).mul_pow, ← pow_mul,
            ← pow_mul, mul_comm n 3, pow_mul l 3 n, hl3, one_pow, mul_one, mul_comm 3 n]
        have h2 : (d ^ (n * 3 % 5)) w = w := by
          rw [← hord, pow_mod_orderOf, ← h1]
          exact Q511.pow_apply_eq_self hcw 3
        have hk0 : 0 < n * 3 % 5 := by omega
        have hk5 : n * 3 % 5 < 5 := Nat.mod_lt _ (by norm_num)
        exact hw1 (hdfix' w hw (Q511.apply_eq_of_pow_apply_eq (by norm_num) hd5 hk0 hk5 h2))
      have h3 : 3 ∣ n := by
        by_contra h3
        have h1 : (c ^ n) ^ 5 = l ^ (n * 5) := by
          rw [hcn, (Commute.pow_pow (show Commute d l from hdl) n n).mul_pow, ← pow_mul,
            ← pow_mul, mul_comm n 5, pow_mul d 5 n, hd5, one_pow, one_mul, mul_comm 5 n]
        have h2 : (l ^ (n * 5 % 3)) w = w := by
          rw [← hlord, pow_mod_orderOf, ← h1]
          exact Q511.pow_apply_eq_self hcw 5
        have hk0 : 0 < n * 5 % 3 := by omega
        have hk3 : n * 5 % 3 < 3 := Nat.mod_lt _ (by norm_num)
        exact hw1 (hlfix' w hw (Q511.apply_eq_of_pow_apply_eq Nat.prime_three hl3 hk0 hk3 h2))
      omega
    have hUc : ∀ n : ℕ, ∀ u ∈ U, (c ^ n) u ∈ U := by
      intro n
      induction n with
      | zero => intro u hu; simpa using hu
      | succ n ih =>
        intro u hu
        have hv := ih u hu
        rw [pow_succ', MulAut.mul_apply]
        generalize (c ^ n) u = v at hv ⊢
        rw [hc, MulAut.mul_apply]
        exact hUd _ (hUl _ hv)
    have hCcard : Nat.card C = 4 := by rw [card_eq_two_pow hV C, hrkC]; norm_num
    have := Fintype.ofFinite ↥C
    have hcardC : 1 < ((Finset.univ : Finset ↥C).erase 1).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hCcard]
      norm_num
    obtain ⟨g₁, hg₁, g₂, hg₂, hg₁₂⟩ := Finset.one_lt_card.mp hcardC
    set f₁ : W := (g₁ : W) with hf₁
    set f₂ : W := (g₂ : W) with hf₂
    have hf₁C : f₁ ∈ C := g₁.2
    have hf₂C : f₂ ∈ C := g₂.2
    have hf₁1 : f₁ ≠ 1 := fun h => (Finset.mem_erase.mp hg₁).1 (Subtype.ext h)
    have hf₂1 : f₂ ≠ 1 := fun h => (Finset.mem_erase.mp hg₂).1 (Subtype.ext h)
    have hf₁₂ : f₁ ≠ f₂ := fun h => hg₁₂ (Subtype.ext h)
    have := Fintype.ofFinite W
    set Ufin : Finset W := (Finset.univ.filter (· ∈ U)).erase 1 with hUfin
    have hUfincard : Ufin.card = 15 := by
      have h16 : (Finset.univ.filter (· ∈ U)).card = 16 := by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, card_eq_two_pow hV U, hrk]
        norm_num
      rw [hUfin, Finset.card_erase_of_mem (by simp [U.one_mem]), h16]
    set S : Finset W := (Finset.range 15).image (fun m => (c ^ m) f₁) with hS
    have hSsub : S ⊆ Ufin := by
      intro x hx
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hx
      rw [hUfin, Finset.mem_erase, Finset.mem_filter]
      refine ⟨fun h1 => hf₁1 ?_, Finset.mem_univ _, hUc m f₁ hf₁C.1⟩
      have := congrArg ((c ^ m)⁻¹ : MulAut W) h1
      simpa using this
    have hstep : ∀ a b : ℕ, a ≤ b → b < 15 → (c ^ a) f₁ = (c ^ b) f₁ → a = b := by
      intro a b hab hb h
      have e : c ^ b = c ^ a * c ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab]
      rw [e, MulAut.mul_apply] at h
      have h' : (c ^ (b - a)) f₁ = f₁ := ((c ^ a).injective h).symm
      have := hreg (b - a) f₁ hf₁C.1 hf₁1 h'
      omega
    have hSinj : Set.InjOn (fun m => (c ^ m) f₁) (Finset.range 15 : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      simp only at hab
      rcases le_total a b with h' | h'
      · exact hstep a b h' hb hab
      · exact (hstep b a h' ha hab.symm).symm
    have hScard : S.card = 15 := by
      rw [hS, Finset.card_image_of_injOn hSinj, Finset.card_range]
    have hSU : S = Ufin := Finset.eq_of_subset_of_card_le hSsub (by rw [hUfincard, hScard])
    have hf₂S : f₂ ∈ S := by
      rw [hSU, hUfin, Finset.mem_erase, Finset.mem_filter]
      exact ⟨hf₂1, Finset.mem_univ _, hf₂C.1⟩
    obtain ⟨m, hm, hmf⟩ := Finset.mem_image.mp hf₂S
    rw [Finset.mem_range] at hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hf₁₂ (by simpa using hmf)
    have hsf₁ : s f₁ = f₁ := (Q511.mem_inf_fix.mp hf₁C).2
    have hsf₂ : s f₂ = f₂ := (Q511.mem_inf_fix.mp hf₂C).2
    have hscm : s * c ^ m * s⁻¹ = (c ^ m)⁻¹ := by rw [← conj_pow, hsc, inv_pow]
    have h1 : ((c ^ m)⁻¹ : MulAut W) f₁ = (c ^ m) f₁ := by
      have e : s ((c ^ m) f₁) = (s * c ^ m * s⁻¹) (s f₁) := by
        simp [MulAut.mul_apply]
      rw [hscm, hsf₁, hmf, hsf₂] at e
      rw [← hmf] at e
      exact e.symm
    have h2 : (c ^ (m + m)) f₁ = f₁ := by
      rw [pow_add, MulAut.mul_apply, ← h1]
      simp
    have := hreg (m + m) f₁ hf₁C.1 hf₁1 h2
    omega

end Module

end CFSG.Quasithin.H13.L32A.M76
