module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.B1Offender

public section

namespace CFSG.Quasithin.B19

open CFSG.Quasithin

section Group

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {t a : G} (ht : t * t = 1) (ha : a ∈ Subgroup.zpowers t) :
    a = 1 ∨ a = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [hm, ← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem eq_of_mem_zpowers_three {x a : G} (hx : x ^ 3 = 1) (ha : a ∈ Subgroup.zpowers x) :
    a = 1 ∨ a = x ∨ a = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  rw [zpow_eq_zpow_emod k h3]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk
  · left
    rw [hk, zpow_zero]
  · right; left
    rw [hk, zpow_one]
  · right; right
    rw [hk, eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, h3]

theorem card_zpowers_eq_three {x : G} (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hx hx1

theorem sq_pow_half {x : G} {n : ℕ} (hn : Odd n) (hx : x ^ n = 1) :
    (x ^ ((n + 1) / 2)) ^ 2 = x := by
  obtain ⟨k, rfl⟩ := hn
  have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h, ← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, pow_succ, hx, one_mul]

theorem eq_one_of_sq_of_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {y : G} (hy : y ∈ N)
    (hy2 : y * y = 1) : y = 1 := by
  have h1 : (⟨y, hy⟩ : ↥N) ^ Nat.card N = 1 := pow_card_eq_one'
  have h2 : (⟨y, hy⟩ : ↥N) ^ 2 = 1 := Subtype.ext (by simp [pow_two, hy2])
  obtain ⟨k, hk⟩ := hN
  have h3 : (⟨y, hy⟩ : ↥N) = 1 := by
    have : (⟨y, hy⟩ : ↥N) ^ (2 * k + 1) = 1 := hk ▸ h1
    rw [pow_succ, pow_mul, h2, one_pow, one_mul] at this
    exact this
  exact congrArg Subtype.val h3

theorem eq_one_of_isPGroup_of_odd {Q N : Subgroup G} (hQ : IsPGroup 2 Q) (hN : Odd (Nat.card N))
    {y : G} (hyQ : y ∈ Q) (hyN : y ∈ N) : y = 1 := by
  obtain ⟨n, hn⟩ := hQ ⟨y, hyQ⟩
  have h1 : y ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have h2 : y ^ Nat.card N = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' : (⟨y, hyN⟩ : ↥N) ^ Nat.card N = 1)
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hN)
  have h3 : y ^ Nat.gcd (2 ^ n) (Nat.card N) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

@[expose] def cosetSub (N : Subgroup G) {t : G} (ht : t * t = 1)
    (hN : ∀ f ∈ N, t * f * t⁻¹ ∈ N) : Subgroup G where
  carrier := {g | g ∈ N ∨ g * t ∈ N}
  one_mem' := Or.inl N.one_mem
  mul_mem' := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (N.mul_mem ha hb)
    · right
      rw [mul_assoc]
      exact N.mul_mem ha hb
    · right
      have e : a * b * t = a * t * (t * b * t⁻¹) := by
        calc a * b * t = a * (t * t) * b * t := by rw [ht, mul_one]
          _ = a * t * (t * b * t⁻¹) := by rw [htinv]; group
      rw [e]
      exact N.mul_mem ha (hN b hb)
    · left
      have e : a * b = a * t * (t * (b * t) * t⁻¹) := by
        calc a * b = a * (t * t) * b * (t * t) := by rw [ht, mul_one, mul_one]
          _ = a * t * (t * (b * t) * t⁻¹) := by rw [htinv]; group
      rw [e]
      exact N.mul_mem ha (hN _ hb)
  inv_mem' := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rintro a (ha | ha)
    · exact Or.inl (N.inv_mem ha)
    · right
      have e : a⁻¹ * t = t * (a * t)⁻¹ * t⁻¹ := by
        calc a⁻¹ * t = a⁻¹ * t⁻¹ := by rw [htinv]
          _ = t * (a * t)⁻¹ * t⁻¹ := by group
      rw [e]
      exact hN _ (N.inv_mem ha)

theorem mem_cosetSub {N : Subgroup G} {t : G} {ht : t * t = 1}
    {hN : ∀ f ∈ N, t * f * t⁻¹ ∈ N} {g : G} : g ∈ cosetSub N ht hN ↔ g ∈ N ∨ g * t ∈ N :=
  Iff.rfl

theorem sup_zpowers_le_cosetSub (N : Subgroup G) {t : G} (ht : t * t = 1)
    (hN : ∀ f ∈ N, t * f * t⁻¹ ∈ N) : N ⊔ Subgroup.zpowers t ≤ cosetSub N ht hN :=
  sup_le (fun _ hg => Or.inl hg)
    (Subgroup.zpowers_le.2 (Or.inr (by rw [ht]; exact N.one_mem)))

theorem mem_or_mul_mem_of_mem_sup {N : Subgroup G} {t : G} (ht : t * t = 1)
    (hN : ∀ f ∈ N, t * f * t⁻¹ ∈ N) {g : G} (hg : g ∈ N ⊔ Subgroup.zpowers t) :
    g ∈ N ∨ g * t ∈ N :=
  sup_zpowers_le_cosetSub N ht hN hg

theorem isSolvable_sup_zpowers (N : Subgroup G) [hNs : Group.IsSolvable N] {t : G}
    (ht : t * t = 1) (hN : ∀ f ∈ N, t * f * t⁻¹ ∈ N) :
    Group.IsSolvable ↥(N ⊔ Subgroup.zpowers t) := by
  classical
  set H := N ⊔ Subgroup.zpowers t with hH
  have hmem : ∀ g ∈ H, g ∈ N ∨ g * t ∈ N := fun g hg => mem_or_mul_mem_of_mem_sup ht hN hg
  have hpar : ∀ a ∈ H, ∀ b ∈ H, (a * b ∈ N ↔ (a ∈ N ↔ b ∈ N)) := by
    intro a ha b hb
    have hS : a * b ∈ cosetSub N ht hN :=
      (cosetSub N ht hN).mul_mem (sup_zpowers_le_cosetSub N ht hN ha)
        (sup_zpowers_le_cosetSub N ht hN hb)
    by_cases haN : a ∈ N <;> by_cases hbN : b ∈ N
    · exact ⟨fun _ => ⟨fun _ => hbN, fun _ => haN⟩, fun _ => N.mul_mem haN hbN⟩
    · refine ⟨fun h => absurd ?_ hbN, fun h => absurd (h.1 haN) hbN⟩
      have := N.mul_mem (N.inv_mem haN) h
      rwa [inv_mul_cancel_left] at this
    · refine ⟨fun h => absurd ?_ haN, fun h => absurd (h.2 hbN) haN⟩
      have := N.mul_mem h (N.inv_mem hbN)
      rwa [mul_inv_cancel_right] at this
    · refine ⟨fun _ => ⟨fun h => absurd h haN, fun h => absurd h hbN⟩, fun _ => ?_⟩
      have hat : a * t ∈ N := (hmem a ha).resolve_left haN
      have hbt : b * t ∈ N := (hmem b hb).resolve_left hbN
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      have e : a * b = a * t * (t * (b * t) * t⁻¹) := by
        calc a * b = a * (t * t) * b * (t * t) := by rw [ht, mul_one, mul_one]
          _ = a * t * (t * (b * t) * t⁻¹) := by rw [htinv]; group
      rw [e]
      exact N.mul_mem hat (hN _ hbt)
  let g : ↥H →* Multiplicative (ZMod 2) :=
    { toFun := fun h => if (h : G) ∈ N then 1 else Multiplicative.ofAdd 1
      map_one' := by simp [N.one_mem]
      map_mul' := by
        intro a b
        have hp := hpar a a.2 b b.2
        have h11 : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
        simp only [Subgroup.coe_mul]
        by_cases haN : (a : G) ∈ N <;> by_cases hbN : (b : G) ∈ N <;> simp_all }
  have hker : g.ker ≤ (Subgroup.inclusion (le_sup_left : N ≤ H)).range := by
    intro h hh
    have h1 : (h : G) ∈ N := by
      by_contra hn
      have : g h = Multiplicative.ofAdd 1 := by simp [g, hn]
      rw [MonoidHom.mem_ker, this] at hh
      exact absurd hh (by decide)
    exact ⟨⟨h, h1⟩, rfl⟩
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion (le_sup_left : N ≤ H)) g hker

end Group

section Module

variable {V : Type*} [CommGroup V]

theorem isFFStarMin_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {t : MulAut V} (htX : t ∈ X) (ht : IsTransvection t) :
    IsFFStarMin X (Subgroup.zpowers t) := by
  obtain ⟨ht1, w, htw⟩ := ht
  have hsq : t * t = 1 := B1.tv_sq hV htw ht1
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) ht1
  have hne : Subgroup.zpowers t ≠ ⊥ := fun h => ht1 (Subgroup.zpowers_eq_bot.1 h)
  have hsub : ∀ B ≤ Subgroup.zpowers t, B = ⊥ ∨ B = Subgroup.zpowers t := by
    intro B hB
    have hd : Nat.card B ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le hB
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact Or.inl (Subgroup.eq_bot_of_card_eq B h)
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hB (by rw [h, hcard]))
  have hoff : IsFFStarOffender X (Subgroup.zpowers t) := by
    refine ⟨Subgroup.zpowers_le.2 htX, hne, B1.isElemAbelian2_zpowers_tv hV ht1 htw,
      fun B hB => ?_⟩
    rcases hsub B hB with rfl | rfl
    · rw [B1.card_bot_mul_card_fixV, hcard, ← B1.card_eq_two_mul_fixV_of_tv hV ht1 htw]
    · exact le_rfl
  refine ⟨hoff, fun B hB hle => ?_⟩
  rcases hsub B hle.2.2.1 with rfl | h
  · exact absurd rfl hB.2.1
  · exact h

theorem tv_eq_of_fix [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {s s' : MulAut V} {w : V}
    (hs : IsTransvectionWith s w) (hs1 : s ≠ 1) (hs' : IsTransvectionWith s' w)
    (hs'1 : s' ≠ 1) {C : Subgroup V} (hCs : ∀ c ∈ C, s c = c) (hCs' : ∀ c ∈ C, s' c = c)
    (hC : Nat.card V ≤ 2 * Nat.card C) : s = s' := by
  have hfix : ∀ {r : MulAut V}, IsTransvectionWith r w → r ≠ 1 → (∀ c ∈ C, r c = c) →
      fixV (Subgroup.zpowers r) = C := by
    intro r hr hr1 hCr
    have hle : C ≤ fixV (Subgroup.zpowers r) := fun c hc y hy => B1.zpowers_fix (hCr c hc) y hy
    have h2 := B1.card_eq_two_mul_fixV_of_tv hV hr1 hr
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  have h1 := hfix hs hs1 hCs
  have h2 := hfix hs' hs'1 hCs'
  refine MulEquiv.ext fun v => ?_
  by_cases hv : v ∈ C
  · rw [hCs v hv, hCs' v hv]
  · have hsv : s v ≠ v := fun h => hv (h1 ▸ fun y hy => B1.zpowers_fix h y hy)
    have hs'v : s' v ≠ v := fun h => hv (h2 ▸ fun y hy => B1.zpowers_fix h y hy)
    rw [(hs.2 v).resolve_left hsv, (hs'.2 v).resolve_left hs'v]

theorem zpowers_three_decomp [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hx3 : x ^ 3 = 1) :
    fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) = ⊤ ∧
      fixV (Subgroup.zpowers x) ⊓ commSub ⊤ (Subgroup.zpowers x) = ⊥ ∧
      (∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
        x m ∈ commSub ⊤ (Subgroup.zpowers x)) ∧
      (∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), x m = m → m = 1) ∧
      (∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), x (x m) = m → m = 1) := by
  obtain ⟨hsup, hinf, hMx, hfpf⟩ := B1.zpowers_decomp hV (r := 3) (by decide) hx3
  refine ⟨hsup, hinf, hMx, hfpf, fun m hm h => hfpf m hm ?_⟩
  exact B1.fix_of_sq_fix (r := 3) (by decide) hx3 (by rw [pow_two]; exact h)

theorem commSub_zpowers_invariant {x b : MulAut V} (hb : b * x * b⁻¹ ∈ Subgroup.zpowers x) :
    ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
      b m ∈ commSub ⊤ (Subgroup.zpowers x) := by
  refine B1.commSub_smul_mem b (fun y hy => ?_) (fun _ _ => trivial)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h1 : b * x ^ k * b⁻¹ = (b * x * b⁻¹) ^ k := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [h1]
  exact Subgroup.zpow_mem _ hb k

theorem fix_of_comm_sq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x b : MulAut V} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hMx : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) = 4)
    (hb : b * b = 1) (hbx : x * b = b * x) :
    ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), b m = m := by
  obtain ⟨-, -, hMxinv, hfpf, hfpf2⟩ := zpowers_three_decomp hV hx3
  have hbn : b * x * b⁻¹ ∈ Subgroup.zpowers x := by
    rw [← hbx, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers x
  have hMb := commSub_zpowers_invariant hbn
  have hbb : ∀ m, b (b m) = m := fun m => by
    rw [← MulAut.mul_apply, hb]
    rfl
  have hx3' : ∀ m, x (x (x m)) = m := fun m => by
    have : (x ^ 3) m = m := by rw [hx3]; rfl
    simpa [pow_succ, MulAut.mul_apply] using this
  rcases B1.fix_or_pow_on_M hMxinv hMb hbx hfpf hfpf2 hMx.le (B1.commSub_top_ne_bot hx1)
    with h | h | h
  · exact h
  · intro m hm
    have h1 : x (x m) = m := by rw [← h _ (hMxinv m hm), ← h m hm, hbb]
    rw [hfpf2 m hm h1, map_one]
  · intro m hm
    have h1 : x m = m := by
      have h2 := h _ (hMxinv _ (hMxinv m hm))
      rw [hx3', ← h m hm] at h2
      rw [← h2, hbb]
    rw [hfpf m hm h1, map_one]

theorem fix_of_comm_inv [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x y t : MulAut V}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hMx : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) = 4)
    (hyx : x * y = y * x) (hyt : y * t = t * y) (htx : t * x * t⁻¹ = x⁻¹) :
    ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), y m = m := by
  obtain ⟨-, -, hMxinv, hfpf, hfpf2⟩ := zpowers_three_decomp hV hx3
  have hyn : y * x * y⁻¹ ∈ Subgroup.zpowers x := by
    rw [← hyx, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers x
  have hMy := commSub_zpowers_invariant hyn
  have htn : t * x * t⁻¹ ∈ Subgroup.zpowers x := by
    rw [htx]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
  have hMt := commSub_zpowers_invariant htn
  have hyt' : ∀ m, y (t m) = t (y m) := fun m => by
    rw [← MulAut.mul_apply, hyt, MulAut.mul_apply]
  have htx' : ∀ m, t (x m) = x⁻¹ (t m) := fun m => by
    have : t * x = x⁻¹ * t := by rw [← htx, inv_mul_cancel_right]
    rw [← MulAut.mul_apply, this, MulAut.mul_apply]
  have hxinv : ∀ m, x⁻¹ m = x (x m) := fun m => by
    have : x⁻¹ = x * x := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ', hx3]
    rw [this, MulAut.mul_apply]
  rcases B1.fix_or_pow_on_M hMxinv hMy hyx hfpf hfpf2 hMx.le (B1.commSub_top_ne_bot hx1)
    with h | h | h
  · exact h
  · intro m hm
    have htm := hMt m hm
    have h1 : x (t m) = x (x (t m)) := by
      calc x (t m) = y (t m) := (h _ htm).symm
        _ = t (y m) := hyt' m
        _ = t (x m) := by rw [h m hm]
        _ = x⁻¹ (t m) := htx' m
        _ = x (x (t m)) := hxinv _
    have h2 : x (t m) = t m := (x.injective h1).symm
    have h3 : t m = 1 := hfpf _ htm h2
    have h4 : m = 1 := by
      have := congrArg t⁻¹ h3
      simpa using this
    rw [h4, map_one]
  · intro m hm
    have htm := hMt m hm
    have hx3' : ∀ u, x (x (x u)) = u := fun u => by
      have : (x ^ 3) u = u := by rw [hx3]; rfl
      simpa [pow_succ, MulAut.mul_apply] using this
    have h1 : x (x (t m)) = x (t m) := by
      calc x (x (t m)) = y (t m) := (h _ htm).symm
        _ = t (y m) := hyt' m
        _ = t (x (x m)) := by rw [h m hm]
        _ = x⁻¹ (t (x m)) := htx' _
        _ = x⁻¹ (x⁻¹ (t m)) := by rw [htx']
        _ = x (t m) := by rw [hxinv, hxinv, hx3']
    have h2 : x (t m) = t m := x.injective h1
    have h3 : t m = 1 := hfpf _ htm h2
    have h4 : m = 1 := by
      have := congrArg t⁻¹ h3
      simpa using this
    rw [h4, map_one]

@[expose] def commLeSub (M : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, g v * v⁻¹ ∈ M}
  one_mem' := fun v => by simp
  mul_mem' := by
    intro g g' hg hg' v
    have h1 : (g * g') v * v⁻¹ = (g (g' v) * (g' v)⁻¹) * (g' v * v⁻¹) := by
      simp only [MulAut.mul_apply]
      group
    rw [h1]
    exact M.mul_mem (hg (g' v)) (hg' v)
  inv_mem' := by
    intro g hg v
    have h1 : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by
      have : g (g⁻¹ v) = v := by simp
      rw [this]
      group
    rw [h1]
    exact M.inv_mem (hg (g⁻¹ v))

theorem commV_le_iff {H : Subgroup (MulAut V)} {M : Subgroup V} :
    commV H ≤ M ↔ H ≤ commLeSub M := by
  constructor
  · intro h g hg v
    exact h (Subgroup.subset_closure ⟨g, hg, v, rfl⟩)
  · intro h
    refine (Subgroup.closure_le M).2 ?_
    rintro _ ⟨g, hg, v, rfl⟩
    exact h hg v

theorem commV_mono {H K : Subgroup (MulAut V)} (h : H ≤ K) : commV H ≤ commV K :=
  Subgroup.closure_mono fun _ ⟨g, hg, v, hv⟩ => ⟨g, h hg, v, hv⟩

theorem commV_iSup {ι : Sort*} (S : ι → Subgroup (MulAut V)) :
    commV (⨆ i, S i) = ⨆ i, commV (S i) := by
  apply le_antisymm
  · rw [commV_le_iff]
    exact iSup_le fun i => commV_le_iff.1 (le_iSup (fun i => commV (S i)) i)
  · exact iSup_le fun i => commV_mono (le_iSup S i)

theorem commV_sup (H K : Subgroup (MulAut V)) : commV (H ⊔ K) = commV H ⊔ commV K := by
  apply le_antisymm
  · rw [commV_le_iff]
    exact sup_le (commV_le_iff.1 le_sup_left) (commV_le_iff.1 le_sup_right)
  · exact sup_le (commV_mono le_sup_left) (commV_mono le_sup_right)

theorem commV_map_conj (g : MulAut V) (K : Subgroup (MulAut V)) :
    commV (K.map (MulAut.conj g).toMonoidHom) = (commV K).map g.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq K g

theorem iSupIndep_of_centSub {ι : Type*} (f : ι → Subgroup (MulAut V)) (M : ι → Subgroup V)
    (h1 : ∀ i, f i ⊓ centSub (M i) = ⊥) (h2 : ∀ i j, i ≠ j → f j ≤ centSub (M i)) :
    iSupIndep f := by
  intro i
  rw [disjoint_iff]
  exact le_bot_iff.1 ((inf_le_inf_left _ (iSup₂_le fun j hj => h2 i j (Ne.symm hj))).trans
    (h1 i).le)

theorem iSupIndep_of_fixV {ι : Type*} (U : ι → Subgroup V) (Y : ι → Subgroup (MulAut V))
    (h1 : ∀ i, U i ⊓ fixV (Y i) = ⊥) (h2 : ∀ i j, i ≠ j → U j ≤ fixV (Y i)) :
    iSupIndep U := by
  intro i
  rw [disjoint_iff]
  exact le_bot_iff.1 ((inf_le_inf_left _ (iSup₂_le fun j hj => h2 i j (Ne.symm hj))).trans
    (h1 i).le)

end Module

end CFSG.Quasithin.B19
