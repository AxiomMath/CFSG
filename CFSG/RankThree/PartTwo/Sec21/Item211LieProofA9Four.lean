module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofS9

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211LieProof

open Equiv

theorem apply_eq_self_of_sq_cube {α : Type*} {u v : Perm α} (hu : u ^ 2 = 1) (hv : v ^ 3 = 1)
    (huv : u * v = v * u) {y : α} (h : u y = v y) : v y = y := by
  have h1 : u (u y) = v (v y) := by
    calc u (u y) = u (v y) := by rw [h]
      _ = (v * u) y := by rw [← huv]; rfl
      _ = v (v y) := by rw [Perm.mul_apply, h]
  have h2 : u (u y) = y := by
    rw [← Perm.mul_apply, ← sq, hu, Perm.one_apply]
  have h3 : v (v (v y)) = y := by
    rw [← Perm.mul_apply, ← Perm.mul_apply, ← pow_three', hv, Perm.one_apply]
  have h4 : v (v y) = y := by rw [← h1]; exact h2
  calc v y = v (v (v y)) := by rw [h4]
    _ = y := h3

theorem pow_apply_inj_of_cube {α : Type*} {b : Perm α} (hb : b ^ 3 = 1) {x : α} (hx : b x ≠ x)
    {i j : ℕ} (hi : i < 3) (hj : j < 3) (h : (b ^ i) x = (b ^ j) x) : i = j := by
  have h3 : b (b (b x)) = x := by
    rw [← Perm.mul_apply, ← Perm.mul_apply, ← pow_three', hb, Perm.one_apply]
  have h2 : b (b x) ≠ x := by
    intro h2
    apply hx
    rw [h2] at h3
    exact h3
  have h1 : b (b x) ≠ b x := fun h1 => hx (b.injective h1)
  interval_cases i <;> interval_cases j <;>
    simp only [pow_zero, pow_one, sq, Perm.one_apply, Perm.mul_apply] at h <;>
    first | rfl | exact absurd h.symm hx | exact absurd h.symm h2 | exact absurd h.symm h1 |
      exact absurd h hx | exact absurd h h2 | exact absurd h h1

theorem apply_eq_of_mul_pow_apply_eq {α : Type*} {T : Subgroup (Perm α)}
    (hT2 : ∀ t ∈ T, t ^ 2 = 1) {b : Perm α} (hb3 : b ^ 3 = 1) (hbT : ∀ t ∈ T, b * t = t * b)
    {x : α} (hx : b x ≠ x) {u u' : Perm α} (hu : u ∈ T) (hu' : u' ∈ T) {i i' : ℕ} (hi : i < 3)
    (hi' : i' < 3) (h : (u * b ^ i) x = (u' * b ^ i') x) : i = i' ∧ u x = u' x := by
  set a := u'⁻¹ * u with ha
  have haT : a ∈ T := T.mul_mem (T.inv_mem hu') hu
  set v := b ^ (i' + 2 * i) with hv
  have hv3 : v ^ 3 = 1 := by
    rw [hv, ← pow_mul, mul_comm, pow_mul, hb3, one_pow]
  have hav : a * v = v * a := ((Commute.pow_left (hbT a haT) _).eq).symm
  have hvy : v ((b ^ i) x) = (b ^ i') x := by
    rw [← Perm.mul_apply, hv, ← pow_add, show i' + 2 * i + i = i' + 3 * i by ring, pow_add,
      pow_mul, hb3, one_pow, mul_one]
  have hay : a ((b ^ i) x) = v ((b ^ i) x) := by
    rw [hvy]
    calc a ((b ^ i) x) = u'⁻¹ ((u * b ^ i) x) := rfl
      _ = u'⁻¹ ((u' * b ^ i') x) := by rw [h]
      _ = (b ^ i') x := by rw [Perm.mul_apply, ← Perm.mul_apply u'⁻¹, inv_mul_cancel,
        Perm.one_apply]
  have h1 := apply_eq_self_of_sq_cube (hT2 a haT) hv3 hav hay
  have h1' := h1
  rw [hvy] at h1'
  have hii := pow_apply_inj_of_cube hb3 hx hi' hi h1'
  refine ⟨hii.symm, ?_⟩
  have h2 : a ((b ^ i) x) = (b ^ i) x := hay.trans h1
  have hab : a * b ^ i = b ^ i * a := ((Commute.pow_left (hbT a haT) _).eq).symm
  rw [← Perm.mul_apply, hab, Perm.mul_apply] at h2
  have h3 : a x = x := (b ^ i).injective h2
  calc u x = u' (u'⁻¹ (u x)) := by rw [← Perm.mul_apply u', mul_inv_cancel, Perm.one_apply]
    _ = u' x := by rw [← Perm.mul_apply u'⁻¹, ← ha, h3]

theorem nodup_five {G : Type*} {a b c d e : G} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : [a, b, c, d, e].Nodup := by
  simp [List.nodup_cons, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

theorem five_le_card_of_nodup {G : Type*} [Group G] [Finite G] (T : Subgroup G)
    {a b c d e : G} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) (he : e ∈ T)
    (hnd : [a, b, c, d, e].Nodup) : 5 ≤ Nat.card T := by
  classical
  have hsub : (([a, b, c, d, e].toFinset : Finset G) : Set G) ⊆ (T : Set G) := by
    intro y hy
    simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd] at h
  rw [← Nat.card_coe_set_eq] at h
  exact h

theorem conj_ne_self_of_card_four {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT4 : Nat.card T = 4) {d : G} (hd3 : d ^ 3 = 1) (hdT : ∀ t ∈ T, d * t * d⁻¹ ∈ T)
    {t : G} (ht : t ∈ T) (hdt : d * t ≠ t * d) {s : G} (hs : s ∈ T) (hs1 : s ≠ 1) :
    d * s * d⁻¹ ≠ s := by
  intro hds
  set y := d * t * d⁻¹ with hy
  set z := d * y * d⁻¹ with hz
  have hyT : y ∈ T := hdT t ht
  have hzT : z ∈ T := hdT y hyT
  have hconj : ∀ a a' : G, d * a * d⁻¹ = d * a' * d⁻¹ → a = a' := fun a a' h =>
    mul_left_cancel (mul_right_cancel h)
  have hd3' : d * d * d = 1 := by rw [← pow_three']; exact hd3
  have hzt : d * z * d⁻¹ = t := by
    have e : d * z * d⁻¹ = (d * d * d) * t * (d * d * d)⁻¹ := by rw [hz, hy]; group
    rw [e, hd3', one_mul, inv_one, mul_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h] at hdt
    exact hdt (by group)
  have hts : t ≠ s := by
    intro h
    rw [h] at hdt
    exact hdt (by
      calc d * s = d * s * d⁻¹ * d := by group
        _ = s * d := by rw [hds])
  have hyt : y ≠ t := fun h => hdt (by
    calc d * t = d * t * d⁻¹ * d := by group
      _ = t * d := by rw [← hy, h])
  have hy1 : y ≠ 1 := fun h => ht1 (hconj t 1 (by rw [← hy, h]; group))
  have hys : y ≠ s := fun h => hts (hconj t s (by rw [← hy, h, hds]))
  have hz1 : z ≠ 1 := fun h => hy1 (hconj y 1 (by rw [← hz, h]; group))
  have hzs : z ≠ s := fun h => hys (hconj y s (by rw [← hz, h, hds]))
  have hzy : z ≠ y := fun h => hyt (hconj y t (by rw [← hz, h]))
  have hzt' : z ≠ t := fun h => hyt (by
    calc y = d * t * d⁻¹ := hy
      _ = d * z * d⁻¹ := by rw [h]
      _ = t := hzt)
  have h5 := five_le_card_of_nodup T (one_mem T) hs ht hyT hzT
    (nodup_five hs1.symm ht1.symm hy1.symm hz1.symm hts.symm hys.symm hzs.symm hyt.symm
      hzt'.symm hzy.symm)
  omega

theorem maxPartProd_lt_four : ∀ n < 4, maxPartProd n < 4 := by
  decide

theorem apply_eq_self_of_moved {T : Subgroup (Perm (Fin 9))}
    (hTc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) (hT2 : ∀ t ∈ T, t ^ 2 = 1)
    (hT4 : Nat.card T = 4) {d b : Perm (Fin 9)} (hd3 : d ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hdT : ∀ t ∈ T, d * t * d⁻¹ ∈ T) (hdC : ∃ t ∈ T, d * t ≠ t * d)
    (hbT : ∀ t ∈ T, b * t = t * b) {x : Fin 9} (hx : b x ≠ x) : ∀ t ∈ T, t x = x := by
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨t₀, ht₀, ht₀x⟩ := hcon
  have hpow : ∀ e : ℕ, t₀ ^ e ∈ T := fun e => T.pow_mem ht₀ e
  have hcomm : ∀ a ∈ T, ∀ e i : ℕ, a * (t₀ ^ e * b ^ i) = (t₀ ^ e * b ^ i) * a := by
    intro a ha e i
    have c1 : a * t₀ ^ e = t₀ ^ e * a := hTc a ha _ (hpow e)
    have c2 : a * b ^ i = b ^ i * a := ((Commute.pow_left (hbT a ha) i).eq).symm
    calc a * (t₀ ^ e * b ^ i) = (a * t₀ ^ e) * b ^ i := by group
      _ = t₀ ^ e * (a * b ^ i) := by rw [c1]; group
      _ = (t₀ ^ e * b ^ i) * a := by rw [c2]; group
  have hfix : ∀ a ∈ T, a x = x → ∀ e i : ℕ, a ((t₀ ^ e * b ^ i) x) = (t₀ ^ e * b ^ i) x := by
    intro a ha hax e i
    rw [← Perm.mul_apply, hcomm a ha e i, Perm.mul_apply, hax]
  have hfix' : ∀ a ∈ T, ∀ e i : ℕ, a ((t₀ ^ e * b ^ i) x) = (t₀ ^ e * b ^ i) x → a x = x := by
    intro a ha e i h
    rw [← Perm.mul_apply, hcomm a ha e i, Perm.mul_apply] at h
    exact (t₀ ^ e * b ^ i).injective h
  have hsame : ∀ e e' i i' : ℕ, e < 2 → e' < 2 → i < 3 → i' < 3 →
      (t₀ ^ e * b ^ i) x = (t₀ ^ e' * b ^ i') x → e = e' ∧ i = i' := by
    intro e e' i i' he he' hi hi' h
    obtain ⟨hii, hex⟩ := apply_eq_of_mul_pow_apply_eq hT2 hb3 hbT hx (hpow e) (hpow e') hi hi' h
    refine ⟨?_, hii⟩
    interval_cases e <;> interval_cases e'
    · rfl
    · simp only [pow_zero, pow_one, Perm.one_apply] at hex
      exact absurd hex.symm ht₀x
    · simp only [pow_zero, pow_one, Perm.one_apply] at hex
      exact absurd hex ht₀x
    · rfl
  by_cases hs : ∃ s ∈ T, s ≠ 1 ∧ s x = x
  · obtain ⟨s, hsT, hs1, hsx⟩ := hs
    obtain ⟨t, ht, hdt⟩ := hdC
    have hds := conj_ne_self_of_card_four hT4 hd3 hdT ht hdt hsT hs1
    have hd3' : d * d * d = 1 := by rw [← pow_three']; exact hd3
    set s' := d⁻¹ * s * d with hs'
    have hs'T : s' ∈ T := by
      have e : s' = d * (d * s * d⁻¹) * d⁻¹ := by
        have e2 : d * (d * s * d⁻¹) * d⁻¹ = (d * d * d) * (d⁻¹ * s * d) * (d * d * d)⁻¹ := by
          group
        rw [e2, hd3', one_mul, inv_one, mul_one]
      rw [e]
      exact hdT _ (hdT s hsT)
    have hcross : ∀ e e' i i' : ℕ, (t₀ ^ e * b ^ i) x ≠ d ((t₀ ^ e' * b ^ i') x) := by
      intro e e' i i' h
      have h1 : s (d ((t₀ ^ e' * b ^ i') x)) = d ((t₀ ^ e' * b ^ i') x) := by
        rw [← h]; exact hfix s hsT hsx e i
      have h2 : s' ((t₀ ^ e' * b ^ i') x) = (t₀ ^ e' * b ^ i') x := by
        rw [hs', Perm.mul_apply, Perm.mul_apply, h1, ← Perm.mul_apply, inv_mul_cancel,
          Perm.one_apply]
      have hs'x : s' x = x := hfix' s' hs'T e' i' h2
      have hs'1 : s' ≠ 1 := fun h0 => hs1 (by
        have e : s = d * s' * d⁻¹ := by rw [hs']; group
        rw [e, h0]; group)
      have hs's : s' ≠ s := fun h0 => hds (by
        calc d * s * d⁻¹ = d * s' * d⁻¹ := by rw [h0]
          _ = s := by rw [hs']; group)
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hT2 s hsT)
      have hss1 : s * s' ≠ 1 := fun h0 => hs's (by
        rw [eq_inv_of_mul_eq_one_right h0, hsinv])
      have hsss : s ≠ s * s' := fun h0 => hs'1 (by
        have : s * 1 = s * s' := by rw [mul_one]; exact h0
        exact (mul_left_cancel this).symm)
      have hs'ss : s' ≠ s * s' := fun h0 => hs1 (by
        have : 1 * s' = s * s' := by rw [one_mul]; exact h0
        exact (mul_right_cancel this).symm)
      have hne : ∀ a : Perm (Fin 9), a x = x → a ≠ t₀ := fun a hax h0 => ht₀x (h0 ▸ hax)
      have hss'x : (s * s') x = x := by rw [Perm.mul_apply, hs'x, hsx]
      have h5 := five_le_card_of_nodup T (one_mem T) hsT hs'T (T.mul_mem hsT hs'T) ht₀
        (nodup_five hs1.symm hs'1.symm hss1.symm (hne 1 rfl) hs's.symm hsss (hne s hsx) hs'ss
          (hne s' hs'x) (hne _ hss'x))
      omega
    have hf : Function.Injective (fun p : Fin 2 × Fin 2 × Fin 3 =>
        (d ^ (p.1 : ℕ)) ((t₀ ^ (p.2.1 : ℕ) * b ^ (p.2.2 : ℕ)) x)) := by
      rintro ⟨j, e, i⟩ ⟨j', e', i'⟩ h
      simp only at h
      have hj : j = j' := by
        fin_cases j <;> fin_cases j'
        · rfl
        · exact absurd (show (t₀ ^ (e : ℕ) * b ^ (i : ℕ)) x = d ((t₀ ^ (e' : ℕ) *
            b ^ (i' : ℕ)) x) by simpa using h) (hcross _ _ _ _)
        · exact absurd (show (t₀ ^ (e' : ℕ) * b ^ (i' : ℕ)) x = d ((t₀ ^ (e : ℕ) *
            b ^ (i : ℕ)) x) by simpa using h.symm) (hcross _ _ _ _)
        · rfl
      subst hj
      have h' := (d ^ (j : ℕ)).injective h
      obtain ⟨he, hi⟩ := hsame _ _ _ _ e.2 e'.2 i.2 i'.2 h'
      simp only [Prod.mk.injEq]
      exact ⟨trivial, Fin.ext he, Fin.ext hi⟩
    have := Fintype.card_le_of_injective _ hf
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    omega
  · simp only [not_exists, not_and] at hs
    have hf : Function.Injective
        (fun p : T × Fin 3 => ((p.1 : Perm (Fin 9)) * b ^ (p.2 : ℕ)) x) := by
      rintro ⟨u, i⟩ ⟨u', i'⟩ h
      simp only at h
      obtain ⟨hii, hux⟩ := apply_eq_of_mul_pow_apply_eq hT2 hb3 hbT hx u.2 u'.2 i.2 i'.2 h
      have hu : (u : Perm (Fin 9)) = u' := by
        by_contra hne
        have h1 : (u' : Perm (Fin 9))⁻¹ * u ≠ 1 := fun h1 => hne (inv_mul_eq_one.mp h1).symm
        apply hs _ (T.mul_mem (T.inv_mem u'.2) u.2) h1
        rw [Perm.mul_apply, hux, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
      exact Prod.ext (Subtype.ext hu) (Fin.ext hii)
    have := Nat.card_le_card_of_injective _ hf
    rw [Nat.card_prod, hT4, Nat.card_fin, Nat.card_fin] at this
    omega

theorem ofSubtype_mul_comm {F : Finset (Fin 9)} (σ : Perm F) {t : Perm (Fin 9)}
    (ht : ∀ y ∈ F, t y = y) : Perm.ofSubtype σ * t = t * Perm.ofSubtype σ := by
  ext y
  simp only [Perm.mul_apply]
  by_cases hy : y ∈ F
  · rw [ht y hy, Perm.ofSubtype_apply_of_mem σ hy, ht _ (σ ⟨y, hy⟩).2]
  · have hty : t y ∉ F := fun h => hy (by
      have h1 := t.injective (ht _ h)
      rw [← h1]
      exact h)
    rw [Perm.ofSubtype_apply_of_not_mem σ hty, Perm.ofSubtype_apply_of_not_mem σ hy]

theorem eq_bot_of_isPGroup_two_of_normal {F : Finset (Fin 9)} (hF : F.card = 3 ∨ F.card = 5)
    (N : Subgroup (alternatingGroup F)) (hN : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (alternatingGroup F) = F.card.factorial / 2 := by
    have : Nontrivial F := by
      rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card, Fintype.card_coe]
      omega
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_coe]
  obtain ⟨k, hk⟩ := hN2.exists_card_eq
  rcases hF with h3 | h5
  · have hdvd : Nat.card N ∣ 3 := by
      have := Subgroup.card_subgroup_dvd_card N
      rwa [hcard, h3] at this
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      rcases k with _ | k
      · rfl
      · exfalso
        have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
        omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq N hk
  · have e : F ≃ Fin 5 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, h5])
    have : IsSimpleGroup (alternatingGroup F) := (Equiv.altCongrHom e).isSimpleGroup
    rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top, hcard, h5] at hk
      have h60 : (Nat.factorial 5) / 2 = 60 := by decide
      rw [h60] at hk
      have hk6 : k < 6 := by
        by_contra hlt
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hlt)
        omega
      interval_cases k <;> omega

theorem comm_of_fourGroup {T W : Subgroup (Perm (Fin 9))}
    (hTc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) (hT2 : ∀ t ∈ T, t ^ 2 = 1)
    (hT4 : Nat.card T = 4) {d b : Perm (Fin 9)} (hd3 : d ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hdT : ∀ t ∈ T, d * t * d⁻¹ ∈ T) (hdC : ∃ t ∈ T, d * t ≠ t * d)
    (hbT : ∀ t ∈ T, b * t = t * b) (hbs : Perm.sign b = 1) (hW2 : IsPGroup 2 W)
    (hWT : ∀ w ∈ W, ∀ t ∈ T, w * t = t * w)
    (hN : ∀ g : Perm (Fin 9), Perm.sign g = 1 → (∀ t ∈ T, g * t = t * g) → g ^ 3 = 1 →
      ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    ∀ w ∈ W, b * w = w * b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro w hw
  set F : Finset (Fin 9) := Finset.univ.filter (fun y => ∀ t ∈ T, t y = y) with hF
  have hmemF : ∀ y, y ∈ F ↔ ∀ t ∈ T, t y = y := fun y => by simp [hF]
  have hbF : ∀ y, y ∉ F → b y = y := fun y hy => by
    by_contra hby
    exact hy ((hmemF y).mpr (apply_eq_self_of_moved hTc hT2 hT4 hd3 hb3 hdT hdC hbT hby))
  have hpres : ∀ g : Perm (Fin 9), (∀ t ∈ T, g * t = t * g) → ∀ y, y ∈ F → g y ∈ F := by
    intro g hg y hy
    rw [hmemF] at hy ⊢
    intro t ht
    rw [← Perm.mul_apply, ← hg t ht, Perm.mul_apply, hy t ht]
  by_cases hb1 : b = 1
  · rw [hb1, one_mul, mul_one]
  obtain ⟨x, hx⟩ : ∃ x, b x ≠ x := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hb1 (Equiv.ext h)
  have hxF : x ∈ F := by
    by_contra h
    exact hx (hbF x h)
  have hbxF : b x ∈ F := by
    by_contra h
    exact hx (b.injective (hbF _ h))
  have hF2 : 2 ≤ F.card := by
    have hsub : ({x, b x} : Finset (Fin 9)) ⊆ F := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> assumption
    have h2 := Finset.card_le_card hsub
    rwa [Finset.card_pair hx.symm] at h2
  have hFodd : F.card % 2 = 1 := by
    have hT2g : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
    have hmod := hT2g.card_modEq_card_fixedPoints (Fin 9)
    have hset : MulAction.fixedPoints T (Fin 9) = (F : Set (Fin 9)) := by
      ext y
      simp only [MulAction.mem_fixedPoints, Finset.mem_coe, hmemF, Subgroup.smul_def,
        Perm.smul_def, Subtype.forall]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_fin] at hmod
    unfold Nat.ModEq at hmod
    omega
  have hF5 : F.card ≤ 5 := by
    have hTcomm : IsMulCommutative T := ⟨⟨fun a a' => Subtype.ext (hTc a a.2 a' a'.2)⟩⟩
    have hcompl : ((F : Set (Fin 9))ᶜ).ncard = 9 - F.card := by
      rw [Set.ncard_compl, Nat.card_fin, Set.ncard_coe_finset]
    have h := card_le_maxPartProd (9 - F.card) (by omega) T hTcomm ((F : Set (Fin 9))ᶜ) hcompl
      (fun a ha y hy => by
        rw [Set.notMem_compl_iff, Finset.mem_coe] at hy
        exact (hmemF y).mp hy a ha)
    rw [hT4] at h
    by_contra hlt
    have := maxPartProd_lt_four (9 - F.card) (by omega)
    omega
  have hF35 : F.card = 3 ∨ F.card = 5 := by omega
  have hnorm : ∀ g : Perm F, g ∈ alternatingGroup F →
      Perm.ofSubtype g ∈ Subgroup.normalizer (W : Set (Perm (Fin 9))) := by
    intro g hg
    have hH : alternatingGroup F ≤
        (Subgroup.normalizer (W : Set (Perm (Fin 9)))).comap Perm.ofSubtype := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro σ hσ
      have hσ3 : σ ^ 3 = 1 := by
        rw [← (show Perm.IsThreeCycle σ from hσ).orderOf]
        exact pow_orderOf_eq_one σ
      refine Subgroup.mem_normalizer_fintype fun n hn => hN _ ?_ ?_ ?_ n hn
      · rw [Perm.sign_ofSubtype]
        exact (show Perm.IsThreeCycle σ from hσ).sign
      · intro t ht
        exact ofSubtype_mul_comm σ fun y hy => (hmemF y).mp hy t ht
      · rw [← map_pow, hσ3, map_one]
    exact hH hg
  set ι : alternatingGroup F →* Perm (Fin 9) := Perm.ofSubtype.comp (alternatingGroup F).subtype
    with hι
  have hιinj : Function.Injective ι :=
    Perm.ofSubtype_injective.comp (alternatingGroup F).subtype_injective
  have hNn : (W.comap ι).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hnorm g g.2) (ι n)).mp hn⟩
  have hNbot := eq_bot_of_isPGroup_two_of_normal hF35 (W.comap ι) hNn
    (hW2.comap_of_injective ι hιinj)
  set c := b * w * b⁻¹ * w⁻¹ with hc
  have hcW : c ∈ W := W.mul_mem (hN b hbs hbT hb3 w hw) (W.inv_mem hw)
  have hcF : ∀ y, y ∉ F → c y = y := by
    intro y hy
    have hw' : w⁻¹ y ∉ F := fun h => hy (by
      have := hpres w (hWT w hw) _ h
      rwa [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply] at this)
    have h1 : b⁻¹ (w⁻¹ y) = w⁻¹ y := by
      rw [Perm.inv_eq_iff_eq]
      exact (hbF _ hw').symm
    rw [hc, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, h1, ← Perm.mul_apply w,
      mul_inv_cancel, Perm.one_apply, hbF y hy]
  have h₁ : ∀ y, c y ∈ F ↔ y ∈ F := by
    intro y
    by_cases hy : y ∈ F
    · exact ⟨fun _ => hy, fun _ => hpres c (hWT c hcW) y hy⟩
    · rw [hcF y hy]
  have hc'c : Perm.ofSubtype (c.subtypePerm h₁) = c :=
    Perm.ofSubtype_subtypePerm h₁ fun y hy => by
      by_contra h
      exact hy (hcF y h)
  have hsign : Perm.sign (c.subtypePerm h₁) = 1 := by
    rw [← Perm.sign_ofSubtype, hc'c, hc, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (Perm.sign b) (Perm.sign w), mul_inv_cancel_right, mul_inv_cancel]
  have hmem : (⟨c.subtypePerm h₁, Perm.mem_alternatingGroup.mpr hsign⟩ : alternatingGroup F) ∈
      W.comap ι := by
    rw [Subgroup.mem_comap]
    change Perm.ofSubtype (c.subtypePerm h₁) ∈ W
    rw [hc'c]
    exact hcW
  rw [hNbot, Subgroup.mem_bot] at hmem
  have hc1 : c = 1 := by
    rw [← hc'c]
    have : c.subtypePerm h₁ = 1 := congrArg Subtype.val hmem
    rw [this, map_one]
  rw [hc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1
  exact hc1

end Item211LieProof

open Item211LieProof
open CFSG.Assembly (IsElemAbelian)

theorem le_centralizer_of_fourGroup_alternating (D T W : Subgroup (alternatingGroup (Fin 9)))
    (hD : IsElemAbelian 3 D) (hT : IsElemAbelian 2 T) (hT4 : Nat.card T = 4)
    (hDT : D ≤ Subgroup.normalizer (T : Set (alternatingGroup (Fin 9)))) (hTD : ⁅T, D⁆ = T)
    (hW2 : IsPGroup 2 W) (hWT : W ≤ Subgroup.centralizer (T : Set (alternatingGroup (Fin 9))))
    (hWN : ∀ g ∈ Subgroup.centralizer (T : Set (alternatingGroup (Fin 9))), g ^ 3 = 1 →
      g ∈ Subgroup.normalizer (W : Set (alternatingGroup (Fin 9)))) :
    D ⊓ Subgroup.centralizer (T : Set (alternatingGroup (Fin 9))) ≤
      Subgroup.centralizer (W : Set (alternatingGroup (Fin 9))) := by
  set ι := (alternatingGroup (Fin 9)).subtype with hι
  have hιi : Function.Injective ι := (alternatingGroup (Fin 9)).subtype_injective
  obtain ⟨t₁, ht₁, d₁, hd₁, hdt⟩ : ∃ t ∈ T, ∃ d ∈ D, d * t ≠ t * d := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hle : T ≤ Subgroup.centralizer (D : Set (alternatingGroup (Fin 9))) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hcon t ht d hd
    have hbot := (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hle
    rw [hTD] at hbot
    rw [hbot, Subgroup.card_bot] at hT4
    omega
  intro b hb
  obtain ⟨hbD, hbC⟩ := Subgroup.mem_inf.mp hb
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hmemT : ∀ t ∈ T.map ι, ∃ t₀ ∈ T, ι t₀ = t := fun t ht => by
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    exact ⟨t₀, ht₀, rfl⟩
  have hcore := comm_of_fourGroup (T := T.map ι) (W := W.map ι) (d := ι d₁) (b := ι b)
    (fun t ht t' ht' => by
      obtain ⟨t₀, ht₀, rfl⟩ := hmemT t ht
      obtain ⟨t₀', ht₀', rfl⟩ := hmemT t' ht'
      rw [← map_mul, ← map_mul]
      exact congrArg ι (congrArg Subtype.val (hT.1.is_comm.comm ⟨t₀, ht₀⟩ ⟨t₀', ht₀'⟩)))
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := hmemT t ht
      rw [← map_pow, hT.2 t₀ ht₀, map_one])
    (by rw [Subgroup.card_map_of_injective hιi, hT4])
    (by rw [← map_pow, hD.2 d₁ hd₁, map_one]) (by rw [← map_pow, hD.2 b hbD, map_one])
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := hmemT t ht
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem ι ((Subgroup.mem_normalizer_iff.mp (hDT hd₁) t₀).mp ht₀))
    ⟨ι t₁, Subgroup.mem_map_of_mem ι ht₁, fun h => hdt (hιi (by rw [map_mul, map_mul, h]))⟩
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := hmemT t ht
      rw [← map_mul, ← map_mul]
      exact congrArg ι (Subgroup.mem_centralizer_iff.mp hbC t₀ ht₀).symm)
    (Equiv.Perm.mem_alternatingGroup.mp b.2) (hW2.map ι)
    (fun w' hw' t ht => by
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw'
      obtain ⟨t₀, ht₀, rfl⟩ := hmemT t ht
      rw [← map_mul, ← map_mul]
      exact congrArg ι (Subgroup.mem_centralizer_iff.mp (hWT hw₀) t₀ ht₀).symm)
    (fun g hgs hgT hg3 w' hw' => by
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw'
      set g₀ : alternatingGroup (Fin 9) := ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hgs⟩
      have hg₀C : g₀ ∈ Subgroup.centralizer (T : Set (alternatingGroup (Fin 9))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        apply hιi
        rw [map_mul, map_mul]
        exact (hgT (ι t) (Subgroup.mem_map_of_mem ι ht)).symm
      have hg₀3 : g₀ ^ 3 = 1 := hιi (by rw [map_pow, map_one]; exact hg3)
      have h1 := (Subgroup.mem_normalizer_iff.mp (hWN g₀ hg₀C hg₀3) w₀).mp hw₀
      have h2 := Subgroup.mem_map_of_mem ι h1
      rwa [map_mul, map_mul, map_inv] at h2)
    (ι w) (Subgroup.mem_map_of_mem ι hw)
  exact (hιi (by rw [map_mul, map_mul]; exact hcore)).symm

end CFSG.RankThree.PartTwo.Sec21
