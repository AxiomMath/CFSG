module

public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem apply_apply_of_sq {t : MulAut V} (ht2 : t ^ 2 = 1) (w : V) : t (t w) = w := by
  have := congrArg (fun g : MulAut V => g w) ht2
  simpa [pow_two, MulAut.mul_apply] using this

omit [Finite V] in
theorem exists_fixed_of_invariant (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {t : MulAut V}
    (ht2 : t ^ 2 = 1) (hW : ∀ w ∈ W, t w ∈ W) (hne : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 ∧ t w = w := by
  obtain ⟨c, hc⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hcW : (c : V) ∈ W := c.2
  have hc1 : (c : V) ≠ 1 := fun h => hc (Subtype.ext h)
  by_cases hu : (c : V) * t (c : V) = 1
  · refine ⟨c, hcW, hc1, ?_⟩
    have h1 : t (c : V) = (c : V)⁻¹ := eq_inv_of_mul_eq_one_right hu
    rw [h1, inv_eq_self_of_sq_eq_one hV]
  · refine ⟨(c : V) * t (c : V), W.mul_mem hcW (hW _ hcW), hu, ?_⟩
    rw [map_mul, apply_apply_of_sq ht2, mul_comm]

omit [Finite V] in
theorem three_le_card_of_free {W : Subgroup V} {x : MulAut V} (hW : ∀ w ∈ W, x w ∈ W)
    (hfree : ∀ w ∈ W, x w = w → w = 1) (hne : W ≠ ⊥) [Finite V] : 2 < Nat.card W := by
  classical
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨c, hc⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hcW : (c : V) ∈ W := c.2
  have hc1 : (c : V) ≠ 1 := fun h => hc (Subtype.ext h)
  have hxc1 : x (c : V) ≠ 1 := by
    intro h
    exact hc1 (x.injective (by rw [h, map_one]))
  have hxcc : x (c : V) ≠ (c : V) := fun h => hc1 (hfree _ hcW h)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.two_lt_card_iff]
  refine ⟨1, c, ⟨x (c : V), hW _ hcW⟩, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _,
    ?_, ?_, ?_⟩
  · intro h; exact hc1 (congrArg Subtype.val h).symm
  · intro h; exact hxc1 (congrArg Subtype.val h).symm
  · intro h; exact hxcc (congrArg Subtype.val h).symm

theorem two_le_rk_of_free (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {x : MulAut V}
    (hW : ∀ w ∈ W, x w ∈ W) (hfree : ∀ w ∈ W, x w = w → w = 1) (hne : W ≠ ⊥) : 2 ≤ rk W := by
  by_contra h
  have h3 := three_le_card_of_free hW hfree hne
  rw [card_eq_two_pow hV W] at h3
  have : 2 ^ rk W ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem even_rk_of_free (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hY : Nat.card Y = 3) {F : Subgroup V} (hF : ∀ g ∈ Y, ∀ f ∈ F, g f ∈ F)
    (hfix : F ⊓ fixV Y = ⊥) : Even (rk F) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := prime_dvd_card_sub_one hY hF hfix
  rw [card_eq_two_pow hV F] at h
  exact even_of_three_dvd_two_pow_sub_one h

omit [Finite V] in
theorem mem_stabSub_of_zpowers {g : MulAut V} {W : Subgroup V}
    (hW : ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ W, x w ∈ W) : g ∈ stabSub W := by
  intro u
  constructor
  · intro h
    have := hW g⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) (g u) h
    simpa using this
  · exact hW g (Subgroup.mem_zpowers g) u

theorem rk_eq_two_mul_sub (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {t x : MulAut V}
    (ht2 : t ^ 2 = 1) (hinv : t * x * t⁻¹ = x⁻¹)
    (hWt : ∀ g ∈ Subgroup.zpowers t, ∀ w ∈ W, g w ∈ W)
    (hWx : ∀ g ∈ Subgroup.zpowers x, ∀ w ∈ W, g w ∈ W)
    (hfix : W ⊓ fixV (Subgroup.zpowers x) = ⊥) :
    rk W = 2 * rk (commSub W (Subgroup.zpowers t)) := by
  have hts : t ∈ stabSub W := mem_stabSub_of_zpowers hWt
  have hxs : x ∈ stabSub W := mem_stabSub_of_zpowers hWx
  have hVW : ∀ w : W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  set t' := resHom W ⟨t, hts⟩ with ht'
  set x' := resHom W ⟨x, hxs⟩ with hx'
  have ht2' : t' ^ 2 = 1 := by
    rw [ht', ← map_pow]
    have : (⟨t, hts⟩ : stabSub W) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  have hxt' : t' * x' * t'⁻¹ = x'⁻¹ := by
    rw [ht', hx', ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hinv)
  have hfix' : fixV (Subgroup.zpowers x') = ⊥ := by
    have h0 : rk (fixV (Subgroup.zpowers x')) = 0 := by
      rw [hx', rk_fixV_resHom hxs, hfix, rk_bot]
    exact (rk_eq_zero_iff hVW).mp h0
  have := rk_eq_two_mul_of_inverts hVW hfix' ht2' hxt'
  rwa [ht', rk_commV_resHom hts hWt] at this

theorem commSub_fixV_eq (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    (hQ : Odd (Nat.card Q)) {t : MulAut V} (hcomm : ∀ q ∈ Q, q * t = t * q) :
    commSub (fixV (Subgroup.zpowers t)) Q = commV Q ⊓ fixV (Subgroup.zpowers t) := by
  have hinv : ∀ g ∈ Q, ∀ w ∈ fixV (Subgroup.zpowers t), g w ∈ fixV (Subgroup.zpowers t) := by
    intro g hg w hw
    rw [mem_fixV_zpowers_iff] at hw ⊢
    have h1 : t (g w) = g (t w) := by
      calc t (g w) = (t * g) w := rfl
        _ = (g * t) w := by rw [hcomm g hg]
        _ = g (t w) := rfl
    rw [h1, hw]
  apply le_antisymm
  · refine le_inf ?_ (commSub_le_of_invariant hinv)
    rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  · intro w ⟨hw1, hw2⟩
    obtain ⟨hsup, -⟩ := coprime_decomp hQ hV hinv
    have hw : w ∈ commSub (fixV (Subgroup.zpowers t)) Q ⊔
        (fixV (Subgroup.zpowers t) ⊓ fixV Q) := by
      rw [hsup]; exact hw2
    obtain ⟨c, hc, f, hf, rfl⟩ := Subgroup.mem_sup.mp hw
    have hdisj := (coprime_decomp hQ hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)).2
    rw [← commV_eq_commSub, top_inf_eq] at hdisj
    have hcV : c ∈ commV Q := by
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl hc
    have hfV : f ∈ commV Q ⊓ fixV Q := by
      refine ⟨?_, hf.2⟩
      have : f = c⁻¹ * (c * f) := by group
      rw [this]
      exact (commV Q).mul_mem ((commV Q).inv_mem hcV) hw1
    rw [hdisj, Subgroup.mem_bot] at hfV
    rw [hfV, mul_one]
    exact hc

omit [Finite V] in
theorem inf_fixV_isDirectSum {A : Subgroup (MulAut V)} {W W₁ W₂ : Subgroup V}
    (hd : IsDirectSum W W₁ W₂) (h₁ : ∀ g ∈ A, ∀ w ∈ W₁, g w ∈ W₁)
    (h₂ : ∀ g ∈ A, ∀ w ∈ W₂, g w ∈ W₂) :
    IsDirectSum (W ⊓ fixV A) (W₁ ⊓ fixV A) (W₂ ⊓ fixV A) := by
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · exact inf_le_inf (hd.1 ▸ le_sup_left) le_rfl
      · exact inf_le_inf (hd.1 ▸ le_sup_right) le_rfl
    · rintro w ⟨hwW, hwF⟩
      have hw : w ∈ W₁ ⊔ W₂ := by rw [hd.1]; exact hwW
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hw
      have key : ∀ g ∈ A, g w₁ = w₁ ∧ g w₂ = w₂ := by
        intro g hg
        have h := hwF g hg
        rw [map_mul] at h
        have e : g w₁ * w₁⁻¹ = (g w₂ * w₂⁻¹)⁻¹ := by
          have this : g w₁ * g w₂ = w₁ * w₂ := h
          apply eq_inv_of_mul_eq_one_left
          calc (g w₁ * w₁⁻¹) * (g w₂ * w₂⁻¹) = (g w₁ * g w₂) * (w₁⁻¹ * w₂⁻¹) :=
                mul_mul_mul_comm _ _ _ _
            _ = (w₁ * w₂) * (w₁⁻¹ * w₂⁻¹) := by rw [this]
            _ = 1 := by rw [mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel, mul_one]
        have hmem : g w₁ * w₁⁻¹ ∈ W₁ ⊓ W₂ := by
          refine ⟨W₁.mul_mem (h₁ g hg w₁ hw₁) (W₁.inv_mem hw₁), ?_⟩
          rw [e]
          exact W₂.inv_mem (W₂.mul_mem (h₂ g hg w₂ hw₂) (W₂.inv_mem hw₂))
        rw [hd.2, Subgroup.mem_bot, mul_inv_eq_one] at hmem
        refine ⟨hmem, ?_⟩
        have h' : g w₁ * g w₂ = w₁ * w₂ := h
        rw [hmem] at h'
        exact mul_left_cancel h'
      exact Subgroup.mul_mem_sup ⟨hw₁, fun g hg => (key g hg).1⟩
        ⟨hw₂, fun g hg => (key g hg).2⟩
  · refine le_bot_iff.mp ?_
    calc (W₁ ⊓ fixV A) ⊓ (W₂ ⊓ fixV A) ≤ W₁ ⊓ W₂ := inf_le_inf inf_le_left inf_le_left
      _ = ⊥ := hd.2

theorem rk_inf_fixV_add {A : Subgroup (MulAut V)} {W W₁ W₂ : Subgroup V}
    (hd : IsDirectSum W W₁ W₂) (h₁ : ∀ g ∈ A, ∀ w ∈ W₁, g w ∈ W₁)
    (h₂ : ∀ g ∈ A, ∀ w ∈ W₂, g w ∈ W₂) :
    rk (W ⊓ fixV A : Subgroup V) = rk (W₁ ⊓ fixV A : Subgroup V) + rk (W₂ ⊓ fixV A : Subgroup V) :=
  rk_eq_add_of_isDirectSum (inf_fixV_isDirectSum hd h₁ h₂)

@[expose] noncomputable def kap (A : Subgroup (MulAut V)) (W : Subgroup V) : ℕ :=
  rk W - rk (W ⊓ fixV A : Subgroup V)

theorem rk_inf_fixV_le (A : Subgroup (MulAut V)) (W : Subgroup V) :
    rk (W ⊓ fixV A : Subgroup V) ≤ rk W :=
  rk_mono inf_le_left

theorem kap_add {A : Subgroup (MulAut V)} {W W₁ W₂ : Subgroup V}
    (hd : IsDirectSum W W₁ W₂) (h₁ : ∀ g ∈ A, ∀ w ∈ W₁, g w ∈ W₁)
    (h₂ : ∀ g ∈ A, ∀ w ∈ W₂, g w ∈ W₂) : kap A W = kap A W₁ + kap A W₂ := by
  have e1 := rk_eq_add_of_isDirectSum hd
  have e2 := rk_inf_fixV_add hd h₁ h₂
  have l1 := rk_inf_fixV_le A W₁
  have l2 := rk_inf_fixV_le A W₂
  unfold kap
  omega

end CFSG.Quasithin
