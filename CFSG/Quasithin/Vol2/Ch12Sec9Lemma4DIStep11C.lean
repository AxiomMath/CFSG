module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep11B
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep11Core

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem DIEnv.y0_mem_K0 (E : DIEnv T L V V₁ V₂ K₁ g D) (h1289 : Lemma12_8_9W) :
    E.y₀ ∈ k0Sub K₁ D (D.π E.a) := by
  obtain ⟨hyK, -, -⟩ := E.y0_norm h1289
  have hyU := E.hK₁U hyK
  refine mem_k0Sub.2 ⟨hyK, hyU, ?_⟩
  have haU : E.a ∈ u128 V V₁ := le_conjClosure V _ (E.hs.v2.1 E.haV₂)
  have hca : E.y₀ * E.a * E.y₀⁻¹ = E.a := by
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 E.hy₀).2 E.a E.haV₂
    rw [← hc]
    group
  rw [D.ρ_π ⟨E.y₀, hyU⟩ E.a haU, hca]

theorem DIEnv.ccF_y0_pow (E : DIEnv T L V V₁ V₂ K₁ g D) (m : ℕ) : ccF E.a (E.y₀ ^ m) = 1 := by
  have hc : E.y₀ ^ m * E.a = E.a * E.y₀ ^ m := by
    have hcomm : Commute E.y₀ E.a := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 E.hy₀).2
      E.a E.haV₂).symm
    exact (hcomm.pow_left m).eq
  unfold ccF
  calc E.y₀ ^ m * E.a * (E.y₀ ^ m)⁻¹ * E.a⁻¹ = E.a * E.y₀ ^ m * (E.y₀ ^ m)⁻¹ * E.a⁻¹ := by
        rw [hc]
    _ = 1 := by group

theorem DIEnv.conj_DIV1 (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    {k : G} (hk : k ∈ k0Sub K₁ D (D.π E.a)) {z : G}
    (hz : z ∈ (E.I ⊓ wcSub T L V V₁) ⊔ V₁) : k * z * k⁻¹ ∈ (E.I ⊓ wcSub T L V V₁) ⊔ V₁ := by
  have hdc : ∀ d ∈ E.I ⊓ wcSub T L V V₁, ∀ v ∈ V₁, d * v = v * d := by
    intro d hd v hv
    have hdZ : d ∈ zU128 V V₁ := E.hIZ (Subgroup.mem_inf.1 hd).1
    have hvZ : v ∈ zU128 V V₁ := V₁_le_zU h1222 h12213 E.hs hv
    exact (mem_centerOf_iff'.1 hvZ).2 d (zU_le_u128 hdZ)
  obtain ⟨d, hd, v, hv, rfl⟩ := mem_sup_decomp hdc z hz
  obtain ⟨hkK, hkN, hρ⟩ := mem_k0Sub.1 hk
  have hvv : k * v * k⁻¹ = v := conj_fix_V1 (card_V₁ E.hs) (E.hK₁H hkK) hv
  have e : k * (d * v) * k⁻¹ = (k * d * k⁻¹) * (k * v * k⁻¹) := by group
  rw [e, hvv]
  have hNk := E.K0_normalizes_DI h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hkK hkN hρ
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hNk d).1 hd))
    (Subgroup.mem_sup_right hv)


theorem DIEnv.exists_pow_y0 (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp) {h : G}
    (hh : h ∈ k0Sub K₁ D (D.π E.a)) (k : ℕ) (hord : orderOf h = 3 ^ k) :
    ∃ m : ℕ, ∃ h' : G, ∃ hh' : h' ∈ k0Sub K₁ D (D.π E.a),
      E.sigma ⟨h', hh'⟩ = 1 ∧ h = E.y₀ ^ m * h' := by
  classical
  have hy0 : E.y₀ ∈ k0Sub K₁ D (D.π E.a) := E.y0_mem_K0 h1289
  have hfr : Module.finrank (ZMod 2) (Additive ↥E.I ⧸ E.fl) = 2 := by
    have := Submodule.finrank_quotient_add_finrank E.fl
    rw [E.hM, E.hℓ] at this
    omega
  have hy3 : E.y₀ ^ 3 = 1 := by
    rw [← E.hy₀3]
    exact pow_orderOf_eq_one _
  have hτ3 : E.sigma ⟨E.y₀, hy0⟩ ^ 3 = 1 := E.sigma_pow_three hy0 1 (by rw [E.hy₀3]; norm_num)
  have hτ1 : E.sigma ⟨E.y₀, hy0⟩ ≠ 1 :=
    E.sigma_y0_ne_one h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hy0
  have hσ3 : E.sigma ⟨h, hh⟩ ^ 3 = 1 := E.sigma_pow_three hh k hord
  rcases eq_one_or_eq_of_order_three hfr _ _ hσ3 hτ3 hτ1 with h1 | h1 | h1
  · exact ⟨0, h, hh, h1, by simp⟩
  · have hh' : E.y₀ ^ 2 * h ∈ k0Sub K₁ D (D.π E.a) :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ hy0 2) hh
    refine ⟨1, E.y₀ ^ 2 * h, hh', ?_, ?_⟩
    · have e : (⟨E.y₀ ^ 2 * h, hh'⟩ : ↥(k0Sub K₁ D (D.π E.a))) =
          ⟨E.y₀, hy0⟩ ^ 2 * ⟨h, hh⟩ := Subtype.ext (by simp [pow_two, mul_assoc])
      rw [e, map_mul, map_pow, h1, ← pow_succ]
      exact hτ3
    · calc h = E.y₀ ^ 3 * h := by rw [hy3, one_mul]
        _ = E.y₀ ^ 1 * (E.y₀ ^ 2 * h) := by rw [pow_one, ← mul_assoc, ← pow_succ']
  · have hh' : E.y₀ * h ∈ k0Sub K₁ D (D.π E.a) := Subgroup.mul_mem _ hy0 hh
    refine ⟨2, E.y₀ * h, hh', ?_, ?_⟩
    · have e : (⟨E.y₀ * h, hh'⟩ : ↥(k0Sub K₁ D (D.π E.a))) = ⟨E.y₀, hy0⟩ * ⟨h, hh⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul, h1]
      have h3 : E.sigma ⟨E.y₀, hy0⟩ * (E.sigma ⟨E.y₀, hy0⟩ * E.sigma ⟨E.y₀, hy0⟩) =
          E.sigma ⟨E.y₀, hy0⟩ ^ 3 := by
        rw [pow_succ, pow_two, mul_assoc]
      rw [h3, hτ3]
    · calc h = E.y₀ ^ 3 * h := by rw [hy3, one_mul]
        _ = E.y₀ ^ 2 * (E.y₀ * h) := by rw [← mul_assoc, ← pow_succ]


theorem DIEnv.leaf_ccF_DI (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (h12813f : Lemma12_8_13_five) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    (hK₁C : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hG5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (hK₁N : ∀ h ∈ Subgroup.normalizer (V₁ : Set G), ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁)
    {h : G} (hh : h ∈ k0Sub K₁ D (D.π E.a)) (k : ℕ) (hord : orderOf h = 3 ^ k) :
    ccF E.a h ∈ E.I ⊓ wcSub T L V V₁ := by
  classical
  obtain ⟨m, h', hh', hσ', hhe⟩ :=
    E.exists_pow_y0 h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hh k hord
  have hN0 : h' ∈ E.N0G := E.mem_N0G.2 ⟨hh', hσ'⟩
  have hc' : ccF E.a h' ∈ (E.I ⊓ wcSub T L V V₁) ⊔ V₁ :=
    E.N0_ccF_mem h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 hpt hK₁C hK4 hG5 hK₁N hN0
  have hy0m : E.y₀ ^ m ∈ k0Sub K₁ D (D.π E.a) := Subgroup.pow_mem _ (E.y0_mem_K0 h1289) m
  have hm := ccF_mul E.a (E.y₀ ^ m) h'
  rw [E.ccF_y0_pow m, mul_one] at hm
  have hcm : ccF E.a h = E.y₀ ^ m * ccF E.a h' * (E.y₀ ^ m)⁻¹ := by
    rw [hhe]
    exact hm
  have hcDI : ccF E.a h ∈ (E.I ⊓ wcSub T L V V₁) ⊔ V₁ := by
    rw [hcm]
    exact E.conj_DIV1 h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hy0m hc'
  have hodd : Odd (orderOf h) := by
    rw [hord]
    exact Odd.pow (by decide)
  have hcI : ccF E.a h ∈ E.I :=
    E.ccF_odd_mem_I h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 hpt hK₁C hK4 hG5 hh
      hodd
  have hdc : ∀ d ∈ E.I ⊓ wcSub T L V V₁, ∀ v ∈ V₁, d * v = v * d := by
    intro d hd v hv
    have hdZ : d ∈ zU128 V V₁ := E.hIZ (Subgroup.mem_inf.1 hd).1
    have hvZ : v ∈ zU128 V V₁ := V₁_le_zU h1222 h12213 E.hs hv
    exact (mem_centerOf_iff'.1 hvZ).2 d (zU_le_u128 hdZ)
  obtain ⟨d, hd, v, hv, hdv⟩ := mem_sup_decomp hdc _ hcDI
  have hvI : v ∈ E.I := by
    have e : v = d⁻¹ * ccF E.a h := by
      rw [hdv]
      group
    rw [e]
    exact E.I.mul_mem (E.I.inv_mem (Subgroup.mem_inf.1 hd).1) hcI
  have hvwc : v ∈ wcSub T L V V₁ := (le_sup_right : V₁ ≤ centerOf (i128 T L V V₁) ⊔ V₁) hv
  have hv1 : v = 1 := by
    have hmem : v ∈ E.I ⊓ wcSub T L V V₁ ⊓ V₁ :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hvI, hvwc⟩, hv⟩
    rw [E.DI_inf_V1] at hmem
    exact Subgroup.mem_bot.1 hmem
  rw [hdv, hv1, mul_one]
  exact hd

theorem DIEnv.V2_conj (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    {h : G} (hh : h ∈ k0Sub K₁ D (D.π E.a))
    (hcDI : ccF E.a h ∈ E.I ⊓ wcSub T L V V₁) :
    ∀ x ∈ V₂ ⊔ (E.I ⊓ wcSub T L V V₁), h * x * h⁻¹ ∈ V₂ ⊔ (E.I ⊓ wcSub T L V V₁) := by
  classical
  obtain ⟨hkK, hkN, hρ⟩ := mem_k0Sub.1 hh
  have hVU : ∀ v ∈ V₂, v ∈ u128 V V₁ := fun v hv => le_conjClosure V _ (E.hs.v2.1 hv)
  have hdc : ∀ v ∈ V₂, ∀ d ∈ E.I ⊓ wcSub T L V V₁, v * d = d * v := by
    intro v hv d hd
    have hdZ : d ∈ zU128 V V₁ := E.hIZ (Subgroup.mem_inf.1 hd).1
    exact (mem_centerOf_iff'.1 hdZ).2 v (hVU v hv)
  have hA : ∀ v ∈ V₂, h * v * h⁻¹ ∈ V₂ ⊔ (E.I ⊓ wcSub T L V V₁) := by
    intro v hv
    by_cases hv1 : v ∈ V₁
    · rw [conj_fix_V1 (card_V₁ E.hs) (E.hK₁H hkK) hv1]
      exact Subgroup.mem_sup_left hv
    · have hz : v * E.a⁻¹ ∈ V₁ := V2_coset E hv hv1
      have e1 : h * (v * E.a⁻¹) * h⁻¹ = v * E.a⁻¹ :=
        conj_fix_V1 (card_V₁ E.hs) (E.hK₁H hkK) hz
      have e2 : h * E.a * h⁻¹ = ccF E.a h * E.a := by
        unfold ccF
        group
      have e3 : h * v * h⁻¹ = (h * (v * E.a⁻¹) * h⁻¹) * (h * E.a * h⁻¹) := by group
      rw [e3, e1, e2, ← mul_assoc]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (E.hs.le hz))
        (Subgroup.mem_sup_right hcDI)) (Subgroup.mem_sup_left E.haV₂)
  intro x hx
  obtain ⟨v, hv, d, hd, rfl⟩ := mem_sup_decomp hdc x hx
  have e : h * (v * d) * h⁻¹ = (h * v * h⁻¹) * (h * d * h⁻¹) := by group
  rw [e]
  have hNk := E.K0_normalizes_DI h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hkK hkN hρ
  exact Subgroup.mul_mem _ (hA v hv)
    (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hNk d).1 hd))

theorem DIEnv.leaf_norm (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (h12813f : Lemma12_8_13_five) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    (hK₁C : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hG5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (hK₁N : ∀ h ∈ Subgroup.normalizer (V₁ : Set G), ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁)
    {h : G} (hh : h ∈ k0Sub K₁ D (D.π E.a)) (k : ℕ) (hord : orderOf h = 3 ^ k) :
    h ∈ Subgroup.normalizer ((E.I ⊓ wcSub T L V V₁ : Subgroup G) : Set G) ∧
      h ∈ Subgroup.normalizer ((V₂ ⊔ (E.I ⊓ wcSub T L V V₁) : Subgroup G) : Set G) := by
  obtain ⟨hkK, hkN, hρ⟩ := mem_k0Sub.1 hh
  refine ⟨E.K0_normalizes_DI h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hkK hkN hρ, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => E.V2_conj h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hh
      (E.leaf_ccF_DI h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 hpt hK₁C hK4 hG5 hK₁N hh k hord)
      x hx
  · intro hx
    have hh' : h⁻¹ ∈ k0Sub K₁ D (D.π E.a) := Subgroup.inv_mem _ hh
    have hord' : orderOf h⁻¹ = 3 ^ k := by rw [orderOf_inv, hord]
    have hc' := E.leaf_ccF_DI h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 hpt hK₁C hK4 hG5 hK₁N
      hh' k hord'
    have := E.V2_conj h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hh' hc' (h * x * h⁻¹) hx
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rw [e] at this
    exact this

end Env

end CFSG.Quasithin.H13.C1294
