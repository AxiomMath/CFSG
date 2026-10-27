module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Disp

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1

section HeModule

variable {W : Type} [CommGroup W] [Finite W]

theorem isSimpleGroup_carrier_he :
    IsSimpleGroup (NativeSporadic.Carrier .He) :=
  (CFSG.Sporadic.He.fam_he_simplicity).2.2

theorem finite_carrier_he :
    Finite (NativeSporadic.Carrier .He) :=
  (CFSG.Sporadic.He.fam_he_simplicity).1

theorem card_carrier_he :
    Nat.card (NativeSporadic.Carrier .He) = 4030387200 :=
  (CFSG.Sporadic.He.fam_he_order).1

theorem center_carrier_he_eq_bot :
    Subgroup.center (NativeSporadic.Carrier .He) = ⊥ := by
  have hs := isSimpleGroup_carrier_he
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (NativeSporadic.Carrier .He)) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : NativeSporadic.Carrier .He, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center (NativeSporadic.Carrier .He) := by
        rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    let _ : CommGroup (NativeSporadic.Carrier .He) :=
      { (inferInstance : Group (NativeSporadic.Carrier .He)) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := NativeSporadic.Carrier .He)
    rw [card_carrier_he] at hp
    exact absurd hp (by norm_num)

theorem two_pow_eight_le_index_fixV_of_he
    (hW : ∀ w : W, w * w = 1) {X K : Subgroup (MulAut W)} (hKX : K ≤ X)
    (hn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (e : ↥K ≃* NativeSporadic.Carrier .He)
    {t : MulAut W} (htX : t ∈ X) (ht2 : t * t = 1) (htK : ∃ k ∈ K, t * k * t⁻¹ ≠ k) :
    2 ^ 8 ≤ (fixV (Subgroup.zpowers t)).index ^ 3 := by
  classical
  have hXnorm : X ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hn x hx k hk, fun hk => ?_⟩
    have := hn x⁻¹ (X.inv_mem hx) _ hk
    simpa [mul_assoc] using this
  let Θ : ↥X →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hXnorm)
  have hΘ : ∀ (x : ↥X) (k : ↥K),
      ((Θ x k : ↥K) : MulAut W) = (x : MulAut W) * k * (x : MulAut W)⁻¹ :=
    fun x k => Subgroup.normalizerMonoidHom_apply_apply_coe K (Subgroup.inclusion hXnorm x) k
  let Φ : ↥X →* MulAut (NativeSporadic.Carrier .He) := (MulAut.congr e).toMonoidHom.comp Θ
  have hΦ : ∀ (x : ↥X) (h : NativeSporadic.Carrier .He), Φ x h = e (Θ x (e.symm h)) :=
    fun x h => rfl
  have hΦK : ∀ κ : ↥K, Φ ⟨(κ : MulAut W), hKX κ.2⟩ = MulAut.conj (e κ) := by
    intro κ
    ext h
    rw [hΦ, MulAut.conj_apply]
    have : Θ ⟨(κ : MulAut W), hKX κ.2⟩ (e.symm h) = κ * e.symm h * κ⁻¹ :=
      Subtype.ext (hΘ _ _)
    rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  set tX : ↥X := ⟨t, htX⟩ with htXdef
  have hψ2 : Φ tX * Φ tX = 1 := by
    rw [← map_mul]
    have : tX * tX = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hψ1 : Φ tX ≠ 1 := by
    intro h1
    obtain ⟨k, hk, hne⟩ := htK
    apply hne
    have h2 := DFunLike.congr_fun h1 (e ⟨k, hk⟩)
    rw [hΦ, MulEquiv.symm_apply_apply] at h2
    have h3 : Θ tX ⟨k, hk⟩ = ⟨k, hk⟩ := e.injective (by simpa using h2)
    have h4 := congrArg (fun y : ↥K => (y : MulAut W)) h3
    simpa [hΘ] using h4
  obtain ⟨cs, hlen, hcsin, hgen⟩ := he_gen (Φ tX) hψ2 hψ1
  have hcen := center_carrier_he_eq_bot
  have hfact : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hfin := finite_carrier_he
  obtain ⟨z, hz17⟩ := exists_prime_orderOf_dvd_card' (G := NativeSporadic.Carrier .He) 17
    (by rw [card_carrier_he]; norm_num)
  have hx17 : orderOf (MulAut.conj z : MulAut (NativeSporadic.Carrier .He)) = 17 := by
    have hdvd : orderOf (MulAut.conj z : MulAut (NativeSporadic.Carrier .He)) ∣ 17 := by
      have := orderOf_map_dvd (MulAut.conj : NativeSporadic.Carrier .He →* MulAut _) z
      rwa [hz17] at this
    have hne : (MulAut.conj z : MulAut (NativeSporadic.Carrier .He)) ≠ 1 := by
      intro h1
      have hz : z ∈ Subgroup.center (NativeSporadic.Carrier .He) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := DFunLike.congr_fun h1 g
        rw [MulAut.conj_apply] at this
        simp only [MulAut.one_apply] at this
        exact (mul_inv_eq_iff_eq_mul.mp this).symm
      rw [hcen, Subgroup.mem_bot] at hz
      have : orderOf z = 1 := by rw [hz]; exact orderOf_one
      rw [hz17] at this
      omega
    rcases (Nat.dvd_prime hfact.out).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have hcs : ∀ c ∈ cs, c ∈ Φ.range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsin c hc
    exact ⟨⟨((e.symm s : ↥K) : MulAut W), hKX (e.symm s).2⟩, by rw [hΦK, MulEquiv.apply_symm_apply]⟩
  have hmem : (MulAut.conj z : MulAut (NativeSporadic.Carrier .He)) ∈ Subgroup.closure
      {z | ∃ c ∈ cs, ∃ b : ↥X, (b : MulAut W) ∈ Subgroup.zpowers t ∧ z = c * Φ b * c⁻¹} := by
    refine Subgroup.closure_mono ?_ (hgen z)
    rintro _ ⟨c, hc, t', ht', rfl⟩
    rw [Set.mem_singleton_iff] at ht'
    subst ht'
    exact ⟨c, hc, tX, Subgroup.mem_zpowers t, rfl⟩
  have key := two_pow_le_index_pow_of_mem hW Φ (B := Subgroup.zpowers t) cs hcs (p := 17)
    (by norm_num) hx17 hmem
  rw [orderOf_two_zmod_17, hlen] at key
  exact key

end HeModule

end CFSG.Quasithin
