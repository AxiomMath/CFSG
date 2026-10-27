module

public import CFSG.RankThree.GF2n.Stroth80.Sec34TailModule

public section

open scoped Pointwise

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

namespace TailFalse

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem bf_map_map (Bf : LinearMap.BilinForm K E) (Qf : E → K)
    (hQadd : ∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f) (h : E ≃ₗ[K] E)
    (hh : ∀ e, Qf (h e) = Qf e) (x y : E) : Bf (h x) (h y) = Bf x y := by
  have e1 := hQadd (h x) (h y)
  rw [← map_add, hh, hh, hh] at e1
  linear_combination hQadd x y - e1

theorem span_singleton_eq_of_eq_smul {x y : E} {c : K} (hx : x ≠ 0) (h : x = c • y) :
    Submodule.span K {x} = Submodule.span K {y} := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx (by rw [h, zero_smul])
  rw [h, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]

theorem smul_span_singleton (g : E ≃ₗ[K] E) (v : E) :
    g • Submodule.span K {v} = Submodule.span K {g v} := by
  rw [Submodule.pointwise_smul_def, Submodule.map_span, Set.image_singleton]
  rfl

theorem smul_eq_map (g : E ≃ₗ[K] E) (S : Submodule K E) :
    g • S = S.map (g : E →ₗ[K] E) := rfl

theorem eichler_fixed (Bf : LinearMap.BilinForm K E) (t : E ≃ₗ[K] E)
    (ht : ∀ x y, Bf (t x) (t y) = Bf x y) {b p : E} (htb : t b = b)
    (hb : b ∈ LinearMap.range ((t : E →ₗ[K] E) - 1)) (hpb : Bf p b ≠ 0) (hbp : Bf b p ≠ 0)
    (hp : t p ∈ Submodule.span K {p}) : False := by
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hp
  have h1 : μ = 1 := by
    have e := ht p b
    rw [← hμ, htb, map_smul, LinearMap.smul_apply, smul_eq_mul] at e
    exact mul_right_cancel₀ hpb (e.trans (one_mul _).symm)
  rw [h1, one_smul] at hμ
  obtain ⟨x, hx⟩ := hb
  have hx' : t x - x = b := by simpa using hx
  have e := ht x p
  rw [← hμ] at e
  exact hbp (by rw [← hx', LinearMap.map_sub₂, e, sub_self])

theorem eq_one_of_sq_eq_one [CharP K 2] {μ : K} (h : μ ^ 2 = 1) : μ = 1 := by
  have h2 : (μ + 1) ^ 2 = 0 := by
    linear_combination h + (μ + 1) * CharTwo.two_eq_zero (R := K)
  have h3 : μ + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  linear_combination h3 - CharTwo.two_eq_zero (R := K)

theorem ncard_le_of_ovoid [Finite K] [Module.Finite K E]
    (hdim : Module.finrank K E = 6) (Bf : LinearMap.BilinForm K E) (Qf : E → K)
    (hQsmul : ∀ (a : K) (e : E), Qf (a • e) = a ^ 2 * Qf e)
    (hQadd : ∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f) {b : E} (hbs : Qf b = 0)
    {U : Submodule K E} (hUs : ∀ u ∈ U, Qf u = 0) (hUdim : Module.finrank K U = 3)
    (hbU : b ∈ U) {S : Set E} (hS : ∀ p ∈ S, Qf p = 0 ∧ Bf p b = 1)
    (hSorth : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → Bf p p' ≠ 0) :
    S.ncard ≤ Nat.card K ^ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · simp
  obtain ⟨W, hW⟩ : ∃ W : Submodule K E, W = LinearMap.ker (LinearMap.flip Bf b) := ⟨_, rfl⟩
  have hmemW : ∀ e, e ∈ W ↔ Bf e b = 0 := fun e => by
    rw [hW, LinearMap.mem_ker, LinearMap.flip_apply]
  have hWdim : Module.finrank K W = 5 := by
    have hsurj : LinearMap.range (LinearMap.flip Bf b) = ⊤ := by
      refine LinearMap.range_eq_top.mpr fun a => ⟨a • c₀, ?_⟩
      rw [map_smul, LinearMap.flip_apply, (hS c₀ hc₀).2, smul_eq_mul, mul_one]
    have := LinearMap.finrank_range_add_finrank_ker (LinearMap.flip Bf b)
    rw [hsurj, ← hW, finrank_top, Module.finrank_self, hdim] at this
    omega
  have hUW : U ≤ W := fun u hu => by
    rw [hmemW]
    have e := hQadd u b
    rw [hUs _ (U.add_mem hu hbU), hUs u hu, hbs] at e
    linear_combination -e
  set U' : Submodule K W := U.comap W.subtype
  have hU'dim : Module.finrank K U' = 3 := by
    rw [(Submodule.comapSubtypeEquivOfLe hUW).finrank_eq, hUdim]
  have hQdim : Module.finrank K (W ⧸ U') = 2 := by
    have := Submodule.finrank_quotient_add_finrank U'
    omega
  have hcard : Nat.card (W ⧸ U') = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hQdim]
  haveI : Finite (W ⧸ U') := Module.finite_of_finite K
  have hmem : ∀ p ∈ S, p - c₀ ∈ W := fun p hp => by
    rw [hmemW, LinearMap.map_sub₂, (hS p hp).2, (hS c₀ hc₀).2, sub_self]
  let f : S → W ⧸ U' := fun p => Submodule.Quotient.mk ⟨p.1 - c₀, hmem p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    by_contra hne
    have hne' : p ≠ p' := fun e => hne (Subtype.ext e)
    have h2 := (Submodule.Quotient.eq U').mp h
    have hU : p - p' ∈ U := by
      have h3 : W.subtype (⟨p - c₀, hmem p hp⟩ - ⟨p' - c₀, hmem p' hp'⟩) ∈ U := h2
      simpa using h3
    have hneg : Qf (-p') = 0 := by
      rw [← neg_one_smul K p', hQsmul, (hS p' hp').1, mul_zero]
    have e := hQadd p (-p')
    rw [← sub_eq_add_neg, hUs _ hU, (hS p hp).1, hneg, map_neg] at e
    exact hSorth p hp p' hp' hne' (by linear_combination e)
  calc S.ncard = Nat.card S := (Nat.card_coe_set_eq S).symm
    _ ≤ Nat.card (W ⧸ U') := Nat.card_le_card_of_injective f hf
    _ = Nat.card K ^ 2 := hcard

theorem exists_normal_sl2 (hHKS : HKSStatement) {k : ℕ} (hk : 2 ≤ k)
    (E : Type) [AddCommGroup E] [Module (GaloisField 2 k) E] [Module.Finite (GaloisField 2 k) E]
    (hdim : Module.finrank (GaloisField 2 k) E = 6)
    (Bf : LinearMap.BilinForm (GaloisField 2 k) E) (Qf : E → GaloisField 2 k)
    (hQsmul : ∀ (a : GaloisField 2 k) (e : E), Qf (a • e) = a ^ 2 * Qf e)
    (hQadd : ∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f)
    (H : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hHQ : ∀ h ∈ H, ∀ e : E, Qf (h e) = Qf e)
    (b : E) (hbs : Qf b = 0)
    (U : Submodule (GaloisField 2 k) E) (hUs : ∀ u ∈ U, Qf u = 0)
    (hUdim : Module.finrank (GaloisField 2 k) U = 3) (hbU : b ∈ U)
    (Λ : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hΛH : Λ ≤ H)
    (hΛcard : Nat.card Λ = Nat.card (GaloisField 2 k) ^ 2)
    (hΛcomm : ∀ t ∈ Λ, ∀ t' ∈ Λ, t * t' = t' * t) (hΛsq : ∀ t ∈ Λ, t * t = 1)
    (hΛb : ∀ t ∈ Λ, t b = b)
    (hΛE : ∀ t ∈ Λ, t ≠ 1 →
      b ∈ LinearMap.range (((t : E ≃ₗ[GaloisField 2 k] E) : E →ₗ[GaloisField 2 k] E) - 1))
    (hΛnorm : ∀ h ∈ H, Submodule.map (h : E →ₗ[GaloisField 2 k] E)
        (Submodule.span (GaloisField 2 k) {b}) = Submodule.span (GaloisField 2 k) {b} →
      ∀ t ∈ Λ, h * t * h⁻¹ ∈ Λ)
    (hmoves : ∃ h ∈ H, Submodule.map (h : E →ₗ[GaloisField 2 k] E)
        (Submodule.span (GaloisField 2 k) {b}) ≠ Submodule.span (GaloisField 2 k) {b})
    (P : Set E) (hbP : b ∈ P) (hP0 : ∀ p ∈ P, p ≠ 0 ∧ Qf p = 0)
    (hPsmul : ∀ p ∈ P, ∀ c : GaloisField 2 k, c ≠ 0 → c • p ∈ P)
    (hPH : ∀ h ∈ H, ∀ p ∈ P, h p ∈ P)
    (hPorth : ∀ p ∈ P, ∀ p' ∈ P, (∀ c : GaloisField 2 k, p' ≠ c • p) → Bf p p' ≠ 0)
    (hPspan : Submodule.span (GaloisField 2 k) P = ⊤) :
    ∃ L : Subgroup (E ≃ₗ[GaloisField 2 k] E), L ≤ H ∧ (L.subgroupOf H).Normal ∧
      IsSimpleGroup L ∧
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * k))) ∧
      Submodule.span (GaloisField 2 k)
        (Set.range fun ℓ : L => ((ℓ : E ≃ₗ[GaloisField 2 k] E)) b) = ⊤ := by
  haveI : Finite E := Module.finite_of_finite (GaloisField 2 k)
  haveI : Finite (Submodule (GaloisField 2 k) E) :=
    Finite.of_injective (fun S : Submodule (GaloisField 2 k) E => (S : Set E))
      SetLike.coe_injective
  haveI : Finite (E ≃ₗ[GaloisField 2 k] E) :=
    Finite.of_injective (fun f : E ≃ₗ[GaloisField 2 k] E => (f : E → E)) DFunLike.coe_injective
  have hiso : ∀ h ∈ H, ∀ x y : E, Bf (h x) (h y) = Bf x y := fun h hh x y =>
    bf_map_map Bf Qf hQadd h (hHQ h hh) x y
  have hBne : ∀ x ∈ P, ∀ y ∈ P, Submodule.span (GaloisField 2 k) {x} ≠
      Submodule.span (GaloisField 2 k) {y} → Bf x y ≠ 0 := fun x hx y hy hxy =>
    hPorth x hx y hy fun c hc => hxy (span_singleton_eq_of_eq_smul (hP0 y hy).1 hc).symm
  set α₀ : Submodule (GaloisField 2 k) E := Submodule.span (GaloisField 2 k) {b} with hα₀
  have hOlines : ∀ S ∈ MulAction.orbit (↥H) α₀,
      ∃ p ∈ P, S = Submodule.span (GaloisField 2 k) {p} := by
    rintro S ⟨g, rfl⟩
    exact ⟨(g : E ≃ₗ[GaloisField 2 k] E) b, hPH _ g.2 b hbP, smul_span_singleton _ b⟩
  have hΛα : ∀ t ∈ Λ, t • α₀ = α₀ := fun t ht => by
    rw [hα₀, smul_span_singleton, hΛb t ht]
  have hsemi : ∀ t ∈ Λ, t ≠ 1 → ∀ S ∈ MulAction.orbit (↥H) α₀, S ≠ α₀ → t • S ≠ S := by
    intro t ht ht1 S hS hSα hfix
    obtain ⟨p, hp, rfl⟩ := hOlines S hS
    rw [smul_span_singleton] at hfix
    refine eichler_fixed Bf t (hiso t (hΛH ht)) (hΛb t ht) (hΛE t ht ht1)
      (hBne p hp b hbP hSα) (hBne b hbP p hp (Ne.symm hSα)) ?_
    rw [← hfix]
    exact Submodule.mem_span_singleton_self _
  set P₁ : Set E := {p | p ∈ P ∧ Bf p b = 1}
  have hnorm : ∀ p ∈ P, Submodule.span (GaloisField 2 k) {p} ≠ α₀ →
      Submodule.span (GaloisField 2 k) {p} ∈
        (fun p => Submodule.span (GaloisField 2 k) {p}) '' P₁ := by
    intro p hp hpα
    have hpb := hBne p hp b hbP hpα
    refine ⟨(Bf p b)⁻¹ • p, ⟨hPsmul p hp _ (inv_ne_zero hpb), ?_⟩, ?_⟩
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hpb]
    · exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hpb)) p
  have hT : ((fun p => Submodule.span (GaloisField 2 k) {p}) '' P₁).ncard ≤
      Nat.card (GaloisField 2 k) ^ 2 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    refine ncard_le_of_ovoid hdim Bf Qf hQsmul hQadd hbs hUs hUdim hbU ?_ ?_
    · rintro p ⟨hp, hpb⟩
      exact ⟨(hP0 p hp).2, hpb⟩
    · rintro p ⟨hp, hpb⟩ p' ⟨hp', hp'b⟩ hne
      refine hPorth p hp p' hp' fun c hc => hne ?_
      rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, hpb, mul_one] at hp'b
      rw [hc, hp'b, one_smul]
  have hOT : MulAction.orbit (↥H) α₀ \ {α₀} ⊆
      (fun p => Submodule.span (GaloisField 2 k) {p}) '' P₁ := by
    rintro S ⟨hS, hSα⟩
    obtain ⟨p, hp, rfl⟩ := hOlines S hS
    exact hnorm p hp hSα
  obtain ⟨R, hR⟩ : ∃ R : Subgroup ↥H, R = Λ.subgroupOf H := ⟨_, rfl⟩
  have hRcard : Nat.card R = Nat.card (GaloisField 2 k) ^ 2 := by
    rw [← hΛcard, hR]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛH).toEquiv
  have hRmem' : ∀ x : ↥H, x ∈ R → (x : E ≃ₗ[GaloisField 2 k] E) ∈ Λ := fun x hx => by
    rw [hR, Subgroup.mem_subgroupOf] at hx
    exact hx
  have hRmem : ∀ r : R, ((r : ↥H) : E ≃ₗ[GaloisField 2 k] E) ∈ Λ := fun r => hRmem' _ r.2
  have hRne : ∀ r : R, r ≠ 1 → ((r : ↥H) : E ≃ₗ[GaloisField 2 k] E) ≠ 1 :=
    fun r hr h => hr (Subtype.ext (Subtype.ext h))
  have hmaps : ∀ β ∈ MulAction.orbit (↥H) α₀ \ {α₀}, ∀ r : R,
      (r : ↥H) • β ∈ MulAction.orbit (↥H) α₀ \ {α₀} := by
    rintro β ⟨hβ, hβα⟩ r
    refine ⟨MulAction.mem_orbit_of_mem_orbit _ hβ, fun h => hβα ?_⟩
    have h' : (r : ↥H) • β = (r : ↥H) • α₀ := by
      rw [Set.mem_singleton_iff.mp h]
      exact (hΛα _ (hRmem r)).symm
    exact smul_left_cancel _ h'
  have hinj : ∀ β ∈ MulAction.orbit (↥H) α₀ \ {α₀}, ∀ r r' : R,
      (r : ↥H) • β = (r' : ↥H) • β → r = r' := by
    rintro β ⟨hβ, hβα⟩ r r' h
    by_contra hne
    have h1 : ((r'⁻¹ * r : R) : ↥H) • β = β := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h, inv_smul_smul]
    exact hsemi _ (hRmem _) (hRne _ fun e => hne (inv_mul_eq_one.mp e).symm) β hβ hβα h1
  obtain ⟨g₀, hg₀H, hg₀⟩ := hmoves
  have hβ₀ : (⟨g₀, hg₀H⟩ : ↥H) • α₀ ∈ MulAction.orbit (↥H) α₀ \ {α₀} :=
    ⟨MulAction.mem_orbit _ _, fun h => hg₀ ((smul_eq_map g₀ α₀).symm.trans h)⟩
  have hcardO' : (MulAction.orbit (↥H) α₀ \ {α₀}).ncard = Nat.card (GaloisField 2 k) ^ 2 := by
    have h1 : Nat.card R ≤ (MulAction.orbit (↥H) α₀ \ {α₀}).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_le_card_of_injective
        (fun r : R => (⟨(r : ↥H) • ((⟨g₀, hg₀H⟩ : ↥H) • α₀), hmaps _ hβ₀ r⟩ :
          ↥(MulAction.orbit (↥H) α₀ \ {α₀})))
        (fun r r' h => hinj _ hβ₀ r r' (congrArg Subtype.val h))
    have h2 := Set.ncard_le_ncard hOT
    omega
  have hOTeq : MulAction.orbit (↥H) α₀ \ {α₀} =
      (fun p => Submodule.span (GaloisField 2 k) {p}) '' P₁ :=
    Set.eq_of_subset_of_ncard_le hOT (by omega)
  have hPO : ∀ p ∈ P, Submodule.span (GaloisField 2 k) {p} ∈ MulAction.orbit (↥H) α₀ := by
    intro p hp
    by_cases hpα : Submodule.span (GaloisField 2 k) {p} = α₀
    · rw [hpα]
      exact MulAction.mem_orbit_self α₀
    · have h := hnorm p hp hpα
      rw [← hOTeq] at h
      exact h.1
  have hcardO : (MulAction.orbit (↥H) α₀).ncard = Nat.card (GaloisField 2 k) ^ 2 + 1 := by
    rw [← Set.ncard_sdiff_singleton_add_one (MulAction.mem_orbit_self α₀), hcardO']
  have hreg : ∀ β ∈ MulAction.orbit (↥H) α₀ \ {α₀}, ∀ γ ∈ MulAction.orbit (↥H) α₀ \ {α₀},
      ∃! r : R, (r : ↥H) • β = γ := by
    intro β hβ γ hγ
    have hbij : Function.Bijective
        (fun r : R => (⟨(r : ↥H) • β, hmaps β hβ r⟩ : ↥(MulAction.orbit (↥H) α₀ \ {α₀}))) :=
      Function.Injective.bijective_of_nat_card_le
        (fun r r' h => hinj β hβ r r' (congrArg Subtype.val h))
        (by rw [Nat.card_coe_set_eq, hcardO', hRcard])
    obtain ⟨r, hr⟩ := hbij.2 ⟨γ, hγ⟩
    exact ⟨r, congrArg Subtype.val hr, fun r' hr' =>
      hinj β hβ r' r (hr'.trans (congrArg Subtype.val hr).symm)⟩
  let α : ↥(MulAction.orbit (↥H) α₀) := ⟨α₀, MulAction.mem_orbit_self α₀⟩
  have hcardΩ : Nat.card ↥(MulAction.orbit (↥H) α₀) = 2 ^ (2 * k) + 1 := by
    rw [Nat.card_coe_set_eq, hcardO, GaloisField.card 2 k (by omega), ← pow_mul, mul_comm]
  have hstab : ∀ r : R, (r : ↥H) • α = α := fun r => Subtype.ext (hΛα _ (hRmem r))
  have hregΩ : ∀ β γ : ↥(MulAction.orbit (↥H) α₀), β ≠ α → γ ≠ α →
      ∃! r : R, (r : ↥H) • β = γ := by
    intro β γ hβ hγ
    obtain ⟨r, hr, hu⟩ := hreg β.1 ⟨β.2, fun h => hβ (Subtype.ext h)⟩ γ.1
      ⟨γ.2, fun h => hγ (Subtype.ext h)⟩
    exact ⟨r, Subtype.ext hr, fun r' hr' => hu r' (congrArg Subtype.val hr')⟩
  haveI : FaithfulSMul ↥H ↥(MulAction.orbit (↥H) α₀) := by
    have key : ∀ g : ↥H, (∀ ω : ↥(MulAction.orbit (↥H) α₀), g • ω = ω) → g = 1 := by
      intro g hg
      have hμ : ∀ p ∈ P, ∃ μ : GaloisField 2 k, μ • p = (g : E ≃ₗ[GaloisField 2 k] E) p := by
        intro p hp
        have h3 : (g : E ≃ₗ[GaloisField 2 k] E) • Submodule.span (GaloisField 2 k) {p} =
            Submodule.span (GaloisField 2 k) {p} := congrArg Subtype.val (hg ⟨_, hPO p hp⟩)
        rw [smul_span_singleton] at h3
        have h2 : (g : E ≃ₗ[GaloisField 2 k] E) p ∈ Submodule.span (GaloisField 2 k) {p} := by
          rw [← h3]
          exact Submodule.mem_span_singleton_self _
        exact Submodule.mem_span_singleton.mp h2
      have hpair : ∀ x ∈ P, ∀ y ∈ P, Submodule.span (GaloisField 2 k) {x} ≠
          Submodule.span (GaloisField 2 k) {y} → ∀ a c : GaloisField 2 k,
          a • x = (g : E ≃ₗ[GaloisField 2 k] E) x → c • y = (g : E ≃ₗ[GaloisField 2 k] E) y →
          a * c = 1 := by
        intro x hx y hy hxy a c ha hc
        have e := hiso _ g.2 x y
        rw [← ha, ← hc] at e
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at e
        refine mul_right_cancel₀ (hBne x hx y hy hxy) ?_
        linear_combination e
      have hfix : ∀ p ∈ P, (g : E ≃ₗ[GaloisField 2 k] E) p = p := by
        intro p hp
        have hq4 : 4 ≤ Nat.card (GaloisField 2 k) := by
          rw [GaloisField.card 2 k (by omega)]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        have h2 : 1 <
            (MulAction.orbit (↥H) α₀ \ {Submodule.span (GaloisField 2 k) {p}}).ncard := by
          rw [Set.ncard_sdiff_singleton_of_mem (hPO p hp), hcardO, Nat.add_sub_cancel]
          nlinarith
        obtain ⟨S₁, ⟨hS₁, hS₁p⟩, S₂, ⟨hS₂, hS₂p⟩, h12⟩ :=
          (Set.one_lt_ncard (Set.toFinite _)).mp h2
        obtain ⟨p₁, hp₁, rfl⟩ := hOlines S₁ hS₁
        obtain ⟨p₂, hp₂, rfl⟩ := hOlines S₂ hS₂
        obtain ⟨μ, hμp⟩ := hμ p hp
        obtain ⟨μ₁, hμ₁⟩ := hμ p₁ hp₁
        obtain ⟨μ₂, hμ₂⟩ := hμ p₂ hp₂
        have e1 := hpair p hp p₁ hp₁ (fun h => hS₁p h.symm) μ μ₁ hμp hμ₁
        have e2 := hpair p hp p₂ hp₂ (fun h => hS₂p h.symm) μ μ₂ hμp hμ₂
        have e3 := hpair p₁ hp₁ p₂ hp₂ h12 μ₁ μ₂ hμ₁ hμ₂
        have hμ0 : μ ≠ 0 := left_ne_zero_of_mul_eq_one e1
        have h12' : μ₁ = μ₂ := mul_left_cancel₀ hμ0 (e1.trans e2.symm)
        have hsq : μ₁ ^ 2 = 1 := by
          rw [sq]
          nth_rewrite 2 [h12']
          exact e3
        have hμ1 : μ = 1 := by
          rw [eq_one_of_sq_eq_one hsq, mul_one] at e1
          exact e1
        rw [← hμp, hμ1, one_smul]
      have hid : ((g : E ≃ₗ[GaloisField 2 k] E) : E →ₗ[GaloisField 2 k] E) = LinearMap.id :=
        LinearMap.ext_on hPspan fun p hp => hfix p hp
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      rw [hid]
      rfl
    refine ⟨fun {h₁ h₂} hh => ?_⟩
    have := key (h₂⁻¹ * h₁) fun ω => by rw [mul_smul, hh, inv_smul_smul]
    exact (inv_mul_eq_one.mp this).symm
  have htwo : MulAction.IsMultiplyPretransitive (↥H) ↥(MulAction.orbit (↥H) α₀) 2 := by
    let β : ↥(MulAction.orbit (↥H) α₀) := ⟨_, hβ₀.1⟩
    have hβ : β ≠ α := fun h => hβ₀.2 (congrArg Subtype.val h)
    have key : ∀ a c : ↥(MulAction.orbit (↥H) α₀), a ≠ c →
        ∃ g : ↥H, g • a = α ∧ g • c = β := by
      intro a c hac
      obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq (↥H) a α
      have hne : g₁ • c ≠ α := fun h => hac (smul_left_cancel g₁ (hg₁.trans h.symm))
      obtain ⟨r, hr, -⟩ := hregΩ (g₁ • c) β hne hβ
      exact ⟨(r : ↥H) * g₁, by rw [mul_smul, hg₁, hstab], by rw [mul_smul, hr]⟩
    rw [MulAction.is_two_pretransitive_iff]
    intro a c a' c' hac hac'
    obtain ⟨g, hga, hgc⟩ := key a c hac
    obtain ⟨g', hga', hgc'⟩ := key a' c' hac'
    refine ⟨g'⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, hga, ← hga', inv_smul_smul]
    · rw [mul_smul, hgc, ← hgc', inv_smul_smul]
  have hRstab : R ≤ MulAction.stabilizer (↥H) α := fun r hr => hstab ⟨r, hr⟩
  have hRnorm : (R.subgroupOf (MulAction.stabilizer (↥H) α)).Normal := by
    refine ⟨fun n hn s => ?_⟩
    have hs : Submodule.map (((s : ↥H) : E ≃ₗ[GaloisField 2 k] E) : E →ₗ[GaloisField 2 k] E)
        α₀ = α₀ := (smul_eq_map _ α₀).symm.trans
          (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp s.2))
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hR, Subgroup.mem_subgroupOf]
    exact hΛnorm _ (s : ↥H).2 hs _ (hRmem' _ hn)
  have hRelem : IsElemAbelian 2 R := by
    refine ⟨⟨⟨fun a c => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (Subtype.ext (hΛcomm _ (hRmem a) _ (hRmem c)))
    · exact Subtype.ext (by simpa [pow_two] using hΛsq _ (hRmem' x hx))
  obtain ⟨L, hLn, hLsimple, ⟨hLiso⟩, hL2⟩ := hHKS (↥H) ↥(MulAction.orbit (↥H) α₀) (2 * k)
    (by omega) hcardΩ htwo α R hRstab hRnorm hRelem hregΩ
  haveI : MulAction.IsPretransitive ↥L ↥(MulAction.orbit (↥H) α₀) :=
    MulAction.isPretransitive_of_is_two_pretransitive (h2 := hL2)
  let e : ↥L ≃* ↥(L.map H.subtype) :=
    Subgroup.equivMapOfInjective L H.subtype H.subtype_injective
  have hL'n : ((L.map H.subtype).subgroupOf H).Normal := by
    have : (L.map H.subtype).subgroupOf H = L := by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [this]
    exact hLn
  have hspan : Submodule.span (GaloisField 2 k)
      (Set.range fun ℓ : L.map H.subtype => ((ℓ : E ≃ₗ[GaloisField 2 k] E)) b) = ⊤ := by
    rw [eq_top_iff, ← hPspan, Submodule.span_le]
    intro p hp
    obtain ⟨ℓ, hℓ⟩ := MulAction.exists_smul_eq (↥L) α ⟨_, hPO p hp⟩
    have h1 : ((ℓ : ↥H) : E ≃ₗ[GaloisField 2 k] E) • α₀ =
        Submodule.span (GaloisField 2 k) {p} := congrArg Subtype.val hℓ
    rw [hα₀, smul_span_singleton] at h1
    have h2 : p ∈ Submodule.span (GaloisField 2 k)
        {((ℓ : ↥H) : E ≃ₗ[GaloisField 2 k] E) b} := by
      rw [h1]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
    rw [← hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span
      ⟨⟨H.subtype ℓ, Subgroup.mem_map_of_mem H.subtype ℓ.2⟩, rfl⟩)
  exact ⟨L.map H.subtype, Subgroup.map_subtype_le L, hL'n, e.symm.isSimpleGroup,
    ⟨e.symm.trans hLiso⟩, hspan⟩

end TailFalse

theorem stroth34_ovoid_false (hHKS : HKSStatement) (hSL2 : SL2ModuleDimStatement) {k : ℕ}
    (hk : 2 ≤ k)
    (E : Type) [AddCommGroup E] [Module (GaloisField 2 k) E] [Module.Finite (GaloisField 2 k) E]
    (hdim : Module.finrank (GaloisField 2 k) E = 6)
    (Bf : LinearMap.BilinForm (GaloisField 2 k) E) (Qf : E → GaloisField 2 k)
    (hQsmul : ∀ (a : GaloisField 2 k) (e : E), Qf (a • e) = a ^ 2 * Qf e)
    (hQadd : ∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f)
    (halt : ∀ e : E, Bf e e = 0) (hnd : ∀ e : E, (∀ f, Bf e f = 0) → e = 0)
    (H : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hHQ : ∀ h ∈ H, ∀ e : E, Qf (h e) = Qf e)
    (hHchar : ∀ χ : H →* (GaloisField 2 k)ˣ, χ = 1)
    (b : E) (hb0 : b ≠ 0) (hbs : Qf b = 0)
    (U : Submodule (GaloisField 2 k) E) (hUs : ∀ u ∈ U, Qf u = 0)
    (hUdim : Module.finrank (GaloisField 2 k) U = 3) (hbU : b ∈ U)
    (Λ : Subgroup (E ≃ₗ[GaloisField 2 k] E)) (hΛH : Λ ≤ H)
    (hΛcard : Nat.card Λ = Nat.card (GaloisField 2 k) ^ 2)
    (hΛcomm : ∀ t ∈ Λ, ∀ t' ∈ Λ, t * t' = t' * t) (hΛsq : ∀ t ∈ Λ, t * t = 1)
    (hΛb : ∀ t ∈ Λ, t b = b)
    (hΛE : ∀ t ∈ Λ, t ≠ 1 →
      b ∈ LinearMap.range (((t : E ≃ₗ[GaloisField 2 k] E) : E →ₗ[GaloisField 2 k] E) - 1))
    (hsing : ∀ v : E, (∀ t ∈ Λ, t v = v) → Qf v = 0 → ∃ s : GaloisField 2 k, v = s • b)
    (hΛnorm : ∀ h ∈ H, Submodule.map (h : E →ₗ[GaloisField 2 k] E)
        (Submodule.span (GaloisField 2 k) {b}) = Submodule.span (GaloisField 2 k) {b} →
      ∀ t ∈ Λ, h * t * h⁻¹ ∈ Λ)
    (hmoves : ∃ h ∈ H, Submodule.map (h : E →ₗ[GaloisField 2 k] E)
        (Submodule.span (GaloisField 2 k) {b}) ≠ Submodule.span (GaloisField 2 k) {b})
    (P : Set E) (hbP : b ∈ P) (hP0 : ∀ p ∈ P, p ≠ 0 ∧ Qf p = 0)
    (hPsmul : ∀ p ∈ P, ∀ c : GaloisField 2 k, c ≠ 0 → c • p ∈ P)
    (hPH : ∀ h ∈ H, ∀ p ∈ P, h p ∈ P)
    (hPorth : ∀ p ∈ P, ∀ p' ∈ P, (∀ c : GaloisField 2 k, p' ≠ c • p) → Bf p p' ≠ 0)
    (hPspan : Submodule.span (GaloisField 2 k) P = ⊤) :
    False := by
  obtain ⟨L, hLH, hLn, hLs, hLiso, hspan⟩ := TailFalse.exists_normal_sl2 hHKS hk E hdim Bf Qf
    hQsmul hQadd H hHQ b hbs U hUs hUdim hbU Λ hΛH hΛcard hΛcomm hΛsq hΛb hΛE hΛnorm hmoves P
    hbP hP0 hPsmul hPH hPorth hPspan
  exact stroth34_module_false hSL2 hk E hdim Bf Qf hQsmul hQadd halt hnd H hHQ hHchar L hLH hLn hLs
    hLiso b hb0 hbs hspan Λ hΛH hΛb hsing

end CFSG.RankThree.GF2n.Stroth80
