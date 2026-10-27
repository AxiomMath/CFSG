module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup

theorem ker_eq_top_of_isPGroup_two_range {X : Type*} [Group X]
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤) {G : Type*} [Group G]
    (f : X →* G) (hf : IsPGroup 2 f.range) : f.ker = ⊤ :=
  hX2 f.ker (hf.of_equiv (QuotientGroup.quotientKerEquivRange f).symm)

theorem le_ker_of_isPGroup_two_of_commute {X : Type*} [Group X] {G : Type*} [Group G] [Finite G]
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤) (f : X →* G)
    (hcomm : ∀ x y : X, Commute (f x) (f y)) (R : Subgroup X) (hR : IsPGroup 2 R) :
    R ≤ f.ker := by
  obtain ⟨e, o, ho, he⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  let g : X →* G :=
    { toFun := fun x => f x ^ o
      map_one' := by rw [map_one, one_pow]
      map_mul' := fun x y => by rw [map_mul, (hcomm x y).mul_pow] }
  have hg : IsPGroup 2 g.range := by
    rintro ⟨_, x, rfl⟩
    refine ⟨e, Subtype.ext ?_⟩
    change (f x ^ o) ^ 2 ^ e = 1
    rw [← pow_mul, mul_comm, ← he, pow_card_eq_one']
  have hker := ker_eq_top_of_isPGroup_two_range hX2 g hg
  intro r hr
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have h1 : f r ^ o = 1 := by
    have : r ∈ g.ker := hker ▸ mem_top r
    exact this
  have h2 : f r ^ 2 ^ k = 1 := by
    have := congrArg (fun z : R => f z) hk
    simpa [map_pow] using this
  have hcop : Nat.Coprime (2 ^ k) o := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 ho)
  rw [MonoidHom.mem_ker]
  have := pow_gcd_eq_one.2 ⟨h2, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem exists_ne_one_conj_mem_zpowers {B : Type*} [Group B] [Finite B] {D Y R : Subgroup B}
    (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDi : D.index ≤ 2) (hYD : Y ≤ D) (hY : Y ≠ ⊥)
    (hRY : ∀ r ∈ R, ∀ y ∈ Y, r * y * r⁻¹ ∈ Y) :
    ∃ y ∈ Y, y ≠ 1 ∧ ∀ r ∈ R, r * y * r⁻¹ ∈ zpowers y := by
  obtain ⟨y₀, hy₀, hy₀1⟩ := (Subgroup.bot_or_exists_ne_one Y).resolve_left hY
  have hfix : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ = y := fun d hd y hy => by
    rw [hD d hd y (hYD hy), mul_inv_cancel_right]
  by_cases hRD : ∀ r ∈ R, r ∈ D
  · refine ⟨y₀, hy₀, hy₀1, fun r hr => ?_⟩
    rw [hfix r (hRD r hr) y₀ hy₀]
    exact mem_zpowers _
  push Not at hRD
  obtain ⟨t, htR, htD⟩ := hRD
  have hD2 : D.index = 2 := by
    have h0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : D.index ≠ 1 := fun h => htD (Subgroup.index_eq_one.1 h ▸ mem_top t)
    omega
  have hcases : ∀ r ∈ R, r ∈ D ∨ ∃ d ∈ D, r = t * d := by
    intro r _
    by_cases hr : r ∈ D
    · exact Or.inl hr
    · refine Or.inr ⟨t⁻¹ * r, ?_, by group⟩
      rw [Subgroup.mul_mem_iff_of_index_two hD2, inv_mem_iff]
      exact iff_of_false htD hr
  set τ : B → B := fun y => t * y * t⁻¹ with hτ
  have htt : t * t ∈ D := by
    rw [Subgroup.mul_mem_iff_of_index_two hD2]
  have hττ : ∀ y ∈ Y, τ (τ y) = y := fun y hy => by
    have h := hfix (t * t) htt y hy
    simp only [hτ]
    calc t * (t * y * t⁻¹) * t⁻¹ = t * t * y * (t * t)⁻¹ := by group
      _ = y := h
  have hact : ∀ r ∈ R, ∀ y ∈ Y, r * y * r⁻¹ = y ∨ r * y * r⁻¹ = τ y := by
    intro r hr y hy
    rcases hcases r hr with hrD | ⟨d, hd, rfl⟩
    · exact Or.inl (hfix r hrD y hy)
    · right
      simp only [hτ]
      calc t * d * y * (t * d)⁻¹ = t * (d * y * d⁻¹) * t⁻¹ := by group
        _ = t * y * t⁻¹ := by rw [hfix d hd y hy]
  by_cases h0 : τ y₀ = y₀
  · refine ⟨y₀, hy₀, hy₀1, fun r hr => ?_⟩
    rcases hact r hr y₀ hy₀ with h | h
    · rw [h]
      exact mem_zpowers _
    · rw [h, h0]
      exact mem_zpowers _
  · have hτY : τ y₀ ∈ Y := hRY t htR y₀ hy₀
    refine ⟨y₀ * (τ y₀)⁻¹, mul_mem hy₀ (inv_mem hτY), fun h => h0 ?_, fun r hr => ?_⟩
    · exact (mul_inv_eq_one.1 h).symm
    · have hτy : τ (y₀ * (τ y₀)⁻¹) = (y₀ * (τ y₀)⁻¹)⁻¹ := by
        have e1 : τ (y₀ * (τ y₀)⁻¹) = τ y₀ * (τ (τ y₀))⁻¹ := by
          simp only [hτ]
          group
        rw [e1, hττ _ hy₀, mul_inv_rev, inv_inv]
      rcases hact r hr _ (mul_mem hy₀ (inv_mem hτY)) with h | h
      · rw [h]
        exact mem_zpowers _
      · rw [h, hτy]
        exact inv_mem (mem_zpowers _)

theorem irreducible_two_prime_residual_killed_by_abelian_index_two_target {A B : Type*}
    [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} (hp : p.Prime)
    (Q X : Subgroup A) [Q.Normal] [X.Normal] (hQX : Q ≤ X) (hQ : IsPGroup 2 Q)
    (hXQ : ∀ x ∈ X.map (QuotientGroup.mk' Q), x ^ p = 1)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hW : p ^ 2 ≤ Nat.card (X.map (QuotientGroup.mk' Q) ⧸ frattini (X.map (QuotientGroup.mk' Q))))
    (hirr : ∀ K : Subgroup (A ⧸ Q),
      (frattini (X.map (QuotientGroup.mk' Q))).map (X.map (QuotientGroup.mk' Q)).subtype ≤ K →
      K ≤ X.map (QuotientGroup.mk' Q) →
      (∀ a : A, ∀ k ∈ K, (a : A ⧸ Q) * k * (a : A ⧸ Q)⁻¹ ∈ K) →
      K = (frattini (X.map (QuotientGroup.mk' Q))).map (X.map (QuotientGroup.mk' Q)).subtype ∨
        K = X.map (QuotientGroup.mk' Q))
    (D : Subgroup B) [D.Normal] (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDi : D.index ≤ 2)
    (ρ : A →* B) : X.map ρ = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Q with hπ
  set Xb := X.map π with hXb
  have hXD : ∀ x ∈ X, ρ x ∈ D := by
    set f : X →* B ⧸ D := (QuotientGroup.mk' D).comp (ρ.comp X.subtype) with hf
    have hf2 : IsPGroup 2 f.range := by
      have h1 : Nat.card f.range ≤ 2 := by
        refine (card_le_card_group f.range).trans ?_
        rw [← index_eq_card]
        exact hDi
      have h0 : 0 < Nat.card f.range := Nat.card_pos
      rcases (show Nat.card f.range = 1 ∨ Nat.card f.range = 2 by omega) with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    have hker := ker_eq_top_of_isPGroup_two_range hX2 f hf2
    intro x hx
    have : (⟨x, hx⟩ : X) ∈ f.ker := hker ▸ mem_top _
    exact (QuotientGroup.eq_one_iff _).1 this
  have hQker : Q ≤ ρ.ker := by
    have hQ' : IsPGroup 2 (Q.subgroupOf X) :=
      hQ.of_equiv (subgroupOfEquivOfLe hQX).symm
    have h := le_ker_of_isPGroup_two_of_commute hX2 (ρ.comp X.subtype)
      (fun x y => hD _ (hXD x x.2) _ (hXD y y.2)) (Q.subgroupOf X) hQ'
    intro q hq
    exact h (mem_subgroupOf.2 (show ((⟨q, hQX hq⟩ : X) : A) ∈ Q from hq))
  set ρ' : A ⧸ Q →* B := QuotientGroup.lift Q ρ hQker with hρ'
  have hρ'π : ∀ a : A, ρ' (π a) = ρ a := fun a => rfl
  set Y := X.map ρ with hY
  have hρ'Y : ∀ w : Xb, ρ' w ∈ Y := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  set f : Xb →* Y := (ρ'.comp Xb.subtype).codRestrict Y hρ'Y with hf
  have hfsurj : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨π x, x, hx, rfl⟩, rfl⟩
  have hYD : Y ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hXD x hx
  have hYcomm : ∀ a b : Y, a * b = b * a := fun a b =>
    Subtype.ext (hD _ (hYD a.2) _ (hYD b.2))
  have hYpow : ∀ a : Y, a ^ p = 1 := by
    intro a
    obtain ⟨w, rfl⟩ := hfsurj a
    rw [← map_pow]
    have : w ^ p = 1 := Subtype.ext (by rw [coe_pow, coe_one]; exact hXQ w w.2)
    rw [this, map_one]
  have hΦ : frattini Xb ≤ f.ker :=
    CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary f hYcomm hYpow
  have hXbN : Xb.Normal := (inferInstance : X.Normal).map π (QuotientGroup.mk'_surjective Q)
  have hconjY : ∀ (a : A) (l : Y), ρ a * l * (ρ a)⁻¹ ∈ Y := by
    rintro a ⟨_, x, hx, rfl⟩
    exact ⟨a * x * a⁻¹, (inferInstance : X.Normal).conj_mem x hx a, by simp⟩
  have hpre : ∀ L : Subgroup Y, (∀ a : A, ∀ l : Y, l ∈ L →
        (⟨ρ a * l * (ρ a)⁻¹, hconjY a l⟩ : Y) ∈ L) →
      (L.comap f).map Xb.subtype = (frattini Xb).map Xb.subtype ∨
        (L.comap f).map Xb.subtype = Xb := by
    intro L hL
    refine hirr _ (map_mono fun w hw => ?_) (map_subtype_le _) ?_
    · change f w ∈ L
      rw [hΦ hw]
      exact one_mem L
    · rintro a _ ⟨w, hw, rfl⟩
      have hmem : (a : A ⧸ Q) * w * (a : A ⧸ Q)⁻¹ ∈ Xb := hXbN.conj_mem w w.2 _
      refine ⟨⟨_, hmem⟩, ?_, rfl⟩
      change f ⟨_, hmem⟩ ∈ L
      have e : f ⟨_, hmem⟩ = ⟨ρ a * f w * (ρ a)⁻¹, hconjY a (f w)⟩ := by
        apply Subtype.ext
        change ρ' ((a : A ⧸ Q) * w * (a : A ⧸ Q)⁻¹) = ρ a * ρ' w * (ρ a)⁻¹
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [e]
      exact hL a _ hw
  rcases hpre ⊥ (fun a l hl => by
      rw [mem_bot] at hl ⊢
      apply Subtype.ext
      simp [hl]) with h | h
  ·
    exfalso
    have hker : f.ker = frattini Xb := by
      have h' : (f.ker).map Xb.subtype = (frattini Xb).map Xb.subtype := by
        rw [← h]
        rfl
      exact map_injective Xb.subtype_injective h'
    have hYcard : p ^ 2 ≤ Nat.card Y := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hker]
      exact hW
    have hYne : Y ≠ ⊥ := by
      intro hbot
      have : Nat.card Y = 1 := by rw [hbot, card_bot]
      have hp1 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
      omega
    obtain ⟨y, hyY, hy1, hyinv⟩ := exists_ne_one_conj_mem_zpowers hD hDi hYD hYne
      (R := ρ.range) (fun r hr y hy => by
        obtain ⟨a, rfl⟩ := hr
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨a * x * a⁻¹, (inferInstance : X.Normal).conj_mem x hx a, by simp⟩)
    set L : Subgroup Y := (zpowers y).subgroupOf Y with hL
    rcases hpre L (fun a l hl => by
        rw [hL, mem_subgroupOf] at hl ⊢
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hl
        have hc := hyinv (ρ a) ⟨a, rfl⟩
        obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hc
        change ρ a * (l : B) * (ρ a)⁻¹ ∈ zpowers y
        rw [← hn]
        have e : ρ a * y ^ n * (ρ a)⁻¹ = (ρ a * y * (ρ a)⁻¹) ^ n := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
        rw [e]
        exact zpow_mem hc n) with h' | h'
    ·
      obtain ⟨w, hw⟩ := hfsurj ⟨y, hyY⟩
      have hwL : (w : A ⧸ Q) ∈ (L.comap f).map Xb.subtype := by
        refine ⟨w, ?_, rfl⟩
        change f w ∈ L
        rw [hw, hL, mem_subgroupOf]
        exact mem_zpowers y
      rw [h'] at hwL
      obtain ⟨w', hw', hww'⟩ := hwL
      have hw'' : w' = w := Subtype.ext hww'
      rw [hw''] at hw'
      have : f w = 1 := hΦ hw'
      rw [hw] at this
      exact hy1 (congrArg Subtype.val this)
    ·
      have hYL : ∀ z : Y, (z : B) ∈ zpowers y := by
        intro z
        obtain ⟨w, rfl⟩ := hfsurj z
        have hw : (w : A ⧸ Q) ∈ (L.comap f).map Xb.subtype := by
          rw [h']
          exact w.2
        obtain ⟨w', hw', hww'⟩ := hw
        have hw'' : w' = w := Subtype.ext hww'
        rw [hw''] at hw'
        exact hw'
      have hyord : orderOf y = p := by
        refine orderOf_eq_prime ?_ hy1
        have := hYpow ⟨y, hyY⟩
        exact congrArg Subtype.val this
      have hle : Nat.card Y ≤ Nat.card (zpowers y) := by
        refine Nat.card_le_card_of_injective (fun z : Y => (⟨z, hYL z⟩ : zpowers y)) ?_
        intro z z' hzz'
        have h := congrArg Subtype.val hzz'
        exact Subtype.ext h
      rw [Nat.card_zpowers, hyord] at hle
      have : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
  ·
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hw : π x ∈ ((⊥ : Subgroup Y).comap f).map Xb.subtype := by
      rw [h]
      exact ⟨x, hx, rfl⟩
    obtain ⟨w, hw', hww⟩ := hw
    have h1 : f w = 1 := mem_bot.1 hw'
    have h2 : ρ' w = ρ x := by
      rw [← hρ'π]
      congr 1
    rw [mem_bot, ← h2]
    exact congrArg Subtype.val h1

end CFSG.Quasithin.SteinbergBT
