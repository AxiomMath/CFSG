module

public import CFSG.Quasithin.Background.E6TwentyThreeI
public import CFSG.Quasithin.Background.E6TwentyThreeJ
public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.Quasithin.Background.E6Eighteen
public import CFSG.Quasithin.EmptyFaithful.T1515cF
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6E27
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623A6Config : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L U₀ X : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → E3.rParam V = 1 →
    U ≤ V → E3.mQuot V U = 1 → ¬ Subgroup.centralizer (U : Set G) ≤ M →
    CharTwo (Subgroup.centralizer (U : Set G)) →
    IsChi0Block (Subgroup.centralizer (U : Set G)) L → IsAltType L 3 → ¬ L ≤ M →
    U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) = ⊥ →
    U₀ < U → E3.mQuot V U₀ ≤ 2 →
    IsComponentIn X (Subgroup.centralizer (U₀ : Set G)) →
    Nonempty (↥X ≃* alternatingGroup (Fin 6)) → L ≤ X → False

section Rank

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_three {p : ℕ} [hp : Fact p.Prime] {H : Subgroup G} {x₁ x₂ x₃ : G}
    (h₁ : x₁ ∈ H) (h₂ : x₂ ∈ H) (h₃ : x₃ ∈ H) (hp₁ : x₁ ^ p = 1) (hp₂ : x₂ ^ p = 1)
    (hp₃ : x₃ ^ p = 1) (hx₁1 : x₁ ≠ 1) (c12 : x₁ * x₂ = x₂ * x₁) (c13 : x₁ * x₃ = x₃ * x₁)
    (c23 : x₂ * x₃ = x₃ * x₂) (hx₂ : x₂ ∉ Subgroup.zpowers x₁)
    (hx₃ : ∀ z ∈ Subgroup.zpowers x₁, ∀ n : ℕ, x₃ ≠ z * x₂ ^ n) :
    3 ≤ CFSG.Open.pRank p H := by
  have hp1 : 1 < p := hp.out.one_lt
  let F₀ : PUnit.{1} →* G := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hcard₀ : Nat.card PUnit.{1} = p ^ 0 := by simp
  have hx₁r : x₁ ∉ F₀.range := by
    rintro ⟨a, ha⟩
    exact hx₁1 ha.symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrep₁⟩ := CFSG.SectionRank.exists_extend
    (fun _ _ => rfl) (fun _ => rfl) hcard₀ F₀ hF₀ hp₁ hx₁r (fun _ => Commute.one_left x₁)
  have hr₁ : ∀ a, F₁ a ∈ Subgroup.zpowers x₁ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₁ a
    rw [hb]
    exact Subgroup.mul_mem _ (by simp [F₀]) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₁) n)
  have hz₂ : ∀ z ∈ Subgroup.zpowers x₁, Commute z x₂ := by
    rintro z ⟨k, rfl⟩
    exact (Commute.zpow_left c12 k)
  have hz₃ : ∀ z ∈ Subgroup.zpowers x₁, Commute z x₃ := by
    rintro z ⟨k, rfl⟩
    exact (Commute.zpow_left c13 k)
  have hx₂r : x₂ ∉ F₁.range := by
    rintro ⟨a, ha⟩
    exact hx₂ (ha ▸ hr₁ a)
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrep₂⟩ :=
    CFSG.SectionRank.exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁ hp₂ hx₂r
      (fun a => hz₂ _ (hr₁ a))
  have hx₃r : x₃ ∉ F₂.range := by
    rintro ⟨a, ha⟩
    obtain ⟨b, n, hb⟩ := hrep₂ a
    exact hx₃ _ (hr₁ b) n (by rw [← hb, ha])
  have hc3 : ∀ a, Commute (F₂ a) x₃ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₂ a
    rw [hb]
    exact (hz₃ _ (hr₁ b)).mul_left ((Commute.pow_left c23 n))
  obtain ⟨F₃, hF₃, hcomm₃, hpow₃, hcard₃, hrep₃⟩ :=
    CFSG.SectionRank.exists_extend hcomm₂ hpow₂ hcard₂ F₂ hF₂ hp₃ hx₃r hc3
  have hrange : F₃.range ≤ H := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hrep₃ a
    obtain ⟨c, m, hc⟩ := hrep₂ b
    obtain ⟨k, hk⟩ := hr₁ c
    rw [hb, hc, ← hk]
    exact H.mul_mem (H.mul_mem (H.zpow_mem h₁ k) (H.pow_mem h₂ m)) (H.pow_mem h₃ n)
  have := CFSG.SectionRank.le_pRank_of_injective hp1 hcomm₃ hpow₃ hcard₃ F₃ hF₃ hrange
  omega

end Rank

section Components

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_of_centralizes {Y : Subgroup G} (hZ : IsPGroup 2 (Subgroup.center ↥Y))
    {w : G} (hwY : w ∈ Y) (hwC : ∀ g ∈ Y, w * g = g * w) (hw3 : w ^ 3 = 1) : w = 1 := by
  have hc : (⟨w, hwY⟩ : ↥Y) ∈ Subgroup.center ↥Y :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hwC g g.2).symm
  set z : Subgroup.center ↥Y := ⟨⟨w, hwY⟩, hc⟩ with hz
  obtain ⟨k, hk⟩ := hZ z
  have h3 : z ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp [hz, hw3]
  have hdvd : orderOf z ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h3)
  have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  have := congrArg (fun u : Subgroup.center ↥Y => ((u : ↥Y) : G)) hdvd
  simpa [hz] using this

theorem mem_normalizer_of_pow_three {H X : Subgroup G} (hX : IsComponentIn X H)
    (hO : oddCoreIn H = ⊥) (hr : CFSG.Open.pRank 3 H ≤ 2) (h3 : 3 ∣ Nat.card X) {y : G}
    (hyH : y ∈ H) (hy3 : y ^ 3 = 1) : y ∈ Subgroup.normalizer (X : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hyN
  have hZ : ∀ {Y : Subgroup G}, IsComponentIn Y H → IsPGroup 2 (Subgroup.center ↥Y) :=
    fun hY => isPGroup_two_center_of_isComponentOf1515c (DoubleA3.isComponentIn_iff_open.mp hY) hO
  have hHy : H.map (MulAut.conj y).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hyH)
  set X₂ := X.map (MulAut.conj y).toMonoidHom with hX₂def
  set X₃ := X₂.map (MulAut.conj y).toMonoidHom with hX₃def
  have hX₂ : IsComponentIn X₂ H := by
    have := BenderBranch.isComponentIn_map (MulAut.conj y) hX
    rwa [hHy] at this
  have hX₃ : IsComponentIn X₃ H := by
    have := BenderBranch.isComponentIn_map (MulAut.conj y) hX₂
    rwa [hHy] at this
  have hinj : Function.Injective (fun K : Subgroup G => K.map (MulAut.conj y).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj y).injective
  have h12 : X ≠ X₂ := fun h => hyN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have h23 : X₂ ≠ X₃ := fun h => h12 (hinj h)
  have h13 : X ≠ X₃ := by
    intro h
    apply hyN
    have hy2 : y ^ 2 ∈ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have : X₃ = X.map (MulAut.conj (y ^ 2)).toMonoidHom := by
        rw [hX₃def, hX₂def, Subgroup.map_map]
        congr 1
        ext g
        simp [MulAut.conj_apply, pow_two, mul_assoc]
      change X.map (MulAut.conj (y ^ 2)).toMonoidHom = X
      rw [← this, ← h]
    have : y = (y ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc y = y ^ 3 * y := by rw [hy3, one_mul]
        _ = y ^ (2 * 2) := by rw [← pow_succ]
    rw [this]
    exact Subgroup.pow_mem _ hy2 2
  have c12 := (BenderBranch.eq_or_commute_of_isComponentIn hX hX₂).resolve_left h12
  have c13 := (BenderBranch.eq_or_commute_of_isComponentIn hX hX₃).resolve_left h13
  have c23 := (BenderBranch.eq_or_commute_of_isComponentIn hX₂ hX₃).resolve_left h23
  have k12 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp c12
  have k13 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp c13
  have k23 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp c23
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3
  set x₁ : G := (e : G) with hx₁
  set x₂ : G := y * x₁ * y⁻¹ with hx₂
  set x₃ : G := y * x₂ * y⁻¹ with hx₃
  have hx₁X : x₁ ∈ X := e.2
  have hx₂X : x₂ ∈ X₂ := ⟨x₁, hx₁X, by simp [hx₂, MulAut.conj_apply]⟩
  have hx₃X : x₃ ∈ X₃ := ⟨x₂, hx₂X, by simp [hx₃, MulAut.conj_apply]⟩
  have hx₁3 : x₁ ^ 3 = 1 := by
    rw [hx₁, ← Subgroup.coe_pow, ← he, pow_orderOf_eq_one, Subgroup.coe_one]
  have hx₂3 : x₂ ^ 3 = 1 := by rw [hx₂, conj_pow, hx₁3]; group
  have hx₃3 : x₃ ^ 3 = 1 := by rw [hx₃, conj_pow, hx₂3]; group
  have hx₁1 : x₁ ≠ 1 := by
    intro h1
    have : e = 1 := Subtype.ext h1
    rw [this, orderOf_one] at he
    omega
  have cm : ∀ {A B : Subgroup G}, A ≤ Subgroup.centralizer (B : Set G) → ∀ a ∈ A, ∀ b ∈ B,
      a * b = b * a := fun hAB a ha b hb => (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb).symm
  refine absurd (three_le_pRank_of_three (hX.1 hx₁X) (hX₂.1 hx₂X) (hX₃.1 hx₃X) hx₁3 hx₂3 hx₃3
    hx₁1 (cm k12 _ hx₁X _ hx₂X) (cm k13 _ hx₁X _ hx₃X) (cm k23 _ hx₂X _ hx₃X) ?_ ?_) (by omega)
  ·
    intro hmem
    have hx₂1 : x₂ ≠ 1 := by
      intro h1
      apply hx₁1
      have : x₁ = y⁻¹ * x₂ * y := by rw [hx₂]; group
      rw [this, h1]; group
    apply hx₂1
    refine eq_one_of_mem_of_centralizes (hZ hX₂) hx₂X (fun g hg => ?_) hx₂3
    have hx₂X1 : x₂ ∈ X := (Subgroup.zpowers_le.mpr hx₁X) hmem
    exact cm k12 _ hx₂X1 _ hg
  ·
    intro z hz n hzn
    have hx₃1 : x₃ ≠ 1 := by
      intro h1
      apply hx₁1
      have : x₁ = y⁻¹ * (y⁻¹ * x₃ * y) * y := by rw [hx₃, hx₂]; group
      rw [this, h1]; group
    apply hx₃1
    have hzX : z ∈ X := (Subgroup.zpowers_le.mpr hx₁X) hz
    refine eq_one_of_mem_of_centralizes (hZ hX₃) hx₃X (fun g hg => ?_) hx₃3
    rw [hzn]
    have h1 := cm k13 _ hzX _ hg
    have h2 := cm k23 _ (X₂.pow_mem hx₂X n) _ hg
    calc z * x₂ ^ n * g = z * (g * x₂ ^ n) := by rw [mul_assoc, h2]
      _ = g * (z * x₂ ^ n) := by rw [← mul_assoc, h1, mul_assoc]

end Components

section Alt3

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_pow_three_mem {L K : Subgroup G} (hs : IsShort2 L) (h3 : IsAltType L 3)
    (hK : ∀ y ∈ L, y ^ 3 = 1 → y ∈ K) : L ≤ K := by
  classical
  obtain ⟨-, -, -, -, -, -, c, hcL, hc3, hcN, hfpf, hLeq⟩ := hs.alt3_structure h3
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hs).trans (C1.blockQ_le L)
  have hcK : c ∈ K := hK c hcL hc3'
  have hcU : ∀ u ∈ blockU L, c * u⁻¹ * c⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hcN u⁻¹).mp (inv_mem hu)
  let f : ↥(blockU L) → ↥(blockU L) := fun v =>
    ⟨v * (c * (v : G)⁻¹ * c⁻¹), mul_mem v.2 (hcU v v.2)⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h1 : (v : G) * (c * (v : G)⁻¹ * c⁻¹) = w * (c * (w : G)⁻¹ * c⁻¹) :=
      congrArg Subtype.val hvw
    have h1' : (v : G) * c * (v : G)⁻¹ = w * c * (w : G)⁻¹ := by
      calc (v : G) * c * (v : G)⁻¹ = ((v : G) * (c * (v : G)⁻¹ * c⁻¹)) * c := by group
        _ = ((w : G) * (c * (w : G)⁻¹ * c⁻¹)) * c := by rw [h1]
        _ = w * c * (w : G)⁻¹ := by group
    have h2 : c * ((w : G)⁻¹ * v) * c⁻¹ = (w : G)⁻¹ * v := by
      calc c * ((w : G)⁻¹ * v) * c⁻¹ = (w : G)⁻¹ * ((w : G) * c * (w : G)⁻¹) * v * c⁻¹ := by
            group
        _ = (w : G)⁻¹ * ((v : G) * c * (v : G)⁻¹) * v * c⁻¹ := by rw [h1']
        _ = (w : G)⁻¹ * v := by group
    by_contra hne
    have hne' : (w : G)⁻¹ * v ≠ 1 := fun h => hne (Subtype.ext (by
      rw [inv_mul_eq_one] at h
      exact h.symm))
    exact hfpf _ (mul_mem (inv_mem w.2) v.2) hne' h2
  have hfs : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have hUK : blockU L ≤ K := by
    intro u hu
    obtain ⟨v, hv⟩ := hfs ⟨u, hu⟩
    have hu' : u = (v : G) * c * (v : G)⁻¹ * c⁻¹ := by
      have := congrArg Subtype.val hv
      simp only [f] at this
      rw [← this]
      group
    have hvc : (v : G) * c * (v : G)⁻¹ ∈ K := hK _
      (mul_mem (mul_mem (hUL v.2) hcL) (inv_mem (hUL v.2))) (by rw [conj_pow, hc3']; group)
    rw [hu']
    exact mul_mem hvc (inv_mem hcK)
  rw [hLeq]
  exact sup_le hUK (Subgroup.zpowers_le.mpr hcK)

end Alt3

section AltSix

open CFSG.ComponentClassification.OuterAutomorphisms

theorem two_dvd_card_outer_alt6 : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  have h1 : Nat.card (MulAut (alternatingGroup (Fin 6))) =
      Nat.card (Outer (alternatingGroup (Fin 6))) * 360 := by
    rw [← CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_card]
    exact (inner (alternatingGroup (Fin 6))).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (CFSG.Quasithin.SteinbergCB.conjPerm 6).range = 720 := by
    have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [← h720]
    exact Nat.card_congr (MonoidHom.ofInjective
      (CFSG.Quasithin.SteinbergCB.conjPerm_injective (n := 6) (by norm_num))).toEquiv.symm
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  have h3 := Subgroup.card_subgroup_dvd_card (CFSG.Quasithin.SteinbergCB.conjPerm 6).range
  rw [h2, h1] at h3
  obtain ⟨k, hk⟩ := h3
  generalize Nat.card (Outer (alternatingGroup (Fin 6))) = n at hk ⊢
  exact ⟨k, by omega⟩

theorem mem_inner_alt6_of_pow_three {τ : MulAut (alternatingGroup (Fin 6))} (hτ : τ ^ 3 = 1) :
    τ ∈ inner (alternatingGroup (Fin 6)) := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  set o : Outer (alternatingGroup (Fin 6)) := QuotientGroup.mk τ with ho
  have ho3 : o ^ 3 = 1 := by rw [ho, ← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
  have hdvd3 : orderOf o ∣ 3 := orderOf_dvd_of_pow_eq_one ho3
  have hdvdO : orderOf o ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := orderOf_dvd_natCard o
  have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have h2 := two_dvd_card_outer_alt6
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  have hord : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact h
    · exfalso
      rw [h] at hdvdO
      obtain ⟨k, hk⟩ := hdvdO
      obtain ⟨m, hm⟩ := h2
      generalize Nat.card (Outer (alternatingGroup (Fin 6))) = n at hk hm hle hpos
      omega
  have ho1 : o = 1 := orderOf_eq_one_iff.mp hord
  rw [ho, QuotientGroup.eq_one_iff] at ho1
  exact ho1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mem_of_pow_three_alt6 {X : Subgroup G} (e : ↥X ≃* alternatingGroup (Fin 6))
    {x : G} (hxN : x ∈ Subgroup.normalizer (X : Set G)) (hx3 : x ^ 3 = 1) :
    ∃ y ∈ X, ∀ g ∈ X, x * g * x⁻¹ = y * g * y⁻¹ := by
  set τ₀ : MulAut ↥X := X.normalizerMonoidHom ⟨x, hxN⟩ with hτ₀
  set τ : MulAut (alternatingGroup (Fin 6)) := MulAut.congr e τ₀ with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow, hτ₀, ← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one, map_one]
  obtain ⟨σ, hσ⟩ := mem_inner_alt6_of_pow_three hτ3
  refine ⟨(e.symm σ : G), (e.symm σ).2, fun g hg => ?_⟩
  have h1 : τ (e ⟨g, hg⟩) = σ * e ⟨g, hg⟩ * σ⁻¹ := by
    rw [← hσ]
    rfl
  have h2 : τ (e ⟨g, hg⟩) = e (τ₀ ⟨g, hg⟩) := by
    rw [hτ]
    simp [MulAut.congr_apply]
  rw [h2] at h1
  have h3 : τ₀ ⟨g, hg⟩ = e.symm σ * ⟨g, hg⟩ * (e.symm σ)⁻¹ := by
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h4 := congrArg Subtype.val h3
  simpa [hτ₀] using h4

theorem eq_one_of_mem_centralizer_alt6 {H X : Subgroup G} (e : ↥X ≃* alternatingGroup (Fin 6))
    (hXH : X ≤ H) (hr : CFSG.Open.pRank 3 H ≤ 2) {c : G} (hcH : c ∈ H)
    (hcC : c ∈ Subgroup.centralizer (X : Set G)) (hc3 : c ^ 3 = 1) : c = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hc1
  obtain ⟨P, hPX, hP3, hP9⟩ := CFSG.QuasithinUnique.exists_elemAbelian_nine e
  have hE₂ : IsElemAbelian 3 (Subgroup.zpowers c) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hne : ¬ Subgroup.zpowers c ≤ P := by
    intro hle
    apply hc1
    have hcX : c ∈ X := hPX (hle (Subgroup.mem_zpowers c))
    have hcen : e ⟨c, hcX⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hcC) g' g'.2)
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen
    have h1 : (⟨c, hcX⟩ : ↥X) = 1 := e.injective (by rw [hcen, map_one])
    exact congrArg Subtype.val h1
  have hcomm : X ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hcC)
  have := three_le_pRank_of_commuting_E hcomm hXH (Subgroup.zpowers_le.mpr hcH) hPX le_rfl hP3
    hE₂ (by rw [hP9]; norm_num) hne
  omega

end AltSix

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_le_normalizer {V X K : Subgroup G}
    (hV : V ≤ Subgroup.normalizer (X : Set G)) (hK : K ≤ X) : ⁅V, K⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro v hv k hk
  have h1 : v * k * v⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hV hv) k).mp (hK hk)
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem (hK hk))

omit [Finite G] in
theorem three_dvd_card_of_quot {X : Subgroup G} (h : 3 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X)) :
    3 ∣ Nat.card X := by
  rw [(Subgroup.center ↥X).card_eq_card_quotient_mul_card_subgroup]
  exact h.mul_right _

omit [Finite G] in
theorem eq_one_of_centralizes_alt {n : ℕ} (hn : 5 ≤ n) {X : Subgroup G}
    (e : ↥X ≃* alternatingGroup (Fin n)) {w : G} (hwX : w ∈ X) (hwC : ∀ g ∈ X, g * w = w * g) :
    w = 1 := by
  have hcen : e ⟨w, hwX⟩ ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hwC g' g'.2)
  rw [alternatingGroup.center_eq_bot (by simp; omega), Subgroup.mem_bot] at hcen
  have h1 : (⟨w, hwX⟩ : ↥X) = 1 := e.injective (by rw [hcen, map_one])
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem center_eq_bot_of_alt {n : ℕ} (hn : 5 ≤ n) {X : Subgroup G}
    (e : ↥X ≃* alternatingGroup (Fin n)) : Subgroup.center ↥X = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => Subtype.ext ?_
  exact eq_one_of_centralizes_alt hn e z.2 fun g hg =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz ⟨g, hg⟩))

theorem e623A3Layer_of (h311 : Theorem311Stmt) (h618 : E618Stmt) (h621 : E621Stmt)
    (h622 : E622Stmt) (h68 : E68Stmt) (hKG : E623CentA3Comp) (hA6 : E623A6Config) :
    E623A3Layer := by
  intro G _ _ T M V U L U₀ X hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀U hU₀q hX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  by_contra hLX
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have h15 : HypE615 hV M := Or.inr hm
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr1).2
  have hU₀le : U₀ ≤ U := hU₀U.le
  have hU₀V : U₀ ≤ V := hU₀le.trans hUV
  have hqUU₀ : E3.mQuot U U₀ ≠ 0 := fun h0 =>
    hU₀U.ne ((E3.mQuot_eq_zero_iff (hV2.to_le hUV) hU₀le).1 h0)
  have hadd := E3.mQuot_add hU₀le hUV
  have hq2 : E3.mQuot V U₀ = 2 := by omega
  have hq1 : E3.mQuot U U₀ = 1 := by omega
  have hU₀1 : U₀ ≠ ⊥ := by
    rintro rfl
    omega
  set H₀ := Subgroup.centralizer (U₀ : Set G) with hH₀def
  have hHH₀ : Subgroup.centralizer (U : Set G) ≤ H₀ := Subgroup.centralizer_le hU₀le
  have hH₀M : ¬ H₀ ≤ M := fun hle => hUM (hHH₀.trans hle)
  have hΓ : U₀ ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hU₀V hU₀1 hH₀M (by omega)
  have hO : oddCoreIn H₀ = ⊥ := h621 G T M V U₀ hV h h15 hU₀V hU₀1
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQsyl : IsSylowTwoOf Q H₀ := e6_5_one h hΓ
  have hr3 : CFSG.Open.pRank 3 H₀ ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.centralizer_le_normalizer _)).trans
      ((A1b.pRank_le_evenRank Nat.prime_three (by norm_num)
        ⟨U₀, hU₀1, hV2.to_le hU₀V, rfl⟩).trans h.qtke.2.2)
  have hXq : CFSG.IsQuasisimple ↥X := BenderBranch.isQuasisimple_of_isComponentIn hX
  have hXZ : IsPGroup 2 (Subgroup.center ↥X) :=
    isPGroup_two_center_of_isComponentOf1515c (DoubleA3.isComponentIn_iff_open.mp hX) hO
  obtain ⟨hXM, hcases⟩ := h68 G T M V U₀ X hV h hΓ hX
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hVN : V ≤ Subgroup.normalizer (X : Set G) := fun v hv =>
    mem_normalizer_of_mem_center_sylow hQsyl hX (hVQ hv)
      (Subgroup.mem_centralizer_iff.2 fun q hq => (Subgroup.mem_centralizer_iff.1 hq.2 v hv).symm)
  have hSX : IsSylowTwoOf (Q ⊓ X) X := isSylowTwoOf_inf_of_subnormal' hQsyl hX.1 hX.2.2
  have hXH₀ : X ≤ H₀ := hX.1
  have hCVX : V ⊓ Subgroup.centralizer (X : Set G) = U₀ := by
    set W := V ⊓ Subgroup.centralizer (X : Set G) with hWdef
    have hWV : W ≤ V := inf_le_left
    have hU₀W : U₀ ≤ W := le_inf hU₀V fun u hu => Subgroup.mem_centralizer_iff.2 fun g hg =>
      (Subgroup.mem_centralizer_iff.1 (hXH₀ hg) u hu).symm
    have hadd' := E3.mQuot_add hU₀W hWV
    have hW0 : E3.mQuot V W ≠ 0 := by
      intro h0
      have hWeq : W = V := (E3.mQuot_eq_zero_iff hV2 hWV).1 h0
      apply hXM
      refine le_trans (fun g hg => ?_) h.centralizer_le
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ W := by rw [hWeq]; exact hv
      exact (Subgroup.mem_centralizer_iff.1 hv'.2 g hg).symm
    have hW1 : E3.mQuot V W ≠ 1 := by
      intro h1
      have hWc := h622 G T M V W hV h h15 hWV h1
      have hXW : X ≤ Subgroup.centralizer (W : Set G) := fun g hg =>
        Subgroup.mem_centralizer_iff.2 fun w hw => (Subgroup.mem_centralizer_iff.1 hw.2 g hg).symm
      exact DoubleA3.not_isComponentIn_of_charTwo hWc X
        (BenderBranch.isComponentIn_of_le hX hXW (Subgroup.centralizer_le hU₀W))
    have hWU₀ : E3.mQuot W U₀ = 0 := by omega
    exact ((E3.mQuot_eq_zero_iff (hV2.to_le hWV) hU₀W).1 hWU₀).symm
  have hm2 : E3.mQuot V (V ⊓ Subgroup.centralizer (X : Set G)) = 2 := by rw [hCVX, hq2]
  have hidx : U₀.relIndex U = 2 := by
    rw [E3.relIndex_eq_two_pow (hV2.to_le hUV), hq1, pow_one]
  obtain ⟨a, haU, haU₀⟩ : ∃ a ∈ U, a ∉ U₀ := by
    by_contra hall
    push Not at hall
    exact hU₀U.ne (le_antisymm hU₀le fun w hw => hall w hw)
  have hCU := centralizer_eq_inf_of_relIndex_two hU₀le hidx haU haU₀
  have haV : a ∈ V := hUV haU
  have haN : a ∈ Subgroup.normalizer (X : Set G) := hVN haV
  have ha2 : a ^ 2 = 1 := h.isElemAbelian.2 a haV
  have haC : a ∉ Subgroup.centralizer (X : Set G) := fun haC =>
    haU₀ (by rw [← hCVX]; exact ⟨haV, haC⟩)
  have haS : ∀ s ∈ Q ⊓ X, a * s = s * a := fun s hs =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hs).1).2 a haV
  have hLnot : ¬ L ≤ Subgroup.centralizer (X : Set G) := fun hle =>
    hLX (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
  obtain ⟨x, hxL, hx3, -, hxC⟩ := A3Push.exists_fpf_not_centralizing hLb.1.1 hL3 hLnot
  have hxU : x ∈ Subgroup.centralizer (U : Set G) := hLb.1.2.1 hxL
  have hxH₀ : x ∈ H₀ := hHH₀ hxU
  have hxa : x * a = a * x := (Subgroup.mem_centralizer_iff.1 hxU a haU).symm
  have hxCX : x ∉ Subgroup.centralizer (X : Set G) := fun hxc => hxC fun g hg => by
    have := Subgroup.mem_centralizer_iff.1 hxc g hg
    calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [this]
      _ = g := by group
  obtain ⟨hQU, hU4, -⟩ := hLb.1.1.alt3_structure hL3
  have hE4 : Nat.card (blockQ L) ≤ 4 := by rw [hQU, hU4]
  have hbound : ∀ r ∈ pCoreOf 2 (X ⊓ Subgroup.centralizer ({a} : Set G)),
      x * r * x⁻¹ * r⁻¹ ∈ blockQ L := by
    set N₁ := compJoin H₀ ⊓ Subgroup.centralizer (U : Set G) with hN₁
    have hXJ : X ≤ compJoin H₀ := le_sSup hX
    have hJN : compJoin H₀ ≤ Subgroup.normalizer (X : Set G) := by
      refine sSup_le fun Y hY => ?_
      rcases BenderBranch.eq_or_commute_of_isComponentIn hY hX with heq | hc
      · rw [heq]
        exact Subgroup.le_normalizer
      · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
          (Subgroup.centralizer_le_normalizer _)
    have hCXa : X ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer (U : Set G) := by
      rw [hCU]
      exact inf_le_inf_right _ hXH₀
    have h1 : X ⊓ Subgroup.centralizer ({a} : Set G) ≤ N₁ := le_inf (inf_le_left.trans hXJ) hCXa
    have hnorm_inf : ∀ {A B : Subgroup G} {g : G}, g ∈ Subgroup.normalizer (A : Set G) →
        g ∈ Subgroup.normalizer (B : Set G) →
        g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
      intro A B g hA hB
      rw [Subgroup.mem_normalizer_iff]
      intro n
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hA n,
        Subgroup.mem_normalizer_iff.mp hB n]
    have h2 : N₁ ≤ Subgroup.normalizer
        ((X ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
      intro n hn
      have hna : n ∈ Subgroup.centralizer ({a} : Set G) := by
        have h' := hn.2
        rw [hCU] at h'
        exact h'.2
      exact hnorm_inf (hJN hn.1) (Subgroup.le_normalizer hna)
    have h3 : N₁ ≤ Subgroup.centralizer (U : Set G) := inf_le_right
    have h4 : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (N₁ : Set G) := fun g hg =>
      hnorm_inf (le_normalizer_compJoin H₀ (hHH₀ hg)) (Subgroup.le_normalizer hg)
    have hsub : IsSubnormal (X ⊓ Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer (U : Set G)) :=
      IsSubnormal.step h1 ((Subgroup.normal_subgroupOf_iff_le_normalizer h1).mpr h2)
        (IsSubnormal.step h3 ((Subgroup.normal_subgroupOf_iff_le_normalizer h3).mpr h4)
          (IsSubnormal.refl _))
    intro r hr
    exact A3Push.commutator_mem_blockQ_of_mem_pCoreOf hLb.1
      (A4.pCoreOf_le_of_subnormal 2 hsub hr) hxL
  have hKGcase : (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X)
        .PSL 2 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSp 2 2 2) → 3 ∣ Nat.card X →
      ⁅V, X ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (X : Set G)) = V → False := by
    intro htype h3 hdec
    rw [hCVX] at hdec
    have hU₀N : U₀ ≤ Subgroup.normalizer ((⁅V, X ⊓ M⁆ : Subgroup G) : Set G) := by
      intro u hu
      have huC : ⁅V, X ⊓ M⁆ ≤ Subgroup.centralizer ({u} : Set G) := by
        rw [Subgroup.commutator_le]
        intro v hv g hg
        have cv : Commute u v := (hVc u (hU₀V hu) v hv)
        have cg : Commute u g := (Subgroup.mem_centralizer_iff.1 (hXH₀ hg.1) u hu)
        rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
        exact (((cv.mul_right cg).mul_right cv.inv_right).mul_right cg.inv_right).eq.symm
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun w hw => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.1 (huC hw)
    have haW : a ∈ ⁅V, X ⊓ M⁆ ⊔ U₀ := by
      rw [hdec]
      exact haV
    obtain ⟨w, hw, u, hu, hwu⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hU₀N).1 haW
    have hwX : w ∈ X := commutator_le_of_le_normalizer hVN inf_le_left hw
    have hb : ∀ g ∈ X, a * g * a⁻¹ = w * g * w⁻¹ := by
      intro g hg
      have hug : u * g = g * u := (Subgroup.mem_centralizer_iff.1 (hXH₀ hg) u hu)
      rw [hwu]
      calc w * u * g * (w * u)⁻¹ = w * (u * g) * u⁻¹ * w⁻¹ := by group
        _ = w * (g * u) * u⁻¹ * w⁻¹ := by rw [hug]
        _ = w * g * w⁻¹ := by group
    exact hxCX (hKG G X (Q ⊓ X) (blockQ L) a w x hXq hXZ htype hSX haS haN ha2 haC hwX hb
      (mem_normalizer_of_pow_three hX hO hr3 h3 hxH₀ hx3) hx3 hxa hE4 hbound)
  have hA6case : Nonempty (↥X ≃* alternatingGroup (Fin 6)) → False := by
    rintro ⟨e⟩
    have h3 : 3 ∣ Nat.card X := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hL3X : ∀ y ∈ L, y ^ 3 = 1 → y ∈ X := by
      intro y hyL hy3
      have hyH₀ : y ∈ H₀ := hHH₀ (hLb.1.2.1 hyL)
      have hyN := mem_normalizer_of_pow_three hX hO hr3 h3 hyH₀ hy3
      obtain ⟨z, hzX, hz⟩ := exists_mem_of_pow_three_alt6 e hyN hy3
      have hcC : z⁻¹ * y ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have h1 := hz g hg
        calc g * (z⁻¹ * y) = z⁻¹ * (z * g * z⁻¹) * y := by group
          _ = z⁻¹ * (y * g * y⁻¹) * y := by rw [h1]
          _ = z⁻¹ * y * g := by group
      have hyz : y * z = z * y := by
        have h1 := hz z hzX
        calc y * z = (y * z * y⁻¹) * y := by group
          _ = (z * z * z⁻¹) * y := by rw [h1]
          _ = z * y := by group
      have hc3 : (z⁻¹ * y) ^ 3 = 1 := by
        have hcomm : Commute z⁻¹ y := (Commute.inv_left (show Commute z y from hyz.symm))
        have hpow : (z⁻¹ * y) ^ 3 = z⁻¹ ^ 3 * y ^ 3 := hcomm.mul_pow 3
        rw [hy3, mul_one] at hpow
        have hmemX : (z⁻¹ * y) ^ 3 ∈ X := by
          rw [hpow]
          exact X.pow_mem (inv_mem hzX) 3
        have hmemC : (z⁻¹ * y) ^ 3 ∈ Subgroup.centralizer (X : Set G) :=
          Subgroup.pow_mem _ hcC 3
        exact eq_one_of_centralizes_alt (by norm_num) e hmemX fun g hg =>
          Subgroup.mem_centralizer_iff.1 hmemC g hg
      have hc1 := eq_one_of_mem_centralizer_alt6 e hXH₀ hr3
        (mul_mem (inv_mem (hXH₀ hzX)) hyH₀) hcC hc3
      have hyz' : y = z := by
        rw [inv_mul_eq_one] at hc1
        exact hc1.symm
      rw [hyz']
      exact hzX
    exact hA6 G T M V U L U₀ X hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀U hU₀q hX ⟨e⟩
      (le_of_forall_pow_three_mem hLb.1.1 hL3 hL3X)
  have h3quot : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ},
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) t n 2 2 →
      (t = .PSL ∧ n = 2) ∨ (t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ n = 3) → 3 ∣ Nat.card X := by
    intro t n ht hcase
    refine three_dvd_card_of_quot ?_
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two ht).1 rfl]
      decide
    · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two ht).1 rfl]
      decide
    · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two ht).2.1 rfl]
      decide
  rcases hcases with ⟨k, htype, -, -, -, -, hk, -, hdec⟩ | ⟨k, hk1, htype, -, hdec, hb⟩ |
      ⟨-, -, -, h1, -⟩ | ⟨htype, -, -, -⟩ | ⟨-, -, h1, -⟩
  ·
    obtain rfl : k = 2 := by omega
    have hdec' := (hdec (by norm_num)).2.1
    rcases htype with ⟨-, ht⟩ | ⟨hodd, -, -⟩ | ⟨-, ht⟩ | ⟨-, ht⟩
    · exact hKGcase (Or.inl ht) (h3quot ht (Or.inl ⟨rfl, rfl⟩)) hdec'
    · exact absurd hodd (by decide)
    · exact hKGcase (Or.inr (Or.inl ht)) (h3quot ht (Or.inr (Or.inl ⟨rfl, rfl⟩))) hdec'
    · exact hKGcase (Or.inr (Or.inr (Or.inl ht))) (h3quot ht (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        hdec'
  ·
    rcases hb with ⟨-, ⟨h2k, -⟩ | ⟨-, h1⟩⟩ | ⟨-, -, -, hkn, -⟩
    ·
      obtain rfl : k = 1 := by omega
      rcases htype with ⟨h2, -⟩ | ⟨-, he⟩
      · omega
      · exact hA6case he
    · omega
    ·
      obtain rfl : k = 2 := by omega
      rcases htype with ⟨-, ht⟩ | ⟨h1, -⟩
      · refine hKGcase (Or.inr (Or.inr (Or.inr ht))) ?_ (hdec (by norm_num)).2
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two ht).2.2.1 rfl]
        decide
      · omega
  · omega
  ·
    have h618' := h618 G T M V U₀ X hV h h15 hΓ (by omega) hX
    rcases htype with he7 | ⟨hc3, -⟩ | ⟨hc3, he⟩
    · obtain ⟨e⟩ := he7
      apply h618'
      have hZbot := center_eq_bot_of_alt (by norm_num) e
      refine ⟨⟨((QuotientGroup.quotientMulEquivOfEq hZbot).trans
        QuotientGroup.quotientBot).trans e⟩, Or.inl ?_⟩
      rw [hZbot, Subgroup.card_bot]
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hXZ
      rw [hc3] at hn
      rcases n with _ | n
      · norm_num at hn
      · rw [pow_succ] at hn
        omega
    · exact h618' ⟨he, Or.inr hc3⟩
  · omega

end Main

end CFSG.Quasithin.E6
