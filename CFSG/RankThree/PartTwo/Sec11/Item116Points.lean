module

public import CFSG.RankThree.PartTwo.KFacts.K74Plane
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.Sec10.Item108
public import CFSG.RankThree.PartTwo.Sec9.Item97

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Irred

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_comm_of_conj_eq {g x : G} (h : g * x * g⁻¹ = x) : x * g = g * x := by
  calc x * g = g * x * g⁻¹ * g := by rw [h]
    _ = g * x := by group

theorem eq_bot_or_eq_of_isIrreducibleOn {W B D : Subgroup G}
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn W B)) (hDB : D ≤ B)
    (hD : ∀ w ∈ W, w ∈ Subgroup.normalizer (B : Set G) →
      w ∈ Subgroup.normalizer (D : Set G)) :
    D = ⊥ ∨ D = B := by
  have hinv : ∀ φ ∈ Sec4.autIn W B, (D.subgroupOf B).map φ.toMonoidHom = D.subgroupOf B := by
    intro φ hφ
    obtain ⟨w, hwN, hwW, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    have hle : (D.subgroupOf B).map (B.normalizerMonoidHom ⟨w, hwN⟩).toMonoidHom ≤
        D.subgroupOf B := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ D := hy
      rw [Subgroup.mem_subgroupOf]
      change ((B.normalizerMonoidHom ⟨w, hwN⟩ y : B) : G) ∈ D
      rw [Sec4.normalizerMonoidHom_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hD w hwW hwN) _).mp hy'
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
  rcases hirr _ hinv with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact le_bot_iff.mp fun x hx => h.le_bot ⟨hx, hDB hx⟩
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hDB h

theorem mem_of_hyperplane {A B : Subgroup G} {d l₀ : G} (hexp : ∀ u ∈ A, u ^ 3 = 1)
    (h27 : Nat.card A = 27) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hdA : d ∈ A)
    (hl₀B : l₀ ∈ Subgroup.normalizer (B : Set G)) (hl₀d : l₀ * d * l₀⁻¹ = d)
    (hl₀A : ∀ u ∈ A, l₀ * u * l₀⁻¹ * u⁻¹ ∈ Subgroup.zpowers d)
    (hl₀1 : ∃ u ∈ A, l₀ * u * l₀⁻¹ ≠ u) : d ∈ B := by
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  by_contra hdB
  have hBC : ∀ b ∈ B, l₀ * b * l₀⁻¹ = b := by
    intro b hb
    have h1 : l₀ * b * l₀⁻¹ * b⁻¹ ∈ B :=
      B.mul_mem ((Subgroup.mem_normalizer_iff.mp hl₀B b).mp hb) (B.inv_mem hb)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hl₀A b (hBA hb))
    have h2 : l₀ * b * l₀⁻¹ * b⁻¹ = 1 := by
      by_contra hne
      apply hdB
      rw [← hk] at h1 hne
      have hd3 : d ^ 3 = 1 := hexp d hdA
      have hy3 : (d ^ k) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
      have hd1 : d ≠ 1 := fun h => hne (by rw [h, one_zpow])
      have hle : Subgroup.zpowers (d ^ k) ≤ Subgroup.zpowers d :=
        Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers d k)
      have heq : Subgroup.zpowers (d ^ k) = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hd3 hd1,
            orderOf_eq_prime hy3 hne])
      exact Subgroup.zpowers_le.mpr h1 (heq ▸ Subgroup.mem_zpowers d)
    calc l₀ * b * l₀⁻¹ = l₀ * b * l₀⁻¹ * b⁻¹ * b := by group
      _ = b := by rw [h2, one_mul]
  have hBd : B ⊔ Subgroup.zpowers d = A := by
    have hle : B ⊔ Subgroup.zpowers d ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr hdA)
    have h1 := Sec9.three_mul_card_le_of_le_of_ne hA3 hle le_sup_left (fun h => hdB (by
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h27]; omega)
  have hle : B ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer ({l₀} : Set G) := by
    refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_conj_eq (hBC b hb))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_conj_eq hl₀d)
  obtain ⟨u, hu, hu1⟩ := hl₀1
  apply hu1
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle (hBd ▸ hu))
  rw [← this, mul_inv_cancel_right]

end Irred

section Orbit

open Matrix

@[expose] def OnLine (y z p q : ZMod 3) : Prop := ∃ k : ZMod 3, y = k * p ∧ z = k * q

instance (y z p q : ZMod 3) : Decidable (OnLine y z p q) := by
  unfold OnLine
  infer_instance

@[expose] def MovesLine (a b c d r t : ZMod 3) : Prop :=
  ∀ k : ZMod 3, a * r + b * t ≠ k * r ∨ c * r + d * t ≠ k * t

instance (a b c d r t : ZMod 3) : Decidable (MovesLine a b c d r t) := by
  unfold MovesLine
  infer_instance

@[expose] def OrbitCover (a b c d p q r t : ZMod 3) : Prop :=
  ∀ y z : ZMod 3, (y ≠ 0 ∨ z ≠ 0) →
    OnLine y z p q ∨ OnLine y z r t ∨ OnLine y z (a * r + b * t) (c * r + d * t) ∨
      OnLine y z (a * (a * r + b * t) + b * (c * r + d * t))
        (c * (a * r + b * t) + d * (c * r + d * t))

instance (a b c d p q r t : ZMod 3) : Decidable (OrbitCover a b c d p q r t) := by
  unfold OrbitCover
  infer_instance

@[expose] def OrbitCoverAll (a b c d p q : ZMod 3) : Prop :=
  ∀ r t : ZMod 3, MovesLine a b c d r t → OrbitCover a b c d p q r t

instance (a b c d p q : ZMod 3) : Decidable (OrbitCoverAll a b c d p q) := by
  unfold OrbitCoverAll
  infer_instance

@[expose] def OrbitCoverFixed (a b c d : ZMod 3) : Prop :=
  ∀ p q : ZMod 3, (p ≠ 0 ∨ q ≠ 0) → a * p + b * q = p → c * p + d * q = q →
    OrbitCoverAll a b c d p q

instance (a b c d : ZMod 3) : Decidable (OrbitCoverFixed a b c d) := by
  unfold OrbitCoverFixed
  infer_instance

theorem orbit_cases_V2 : ∀ a b c d : ZMod 3,
    !![a, b; c, d] * !![a, b; c, d] * !![a, b; c, d] = 1 → OrbitCoverFixed a b c d := by
  decide +kernel

open KFacts in
theorem mem_span_singleton_V2_iff {u v : V2} :
    v ∈ Submodule.span (ZMod 3) ({u} : Set V2) ↔ ∃ k : ZMod 3, v 0 = k * u 0 ∧ v 1 = k * u 1 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp, by simp⟩
  · rintro ⟨k, h0, h1⟩
    refine ⟨k, ?_⟩
    ext i
    fin_cases i
    · simp [h0]
    · simp [h1]

open KFacts in
theorem mem_span_cases_V2 {τ : V2 ≃ₗ[ZMod 3] V2} (hτ : τ ^ 3 = 1) {v₀ u v : V2} (hv₀ : v₀ ≠ 0)
    (hτv₀ : τ v₀ = v₀) (hu : τ u ∉ Submodule.span (ZMod 3) ({u} : Set V2)) (hv : v ≠ 0) :
    v ∈ Submodule.span (ZMod 3) ({v₀} : Set V2) ∨ v ∈ Submodule.span (ZMod 3) ({u} : Set V2) ∨
      v ∈ Submodule.span (ZMod 3) ({τ u} : Set V2) ∨
      v ∈ Submodule.span (ZMod 3) ({τ (τ u)} : Set V2) := by
  have hM := toMatrix'_pow_eq_one_V2 hτ
  rw [toMatrix'_eq_V2, pow_three'] at hM
  have happ : ∀ w : V2, τ w = ![τ (Pi.single 0 1) 0 * w 0 + τ (Pi.single 1 1) 0 * w 1,
      τ (Pi.single 0 1) 1 * w 0 + τ (Pi.single 1 1) 1 * w 1] := by
    intro w
    have h1 := apply_eq_V2 (τ : V2 →ₗ[ZMod 3] V2) (w 0) (w 1)
    have h2 : (![w 0, w 1] : V2) = w := by
      ext i
      fin_cases i <;> rfl
    rw [h2] at h1
    exact h1
  have hne : ∀ w : V2, w ≠ 0 → (w 0 ≠ 0 ∨ w 1 ≠ 0) := by
    intro w hw
    by_contra h
    push Not at h
    apply hw
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  have hτv₀' := happ v₀
  rw [hτv₀] at hτv₀'
  have hfix0 : τ (Pi.single 0 1) 0 * v₀ 0 + τ (Pi.single 1 1) 0 * v₀ 1 = v₀ 0 := by
    conv_rhs => rw [hτv₀']
    rfl
  have hfix1 : τ (Pi.single 0 1) 1 * v₀ 0 + τ (Pi.single 1 1) 1 * v₀ 1 = v₀ 1 := by
    conv_rhs => rw [hτv₀']
    rfl
  have hmove : ∀ k : ZMod 3, τ (Pi.single 0 1) 0 * u 0 + τ (Pi.single 1 1) 0 * u 1 ≠ k * u 0 ∨
      τ (Pi.single 0 1) 1 * u 0 + τ (Pi.single 1 1) 1 * u 1 ≠ k * u 1 := by
    intro k
    by_contra h
    push Not at h
    apply hu
    rw [mem_span_singleton_V2_iff, happ u]
    exact ⟨k, h.1, h.2⟩
  have hτu0 : (τ u) 0 = τ (Pi.single 0 1) 0 * u 0 + τ (Pi.single 1 1) 0 * u 1 := by
    rw [happ u]
    rfl
  have hτu1 : (τ u) 1 = τ (Pi.single 0 1) 1 * u 0 + τ (Pi.single 1 1) 1 * u 1 := by
    rw [happ u]
    rfl
  have hττu0 : (τ (τ u)) 0 = τ (Pi.single 0 1) 0 * (τ u) 0 + τ (Pi.single 1 1) 0 * (τ u) 1 := by
    rw [happ (τ u)]
    rfl
  have hττu1 : (τ (τ u)) 1 = τ (Pi.single 0 1) 1 * (τ u) 0 + τ (Pi.single 1 1) 1 * (τ u) 1 := by
    rw [happ (τ u)]
    rfl
  rcases orbit_cases_V2 _ _ _ _ hM _ _ (hne v₀ hv₀) hfix0 hfix1 _ _ hmove _ _ (hne v hv) with
    ⟨k, h0, h1⟩ | ⟨k, h0, h1⟩ | ⟨k, h0, h1⟩ | ⟨k, h0, h1⟩
  · exact Or.inl (mem_span_singleton_V2_iff.mpr ⟨k, h0, h1⟩)
  · exact Or.inr (Or.inl (mem_span_singleton_V2_iff.mpr ⟨k, h0, h1⟩))
  · refine Or.inr (Or.inr (Or.inl (mem_span_singleton_V2_iff.mpr ⟨k, ?_, ?_⟩)))
    · rw [hτu0]; exact h0
    · rw [hτu1]; exact h1
  · refine Or.inr (Or.inr (Or.inr (mem_span_singleton_V2_iff.mpr ⟨k, ?_, ?_⟩)))
    · rw [hττu0, hτu0, hτu1]; exact h0
    · rw [hττu1, hτu0, hτu1]; exact h1

end Orbit

section SylowW

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_zpowers_of_mem_zpowers_conj {s x y : G}
    (h : y ∈ Subgroup.zpowers (s * x * s⁻¹)) : s⁻¹ * y * s ∈ Subgroup.zpowers x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow]
  group

open KFacts in
theorem exists_isSylowOf_le_normalizer {W B : Subgroup G} {c : G}
    (hBe : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hWB : W ≤ Subgroup.normalizer (B : Set G)) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn W B))
    (hcB : c ∈ B) (hc1 : c ≠ 1) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S W ∧
      S ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : c ^ 3 = 1 := hBe.2 c hcB
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 W
  by_cases hSc : S ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  · exact ⟨S, hS, hSc⟩
  obtain ⟨s, hsS, hsc⟩ := Set.not_subset.mp hSc
  have hS3 := hS.isPGroup
  have hSW := hS.le
  obtain ⟨b₀, ⟨hb₀B, hb₀S⟩, hb₀3⟩ :=
    exists_mem_centralizer_orderOf_eq hS3 (hSW.trans hWB) (by rw [hB9]; norm_num)
  have hb₀3' : b₀ ^ 3 = 1 := hb₀3 ▸ pow_orderOf_eq_one b₀
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb₀3
    exact absurd hb₀3 (by norm_num)
  by_cases hO : ∃ w ∈ W, w⁻¹ * b₀ * w ∈ Subgroup.zpowers c
  · obtain ⟨w, hwW, hwc⟩ := hO
    refine ⟨S.map (MulAut.conj w⁻¹).toMonoidHom, ?_, ?_⟩
    · refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        change w⁻¹ * t * w⁻¹⁻¹ ∈ W
        exact W.mul_mem (W.mul_mem (W.inv_mem hwW) (hSW ht)) (W.inv_mem (W.inv_mem hwW))
      · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hS.card_eq]
    · rintro _ ⟨t, ht, rfl⟩
      change w⁻¹ * t * w⁻¹⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)
      set c' := w⁻¹ * b₀ * w with hc'
      have hc'3 : c' ^ 3 = 1 := by
        rw [hc', show w⁻¹ * b₀ * w = w⁻¹ * b₀ * w⁻¹⁻¹ by group, conj_pow, hb₀3']
        group
      have hc'1 : c' ≠ 1 := fun h => hb₀1 (by
        rw [hc'] at h
        calc b₀ = w * (w⁻¹ * b₀ * w) * w⁻¹ := by group
          _ = 1 := by rw [h]; group)
      have heq : Subgroup.zpowers c' = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwc) (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hco, orderOf_eq_prime hc'3 hc'1])
      have htc' : t * b₀ = b₀ * t := Subgroup.mem_centralizer_iff.mp hb₀S t ht
      have hfix : (w⁻¹ * t * w⁻¹⁻¹) * c' * (w⁻¹ * t * w⁻¹⁻¹)⁻¹ = c' := by
        rw [hc']
        calc w⁻¹ * t * w⁻¹⁻¹ * (w⁻¹ * b₀ * w) * (w⁻¹ * t * w⁻¹⁻¹)⁻¹ =
            w⁻¹ * (t * b₀) * t⁻¹ * w := by group
          _ = w⁻¹ * b₀ * w := by rw [htc']; group
      apply Sec10.mem_normalizer_zpowers_of_conj_mem
      have hcc' : c ∈ Subgroup.zpowers c' := heq ▸ Subgroup.mem_zpowers c
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcc'
      have h1 : (w⁻¹ * t * w⁻¹⁻¹) * c * (w⁻¹ * t * w⁻¹⁻¹)⁻¹ = c := by
        rw [← hk, ← conj_zpow, hfix]
      rw [h1]
      exact Subgroup.mem_zpowers c
  · exfalso
    push Not at hO
    obtain ⟨f⟩ := Sec12.exists_coords hBe (n := 2) (by rw [hB9]; norm_num)
    have hsB : s ∈ Subgroup.normalizer (B : Set G) := hWB (hSW hsS)
    set σ := B.normalizerMonoidHom ⟨s, hsB⟩ with hσ
    set τ := Sec12.coordHom f σ with hτ
    have hτx : ∀ x : B, τ (Sec12.coordVec f x) = Sec12.coordVec f (σ x) := by
      intro x
      rw [hτ, Sec12.coordHom_apply, Sec12.coordVec, Sec12.coordVec]
      simp
    have hσx : ∀ x : B, ((σ x : B) : G) = s * x * s⁻¹ := fun x =>
      Sec4.normalizerMonoidHom_apply_coe hsB x
    have hτ3 : τ ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := hS3 ⟨s, hsS⟩
      have hk' : τ ^ 3 ^ k = 1 := by
        have h1 : (⟨s, hsB⟩ : Subgroup.normalizer (B : Set G)) ^ 3 ^ k = 1 :=
          Subtype.ext (by simpa using congrArg Subtype.val hk)
        rw [hτ, hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
      have h1 : orderOf τ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have h2 : orderOf τ ∣ 48 := card_V2_equiv ▸ orderOf_dvd_natCard τ
      obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
      have hj1 : j ≤ 1 := by
        by_contra hj
        have h9 : 9 ∣ orderOf τ := by
          rw [hjeq]
          exact (Nat.pow_dvd_pow 3 (by omega : 2 ≤ j))
        have := h9.trans h2
        norm_num at this
      rw [← orderOf_dvd_iff_pow_eq_one, hjeq]
      exact Nat.pow_dvd_pow 3 hj1
    have hv₀0 : Sec12.coordVec f ⟨b₀, hb₀B⟩ ≠ 0 :=
      Sec12.coordVec_ne_zero f (fun h => hb₀1 (congrArg Subtype.val h))
    have hτv₀ : τ (Sec12.coordVec f ⟨b₀, hb₀B⟩) = Sec12.coordVec f ⟨b₀, hb₀B⟩ := by
      rw [hτx]
      congr 1
      apply Subtype.ext
      rw [hσx]
      have := Subgroup.mem_centralizer_iff.mp hb₀S s hsS
      rw [this, mul_inv_cancel_right]
    have hτu : τ (Sec12.coordVec f ⟨c, hcB⟩) ∉
        Submodule.span (ZMod 3) ({Sec12.coordVec f ⟨c, hcB⟩} : Set V2) := by
      intro h
      apply hsc
      rw [hτx, coordVec_mem_span_iff] at h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      apply Sec10.mem_normalizer_zpowers_of_conj_mem
      have h1 : s * c * s⁻¹ = ((σ ⟨c, hcB⟩ : B) : G) := (hσx ⟨c, hcB⟩).symm
      rw [h1, ← hk]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp⟩
    have hcoe : ∀ x y : B, x ∈ Subgroup.zpowers y → (x : G) ∈ Subgroup.zpowers (y : G) := by
      intro x y hxy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxy
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp⟩
    have hWb₀ : ∀ w ∈ W, w * b₀ * w⁻¹ ∈ Subgroup.zpowers b₀ := by
      intro w hwW
      have hxB : w * b₀ * w⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hWB hwW) b₀).mp hb₀B
      have hx1 : (⟨w * b₀ * w⁻¹, hxB⟩ : B) ≠ 1 := by
        intro h
        apply hb₀1
        have h' : w * b₀ * w⁻¹ = 1 := congrArg Subtype.val h
        calc b₀ = w⁻¹ * (w * b₀ * w⁻¹) * w := by group
          _ = 1 := by rw [h']; group
      rcases mem_span_cases_V2 hτ3 hv₀0 hτv₀ hτu (Sec12.coordVec_ne_zero f hx1) with
        h | h | h | h
      · rw [coordVec_mem_span_iff] at h
        exact hcoe _ _ h
      · rw [coordVec_mem_span_iff] at h
        exact absurd (by simpa using hcoe _ _ h) (hO w⁻¹ (W.inv_mem hwW))
      · rw [hτx, coordVec_mem_span_iff] at h
        have h1 := hcoe _ _ h
        rw [hσx] at h1
        have h2 := conj_mem_zpowers_of_mem_zpowers_conj h1
        refine absurd ?_ (hO (w⁻¹ * s) (W.mul_mem (W.inv_mem hwW) (hSW hsS)))
        rw [show (w⁻¹ * s)⁻¹ * b₀ * (w⁻¹ * s) = s⁻¹ * (w * b₀ * w⁻¹) * s by group]
        exact h2
      · rw [hτx, hτx, coordVec_mem_span_iff] at h
        have h1 := hcoe _ _ h
        rw [hσx, hσx] at h1
        have h2 := conj_mem_zpowers_of_mem_zpowers_conj (conj_mem_zpowers_of_mem_zpowers_conj h1)
        refine absurd ?_ (hO (w⁻¹ * s * s)
          (W.mul_mem (W.mul_mem (W.inv_mem hwW) (hSW hsS)) (hSW hsS)))
        rw [show (w⁻¹ * s * s)⁻¹ * b₀ * (w⁻¹ * s * s) = s⁻¹ * (s⁻¹ * (w * b₀ * w⁻¹) * s) * s by
          group]
        exact h2
    rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr hb₀B)
        (fun w hwW _ => Sec10.mem_normalizer_zpowers_of_conj_mem (hWb₀ w hwW)) with h | h
    · exact hb₀1 (by rw [← Subgroup.mem_bot, ← h]; exact Subgroup.mem_zpowers b₀)
    · have h3 : Nat.card (Subgroup.zpowers b₀) = 3 := by rw [Nat.card_zpowers, hb₀3]
      rw [h, hB9] at h3
      norm_num at h3

end SylowW


section Fusion

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall_conj_mem {A : Subgroup G} {z : G}
    (h : ∀ u ∈ A, z⁻¹ * u * z ∈ A) : z ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj z⁻¹).toMonoidHom ≤ A := by
    rintro _ ⟨u, hu, rfl⟩
    change z⁻¹ * u * z⁻¹⁻¹ ∈ A
    rw [inv_inv]
    exact h u hu
  have heq : A.map (MulAut.conj z⁻¹).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulEquiv.injective _)])
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [← heq] at hu
    obtain ⟨v, hv, hveq⟩ := hu
    have hv' : z⁻¹ * v * z = u := by
      rw [← hveq]
      change z⁻¹ * v * z = z⁻¹ * v * z⁻¹⁻¹
      rw [inv_inv]
    rw [← hv']
    simpa [mul_assoc] using hv
  · intro hu
    have := h _ hu
    simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_isSylowOf_ge {P K : Subgroup G} (hP : IsPGroup 3 P) (hPK : P ≤ K) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S K ∧ P ≤ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩,
    fun x hx => ⟨⟨x, hPK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩⟩

theorem exists_mem_normalizer_conj_eq {A R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤)
    (hΩ : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1})
    (hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hexp : ∀ u ∈ A, u ^ 3 = 1) {x g : G}
    (hx : x ∈ A) (hxg : g⁻¹ * x * g ∈ A) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), g⁻¹ * x * g = w⁻¹ * x * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x' := g⁻¹ * x * g with hx'
  set C := Subgroup.centralizer ({x'} : Set G) with hC
  have hmemA : ∀ y ∈ R, y ^ 3 = 1 → y ∈ A := fun y hy hy3 => by
    rw [hΩ]
    exact Subgroup.subset_closure ⟨hy, hy3⟩
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have hAC : A ≤ C := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x' hxg u hu).symm
  set Ag := A.map (MulAut.conj g⁻¹).toMonoidHom with hAg
  have hAg_mem : ∀ u ∈ A, g⁻¹ * u * g ∈ Ag := fun u hu => ⟨u, hu, by
    change g⁻¹ * u * g⁻¹⁻¹ = g⁻¹ * u * g
    rw [inv_inv]⟩
  have hAgC : Ag ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    change g⁻¹ * u * g⁻¹⁻¹ ∈ C
    rw [inv_inv, hC, Subgroup.mem_centralizer_singleton_iff, hx']
    have h1 := hcomm x hx u hu
    calc g⁻¹ * u * g * (g⁻¹ * x * g) = g⁻¹ * (u * x) * g := by group
      _ = g⁻¹ * (x * u) * g := by rw [h1]
      _ = g⁻¹ * x * g * (g⁻¹ * u * g) := by group
  have hAg3 : IsPGroup 3 Ag := hA3.map _
  obtain ⟨S₁, hS₁, hAS₁⟩ := exists_isSylowOf_ge hA3 hAC
  obtain ⟨S₂, hS₂, hAgS₂⟩ := exists_isSylowOf_ge hAg3 hAgC
  obtain ⟨k, hkC, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hS₁ hS₂
  obtain ⟨T, hT, hS₁T⟩ := exists_isSylowOf_ge hS₁.isPGroup (le_top : S₁ ≤ ⊤)
  obtain ⟨y, -, hy⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hR hT
  have hconj3 : ∀ (z u : G), u ^ 3 = 1 → (z⁻¹ * u * z) ^ 3 = 1 := by
    intro z u hu
    rw [show z⁻¹ * u * z = z⁻¹ * u * z⁻¹⁻¹ by rw [inv_inv], conj_pow, hu]
    group
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    have h1 : ∀ u ∈ A, y⁻¹ * u * y ∈ A := fun u hu =>
      hmemA _ ((hy u).mp (hS₁T (hAS₁ hu))) (hconj3 y u (hexp u hu))
    exact mem_normalizer_of_forall_conj_mem h1
  have hgkyN : g * k * y ∈ Subgroup.normalizer (A : Set G) := by
    have h1 : ∀ u ∈ A, (g * k * y)⁻¹ * u * (g * k * y) ∈ A := by
      intro u hu
      have h2 : k⁻¹ * (g⁻¹ * u * g) * k ∈ S₁ := (hk _).mp (hAgS₂ (hAg_mem u hu))
      have h3 := (hy _).mp (hS₁T h2)
      have h4 : (g * k * y)⁻¹ * u * (g * k * y) = y⁻¹ * (k⁻¹ * (g⁻¹ * u * g) * k) * y := by
        group
      rw [h4]
      refine hmemA _ h3 ?_
      rw [← h4]
      exact hconj3 _ u (hexp u hu)
    exact mem_normalizer_of_forall_conj_mem h1
  refine ⟨g * k, ?_, ?_⟩
  · have := Subgroup.mul_mem _ hgkyN (Subgroup.inv_mem _ hyN)
    simpa [mul_assoc] using this
  · have hkx : k * x' = x' * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
    calc x' = k⁻¹ * (k * x') := by group
      _ = k⁻¹ * (x' * k) := by rw [hkx]
      _ = (g * k)⁻¹ * x * (g * k) := by rw [hx']; group

theorem isSylowOf_top_of_isSylowOf_normalizer {A R : Subgroup G}
    (hRW : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.normalizer (A : Set G)))
    (hΩ : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}) :
    CFSG.ABGLocalTools.IsSylowOf 3 R ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sec12.isSylowOf_of_normalizer_le hRW le_top ?_
  rintro z ⟨-, hz⟩
  apply mem_normalizer_of_forall_conj_mem
  intro u hu
  have hz' : z⁻¹ ∈ Subgroup.normalizer (R : Set G) := Subgroup.inv_mem _ hz
  rw [hΩ] at hu ⊢
  have hle : Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} ≤
      (Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}).comap (MulAut.conj z⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyR, hy3⟩
    apply Subgroup.subset_closure
    refine ⟨(Subgroup.mem_normalizer_iff.mp hz' y).mp hyR, ?_⟩
    change (z⁻¹ * y * z⁻¹⁻¹) ^ 3 = 1
    rw [conj_pow, hy3]
    group
  have h1 : (MulAut.conj z⁻¹).toMonoidHom u ∈ Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} :=
    hle hu
  change z⁻¹ * u * z⁻¹⁻¹ ∈ Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} at h1
  rwa [inv_inv] at h1

end Fusion

end CFSG.RankThree.PartTwo.Sec11
