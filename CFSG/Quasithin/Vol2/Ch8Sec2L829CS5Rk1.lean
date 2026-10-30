module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Def
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Grp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Rk1

variable {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ}

theorem RankOneSyl.mem_of_two_elt [Finite Y] (hR : RankOneSyl X S q) {x : Y} (hxX : x ∈ X)
    (hxN : x ∈ Subgroup.normalizer (S : Set Y)) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ S :=
  mem_of_normalizes_sylowTwo_cs5 hR.sylow hxX hxN hx2

theorem RankOneSyl.trans [Finite Y] (hR : RankOneSyl X S q) {g₁ g₂ : Y} (hg₁ : g₁ ∈ X)
    (hg₁N : g₁ ∉ Subgroup.normalizer (S : Set Y)) (hg₂ : g₂ ∈ X)
    (hg₂N : g₂ ∉ Subgroup.normalizer (S : Set Y)) :
    ∃ s ∈ S, (s * g₁)⁻¹ * g₂ ∈ Subgroup.normalizer (S : Set Y) := by
  classical
  have hSX : S ≤ X := hR.le
  have hSN : S ≤ Subgroup.normalizer (S : Set Y) := Subgroup.le_normalizer
  set B' : Subgroup ↥X := (X ⊓ Subgroup.normalizer (S : Set Y)).subgroupOf X with hB'
  have hmemB' : ∀ a : ↥X, a ∈ B' ↔ (a : Y) ∈ Subgroup.normalizer (S : Set Y) := by
    intro a
    rw [hB', Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  let ω₀ : ↥X ⧸ B' := QuotientGroup.mk 1
  have hcard : Nat.card (↥X ⧸ B') = Nat.card S + 1 := hR.index
  have hne : ∀ a : ↥X, a ∉ B' → (QuotientGroup.mk a : ↥X ⧸ B') ≠ ω₀ := by
    intro a ha h
    apply ha
    have := (QuotientGroup.eq (a := a) (b := 1)).mp h
    simpa using this
  let φ : ↥S → {ω : ↥X ⧸ B' // ω ≠ ω₀} := fun s =>
    ⟨QuotientGroup.mk (⟨s * g₁, X.mul_mem (hSX s.2) hg₁⟩ : ↥X), hne _ (by
      rw [hmemB']
      intro h
      apply hg₁N
      have h2 : (s : Y)⁻¹ * (s * g₁) ∈ Subgroup.normalizer (S : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hSN s.2)) h
      simpa using h2)⟩
  have hinj : Function.Injective φ := by
    intro s s' hss
    have h1 : (QuotientGroup.mk (⟨s * g₁, X.mul_mem (hSX s.2) hg₁⟩ : ↥X) : ↥X ⧸ B') =
        QuotientGroup.mk (⟨s' * g₁, X.mul_mem (hSX s'.2) hg₁⟩ : ↥X) := congrArg Subtype.val hss
    have h2 := (QuotientGroup.eq).mp h1
    rw [hmemB'] at h2
    set t : Y := (s : Y)⁻¹ * s' with ht
    have htS : t ∈ S := S.mul_mem (S.inv_mem s.2) s'.2
    have h3 : g₁⁻¹ * t * g₁ ∈ Subgroup.normalizer (S : Set Y) := by
      have : (g₁⁻¹ * (s : Y)⁻¹) * (s' * g₁) = g₁⁻¹ * t * g₁ := by simp [ht, mul_assoc]
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, this] using h2
    obtain ⟨k, hk⟩ := exists_two_pow_eq_one_of_mem_cs5 hR.isPGroup htS
    have h4 : g₁⁻¹ * t * g₁ ∈ S :=
      hR.mem_of_two_elt (X.mul_mem (X.mul_mem (X.inv_mem hg₁) (hSX htS)) hg₁) h3
        ⟨k, pow_two_pow_conj_cs5 g₁ t hk⟩
    have h5 : t ∈ S ⊓ B6.conjSub g₁ S := ⟨htS, B6.mem_conjSub.mpr h4⟩
    rw [hR.ti g₁ hg₁ hg₁N] at h5
    have h6 : t = 1 := h5
    exact Subtype.ext (inv_mul_eq_one.mp h6)
  have hcard' : Nat.card {ω : ↥X ⧸ B' // ω ≠ ω₀} = Nat.card S := by
    have h1 := Nat.card_congr (Equiv.optionSubtypeNe ω₀)
    rw [Finite.card_option, hcard] at h1
    omega
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by rw [hcard'])
  have hω₂ := hne (⟨g₂, hg₂⟩ : ↥X) (by rw [hmemB']; exact hg₂N)
  obtain ⟨s, hs⟩ := hbij.2 ⟨_, hω₂⟩
  refine ⟨(s : Y), s.2, ?_⟩
  have h1 : (QuotientGroup.mk (⟨s * g₁, X.mul_mem (hSX s.2) hg₁⟩ : ↥X) : ↥X ⧸ B') =
      QuotientGroup.mk (⟨g₂, hg₂⟩ : ↥X) := congrArg Subtype.val hs
  have h2 := QuotientGroup.eq.mp h1
  rw [hmemB'] at h2
  simpa [mul_assoc] using h2

theorem mem_normalizer_conjSub_cs5 {S : Subgroup Y} {g x : Y} :
    x ∈ Subgroup.normalizer ((B6.conjSub g S : Subgroup Y) : Set Y) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (S : Set Y) := by
  simp only [Subgroup.mem_normalizer_iff, B6.mem_conjSub]
  constructor
  · intro H k
    have := H (g * k * g⁻¹)
    simpa [mul_assoc] using this
  · intro H h
    have := H (g⁻¹ * h * g)
    simpa [mul_assoc] using this

@[expose] def twoPtStab (X S : Subgroup Y) (g : Y) : Subgroup Y :=
  X ⊓ Subgroup.normalizer (S : Set Y) ⊓ Subgroup.normalizer ((B6.conjSub g S : Subgroup Y) : Set Y)

theorem RankOneSyl.eq_one_of_two_elt_twoPtStab [Finite Y] (hR : RankOneSyl X S q) {g : Y}
    (hg : g ∈ X) (hgN : g ∉ Subgroup.normalizer (S : Set Y)) {x : Y}
    (hx : x ∈ twoPtStab X S g) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨⟨hxX, hxN⟩, hxN'⟩ := hx
  have h1 : x ∈ S := hR.mem_of_two_elt hxX hxN hx2
  have hconj : g⁻¹ * x * g ∈ Subgroup.normalizer (S : Set Y) :=
    mem_normalizer_conjSub_cs5.mp hxN'
  obtain ⟨k, hk⟩ := hx2
  have h2 : g⁻¹ * x * g ∈ S :=
    hR.mem_of_two_elt (X.mul_mem (X.mul_mem (X.inv_mem hg) hxX) hg) hconj
      ⟨k, pow_two_pow_conj_cs5 g x hk⟩
  have h3 : x ∈ S ⊓ B6.conjSub g S := ⟨h1, B6.mem_conjSub.mpr h2⟩
  rw [hR.ti g hg hgN] at h3
  exact h3

theorem RankOneSyl.fpf [Finite Y] (hR : RankOneSyl X S q) {g : Y} (hg : g ∈ X)
    (hgN : g ∉ Subgroup.normalizer (S : Set Y)) {s : Y} (hs : s ∈ S)
    (hc : ∀ d ∈ twoPtStab X S g, d * s = s * d) : s = 1 := by
  have hSX : S ≤ X := hR.le
  have hSN : S ≤ Subgroup.normalizer (S : Set Y) := Subgroup.le_normalizer
  have hfac : ∀ b ∈ X ⊓ Subgroup.normalizer (S : Set Y), ∃ s₀ ∈ S, ∃ d ∈ twoPtStab X S g,
      b = s₀ * d := by
    intro b hb
    have hbg : b * g ∈ X := X.mul_mem hb.1 hg
    have hbgN : b * g ∉ Subgroup.normalizer (S : Set Y) := by
      intro h
      apply hgN
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb.2) h
      simpa using this
    obtain ⟨s₀, hs₀, h⟩ := hR.trans hg hgN hbg hbgN
    refine ⟨s₀, hs₀, s₀⁻¹ * b, ⟨⟨X.mul_mem (X.inv_mem (hSX hs₀)) hb.1,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hSN hs₀)) hb.2⟩, ?_⟩, by simp⟩
    refine mem_normalizer_conjSub_cs5.mpr ?_
    have : g⁻¹ * (s₀⁻¹ * b) * g = (s₀ * g)⁻¹ * (b * g) := by simp [mul_assoc]
    rw [this]
    exact h
  have hZ : ∀ z ∈ centerSub S, z ≠ 1 → ∃ d ∈ twoPtStab X S g, d * z ≠ z * d := by
    intro z hz hz1
    by_contra hcon
    push Not at hcon
    have hall : ∀ z' ∈ centerSub S, z' ≠ 1 → z' = z := by
      intro z' hz' hz'1
      obtain ⟨b, hb, hbz⟩ := hR.ztrans z hz hz1 z' hz' hz'1
      obtain ⟨s₀, hs₀, d, hd, rfl⟩ := hfac b hb
      obtain ⟨hzS, hzc⟩ := mem_centerSub_cs5.mp hz
      rw [← hbz]
      have hdz := hcon d hd
      have hdz' : d * z * d⁻¹ = z := by rw [hdz]; group
      calc s₀ * d * z * (s₀ * d)⁻¹ = s₀ * (d * z * d⁻¹) * s₀⁻¹ := by group
        _ = s₀ * z * s₀⁻¹ := by rw [hdz']
        _ = z := by rw [hzc s₀ hs₀]; simp
    have hsub : ((centerSub S : Subgroup Y) : Set Y) ⊆ {1, z} := by
      intro z' hz'
      by_cases h1 : z' = 1
      · simp [h1]
      · simp [hall z' hz' h1]
    have hle : Nat.card (centerSub S) ≤ 2 := by
      have hnc : Nat.card (centerSub S) = Set.ncard ((centerSub S : Subgroup Y) : Set Y) :=
        Nat.card_coe_set_eq _
      rw [hnc]
      calc Set.ncard ((centerSub S : Subgroup Y) : Set Y) ≤ Set.ncard ({1, z} : Set Y) :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          have := Set.ncard_insert_le (1 : Y) ({z} : Set Y)
          simpa using this
    have := hR.zcard
    have := hR.three_le
    omega
  by_contra hs1
  obtain ⟨k, hk⟩ := exists_two_pow_eq_one_of_mem_cs5 hR.isPGroup hs
  classical
  have hex : ∃ m : ℕ, s ^ 2 ^ m = 1 := ⟨k, hk⟩
  have hm : s ^ 2 ^ (Nat.find hex) = 1 := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hm
    exact hs1 (by simpa using hm)
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, Nat.find hex = m' + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hlt : ¬ s ^ 2 ^ m' = 1 := Nat.find_min hex (by omega)
  have ht2 : s ^ 2 ^ m' * s ^ 2 ^ m' = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [hm'] at hm
    exact hm
  have htS : s ^ 2 ^ m' ∈ S := S.pow_mem hs _
  have htZ : s ^ 2 ^ m' ∈ centerSub S := hR.omega1 _ htS ht2
  obtain ⟨d, hd, hdne⟩ := hZ _ htZ hlt
  apply hdne
  have : d * s = s * d := hc d hd
  exact (Commute.pow_right (this : Commute d s) _).eq

theorem RankOneSyl.rigidity [Finite Y] [X.Normal] (hR : RankOneSyl X S q)
    (hC : ∀ y : Y, (∀ x ∈ X, y * x = x * y) → y = 1) {y : Y}
    (hy : ∀ b ∈ X ⊓ Subgroup.normalizer (S : Set Y), y * b = b * y) : y = 1 := by
  have hSX : S ≤ X := hR.le
  have hSN : S ≤ Subgroup.normalizer (S : Set Y) := Subgroup.le_normalizer
  have hyB : ∀ b ∈ X ⊓ Subgroup.normalizer (S : Set Y), y * b * y⁻¹ = b := by
    intro b hb
    rw [hy b hb]
    group
  have hyc : y ∈ Subgroup.centralizer (S : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => (hy h ⟨hSX hh, hSN hh⟩).symm
  have hyN : y ∈ Subgroup.normalizer (S : Set Y) := Subgroup.centralizer_le_normalizer _ hyc
  have claim1 : ∀ g ∈ X, g⁻¹ * (y * g * y⁻¹) ∈ Subgroup.normalizer (S : Set Y) := by
    intro g hg
    by_cases hgN : g ∈ Subgroup.normalizer (S : Set Y)
    · have h1 : y * g * y⁻¹ = g := hyB g ⟨hg, hgN⟩
      rw [h1]
      simp
    · have hg₂ : y * g * y⁻¹ ∈ X := Subgroup.Normal.conj_mem inferInstance g hg y
      have hg₂N : y * g * y⁻¹ ∉ Subgroup.normalizer (S : Set Y) := by
        intro h
        apply hgN
        have e : y * (y * g * y⁻¹) = y * g := by rw [hy _ ⟨hg₂, h⟩]; group
        have e2 : y * g * y⁻¹ = g := mul_left_cancel e
        rwa [e2] at h
      obtain ⟨s, hs, hsg⟩ := hR.trans hg hgN hg₂ hg₂N
      have hcomm : ∀ d ∈ twoPtStab X S g, d * s = s * d := by
        intro d hd
        obtain ⟨⟨hdX, hdN⟩, hdN'⟩ := hd
        have hyd : y⁻¹ * d * y = d := by
          have := hy d ⟨hdX, hdN⟩
          calc y⁻¹ * d * y = y⁻¹ * (d * y) := by group
            _ = y⁻¹ * (y * d) := by rw [this]
            _ = d := by group
        have h1 : d ∈ Subgroup.normalizer ((B6.conjSub (y * g * y⁻¹) S : Subgroup Y) : Set Y) := by
          refine mem_normalizer_conjSub_cs5.mpr ?_
          have e : (y * g * y⁻¹)⁻¹ * d * (y * g * y⁻¹) = y * (g⁻¹ * d * g) * y⁻¹ := by
            calc (y * g * y⁻¹)⁻¹ * d * (y * g * y⁻¹) = y * g⁻¹ * (y⁻¹ * d * y) * g * y⁻¹ := by group
              _ = y * g⁻¹ * d * g * y⁻¹ := by rw [hyd]
              _ = y * (g⁻¹ * d * g) * y⁻¹ := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN (mem_normalizer_conjSub_cs5.mp hdN'))
            (Subgroup.inv_mem _ hyN)
        have h2 : (s * g)⁻¹ * d * (s * g) ∈ Subgroup.normalizer (S : Set Y) := by
          have h1' := mem_normalizer_conjSub_cs5.mp h1
          set n := (s * g)⁻¹ * (y * g * y⁻¹) with hn
          have e : (s * g)⁻¹ * d * (s * g) =
              n * ((y * g * y⁻¹)⁻¹ * d * (y * g * y⁻¹)) * n⁻¹ := by
            simp only [hn]
            group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsg h1') (Subgroup.inv_mem _ hsg)
        have h3 : s⁻¹ * d * s ∈ twoPtStab X S g := by
          refine ⟨⟨X.mul_mem (X.mul_mem (X.inv_mem (hSX hs)) hdX) (hSX hs),
            Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hSN hs)) hdN) (hSN hs)⟩,
            mem_normalizer_conjSub_cs5.mpr ?_⟩
          have e : g⁻¹ * (s⁻¹ * d * s) * g = (s * g)⁻¹ * d * (s * g) := by group
          rw [e]
          exact h2
        have h4 : s⁻¹ * d * s * d⁻¹ ∈ twoPtStab X S g :=
          Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ ⟨⟨hdX, hdN⟩, hdN'⟩)
        have h5 : s⁻¹ * d * s * d⁻¹ ∈ S := by
          have e : s⁻¹ * d * s * d⁻¹ = s⁻¹ * (d * s * d⁻¹) := by group
          rw [e]
          exact S.mul_mem (S.inv_mem hs) ((Subgroup.mem_normalizer_iff.mp hdN s).mp hs)
        obtain ⟨k, hk⟩ := exists_two_pow_eq_one_of_mem_cs5 hR.isPGroup h5
        have h6 := hR.eq_one_of_two_elt_twoPtStab hg hgN h4 ⟨k, hk⟩
        have h7 : d * s = s * d := by
          have : s⁻¹ * d * s = d := by
            have := congrArg (· * d) h6
            simpa [mul_assoc] using this
          calc d * s = s * (s⁻¹ * d * s) := by group
            _ = s * d := by rw [this]
        exact h7
      have hs1 : s = 1 := hR.fpf hg hgN hs hcomm
      subst hs1
      simpa using hsg
  let N₀ : Subgroup Y :=
    { carrier := {u | u ∈ X ∧ ∀ g ∈ X, g⁻¹ * u * g ∈ Subgroup.normalizer (S : Set Y)}
      mul_mem' := by
        rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
        refine ⟨X.mul_mem haX hbX, fun g hg => ?_⟩
        have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
        rw [e]
        exact Subgroup.mul_mem _ (ha g hg) (hb g hg)
      one_mem' := ⟨X.one_mem, fun g _ => by simpa using Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨haX, ha⟩
        refine ⟨X.inv_mem haX, fun g hg => ?_⟩
        have e : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ (ha g hg) }
  have hN₀ : N₀ = ⊥ := by
    refine hR.core N₀ (fun u hu => ⟨hu.1, ?_⟩) (fun x hx n hn => ?_)
    · simpa using hu.2 1 X.one_mem
    · refine ⟨Subgroup.Normal.conj_mem inferInstance n hn.1 x |> fun h => ?_, fun g hg => ?_⟩
      · exact h
      · have e : g⁻¹ * (x * n * x⁻¹) * g = (x⁻¹ * g)⁻¹ * n * (x⁻¹ * g) := by group
        rw [e]
        exact hn.2 _ (X.mul_mem (X.inv_mem hx) hg)
  have hy1 : ∀ x ∈ X, y * x * y⁻¹ = x := by
    intro x hx
    have huX : x⁻¹ * (y * x * y⁻¹) ∈ X :=
      X.mul_mem (X.inv_mem hx) (Subgroup.Normal.conj_mem inferInstance x hx y)
    have hu : x⁻¹ * (y * x * y⁻¹) ∈ N₀ := by
      refine ⟨huX, fun g hg => ?_⟩
      have a1 := claim1 (x * g) (X.mul_mem hx hg)
      have a2 := claim1 g hg
      have e : g⁻¹ * (x⁻¹ * (y * x * y⁻¹)) * g =
          ((x * g)⁻¹ * (y * (x * g) * y⁻¹)) * (g⁻¹ * (y * g * y⁻¹))⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ a1 (Subgroup.inv_mem _ a2)
    rw [hN₀] at hu
    have h1 : x⁻¹ * (y * x * y⁻¹) = 1 := hu
    have := congrArg (x * ·) h1
    simpa using this
  exact hC y fun x hx => by
    have := hy1 x hx
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [this]


end Rk1

end CFSG.Quasithin.H13
