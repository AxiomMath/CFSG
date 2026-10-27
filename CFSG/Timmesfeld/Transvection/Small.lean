module

public import CFSG.Timmesfeld.Transvection.QTwoSimple
public import CFSG.Timmesfeld.Transvection.LineSpan
public import CFSG.Timmesfeld.ARS.Sec4Defs

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

theorem eq_top_or_eq_top_of_forall_le (hΔ : IsRootClass Δ) {U V : Subgroup H}
    (h : ∀ W ∈ Δ, W ≤ U ∨ W ≤ V) : U = ⊤ ∨ V = ⊤ := by
  have htop : ∀ g : H, g ∈ gen Δ := fun g => by
    rw [gen, hΔ.gen]
    exact Subgroup.mem_top g
  by_cases hU : ∀ W ∈ Δ, W ≤ U
  · left
    rw [eq_top_iff]
    intro g _
    exact gen_le hU (htop g)
  push Not at hU
  obtain ⟨W₀, hW₀, hW₀U⟩ := hU
  right
  set 𝒜 : Set (Subgroup H) := {W | W ∈ Δ ∧ ¬ W ≤ U} with h𝒜
  have hnorm : ∀ g : H, ∀ y ∈ gen 𝒜, g * y * g⁻¹ ∈ gen 𝒜 := by
    intro g
    refine gen_induction (p := fun g => ∀ y ∈ gen 𝒜, g * y * g⁻¹ ∈ gen 𝒜) (htop g) ?_ ?_ ?_
    · intro W' hW' x hx y hy
      by_cases hW'U : W' ≤ U
      · refine gen_induction (p := fun y => x * y * x⁻¹ ∈ gen 𝒜) hy ?_ ?_ ?_
        · intro W hW z hz
          have hWx : conjSub W x ∈ 𝒜 := by
            refine ⟨hΔ.conjSub_mem hW.1 x, fun hle => hW.2 fun w hw => ?_⟩
            have h1 : x * w * x⁻¹ ∈ U := hle (conj_mem_conjSub x hw)
            have hxU : x ∈ U := hW'U hx
            have h2 := U.mul_mem (U.mul_mem (U.inv_mem hxU) h1) hxU
            rwa [show x⁻¹ * (x * w * x⁻¹) * x = w by group] at h2
          exact le_gen hWx (conj_mem_conjSub x hz)
        · rw [mul_one, mul_inv_cancel]
          exact Subgroup.one_mem _
        · intro y z hy hz
          have := (gen 𝒜).mul_mem hy hz
          rwa [show x * y * x⁻¹ * (x * z * x⁻¹) = x * (y * z) * x⁻¹ by group] at this
      · have hx' : x ∈ gen 𝒜 := le_gen (show W' ∈ 𝒜 from ⟨hW', hW'U⟩) hx
        exact (gen 𝒜).mul_mem ((gen 𝒜).mul_mem hx' hy) ((gen 𝒜).inv_mem hx')
    · intro y hy
      rwa [one_mul, inv_one, mul_one]
    · intro g₁ g₂ h₁ h₂ y hy
      have := h₁ _ (h₂ y hy)
      rwa [show g₁ * (g₂ * y * g₂⁻¹) * g₁⁻¹ = g₁ * g₂ * y * (g₁ * g₂)⁻¹ by group] at this
  have hall : ∀ W ∈ Δ, W ≤ gen 𝒜 := by
    intro W hW
    obtain ⟨g, rfl⟩ := hΔ.exists_conjSub_eq hW₀ hW
    intro z hz
    have h1 : g⁻¹ * z * g ∈ gen 𝒜 := le_gen (show W₀ ∈ 𝒜 from ⟨hW₀, hW₀U⟩) (mem_conjSub.1 hz)
    have := hnorm g _ h1
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at this
  have hle : gen 𝒜 ≤ V := gen_le fun W hW => (h W hW.1).resolve_left hW.2
  rw [eq_top_iff]
  intro g _
  exact hle (gen_le hall (htop g))

theorem exists_not_commuting_both (hΔ : IsRootClass Δ) (hcen : Subgroup.center H = ⊥)
    {A B : Subgroup H} (hA : A ∈ Δ) (hB : B ∈ Δ) :
    ∃ W ∈ Δ, ¬ Commuting W A ∧ ¬ Commuting W B := by
  by_contra hno
  push Not at hno
  have h : ∀ W ∈ Δ, W ≤ Subgroup.centralizer (A : Set H) ∨
      W ≤ Subgroup.centralizer (B : Set H) := by
    intro W hW
    by_cases hWA : Commuting W A
    · exact Or.inl (commuting_iff_le_centralizer.1 hWA.symm)
    · exact Or.inr (commuting_iff_le_centralizer.1 (hno W hW hWA).symm)
  have hcentral : ∀ {C : Subgroup H}, C ∈ Δ → Subgroup.centralizer (C : Set H) = ⊤ → False := by
    intro C hC hCtop
    apply hΔ.ne_bot C hC
    rw [eq_bot_iff]
    intro c hc
    have hcz : c ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun g =>
      (Subgroup.mem_centralizer_iff.1 (hCtop ▸ Subgroup.mem_top g) c hc).symm
    rw [hcen] at hcz
    exact hcz
  rcases eq_top_or_eq_top_of_forall_le hΔ h with h1 | h1
  · exact hcentral hA h1
  · exact hcentral hB h1

theorem thickLines_of_meetsLines (hΔ : IsTransvectionClass Δ) (hcen : Subgroup.center H = ⊥)
    (hlines : MeetsLines Δ) : ThickLines Δ := by
  intro A hA B hB hAB hc
  obtain ⟨W, hW, hWA, hWB⟩ := exists_not_commuting_both hΔ.root hcen hA hB
  obtain ⟨D, ⟨hD, hDl⟩, hWD⟩ := hlines A hA B hB hAB hc W hW
  refine ⟨D, hD, ?_, ?_, hDl⟩
  · rintro rfl
    exact hWA hWD
  · rintro rfl
    exact hWB hWD

theorem eq_one_of_odd_of_sq_mem {N : Subgroup H} (h2 : IsPGroup 2 N) {x : H}
    (hodd : Odd (orderOf x)) (hx : x * x ∈ N) : x = 1 := by
  obtain ⟨k, hk⟩ := h2 ⟨x * x, hx⟩
  have hk' : x ^ (2 ^ (k + 1)) = 1 := by
    have h := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact h
  have hdvd : orderOf x ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hk'
  exact orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ (Odd.coprime_two_right hodd)) hdvd)

theorem eq_bot_of_isPGroup_two [Finite H] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hcen : Subgroup.center H = ⊥) (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ Commuting A B)
    {N : Subgroup H} (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have hiso := hΔ.noIsolated hpts hrank
  have hsq : ∀ {X : Subgroup H}, X ∈ Δ → ∀ x ∈ X, x * x = 1 := fun hX x hx =>
    hΔ.root.mul_self _ hX x hx
  have hopp : ∀ {X Y : Subgroup H}, X ∈ Δ → Y ∈ Δ → Opposite X Y → ∀ {x y : H}, x ∈ X →
      x ≠ 1 → y ∈ Y → y ≠ 1 → x * y * (x * y) ∉ N := by
    intro X Y hX hY hXY x y hx hx1 hy hy1 hN'
    have h1 := eq_one_of_odd_of_sq_mem h2 (hXY.odd_orderOf_mul (hsq hX) hx hx1 hy hy1) hN'
    have hxy : y = x := by
      have := eq_inv_of_mul_eq_one_right h1
      rwa [inv_eq_of_mul_eq_one_right (hsq hX x hx)] at this
    have hmem : x ∈ X ⊓ Y := ⟨hx, hxy ▸ hy⟩
    rw [hΔ.inf_eq_bot hiso hX hY hXY.1, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hstep1 : ∀ {A : Subgroup H}, A ∈ Δ → ∀ n ∈ N, Commuting A (conjSub A n) := by
    intro A hA n hn
    by_cases heq : conjSub A n = A
    · rw [heq]
      exact hΔ.root.commuting_self hA
    rcases hΔ.commuting_or_opposite hA (hΔ.root.conjSub_mem hA n) (Ne.symm heq) with h | h
    · exact h
    exfalso
    obtain ⟨a, ha, ha1⟩ := hΔ.root.exists_ne_one hA
    refine hopp hA (hΔ.root.conjSub_mem hA n) h ha ha1 (conj_mem_conjSub n ha)
      (fun h' => ha1 (conj_eq_one_iff.1 h')) ?_
    have h1 : a * (n * a * n⁻¹) ∈ N := by
      have : a * (n * a * n⁻¹) = (a * n * a⁻¹) * n⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right (hsq hA a ha)]
        group
      rw [this]
      exact N.mul_mem (hN.conj_mem n hn a) (N.inv_mem hn)
    exact N.mul_mem h1 h1
  have hstep2 : ∀ {A : Subgroup H}, A ∈ Δ → ∀ n ∈ N, ∀ X ∈ Δ, Commuting A X →
      Commuting (conjSub A n) X := by
    intro A hA n hn X hX hAX
    by_contra hne
    have hAn := hΔ.root.conjSub_mem hA n
    have hXne : conjSub A n ≠ X := fun h => hne (h ▸ hΔ.root.commuting_self hAn)
    have hopp' : Opposite (conjSub A n) X :=
      (hΔ.commuting_or_opposite hAn hX hXne).resolve_left hne
    have hopp'' : Opposite A (conjSub X n⁻¹) := by
      have := hopp'.conj n⁻¹
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
    have hXn := hΔ.root.conjSub_mem hX n⁻¹
    obtain ⟨a, ha, ha1⟩ := hΔ.root.exists_ne_one hA
    obtain ⟨x, hx, hx1⟩ := hΔ.root.exists_ne_one hX
    refine hopp hA hXn hopp'' ha ha1 (conj_mem_conjSub n⁻¹ hx)
      (fun h => hx1 (conj_eq_one_iff.1 h)) ?_
    have hcomm : a * x = x * a := hAX a ha x hx
    have hc : (a * x)⁻¹ = a * x := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq hX x hx),
        inv_eq_of_mul_eq_one_right (hsq hA a ha), hcomm]
    have hm : x⁻¹ * n⁻¹ * x * n ∈ N := by
      have h1 := hN.conj_mem n⁻¹ (N.inv_mem hn) x⁻¹
      rw [inv_inv] at h1
      exact N.mul_mem h1 hn
    have hay : a * (n⁻¹ * x * n⁻¹⁻¹) = a * x * (x⁻¹ * n⁻¹ * x * n) := by group
    rw [hay]
    have : a * x * (x⁻¹ * n⁻¹ * x * n) * (a * x * (x⁻¹ * n⁻¹ * x * n)) =
        (a * x) * (x⁻¹ * n⁻¹ * x * n) * (a * x)⁻¹ * (x⁻¹ * n⁻¹ * x * n) := by
      rw [hc]
      group
    rw [this]
    exact N.mul_mem (hN.conj_mem _ hm _) hm
  have hstep3 : ∀ {A : Subgroup H}, A ∈ Δ → ∀ n ∈ N, conjSub A n = A := fun hA n hn =>
    eq_of_commuting_subset hΔ hpts hA (hΔ.root.conjSub_mem hA n) fun C hC hAC =>
      hstep2 hA n hn C hC hAC
  have hstep4 : ∀ {A : Subgroup H}, A ∈ Δ → ∀ a ∈ A, a ∈ N → a = 1 := by
    intro A hA a ha haN
    by_contra ha1
    obtain ⟨B, hB, hAB⟩ := hiso A hA
    obtain ⟨b, hb, hb1⟩ := hΔ.root.exists_ne_one hB
    refine hopp hA hB hAB ha ha1 hb hb1 ?_
    have : a * b * (a * b) = a * (b * a * b⁻¹) := by
      rw [inv_eq_of_mul_eq_one_right (hsq hB b hb)]
      group
    rw [this]
    exact N.mul_mem haN (hN.conj_mem a haN b)
  have hcomm : ∀ n ∈ N, ∀ {A : Subgroup H}, A ∈ Δ → ∀ a ∈ A, n * a = a * n := by
    intro n hn A hA a ha
    have h1 : n * a * n⁻¹ ∈ A := by
      have := conj_mem_conjSub n ha
      rwa [hstep3 hA n hn] at this
    have h2 : n * a * n⁻¹ * a⁻¹ ∈ N := by
      have := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) a)
      rwa [show n * (a * n⁻¹ * a⁻¹) = n * a * n⁻¹ * a⁻¹ by group] at this
    have h3 := hstep4 hA _ (A.mul_mem h1 (A.inv_mem ha)) h2
    calc n * a = n * a * n⁻¹ * a⁻¹ * (a * n) := by group
      _ = a * n := by rw [h3, one_mul]
  rw [eq_bot_iff]
  intro n hn
  rw [← hcen, Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ gen Δ := by
    rw [gen, hΔ.root.gen]
    exact Subgroup.mem_top g
  exact gen_induction (p := fun g => g * n = n * g) hg
    (fun A hA a ha => (hcomm n hn hA a ha).symm) (by rw [one_mul, mul_one])
    fun y z hy hz => by rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]

theorem small_of_meetsLines {H : Type} [Group H] [Finite H] {Δ : Set (Subgroup H)}
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hcen : Subgroup.center H = ⊥)
    (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ Commuting A B) (hlines : MeetsLines Δ)
    (hO3 : ∀ N : Subgroup H, N.Normal → IsPGroup 3 N → N = ⊥) :
    (∃ A ∈ Δ, Nat.card A = 2) → IsSimpleGroup (commutator H) ∧ ThickLines Δ := by
  rintro ⟨A, hA, h2⟩
  have hthick := thickLines_of_meetsLines hΔ hcen hlines
  exact ⟨isSimpleGroup_commutator_of_card_two hΔ hcen hpts hrank hlines hthick
    (fun N hN hp => eq_bot_of_isPGroup_two hΔ hpts hcen hrank hN hp) hO3
    (fun X hX => QTwo.card_eq_two hΔ hA h2 hX), hthick⟩

end CFSG.Timmesfeld.Transvection
