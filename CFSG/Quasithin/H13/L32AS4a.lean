module

public import CFSG.Quasithin.H13.A6Nu
public import CFSG.Quasithin.H13.L32A72d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem relIndex_cfix_sup_mul [Finite G] (c : G) {X Y Z : Subgroup G} (hYZ : Y ≤ Z) (hZX : Z ≤ X)
    (hNY : cfix c X ≤ Subgroup.normalizer (Y : Set G))
    (hNZ : cfix c X ≤ Subgroup.normalizer (Z : Set G)) :
    (cfix c X ⊔ Y).relIndex X = (cfix c X ⊔ Z).relIndex X * (cfix c Z ⊔ Y).relIndex Z := by
  have hNY' : cfix c Z ≤ Subgroup.normalizer (Y : Set G) :=
    (inf_le_inf_right _ hZX).trans hNY
  have h1 := nu_mul c (hYZ.trans hZX) hNY
  have h2 := nu_mul c hZX hNZ
  have h3 := nu_mul c hYZ hNY'
  have hpos : nu c Y ≠ 0 := by
    unfold nu
    show ((cfix c Y).subgroupOf Y).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  rw [h2, h3, ← mul_assoc] at h1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h1).symm

theorem mem_cfix_sup_iff [Finite G] {c : G} (hc : c ^ 3 = 1) {X Y : Subgroup G} (hYX : Y ≤ X)
    (hY : ¬ 3 ∣ Nat.card Y) (hcY : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (s : G) :
    s ∈ cfix c X ⊔ Y ↔ s ∈ X ∧ c * s * c⁻¹ * s⁻¹ ∈ Y := by
  have hconj : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hXY hx) y).mp hy
  constructor
  · intro hs
    let P : Subgroup G :=
      { carrier := {s | s ∈ X ∧ c * s * c⁻¹ * s⁻¹ ∈ Y}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨X.mul_mem ha hb, ?_⟩
          have e : c * (a * b) * c⁻¹ * (a * b)⁻¹ =
              (c * a * c⁻¹ * a⁻¹) * (a * (c * b * c⁻¹ * b⁻¹) * a⁻¹) := by group
          rw [e]
          exact Y.mul_mem ha' (hconj a ha _ hb')
        one_mem' := ⟨X.one_mem, by simp⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨X.inv_mem ha, ?_⟩
          have e : c * a⁻¹ * c⁻¹ * a⁻¹⁻¹ = a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
          rw [e]
          exact hconj _ (X.inv_mem ha) _ (Y.inv_mem ha') }
    have hle : cfix c X ⊔ Y ≤ P := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · obtain ⟨hxX, hxc⟩ := mem_cfix.mp hx
        refine ⟨hxX, ?_⟩
        rw [hxc, mul_inv_cancel_right, mul_inv_cancel]
        exact Y.one_mem
      · exact ⟨hYX hy, Y.mul_mem (hcY y hy) (Y.inv_mem hy)⟩
    exact hle hs
  · rintro ⟨hsX, hsc⟩
    have hx : s⁻¹ * (c * s * c⁻¹) ∈ Y := by
      have e : s⁻¹ * (c * s * c⁻¹) = s⁻¹ * (c * s * c⁻¹ * s⁻¹) * s⁻¹⁻¹ := by group
      rw [e]
      exact hconj _ (X.inv_mem hsX) _ hsc
    obtain ⟨n, hn, hcn⟩ := exists_comm_mul_of_conj_mem hc hY hcY hx
    have hsn : s * n ∈ cfix c X := by
      refine mem_cfix.mpr ⟨X.mul_mem hsX (hYX hn), ?_⟩
      calc c * (s * n) = c * (s * n) * c⁻¹ * c := by group
        _ = s * n * c := by rw [hcn]
    have e : s = (s * n) * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hsn) (Subgroup.mem_sup_right (Y.inv_mem hn))

theorem cfix_sup_eq_of_comm_le [Finite G] {c : G} (hc : c ^ 3 = 1) {X Y : Subgroup G}
    (hYX : Y ≤ X) (hY : ¬ 3 ∣ Nat.card Y) (hcY : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hcomm : ∀ s ∈ X, c * s * c⁻¹ * s⁻¹ ∈ Y) :
    cfix c X ⊔ Y = X :=
  le_antisymm (sup_le inf_le_left hYX) fun s hs =>
    (mem_cfix_sup_iff hc hYX hY hcY hXY s).mpr ⟨hs, hcomm s hs⟩

theorem cfix_sup_eq_of_fpf' {c : G} {X Y : Subgroup G}
    (hfp : ∀ s ∈ X, c * s * c⁻¹ * s⁻¹ ∈ Y → s ∈ Y) : cfix c X ⊔ Y = Y :=
  cfix_sup_eq_of_fpf hfp

private theorem mul_pow_of_comm' {v m : G} (h : v * m = m * v) (k : ℕ) :
    (v * m) ^ k = v ^ k * m ^ k :=
  (Commute.mul_pow h k)

theorem exists_card_four_of_lt [Finite G] {B Y V₁ : Subgroup G} (hB : IsPGroup 2 B)
    (hY : IsPGroup 2 Y) (hlt : V₁ < Y) (hV₁ : Nat.card V₁ = 2)
    (hcent : ∀ v ∈ V₁, ∀ y ∈ Y, v * y = y * v) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hBV : B ≤ Subgroup.normalizer (V₁ : Set G)) :
    ∃ D : Subgroup G, V₁ < D ∧ D ≤ Y ∧ Nat.card D = 4 ∧
      B ≤ Subgroup.normalizer (D : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVY : V₁ ≤ Y := hlt.le
  have hYV : Y ≤ Subgroup.normalizer (V₁ : Set G) := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [← hcent v hv y hy, mul_inv_cancel_right]
      exact hv
    · intro hv
      have h1 := hcent _ hv y hy
      have e : v = y * v * y⁻¹ := by
        calc v = y⁻¹ * (y * v * y⁻¹ * y) := by group
          _ = y⁻¹ * (y * (y * v * y⁻¹)) := by rw [h1]
          _ = y * v * y⁻¹ := by group
      rwa [← e] at hv
  obtain ⟨m, hmY, hmV, hmB⟩ := exists_mem_fix_mod hVY hlt.ne hB hY hBY hBV hYV
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hY) ⟨m, hmY⟩
  have hex : ∃ j : ℕ, m ^ (2 ^ j) ∈ V₁ := by
    refine ⟨n, ?_⟩
    have h1 : (⟨m, hmY⟩ : ↥Y) ^ (2 ^ n) = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one _
    have h2 : m ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [h2]
    exact V₁.one_mem
  set j₀ := Nat.find hex with hj₀
  have hj₀mem : m ^ (2 ^ j₀) ∈ V₁ := Nat.find_spec hex
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · exfalso
      rw [h, pow_zero, pow_one] at hj₀mem
      exact hmV hj₀mem
    · exact h
  set m' := m ^ (2 ^ (j₀ - 1)) with hm'
  have hm'V : m' ∉ V₁ := Nat.find_min hex (by omega)
  have hm'Y : m' ∈ Y := Y.pow_mem hmY _
  have hm'2 : m' ^ 2 ∈ V₁ := by
    rw [hm', ← pow_mul, ← pow_succ, show j₀ - 1 + 1 = j₀ by omega]
    exact hj₀mem
  have hm'B : ∀ b ∈ B, b * m' * b⁻¹ * m'⁻¹ ∈ V₁ := by
    intro b hb
    set v := b * m * b⁻¹ * m⁻¹ with hv
    have hvV : v ∈ V₁ := hmB b hb
    have hbm : b * m * b⁻¹ = v * m := by rw [hv]; group
    have hconj : b * m' * b⁻¹ = (b * m * b⁻¹) ^ (2 ^ (j₀ - 1)) := by
      rw [hm', conj_pow]
    rw [hconj, hbm, mul_pow_of_comm' (hcent v hvV m hmY), mul_inv_cancel_right]
    exact V₁.pow_mem hvV _
  set D := Subgroup.zpowers m' ⊔ V₁ with hD
  have hm'D : m' ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers m')
  have hVD : V₁ ≤ D := le_sup_right
  have hZV : Subgroup.zpowers m' ≤ Subgroup.normalizer (V₁ : Set G) :=
    (Subgroup.zpowers_le.mpr hm'Y).trans hYV
  refine ⟨D, lt_of_le_of_ne hVD fun h => hm'V (h ▸ hm'D),
    sup_le (Subgroup.zpowers_le.mpr hm'Y) hVY, ?_, ?_⟩
  ·
    have hprod := card_sup_mul_card_inf' hZV
    rw [← hD, hV₁] at hprod
    have hm'1 : m' ≠ 1 := fun h => hm'V (h ▸ V₁.one_mem)
    by_cases hsq : m' ^ 2 = 1
    · have hord : orderOf m' = 2 := orderOf_eq_prime hsq hm'1
      have hcz : Nat.card (Subgroup.zpowers m') = 2 := by
        rw [Nat.card_zpowers, hord]
      have hinf : Subgroup.zpowers m' ⊓ V₁ = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hx, hxV⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have hk : m' ^ k = m' ^ (k % 2) := by
          rw [← zpow_mod_orderOf, hord]
          norm_cast
        rw [hk] at hxV ⊢
        have : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases this with h0 | h1
        · rw [h0, zpow_zero]
          exact Subgroup.one_mem _
        · rw [h1, zpow_one] at hxV
          exact absurd hxV hm'V
      rw [hcz, hinf, Subgroup.card_bot] at hprod
      omega
    ·
      have hV1le : V₁ ≤ Subgroup.zpowers m' := by
        intro v hv
        have hcard2 : Nat.card V₁ = 2 := hV₁
        have hm'2ne : (⟨m' ^ 2, hm'2⟩ : ↥V₁) ≠ 1 := fun h => hsq (congrArg Subtype.val h)
        obtain ⟨w, hw⟩ : ∃ w : ↥V₁, w ≠ 1 := ⟨_, hm'2ne⟩
        by_cases hv1 : v = 1
        · rw [hv1]
          exact Subgroup.one_mem _
        · have : (⟨v, hv⟩ : ↥V₁) = ⟨m' ^ 2, hm'2⟩ := by
            have hc := hcard2
            rw [Nat.card_eq_two_iff] at hc
            obtain ⟨a, b, hab, hab'⟩ := hc
            have hva : (⟨v, hv⟩ : ↥V₁) ∈ ({a, b} : Set ↥V₁) := hab' ▸ Set.mem_univ _
            have hma : (⟨m' ^ 2, hm'2⟩ : ↥V₁) ∈ ({a, b} : Set ↥V₁) := hab' ▸ Set.mem_univ _
            have h1a : (1 : ↥V₁) ∈ ({a, b} : Set ↥V₁) := hab' ▸ Set.mem_univ _
            have hv1' : (⟨v, hv⟩ : ↥V₁) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hva hma h1a
            rcases h1a with h1a | h1a <;> rcases hva with hva | hva <;>
              rcases hma with hma | hma
            all_goals first
              | exact absurd (hva.trans h1a.symm) hv1'
              | exact absurd (hma.trans h1a.symm) hm'2ne
              | exact hva.trans hma.symm
          have hv' : v = m' ^ 2 := congrArg Subtype.val this
          rw [hv']
          exact Subgroup.npow_mem_zpowers m' 2
      have hinf : Subgroup.zpowers m' ⊓ V₁ = V₁ := inf_eq_right.mpr hV1le
      have h4 : m' ^ 4 = 1 := by
        have h1 : (m' ^ 2) ^ 2 = 1 := by
          have := pow_card_eq_one' (x := (⟨m' ^ 2, hm'2⟩ : ↥V₁))
          rw [hV₁] at this
          exact congrArg Subtype.val this
        rw [← pow_mul] at h1
        exact h1
      have hord : orderOf m' = 4 := by
        have hdvd : orderOf m' ∣ 4 := orderOf_dvd_of_pow_eq_one h4
        have hne2 : ¬ orderOf m' ∣ 2 := fun h => hsq (orderOf_dvd_iff_pow_eq_one.mp h)
        have h4' : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4'] at hdvd
        obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        interval_cases i
        · rw [hio] at hne2
          exact absurd (one_dvd 2) hne2
        · rw [hio] at hne2
          exact absurd dvd_rfl hne2
        · rw [hio]
          norm_num
      have hcz : Nat.card (Subgroup.zpowers m') = 4 := by
        rw [Nat.card_zpowers, hord]
      rw [hcz, hinf, hV₁] at hprod
      omega
  ·
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [hD, Subgroup.map_sup, sup_le_iff]
      constructor
      · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        show b * m' * b⁻¹ ∈ D
        have e : b * m' * b⁻¹ = (b * m' * b⁻¹ * m'⁻¹) * m' := by group
        rw [e]
        exact D.mul_mem (hVD (hm'B b hb)) hm'D
      · rw [(Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBV hb))]
        exact hVD
    · rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]

end CFSG.Quasithin.H13.L32A
