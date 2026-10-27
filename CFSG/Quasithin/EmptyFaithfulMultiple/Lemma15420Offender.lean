module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Factors
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15420

variable {G : Type*} [Group G]

theorem eq_of_card_eq_two {F : Subgroup G} (hF : Nat.card F = 2) {x y : G} (hx : x ∈ F)
    (hy : y ∈ F) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  have e1 : (⟨x, hx⟩ : F) = w := hw _ (fun h => hx1 (congrArg Subtype.val h))
  have e2 : (⟨y, hy⟩ : F) = w := hw _ (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem isPGroup_zpowers_of_mul_self {a : G} (ha2 : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : a = 1
  · rw [h1, Subgroup.zpowers_one_eq_bot]
    exact IsPGroup.of_bot
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact ha2) h1

variable [Finite G]

theorem card_inf_centralizer_eq_two {U : Subgroup G} (hU : Nat.card U = 4)
    {a : G} (ha : IsPGroup 2 (Subgroup.zpowers a))
    (haN : a ∈ Subgroup.normalizer (U : Set G)) (haC : a ∉ Subgroup.centralizer (U : Set G)) :
    Nat.card (U ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := U ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hdvd : Nat.card C ∣ 4 := hU ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card C ≠ 4 := by
    intro h4
    apply haC
    have hCU : C = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hU])
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have : u ∈ C := hCU ▸ hu
    exact (Subgroup.mem_centralizer_singleton_iff.mp this.2)
  obtain ⟨c, hcU, hc1, hcC⟩ := exists_ne_one_mem_centralizer_of_isPGroup ha
    ((Subgroup.zpowers_le).mpr haN) (by rw [hU]; norm_num)
  have hcmem : c ∈ C := by
    refine ⟨hcU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hcC a (Subgroup.mem_zpowers a)).symm
  have hne1 : Nat.card C ≠ 1 := by
    intro h1
    have := (Subgroup.card_eq_one).mp h1
    rw [this] at hcmem
    exact hc1 hcmem
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at hdvd
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k <;> simp_all

theorem conj_eq_mul_of_not_mem {U : Subgroup G} (hU : Nat.card U = 4)
    (hU2 : ∀ u ∈ U, u * u = 1) {a f g : G} (ha2 : a * a = 1)
    (haN : a ∈ Subgroup.normalizer (U : Set G)) (haC : a ∉ Subgroup.centralizer (U : Set G))
    (hf : f ∈ U ⊓ Subgroup.centralizer ({a} : Set G)) (hf1 : f ≠ 1) (hg : g ∈ U)
    (hga : g ∉ Subgroup.centralizer ({a} : Set G)) : a * g * a⁻¹ = f * g := by
  have hcard := card_inf_centralizer_eq_two hU (isPGroup_zpowers_of_mul_self ha2) haN haC
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hag : a * g * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp haN g).mp hg
  have hcU : a * g * a⁻¹ * g ∈ U := U.mul_mem hag hg
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => mul_comm_of_sq_eq_one hU2 hx hy
  have hcC : a * g * a⁻¹ * g ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : a * (a * g * a⁻¹ * g) * a⁻¹ = a * g * a⁻¹ * g := by
      have h1 : a * (a * g * a⁻¹ * g) * a⁻¹ = (a * a) * g * (a * a)⁻¹ * (a * g * a⁻¹) := by
        group
      rw [h1, ha2, inv_one, one_mul, mul_one]
      exact hcomm _ hg _ hag
    calc a * g * a⁻¹ * g * a = a * (a * g * a⁻¹ * g) * a⁻¹ * a := by rw [e]
      _ = a * (a * g * a⁻¹ * g) := by group
  have hc1 : a * g * a⁻¹ * g ≠ 1 := by
    intro h
    apply hga
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hU2 g hg)
    have e : a * g * a⁻¹ = g := by
      have := eq_inv_of_mul_eq_one_left h
      rw [this, hg']
    calc g * a = a * g * a⁻¹ * a := by rw [e]
      _ = a * g := by group
  have hcf := eq_of_card_eq_two hcard ⟨hcU, hcC⟩ hf hc1 hf1
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hU2 g hg)
  calc a * g * a⁻¹ = a * g * a⁻¹ * g * g⁻¹ := by group
    _ = f * g := by rw [hcf, hg']

theorem mul_mem_centralizer_of_not_mem {U : Subgroup G} (hU : Nat.card U = 4)
    (hU2 : ∀ u ∈ U, u * u = 1) {a b : G} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a)
    (haN : a ∈ Subgroup.normalizer (U : Set G)) (hbN : b ∈ Subgroup.normalizer (U : Set G))
    (haC : a ∉ Subgroup.centralizer (U : Set G)) (hbC : b ∉ Subgroup.centralizer (U : Set G)) :
    a * b ∈ Subgroup.centralizer (U : Set G) := by
  have hcard_a := card_inf_centralizer_eq_two hU (isPGroup_zpowers_of_mul_self ha2) haN haC
  have hcard_b := card_inf_centralizer_eq_two hU (isPGroup_zpowers_of_mul_self hb2) hbN hbC
  obtain ⟨f, hf, hf1⟩ := (Subgroup.bot_or_exists_ne_one
    (U ⊓ Subgroup.centralizer ({a} : Set G))).resolve_left (by
      intro h
      rw [h, Subgroup.card_bot] at hcard_a
      omega)
  have hbf : b * f * b⁻¹ = f := by
    have h1 : b * f * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hbN f).mp hf.1
    have h2 : b * f * b⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfa : f * a = a * f := Subgroup.mem_centralizer_singleton_iff.mp hf.2
      have hba : b * a = a * b := hab.symm
      have hbia : b⁻¹ * a = a * b⁻¹ := by
        calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * a) * b⁻¹ := by rw [hab]
          _ = a * b⁻¹ := by group
      calc b * f * b⁻¹ * a = b * f * (b⁻¹ * a) := by group
        _ = b * f * (a * b⁻¹) := by rw [hbia]
        _ = b * (f * a) * b⁻¹ := by group
        _ = b * (a * f) * b⁻¹ := by rw [hfa]
        _ = (b * a) * f * b⁻¹ := by group
        _ = (a * b) * f * b⁻¹ := by rw [hba]
        _ = a * (b * f * b⁻¹) := by group
    have h3 : b * f * b⁻¹ ≠ 1 := fun h => hf1 (by
      calc f = b⁻¹ * (b * f * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group)
    exact eq_of_card_eq_two hcard_a ⟨h1, h2⟩ hf h3 hf1
  have hfb : f ∈ U ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine ⟨hf.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc f * b = b * f * b⁻¹ * b := by rw [hbf]
      _ = b * f := by group
  have hsame : ∀ g ∈ U, g ∈ Subgroup.centralizer ({a} : Set G) →
      g ∈ Subgroup.centralizer ({b} : Set G) := by
    intro g hg hga
    by_cases hg1 : g = 1
    · rw [hg1]; exact Subgroup.one_mem _
    have := eq_of_card_eq_two hcard_a ⟨hg, hga⟩ hf hg1 hf1
    rw [this]
    exact hfb.2
  have hsame' : ∀ g ∈ U, g ∈ Subgroup.centralizer ({b} : Set G) →
      g ∈ Subgroup.centralizer ({a} : Set G) := by
    intro g hg hgb
    by_cases hg1 : g = 1
    · rw [hg1]; exact Subgroup.one_mem _
    have := eq_of_card_eq_two hcard_b ⟨hg, hgb⟩ hfb hg1 hf1
    rw [this]
    exact hf.2
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hga : g ∈ Subgroup.centralizer ({a} : Set G)
  · have hgb := hsame g hg hga
    have e1 : a * g = g * a := (Subgroup.mem_centralizer_singleton_iff.mp hga).symm
    have e2 : b * g = g * b := (Subgroup.mem_centralizer_singleton_iff.mp hgb).symm
    calc g * (a * b) = a * g * b := by rw [← mul_assoc, ← e1]
      _ = a * b * g := by rw [mul_assoc, ← e2, ← mul_assoc]
  · have hgb : g ∉ Subgroup.centralizer ({b} : Set G) := fun h => hga (hsame' g hg h)
    have ea := conj_eq_mul_of_not_mem hU hU2 ha2 haN haC hf hf1 hg hga
    have eb := conj_eq_mul_of_not_mem hU hU2 hb2 hbN hbC hfb hf1 hg hgb
    have hfa : a * f * a⁻¹ = f := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hf.2
      calc a * f * a⁻¹ = f * a * a⁻¹ := by rw [this]
        _ = f := by group
    have hf2 : f * f = 1 := hU2 f hf.1
    have key : (a * b) * g * (a * b)⁻¹ = g := by
      calc (a * b) * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ := by group
        _ = a * (f * g) * a⁻¹ := by rw [eb]
        _ = (a * f * a⁻¹) * (a * g * a⁻¹) := by group
        _ = f * (f * g) := by rw [hfa, ea]
        _ = g := by rw [← mul_assoc, hf2, one_mul]
    calc g * (a * b) = (a * b) * g * (a * b)⁻¹ * (a * b) := by rw [key]
      _ = (a * b) * g := by group

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {a y : G} (ha2 : a * a = 1)
    (hy : y ∈ Subgroup.zpowers a) : y = 1 ∨ y = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.mul_ediv_add_emod k 2, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem card_eq_two_mul {A H : Subgroup G} (hHA : H ≤ A) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x * x = 1) {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀H : a₀ ∉ H)
    (hmul : ∀ x ∈ A, x ∉ H → x * a₀ ∈ H) : Nat.card A = 2 * Nat.card H := by
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀H (h ▸ H.one_mem)
  have ho : orderOf a₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hA2 a₀ ha₀) ha₀1
  have hZ : Subgroup.zpowers a₀ ≤ A := Subgroup.zpowers_le.mpr ha₀
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H (Subgroup.zpowers a₀)
    (fun x hx y hy => hAc x (hHA hx) y (hZ hy))
  have hinf : H ⊓ Subgroup.zpowers a₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hyH, hyZ⟩
    rcases eq_one_or_eq_of_mem_zpowers (hA2 a₀ ha₀) hyZ with h | h
    · exact h ▸ Subgroup.one_mem _
    · exact absurd (h ▸ hyH) ha₀H
  have hsup : H ⊔ Subgroup.zpowers a₀ = A := by
    refine le_antisymm (sup_le hHA hZ) fun x hx => ?_
    by_cases hxH : x ∈ H
    · exact Subgroup.mem_sup_left hxH
    · have h1 := hmul x hx hxH
      have e : x = (x * a₀) * a₀⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers a₀)))
  rw [hsup, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, ho] at hcard
  rw [hcard, mul_comm]

theorem exists_mem_centralizer_not_mem {T A V U₁ U₂ : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hU₁V : U₁ ≤ V) (hU₂V : U₂ ≤ V)
    (hU₁ : Nat.card U₁ = 4) (hU₂ : Nat.card U₂ = 4) (hinf : U₁ ⊓ U₂ = ⊥)
    (hN₁ : A ≤ Subgroup.normalizer (U₁ : Set G)) (hN₂ : A ≤ Subgroup.normalizer (U₂ : Set G))
    (hnc : ¬ A ≤ Subgroup.centralizer (U₁ : Set G)) :
    ∃ a ∈ A, a ∈ Subgroup.centralizer (U₂ : Set G) ∧ a ∉ Subgroup.centralizer (U₁ : Set G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hAT, hAe, hAmax⟩ := hA
  have := hAe.1
  have := hV.1
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hAe.2 x hx
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    setLike_mul_comm (s := A) hx hy
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← sq]; exact hV.2 x hx
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    setLike_mul_comm (s := V) hx hy
  have hU₁2 : ∀ u ∈ U₁, u * u = 1 := fun u hu => hV2 u (hU₁V hu)
  have hU₂2 : ∀ u ∈ U₂, u * u = 1 := fun u hu => hV2 u (hU₂V hu)
  set A₁ := A ⊓ Subgroup.centralizer (U₁ : Set G) with hA₁def
  obtain ⟨a₀, ha₀A, ha₀C⟩ := Set.not_subset.mp hnc
  have ha₀A₁ : a₀ ∉ A₁ := fun h => ha₀C h.2
  have ha₀C₂ : a₀ ∉ Subgroup.centralizer (U₂ : Set G) := fun h => ha₀C (hcon a₀ ha₀A h)
  have hmul₁ : ∀ x ∈ A, x ∉ A₁ → x * a₀ ∈ A₁ := by
    intro x hx hxA₁
    have hxC : x ∉ Subgroup.centralizer (U₁ : Set G) := fun h => hxA₁ ⟨hx, h⟩
    exact ⟨A.mul_mem hx ha₀A, mul_mem_centralizer_of_not_mem hU₁ hU₁2 (hA2 x hx)
      (hA2 a₀ ha₀A) (hAc x hx a₀ ha₀A) (hN₁ hx) (hN₁ ha₀A) hxC ha₀C⟩
  have hcardA : Nat.card A = 2 * Nat.card A₁ :=
    card_eq_two_mul inf_le_left hAc hA2 ha₀A ha₀A₁ hmul₁
  have hA₁C₂ : A₁ ≤ Subgroup.centralizer (U₂ : Set G) := by
    intro x hx
    by_contra hxC
    have h1 : x * a₀ ∈ Subgroup.centralizer (U₂ : Set G) :=
      mul_mem_centralizer_of_not_mem hU₂ hU₂2 (hA2 x hx.1) (hA2 a₀ ha₀A) (hAc x hx.1 a₀ ha₀A)
        (hN₂ hx.1) (hN₂ ha₀A) hxC ha₀C₂
    have h2 : x * a₀ ∈ Subgroup.centralizer (U₁ : Set G) := hcon _ (A.mul_mem hx.1 ha₀A) h1
    have e : a₀ = x⁻¹ * (x * a₀) := by group
    exact ha₀C (e ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2) h2)
  set W := U₁ ⊔ U₂ with hWdef
  have hWV : W ≤ V := sup_le hU₁V hU₂V
  obtain ⟨hcW, hWset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ U₂
    (fun x hx y hy => hVc x (hU₁V hx) y (hU₂V hy))
  rw [← hWdef, hinf, Subgroup.card_bot, mul_one, hU₁, hU₂] at hcW
  have hA₁W : ∀ x ∈ A₁, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have hU₁C : U₁ ≤ Subgroup.centralizer ({x} : Set G) := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx.2 u hu)
    have hU₂C : U₂ ≤ Subgroup.centralizer ({x} : Set G) := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hA₁C₂ hx) u hu)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hU₁C hU₂C hy)).symm
  set B := A₁ ⊔ W with hBdef
  obtain ⟨hcB, hBset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ W hA₁W
  rw [← hBdef, hcW] at hcB
  have hBe : IsElemAbelian 2 B := by
    have hmem : ∀ x ∈ B, ∃ a ∈ A₁, ∃ w ∈ W, x = a * w := by
      intro x hx
      have hx' : x ∈ ((B : Subgroup G) : Set G) := hx
      rw [hBset] at hx'
      obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨a, ha, w, hw, rfl⟩
    refine ⟨IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, w, hw, rfl⟩ := hmem x hx
      obtain ⟨a', ha', w', hw', rfl⟩ := hmem y hy
      have h1 : w * a' = a' * w := (hA₁W a' ha' w hw).symm
      have h2 : w' * a = a * w' := (hA₁W a ha w' hw').symm
      have h3 : a * a' = a' * a := hAc a ha.1 a' ha'.1
      have h4 : w * w' = w' * w := hVc w (hWV hw) w' (hWV hw')
      calc a * w * (a' * w') = a * (w * a') * w' := by group
        _ = a * (a' * w) * w' := by rw [h1]
        _ = (a * a') * (w * w') := by group
        _ = (a' * a) * (w' * w) := by rw [h3, h4]
        _ = a' * (a * w') * w := by group
        _ = a' * (w' * a) * w := by rw [h2]
        _ = a' * w' * (a * w) := by group
    · obtain ⟨a, ha, w, hw, rfl⟩ := hmem x hx
      have h1 : w * a = a * w := (hA₁W a ha w hw).symm
      rw [sq]
      calc a * w * (a * w) = a * (w * a) * w := by group
        _ = a * (a * w) * w := by rw [h1]
        _ = (a * a) * (w * w) := by group
        _ = 1 := by rw [hA2 a ha.1, hV2 w (hWV hw), one_mul]
  have hBT : B ≤ T := sup_le (inf_le_left.trans hAT) (hWV.trans hVT)
  have hBA : Nat.card B ≤ Nat.card A := hAmax B hBT hBe
  set D₁ := U₁ ⊓ Subgroup.centralizer ({a₀} : Set G) with hD₁def
  set D₂ := U₂ ⊓ Subgroup.centralizer ({a₀} : Set G) with hD₂def
  have hD₁ : Nat.card D₁ = 2 :=
    card_inf_centralizer_eq_two hU₁ (isPGroup_zpowers_of_mul_self (hA2 a₀ ha₀A)) (hN₁ ha₀A) ha₀C
  have hD₂ : Nat.card D₂ = 2 :=
    card_inf_centralizer_eq_two hU₂ (isPGroup_zpowers_of_mul_self (hA2 a₀ ha₀A)) (hN₂ ha₀A)
      ha₀C₂
  obtain ⟨hcD, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂
    (fun x hx y hy => hVc x (hU₁V hx.1) y (hU₂V hy.1))
  have hD : Nat.card (D₁ ⊔ D₂ : Subgroup G) ≤ 4 := by
    have hpos : 0 < Nat.card (D₁ ⊓ D₂ : Subgroup G) := Nat.card_pos
    rw [hD₁, hD₂] at hcD
    nlinarith
  have hAW : A₁ ⊓ W ≤ D₁ ⊔ D₂ := by
    intro x ⟨hxA, hxW⟩
    have hx' : x ∈ ((W : Subgroup G) : Set G) := hxW
    rw [hWset] at hx'
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Set.mem_mul.mp hx'
    have hcomm : a₀ * (u₁ * u₂) = (u₁ * u₂) * a₀ := hAc a₀ ha₀A _ hxA.1
    set p := a₀ * u₁ * a₀⁻¹ with hp
    set q := a₀ * u₂ * a₀⁻¹ with hq
    have hpU : p ∈ U₁ := (Subgroup.mem_normalizer_iff.mp (hN₁ ha₀A) u₁).mp hu₁
    have hqU : q ∈ U₂ := (Subgroup.mem_normalizer_iff.mp (hN₂ ha₀A) u₂).mp hu₂
    have hpq : p * q = u₁ * u₂ := by
      calc p * q = a₀ * (u₁ * u₂) * a₀⁻¹ := by rw [hp, hq]; group
        _ = u₁ * u₂ := by rw [hcomm]; group
    have h1 : u₁⁻¹ * p = u₂ * q⁻¹ := by
      calc u₁⁻¹ * p = u₁⁻¹ * (p * q) * q⁻¹ := by group
        _ = u₂ * q⁻¹ := by rw [hpq]; group
    have h2 : u₁⁻¹ * p ∈ U₁ ⊓ U₂ :=
      ⟨U₁.mul_mem (U₁.inv_mem hu₁) hpU, h1 ▸ U₂.mul_mem hu₂ (U₂.inv_mem hqU)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    have hpe : p = u₁ := by
      calc p = u₁ * (u₁⁻¹ * p) := by group
        _ = u₁ := by rw [h2, mul_one]
    have hqe : q = u₂ := by
      have h3 : u₂ * q⁻¹ = 1 := h1 ▸ h2
      calc q = (u₂ * q⁻¹)⁻¹ * u₂ := by group
        _ = u₂ := by rw [h3, inv_one, one_mul]
    have hu₁C : u₁ ∈ D₁ := by
      refine ⟨hu₁, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc u₁ * a₀ = p * a₀ := by rw [hpe]
        _ = a₀ * u₁ := by rw [hp]; group
    have hu₂C : u₂ ∈ D₂ := by
      refine ⟨hu₂, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc u₂ * a₀ = q * a₀ := by rw [hqe]
        _ = a₀ * u₂ := by rw [hq]; group
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁C) (Subgroup.mem_sup_right hu₂C)
  have hAWc : Nat.card (A₁ ⊓ W : Subgroup G) ≤ 4 :=
    (Subgroup.card_le_of_le hAW).trans hD
  have hA₁pos : 0 < Nat.card A₁ := Nat.card_pos
  have : Nat.card A₁ * 16 ≤ 2 * Nat.card A₁ * 4 := by
    rw [← hcB, ← hcardA]
    exact Nat.mul_le_mul hBA hAWc
  omega

end L15420

end CFSG.Quasithin.EmptyFaithfulMultiple
