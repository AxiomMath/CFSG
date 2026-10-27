module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathSub
import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath

open CFSG.RankThree.PartTwo.Sec4.RonanK432

variable {C S : Type} [CommGroup C] [Group S]

theorem zpow_coord (x : Fin 3 → C) (m : ℤ) (i : Fin 3) : (x ^ m) i = x i ^ m := rfl

@[expose] def HasTwist (φ : (Fin 3 → C) →* S) (μ : ℤ) (i j : Fin 3) : Prop :=
  ∃ g : S, ∃ f : (Fin 3 → C) → Fin 3 → C,
    (∀ c, g * φ c * g⁻¹ = φ (f c)) ∧ ∀ c, f c i = c i ^ μ ∧ f c j = c j

theorem witness_base {φ : (Fin 3 → C) →* S} (hφ : Function.Injective φ) {μ : ℤ}
    (hμ : ¬ (3 : ℤ) ∣ μ - 1) (htw : ∀ i j : Fin 3, i ≠ j → HasTwist φ μ i j)
    {s : S} (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (sh x))
    {y : Fin 3 → C} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ g : S, (g * φ y * g⁻¹) * φ y = φ y * (g * φ y * g⁻¹) ∧
      g * φ y * g⁻¹ ∉ Subgroup.zpowers (φ y) := by
  have hy3' : ∀ i, y i ^ 3 = 1 := fun i => by simpa using congr_fun hy3 i
  by_cases hmany : ∃ i j, i ≠ j ∧ y i ≠ 1 ∧ y j ≠ 1
  · obtain ⟨i, j, hij, hi, hj⟩ := hmany
    obtain ⟨g, f, hg, hf⟩ := htw i j hij
    obtain ⟨y', hy'⟩ : ∃ y' : Fin 3 → C, y' = f y := ⟨_, rfl⟩
    have hconj : g * φ y * g⁻¹ = φ y' := by rw [hy']; exact hg y
    have hy'i : y' i = y i ^ μ := by rw [hy']; exact (hf y).1
    have hy'j : y' j = y j := by rw [hy']; exact (hf y).2
    refine ⟨g, ?_, ?_⟩
    · rw [hconj, ← map_mul, ← map_mul, mul_comm]
    · rw [hconj]
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hsame : y ^ m = y' := hφ (by rw [map_zpow]; exact hm)
      have h1 : y i ^ m = y i ^ μ := by
        have := congr_fun hsame i
        rwa [zpow_coord, hy'i] at this
      have h2 : y j ^ m = y j := by
        have := congr_fun hsame j
        rwa [zpow_coord, hy'j] at this
      have hoi : orderOf (y i) = 3 := orderOf_eq_prime (hy3' i) hi
      have hoj : orderOf (y j) = 3 := orderOf_eq_prime (hy3' j) hj
      have d1 : ((3 : ℕ) : ℤ) ∣ m - μ := by
        rw [← hoi]
        exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub, h1, mul_inv_cancel])
      have d2 : ((3 : ℕ) : ℤ) ∣ m - 1 := by
        rw [← hoj]
        exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub_one, h2, mul_inv_cancel])
      apply hμ
      omega
  · have hmany' : ∀ i j, i ≠ j → y i ≠ 1 → y j = 1 := by
      intro i j hij hi
      by_contra hj
      exact hmany ⟨i, j, hij, hi, hj⟩
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 1 := by
      by_contra h
      exact hy1 (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    refine ⟨s, ?_, ?_⟩
    · rw [hs, ← map_mul, ← map_mul, mul_comm]
    · rw [hs]
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hsame : y ^ m = sh y := hφ (by rw [map_zpow]; exact hm)
      have hne : i ≠ i + 1 := by
        fin_cases i <;> decide
      have h1 := congr_fun hsame (i + 1)
      rw [zpow_coord, hmany' i (i + 1) hne hi, one_zpow] at h1
      simp only [sh, add_sub_cancel_right] at h1
      exact hi h1.symm

theorem witness_twist {φ : (Fin 3 → C) →* S} (hφ : Function.Injective φ)
    {t : S} {σ : (Fin 3 → C) →* (Fin 3 → C)} (ht : ∀ x, t * φ x * t⁻¹ = φ (σ x))
    (hσc : ∀ z : C, σ (fun _ => z) = fun _ => z)
    (htB : ∀ x : Fin 3 → C, φ x ≠ t)
    {y w : Fin 3 → C} {z : C} (hz1 : z ≠ 1)
    (hw : w * (σ w)⁻¹ = fun _ => z) (hu3 : (φ y * t) ^ 3 = 1) :
    ∃ g : S, (g * (φ y * t) * g⁻¹) * (φ y * t) = (φ y * t) * (g * (φ y * t) * g⁻¹) ∧
      g * (φ y * t) * g⁻¹ ∉ Subgroup.zpowers (φ y * t) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → C, c = fun _ => z := ⟨_, rfl⟩
  have hσc' : σ c = c := by rw [hc]; exact hσc z
  have hw' : w * (σ w)⁻¹ = c := by rw [hc]; exact hw
  have hyc : y * c = c * y := mul_comm _ _
  have hwy : w * y = y * w := mul_comm _ _
  have hconj : φ w * (φ y * t) * (φ w)⁻¹ = φ c * (φ y * t) := by
    have h1 : t * (φ w)⁻¹ * t⁻¹ = (φ (σ w))⁻¹ := by
      rw [← ht w]
      group
    calc φ w * (φ y * t) * (φ w)⁻¹
        = φ w * φ y * (t * (φ w)⁻¹ * t⁻¹) * t := by group
      _ = φ (w * y * (σ w)⁻¹) * t := by rw [h1, map_mul, map_mul, map_inv]
      _ = φ (c * y) * t := by rw [hwy, mul_assoc y, hw', hyc]
      _ = φ c * (φ y * t) := by rw [map_mul, mul_assoc]
  have hcomm : φ c * (φ y * t) = (φ y * t) * φ c := by
    have h2 : t * φ c * t⁻¹ = φ c := by rw [ht c, hσc']
    calc φ c * (φ y * t) = φ (c * y) * t := by rw [map_mul, mul_assoc]
      _ = φ (y * c) * t := by rw [hyc]
      _ = φ y * (t * φ c * t⁻¹) * t := by rw [h2, map_mul]
      _ = (φ y * t) * φ c := by group
  refine ⟨φ w, ?_, ?_⟩
  · rw [hconj]
    calc φ c * (φ y * t) * (φ y * t) = (φ y * t) * φ c * (φ y * t) := by rw [hcomm]
      _ = (φ y * t) * (φ c * (φ y * t)) := mul_assoc _ _ _
  · rw [hconj]
    intro hmem
    have hφt : ∀ x : Fin 3 → C, φ y * t ≠ φ x := by
      intro x h
      apply htB (y⁻¹ * x)
      rw [map_mul, map_inv, ← h]
      group
    rcases mem_zpowers_cases_of_pow_three hu3 hmem with h | h | h
    · exact hφt c⁻¹ (by rw [map_inv]; exact eq_inv_of_mul_eq_one_right h)
    · have h1 : φ c = 1 := by simpa using h
      have h2 : c = 1 := hφ (h1.trans (map_one φ).symm)
      apply hz1
      have := congr_fun h2 0
      rw [hc] at this
      exact this
    · have e : (φ y * t)⁻¹ = (φ y * t) * (φ y * t) :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hu3)
      exact hφt c (mul_right_cancel (h.trans e)).symm

theorem not_weaklyClosed_of_wreath_twists [Finite C] [Finite S] {a : ℕ} (ha : 1 ≤ a)
    (hC : Nat.card C = 3 ^ a) {φ : (Fin 3 → C) →* S} (hφ : Function.Injective φ) {μ : ℤ}
    (hμ : ¬ (3 : ℤ) ∣ μ - 1) (htw : ∀ i j : Fin 3, i ≠ j → HasTwist φ μ i j)
    {s : S} (hs3 : s ^ 3 = 1) (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (sh x))
    (hS : ¬ 3 ^ (3 * a + 2) ∣ Nat.card S) {z : S} (hz : orderOf z = 3) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBcard : Nat.card φ.range = 3 ^ (3 * a) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun, hC,
      Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]
  have hn : ∀ b ∈ φ.range, s * b * s⁻¹ ∈ φ.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨sh x, (hs x).symm⟩
  have h3C : 3 ∣ Nat.card C := by
    rw [hC]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 3 h3C
  have hz₀3 : z₀ ^ 3 = 1 := by
    have := pow_orderOf_eq_one z₀
    rwa [hz₀] at this
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₀
    omega
  have hsB : ∀ x : Fin 3 → C, φ x ≠ s := by
    intro x hx
    have hcomm : φ x * φ (Pi.mulSingle 0 z₀) = φ (Pi.mulSingle 0 z₀) * φ x := by
      rw [← map_mul, ← map_mul, mul_comm]
    have h1 : φ (sh (Pi.mulSingle 0 z₀)) = φ (Pi.mulSingle 0 z₀) :=
      calc φ (sh (Pi.mulSingle 0 z₀)) = s * φ (Pi.mulSingle 0 z₀) * s⁻¹ := (hs _).symm
        _ = φ x * φ (Pi.mulSingle 0 z₀) * (φ x)⁻¹ := by rw [hx]
        _ = φ (Pi.mulSingle 0 z₀) := by rw [hcomm, mul_inv_cancel_right]
    have h2 := congr_fun (hφ h1) 1
    simp only [sh] at h2
    have h3 : ((1 : Fin 3) - 1) = 0 := by decide
    rw [h3, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide)] at h2
    exact hz₀1 h2
  have hsnB : s ∉ φ.range := fun h => by
    obtain ⟨x, hx⟩ := h
    exact hsB x hx
  have hQcard : Nat.card (extSub φ.range s hs3 hn) = 3 ^ (3 * a + 1) := by
    rw [card_extSub φ.range s hs3 hn hsnB, hBcard, pow_succ]
  have hsB2 : ∀ x : Fin 3 → C, φ x ≠ s ^ 2 := by
    intro x h
    apply hsB (x * x)
    calc φ (x * x) = s ^ 2 * s ^ 2 := by rw [map_mul, h]
      _ = s ^ 3 * s := by group
      _ = s := by rw [hs3, one_mul]
  refine not_weaklyClosed_of_sylow_witness (3 * a + 1) (extSub φ.range s hs3 hn) hQcard hS ?_ hz
  rintro q ⟨b, hb, k, hk, rfl⟩ hq3
  obtain ⟨y, rfl⟩ := hb
  have hu3 : (φ y * s ^ k) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (φ y * s ^ k)
    rwa [hq3] at this
  interval_cases k
  · simp only [pow_zero, mul_one] at hq3 ⊢
    have hφy3 : φ y ^ 3 = 1 := by simpa using hu3
    have hy3 : y ^ 3 = 1 := hφ (by rw [map_pow, map_one]; exact hφy3)
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hq3
      omega
    exact witness_base hφ hμ htw hs hy3 hy1
  · simp only [pow_one] at hu3 ⊢
    exact witness_twist (σ := shHom) hφ hs (fun _ => rfl) hsB hz₀1 (wreath_w1 hz₀3) hu3
  · refine witness_twist (σ := shHom.comp shHom) hφ ?_ (fun _ => rfl) hsB2 hz₀1 (wreath_w2 hz₀3)
      hu3
    intro x
    calc s ^ 2 * φ x * (s ^ 2)⁻¹ = s * (s * φ x * s⁻¹) * s⁻¹ := by
          rw [pow_two, mul_inv_rev]
          simp only [mul_assoc]
      _ = φ (shHom (shHom x)) := by rw [hs x, hs (sh x)]; rfl

theorem listRow_of_wreath_twists [Finite C] [Finite S] {a : ℕ} (ha : 1 ≤ a)
    (hC : Nat.card C = 3 ^ a) {φ : (Fin 3 → C) →* S} (hφ : Function.Injective φ) {μ : ℤ}
    (hμ : ¬ (3 : ℤ) ∣ μ - 1) (htw : ∀ i j : Fin 3, i ≠ j → HasTwist φ μ i j)
    {s : S} (hs3 : s ^ 3 = 1) (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (sh x))
    (hS : ¬ 3 ^ (3 * a + 2) ∣ Nat.card S) : ListRow S :=
  listRow_of_forall_not_weaklyClosed fun _ hz =>
    not_weaklyClosed_of_wreath_twists ha hC hφ hμ htw hs3 hs hS hz

theorem hasTwist_of_single {φ : (Fin 3 → C) →* S} {μ : ℤ}
    (htw : ∀ i : Fin 3, ∃ g : S, ∀ c, g * φ c * g⁻¹ = φ (Function.update c i (c i ^ μ)))
    {i j : Fin 3} (hij : i ≠ j) : HasTwist φ μ i j := by
  obtain ⟨g, hg⟩ := htw i
  exact ⟨g, fun c => Function.update c i (c i ^ μ), hg,
    fun c => ⟨by simp, Function.update_of_ne hij.symm _ _⟩⟩

theorem listRow_of_wreath [Finite C] [Finite S] {a : ℕ} (ha : 1 ≤ a)
    (hC : Nat.card C = 3 ^ a) {φ : (Fin 3 → C) →* S} (hφ : Function.Injective φ) {μ : ℤ}
    (hμ : ¬ (3 : ℤ) ∣ μ - 1)
    (htw : ∀ i : Fin 3, ∃ g : S, ∀ c, g * φ c * g⁻¹ = φ (Function.update c i (c i ^ μ)))
    {s : S} (hs3 : s ^ 3 = 1) (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (sh x))
    (hS : ¬ 3 ^ (3 * a + 2) ∣ Nat.card S) : ListRow S :=
  listRow_of_wreath_twists ha hC hφ hμ (fun _ _ hij => hasTwist_of_single htw hij) hs3 hs hS

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath
