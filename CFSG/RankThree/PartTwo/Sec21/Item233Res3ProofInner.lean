module

public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofZRoot
public import CFSG.RankThree.PartTwo.Sec21.Item228U54
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open scoped Pointwise

variable {G : Type} [Group G]

theorem inf_centralizer_self_eq_bot {Z : Subgroup G} (hZc : Subgroup.center Z = ⊥) :
    Z ⊓ Subgroup.centralizer (Z : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxZ, hxC⟩
  have hx : (⟨x, hxZ⟩ : Z) ∈ Subgroup.center Z := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  rw [hZc, Subgroup.mem_bot] at hx
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)

theorem card_inf_eq_nine [Finite G] {A Z : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G)) (hZc : Subgroup.center Z = ⊥)
    (hCI : Sec4.CubeInner Z)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3)
    (h27 : ¬ 27 ∣ Nat.card Z) : Nat.card (A ⊓ Z : Subgroup G) = 9 := by
  have hle := card_le_card_inf_mul_card_inf_centralizer hA hAN hZc hCI
  rw [hA27, hC3] at hle
  have hdvd : Nat.card (A ⊓ Z : Subgroup G) ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hZd : Nat.card (A ⊓ Z : Subgroup G) ∣ Nat.card Z := Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hkeq] at hle hZd ⊢
  interval_cases k
  · norm_num at hle
  · norm_num at hle
  · norm_num
  · exact absurd hZd (by norm_num; exact h27)

theorem inf_sup_inf_centralizer_eq [Finite G] {A Z : Subgroup G} (hA27 : Nat.card A = 3 ^ 3)
    (hZc : Subgroup.center Z = ⊥) (hF9 : Nat.card (A ⊓ Z : Subgroup G) = 9)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3) :
    (A ⊓ Z) ⊔ (A ⊓ Subgroup.centralizer (Z : Set G)) = A := by
  set F := A ⊓ Z with hF
  set C := A ⊓ Subgroup.centralizer (Z : Set G) with hC
  have hJA : F ⊔ C ≤ A := sup_le inf_le_left inf_le_left
  have hCF : ¬ C ≤ F := by
    intro h
    have h1 : C ≤ Z ⊓ Subgroup.centralizer (Z : Set G) :=
      le_inf (h.trans inf_le_right) inf_le_right
    rw [inf_centralizer_self_eq_bot hZc] at h1
    have h2 := Subgroup.card_le_of_le h1
    rw [hC3, Subgroup.card_bot] at h2
    omega
  have hlt : F < F ⊔ C := lt_of_le_of_ne le_sup_left fun h => hCF (h ▸ le_sup_right)
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hF9] at hcard
  have hdvd : Nat.card (F ⊔ C : Subgroup G) ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_dvd_of_le hJA
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h27 : Nat.card (F ⊔ C : Subgroup G) = 3 ^ 3 := by
    rw [hkeq] at hcard ⊢
    interval_cases k
    · norm_num at hcard
    · norm_num at hcard
    · norm_num at hcard
    · rfl
  exact Subgroup.eq_of_le_of_card_ge hJA (by rw [h27, hA27])

theorem isElemAbelian_of_le {p : ℕ} {E X : Subgroup G} (hE : IsElemAbelian p E) (hXE : X ≤ E) :
    IsElemAbelian p X := CFSG.Open.IsElemAbelian.mono hE hXE

theorem mem_normalizer_of_forall_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_mul_of_inf_sup_eq {A Z : Subgroup G}
    (hAZ : (A ⊓ Z) ⊔ (A ⊓ Subgroup.centralizer (Z : Set G)) = A) :
    ∀ a ∈ A, ∃ f ∈ A ⊓ Z, ∃ c ∈ A ⊓ Subgroup.centralizer (Z : Set G), f * c = a := by
  have hCN : A ⊓ Subgroup.centralizer (Z : Set G) ≤
      Subgroup.normalizer ((A ⊓ Z : Subgroup G) : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right)
        (Subgroup.mem_inf.mp hc).2)
  intro a ha
  have ha' : a ∈ ((A ⊓ Z ⊔ A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) := by
    rw [hAZ]
    exact ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN] at ha'
  obtain ⟨f, hf, c, hc, hfc⟩ := ha'
  exact ⟨f, hf, c, hc, hfc⟩

theorem exists_fourGroup_of_lines [Finite G] {A Z : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 3 ^ 3) (hZc : Subgroup.center Z = ⊥)
    (hAZ : (A ⊓ Z) ⊔ (A ⊓ Subgroup.centralizer (Z : Set G)) = A)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3)
    (hlines : ∀ ℓ : Subgroup G, ℓ ≤ A ⊓ Z → Nat.card ℓ = 3 → ∃ V : Subgroup G, V ≤ Z ∧
      IsElemAbelian 2 V ∧ Nat.card V = 4 ∧ A ⊓ Z ≤ Subgroup.normalizer (V : Set G) ∧
      (A ⊓ Z) ⊓ Subgroup.centralizer (V : Set G) = ℓ)
    {ρ : MulAut A} (hρZ : ρ ∈ starOf A Z) (hρ : IsReflectionOn ρ) :
    ∃ V ∈ fourGroups A, A ⊓ Subgroup.centralizer (V : Set G) ≤ fixedInG A ρ := by
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  set F := A ⊓ Z with hF
  set C := A ⊓ Subgroup.centralizer (Z : Set G) with hC
  set B := fixedInG A ρ with hB
  have hB9 : Nat.card B = 9 := Item228ResProof.card_fixedInG_eq_nine hAc hA27 hρ
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hdecomp : ∀ a ∈ A, ∃ f ∈ F, ∃ c ∈ C, f * c = a := exists_mul_of_inf_sup_eq hAZ
  obtain ⟨⟨w, hwN⟩, hwZ, hρw⟩ := hρZ
  have hwZ' : w ∈ Z := Subgroup.mem_subgroupOf.mp hwZ
  have hCB : C ≤ B := by
    intro c hc
    obtain ⟨hcA, hcC⟩ := Subgroup.mem_inf.mp hc
    refine ⟨⟨c, hcA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf, ← hρw]
    apply Subtype.ext
    change w * c * w⁻¹ = c
    have hcw : w * c = c * w := Subgroup.mem_centralizer_iff.mp hcC w hwZ'
    rw [hcw, mul_inv_cancel_right]
  have hCZ : ∀ c ∈ C, c ∈ Z → c = 1 := by
    intro c hc hcZ
    have h1 : c ∈ Z ⊓ Subgroup.centralizer (Z : Set G) := ⟨hcZ, (Subgroup.mem_inf.mp hc).2⟩
    rw [inf_centralizer_self_eq_bot hZc] at h1
    exact Subgroup.mem_bot.mp h1
  set ℓ := B ⊓ Z with hℓ
  have hℓF : ℓ ≤ F := le_inf (inf_le_left.trans hBA) inf_le_right
  have hℓ3 : Nat.card ℓ = 3 := by
    have hℓne : ℓ ≠ ⊥ := by
      have hBC : ¬ B ≤ C := by
        intro h
        have := Subgroup.card_le_of_le h
        rw [hB9, hC3] at this
        omega
      obtain ⟨b, hbB, hbC⟩ := Set.not_subset.mp hBC
      obtain ⟨f, hf, c, hc, rfl⟩ := hdecomp b (hBA hbB)
      intro hbot
      have hfB : f ∈ B := by
        have := B.mul_mem hbB (B.inv_mem (hCB hc))
        rwa [mul_inv_cancel_right] at this
      have hfℓ : f ∈ ℓ := ⟨hfB, (Subgroup.mem_inf.mp hf).2⟩
      rw [hbot, Subgroup.mem_bot] at hfℓ
      rw [hfℓ, one_mul] at hbC
      exact hbC hc
    have hℓF' : ℓ ≠ F := by
      intro h
      have hFB : F ≤ B := h ▸ inf_le_left
      have hAB : A ≤ B := hAZ ▸ sup_le hFB hCB
      have := Subgroup.card_le_of_le hAB
      rw [hA27, hB9] at this
      norm_num at this
    have hF9 : Nat.card F = 9 := by
      have := Subgroup.card_le_of_le hℓF
      have h1 := Subgroup.card_dvd_of_le (show F ≤ A from inf_le_left)
      rw [hA27] at h1
      have hFC : Nat.card A ≤ Nat.card F * Nat.card C := by
        have hsurj : Function.Surjective (fun p : F × C => (⟨(p.1 : G) * p.2,
            A.mul_mem (Subgroup.mem_inf.mp p.1.2).1 (Subgroup.mem_inf.mp p.2.2).1⟩ : A)) := by
          rintro ⟨a, ha⟩
          obtain ⟨f, hf, c, hc, rfl⟩ := hdecomp a ha
          exact ⟨(⟨f, hf⟩, ⟨c, hc⟩), rfl⟩
        rw [← Nat.card_prod]
        exact Nat.card_le_card_of_surjective _ hsurj
      rw [hA27, hC3] at hFC
      obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
      have hF27 : Nat.card F ≠ 27 := by
        intro h27
        have hFA : F = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA27]; norm_num)
        have hCF : C ≤ F := hFA ▸ inf_le_left
        obtain ⟨c, hc, hc1⟩ : ∃ c ∈ C, c ≠ 1 := by
          by_contra hcon
          push Not at hcon
          have : C = ⊥ := (Subgroup.eq_bot_iff_forall C).mpr hcon
          rw [this, Subgroup.card_bot] at hC3
          omega
        exact hc1 (hCZ c hc (Subgroup.mem_inf.mp (hCF hc)).2)
      rw [hkeq] at hFC hF27 ⊢
      interval_cases k
      · norm_num at hFC
      · norm_num at hFC
      · rfl
      · exact absurd (by norm_num) hF27
    have hlt : ℓ < F := lt_of_le_of_ne hℓF hℓF'
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card ℓ ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hF9]
      exact Subgroup.card_dvd_of_le hℓF
    have h3 : Nat.card ℓ ≠ 1 := fun h => hℓne (Subgroup.eq_bot_of_card_eq ℓ h)
    rw [hF9] at h1
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rw [hkeq] at h1 h3 ⊢
    interval_cases k
    · exact absurd (by norm_num) h3
    · rfl
    · norm_num at h1
  obtain ⟨V, hVZ, hVe, hV4, hFV, hFCV⟩ := hlines ℓ hℓF hℓ3
  have hCV : C ≤ Subgroup.centralizer (V : Set G) := fun c hc =>
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVZ) hc.2
  refine ⟨V, mem_fourGroups_iff.mpr ⟨?_, hVe, hV4⟩, ?_⟩
  · rw [← hAZ]
    exact sup_le hFV (hCV.trans (Subgroup.centralizer_le_normalizer _))
  · rintro a ⟨haA, haV⟩
    obtain ⟨f, hf, c, hc, rfl⟩ := hdecomp a haA
    have hfV : f ∈ Subgroup.centralizer (V : Set G) := by
      have := (Subgroup.centralizer (V : Set G)).mul_mem haV
        ((Subgroup.centralizer (V : Set G)).inv_mem (hCV hc))
      rwa [mul_inv_cancel_right] at this
    have hfℓ : f ∈ ℓ := hFCV ▸ (⟨hf, hfV⟩ : f ∈ F ⊓ Subgroup.centralizer (V : Set G))
    exact B.mul_mem hfℓ.1 (hCB hc)

end CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof
