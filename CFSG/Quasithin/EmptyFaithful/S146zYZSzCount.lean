module

public import CFSG.Quasithin.EmptyFaithful.S146zYZSzTI
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.S146zY.SzNoFive

structure SzSylowData (K : Type) [Group K] (q : ℕ) (S : Sylow 2 K) : Prop where
  three_le : 3 ≤ q
  two_dvd : 2 ∣ q
  card : Nat.card K = q ^ 2 * (q ^ 2 + 1) * (q - 1)
  card_sylow : Nat.card (S : Subgroup K) = q ^ 2
  card_normalizer : Nat.card (Subgroup.normalizer ((S : Subgroup K) : Set K)) = q ^ 2 * (q - 1)
  odd_inter : ∀ g : K, g ∉ Subgroup.normalizer ((S : Subgroup K) : Set K) →
    Odd (Nat.card ↥(Subgroup.normalizer ((S : Subgroup K) : Set K) ⊓
      (Subgroup.normalizer ((S : Subgroup K) : Set K)).map (MulAut.conj g⁻¹).toMonoidHom))

section General

variable {K : Type} [Group K]

theorem inf_normalizer_eq_of_two_five [Finite K] {S : Sylow 2 K} {B : Subgroup K}
    (hSB : (S : Subgroup K) ≤ B)
    (hB : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → r = 2 ∨ r = 5)
    (hN : ¬ 5 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup K) : Set K))) :
    B ⊓ Subgroup.normalizer ((S : Subgroup K) : Set K) = (S : Subgroup K) := by
  have hCB : B ⊓ Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ B := inf_le_left
  have hCN : B ⊓ Subgroup.normalizer ((S : Subgroup K) : Set K) ≤
      Subgroup.normalizer ((S : Subgroup K) : Set K) := inf_le_right
  have h2 : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ↥(B ⊓ Subgroup.normalizer ((S : Subgroup K) : Set K)) → r = 2 := by
    intro r hr hrC
    rcases hB r hr (hrC.trans (Subgroup.card_dvd_of_le hCB)) with h | h
    · exact h
    · subst h
      exact absurd (hrC.trans (Subgroup.card_dvd_of_le hCN)) hN
  have hcard := Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_pos (α := ↥(B ⊓ Subgroup.normalizer ((S : Subgroup K) : Set K)))).ne'
    (fun {r} hr hrd => h2 r hr hrd)
  exact S.is_maximal' (IsPGroup.of_card hcard) (le_inf hSB Subgroup.le_normalizer)

variable {q : ℕ} {S : Sylow 2 K}

theorem eq_one_of_conj_mem (H : SzSylowData K q S) {B : Subgroup K}
    (hBN : B ⊓ Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ (S : Subgroup K))
    {g : K} (hgB : g ∈ B) (hgS : g ∉ (S : Subgroup K)) {x : K} (hx : x ∈ (S : Subgroup K))
    (hxg : g⁻¹ * x * g ∈ (S : Subgroup K)) : x = 1 := by
  have hgN : g⁻¹ ∉ Subgroup.normalizer ((S : Subgroup K) : Set K) := fun h =>
    hgS (hBN ⟨hgB, by simpa using Subgroup.inv_mem _ h⟩)
  have hodd := H.odd_inter g⁻¹ hgN
  rw [inv_inv] at hodd
  have hmem : x ∈ Subgroup.normalizer ((S : Subgroup K) : Set K) ⊓
      (Subgroup.normalizer ((S : Subgroup K) : Set K)).map (MulAut.conj g).toMonoidHom := by
    refine ⟨Subgroup.le_normalizer hx, Subgroup.mem_map.2 ⟨g⁻¹ * x * g,
      Subgroup.le_normalizer hxg, ?_⟩⟩
    simp [MulAut.conj_apply, mul_assoc]
  have h1 := Subgroup.orderOf_dvd_natCard _ hmem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨x, hx⟩
  have h2 : orderOf x = 2 ^ k := by simpa using hk
  have h3 : Odd (orderOf x) := Odd.of_dvd_nat hodd h1
  rw [h2] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 h3) (Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0] at h2
  exact orderOf_eq_one_iff.1 (by simpa using h2)

theorem exists_five_pow_eq [Finite K] (H : SzSylowData K q S) (h5 : ¬ 5 ∣ q ^ 2 * (q - 1))
    {B : Subgroup K} (hSB : (S : Subgroup K) ≤ B)
    (hB : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → r = 2 ∨ r = 5) (h5B : 5 ∣ Nat.card B) :
    ∃ j : ℕ, q ^ 2 + 1 = 5 ^ j := by
  classical
  have hq3 := H.three_le
  have hq : 2 ∣ q := H.two_dvd
  have hSq : Nat.card (S : Subgroup K) = q ^ 2 := H.card_sylow
  have hN5 : ¬ 5 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup K) : Set K)) := by
    rwa [H.card_normalizer]
  have hBN := inf_normalizer_eq_of_two_five hSB hB hN5
  have hPcard : Nat.card ((S : Subgroup K).subgroupOf B) = q ^ 2 := by
    rw [← hSq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv
  have hTI : ∀ g : B, g ∉ (S : Subgroup K).subgroupOf B → ∀ x ∈ (S : Subgroup K).subgroupOf B,
      g⁻¹ * x * g ∈ (S : Subgroup K).subgroupOf B → x = 1 := by
    intro g hg x hx hxg
    exact Subtype.ext (eq_one_of_conj_mem H hBN.le g.2 hg hx hxg)
  have hPtop : (S : Subgroup K).subgroupOf B ≠ ⊤ := by
    intro htop
    have hBS : B ≤ (S : Subgroup K) := by
      intro b hb
      have : (⟨b, hb⟩ : B) ∈ (S : Subgroup K).subgroupOf B := by rw [htop]; trivial
      exact this
    have hBeq : Nat.card B = q ^ 2 :=
      le_antisymm (hSq ▸ Subgroup.card_le_of_le hBS) (hSq ▸ Subgroup.card_le_of_le hSB)
    rw [hBeq] at h5B
    exact h5 (h5B.trans (Dvd.intro _ rfl))
  have hcount := card_add_one_le_index_of_ti hTI hPtop
  rw [hPcard] at hcount
  have hmul : q ^ 2 * ((S : Subgroup K).subgroupOf B).index = Nat.card B := by
    rw [← hPcard]
    exact Subgroup.card_mul_index _
  generalize ((S : Subgroup K).subgroupOf B).index = m at hcount hmul
  have hq2pos : 0 < q ^ 2 := by positivity
  have hBK : Nat.card B ∣ Nat.card K := Subgroup.card_subgroup_dvd_card B
  rw [H.card, ← hmul] at hBK
  have hm_dvd : m ∣ (q ^ 2 + 1) * (q - 1) := by
    refine Nat.dvd_of_mul_dvd_mul_left hq2pos ?_
    rwa [← mul_assoc]
  have hm5 : ∀ r : ℕ, r.Prime → r ∣ m → r = 5 := by
    intro r hr hrm
    have hrB : r ∣ Nat.card B := hmul ▸ Dvd.dvd.mul_left hrm (q ^ 2)
    rcases hB r hr hrB with h | h
    · exfalso
      subst h
      have h2 := hrm.trans hm_dvd
      have hq2 : 2 ∣ q ^ 2 := Dvd.dvd.pow hq (by norm_num)
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
      · omega
      · omega
    · exact h
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hmul
    exact absurd hmul.symm Nat.card_pos.ne'
  have hmpow := Nat.eq_prime_pow_of_unique_prime_dvd hm0 (fun {r} hr hrd => hm5 r hr hrd)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m = 5 ^ j := ⟨_, hmpow⟩
  have hcop : Nat.Coprime m (q - 1) := by
    rw [hj]
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2
      (fun hd => h5 (hd.trans (Dvd.intro_left _ rfl)))
  have hm_dvd' : m ∣ q ^ 2 + 1 := hcop.dvd_of_dvd_mul_right hm_dvd
  have hle : m ≤ q ^ 2 + 1 := Nat.le_of_dvd (by positivity) hm_dvd'
  exact ⟨j, by rw [← hj]; omega⟩

end General

end CFSG.Quasithin.S146zY.SzNoFive
