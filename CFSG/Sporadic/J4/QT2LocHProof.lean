
module

public import CFSG.Sporadic.J4.QT2LocHCheck
public import CFSG.Sporadic.J4.QT2LocHGen
public import CFSG.Sporadic.J4.QT2LocFiveProofBase
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem acts_pow {g : J} {t : List ℕ} (h : Acts g t) : ∀ n : ℕ, Acts (g ^ n) (powT t n)
  | 0 => by simpa [powT] using Acts.one
  | n + 1 => by
    have := h.mul (acts_pow h n)
    rwa [pow_succ']

section Tables

variable (hM : MatFacts)
include hM

theorem acts_exists_of_mem_Hj : ∀ g ∈ Hj, ∃ t, Acts g t := by
  intro g hg
  have hg' := Hj_le_closure hg
  clear hg
  induction hg' using Subgroup.closure_induction_right with
  | one => exact ⟨idT, Acts.one⟩
  | mul_right x hx y hy ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨ℓ, hℓ, rfl⟩ := hy
    exact ⟨_, ht.mul (Acts_XJ hM hℓ)⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨ℓ, hℓ, rfl⟩ := hy
    obtain ⟨hℓ', hinv⟩ := XJ_inv hℓ
    refine ⟨compT t (letterTab (-ℓ)), ht.mul ?_⟩
    rw [← hinv]
    exact Acts_XJ hM hℓ'

theorem acts_xi : Acts fiveElt xiT := Acts_wordProd hM fiveWord fiveWord_letters

theorem acts_xiK (k : ℕ) : Acts (fiveElt ^ k) (xiK k) := acts_pow (acts_xi hM) k

end Tables

theorem iset_props :
    (∀ s ∈ invSeedsT, s ∈ isetT) ∧ (∀ t ∈ isetT, compT t t = idT) ∧
      (∀ t ∈ isetT, ∀ ℓ ∈ letters, letConj ℓ t ∈ isetT) := by
  have h := chkIset_true
  unfold chkIset at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun s hs => ?_, fun t ht => (h2 t ht).1, fun t ht ℓ hℓ => ?_⟩
  · simpa [isetSet, Std.HashSet.contains_ofList] using h1 s hs
  · simpa [isetSet, Std.HashSet.contains_ofList] using (h2 t ht).2 ℓ hℓ

theorem card_Hj_factorization_two (hF : J4Facts) : (Nat.card Hj).factorization 2 = 21 := by
  rw [card_Hj hF]
  have h : (501397585920 : ℕ) = 2 ^ 21 * 239085 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Sylow

variable (hM : MatFacts)
include hM

theorem piT_conj_letter {h : J} (hh : ∃ t ∈ isetT, Acts h t) {ℓ : ℤ} (hℓ : ℓ ∈ letters) :
    ∃ t ∈ isetT, Acts (XJ ℓ * h * (XJ ℓ)⁻¹) t := by
  obtain ⟨t, ht, hA⟩ := hh
  obtain ⟨hℓ', hinv⟩ := XJ_inv hℓ
  refine ⟨letConj ℓ t, iset_props.2.2 t ht ℓ hℓ, ?_⟩
  have hi : Acts (XJ ℓ)⁻¹ (letterTab (-ℓ)) := by
    rw [← hinv]
    exact Acts_XJ hM hℓ'
  have h1 := (Acts_XJ hM hℓ).mul (hA.mul hi)
  rw [← mul_assoc] at h1
  exact h1

theorem piT_conj : ∀ g ∈ Hj, ∀ h : J, (∃ t ∈ isetT, Acts h t) →
    ∃ t ∈ isetT, Acts (g * h * g⁻¹) t := by
  intro g hg
  have hg' := Hj_le_closure hg
  clear hg
  induction hg' using Subgroup.closure_induction_right with
  | one => intro h hh; simpa using hh
  | mul_right x hx y hy ih =>
    intro h hh
    obtain ⟨ℓ, hℓ, rfl⟩ := hy
    have h2 := ih _ (piT_conj_letter hM hh hℓ)
    have e : x * (XJ ℓ * h * (XJ ℓ)⁻¹) * x⁻¹ = x * XJ ℓ * h * (x * XJ ℓ)⁻¹ := by group
    rwa [e] at h2
  | mul_inv_cancel x hx y hy ih =>
    intro h hh
    obtain ⟨ℓ, hℓ, rfl⟩ := hy
    obtain ⟨hℓ', hinv⟩ := XJ_inv hℓ
    have h1 := piT_conj_letter hM hh hℓ'
    rw [hinv] at h1
    have h2 := ih _ h1
    have e : x * ((XJ ℓ)⁻¹ * h * ((XJ ℓ)⁻¹)⁻¹) * x⁻¹ = x * (XJ ℓ)⁻¹ * h * (x * (XJ ℓ)⁻¹)⁻¹ := by
      group
    rwa [e] at h2

theorem exists_conj_into_P0 (hF : J4Facts) {h : J} (hh : h ∈ Hj) (h2 : h * h = 1) :
    ∃ g ∈ Hj, g * h * g⁻¹ ∈ P0 :=
  exists_conj_into_of_involution Hj P0 P0_le_Hj
    (by rw [card_P0 hM hF, card_Hj_factorization_two hF]) hh h2

theorem iset_complete (hF : J4Facts) {h : J} (hh : h ∈ Hj) (h2 : h * h = 1) {t : List ℕ}
    (ht : Acts h t) : t ∈ isetT := by
  obtain ⟨g, hg, hgh⟩ := exists_conj_into_P0 hM hF hh h2
  obtain ⟨t0, ht0, hA0⟩ := table_of_mem hM _ hgh
  have hsq : compT t0 t0 = idT := by
    have hA1 := hA0.mul hA0
    have e : (g * h * g⁻¹) * (g * h * g⁻¹) = 1 := by
      calc (g * h * g⁻¹) * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    rw [e] at hA1
    exact Acts.unique hM hA1 Acts.one
  have hseed : t0 ∈ invSeedsT := by
    unfold invSeedsT
    rw [List.mem_filter]
    exact ⟨ht0, by simp [hsq]⟩
  have h0 : ∃ t ∈ isetT, Acts (g * h * g⁻¹) t := ⟨t0, iset_props.1 t0 hseed, hA0⟩
  have h1 := piT_conj hM g⁻¹ (Hj.inv_mem hg) _ h0
  have e2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e2] at h1
  obtain ⟨t', ht', hA'⟩ := h1
  have := Acts.unique hM hA' ht
  rw [← this]
  exact ht'

end Sylow

end CFSG.Sporadic.J4.QT2
