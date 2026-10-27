module

public import CFSG.Quasithin.Background.A318PHatCore
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.Asc83Table (E9Basis)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem HatData.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L') (h : HatData L) :
    HatData L' where
  out := by
    rw [← Nat.card_congr (equivalence e).toEquiv]
    exact h.out
  card := by
    obtain ⟨m, hm, hm3⟩ := h.card
    exact ⟨m, by rw [← Nat.card_congr e.toEquiv]; exact hm, hm3⟩
  irr := by
    obtain ⟨P, hP, hPel, n, hn, hirr⟩ := h.irr
    refine ⟨P.map e.toMonoidHom, ?_, CFSG.SectionRank.isElemAbelian_map hPel _, e n, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective e.injective, hP]
    · rw [Subgroup.mem_normalizer_iff] at hn ⊢
      intro x
      rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
      have h1 : e.symm (e n * x * (e n)⁻¹) = n * e.symm x * n⁻¹ := by simp
      rw [h1]
      exact hn _
    · intro Λ hΛ hΛ3 heq
      refine hirr (Λ.map e.symm.toMonoidHom) ?_ ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact (Subgroup.mem_map_equiv).1 (hΛ hz)
      · rw [Subgroup.card_map_of_injective e.symm.injective, hΛ3]
      · have hcomp : (MulAut.conj n).toMonoidHom.comp e.symm.toMonoidHom =
            e.symm.toMonoidHom.comp (MulAut.conj (e n)).toMonoidHom := by
          ext x
          simp [MulAut.conj_apply]
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, heq]

theorem mem_zpowers_cube {G : Type*} [Group G] {c d : G} (hc : c ^ 3 = 1)
    (hd : d ∈ Subgroup.zpowers c) : d = 1 ∨ d = c ∨ d = c ^ 2 := by
  obtain ⟨k, hk⟩ := hd
  have hk' : d = c ^ k := hk.symm
  subst hk'
  have h1 : c ^ k = c ^ (k % 3) := zpow_eq_zpow_emod' k hc
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  rw [h1]
  interval_cases (k % 3) <;> simp

theorem exists_irr_of_conj {L : Type} [Group L] {a b n : L} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2)
    (h₁ : n * a * n⁻¹ = b) (h₂ : n * b * n⁻¹ = a ^ 2)
    (hdec : ∀ i, i < 3 → ∀ j, j < 3 → (i ≠ 0 ∨ j ≠ 0) →
      n * (a ^ i * b ^ j) * n⁻¹ ≠ a ^ i * b ^ j ∧
        n * (a ^ i * b ^ j) * n⁻¹ ≠ (a ^ i * b ^ j) ^ 2) :
    ∃ P : Subgroup L, Nat.card P = 9 ∧ CFSG.Open.IsElemAbelian 3 P ∧
      ∃ n ∈ Subgroup.normalizer (P : Set L), ∀ Λ : Subgroup L, Λ ≤ P → Nat.card Λ = 3 →
        Λ.map (MulAut.conj n).toMonoidHom ≠ Λ := by
  have hcomm : Commute a b := hab
  let E : E9Basis L := E9Basis.ofNe ha hb hcomm ha1 hb1 hba hba2
  refine ⟨E.sub, E.card, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
    E.isElementaryAbelian, n, ?_, ?_⟩
  · have h1' : n * E.a * n⁻¹ = E.a ^ 0 * E.b ^ 1 := by
      change n * a * n⁻¹ = a ^ 0 * b ^ 1
      rw [h₁]
      simp
    have h2' : n * E.b * n⁻¹ = E.a ^ 2 * E.b ^ 0 := by
      change n * b * n⁻¹ = a ^ 2 * b ^ 0
      rw [h₂]
      simp
    have := E.mem_normalizer_of_conj 0 2 1 0 h1' h2'
    rwa [E.closure_range] at this
  · intro Λ hΛP hΛ3 heq
    have hfin : Finite Λ := Nat.finite_of_card_ne_zero (by rw [hΛ3]; norm_num)
    obtain ⟨c, hcΛ, hc1⟩ : ∃ c ∈ Λ, c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Λ = ⊥ := (Subgroup.eq_bot_iff_forall Λ).2 hcon
      rw [this, Subgroup.card_bot] at hΛ3
      omega
    have hc3 : c ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Λ) (x := ⟨c, hcΛ⟩)
      rw [hΛ3] at this
      exact congrArg Subtype.val this
    have hΛz : Λ = Subgroup.zpowers c := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcΛ) ?_).symm
      rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1, hΛ3]
    obtain ⟨i, j, hi, hj, hcij⟩ := E.exists_pow_mul_pow (hΛP hcΛ)
    have hcij' : c = a ^ i * b ^ j := hcij
    have hij : i ≠ 0 ∨ j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hc1
      rw [hcij', hcon.1, hcon.2]
      simp
    have hnc : n * c * n⁻¹ ∈ Λ := by
      rw [← heq]
      exact ⟨c, hcΛ, by simp [MulAut.conj_apply]⟩
    rw [hΛz] at hnc
    obtain ⟨h1, h2⟩ := hdec i hi j hj hij
    rw [hcij'] at hnc
    rcases mem_zpowers_cube (by rw [← hcij']; exact hc3) hnc with h | h | h
    · apply hc1
      rw [hcij']
      have h' := congrArg (fun z => n⁻¹ * z * n) h
      simpa [mul_assoc] using h'
    · exact h1 h
    · exact h2 h

theorem exists_irr_perm {m : ℕ} (S : Subgroup (Equiv.Perm (Fin m))) {a b n : Equiv.Perm (Fin m)}
    (haS : a ∈ S) (hbS : b ∈ S) (hnS : n ∈ S) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2)
    (h₁ : n * a * n⁻¹ = b) (h₂ : n * b * n⁻¹ = a ^ 2)
    (hdec : ∀ i, i < 3 → ∀ j, j < 3 → (i ≠ 0 ∨ j ≠ 0) →
      n * (a ^ i * b ^ j) * n⁻¹ ≠ a ^ i * b ^ j ∧
        n * (a ^ i * b ^ j) * n⁻¹ ≠ (a ^ i * b ^ j) ^ 2) :
    ∃ P : Subgroup ↥S, Nat.card P = 9 ∧ CFSG.Open.IsElemAbelian 3 P ∧
      ∃ n ∈ Subgroup.normalizer (P : Set ↥S), ∀ Λ : Subgroup ↥S, Λ ≤ P → Nat.card Λ = 3 →
        Λ.map (MulAut.conj n).toMonoidHom ≠ Λ := by
  refine exists_irr_of_conj (a := ⟨a, haS⟩) (b := ⟨b, hbS⟩) (n := ⟨n, hnS⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_
  · exact Subtype.ext (by simpa using ha)
  · exact Subtype.ext (by simpa using hb)
  · exact Subtype.ext (by simpa using hab)
  · intro h
    exact ha1 (congrArg Subtype.val h)
  · intro h
    exact hb1 (congrArg Subtype.val h)
  · intro h
    exact hba (congrArg Subtype.val h)
  · intro h
    exact hba2 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using h₁)
  · exact Subtype.ext (by simpa using h₂)
  · intro i hi j hj hij
    obtain ⟨d1, d2⟩ := hdec i hi j hj hij
    exact ⟨fun h => d1 (by simpa using congrArg Subtype.val h),
      fun h => d2 (by simpa using congrArg Subtype.val h)⟩

end A318P

end CFSG.Quasithin
