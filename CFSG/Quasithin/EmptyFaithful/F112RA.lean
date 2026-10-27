module

public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace F112RR

variable {G : Type} [Group G] [Finite G]

theorem two_mul_card_inf_le {A P : Subgroup G} (h : ¬ A ≤ P) :
    2 * Nat.card ↥(A ⊓ P) ≤ Nat.card ↥A := by
  have hdvd : Nat.card ↥(A ⊓ P) ∣ Nat.card ↥A := Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card ↥(A ⊓ P) := Nat.card_pos
  have hk1 : k ≠ 1 := by
    intro hk1
    rw [hk1, mul_one] at hk
    apply h
    have heq : A ⊓ P = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact heq ▸ inf_le_right
  have hk0 : k ≠ 0 := by
    intro hk0
    have : 0 < Nat.card ↥A := Nat.card_pos
    rw [hk0, mul_zero] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  calc 2 * Nat.card ↥(A ⊓ P) ≤ k * Nat.card ↥(A ⊓ P) := Nat.mul_le_mul_right _ hk2
    _ = Nat.card ↥A := by rw [hk, mul_comm]

theorem exists_elemAbelian_card_ge {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (c1519 : Lemma1519Concl T Mc M) (c1521 : Lemma15201Concl T Mc M)
    (c319 : Concl319 T M (V154 T Mc M) H True) :
    IsElemAbelian 2 (conjClosure (V154 T Mc M) H) ∧
      conjClosure (V154 T Mc M) H ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ T ∧
      H ≤ Subgroup.normalizer (conjClosure (V154 T Mc M) H : Set G) ∧
      64 ≤ Nat.card ↥(conjClosure (V154 T Mc M) H) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := V154 T Mc M with hV
  set U := conjClosure V H with hU
  set P := pCoreOf 2 H with hP
  have hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hPT : P ≤ T := F7.isSylowTwoOf_pCoreOf_le hT
  have hVT : V ≤ T := S152N.V154_le_T hs
  have hTH : T ≤ H := hH.1.1
  have hnorm : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V H
  have hUH : U ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hTH (hVT hz))) (H.inv_mem hh)
  have hUab : IsElemAbelian 2 U := c319.elemAbelian
  have hUp : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian hUab
  have hUP : U ≤ P := le_pCoreOf_of_le_normalizer hUH hnorm hUp
  refine ⟨hUab, hUP, hPT, hnorm, ?_⟩
  obtain ⟨A, hA⟩ := c319.exists_A
  have hA1 := hA.1
  have hA2 := hA.2.1
  have hAP : ¬ A ≤ P := by
    intro hAP
    apply hA2
    refine ⟨hAP, hA1.2.1, fun B hBP hBab => hA1.2.2 B (hBP.trans hPT) hBab⟩
  have hAJ : A ≤ thompsonJ T := by
    unfold thompsonJ
    exact le_iSup₂_of_le (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) A hA1 le_rfl
  have hVA : V ≤ U ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_inf (le_conjClosure V H) ?_
    intro v hv a ha
    have hc : ⁅v, a⁆ ∈ ⁅V, thompsonJ T⁆ := Subgroup.commutator_mem_commutator hv (hAJ ha)
    rw [c1519.one_commute, Subgroup.mem_bot] at hc
    show a * v = v * a
    have : v * a * v⁻¹ * a⁻¹ = 1 := hc
    calc a * v = (v * a * v⁻¹ * a⁻¹) * (a * v) := by rw [this, one_mul]
      _ = v * a := by group
  have h16 : 16 ≤ Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) := by
    have := Subgroup.card_le_of_le hVA
    rw [c1521.card] at this
    exact this
  have hcount := c319.count_one A hA
  have hAP2 := two_mul_card_inf_le hAP
  have hpos : 0 < Nat.card ↥(A ⊓ P) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card ↥U * Nat.card ↥(A ⊓ P) ^ 2 < 64 * Nat.card ↥(A ⊓ P) ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hlt (by positivity)
  have h2 : 4 * Nat.card ↥(A ⊓ P) ^ 2 ≤ Nat.card ↥A ^ 2 := by
    have := Nat.mul_le_mul hAP2 hAP2
    nlinarith
  have h3 : 64 * Nat.card ↥(A ⊓ P) ^ 2 ≤ Nat.card ↥A ^ 2 *
      Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) := by
    calc 64 * Nat.card ↥(A ⊓ P) ^ 2 = (4 * Nat.card ↥(A ⊓ P) ^ 2) * 16 := by ring
      _ ≤ Nat.card ↥A ^ 2 * 16 := Nat.mul_le_mul_right _ h2
      _ ≤ Nat.card ↥A ^ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) :=
        Nat.mul_le_mul_left _ h16
  have h4 : Nat.card ↥A ^ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(A ⊓ P) ^ 2 * Nat.card ↥U := hcount
  nlinarith

end F112RR

end CFSG.Quasithin
