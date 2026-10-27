module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaShape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918Perm
import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SymCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

private theorem five_dvd_factorial_div_two {n : ℕ} (hn : 5 ≤ n) : 5 ∣ n.factorial / 2 := by
  have h5 : 5 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨k, hk⟩ := h2
  rw [hk, Nat.mul_div_cancel_left k (by norm_num)]
  rw [hk] at h5
  exact (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 5 2)).1 h5

private noncomputable def mulEquivPermOfAltSwap {X : Type} [Group X] {n : ℕ}
    {Y : Subgroup X} (e : X ≃* alternatingGroup (Fin n)) {a b : Fin n} (hab : a ≠ b)
    (hY : Y.map e.toMonoidHom =
      (Subgroup.centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin n)))).comap
        (alternatingGroup (Fin n)).subtype) :
    ↥Y ≃* Equiv.Perm (Fin (n - 2)) := by
  let C : Subgroup (Equiv.Perm (Fin n)) :=
    Subgroup.centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin n)))
  let A : Subgroup (Equiv.Perm (Fin n)) := alternatingGroup (Fin n)
  have hmap : (C.comap A.subtype).map A.subtype = C ⊓ A := by
    rw [Subgroup.comap_subtype C A, Subgroup.subgroupOf_map_subtype C A]
  let e1 : ↥Y ≃* ↥(Y.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective
  let e2 : ↥(Y.map e.toMonoidHom) ≃* ↥(C.comap A.subtype) := MulEquiv.subgroupCongr hY
  let e3 : ↥(C.comap A.subtype) ≃* ↥(C ⊓ A) :=
    (Subgroup.equivMapOfInjective (C.comap A.subtype) A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  let e4 : ↥(C ⊓ A) ≃* Equiv.Perm (Fin (n - 2)) :=
    (CFSG.HardMathSupport.RichardWeiss.Proving.PLType.altCentSwapEquiv (m := n) hab).symm
  exact ((e1.trans e2).trans e3).trans e4

theorem not_exists_normal_two_three_of_mulEquiv_perm {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} {k : ℕ} (hk : 5 ≤ k) (e : ↥Y ≃* Equiv.Perm (Fin k)) :
    ¬ ∃ Nn : Subgroup X, Nn ≤ Y ∧ (Nn.subgroupOf Y).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3 := by
  rintro ⟨Nn, hNnY, hNorm, h3dvd, hprime⟩
  let N : Subgroup (Equiv.Perm (Fin k)) := (Nn.subgroupOf Y).map e.toMonoidHom
  have hNnorm : N.Normal := hNorm.map e.toMonoidHom e.surjective
  have hcardNn : Nat.card (Nn.subgroupOf Y) = Nat.card Nn :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNnY).toEquiv
  have hcardN : Nat.card N = Nat.card (Nn.subgroupOf Y) :=
    Subgroup.card_map_of_injective (K := Nn.subgroupOf Y) e.injective
  have hNne : N ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Nn.subgroupOf Y) = 1 := by rw [← hcardN, hbot]; simp
    have h3 : 3 ∣ Nat.card (Nn.subgroupOf Y) := hcardNn.symm ▸ h3dvd
    rw [h1] at h3
    exact absurd h3 (by norm_num)
  have hAle : alternatingGroup (Fin k) ≤ N :=
    alternatingGroup_le_of_normal_perm (Or.inr hk) hNnorm hNne
  have h5Nn : 5 ∣ Nat.card Nn := by
    have h5A : 5 ∣ Nat.card (alternatingGroup (Fin k)) := by
      haveI : Nontrivial (Fin k) :=
        Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_fin]; omega)
      rw [nat_card_alternatingGroup, Nat.card_fin]
      exact five_dvd_factorial_div_two hk
    have hdvd : Nat.card (alternatingGroup (Fin k)) ∣ Nat.card Nn := by
      have h := Subgroup.card_dvd_of_le hAle
      rwa [hcardN, hcardNn] at h
    exact h5A.trans hdvd
  exact absurd (hprime 5 (by norm_num) h5Nn) (by omega)

theorem not_exists_normal_two_three_of_isSimpleGroup {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} (hY : IsSimpleGroup ↥Y) (h5 : 5 ∣ Nat.card Y) :
    ¬ ∃ Nn : Subgroup X, Nn ≤ Y ∧ (Nn.subgroupOf Y).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3 := by
  rintro ⟨Nn, hNnY, hNorm, h3dvd, hprime⟩
  haveI : IsSimpleGroup ↥Y := hY
  haveI : (Nn.subgroupOf Y).Normal := hNorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Nn.subgroupOf Y) with hbot | htop
  · have h1 : Nat.card (Nn.subgroupOf Y) = 1 := by rw [hbot]; simp
    have hcard : Nat.card (Nn.subgroupOf Y) = Nat.card Nn :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNnY).toEquiv
    have h3 : 3 ∣ Nat.card (Nn.subgroupOf Y) := hcard.symm ▸ h3dvd
    rw [h1] at h3
    exact absurd h3 (by norm_num)
  · have hEq : Nn = Y := by
      refine le_antisymm hNnY ?_
      exact (Subgroup.subgroupOf_eq_top).1 htop
    have h5Nn : 5 ∣ Nat.card Nn := by
      rw [hEq]
      exact h5
    exact absurd (hprime 5 (by norm_num) h5Nn) (by omega)

theorem not_exists_normal_two_three_of_shape_four {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : (∃ ε : Bool, IsOmegaEps2 X ε m ∧ IsCentralizerOfTransvectionIn X m Y) ∨
      (IsAlt X (2 * m + 2) ∧
        ∃ (e : X ≃* alternatingGroup (Fin (2 * m + 2))) (a b : Fin (2 * m + 2)), a ≠ b ∧
          Y.map e.toMonoidHom =
            (Subgroup.centralizer
              ({Equiv.swap a b} : Set (Equiv.Perm (Fin (2 * m + 2))))).comap
              (alternatingGroup (Fin (2 * m + 2))).subtype)) :
    ¬ ∃ Nn : Subgroup X, Nn ≤ Y ∧ (Nn.subgroupOf Y).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3 := by
  rintro ⟨Nn, hNnY, hNorm, h3dvd, hprime⟩
  rcases h with ⟨ε, hX, hY⟩ | ⟨_halt, e, a, b, hab, hYmap⟩
  · rcases hm with rfl | rfl
    · cases ε with
      | false =>
        have hshape := omegaCentralizerShape_holds X false 3 Y hX hY
        obtain ⟨e⟩ := hshape.1 rfl rfl
        exact not_exists_normal_two_three_of_mulEquiv_perm (k := 6) (by norm_num) e
          ⟨Nn, hNnY, hNorm, h3dvd, hprime⟩
      | true =>
        have hXp : IsOmegaPlus X 6 1 := by simpa [IsOmegaEps2] using hX
        obtain ⟨e, a, b, hab, hYmap⟩ := exists_swap_of_isOmegaPlus_six hXp hY
        exact not_exists_normal_two_three_of_mulEquiv_perm (k := 6) (by norm_num)
          (mulEquivPermOfAltSwap e hab hYmap) ⟨Nn, hNnY, hNorm, h3dvd, hprime⟩
    · have hshape := omegaCentralizerShape_holds X ε 4 Y hX hY
      have hYcard : Nat.card Y = 1451520 := by
        obtain ⟨_, _, _, _, hc⟩ := hY
        norm_num at hc
        exact hc
      have h5 : 5 ∣ Nat.card Y := by rw [hYcard]; norm_num
      exact not_exists_normal_two_three_of_isSimpleGroup (hshape.2 rfl) h5
        ⟨Nn, hNnY, hNorm, h3dvd, hprime⟩
  · exact not_exists_normal_two_three_of_mulEquiv_perm (k := (2 * m + 2) - 2) (by omega)
      (mulEquivPermOfAltSwap (n := 2 * m + 2) e hab hYmap)
      ⟨Nn, hNnY, hNorm, h3dvd, hprime⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
