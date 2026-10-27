module

import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeHyperplaneGeneration
import CFSG.LocalAnalysis.LargeEvenClassification.InvariantKernel
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.K1327

open scoped commutatorElement
open CFSG.Open CFSG.LargeEvenClassification.Helpers

variable {G : Type} [Group G]

theorem commutator_eq_mul (u c : G) : ⁅u, c⁆ = u * (c * u⁻¹ * c⁻¹) := by
  simp [commutatorElement_def, mul_assoc]

theorem commutator_mem {V : Subgroup G} {u c : G} (hu : u ∈ V)
    (hV : ∀ v ∈ V, c * v * c⁻¹ ∈ V) : ⁅u, c⁆ ∈ V := by
  rw [commutator_eq_mul]
  exact V.mul_mem hu (hV _ (V.inv_mem hu))

theorem eq_one_of_commute_pow {p : ℕ} (hp : p.Prime) {V : Subgroup G} {u c : G} (hu : u ∈ V)
    (hcp : c ^ p = 1) (hV : ∀ v ∈ V, c * v * c⁻¹ ∈ V) (hcop : ¬ p ∣ Nat.card V)
    (hcomm : Commute ⁅u, c⁆ c) : ⁅u, c⁆ = 1 := by
  set w := ⁅u, c⁆ with hw
  have hwV : w ∈ V := commutator_mem hu hV
  have hwc : w * c = u * c * u⁻¹ := by
    simp [hw, commutatorElement_def, mul_assoc]
  have h1 : (w * c) ^ p = 1 := by
    rw [hwc]
    have : (u * c * u⁻¹) ^ p = u * c ^ p * u⁻¹ := conj_pow
    rw [this, hcp]
    simp
  have h2 : w ^ p = 1 := by
    have h3 := hcomm.mul_pow p
    rw [h3, hcp, mul_one] at h1
    exact h1
  have h3 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf w ∣ Nat.card V := by
    have := orderOf_dvd_natCard (⟨w, hwV⟩ : V)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime hp).1 h3 with h5 | h5
  · exact orderOf_eq_one_iff.1 h5
  · exact absurd (h5 ▸ h4) hcop

theorem le_iSup_centralizers [Finite G] {p : ℕ} (hp : p.Prime) {B V : Subgroup G}
    (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) (hcop : ¬ p ∣ Nat.card V) :
    V ≤ ⨆ b : {x : B // x ≠ 1}, V ⊓ Subgroup.centralizer ({(b.val : G)} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  let : CommGroup B := { (inferInstance : Group B) with mul_comm := @mul_comm' B _ hB.1 }
  have hstable : ∀ conjugator : B, ∀ element : G, element ∈ V →
      conjugator.val * element * (conjugator.val)⁻¹ ∈ V := by
    intro conjugator element helement
    exact (Subgroup.mem_normalizer_iff.mp (hBV conjugator.property) element).mp helement
  let action := invariantSubgroupConjugation B.subtype V hstable
  have hexponent : ∀ element : B, element ^ p = 1 := by
    intro element
    apply Subtype.ext
    exact hB.2 element element.property
  have hgenerates := coprime_hyperplane_fixed_generation hp (IsPGroup.of_card hBcard)
    hexponent action hcop
  let CentralizerSpan := ⨆ b : {x : B // x ≠ 1},
    V ⊓ Subgroup.centralizer ({(b.val : G)} : Set G)
  have hspanLe : hyperplaneFixedSpan p action ≤ CentralizerSpan.comap V.subtype := by
    apply iSup_le
    intro Fixers
    have hFnb : Fixers.val ≠ ⊥ := by
      intro hbot
      have h3 : Fixers.val.index ≤ p := Fixers.property
      have h1 := Subgroup.card_mul_index Fixers.val
      have hcard : Nat.card Fixers.val = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hcard, one_mul, hBcard] at h1
      have h4 : p ^ 2 ≤ p := h1 ▸ h3
      have h5 : p < p ^ 2 := by nlinarith [hp.two_le]
      omega
    obtain ⟨fixer, hfixer, hfixerNe⟩ :=
      (Subgroup.bot_or_exists_ne_one Fixers.val).resolve_left hFnb
    intro element helement
    have hfixedLe : V ⊓ Subgroup.centralizer ({(fixer.val : G)} : Set G) ≤ CentralizerSpan :=
      le_iSup_of_le ⟨fixer, hfixerNe⟩ le_rfl
    apply hfixedLe
    refine ⟨element.property, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hfixed := congrArg (fun entry : V => entry.val) (helement ⟨fixer, hfixer⟩)
    change fixer.val * element.val * fixer.val⁻¹ = element.val at hfixed
    exact ((mul_inv_eq_iff_eq_mul).mp hfixed).symm
  intro element helement
  exact hspanLe (hgenerates.symm ▸ (show (⟨element, helement⟩ : V) ∈ (⊤ : Subgroup V)
    from Subgroup.mem_top _))

theorem commute_of_commute_centralizers [Finite G] {p : ℕ} (hp : p.Prime) {B V : Subgroup G}
    (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) (hcop : ¬ p ∣ Nat.card V) {c : G}
    (hcomm : ∀ b ∈ B, b ≠ 1 → ∀ u ∈ V ⊓ Subgroup.centralizer ({b} : Set G), Commute u c) :
    ∀ u ∈ V, Commute u c := by
  have hgen := le_iSup_centralizers hp hB hBcard hBV hcop
  have hle : V ≤ Subgroup.centralizer ({c} : Set G) := by
    refine hgen.trans (iSup_le fun b => ?_)
    intro u hu
    have h := hcomm b.val.val b.val.property (fun h => b.property (Subtype.ext h)) u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact h.symm.eq
  intro u hu
  have := Subgroup.mem_centralizer_iff.1 (hle hu) c rfl
  exact this.symm

end CFSG.RankThree.PartOne.K1327
