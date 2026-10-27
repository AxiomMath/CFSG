module

public import CFSG.GroupTheory.OddCoreFixedPointFreeAbelian
public import CFSG.GroupTheory.ThreeFreeNormalAbelian
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.oddCore_commute_of_CYtau
    {B : Subgroup G} {X : Subgroup (MulAut ↥B)} {τX : MulAut ↥B}
    (hτXmem : τX ∈ X) (hτ2 : τX * τX = 1)
    (hCY : ∀ g : X, g ∈ oddCore X →
      (g : MulAut ↥B) * τX = τX * (g : MulAut ↥B) → (g : MulAut ↥B) = 1) :
    ∀ a b : X, a ∈ oddCore X → b ∈ oddCore X → a * b = b * a := by
  let τ : X := ⟨τX, hτXmem⟩
  have hτ2' : τ * τ = 1 := Subtype.ext hτ2
  have hfree : ∀ y : X, y ∈ oddCore X → τ * y * τ⁻¹ = y → y = 1 := by
    intro y hy hconj
    have hcoe : τX * (y : MulAut ↥B) * τX⁻¹ = (y : MulAut ↥B) :=
      congrArg (fun z : X => (z : MulAut ↥B)) hconj
    have hcomm : (y : MulAut ↥B) * τX = τX * (y : MulAut ↥B) := by
      calc
        (y : MulAut ↥B) * τX = (τX * (y : MulAut ↥B) * τX⁻¹) * τX := by rw [hcoe]
        _ = τX * (y : MulAut ↥B) * (τX⁻¹ * τX) := by group
        _ = τX * (y : MulAut ↥B) := by rw [inv_mul_cancel, mul_one]
    exact Subtype.ext (hCY y hy hcomm)
  have hcomm :=
    CFSG.oddCore_commute_of_fixedPointFree_involution (X := X) (τ := τ) hτ2' hfree
  intro a b ha hb
  exact hcomm a ha b hb

theorem FF81Hyp.not_three_dvd_oddCore
    {B : Subgroup G} {X : Subgroup (MulAut ↥B)}
    (hB3 : IsPGroup 3 ↥B) (hBnt : Nontrivial ↥B)
    (hirr : ∀ U : Subgroup ↥B,
      (∀ σ : MulAut ↥B, σ ∈ X → Subgroup.map σ U = U) → U = ⊥ ∨ U = ⊤)
    (hYab : ∀ a b : X, a ∈ oddCore X → b ∈ oddCore X → a * b = b * a) :
    ¬ 3 ∣ Nat.card ↥(oddCore X) := by
  let Y : Subgroup (MulAut ↥B) := (oddCore X).map X.subtype
  have hYX : Y ≤ X := Subgroup.map_subtype_le (oddCore X)
  have hYnorm : ∀ σ : MulAut ↥B, σ ∈ X → ∀ y : MulAut ↥B, y ∈ Y →
      σ * y * σ⁻¹ ∈ Y := by
    intro σ hσ y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσ⟩ * g * ⟨σ, hσ⟩⁻¹,
      (oddCore_normal X).conj_mem g hg ⟨σ, hσ⟩, rfl⟩
  have hYab' : ∀ a : MulAut ↥B, a ∈ Y → ∀ b : MulAut ↥B, b ∈ Y → a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg Subtype.val (hYab g h hg hh)
  have hfaith : ∀ y : MulAut ↥B, (∀ x : ↥B, y x = x) → y = 1 := by
    intro y hy
    exact MulEquiv.ext (fun x => by simpa using hy x)
  have hnot := CFSG.not_three_dvd_card_of_irreducible_abelian_normal
    (B := ↥B) (X := X) (Y := Y) hYX hYnorm hYab' hirr hB3 hBnt hfaith
  have hcard : Nat.card Y = Nat.card ↥(oddCore X) := Subgroup.card_subtype X (oddCore X)
  rw [hcard] at hnot
  exact hnot

end CFSG.RankThree.PartTwo.Sec21.FF81
