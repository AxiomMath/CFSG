module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.K133.ParA

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.K133
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeList)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem isElemAb_of_le {p : ℕ} {G : Type*} [Group G] {A K : Subgroup G}
    (hA : IsElementaryAbelian p ↥A) (hKA : K ≤ A) : IsElementaryAbelian p ↥K :=
  CFSG.IsElementaryAbelian.of_le hA hKA

section Route

variable {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H]

theorem generation_of_seitzAt {d : TauCeti.LieTypeIndex} (hAt : ExtSeitzAt d) (hp5 : 5 ≤ p)
    (S : Subgroup H) [S.Normal] [IsSimpleGroup ↥S] (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hiso : IsoLie ↥S d) (hpd : p ≠ d.characteristic)
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) {F : Subgroup H}
    (hFab : IsElementaryAbelian p ↥F) (hF : Nat.card F = p ^ 2) :
    Subgroup.closure {s : H | s ∈ S ∧ ∃ F' : Subgroup H, F' ≤ F ∧ F' ≠ ⊥ ∧
      ∀ f ∈ F', f * s = s * f} = S ∨ (p = 5 ∧ (d = .tits ∨ d = .suzuki 2)) := by
  have hρ := conjNormal_injective_of_centralizer S hSc
  have hE'ab : CFSG.IsElementaryAbelian p (F.map (MulAut.conjNormal (H := S))) := by
    have := hFab
    exact CFSG.IsElementaryAbelian.map _
  have hE'card : Nat.card (F.map (MulAut.conjNormal (H := S))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hρ, hF]
  rcases hAt ↥S hnab hiso p Fact.out hp5 hpd _ hE'ab hE'card with hgen | hexc
  · left
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun s hs => hs.1
    · intro s hs
      have hmem : (⟨s, hs⟩ : ↥S) ∈ Subgroup.closure
          {k : ↥S | ∃ Φ : Subgroup (MulAut ↥S), Φ ≤ F.map (MulAut.conjNormal (H := S)) ∧ Φ ≠ ⊥ ∧
            ∀ φ ∈ Φ, φ k = k} := hgen ▸ Subgroup.mem_top _
      have hle : Subgroup.closure
          {k : ↥S | ∃ Φ : Subgroup (MulAut ↥S), Φ ≤ F.map (MulAut.conjNormal (H := S)) ∧ Φ ≠ ⊥ ∧
            ∀ φ ∈ Φ, φ k = k} ≤
          (Subgroup.closure {s : H | s ∈ S ∧ ∃ F' : Subgroup H, F' ≤ F ∧ F' ≠ ⊥ ∧
            ∀ f ∈ F', f * s = s * f}).comap S.subtype := by
        rw [Subgroup.closure_le]
        rintro k ⟨Φ, hΦE, hΦ1, hΦk⟩
        refine Subgroup.subset_closure ⟨k.2, F ⊓ Φ.comap (MulAut.conjNormal (H := S)),
          inf_le_left, ?_, ?_⟩
        · obtain ⟨⟨φ, hφΦ⟩, hφ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hΦ1
          obtain ⟨f, hfF, rfl⟩ := hΦE hφΦ
          have hf1 : f ≠ 1 := by
            rintro rfl
            exact hφ1 (Subtype.ext (map_one _))
          intro hbot
          have : f ∈ F ⊓ Φ.comap (MulAut.conjNormal (H := S)) := ⟨hfF, hφΦ⟩
          rw [hbot, Subgroup.mem_bot] at this
          exact hf1 this
        · intro f hf
          have h1 := congrArg (fun a : ↥S => (a : H)) (hΦk _ hf.2)
          simp only [MulAut.conjNormal_apply] at h1
          calc f * (k : H) = f * k * f⁻¹ * f := by group
            _ = (k : H) * f := by rw [h1]
      exact hle hmem
  · exact Or.inr hexc

end Route

end CFSG.RankThree.PartOne.K159F
