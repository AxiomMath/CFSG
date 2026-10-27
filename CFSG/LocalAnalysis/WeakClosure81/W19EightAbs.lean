module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightDih
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenLemmas

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup
open scoped commutatorElement

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem two_orbit_of_hyperplane {A B : Subgroup (LGL 2 W)} (hA : IsElemAbelian 2 A) (hBA : B ≤ A)
    (hidx : (B.subgroupOf A).index = 2) {w : W} (hw : ∀ b ∈ B, b w = w) {a₁ : LGL 2 W}
    (ha₁ : a₁ ∈ A) (hmv : a₁ w ≠ w) : ∀ b ∈ A, b w = w ∨ b w = a₁ w := by
  intro b hb
  by_cases hbB : b ∈ B
  · exact Or.inl (hw b hbB)
  · right
    have ha₁B : a₁ ∉ B := fun h => hmv (hw a₁ h)
    have key : (⟨b, hb⟩ : A) * ⟨a₁, ha₁⟩ ∈ B.subgroupOf A := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false (fun h => hbB h) (fun h => ha₁B h)
    have hba : b * a₁ ∈ B := key
    have h1 : b (a₁ w) = w := by
      have := hw _ hba
      simpa [LinearEquiv.mul_apply] using this
    have hbb : b * b = 1 := hA.mul_self_eq_one hb
    calc b w = b (b (a₁ w)) := by rw [h1]
      _ = a₁ w := by
        have := congrArg (fun f : LGL 2 W => f (a₁ w)) hbb
        simpa [LinearEquiv.mul_apply] using this

theorem exists_two_orbit_conf [Finite W] {A X : Subgroup (LGL 2 W)} (hA : IsElemAbelian 2 A)
    (hodd : Odd (Nat.card X)) (hAX : A ≤ normalizer (X : Set (LGL 2 W)))
    (hC : A ⊓ centralizer (X : Set (LGL 2 W)) = ⊥) (h4 : 4 ≤ Nat.card A)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w : W, a (b w - w) = b w - w) :
    ∃ (a₁ x₂ : LGL 2 W) (w : W), a₁ ∈ A ∧ x₂ ∈ X ∧ x₂ ≠ 1 ∧ a₁ w ≠ w ∧
      (∀ b ∈ A, b w = w ∨ b w = a₁ w) ∧ x₂ (a₁ w - w) = a₁ w - w := by
  obtain ⟨B, a₁, x₂, w, hBA, hidx, ha₁, hx₂, hx₂1, hBw, hmv, hfix⟩ :=
    exists_dihedral_conf hA hodd hAX hC h4 hquad
  exact ⟨a₁, x₂, w, ha₁, hx₂, hx₂1, hmv, two_orbit_of_hyperplane hA hBA hidx hBw ha₁ hmv, hfix⟩

theorem exists_two_orbit_of_comm_ne [Finite W] {A X : Subgroup (LGL 2 W)} (hA : IsElemAbelian 2 A)
    (h4 : 4 ≤ Nat.card A) (hAX : A ≤ normalizer (X : Set (LGL 2 W))) (hodd : Odd (Nat.card X))
    (hne : ⁅X, A⁆ ≠ ⊥) :
    ∃ (a₁ : LGL 2 W) (w : W), a₁ ∈ A ∧ a₁ w ≠ w ∧ ∀ b ∈ A, b w = w ∨ b w = a₁ w := by
  by_contra hcon
  apply hne
  refine six_thirteen_A hA (by simpa using h4) hAX hodd fun D hD => ?_
  have hDA : D ≤ A := hD.1
  have hidx : (D.subgroupOf A).index = 2 :=
    (CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.mem_hyperplanes_iff_index hDA).1 hD
  refine le_antisymm (fun w hw => ?_) (fixSub_anti _ _ hDA)
  rw [mem_fixSub] at hw ⊢
  by_contra hnot
  have hex : ∃ a ∈ A, a w ≠ w := by
    by_contra h'
    exact hnot fun a ha => by
      by_contra hne'
      exact h' ⟨a, ha, hne'⟩
  obtain ⟨a, ha, hmv⟩ := hex
  exact hcon ⟨a, w, ha, hmv, two_orbit_of_hyperplane hA hDA hidx hw ha hmv⟩

theorem eq_bot_of_normal_isPGroup_irreducible [Finite W] [Nontrivial W] {K N : Subgroup (LGL 2 W)}
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ k ∈ K, ∀ u ∈ U, k u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hNK : N ≤ K) (hn : K ≤ normalizer (N : Set (LGL 2 W))) (hN : IsPGroup 2 N) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ k ∈ K, ∀ u ∈ fixSub N, k u ∈ fixSub N := fun k hk u hu =>
    map_mem_fixSub_of_mem_normalizer N (hn hk) hu
  obtain ⟨u, -, hu0, hufix⟩ := exists_fixed_of_isPGroup (U := ⊤) hN
    (top_ne_bot (α := Submodule (ZMod 2) W)) (fun _ _ _ _ => Submodule.mem_top)
  have hne : fixSub N ≠ ⊥ := fun h => hu0 (by
    have : u ∈ fixSub N := hufix
    rw [h] at this
    simpa using this)
  rcases hirr (fixSub N) hinv with h | h
  · exact absurd h hne
  · exact (fixSub_eq_top_iff N).1 h

end CFSG.LocalAnalysis.WeakClosure81

end
