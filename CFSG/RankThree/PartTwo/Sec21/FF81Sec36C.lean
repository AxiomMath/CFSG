module

import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36W

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace S36

variable {G : Type} [Group G] [Finite G]

def monoV : Fin 4 → Fin 3 → (Fin 3 → ZMod 3) :=
  ![![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]],
    ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]]]

def monoM (k : Fin 4) (z : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  z 0 • monoV k 0 + z 1 • monoV k 1 + z 2 • monoV k 2

def πh : Fin 4 → Fin 13 → Fin 13 :=
  ![![0, 1, 2, 4, 3, 6, 5, 7, 8, 12, 11, 10, 9], ![1, 0, 2, 3, 4, 7, 8, 5, 6, 9, 10, 12, 11],
    ![1, 2, 0, 7, 8, 3, 4, 5, 6, 9, 12, 10, 11], ![0, 2, 1, 5, 6, 3, 4, 7, 8, 9, 11, 10, 12]]

def rep (w : ℕ) : Fin 13 := if w = 1 then 2 else if w = 2 then 4 else 11

def pathOf : Fin 13 → List (Fin 4) :=
  ![[2], [3], [], [0], [], [3, 0], [3], [2, 0], [2], [0, 1], [0], [], [1]]

theorem πh_dot : ∀ k : Fin 4, ∀ i : Fin 13, ∀ z0 z1 z2 : ZMod 3,
    dot (hypF i) ![z0, z1, z2] = 0 → dot (hypF (πh k i)) (monoM k ![z0, z1, z2]) = 0 := by
  decide +kernel

theorem pathOf_spec : ∀ i : Fin 13, (pathOf i).foldr (fun k j => πh k j) (rep (hypW i)) = i := by
  decide

theorem eq_rep_of_inv (c : Fin 13 → ℕ) (hc : ∀ k i, c (πh k i) = c i) (i : Fin 13) :
    c i = c (rep (hypW i)) := by
  conv_lhs => rw [← pathOf_spec i]
  generalize pathOf i = ks
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [List.foldr_cons, hc, ih]

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem conj_ε3 (hB : FF81Basis b L B b₁ b₂ b₃) {g : G} (m : Fin 3 → Fin 3 → ZMod 3)
    (h0 : g * b₁ * g⁻¹ = ε3 b₁ b₂ b₃ (m 0)) (h1 : g * b₂ * g⁻¹ = ε3 b₁ b₂ b₃ (m 1))
    (h2 : g * b₃ * g⁻¹ = ε3 b₁ b₂ b₃ (m 2)) (z : Fin 3 → ZMod 3) :
    g * ε3 b₁ b₂ b₃ z * g⁻¹ = ε3 b₁ b₂ b₃ (z 0 • m 0 + z 1 • m 1 + z 2 • m 2) := by
  show g * (b₁ ^ (z 0).val * b₂ ^ (z 1).val * b₃ ^ (z 2).val) * g⁻¹ = _
  rw [show g * (b₁ ^ (z 0).val * b₂ ^ (z 1).val * b₃ ^ (z 2).val) * g⁻¹ =
      (g * b₁ ^ (z 0).val * g⁻¹) * (g * b₂ ^ (z 1).val * g⁻¹) * (g * b₃ ^ (z 2).val * g⁻¹) by
      group, ← conj_pow, ← conj_pow, ← conj_pow, h0, h1, h2, ← hB.ε3_smul, ← hB.ε3_smul,
    ← hB.ε3_smul, ← hB.ε3_add, ← hB.ε3_add]

theorem ε3_b₁ : ε3 b₁ b₂ b₃ ![1, 0, 0] = b₁ := by simp [ε3, val_one3]
theorem ε3_b₂ : ε3 b₁ b₂ b₃ ![0, 1, 0] = b₂ := by simp [ε3, val_one3]
theorem ε3_b₃ : ε3 b₁ b₂ b₃ ![0, 0, 1] = b₃ := by simp [ε3, val_one3]

theorem ε3_b₁_inv (hB : FF81Basis b L B b₁ b₂ b₃) : ε3 b₁ b₂ b₃ ![2, 0, 0] = b₁⁻¹ := by
  have h3 : b₁ ^ 3 = 1 := hB.b_facts.1
  have : ε3 b₁ b₂ b₃ ![2, 0, 0] = b₁ ^ 2 := by
    simp [ε3, show (2 : ZMod 3).val = 2 from rfl]
  rw [this]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.exists_mono (hB : FF81Basis b L B b₁ b₂ b₃) (k : Fin 4) :
    ∃ g ∈ L, g * b₁ * g⁻¹ = ε3 b₁ b₂ b₃ (monoV k 0) ∧ g * b₂ * g⁻¹ = ε3 b₁ b₂ b₃ (monoV k 1) ∧
      g * b₃ * g⁻¹ = ε3 b₁ b₂ b₃ (monoV k 2) := by
  obtain ⟨-, -, -, ⟨n1, -, e10, e11, e12, e13⟩, ⟨n2, -, e20, e21, e22, e23⟩,
    ⟨n3, -, e30, e31, e32, e33⟩⟩ := hB.mono
  have lift : ∀ n : G, n * b * n⁻¹ = b → ∃ g ∈ L, ∀ x ∈ L, n * x * n⁻¹ = g * x * g⁻¹ := by
    intro n hn
    have hnb : n ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc n * b = n * b * n⁻¹ * n := by group
        _ = b * n := by rw [hn])
    exact kf_sp62Out G L hB.hyp.model n (hB.hyp.hLN hnb)
  fin_cases k
  · obtain ⟨g, hg, hgx⟩ := lift n1 e10
    refine ⟨g, hg, ?_, ?_, ?_⟩
    · rw [← hgx _ hB.hb₁, e11]; exact (ε3_b₁_inv hB).symm
    · rw [← hgx _ hB.hb₂, e12]; exact ε3_b₂.symm
    · rw [← hgx _ hB.hb₃, e13]; exact ε3_b₃.symm
  · obtain ⟨g, hg, hgx⟩ := lift n2 e20
    refine ⟨g, hg, ?_, ?_, ?_⟩
    · rw [← hgx _ hB.hb₁, e21]; exact ε3_b₂.symm
    · rw [← hgx _ hB.hb₂, e22]; exact ε3_b₁.symm
    · rw [← hgx _ hB.hb₃, e23]; exact ε3_b₃.symm
  · obtain ⟨g, hg, hgx⟩ := lift n3 e30
    refine ⟨g, hg, ?_, ?_, ?_⟩
    · rw [← hgx _ hB.hb₁, e31]; exact ε3_b₂.symm
    · rw [← hgx _ hB.hb₂, e32]; exact ε3_b₃.symm
    · rw [← hgx _ hB.hb₃, e33]; exact ε3_b₁.symm
  · obtain ⟨g, hg, e1, e2, e3⟩ := hB.monoL
    exact ⟨g, hg, e1.trans ε3_b₁.symm, e2.trans ε3_b₃.symm, e3.trans ε3_b₂.symm⟩

theorem card_inf_cenS_conjBy {X H : Subgroup G} {g : G} (hg : g ∈ Nor X) :
    Nat.card ↥(X ⊓ CenS (conjBy g H)) = Nat.card ↥(X ⊓ CenS H) := by
  have heq : conjBy g (X ⊓ CenS H) = X ⊓ CenS (conjBy g H) := by
    ext z
    rw [mem_conjBy_iff]
    have hX : g⁻¹ * z * g ∈ X ↔ z ∈ X := by
      constructor
      · intro h
        have := (Subgroup.mem_normalizer_iff.mp hg _).mp h
        rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at this
      · intro h
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) z).mp h
        rwa [inv_inv] at this
    simp only [Subgroup.mem_inf, hX, CenS, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
    · rw [mem_conjBy_iff] at hy
      have := h _ hy
      calc y * z = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = z * y := by group
    · have := h (g * y * g⁻¹) ⟨y, hy, rfl⟩
      calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
        _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [this]
        _ = (g⁻¹ * z * g) * y := by group
  rw [← heq, card_conjBy]

theorem card_hyp_rep (hB : FF81Basis b L B b₁ b₂ b₃) {X : Subgroup G} (hX : L ≤ Nor X)
    (i : Fin 13) :
    Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) =
      Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ (rep (hypW i)))) := by
  refine eq_rep_of_inv (fun i => Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i))) (fun k i => ?_) i
  obtain ⟨g, hgL, h0, h1, h2⟩ := hB.exists_mono k
  have hle : conjBy g (hyp b₁ b₂ b₃ i) ≤ hyp b₁ b₂ b₃ (πh k i) := by
    rintro _ ⟨h, hh, rfl⟩
    obtain ⟨z, rfl⟩ := hB.exists_ε3 (hyp_le i hh)
    change g * ε3 b₁ b₂ b₃ z * g⁻¹ ∈ _
    rw [conj_ε3 hB (monoV k) h0 h1 h2]
    refine (hB.mem_hyp _ _).2 ?_
    have hz := (hB.mem_hyp i z).1 hh
    rw [vec3_eta z] at hz
    have := πh_dot k i _ _ _ hz
    rwa [monoM] at this
  have heq : conjBy g (hyp b₁ b₂ b₃ i) = hyp b₁ b₂ b₃ (πh k i) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjBy, hB.card_hyp, hB.card_hyp])
  rw [← heq, card_inf_cenS_conjBy (hX hgL)]

end S36

end CFSG.RankThree.PartTwo.Sec21.FF81
