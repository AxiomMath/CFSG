module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3SixKer
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem leftSingular_le {x : ℕ → V} {i k : ℕ} (hik : i + 2 ≤ k)
    (hadj : ∀ m, i ≤ m → m < k → Γ.Adj (x m) (x (m + 1)))
    (h : LeftSingular Γ G x i k) : ∀ g ∈ stabRange G x i k, g ∈ nbrStab Γ G (x i) := by
  obtain ⟨w, hw, hwne, hfix⟩ := h
  intro g hg
  exact F.fix_two_nbrs hw (hadj i le_rfl (by omega)) hwne (hfix g hg)
    (mem_stabRange.1 hg (i + 1) (by omega) (by omega))

theorem rightSingular_le {x : ℕ → V} {i k : ℕ} (hik : i + 2 ≤ k)
    (hadj : ∀ m, i ≤ m → m < k → Γ.Adj (x m) (x (m + 1)))
    (h : RightSingular Γ G x i k) : ∀ g ∈ stabRange G x i k, g ∈ nbrStab Γ G (x k) := by
  obtain ⟨w, hw, hwne, hfix⟩ := h
  intro g hg
  have hk : Γ.Adj (x k) (x (k - 1)) := by
    have := (hadj (k - 1) (by omega) (by omega)).symm
    rwa [show k - 1 + 1 = k by omega] at this
  exact F.fix_two_nbrs hw hk hwne (hfix g hg) (mem_stabRange.1 hg (k - 1) (by omega) (by omega))

theorem mem_stabRange_four {x : ℕ → V} {i : ℕ}
    (hadj : ∀ m, i ≤ m → m < i + 4 → Γ.Adj (x m) (x (m + 1)))
    (hnb : ∀ m, i ≤ m → m + 2 ≤ i + 4 → x m ≠ x (m + 2)) {g : G} :
    g ∈ stabRange G x i (i + 4) ↔ g ∈ nbrStab Γ G (x (i + 1)) ∧ g ∈ nbrStab Γ G (x (i + 2)) ∧
      g ∈ nbrStab Γ G (x (i + 3)) := by
  rw [F.mem_stabRange_iff_nbrStab (by omega) hadj hnb]
  constructor
  · intro h
    exact ⟨h (i + 1) (by omega) (by omega), h (i + 2) (by omega) (by omega),
      h (i + 3) (by omega) (by omega)⟩
  · rintro ⟨h1, h2, h3⟩ m hm1 hm2
    obtain rfl | rfl | rfl : m = i + 1 ∨ m = i + 2 ∨ m = i + 3 := by omega
    · exact h1
    · exact h2
    · exact h3

theorem valence_eq_three {u v : V} (huv : Γ.Adj u v) (h : pval Γ u = 5) : pval Γ v = 3 := by
  have h1 := F.alternating u v huv
  have e1 : pval Γ u = Nat.card (Γ.neighborSet u) := rfl
  have e2 : pval Γ v = Nat.card (Γ.neighborSet v) := rfl
  rcases F.valence v with h' | h' <;> omega

theorem valence_eq_five {u v : V} (huv : Γ.Adj u v) (h : pval Γ u = 3) : pval Γ v = 5 := by
  have h1 := F.alternating u v huv
  have e1 : pval Γ u = Nat.card (Γ.neighborSet u) := rfl
  have e2 : pval Γ v = Nat.card (Γ.neighborSet v) := rfl
  rcases F.valence v with h' | h' <;> omega

theorem nbrR_le_of_left (h40 : Fan40 F) {a₁ a₂ a₃ a₄ : V} (h12 : Γ.Adj a₁ a₂) (h23 : Γ.Adj a₂ a₃)
    (h34 : Γ.Adj a₃ a₄) (h13 : a₁ ≠ a₃) (h24 : a₂ ≠ a₄) (ha4 : pval Γ a₄ = 3)
    (hL : nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ≤ nbrStab Γ G a₁) :
    nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ≤ nbrStab Γ G a₄ := by
  set D := nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ with hD
  have hfin : Finite ↥D := by
    have := F.loc_finite a₃
    exact Finite.of_injective (Subgroup.inclusion (show D ≤ MulAction.stabilizer G a₃ from
      fun g hg => F.nbrStab_le_stabilizer a₃ hg.2)) (Subgroup.inclusion_injective _)
  have hDst : D ≤ MulAction.stabilizer G a₄ ⊓ MulAction.stabilizer G a₃ := fun g hg =>
    ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg.2 a₄ h34),
      F.nbrStab_le_stabilizer a₃ hg.2⟩
  have hle : (D ⊓ nbrStab Γ G a₄).relIndex D ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact F.relIndex_le_two h34.symm ha4 hDst
  have hMN : D ⊓ nbrStab Γ G a₄ ≤ nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ :=
    fun y hy => ⟨⟨hL hy, hy.1.1⟩, hy.1.2⟩
  have hND : nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ≤ D := fun y hy => ⟨hy.1.2, hy.2⟩
  have hne : nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ≠ D := by
    intro h
    apply F.not_inf_le_left h40 h12 h23 h34 h13 h24
    intro y hy
    have : y ∈ nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ := by rw [h]; exact hy
    exact this.1.1
  have := eq_of_relIndex_le_two hMN hND hle (relIndex_ne_zero_of_finite _ _) hne
  exact fun y hy => (this hy).2

theorem nbrL_le_of_right (h40 : Fan40 F) {a₂ a₃ a₄ a₅ : V} (h23 : Γ.Adj a₂ a₃) (h34 : Γ.Adj a₃ a₄)
    (h45 : Γ.Adj a₄ a₅) (h24 : a₂ ≠ a₄) (h35 : a₃ ≠ a₅) (ha2 : pval Γ a₂ = 3)
    (hR : nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ≤ nbrStab Γ G a₅) :
    nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ⊓ nbrStab Γ G a₅ ≤ nbrStab Γ G a₂ := by
  set D := nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ with hD
  have hfin : Finite ↥D := by
    have := F.loc_finite a₃
    exact Finite.of_injective (Subgroup.inclusion (show D ≤ MulAction.stabilizer G a₃ from
      fun g hg => F.nbrStab_le_stabilizer a₃ hg.1)) (Subgroup.inclusion_injective _)
  have hDst : D ≤ MulAction.stabilizer G a₂ ⊓ MulAction.stabilizer G a₃ := fun g hg =>
    ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg.1 a₂ h23.symm),
      F.nbrStab_le_stabilizer a₃ hg.1⟩
  have hMeq : nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ = nbrStab Γ G a₂ ⊓ D :=
    inf_assoc _ _ _
  have hle : (nbrStab Γ G a₂ ⊓ D).relIndex D ≤ 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact F.relIndex_le_two h23 ha2 hDst
  have hMN : nbrStab Γ G a₂ ⊓ D ≤ D ⊓ nbrStab Γ G a₅ := fun y hy =>
    ⟨hy.2, hR (by rw [hMeq]; exact hy)⟩
  have hND : D ⊓ nbrStab Γ G a₅ ≤ D := inf_le_left
  have hne : D ⊓ nbrStab Γ G a₅ ≠ D := by
    intro h
    apply F.not_inf_le_right h40 h23 h34 h45 h24 h35
    intro y hy
    have : y ∈ D ⊓ nbrStab Γ G a₅ := by rw [h]; exact hy
    exact this.2
  have := eq_of_relIndex_le_two hMN hND hle (relIndex_ne_zero_of_finite _ _) hne
  exact fun y hy => (this hy).1

theorem false_of_iii (L : LocalFacts F) (h32 : Fan32 F) (h40 : Fan40 F) {a₁ a₂ a₃ a₄ a₅ : V}
    (h12 : Γ.Adj a₁ a₂) (h23 : Γ.Adj a₂ a₃) (h34 : Γ.Adj a₃ a₄) (h45 : Γ.Adj a₄ a₅)
    (h24 : a₂ ≠ a₄) (ha2 : pval Γ a₂ = 3) (ha3 : pval Γ a₃ = 5) (ha4 : pval Γ a₄ = 3)
    (hNR : nbrStab Γ G a₁ ⊓ nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ≤ nbrStab Γ G a₄)
    (hNL : nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ⊓ nbrStab Γ G a₅ ≤ nbrStab Γ G a₂) : False :=
  F.false_of_le_ballStab L h32 h23 h34 ha2 ha4 ha3
    (F.le_ballStab_of_both L h40 h12 h23 h34 h45 h24 hNR hNL)

theorem false_of_ii (L : LocalFacts F) (h32 : Fan32 F) (h40 : Fan40 F) {a₁ a₂ a₃ a₄ a₅ : V}
    (h12 : Γ.Adj a₁ a₂) (h23 : Γ.Adj a₂ a₃) (h34 : Γ.Adj a₃ a₄) (h45 : Γ.Adj a₄ a₅)
    (h13 : a₁ ≠ a₃) (h24 : a₂ ≠ a₄) (h35 : a₃ ≠ a₅) (ha2 : pval Γ a₂ = 3) (ha3 : pval Γ a₃ = 5)
    (ha4 : pval Γ a₄ = 3)
    (hL : nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ≤ nbrStab Γ G a₁)
    (hR : nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ≤ nbrStab Γ G a₅) : False :=
  F.false_of_iii L h32 h40 h12 h23 h34 h45 h24 ha2 ha3 ha4
    (F.nbrR_le_of_left h40 h12 h23 h34 h13 h24 ha4 hL)
    (F.nbrL_le_of_right h40 h23 h34 h45 h24 h35 ha2 hR)

theorem false_of_i (L : LocalFacts F) (h32 : Fan32 F) (h40 : Fan40 F) {a₁ a₂ a₃ a₄ : V}
    (h12 : Γ.Adj a₁ a₂) (h23 : Γ.Adj a₂ a₃) (h34 : Γ.Adj a₃ a₄) (h13 : a₁ ≠ a₃) (h24 : a₂ ≠ a₄)
    (ha2 : pval Γ a₂ = 3) (ha3 : pval Γ a₃ = 5) (ha4 : pval Γ a₄ = 3)
    (hL : nbrStab Γ G a₂ ⊓ nbrStab Γ G a₃ ⊓ nbrStab Γ G a₄ ≤ nbrStab Γ G a₁)
    (hc4 : (nbrStab Γ G a₁).relIndex (MulAction.stabilizer G a₁ ⊓ MulAction.stabilizer G a₂) = 4) :
    False := by
  have hNR := F.nbrR_le_of_left h40 h12 h23 h34 h13 h24 ha4 hL
  obtain ⟨h, hh, hha⟩ := F.loc_trans a₂ a₁ a₃ h12.symm h23
  have hh2 : h • a₂ = a₂ := MulAction.mem_stabilizer_iff.1 hh
  have hc : (nbrStab Γ G a₃).relIndex (MulAction.stabilizer G a₃ ⊓ MulAction.stabilizer G a₂) =
      pval Γ a₃ - 1 := by
    have := F.relIndex_nbrStab_smul h a₁ a₂
    rw [hha, hh2, hc4] at this
    rw [this, ha3]
  have hM := F.le_ballStab_of_left L h40 h12 h23 h34 h24 ha2 hc hNR
  exact F.false_of_le_ballStab L h32 h23 h34 ha2 ha4 ha3 hM

end FanTree

theorem fan_3_6 {F : FanTree Γ G} (L : LocalFacts F) (h32 : Fan32 F) : Fan36 F := by
  intro h40 P hv
  have hv1 : pval Γ (P.vert 1) = 5 := by
    have e : pval Γ (P.vert 1) = Nat.card (Γ.neighborSet (P.vert 1)) := rfl
    rcases F.valence (P.vert 1) with h | h <;> omega
  have h12 : Γ.Adj (P.vert 1) (P.vert 2) := P.adj 1 (by norm_num)
  have h23 : Γ.Adj (P.vert 2) (P.vert 3) := P.adj 2 (by norm_num)
  have h34 : Γ.Adj (P.vert 3) (P.vert 4) := P.adj 3 (by norm_num)
  have h45 : Γ.Adj (P.vert 4) (P.vert 5) := P.adj 4 (by norm_num)
  have h13 : P.vert 1 ≠ P.vert 3 := P.nb 1 (by norm_num)
  have h24 : P.vert 2 ≠ P.vert 4 := P.nb 2 (by norm_num)
  have h35 : P.vert 3 ≠ P.vert 5 := P.nb 3 (by norm_num)
  have hv2 : pval Γ (P.vert 2) = 3 := F.valence_eq_three h12 hv1
  have hv3 : pval Γ (P.vert 3) = 5 := F.valence_eq_five h23 hv2
  have hv4 : pval Γ (P.vert 4) = 3 := F.valence_eq_three h34 hv3
  have kerL : LeftSingular Γ G P.vert 1 5 →
      nbrStab Γ G (P.vert 2) ⊓ nbrStab Γ G (P.vert 3) ⊓ nbrStab Γ G (P.vert 4) ≤
        nbrStab Γ G (P.vert 1) := by
    intro h y hy
    have hyS : y ∈ stabRange G P.vert 1 (1 + 4) :=
      (F.mem_stabRange_four (i := 1) (fun m _ hm => P.adj m (by omega))
        (fun m _ hm => P.nb m (by omega))).2 ⟨hy.1.1, hy.1.2, hy.2⟩
    exact F.leftSingular_le (by norm_num) (fun m _ hm => P.adj m (by omega)) h y hyS
  have kerR : RightSingular Γ G P.vert 1 5 →
      nbrStab Γ G (P.vert 2) ⊓ nbrStab Γ G (P.vert 3) ⊓ nbrStab Γ G (P.vert 4) ≤
        nbrStab Γ G (P.vert 5) := by
    intro h y hy
    have hyS : y ∈ stabRange G P.vert 1 (1 + 4) :=
      (F.mem_stabRange_four (i := 1) (fun m _ hm => P.adj m (by omega))
        (fun m _ hm => P.nb m (by omega))).2 ⟨hy.1.1, hy.1.2, hy.2⟩
    exact F.rightSingular_le (by norm_num) (fun m _ hm => P.adj m (by omega)) h y hyS
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hLS, g, hg, hng⟩
    exact F.false_of_i L h32 h40 h12 h23 h34 h13 h24 hv2 hv3 hv4 (kerL hLS)
      (F.relIndex_eq_four_of_not_gcirc h12 hg hng)
  · rintro ⟨hLS, hRS⟩
    exact F.false_of_ii L h32 h40 h12 h23 h34 h45 h13 h24 h35 hv2 hv3 hv4 (kerL hLS) (kerR hRS)
  · rintro ⟨hLS, hRS⟩
    have hNL : nbrStab Γ G (P.vert 3) ⊓ nbrStab Γ G (P.vert 4) ⊓ nbrStab Γ G (P.vert 5) ≤
        nbrStab Γ G (P.vert 2) := by
      intro y hy
      have hyS : y ∈ stabRange G P.vert 2 (2 + 4) :=
        (F.mem_stabRange_four (i := 2) (fun m _ hm => P.adj m (by omega))
          (fun m _ hm => P.nb m (by omega))).2 ⟨hy.1.1, hy.1.2, hy.2⟩
      exact F.leftSingular_le (by norm_num) (fun m _ hm => P.adj m (by omega)) hLS y hyS
    have hNR : nbrStab Γ G (P.vert 1) ⊓ nbrStab Γ G (P.vert 2) ⊓ nbrStab Γ G (P.vert 3) ≤
        nbrStab Γ G (P.vert 4) := by
      intro y hy
      have hyS : y ∈ stabRange G P.vert 0 (0 + 4) :=
        (F.mem_stabRange_four (i := 0) (fun m _ hm => P.adj m (by omega))
          (fun m _ hm => P.nb m (by omega))).2 ⟨hy.1.1, hy.1.2, hy.2⟩
      exact F.rightSingular_le (by norm_num) (fun m _ hm => P.adj m (by omega)) hRS y hyS
    exact F.false_of_iii L h32 h40 h12 h23 h34 h45 h24 hv2 hv3 hv4 hNR hNL

end CFSG.Quasithin.Fan86
