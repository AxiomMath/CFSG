module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Open CFSG.Assembly
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Basis3

theorem acts_sgnOn_iff {G : Type} [Group G] {k : ℕ}
    (B : Basis3 G k) (g : G) (T : Finset (Fin k)) :
    B.Acts g (spMat 1 (sgnOn T)) ↔
      ∀ j, g * B.b j * g⁻¹ = if j ∈ T then (B.b j)⁻¹ else B.b j := by
  have hcol : ∀ j : Fin k, (fun i => spMat 1 (sgnOn T) i j) = Pi.single j (sgnOn T j) := by
    intro j
    ext i
    simp [spMat, Pi.single_apply, eq_comm]
  have hvec : ∀ j : Fin k, B.vec (Pi.single j (sgnOn T j)) =
      if j ∈ T then (B.b j)⁻¹ else B.b j := by
    intro j
    by_cases hj : j ∈ T
    · rw [if_pos hj, show sgnOn T j = -1 by simp [sgnOn, hj]]
      have hv : (Pi.single j (-1) : Coords k) = -(Pi.single j (1 : ZMod 3) : Coords k) := by
        ext i
        by_cases hij : i = j <;> simp [hij]
      rw [hv]
      exact (B.vec_neg (Pi.single j (1 : ZMod 3))).trans
        (congrArg Inv.inv (B.vec_single j))
    · rw [if_neg hj, show sgnOn T j = 1 by simp [sgnOn, hj], B.vec_single]
  constructor
  · intro h j
    rw [h j, hcol, hvec]
  · intro h j
    rw [hcol, hvec]
    exact h j

end Basis3

private theorem sgnOn_singleton_one_not_mem_evenFix0 :
    spMat 1 (sgnOn ({1} : Finset (Fin 8))) ∉ evenFix0 7 := by
  intro h
  obtain ⟨σ, s, -, ⟨-, -, hprod⟩, heq⟩ := h
  have hsg : ∀ j : Fin 8, sgnOn ({1} : Finset (Fin 8)) j ≠ 0 := by
    intro j
    by_cases hj : j = 1 <;> simp [sgnOn, hj]
  have hsEq : s = sgnOn ({1} : Finset (Fin 8)) := by
    funext j
    have he := congrArg (fun A : Matrix (Fin 8) (Fin 8) (ZMod 3) => A j j) heq
    have he' : sgnOn ({1} : Finset (Fin 8)) j = if j = σ j then s j else 0 := by
      simpa [spMat] using he
    have hj : j = σ j := by
      by_contra hn
      rw [if_neg hn] at he'
      exact hsg j he'
    simpa only [if_pos hj] using he'.symm
  rw [hsEq] at hprod
  have hneg : ∏ i : Fin 7, sgnOn ({1} : Finset (Fin 8)) i.succ = (-1 : ZMod 3) := by
    decide +kernel
  exact (by decide : (-1 : ZMod 3) ≠ 1) (hneg.symm.trans hprod)

theorem no_single_inverter_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (g : G) (hgK : g ∈ K)
    (hg : ∀ j : Fin 8, g * B.b j * g⁻¹ = if j = 1 then (B.b j)⁻¹ else B.b j) : False := by
  have hact : B.Acts g (spMat 1 (sgnOn ({1} : Finset (Fin 8)))) :=
    (B.acts_sgnOn_iff g {1}).mpr (by simpa only [Finset.mem_singleton] using hg)
  have hmem : spMat 1 (sgnOn ({1} : Finset (Fin 8))) ∈ B.realized K := ⟨g, hgK, hact⟩
  rw [realized_eq_evenFix0_of_std_twD7 hstd B hB hrec] at hmem
  exact sgnOn_singleton_one_not_mem_evenFix0 hmem

theorem not_inner_on_commutator_centralizer_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (g : G) (hgK : g ∈ K) (hgb : g * B.b 1 * g⁻¹ = (B.b 1)⁻¹) :
    ¬ ∃ m ∈ ⁅centralizer ({B.b 1} : Set G) ⊓ K,
        centralizer ({B.b 1} : Set G) ⊓ K⁆,
      ∀ x ∈ ⁅centralizer ({B.b 1} : Set G) ⊓ K,
        centralizer ({B.b 1} : Set G) ⊓ K⁆,
        g * x * g⁻¹ = m * x * m⁻¹ := by
  rintro ⟨m, hm, hinner⟩
  let C : Subgroup G := centralizer ({B.b 1} : Set G) ⊓ K
  have hmC : m ∈ C := (commutator_le_self C) hm
  have hmK : m ∈ K := hmC.2
  let d := m⁻¹ * g
  have hdK : d ∈ K := K.mul_mem (K.inv_mem hmK) hgK
  have hKC : K ≤ centralizer ({b₀} : Set G) := hstd.2.1.1.2.1
  have hd0 : d * B.b 0 * d⁻¹ = B.b 0 := by
    have hc : Commute d b₀ :=
      (mem_centralizer_iff.mp (hKC hdK) b₀ (Set.mem_singleton b₀)).symm
    rw [hB.2.1, hc.eq, mul_inv_cancel_right]
  have hd1 : d * B.b 1 * d⁻¹ = (B.b 1)⁻¹ := by
    have hmc : Commute m (B.b 1) :=
      (mem_centralizer_iff.mp hmC.1 (B.b 1) (Set.mem_singleton (B.b 1))).symm
    calc d * B.b 1 * d⁻¹ = m⁻¹ * (g * B.b 1 * g⁻¹) * m := by dsimp [d]; group
      _ = m⁻¹ * (B.b 1)⁻¹ * m := by rw [hgb]
      _ = (B.b 1)⁻¹ := by rw [hmc.inv_left.inv_right.eq, inv_mul_cancel_right]
  have hdtail : ∀ i : Fin 6, d * B.b i.succ.succ * d⁻¹ = B.b i.succ.succ := by
    intro i
    have hiM := tail_mem_commutator_centralizer_of_std_twD7 hstd B hB hrec i
    calc
      d * B.b i.succ.succ * d⁻¹ = m⁻¹ * (g * B.b i.succ.succ * g⁻¹) * m := by
        dsimp [d]
        group
      _ = m⁻¹ * (m * B.b i.succ.succ * m⁻¹) * m := by rw [hinner _ hiM]
      _ = B.b i.succ.succ := by group
  have hd : ∀ j : Fin 8, d * B.b j * d⁻¹ = if j = 1 then (B.b j)⁻¹ else B.b j := by
    intro j
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) j
    · simpa using hd0
    · simpa using hd1
    · have hi1 : (i.succ.succ : Fin 8) ≠ 1 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at hv
        omega
      simpa only [if_neg hi1] using hdtail i
  exact no_single_inverter_of_std_twD7 hstd B hB hrec d hdK hd

theorem exists_beta_line_swap_outer_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    ∃ g ∈ K, g ∈ normalizer (E : Set G) ∧
      g ∈ normalizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
        centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ∧
      g * (b₀ * B.b 1) * g⁻¹ = (b₀⁻¹ * B.b 1)⁻¹ ∧
      g * (b₀⁻¹ * B.b 1) * g⁻¹ = (b₀ * B.b 1)⁻¹ ∧
      g * B.b 2 * g⁻¹ = (B.b 2)⁻¹ ∧
      ¬ ∃ m ∈ ⁅centralizer ({B.b 1} : Set G) ⊓ K,
          centralizer ({B.b 1} : Set G) ⊓ K⁆,
        ∀ x ∈ ⁅centralizer ({B.b 1} : Set G) ⊓ K,
          centralizer ({B.b 1} : Set G) ⊓ K⁆,
          g * x * g⁻¹ = m * x * m⁻¹ := by
  obtain ⟨g, hgK, hgE, hgM, hg0, hg1, hg2⟩ :=
    exists_beta_line_swap_of_std_twD7 hstd B hB hrec
  have hKC : K ≤ centralizer ({b₀} : Set G) := hstd.2.1.1.2.1
  have hgb₀ : g * b₀ * g⁻¹ = b₀ := by
    have hc : Commute g b₀ :=
      (mem_centralizer_iff.mp (hKC hgK) b₀ (Set.mem_singleton b₀)).symm
    rw [hc.eq, mul_inv_cancel_right]
  have hc : Commute b₀ (B.b 1) := hB.2.1 ▸ B.comm 0 1
  have heq : b₀ * (g * B.b 1 * g⁻¹) = b₀ * (B.b 1)⁻¹ := by
    calc
      b₀ * (g * B.b 1 * g⁻¹) = (g * b₀ * g⁻¹) * (g * B.b 1 * g⁻¹) := by rw [hgb₀]
      _ = g * (b₀ * B.b 1) * g⁻¹ := by group
      _ = (b₀⁻¹ * B.b 1)⁻¹ := hg0
      _ = b₀ * (B.b 1)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
        exact hc.inv_right.eq.symm
  have hgb₁ : g * B.b 1 * g⁻¹ = (B.b 1)⁻¹ := mul_left_cancel heq
  exact ⟨g, hgK, hgE, hgM, hg0, hg1, hg2,
    not_inner_on_commutator_centralizer_of_std_twD7 hstd B hB hrec g hgK hgb₁⟩

end CFSG.StandardType.FrameRoute.FS81
