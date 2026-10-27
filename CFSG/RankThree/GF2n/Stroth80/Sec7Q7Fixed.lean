module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7RootLemma

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Sec7Q7MovedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ g ∈ M, g ∈ Subgroup.normalizer (LB M Q B : Set G) →
    conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) →
    (∀ k ∈ hc.CN t,
      k ∈ Subgroup.normalizer (conjSubgroup g (Vt M (LB M Q B) B Z t) : Set G)) →
    (∃ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), ∃ l ∈ LB M Q B,
      ⁅l, v⁆ ∉ Vt M (LB M Q B) B Z t) → False

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_commutator_eq (g a b : G) :
    ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem sec7Q7Fixed_of_inputs (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hCV : Sec7CVStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → ∀ g ∈ M, g ∈ Subgroup.normalizer (LB M Q B : Set G) →
      (∀ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), ∀ l ∈ LB M Q B,
        ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t) →
      conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  intro G _ _ M Q Z B hc n t hs g hg hgN hcase
  have hgM : g⁻¹ ∈ M := M.inv_mem hg
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hLn : ∀ l ∈ LB M Q B, g * l * g⁻¹ ∈ LB M Q B := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hgN l).mp hl
  have hLn' : ∀ l ∈ LB M Q B, g⁻¹ * l * g ∈ LB M Q B := fun l hl => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) l).mp hl
    simpa using this
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV'Q : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Q := fun x hx => by
    rw [← hc.conj_Q_eq hg, mem_conjSubgroup]
    exact hVQ (mem_conjSubgroup.mp hx)
  have hsub : ⁅Vt M (LB M Q B) B Z t, LB M Q B⁆ ≤
      conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [mem_conjSubgroup, inv_inv]
    have hgv : g * v * g⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * v * g⁻¹) * g = v by group]
      exact hv
    have h1 := hcase _ hgv _ (hLn l hl)
    have e : g * ⁅v, l⁆ * g⁻¹ = ⁅g * l * g⁻¹, g * v * g⁻¹⁆⁻¹ := by
      rw [commutatorElement_inv, conj_commutator_eq]
    rw [e]
    exact (Vt M (LB M Q B) B Z t).inv_mem h1
  have hle : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Vt M (LB M Q B) B Z t := by
    intro x hx
    refine (hCV G M Q Z B hc n t hs x (hV'Q hx)).mpr fun y hy => ?_
    obtain ⟨hyL, hyN⟩ := Subgroup.mem_inf.mp hy
    have hl₀ : g⁻¹ * y * g ∈ LB M Q B := hLn' y hyL
    have hcomm : ∀ v ∈ ⁅Vt M (LB M Q B) B Z t, LB M Q B⁆, ⁅g⁻¹ * y * g, v⁆ ∈ Z := by
      intro v hv
      have hv' : g * v * g⁻¹ ∈ Vt M (LB M Q B) B Z t := by
        have := mem_conjSubgroup.mp (hsub hv)
        simpa using this
      have e : ⁅g⁻¹ * y * g, v⁆ = g⁻¹ * ⁅y, g * v * g⁻¹⁆ * g := by
        simp only [commutatorElement_def]
        group
      rw [e]
      have h1 := hZn g⁻¹ hgM _ ((Ctx.mem_CN.mp hyN).2 _ hv')
      simpa using h1
    have hl₀N := mem_CN_of_comm_comm_mem_Z hA hPts hc hs hl₀ hcomm
    have hx' : g⁻¹ * x * g ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hx
    have e : ⁅y, x⁆ = g * ⁅g⁻¹ * y * g, g⁻¹ * x * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hZn g hg _ ((Ctx.mem_CN.mp hl₀N).2 _ hx')
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem sec7Q7_of_moved (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hCV : Sec7CVStatement) (hB : Sec7Q7MovedStatement) : Sec7Q7Statement := by
  intro G _ _ M Q Z B hc n t hs g hg hgN hW hN
  by_cases hcase : ∀ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), ∀ l ∈ LB M Q B,
      ⁅l, v⁆ ∈ Vt M (LB M Q B) B Z t
  · exact sec7Q7Fixed_of_inputs hA hPts hCV G M Q Z B hc n t hs g hg hgN hcase
  · push Not at hcase
    obtain ⟨v, hv, l, hl, hlv⟩ := hcase
    exact (hB G M Q Z B hc n t hs g hg hgN hW hN ⟨v, hv, l, hl, hlv⟩).elim

end CFSG.RankThree.GF2n.Stroth80
