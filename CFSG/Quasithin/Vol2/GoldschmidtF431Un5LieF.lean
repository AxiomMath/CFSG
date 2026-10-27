module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieA
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Par

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open scoped commutatorElement
open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5
  CFSG.Quasithin.H13.Sec53F.Unit

section Unique

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem V4_unique_Y {E : Subgroup (hypPSU h 2 1)} (hE : E ≤ hypProjUnitriangular h 2 1)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1)
    (hcard : Nat.card E = Nat.card (v5Y h)) : E = v5Y h := by
  have := finite_hypPSU_five h
  set G : Subgroup (hypSU h 2 1) := hypUnitriangular h 2 1 ⊓ E.comap (hypProj h 2 1) with hG
  have hGU : G ≤ hypUnitriangular h 2 1 := inf_le_left
  have hmap : G.map (hypProj h 2 1) = E := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg.2
    · intro hx
      obtain ⟨u, hu, rfl⟩ := hE hx
      exact ⟨u, ⟨hu, hx⟩, rfl⟩
  have hGc : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy =>
    hypProj_eq_of_mem_U (mul_mem (hGU hx) (hGU hy)) (mul_mem (hGU hy) (hGU hx))
      (by rw [map_mul, map_mul]; exact hab _ hx.2 _ hy.2)
  have hGs : ∀ x ∈ G, x * x = 1 := fun x hx =>
    hypProj_eq_of_mem_U (mul_mem (hGU hx) (hGU hx)) (one_mem _)
      (by rw [map_mul, map_one, ← sq]; exact hsq _ hx.2)
  have hcardG : Nat.card G = Nat.card E := by
    rw [← hmap]
    exact (card_map_hypProj hGU).symm
  rcases elemAb_le_Vsub_or_card_le hGU hGc hGs with hV | hle
  · have hEV : E ≤ v5Y h := by
      rw [← hmap]
      exact Subgroup.map_mono hV
    exact Subgroup.eq_of_le_of_card_ge hEV hcard.ge
  · exfalso
    have h4 : (2 ^ f) ^ 4 ≤ (2 ^ f) ^ 3 := by
      rw [← card_v5Y (h := h), ← hcard, ← hcardG]
      exact hle
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.one_le; omega)
    exact absurd h4 (not_le.2 (Nat.pow_lt_pow_right h1 (by norm_num)))

end Unique

section Perfect

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def nuP (g : hypSU h 2 1) : K := mat g ιe₁ ιe₁ * h.bar (mat g ιe₁ ιe₁)

theorem mat_mul_e₁e₁ {g g' : hypSU h 2 1} (hg' : g' ∈ u5PtStab h) :
    mat (g * g') ιe₁ ιe₁ = mat g ιe₁ ιe₁ * mat g' ιe₁ ιe₁ := by
  have hcol := (mem_u5PtStab_iff g').1 hg'
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single ιe₁]
  · intro c _ hc
    rw [hcol c hc, mul_zero]
  · simp

theorem nuP_mul {g g' : hypSU h 2 1} (hg' : g' ∈ u5PtStab h) : nuP (g * g') = nuP g * nuP g' := by
  rw [nuP, nuP, nuP, mat_mul_e₁e₁ hg', map_mul]
  ring

theorem nuP_one : nuP (1 : hypSU h 2 1) = 1 := by
  simp [nuP, mat_one]

theorem nuP_commutator {a b : hypSU h 2 1} (ha : a ∈ u5PtStab h) (hb : b ∈ u5PtStab h) :
    nuP ⁅a, b⁆ = 1 := by
  have hai : a⁻¹ ∈ u5PtStab h := inv_mem ha
  have hbi : b⁻¹ ∈ u5PtStab h := inv_mem hb
  rw [commutatorElement_def, nuP_mul hbi, nuP_mul hai, nuP_mul hb]
  have h1 : nuP a * nuP a⁻¹ = 1 := by rw [← nuP_mul hai, mul_inv_cancel, nuP_one]
  have h2 : nuP b * nuP b⁻¹ = 1 := by rw [← nuP_mul hbi, mul_inv_cancel, nuP_one]
  calc nuP a * nuP b * nuP a⁻¹ * nuP b⁻¹ = (nuP a * nuP a⁻¹) * (nuP b * nuP b⁻¹) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

theorem mul_z₁SU_comm_of_nuP {g : hypSU h 2 1} (hg : g ∈ u5PtStab h) (hν : nuP g = 1) :
    g * z₁SU h = z₁SU h * g := by
  have e := conj_single_ptStab hg 1
  have h2 : g * z₁SU h * g⁻¹ = z₁SU h := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_z₁SU_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      ← mat_mul, mul_inv_cancel, mat_one, e, mul_one]
    exact congrArg (fun c => 1 + Matrix.single ιe₁ ιf₁ c) hν
  calc g * z₁SU h = (g * z₁SU h * g⁻¹) * g := by group
    _ = z₁SU h * g := by rw [h2]

theorem z5Y_mem_centerOf (hf : 2 ≤ f) : z5Y h ∈ centerOf (perfectCore (u5PtP h)) := by
  refine ⟨U_le_perfectCore_u5PtP hf z5Y_mem_U, ?_⟩
  show z5Y h ∈ Subgroup.centralizer ((perfectCore (u5PtP h) : Subgroup (hypPSU h 2 1)) :
    Set (hypPSU h 2 1))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ ⁅u5PtP h, u5PtP h⁆ := iInf_le (fun n => derivedSeriesOf (u5PtP h) n) 1 hy
  have hle : ⁅u5PtP h, u5PtP h⁆ ≤ Subgroup.centralizer ({z5Y h} : Set (hypPSU h 2 1)) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    have hcm : ⁅a₀, b₀⁆ ∈ u5PtStab h := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha₀ hb₀) (inv_mem ha₀)) (inv_mem hb₀)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_commutatorElement, z5Y, ← map_mul,
      ← map_mul]
    exact congrArg _ (mul_z₁SU_comm_of_nuP hcm (nuP_commutator ha₀ hb₀))
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy')

theorem ZP_trans_Y (hf : 2 ≤ f) {x : hypPSU h 2 1} (hx : x ∈ centerOf (perfectCore (u5PtP h)))
    (hx1 : x ≠ 1) : ∃ m ∈ u5PtP h, m * z5Y h * m⁻¹ = x :=
  trans_u5PtP hf (z5Y_mem_centerOf hf) hx z5Y_ne_one hx1

end Perfect

end CFSG.Quasithin.H13.F431.Un
