module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EDer
public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofBar
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def innCent (L U : Subgroup G) : Subgroup (MulAut (lBar L)) :=
  (MulAut.conj : lBar L →* MulAut (lBar L)).range ⊓
    Subgroup.centralizer (barImage L U : Set (MulAut (lBar L)))

theorem conj_mul_mem_range_conj {X : Type*} [Group X] (σ τ : MulAut X)
    (hτ : τ ∈ (MulAut.conj : X →* MulAut X).range) :
    σ * τ * σ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨x, rfl⟩ := hτ
  refine ⟨σ x, ?_⟩
  ext z
  simp [MulAut.mul_apply, map_mul, map_inv, MulAut.conj_apply]

theorem false_of_comm_eq_bot {A E U L : Subgroup G} {c : G}
    (hPF : Item211LieProof.PairFacts A E U c L) (hUE : ⁅U, E⁆ = ⊥)
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L)
    (hZ : Subgroup.center (lBar L) = ⊥)
    (hED : barImage L E ≤ ⁅innCent L U, innCent L U⁆)
    (hO2 : ∀ P : Subgroup (MulAut (lBar L)), IsPGroup 2 P → P ≤ ⁅innCent L U, innCent L U⁆ →
      ⁅innCent L U, innCent L U⁆ ≤ Subgroup.normalizer (P : Set (MulAut (lBar L))) → P = ⊥) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := Item211LieProof.vFacts hPF
  set C' := Subgroup.centralizer ((U : Set G) ∪ {c}) with hC'
  set O := inSubgroup (CFSG.pCore 2) C' with hO
  set D := ⁅innCent L U, innCent L U⁆ with hD
  set Y := barImage L O with hY
  have hEU : E ≤ Subgroup.centralizer (U : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : ⁅u, e⁆ ∈ ⁅U, E⁆ := Subgroup.commutator_mem_commutator hu he
    rw [hUE, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hB : E ⊓ Subgroup.centralizer (U : Set G) = E := inf_eq_left.mpr hEU
  have hY2 : IsPGroup 2 Y := isPGroup_barImage ((CFSG.pCore_isPGroup).map C'.subtype)
  have hOU : ∀ o ∈ O, ∀ u ∈ U, o * u = u * o := by
    intro o ho u hu
    have hoC : o ∈ C' := (Subgroup.map_subtype_le _) ho
    exact ((Subgroup.mem_centralizer_iff.mp hoC) u (Or.inl hu)).symm
  have hYU : ∀ y ∈ Y, ∀ a ∈ barImage L U, y * a = a * y := barImage_commute hOU
  have hLC := hPF.L_le_centralizer
  have hCLU : L ⊓ Subgroup.centralizer (U : Set G) ≤ C' := by
    intro x hx
    rw [hC', Subgroup.mem_centralizer_iff]
    rintro y (hy | hy)
    · exact (Subgroup.mem_centralizer_iff.mp hx.2) y hy
    · rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp (hLC hx.1)) c rfl
  have hNO : ∀ x ∈ L ⊓ Subgroup.centralizer (U : Set G), ∀ o ∈ O, x * o * x⁻¹ ∈ O :=
    fun x hx o ho => (Subgroup.mem_normalizer_iff.mp
      (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 C' (hCLU hx))
        o).mp ho
  have hDY : D ≤ Subgroup.normalizer (Y : Set (MulAut (lBar L))) :=
    (derived_centralizer_le_barImage hθc hZ hPF.UN).trans
      (Item211LieProof.barImage_E_le_normalizer hNO)
  have hYinn : ∀ y ∈ Y, ∀ τ ∈ innCent L U, y * τ * y⁻¹ ∈ innCent L U := by
    intro y hy τ hτ
    obtain ⟨hτR, hτC⟩ := Subgroup.mem_inf.mp hτ
    refine Subgroup.mem_inf.mpr ⟨conj_mul_mem_range_conj y τ hτR, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := hYU y hy a ha
    have h2 := (Subgroup.mem_centralizer_iff.mp hτC) a ha
    have h3 : a * y⁻¹ = y⁻¹ * a := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h1, inv_mul_cancel_left]
    calc a * (y * τ * y⁻¹) = (a * y) * τ * y⁻¹ := by group
      _ = (y * a) * τ * y⁻¹ := by rw [h1]
      _ = y * (a * τ) * y⁻¹ := by group
      _ = y * (τ * a) * y⁻¹ := by rw [h2]
      _ = y * τ * (a * y⁻¹) := by group
      _ = y * τ * (y⁻¹ * a) := by rw [h3]
      _ = y * τ * y⁻¹ * a := by group
  have hconjD : ∀ y ∈ Y, ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro y hy d hd
    have hmap : (innCent L U).map (MulAut.conj y).toMonoidHom ≤ innCent L U := by
      rintro _ ⟨τ, hτ, rfl⟩
      exact hYinn y hy τ hτ
    have h1 : D.map (MulAut.conj y).toMonoidHom ≤ D := by
      rw [hD, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact h1 ⟨d, hd, rfl⟩
  have hYD : Y ≤ Subgroup.normalizer (D : Set (MulAut (lBar L))) := fun y hy =>
    Subgroup.mem_normalizer_fintype (hconjD y hy)
  set P := ⁅Y, D⁆ with hP
  have hPY : P ≤ Y := by
    rw [hP, Subgroup.commutator_le]
    intro y hy d hd
    rw [commutatorElement_def]
    have h1 : d * y⁻¹ * d⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hDY hd) y⁻¹).mp (Y.inv_mem hy)
    have e1 : y * d * y⁻¹ * d⁻¹ = y * (d * y⁻¹ * d⁻¹) := by group
    rw [e1]
    exact Y.mul_mem hy h1
  have hPD : P ≤ D := by
    rw [hP, Subgroup.commutator_le]
    intro y hy d hd
    rw [commutatorElement_def]
    exact D.mul_mem (hconjD y hy d hd) (D.inv_mem hd)
  have hPbot : P = ⊥ :=
    hO2 P (hY2.to_le hPY) hPD (Subgroup.normalizer_commutator_ge_right Y D)
  have hVY : barImage L (lThreeV E U c) ≤ Y := Subgroup.map_mono fun _ hx =>
    Subgroup.mem_subgroupOf.mpr (hV.le_X0 (Subgroup.mem_subgroupOf.mp hx))
  have hcomm : ⁅barImage L (lThreeV E U c), barImage L E⁆ = ⊥ := by
    have h1 : ⁅barImage L (lThreeV E U c), barImage L E⁆ ≤ P :=
      Subgroup.commutator_mono hVY hED
    rw [hPbot] at h1
    exact le_bot_iff.mp h1
  have hVB := Item211LieProof.barImage_V_comm_B hPF
  rw [hB, hcomm] at hVB
  exact Item211LieProof.barImage_V_ne_bot hPF hVB.symm

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
