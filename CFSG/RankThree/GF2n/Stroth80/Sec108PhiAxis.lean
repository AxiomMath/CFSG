module

public import CFSG.RankThree.GF2n.Stroth80.Sec108PhiAlt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private abbrev crossAxis {K : Type} (M : Matrix (Fin 3) (Fin 3) K) : Fin 3 → K :=
  ![M 2 1, M 0 2, M 1 0]

private theorem crossAxis_crossMatrix {K : Type} [Field K] (a : Fin 3 → K) :
    crossAxis (CFSG.LinearAlgebra.crossMatrix a) = a := by
  ext i
  fin_cases i <;> simp [crossAxis, CFSG.LinearAlgebra.crossMatrix]

private theorem crossMatrix_injective {K : Type} [Field K] :
    Function.Injective (CFSG.LinearAlgebra.crossMatrix (K := K)) := by
  intro a b h
  have h' : crossAxis (CFSG.LinearAlgebra.crossMatrix a) =
      crossAxis (CFSG.LinearAlgebra.crossMatrix b) := by rw [h]
  rwa [crossAxis_crossMatrix, crossAxis_crossMatrix] at h'

private theorem phiMat_congr (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m m' : ↥(H0 M Z)} (h : (m : G) = (m' : G)) :
    D.phiMat AM m = D.phiMat AM m' := by
  rw [Subtype.ext h]

private def dotProductFunctional {K : Type} [Field K] (β : Fin 3 → K) :
    (Fin 3 → K) →ₗ[K] K :=
  (dotProductBilin K K).flip β

private theorem dotProductFunctional_apply {K : Type} [Field K] (β a : Fin 3 → K) :
    dotProductFunctional β a = a ⬝ᵥ β := rfl

private theorem finrank_ker_dotProductFunctional {K : Type} [Field K] {β : Fin 3 → K}
    (hβ : β ≠ 0) : Module.finrank K (LinearMap.ker (dotProductFunctional β)) = 2 := by
  have hf : dotProductFunctional β ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hβ
    have h1 := congrArg (fun g : (Fin 3 → K) →ₗ[K] K => g (Pi.single i 1)) h
    have h2 : dotProductFunctional β (Pi.single i 1) = β i := by
      rw [dotProductFunctional_apply, single_dotProduct, one_mul]
    rw [h2] at h1
    exact hi (by simpa using h1)
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (K := K) (V₁ := Fin 3 → K) hf
  have h3 : Module.finrank K (Fin 3 → K) = 3 := by simp
  omega

private theorem natCard_ker_dotProductFunctional {K : Type} [Field K] [Finite K]
    {β : Fin 3 → K} (hβ : β ≠ 0) :
    Nat.card ↥(LinearMap.ker (dotProductFunctional β)) = Nat.card K ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := K)
    (V := ↥(LinearMap.ker (dotProductFunctional β))), finrank_ker_dotProductFunctional hβ]

private theorem phiMat_eq_crossMatrix_crossAxis (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n : G} (hn : n ∈ hc.CN t) :
    D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ =
      CFSG.LinearAlgebra.crossMatrix (crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)) := by
  refine CFSG.LinearAlgebra.eq_crossMatrix ?_ ?_
  · rw [D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM hn he)
      (D.comm_t_of_mem_CN AM hn)]
    exact (CharTwo.neg_eq _).symm
  · exact fun i => D.phiMat_diag AM hn i

private theorem phiMat_eq_conj_mul_of_mem_LB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {l n : G} (hl : l ∈ LB M Q B)
    (hn : n ∈ hc.CN t) (hnB : n ∈ LB M Q B) :
    D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ =
      D.matV AM ⟨l, hc.LB_le_H0 hl⟩ * D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ *
        (D.matV AM ⟨l, hc.LB_le_H0 hl⟩)ᵀ := by
  have hlRt : l ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) D.good.1.mem_LB hl
  have hqQ : ⁅l, n⁆ ∈ Q := Subgroup.commutator_le.mp hc.commutator_LB_le_Q l hl n hnB
  have hqCN : ⁅l, n⁆ ∈ hc.CN t := by
    rw [D.CN_eq]
    exact Subgroup.mem_sup_left hqQ
  have hlnl : l * n * l⁻¹ ∈ hc.CN t := D.conj_mem_CN hlRt hn
  have hqdef : ⁅l, n⁆ * n = l * n * l⁻¹ := by
    rw [commutatorElement_def]
    group
  have hS_eq : D.phiMat AM ⟨l * n * l⁻¹, D.CN_le_H0 hlnl⟩ =
      D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ := by
    have hmul := D.phiMat_mul AM (m := ⟨⁅l, n⁆, D.CN_le_H0 hqCN⟩)
      (m' := ⟨n, D.CN_le_H0 hn⟩)
      (fun e he => D.fix_Vsp_of_mem_CN AM hqCN he)
      (fun e he => D.fix_Vsp_of_mem_CN AM hn he)
      (D.comm_t_of_mem_CN AM hn)
    have hqzero : D.phiMat AM ⟨⁅l, n⁆, D.CN_le_H0 hqCN⟩ = 0 :=
      (D.phiMat_eq_zero_iff_root AM hqCN).mpr ⟨1, Y.one_mem, by simpa using hqQ⟩
    rw [hqzero, zero_add] at hmul
    have hcongr : D.phiMat AM (⟨⁅l, n⁆, D.CN_le_H0 hqCN⟩ * ⟨n, D.CN_le_H0 hn⟩) =
        D.phiMat AM ⟨l * n * l⁻¹, D.CN_le_H0 hlnl⟩ :=
      phiMat_congr D AM hqdef
    rw [hcongr] at hmul
    exact hmul
  have hconj := D.phiMat_conj AM (m := ⟨n, D.CN_le_H0 hn⟩)
    (r := ⟨l, hc.LB_le_H0 hl⟩)
    (Sec108Data.phi_comm_of_comm_mem AM (D.comm_Rt_root_mem l hlRt t D.sit.mem))
    (fun j => D.phi_bV_eq_sum AM (m := ⟨l, hc.LB_le_H0 hl⟩)
      (fun e he => D.phi_mem_Vsp AM (m := ⟨l, hc.LB_le_H0 hl⟩) hlRt he) j)
    (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (D.comm_t_of_mem_CN AM hn)
  have hleft : D.phiMat AM (⟨l, hc.LB_le_H0 hl⟩ * ⟨n, D.CN_le_H0 hn⟩ *
      ⟨l, hc.LB_le_H0 hl⟩⁻¹) = D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ :=
    (phiMat_congr D AM (m := ⟨l, hc.LB_le_H0 hl⟩ * ⟨n, D.CN_le_H0 hn⟩ *
      ⟨l, hc.LB_le_H0 hl⟩⁻¹) (m' := ⟨l * n * l⁻¹, D.CN_le_H0 hlnl⟩) rfl).trans hS_eq
  rw [← hconj, hleft]

private theorem dotProduct_crossAxis_eq_zero_of_mem_LB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM)
    {n : G} (hn : n ∈ hc.CN t) (hnB : n ∈ LB M Q B) :
    crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) ⬝ᵥ β = 0 := by
  obtain ⟨μ, hμ0, hμβ⟩ := CFSG.LinearAlgebra.exists_ne_zero_dotProduct_eq_zero β
  obtain ⟨l, hl, hmat⟩ := D.exists_LB_matV AM hβ hβB hμβ
  have hkey := phiMat_eq_conj_mul_of_mem_LB D AM hl hn hnB
  rw [hmat, phiMat_eq_crossMatrix_crossAxis D AM hn] at hkey
  rw [CFSG.LinearAlgebra.one_add_vecMulVec_mul_crossMatrix, hμβ, zero_smul, add_zero] at hkey
  have hsubeq : crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) -
      (β ⬝ᵥ crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)) • μ =
      crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) :=
    (crossMatrix_injective hkey).symm
  have hzero : (β ⬝ᵥ crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)) • μ = 0 := by
    have h' : crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) -
        (β ⬝ᵥ crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)) • μ =
        crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) - 0 := by
      rw [sub_zero]
      exact hsubeq
    have h'' : crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) +
        -((β ⬝ᵥ crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)) • μ) =
        crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) + 0 := by
      simpa [sub_eq_add_neg] using h'
    exact neg_eq_zero.mp (add_left_cancel h'')
  rcases smul_eq_zero.mp hzero with h | h
  · exact (dotProduct_comm _ _).trans h
  · exact absurd h hμ0

private def phiHomLBSet (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : Set (Matrix (Fin 3) (Fin 3) AM.K) :=
  {X | Multiplicative.ofAdd X ∈ ((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)}

private theorem mem_phiHomLBSet (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {X : Matrix (Fin 3) (Fin 3) AM.K} :
    X ∈ phiHomLBSet D AM ↔
      Multiplicative.ofAdd X ∈ ((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM) :=
  Iff.rfl

private def axisSet {K : Type} [Field K] (β : Fin 3 → K) : Set (Matrix (Fin 3) (Fin 3) K) :=
  {X | ∃ a, a ⬝ᵥ β = 0 ∧ X = CFSG.LinearAlgebra.crossMatrix a}

private theorem mem_axisSet {K : Type} [Field K] {β : Fin 3 → K} {X : Matrix (Fin 3) (Fin 3) K} :
    X ∈ axisSet β ↔ ∃ a, a ⬝ᵥ β = 0 ∧ X = CFSG.LinearAlgebra.crossMatrix a :=
  Iff.rfl

private theorem phiHomLBSet_subset_axisSet (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM) :
    phiHomLBSet D AM ⊆ axisSet β := by
  intro X hX
  rw [mem_phiHomLBSet] at hX
  obtain ⟨x, hx, hxX⟩ := Subgroup.mem_map.mp hX
  have hxLB : (x : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hx
  have hXphi : X = D.phiMat AM ⟨x.1, D.CN_le_H0 x.2⟩ := by
    have h := congrArg Multiplicative.toAdd hxX
    simpa [D.phiHom_apply AM x] using h.symm
  rw [mem_axisSet]
  refine ⟨crossAxis X, ?_, ?_⟩
  · rw [hXphi]
    exact dotProduct_crossAxis_eq_zero_of_mem_LB D AM hβ hβB x.2 hxLB
  · rw [hXphi]
    exact phiMat_eq_crossMatrix_crossAxis D AM x.2

private theorem card_phiHomLBSet (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Nat.card (phiHomLBSet D AM) = Nat.card Z ^ 2 := by
  let e : ↥(phiHomLBSet D AM) ≃
      ↥(((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)) :=
    { toFun := fun M => (⟨Multiplicative.ofAdd M.1, M.2⟩ : _)
      invFun := fun x => (⟨Multiplicative.toAdd x.1, x.2⟩ : _)
      left_inv := fun M => by ext; simp
      right_inv := fun x => by ext; simp }
  rw [Nat.card_congr e, D.card_map_phiHom_LB AM]

private theorem card_axisSet (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K}
    (hβ : β ≠ 0) :
    Nat.card (axisSet β) = Nat.card Z ^ 2 := by
  have hker : Nat.card ↥(LinearMap.ker (dotProductFunctional β)) = Nat.card Z ^ 2 := by
    rw [natCard_ker_dotProductFunctional hβ, AM.glob.card]
  have hle : Nat.card (axisSet β) ≤ Nat.card ↥(LinearMap.ker (dotProductFunctional β)) := by
    refine Nat.card_le_card_of_injective
      (fun M : ↥(axisSet β) => (⟨crossAxis M.1, ?_⟩ : ↥(LinearMap.ker (dotProductFunctional β))))
      ?_
    · rw [LinearMap.mem_ker]
      obtain ⟨b, hb, hMb⟩ := mem_axisSet.mp M.2
      have hax : crossAxis M.1 = b := by
        rw [hMb]
        exact crossAxis_crossMatrix b
      rw [hax]
      exact hb
    · intro M M' h
      have hax : crossAxis M.1 = crossAxis M'.1 := by
        simpa using congrArg Subtype.val h
      obtain ⟨b, -, hMb⟩ := mem_axisSet.mp M.2
      obtain ⟨b', -, hMb'⟩ := mem_axisSet.mp M'.2
      have hbb' : b = b' := by
        rw [hMb, hMb'] at hax
        simpa [crossAxis_crossMatrix] using hax
      apply Subtype.ext
      rw [hMb, hMb', hbb']
  have hle' : Nat.card ↥(LinearMap.ker (dotProductFunctional β)) ≤ Nat.card (axisSet β) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(LinearMap.ker (dotProductFunctional β)) =>
        (⟨CFSG.LinearAlgebra.crossMatrix x.1, ?_⟩ : ↥(axisSet β))) ?_
    · rw [mem_axisSet]
      refine ⟨x.1, ?_, rfl⟩
      have hx := x.2
      rw [LinearMap.mem_ker, dotProductFunctional_apply] at hx
      exact hx
    · intro x x' h
      exact Subtype.ext (crossMatrix_injective (congrArg Subtype.val h))
  rw [← hker]
  exact le_antisymm hle hle'

private theorem phiHomLBSet_eq_axisSet (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM) :
    phiHomLBSet D AM = axisSet β :=
  Set.eq_of_subset_of_ncard_le (phiHomLBSet_subset_axisSet D AM hβ hβB)
    (by
      change Nat.card (axisSet β) ≤ Nat.card (phiHomLBSet D AM)
      rw [card_axisSet AM hβ, card_phiHomLBSet D AM])

private theorem ofAdd_crossMatrix_mem_map_phiHom (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM) {a : Fin 3 → AM.K}
    (ha : a ⬝ᵥ β = 0) :
    Multiplicative.ofAdd (CFSG.LinearAlgebra.crossMatrix a) ∈
      ((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM) := by
  have hEq := phiHomLBSet_eq_axisSet D AM hβ hβB
  have hmem : CFSG.LinearAlgebra.crossMatrix a ∈ axisSet β := mem_axisSet.mpr ⟨a, ha, rfl⟩
  rw [← hEq] at hmem
  exact mem_phiHomLBSet D AM |>.mp hmem

private theorem mem_LB_of_dotProduct_crossAxis_eq_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM) {n : G} (hn : n ∈ hc.CN t)
    (ha : crossAxis (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) ⬝ᵥ β = 0) :
    n ∈ LB M Q B := by
  have hmem := ofAdd_crossMatrix_mem_map_phiHom D AM hβ hβB ha
  rw [← phiMat_eq_crossMatrix_crossAxis D AM hn] at hmem
  obtain ⟨x, hx, hxM⟩ := Subgroup.mem_map.mp hmem
  have hxLB : (x : G) ∈ LB M Q B := hx
  have hxn : D.phiHom AM (⟨n, hn⟩ : ↥(hc.CN t)) =
      Multiplicative.ofAdd (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) := by
    apply Multiplicative.toAdd.injective
    rw [D.phiHom_apply AM ⟨n, hn⟩]
    exact phiMat_congr D AM rfl
  set xn : ↥(hc.CN t) := x⁻¹ * ⟨n, hn⟩ with hxn_def
  have hzero : D.phiMat AM ⟨(xn : G), D.CN_le_H0 xn.2⟩ = 0 := by
    have hphi : D.phiHom AM xn = 1 := by
      rw [hxn_def, map_mul, map_inv, hxM, hxn]
      group
    have h := D.phiHom_apply AM xn
    rw [hphi] at h
    simpa using h.symm
  obtain ⟨y, hy, hyq⟩ := (D.phiMat_eq_zero_iff_root AM xn.2).mp hzero
  have hxval : (xn : G) = x.1⁻¹ * n := by
    rw [hxn_def]
    rfl
  have hmemLB : x.1⁻¹ * n ∈ LB M Q B := by
    have h1 : y⁻¹ * (x.1⁻¹ * n) ∈ LB M Q B := by
      rw [← hxval]
      exact sec39_Q_le_LB hyq
    have e : x.1⁻¹ * n = y * (y⁻¹ * (x.1⁻¹ * n)) := by group
    rw [e]
    exact (LB M Q B).mul_mem (D.root_le_LB hy) h1
  have e2 : n = x.1 * (x.1⁻¹ * n) := by group
  rw [e2]
  exact (LB M Q B).mul_mem hxLB hmemLB

theorem Sec108Data.mem_LB_iff_dotProduct (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM) {n : G} (hn : n ∈ hc.CN t) :
    n ∈ LB M Q B ↔ ![D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 2 1, D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 0 2,
      D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 1 0] ⬝ᵥ β = 0 := by
  constructor
  · intro hnB
    exact dotProduct_crossAxis_eq_zero_of_mem_LB D AM hβ hβB hn hnB
  · intro ha
    exact mem_LB_of_dotProduct_crossAxis_eq_zero D AM hβ hβB hn ha

end CFSG.RankThree.GF2n.Stroth80
