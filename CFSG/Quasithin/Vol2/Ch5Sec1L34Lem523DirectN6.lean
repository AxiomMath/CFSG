module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectN2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise
open CFSG.Quasithin.H13.Direct523Semi CFSG.Quasithin.H13.Direct523Count
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL)

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem conj_z_not_mem_Z₁ (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact)
    (hU : ¬ IsMulCommutative ↥(Ugrp Z₁ D₃)) {z d : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1)
    (hd : d ∈ D₃) (hd1 : d ≠ 1) : d * z * d⁻¹ ∉ Z₁ := by
  intro hmem
  obtain ⟨u, hu, v0, hv0, huv⟩ := exists_noncomm_V₂_U s h5114 hF hU
  have hv0Z : v0 ∈ Z₁ := by
    obtain ⟨u', hu', h | h⟩ := s.mem_V₂_iff hz hz1 hd hd1 h5114 hF hv0
    · rw [h]; exact hu'
    · rw [h]; exact mul_mem hu' hmem
  exact huv (Subgroup.mem_centralizer_iff.mp (s.U_le_G₁ hu) v0 hv0Z).symm

theorem exists_v (s : Setup521 G T M L V H B D D₃ Z₁ n) {N : Subgroup G}
    (D : NatL2Data L N 2) {z : G} (hzN : z ∈ N) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hNT : N ≤ T) {a₀ : D.K} (ha₀ : a₀ ≠ 0) (hwa : coordN D z hzN = a₀ • Direct523Semi.e₁)
    (hV2 : ∀ v ∈ conjClosure Z₁ D₃, ∃ hv : v ∈ N, ∃ μ : D.K, μ ^ 4 = μ ∧
      coordN D v hv = μ • coordN D z hzN)
    {c : D.K} (hc0 : c ≠ 0) {u₁ : G} (hu₁ : u₁ ∈ Ugrp Z₁ D₃)
    (hu₁N : u₁ ∈ Subgroup.normalizer (N : Set G)) (hρ : D.conj ⟨u₁, hu₁N⟩ = uB c)
    {z' : G} (hz'V2 : z' ∈ conjClosure Z₁ D₃) :
    ∃ v : G, ∃ hvN : v ∈ N, v ∈ T ∧ u₁ * v * u₁⁻¹ * v⁻¹ = z' := by
  obtain ⟨hz'N, μ, -, hcoord⟩ := hV2 z' hz'V2
  rw [hwa] at hcoord
  set t : D.K := μ * a₀ / c with ht
  set x : Fin 2 → D.K := ![0, t] with hx
  set v : G := ((D.E.symm (Multiplicative.ofAdd x) : ↥N) : G) with hv
  have hvN : v ∈ N := (D.E.symm (Multiplicative.ofAdd x)).2
  have hcoordv : coordN D v hvN = x := by
    unfold coordN
    simp [v]
  have hcommN : u₁ * v * u₁⁻¹ * v⁻¹ ∈ N :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hu₁N v).mp hvN) (inv_mem hvN)
  refine ⟨v, hvN, hNT hvN, ?_⟩
  apply coordN_injective D hcommN hz'N
  rw [coordN_comm D hu₁N hvN hcommN, hρ, hcoordv, hcoord]
  funext i
  fin_cases i
  · simp [uB_apply, x, e₁]
    rw [ht]
    field_simp
  · simp [uB_apply, x, e₁]

theorem comm_finset {N : Subgroup G} (D : NatL2Data L N 2) {U' : Subgroup G} {v : G}
    (hvN : v ∈ N) (hU' : ∀ u ∈ U', u ∈ Subgroup.normalizer (N : Set G))
    (B₁ B₂ B₃ B₄ : (Fin 2 → D.K) ≃+ (Fin 2 → D.K))
    (hcases : ∀ u ∈ U', ∀ hu : u ∈ Subgroup.normalizer (N : Set G),
      D.conj ⟨u, hu⟩ = B₁ ∨ D.conj ⟨u, hu⟩ = B₂ ∨ D.conj ⟨u, hu⟩ = B₃ ∨ D.conj ⟨u, hu⟩ = B₄) :
    ∃ F : Finset G, F.card ≤ 4 ∧ ∀ u ∈ U', ∀ hu : u ∈ Subgroup.normalizer (N : Set G),
      u * v * u⁻¹ * v⁻¹ ∈ F := by
  classical
  let inv : (Fin 2 → D.K) → G := fun p => ((D.E.symm (Multiplicative.ofAdd p) : ↥N) : G)
  have hinv : ∀ y (hy : y ∈ N), inv (coordN D y hy) = y := by
    intro y hy
    have h : (D.E.symm (Multiplicative.ofAdd (coordN D y hy)) : ↥N) = ⟨y, hy⟩ := by
      unfold coordN
      simp
    exact congrArg Subtype.val h
  let P : Finset (Fin 2 → D.K) :=
    {B₁ (coordN D v hvN) - coordN D v hvN, B₂ (coordN D v hvN) - coordN D v hvN,
      B₃ (coordN D v hvN) - coordN D v hvN, B₄ (coordN D v hvN) - coordN D v hvN}
  refine ⟨P.image inv, ?_, ?_⟩
  · refine (Finset.card_image_le).trans ?_
    exact Finset.card_le_four
  · intro u hu hun
    have hcommN : u * v * u⁻¹ * v⁻¹ ∈ N :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hun v).mp hvN) (inv_mem hvN)
    rw [← hinv _ hcommN, coordN_comm D hun hvN hcommN]
    apply Finset.mem_image_of_mem
    rcases hcases u hu hun with h | h | h | h <;> rw [h] <;> simp [P]

end CFSG.Quasithin.H13
