module

public import CFSG.RankThree.PartTwo.CTU6.Model
public import CFSG.LieType.CurtisTits.Unitary
public import CFSG.RankThree.PartOne.CTP.SpinMinusEven

public section

namespace CFSG.RankThree.PartTwo.CTU6

open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.RankThree.PartOne.CTP CFSG.LieType.BorelTits
  CFSG.Timmesfeld CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (fixedSubfield card_fixedSubfield)
open CFSG.ClassicalInvolution.WeakCT (NodeData LinearBlockStandardPair blk edgeUp
  rootedTree_edgeUp_last exists_frame_of_tree_short exists_levi_node exists_levi_of_model
  exists_levi_orth weakCT_of_twisted_nodes commute_of_tv₂ tv_zero_one_one_ne_one)
open scoped MatrixGroups

section Commute

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem rootMatrix_mul_longRootMatrix_comm {i j k : Fin n} (c d : F) (h1 : j ≠ k)
    (h2 : Fin.rev k ≠ i) (h3 : Fin.rev i ≠ k) (h4 : Fin.rev k ≠ Fin.rev j) :
    rootMatrix σ i j c * longRootMatrix k d = longRootMatrix k d * rootMatrix σ i j c := by
  have e1 : single i j c * single k (Fin.rev k) d = 0 := by simp [h1]
  have e2 : single k (Fin.rev k) d * single i j c = 0 := by simp [h2]
  have e3 : single (Fin.rev j) (Fin.rev i) (σ c) * single k (Fin.rev k) d = 0 := by simp [h3]
  have e4 : single k (Fin.rev k) d * single (Fin.rev j) (Fin.rev i) (σ c) = 0 := by simp [h4]
  simp only [rootMatrix, longRootMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2, e3, e4]
  abel

theorem commute_of_mat_comm {x y : SU σ n}
    (h : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((y : GL (Fin n) F) : Matrix _ _ F) =
      ((y : GL (Fin n) F) : Matrix _ _ F) * ((x : GL (Fin n) F) : Matrix _ _ F)) :
    Commute x y :=
  Subtype.ext (Units.ext h)

end Commute

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)

theorem commute_rS0_rL (a : SL(2, K)) (b : SL(2, fixedSubfield K 2 f)) :
    Commute (rS0 _ (unitaryInvolution_involutive hK) a) (rL K f b) := by
  refine commute_of_tv₂ _ _ (fun c d => ⟨?_, ?_, ?_, ?_⟩) a b
  · rw [rS0_tv01, rL_tv01]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS0_tv01, rL_tv10]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS0_tv10, rL_tv01]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS0_tv10, rL_tv10]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)

theorem weakCT_unitary_six_even (hf : 2 ≤ f) {X : Type} [Group X] (U : Fin 3 → Subgroup X)
    (hgen : ⨆ k, U k = ⊤) (hcomm : ∀ u ∈ U 0, ∀ v ∈ U 2, u * v = v * u)
    (hpair : ∃ W, LinearBlockStandardPair K W (U 0) (U 1))
    (htw : ∃ W, (su4Model hK).StandardPair W (U 2) (U 1)) :
    ∃ Ψ : SU (unitaryInvolution K 2 f) 6 →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (SU (unitaryInvolution K 2 f) 6)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSU 6 2 f ∧
      ∀ k, (CurtisTits.rankOne (rootDatum hK 6).rootGroup k).map Ψ = U k := by
  classical
  have hσ := unitaryInvolution_involutive hK
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; nlinarith
  obtain ⟨W, θ₁, -, -, hl, hs, hU2, hU1⟩ := htw
  let P := su4Model hK
  have hμ : ∃ s, P.mu s ≠ 1 := exists_su4Mu_ne hK hf
  have hlU : (θ₁.comp P.lb).range = U 2 := by rw [MonoidHom.range_comp]; exact hU2
  let US : Fin 2 → Subgroup X := fun i => U ⟨i.val, by omega⟩
  have hcommS : ∀ i j : Fin 2, i ≠ j → ¬ edgeUp 2 i j → ¬ edgeUp 2 j i →
      ∀ u ∈ US i, ∀ v ∈ US j, u * v = v * u := by
    intro i j hne h1 h2
    exfalso
    have h3 : i.val ≠ j.val := fun h => hne (Fin.ext h)
    simp only [edgeUp] at h1 h2
    have := i.2
    have := j.2
    omega
  have hpairS : ∀ i j : Fin 2, edgeUp 2 i j →
      ∃ W, LinearBlockStandardPair K W (US i) (US j) := by
    intro i j hij
    simp only [edgeUp] at hij
    have hi : i = 0 := Fin.ext (by have := j.2; simp only [Fin.val_zero]; omega)
    have hj : j = 1 := Fin.ext (by have := j.2; simp only [Fin.val_one]; omega)
    subst hi hj
    exact hpair
  have hsU : (θ₁.comp P.sb).range = US ⟨2 - 1, by omega⟩ := by
    rw [MonoidHom.range_comp]
    exact hU1
  have hVS : ∀ q : Fin 2, (edgeUp 2 ⟨2 - 1, by omega⟩ q ∨ edgeUp 2 q ⟨2 - 1, by omega⟩) →
      ∀ x ∈ (θ₁.comp P.lb).range, ∀ y ∈ US q, x * y = y * x := by
    intro q hq x hx y hy
    have hq0 : q = 0 := Fin.ext (by
      have := q.2
      simp only [edgeUp] at hq
      simp only [Fin.val_zero]
      omega)
    subst hq0
    rw [hlU] at hx
    exact (hcomm y hy x hx).symm
  obtain ⟨ρS, hρS₁, hρSU, hρSψ⟩ := exists_frame_of_tree_short P hμ hK4
    (rootedTree_edgeUp_last (m := 2) (by norm_num)) ⟨0, Or.inr rfl⟩ hcommS hpairS hs hsU hVS
  let D := rootDatum hK 6
  have up0 : ∀ c, rS0 _ hσ (CFSG.Timmesfeld.tv 0 1 c) ∈ D.rootGroup (Pi.single k0 1) :=
    fun c => by rw [rS0_tv01]; exact short_upper_mem hσ (k := k0) (by decide) c
  have lo0 : ∀ c, rS0 _ hσ (CFSG.Timmesfeld.tv 1 0 c) ∈ D.rootGroup (-Pi.single k0 1) :=
    fun c => by rw [rS0_tv10]; exact short_lower_mem hσ (k := k0) (by decide) c
  have pu0 := short_param_upper hσ (k := k0) (by decide) (rS0 _ hσ) (rS0_tv01 hσ)
  have pl0 := short_param_lower hσ (k := k0) (by decide) (rS0 _ hσ) (rS0_tv10 hσ)
  have up1 : ∀ c, rS1 _ hσ (CFSG.Timmesfeld.tv 0 1 c) ∈ D.rootGroup (Pi.single k1 1) :=
    fun c => by rw [rS1_tv01]; exact short_upper_mem hσ (k := k1) (by decide) c
  have lo1 : ∀ c, rS1 _ hσ (CFSG.Timmesfeld.tv 1 0 c) ∈ D.rootGroup (-Pi.single k1 1) :=
    fun c => by rw [rS1_tv10]; exact short_lower_mem hσ (k := k1) (by decide) c
  have pu1 := short_param_upper hσ (k := k1) (by decide) (rS1 _ hσ) (rS1_tv01 hσ)
  have pl1 := short_param_lower hσ (k := k1) (by decide) (rS1 _ hσ) (rS1_tv10 hσ)
  let nd : ∀ k : Fin D.rank, NodeData D X k (U k) := fun k =>
    match k with
    | ⟨0, _⟩ => NodeData.ofParam (rS0 _ hσ) (ρS 0) (hρSU 0).2 (rS0_injective hσ) up0 lo0 pu0 pl0
    | ⟨1, _⟩ => NodeData.ofParam (rS1 _ hσ) (ρS 1) (hρSU 1).2 (rS1_injective hσ) up1 lo1 pu1 pl1
    | ⟨2, _⟩ => NodeData.ofParam (rL K f) (θ₁.comp P.lb) hlU rL_injective (rL_upper_mem hK)
        (rL_lower_mem hK) (rL_param_upper hK) (rL_param_lower hK)
    | ⟨n + 3, h⟩ => absurd h (by change ¬ n + 3 < 3; omega)
  have P0 : (nd k0).IsParam (rS0 _ hσ) (ρS 0) :=
    NodeData.ofParam_isParam (hρSU 0).2 (rS0_injective hσ) up0 lo0 pu0 pl0
  have P1 : (nd k1).IsParam (rS1 _ hσ) (ρS 1) :=
    NodeData.ofParam_isParam (hρSU 1).2 (rS1_injective hσ) up1 lo1 pu1 pl1
  have P2 : (nd k2).IsParam (rL K f) (θ₁.comp P.lb) :=
    NodeData.ofParam_isParam hlU rL_injective (rL_upper_mem hK) (rL_lower_mem hK)
      (rL_param_upper hK) (rL_param_lower hK)
  have hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1 := by
    refine ⟨k0, ⟨rS0 _ hσ (CFSG.Timmesfeld.tv 0 1 1), up0 1⟩, ?_⟩
    rw [P0.ψp_eq 1]
    intro h
    exact tv_zero_one_one_ne_one ((hρSU 0).1 (h.trans (map_one _).symm))
  have hadm : StatedLieAdmissible .PSU 6 2 f :=
    ⟨Nat.prime_two, by omega, by norm_num, fun h => by
      have := congrArg Prod.fst h
      simp at this⟩
  have hCT : CurtisTits.CurtisTitsConclusion.{0} D .PSU 6 2 f :=
    CurtisTits.curtisTitsConclusion_unitary hadm hK
  have hL := leviConePresented_unitary hK (n := 6) (by norm_num)
  have hdiv : D.divisible = ∅ := by
    change Unitary.divisible 6 = ∅
    simp only [Unitary.divisible, show Even 6 from ⟨3, rfl⟩, ↓reduceIte]
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hK
  have hCTG := isCTGroupDatum hK 6 (by norm_num) ζ hζ
  have hZ : ∀ (a : SL(2, K)) (b : SL(2, fixedSubfield K 2 f)), a ∈ Subgroup.center SL(2, K) →
      b ∈ Subgroup.center SL(2, fixedSubfield K 2 f) → rS0 _ hσ a = rL K f b →
        rS0 _ hσ a = 1 := by
    intro a b ha _ _
    rw [center_sl2_eq_bot_of_two_eq_zero (CharTwo.two_eq_zero (R := K)), Subgroup.mem_bot] at ha
    rw [ha, map_one]
  have m0 : ∀ a, ρS 0 a ∈ U 0 := fun a => by
    have h : ρS 0 a ∈ (ρS 0).range := ⟨a, rfl⟩
    rw [(hρSU 0).2] at h
    exact h
  have hloc : ∀ i j : Fin D.rank, i ≤ j →
      ∃ (E : LeviEmbedding D i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : D.rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hij; simp [Fin.le_def]; done) | skip
    · exact exists_levi_node hdiv hCTG nd P0 (rS0_injective hσ)
    ·
      obtain ⟨ψ, hψ0, hψ1⟩ := hρSψ 0 1 rfl
      exact exists_levi_of_model hdiv hCTG nd P0 P1 (embSL3 _ hσ) (embSL3_injective _ hσ)
        (blk K 0) (blk K 1) rfl rfl ψ hψ0 hψ1
    ·
      exact exists_levi_orth hdiv hCTG nd P0 P2 (rS0_injective hσ) rL_injective
        (commute_rS0_rL hK) hZ (fun a b => hcomm _ (m0 a) _ (hlU ▸ ⟨b, rfl⟩))
    · exact exists_levi_node hdiv hCTG nd P1 (rS1_injective hσ)
    ·
      exact exists_levi_of_model hdiv hCTG nd P1 P2 (embSU4 _) (embSU4_injective _)
        (sbEmb _ hσ) (lbSU4 K f) (embSU4_comp_sbEmb _ hσ) rfl θ₁ hρS₁.symm rfl
    · exact exists_levi_node hdiv hCTG nd P2 rL_injective
  exact weakCT_of_twisted_nodes hCT hL hdiv hgen nd hnt hloc

end CFSG.RankThree.PartTwo.CTU6
