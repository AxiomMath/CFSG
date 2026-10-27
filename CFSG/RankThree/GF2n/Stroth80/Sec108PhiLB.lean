module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Phi

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

theorem Sec108Data.exists_coord_Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ∃ β : Fin 3 → AM.K, β ≠ 0 ∧ ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM := by
  have hne : D.Bsp AM ≠ ⊥ := by
    intro h
    have hfin := D.finrank_Bsp AM
    rw [h, finrank_bot] at hfin
    exact zero_ne_one hfin
  obtain ⟨b, hbB, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hbV : b ∈ AM.Vsp hc t := D.Bsp_le_Vsp AM hbB
  let β : Fin 3 → AM.K := (D.bV AM).repr ⟨b, hbV⟩
  have hsum : ∑ i, β i • (D.bV AM i : AM.M₀.E) = b := by
    have h := (D.bV AM).sum_repr ⟨b, hbV⟩
    have h' : ((∑ i, (D.bV AM).repr ⟨b, hbV⟩ i • D.bV AM i : ↥(AM.Vsp hc t)) :
        AM.M₀.E) = b := by
      rw [h]
    simpa only [β, Submodule.coe_sum, Submodule.coe_smul, Subtype.coe_mk] using h'
  refine ⟨β, ?_, ?_⟩
  · intro hβ
    apply hb0
    rw [← hsum, hβ]
    simp
  · rw [hsum]
    exact hbB

private theorem bV_sum_ne_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0) :
    ∑ i, β i • (D.bV AM i : AM.M₀.E) ≠ 0 := by
  intro h
  apply hβ
  have hzero : (∑ i, β i • D.bV AM i : ↥(AM.Vsp hc t)) = 0 := by
    apply Subtype.ext
    simpa using h
  have hβ0 := (Fintype.linearIndependent_iffₛ.mp (D.bV AM).linearIndependent) β 0
    (by simpa using hzero)
  refine funext fun i => ?_
  simpa using hβ0 i

private theorem Bsp_exists_smul (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {c : AM.M₀.E} (hcB : c ∈ D.Bsp AM)
    (hc0 : c ≠ 0) {w : AM.M₀.E} (hw : w ∈ D.Bsp AM) :
    ∃ s : AM.K, w = s • c := by
  obtain ⟨b, -, -, hB, -, -⟩ := Ctx.dictB hc AM.glob
  obtain ⟨s, hs⟩ := (hB c).mp ((D.mem_Bsp AM).mp hcB)
  obtain ⟨t', ht'⟩ := (hB w).mp ((D.mem_Bsp AM).mp hw)
  have hs0 : s ≠ 0 := by
    intro h
    exact hc0 (by rw [hs, h, zero_smul])
  refine ⟨t' * s⁻¹, ?_⟩
  rw [ht', hs, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

private theorem sum_one_add_vecMulVec_eq (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (β μ : Fin 3 → AM.K) (j : Fin 3) :
    ∑ i, (1 + Matrix.vecMulVec β μ) i j • (D.bV AM i : AM.M₀.E) =
      D.bV AM j + μ j • ∑ i, β i • (D.bV AM i : AM.M₀.E) := by
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, add_smul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp [Matrix.one_apply]
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [smul_smul, mul_comm]

private theorem matV_eq_one_add_vecMulVec (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {x : G} (hx : x ∈ LB M Q B)
    {β μ : Fin 3 → AM.K}
    (hδ : ∀ j, ((D.delta AM ⟨x, hx⟩
        ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩ : ↥(D.Bsp AM)) : AM.M₀.E) =
      μ j • ∑ i, β i • (D.bV AM i : AM.M₀.E)) :
    D.matV AM ⟨x, hc.LB_le_H0 hx⟩ = 1 + Matrix.vecMulVec β μ := by
  refine D.matV_eq_of_forall AM fun j => ?_
  rw [sum_one_add_vecMulVec_eq D AM β μ j]
  have h := D.delta_apply AM ⟨x, hx⟩
    ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩
  have h1 : AM.φ ⟨x, hc.LB_le_H0 hx⟩ (D.bV AM j) - D.bV AM j =
      μ j • ∑ i, β i • (D.bV AM i : AM.M₀.E) := h.symm.trans (hδ j)
  calc AM.φ ⟨x, hc.LB_le_H0 hx⟩ (D.bV AM j) =
      (AM.φ ⟨x, hc.LB_le_H0 hx⟩ (D.bV AM j) - D.bV AM j) + D.bV AM j := by
        rw [sub_add_cancel]
    _ = μ j • ∑ i, β i • (D.bV AM i : AM.M₀.E) + D.bV AM j := by rw [h1]
    _ = D.bV AM j + μ j • ∑ i, β i • (D.bV AM i : AM.M₀.E) := add_comm _ _

private theorem dotProduct_eq_zero_of_delta (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {x : G} (hx : x ∈ LB M Q B)
    {β μ : Fin 3 → AM.K} {c : AM.M₀.E}
    (hc : c = ∑ i, β i • (D.bV AM i : AM.M₀.E))
    (hcB : c ∈ D.Bsp AM) (hc0 : c ≠ 0)
    (hδ : ∀ j, ((D.delta AM ⟨x, hx⟩
        ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩ : ↥(D.Bsp AM)) : AM.M₀.E) = μ j • c) :
    μ ⬝ᵥ β = 0 := by
  have hcAsp : c ∈ D.Asp AM := D.Vsp_le_Asp AM (D.Bsp_le_Vsp AM hcB)
  have hdel : ((D.delta AM ⟨x, hx⟩ ⟨c, hcAsp⟩ : ↥(D.Bsp AM)) : AM.M₀.E) = 0 := by
    rw [D.delta_Bsp AM ⟨x, hx⟩ ⟨c, hcAsp⟩ hcB]
    rfl
  have hcEq : (⟨c, hcAsp⟩ : ↥(D.Asp AM)) =
      ∑ i, β i • (⟨D.bV AM i, D.Vsp_le_Asp AM (D.bV AM i).2⟩ : ↥(D.Asp AM)) := by
    apply Subtype.ext
    exact hc
  have hsum : ((D.delta AM ⟨x, hx⟩ ⟨c, hcAsp⟩ : ↥(D.Bsp AM)) : AM.M₀.E) =
      (∑ i, β i * μ i) • c := by
    have h1 : D.delta AM ⟨x, hx⟩ ⟨c, hcAsp⟩ =
        ∑ i, β i • D.delta AM ⟨x, hx⟩
          ⟨D.bV AM i, D.Vsp_le_Asp AM (D.bV AM i).2⟩ := by
      rw [hcEq, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        change D.delta AM ⟨x, hx⟩
            (β i • (⟨D.bV AM i, D.Vsp_le_Asp AM (D.bV AM i).2⟩ : ↥(D.Asp AM))) =
          β i • D.delta AM ⟨x, hx⟩
            ⟨D.bV AM i, D.Vsp_le_Asp AM (D.bV AM i).2⟩
        rw [map_smul]
    calc ((D.delta AM ⟨x, hx⟩ ⟨c, hcAsp⟩ : ↥(D.Bsp AM)) : AM.M₀.E)
        = ((∑ i, β i • D.delta AM ⟨x, hx⟩
            ⟨D.bV AM i, D.Vsp_le_Asp AM (D.bV AM i).2⟩ : ↥(D.Bsp AM)) : AM.M₀.E) := by
          rw [h1]
      _ = ∑ i, β i • ((D.delta AM ⟨x, hx⟩
            ⟨D.bV AM i, D.Vsp_le_Asp AM (D.bV AM i).2⟩ : ↥(D.Bsp AM)) : AM.M₀.E) := by
          simp
      _ = ∑ i, β i • (μ i • c) := by simp only [hδ]
      _ = ∑ i, (β i * μ i) • c := Finset.sum_congr rfl fun i _ => by rw [smul_smul]
      _ = (∑ i, β i * μ i) • c := by rw [Finset.sum_smul]
  have hβμ : (∑ i, β i * μ i) = 0 := by
    rcases smul_eq_zero.mp (hsum.symm.trans hdel) with h0 | h0
    · exact h0
    · exact absurd h0 hc0
  calc μ ⬝ᵥ β = ∑ i, μ i * β i := rfl
    _ = ∑ i, β i * μ i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = 0 := hβμ

theorem Sec108Data.exists_matV_LB (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {β : Fin 3 → AM.K} (hβ : β ≠ 0) (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM)
    {l : G} (hl : l ∈ LB M Q B) :
    ∃ μ : Fin 3 → AM.K, μ ⬝ᵥ β = 0 ∧
      D.matV AM ⟨l, hc.LB_le_H0 hl⟩ = 1 + Matrix.vecMulVec β μ := by
  let c : AM.M₀.E := ∑ i, β i • (D.bV AM i : AM.M₀.E)
  have hc0 : c ≠ 0 := bV_sum_ne_zero D AM hβ
  have hex : ∀ j : Fin 3, ∃ s : AM.K,
      ((D.delta AM ⟨l, hl⟩
        ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩ : ↥(D.Bsp AM)) : AM.M₀.E) = s • c :=
    fun j => Bsp_exists_smul D AM hβB hc0
      (D.delta AM ⟨l, hl⟩ ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩).2
  choose μ hμ using hex
  exact ⟨μ, dotProduct_eq_zero_of_delta D AM hl (c := c) rfl hβB hc0 hμ,
    matV_eq_one_add_vecMulVec D AM hl hμ⟩

private theorem exists_delta_eq_coord (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β μ : Fin 3 → AM.K}
    (hμ : μ ⬝ᵥ β = 0) {c : AM.M₀.E}
    (hsum_c : c = ∑ i, β i • (D.bV AM i : AM.M₀.E)) (hcB : c ∈ D.Bsp AM) (hc0 : c ≠ 0) :
    ∃ x : ↥(LB M Q B), ∀ j, ((D.delta AM x
        ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩ : ↥(D.Bsp AM)) : AM.M₀.E) =
      μ j • c := by
  have hcV : c ∈ AM.Vsp hc t := D.Bsp_le_Vsp AM hcB
  have hcAsp : c ∈ D.Asp AM := D.Vsp_le_Asp AM hcV
  let ell : ↥(AM.Vsp hc t) →ₗ[AM.K] AM.K := ∑ j, μ j • (D.bV AM).coord j
  have hell_bV : ∀ j, ell (D.bV AM j) = μ j := by
    intro j
    simp [ell, Finsupp.single_apply]
  have hell_c : ell ⟨c, hcV⟩ = 0 := by
    have hcsub : (⟨c, hcV⟩ : ↥(AM.Vsp hc t)) = ∑ i, β i • D.bV AM i := by
      apply Subtype.ext
      exact hsum_c
    rw [hcsub, map_sum]
    simp only [map_smul, hell_bV, smul_eq_mul]
    calc ∑ i, β i * μ i = ∑ i, μ i * β i := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hμ
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ell
  let mtilde : ↥(D.Asp AM) →ₗ[AM.K] AM.K := g.comp (D.Asp AM).subtype
  have hmtilde_bV : ∀ j,
      mtilde ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩ = μ j := by
    intro j
    have h := LinearMap.congr_fun hg ⟨D.bV AM j, (D.bV AM j).2⟩
    exact h.trans (hell_bV j)
  have hmtilde_c : mtilde ⟨c, hcAsp⟩ = 0 := by
    have h := LinearMap.congr_fun hg ⟨c, hcV⟩
    exact h.trans hell_c
  let f : ↥(D.Asp AM) →ₗ[AM.K] ↥(D.Bsp AM) :=
    (mtilde.smulRight c).codRestrict (D.Bsp AM)
      (fun a => (D.Bsp AM).smul_mem (mtilde a) hcB)
  have hf : ∀ a : ↥(D.Asp AM), (a : AM.M₀.E) ∈ D.Bsp AM → f a = 0 := by
    intro a ha
    obtain ⟨s, hs⟩ := Bsp_exists_smul D AM hcB hc0 ha
    apply Subtype.ext
    change mtilde a • c = (0 : AM.M₀.E)
    have haEq : a = s • (⟨c, hcAsp⟩ : ↥(D.Asp AM)) := by
      apply Subtype.ext
      change (a : AM.M₀.E) = s • c
      exact hs
    rw [haEq, map_smul, hmtilde_c, smul_zero, zero_smul]
  obtain ⟨x, hx⟩ := D.exists_delta_eq AM f hf
  refine ⟨x, fun j => ?_⟩
  have h := LinearMap.congr_fun hx
    ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩
  rw [h]
  change mtilde ⟨D.bV AM j, D.Vsp_le_Asp AM (D.bV AM j).2⟩ • c = μ j • c
  rw [hmtilde_bV j]

theorem Sec108Data.exists_LB_matV (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {β : Fin 3 → AM.K} (hβ : β ≠ 0) (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM)
    {μ : Fin 3 → AM.K} (hμ : μ ⬝ᵥ β = 0) :
    ∃ l, ∃ hl : l ∈ LB M Q B, D.matV AM ⟨l, hc.LB_le_H0 hl⟩ = 1 + Matrix.vecMulVec β μ := by
  let c : AM.M₀.E := ∑ i, β i • (D.bV AM i : AM.M₀.E)
  obtain ⟨x, hx⟩ := exists_delta_eq_coord D AM hμ (c := c) rfl hβB
    (bV_sum_ne_zero D AM hβ)
  exact ⟨x, x.2, matV_eq_one_add_vecMulVec D AM x.2 hx⟩

end CFSG.RankThree.GF2n.Stroth80
