module

public import CFSG.RankThree.GF2n.Smith81.OrthE1B2
public import CFSG.RankThree.GF2n.Smith81.OrthE1B7b
public import CFSG.RankThree.GF2n.Smith81.OrthE1B6Cent
public import CFSG.RankThree.GF2n.Smith81.OrthE1B6Syl

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Basic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {t : G}

theorem conj_le_Lgen {X : Subgroup G} {h : G} (hh : h ∈ Lgen M (LB M Q B))
    (hX : X ≤ Lgen M (LB M Q B)) : conjSubgroup h X ≤ Lgen M (LB M Q B) := by
  intro x hx
  have h1 : h⁻¹ * x * h ∈ X := mem_conjSubgroup.mp hx
  have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hh (hX h1)) (inv_mem hh)

theorem LB_le_E0 (hSplit : RtSplitStatement) (hH : E1Hyp M Q Z B t)
    (D : E1CaseBData M Q Z B t) : LB M Q B ≤ D.Y ⊔ D.Fb ⊔ D.Fc := by
  obtain ⟨-, -, -, -, -, hLB, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨-, -, -, -, hsup, -⟩ := D.two
  refine hLB.le.trans (sup_le ?_ ?_)
  · exact D.N_le_Y.trans (le_sup_left.trans le_sup_left)
  · refine inf_le_right.trans ?_
    rw [← hsup]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem X_le_E0 (D : E1CaseBData M Q Z B t) : E1Xpre M Q B t ≤ D.Y ⊔ D.Fb ⊔ D.Fc := by
  obtain ⟨-, -, -, -, hsup, -⟩ := D.two
  rw [← hsup]
  exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem E0_le_Lgen (hH : E1Hyp M Q Z B t) (D : E1CaseBData M Q Z B t) :
    D.Y ⊔ D.Fb ⊔ D.Fc ≤ Lgen M (LB M Q B) := by
  have hXL : E1Xpre M Q B t ≤ Lgen M (LB M Q B) := E1Xpre_le_Lgen hH.ctx hH.mem
  obtain ⟨-, -, hFbX, hFcX, -⟩ := D.two
  obtain ⟨-, -, hYX', -, -⟩ := D.two'
  exact sup_le (sup_le (hYX'.trans (conj_le_Lgen D.hg.1 hXL)) (hFbX.trans hXL)) (hFcX.trans hXL)


theorem caseBHyp_of_normalizer (hSplit : RtSplitStatement) (hH : E1Hyp M Q Z B t) {h : G}
    (hh : h ∈ Lgen M (LB M Q B)) (hhN : h ∈ Subgroup.normalizer (LB M Q B : Set G))
    (hne : conjSubgroup h (Nt M (LB M Q B) t) ≠ Nt M (LB M Q B) t) : E1CaseBHyp M Q B t h := by
  obtain ⟨hNL, -⟩ := hSplit G M Q Z B t hH
  exact ⟨hh, hhN, (Subgroup.map_mono hNL).trans (conjSubgroup_eq_self_iff.mpr hhN).le, hne⟩

theorem plus_of_caseBHyp (hB1 : B1Statement) (hH : E1Hyp M Q Z B t) {g : G}
    (hg : E1CaseBHyp M Q B t g) : CaseE1Plus M Q Z B t := by
  rcases (caseE1_iff M Q Z B t).mp hH.case with h | h
  · exact h
  · exact ((hB1 G M Q Z B t hH g hg).1 h).elim

theorem frame_of_data (hB1 : B1Statement) (hT : TripleStatement) (hH : E1Hyp M Q Z B t)
    (D : E1CaseBData M Q Z B t) :
    ∃ (AM : ActionModel M Q Z) (θ : AM.M₀.E ≃ₗ[AM.K] Tensor3 AM.K),
      (∀ e, AM.M₀.Qf e = tensor3Form (θ e)) ∧ FactorAct AM θ D.Y tensor3Act0 ∧
        FactorAct AM θ D.Fb tensor3Act1 ∧ FactorAct AM θ D.Fc tensor3Act2 := by
  have hplus := plus_of_caseBHyp hB1 hH D.hg
  obtain ⟨AM⟩ := ActionModel.nonempty hH.ctx.hyp
  have hN'g : conjSubgroup D.g (Nt M (LB M Q B) t) ≤ Nt M (LB M Q B) t ⊔ D.Fb :=
    le_sup_of_le_right D.N'_le_Fb
  obtain ⟨⟨θ0, hform, hY, hFb, hFc⟩, -⟩ :=
    hT G M Q Z B t hH AM D.g D.hg hplus D.Fb D.Fc D.Y D.two hN'g D.two'
  exact ⟨AM, θ0, hform, hY, hFb, hFc⟩

theorem conjX_le_X_of_conjN_eq (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    (hH : E1Hyp M Q Z B t) {h : G} (hh : h ∈ Lgen M (LB M Q B))
    (hN : conjSubgroup h (Nt M (LB M Q B) t) = Nt M (LB M Q B) t) :
    conjSubgroup h (E1Xpre M Q B t) ≤ E1Xpre M Q B t := by
  have hc := hH.ctx
  have hhH : h ∈ H0 M Z := Lgen_le_H0 hc hh
  have hhM : h ∈ M := hhH.1
  have hXL : E1Xpre M Q B t ≤ Lgen M (LB M Q B) := E1Xpre_le_Lgen hc hH.mem
  obtain ⟨hNL, hNX, hNR, hXR⟩ := b2_nt_facts hSplit hH
  have hcommNX := b2_comm_NX (Z := Z) hNX hNR hXR
  obtain ⟨-, -, -, -, hperf, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨-, -, hperfle⟩ := hCt G M Q Z B t hH
  have hQ : conjSubgroup h Q = Q := hc.conj_Q_eq hhM
  have hQN : ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hhM) q).mp hq
  have hQX : Q ≤ E1Xpre M Q B t := le_sup_right
  have hQP : Q ≤ conjSubgroup h (E1Xpre M Q B t) :=
    calc Q = conjSubgroup h Q := hQ.symm
      _ ≤ conjSubgroup h (E1Xpre M Q B t) := Subgroup.map_mono hQX
  have hPL : conjSubgroup h (E1Xpre M Q B t) ≤ Lgen M (LB M Q B) := conj_le_Lgen hh hXL
  have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
  have hPC : conjSubgroup h (E1Xpre M Q B t) ≤ E1Ct hc t := by
    intro p hp
    have hpL := hPL hp
    refine ⟨⟨(Lgen_le_H0 hc hpL).1, ?_⟩, Lgen_le_H0 hc hpL⟩
    have hx' : h⁻¹ * p * h ∈ E1Xpre M Q B t := mem_conjSubgroup.mp hp
    have ht' : h⁻¹ * t * h ∈ Nt M (LB M Q B) t := by
      have : t ∈ conjSubgroup h (Nt M (LB M Q B) t) := by rw [hN]; exact htN
      exact mem_conjSubgroup.mp this
    have h1 : ⁅h⁻¹ * p * h, h⁻¹ * t * h⁆ ∈ Q := b2_comm_symm (hcommNX _ ht' _ hx')
    have e : ⁅p, t⁆ = h * ⁅h⁻¹ * p * h, h⁻¹ * t * h⁆ * h⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hQN _ h1
  have hPperf : ⁅conjSubgroup h (E1Xpre M Q B t), conjSubgroup h (E1Xpre M Q B t)⁆ ⊔ Q =
      conjSubgroup h (E1Xpre M Q B t) := by
    have e : conjSubgroup h (⁅E1Xpre M Q B t, E1Xpre M Q B t⁆ ⊔ Q) =
        ⁅conjSubgroup h (E1Xpre M Q B t), conjSubgroup h (E1Xpre M Q B t)⁆ ⊔ Q := by
      unfold conjSubgroup at hQ ⊢
      rw [Subgroup.map_sup, Subgroup.map_commutator, hQ]
    rw [← e, hperf]
  exact hperfle _ hQP hPC hPperf


theorem factor_le_M (hSplit : RtSplitStatement) (hH : E1Hyp M Q Z B t) {X F : Subgroup G}
    (hX : X ≤ E1Xpre M Q B t) (hF : F ≤ X) : F ≤ M := by
  obtain ⟨-, -, hNR, -⟩ := b2_nt_facts hSplit hH
  have hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by rw [← hNR]; exact le_sup_right
  exact (hF.trans (hX.trans hXR)).trans (hH.ctx.Rt_le_M t)

theorem conjX_le_E0 (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    (hB1 : B1Statement) (hB2 : B2Statement) (hT : TripleStatement) (hH : E1Hyp M Q Z B t)
    (D : E1CaseBData M Q Z B t) {h : G} (hh : h ∈ Lgen M (LB M Q B))
    (hhN : h ∈ Subgroup.normalizer (LB M Q B : Set G)) :
    conjSubgroup h (E1Xpre M Q B t) ≤ D.Y ⊔ D.Fb ⊔ D.Fc := by
  by_cases hN : conjSubgroup h (Nt M (LB M Q B) t) = Nt M (LB M Q B) t
  · exact (conjX_le_X_of_conjN_eq hCt hSplit hH hh hN).trans (X_le_E0 D)
  have hg' : E1CaseBHyp M Q B t h := caseBHyp_of_normalizer hSplit hH hh hhN hN
  have hplus := plus_of_caseBHyp hB1 hH hg'
  obtain ⟨Fb', Fc', hFF, hN'⟩ := (hB1 G M Q Z B t hH h hg').2 hplus
  obtain ⟨Y', hY'⟩ := hB2 G M Q Z B t hH h hg' hplus Fb' Fc' hFF hN'
  obtain ⟨AM'⟩ := ActionModel.nonempty hH.ctx.hyp
  obtain ⟨-, -, -, -, hYFb'⟩ := hT G M Q Z B t hH AM' h hg' hplus Fb' Fc' Y' hFF hN' hY'
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hH.ctx.hyp.Q_normal.2
  obtain ⟨-, -, hFb'X, hFc'X, hsup', -, -, -, -⟩ := hFF
  obtain ⟨hQY', -, hY'X, -, hsup'', -, hcomm'', -, -⟩ := hY'
  have hFb'M : Fb' ≤ M := factor_le_M hSplit hH le_rfl hFb'X
  have hFc'M : Fc' ≤ M := factor_le_M hSplit hH le_rfl hFc'X
  have hcentX : ∀ c ∈ Y', ∀ y ∈ E1Xpre M Q B t, ⁅c, y⁆ ∈ Q := by
    rw [← hsup']
    exact b2_centralizer_sup hQn hFb'M hFc'M hYFb' hcomm''
  have hXL : E1Xpre M Q B t ≤ Lgen M (LB M Q B) := E1Xpre_le_Lgen hH.ctx hH.mem
  have hY'L : Y' ≤ Lgen M (LB M Q B) := hY'X.trans (conj_le_Lgen hh hXL)
  obtain ⟨AM, θ, hθ, hY, hFb, hFc⟩ := frame_of_data hB1 hT hH D
  obtain ⟨hQFb, hQFc, hFbX, hFcX, -⟩ := D.two
  obtain ⟨hQY, -⟩ := D.two'
  have hY'Y : Y' ≤ D.Y := fun y hy =>
    centY AM θ hθ hQY hY hFb hFc (Lgen_le_H0 hH.ctx (hY'L hy))
      (fun f hf => hcentX y hy f (hFbX hf)) (fun f hf => hcentX y hy f (hFcX hf))
  rw [← hsup'']
  exact sup_le (hY'Y.trans (le_sup_left.trans le_sup_left)) (hFc'X.trans (X_le_E0 D))


theorem conj_E0_le (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    (hB1 : B1Statement) (hB2 : B2Statement) (hT : TripleStatement) (hH : E1Hyp M Q Z B t)
    (D : E1CaseBData M Q Z B t) {n : G} (hn : n ∈ Lgen M (LB M Q B))
    (hnN : n ∈ Subgroup.normalizer (LB M Q B : Set G)) :
    conjSubgroup n (D.Y ⊔ D.Fb ⊔ D.Fc) ≤ D.Y ⊔ D.Fb ⊔ D.Fc := by
  obtain ⟨hFbX, hFcX⟩ : D.Fb ≤ E1Xpre M Q B t ∧ D.Fc ≤ E1Xpre M Q B t :=
    ⟨D.two.2.2.1, D.two.2.2.2.1⟩
  have hYX' : D.Y ≤ conjSubgroup D.g (E1Xpre M Q B t) := D.two'.2.2.1
  have hX := conjX_le_E0 hCt hSplit hB1 hB2 hT hH D hn hnN
  have hgn : n * D.g ∈ Lgen M (LB M Q B) := mul_mem hn D.hg.1
  have hgnN : n * D.g ∈ Subgroup.normalizer (LB M Q B : Set G) := mul_mem hnN D.hg.2.1
  have hX' := conjX_le_E0 hCt hSplit hB1 hB2 hT hH D hgn hgnN
  rw [conjSubgroup_sup', conjSubgroup_sup']
  refine sup_le (sup_le ?_ ?_) ?_
  · have h1 : conjSubgroup n D.Y ≤ conjSubgroup n (conjSubgroup D.g (E1Xpre M Q B t)) :=
      Subgroup.map_mono hYX'
    rw [← conjSubgroup_mul] at h1
    exact h1.trans hX'
  · exact (Subgroup.map_mono hFbX).trans hX
  · exact (Subgroup.map_mono hFcX).trans hX

theorem conj_E0_eq (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    (hB1 : B1Statement) (hB2 : B2Statement) (hT : TripleStatement) (hH : E1Hyp M Q Z B t)
    (D : E1CaseBData M Q Z B t) {n : G} (hn : n ∈ Lgen M (LB M Q B))
    (hnN : n ∈ Subgroup.normalizer (LB M Q B : Set G)) :
    conjSubgroup n (D.Y ⊔ D.Fb ⊔ D.Fc) = D.Y ⊔ D.Fb ⊔ D.Fc := by
  refine le_antisymm (conj_E0_le hCt hSplit hB1 hB2 hT hH D hn hnN) ?_
  have h1 := conj_E0_le hCt hSplit hB1 hB2 hT hH D (inv_mem hn) (inv_mem hnN)
  intro x hx
  have h2 : n⁻¹ * x * n ∈ D.Y ⊔ D.Fb ⊔ D.Fc := by
    have := h1 (show n⁻¹ * x * n⁻¹⁻¹ ∈ conjSubgroup n⁻¹ (D.Y ⊔ D.Fb ⊔ D.Fc) from
      ⟨x, hx, by simp [MulAut.conj_apply]⟩)
    simpa using this
  exact mem_conjSubgroup.mpr h2

end Basic


section Lift

open CFSG.RankThree.GF2n.Smith81.OrthTN

theorem exists_sylow_index_two {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {H : Type*} [Group H] (L : Subgroup H) (hL : IsPGroup 2 L)
    (ρ : H →* (Cube 3 K ≃ₗ[K] Cube 3 K)) (hker : ρ.ker ≤ L) (hρL : L.map ρ = cubeU 3 K)
    (hnorm : ∀ n : H, ρ n ∈ Subgroup.normalizer (cubeU 3 K : Set (Cube 3 K ≃ₗ[K] Cube 3 K)) →
      (∀ x ∈ cubeE 3 K, ρ n * x * (ρ n)⁻¹ ∈ cubeE 3 K) ∧
        (∀ x ∈ cubeE 3 K, (ρ n)⁻¹ * x * ρ n ∈ cubeE 3 K)) :
    ∃ S : Sylow 2 H, L ≤ S ∧ L.relIndex S ≤ 2 := by
  obtain ⟨S, hS⟩ := hL.exists_le_sylow
  refine ⟨S, hS, ?_⟩
  have hP : IsPGroup 2 (Subgroup.map ρ (S : Subgroup H)) := S.isPGroup'.map ρ
  have hUP : cubeU 3 K ≤ Subgroup.map ρ (S : Subgroup H) := by
    rw [← hρL]; exact Subgroup.map_mono hS
  have key := b6_index_two hq (Subgroup.map ρ (S : Subgroup H)) hP hUP (fun s hs hsN => by
    obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.mp hs
    exact hnorm n hsN)
  have e : (L.map ρ).relIndex ((S : Subgroup H).map ρ) = L.relIndex S := by
    rw [Subgroup.relIndex_map_map, sup_eq_left.mpr hker, sup_eq_left.mpr (hker.trans hS)]
  rw [hρL] at e
  rw [← e]
  exact key


variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {t : G}

theorem exists_S1 (hCt : CtStructureStatement) (hSplit : RtSplitStatement)
    (hB1 : B1Statement) (hB2 : B2Statement) (hT : TripleStatement) (hH : E1Hyp M Q Z B t)
    (D : E1CaseBData M Q Z B t) :
    ∃ S₁ : Subgroup G, Syl2Pre M Q B S₁ ∧ LB M Q B ≤ S₁ ∧ (LB M Q B).relIndex S₁ ≤ 2 := by
  classical
  have hc := hH.ctx
  obtain ⟨AM, θ0, hθ0, hY, hFb, hFc⟩ := frame_of_data hB1 hT hH D
  let θ : AM.M₀.E ≃ₗ[AM.K] Cube 3 AM.K := θ0.trans (tensor3Cube AM.K)
  let ρ0 := b7b_coordHom AM θ
  have hqK : 4 ≤ Nat.card AM.K := by rw [AM.glob.card]; exact hc.hyp.q4
  have hLBE := LB_le_E0 hSplit hH D
  have hE0L := E0_le_Lgen hH D
  have hLH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hE0H : D.Y ⊔ D.Fb ⊔ D.Fc ≤ H0 M Z := hE0L.trans hLH
  have hYH : D.Y ≤ H0 M Z := le_sup_left.trans (le_sup_left.trans hE0H)
  have hFbH : D.Fb ≤ H0 M Z := le_sup_right.trans (le_sup_left.trans hE0H)
  have hFcH : D.Fc ≤ H0 M Z := le_sup_right.trans hE0H
  have himgY := b7b_factorAct_img AM θ0 D.Y 0 tensor3Act0 tensor3Cube_act0 hY
  have himgFb := b7b_factorAct_img AM θ0 D.Fb 1 tensor3Act1 tensor3Cube_act1 hFb
  have himgFc := b7b_factorAct_img AM θ0 D.Fc 2 tensor3Act2 tensor3Cube_act2 hFc
  have himgE : ((D.Y ⊔ D.Fb ⊔ D.Fc).subgroupOf (H0 M Z)).map ρ0 = cubeE 3 AM.K := by
    rw [b7b_img_sup ρ0 (sup_le hYH hFbH) hFcH, b7b_img_sup ρ0 hYH hFbH, himgY, himgFb, himgFc]
    exact (cubeE_eq_sup hqK).symm
  have hLBH : LB M Q B ≤ H0 M Z := hLBE.trans hE0H
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hQH : Q ≤ H0 M Z := hQLB.trans hLBH
  set L : Subgroup ↥(H0 M Z) := (LB M Q B).subgroupOf (H0 M Z) with hLdef
  have hker : ∀ x, ρ0 x = 1 → x ∈ L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hQLB ((b7b_coordHom_eq_one_iff AM θ x).mp hx))
  have hkerEq : ρ0.ker = Q.subgroupOf (H0 M Z) := Subgroup.ext fun x => by
    rw [MonoidHom.mem_ker, b7b_coordHom_eq_one_iff, Subgroup.mem_subgroupOf]
  have hcardL : Nat.card (L.map ρ0) = Nat.card AM.K ^ 3 := by
    have h1 := b7b_card_map_mul_card_ker ρ0 L
    have hLinf : L ⊓ ρ0.ker = ρ0.ker :=
      inf_eq_right.mpr fun x hx => hker x (MonoidHom.mem_ker.mp hx)
    rw [hLinf, hkerEq] at h1
    have hQcard : Nat.card ↥(Q.subgroupOf (H0 M Z)) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
    have hLcard : Nat.card L = Nat.card (LB M Q B) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLBH).toEquiv
    rw [hQcard, hLcard, b7b_card_LB_of_split hSplit hH, ← AM.glob.card] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [h1, mul_comm])
  have hLE : L.map ρ0 ≤ cubeE 3 AM.K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← himgE]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (hLBE (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
  obtain ⟨C, hCE, hC⟩ := exists_conj_cubeU 3 AM.K (L.map ρ0) hLE hcardL
  let cj : (Cube 3 AM.K ≃ₗ[AM.K] Cube 3 AM.K) →* (Cube 3 AM.K ≃ₗ[AM.K] Cube 3 AM.K) :=
    (MulAut.conj C⁻¹).toMonoidHom
  have hcj : ∀ g, cj g = C⁻¹ * g * C := fun g => by simp [cj, MulAut.conj_apply]
  let ι : ↥(Lgen M (LB M Q B)) →* ↥(H0 M Z) := Subgroup.inclusion hLH
  let ρ : ↥(Lgen M (LB M Q B)) →* (Cube 3 AM.K ≃ₗ[AM.K] Cube 3 AM.K) := (cj.comp ρ0).comp ι
  have hρ : ∀ x, ρ x = C⁻¹ * ρ0 (ι x) * C := fun x => hcj _
  let L' : Subgroup ↥(Lgen M (LB M Q B)) := (LB M Q B).subgroupOf (Lgen M (LB M Q B))
  have hLBL : LB M Q B ≤ Lgen M (LB M Q B) := hLBE.trans hE0L
  have hmemL' : ∀ x : ↥(Lgen M (LB M Q B)), x ∈ L' ↔ (x : G) ∈ LB M Q B := fun x =>
    Subgroup.mem_subgroupOf
  have hker' : ρ.ker ≤ L' := by
    intro x hx
    have h1 : C⁻¹ * ρ0 (ι x) * C = 1 := by rw [← hρ]; exact hx
    have h2 : ρ0 (ι x) = 1 := by
      have e : ρ0 (ι x) = C * (C⁻¹ * ρ0 (ι x) * C) * C⁻¹ := by group
      rw [e, h1]; group
    exact (hmemL' x).mpr (hQLB ((b7b_coordHom_eq_one_iff AM θ (ι x)).mp h2))
  have hρL : L'.map ρ = cubeU 3 AM.K := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      have h1 : ρ0 (ι l) ∈ L.map ρ0 := Subgroup.mem_map_of_mem ρ0 (show ι l ∈ L from hl)
      rw [hρ]
      exact (hC _).mp h1
    · intro hx
      have h1 : C * x * C⁻¹ ∈ L.map ρ0 := (hC _).mpr (by simpa [mul_assoc] using hx)
      obtain ⟨y, hy, hyx⟩ := h1
      have hyLB : (y : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hy
      refine ⟨⟨(y : G), hLBL hyLB⟩, (hmemL' _).mpr hyLB, ?_⟩
      rw [hρ]
      have : ι ⟨(y : G), hLBL hyLB⟩ = y := rfl
      rw [this, hyx]
      group
  have hLpg : IsPGroup 2 L' := by
    obtain ⟨n, k, hn2, -⟩ := hc.hyp.cp
    have hQ9 : Nat.card Q = Nat.card Z ^ 9 := hH.case.1
    refine IsPGroup.of_card (n := n * 12) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLBL).toEquiv,
      b7b_card_LB_of_split hSplit hH, hQ9, ← pow_add, hn2, ← pow_mul]
  have hnormLB : ∀ n : ↥(Lgen M (LB M Q B)),
      ρ n ∈ Subgroup.normalizer
        (cubeU 3 AM.K : Set (Cube 3 AM.K ≃ₗ[AM.K] Cube 3 AM.K)) →
        (n : G) ∈ Subgroup.normalizer (LB M Q B : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    have hl' : l ∈ LB M Q B := hl
    have hlL : (⟨l, hLBL hl'⟩ : ↥(Lgen M (LB M Q B))) ∈ L' := (hmemL' _).mpr hl'
    have h1 : ρ ⟨l, hLBL hl'⟩ ∈ cubeU 3 AM.K := by
      rw [← hρL]; exact Subgroup.mem_map_of_mem ρ hlL
    have h2 : ρ n * ρ ⟨l, hLBL hl'⟩ * (ρ n)⁻¹ ∈ cubeU 3 AM.K :=
      (Subgroup.mem_normalizer_iff.mp hn _).mp h1
    rw [← map_inv, ← map_mul, ← map_mul, ← hρL] at h2
    obtain ⟨l₁, hl₁, hl₁e⟩ := h2
    have h3 : l₁⁻¹ * (n * ⟨l, hLBL hl'⟩ * n⁻¹) ∈ L' := by
      apply hker'
      rw [MonoidHom.mem_ker, map_mul, map_inv, hl₁e, inv_mul_cancel]
    have h4 : n * ⟨l, hLBL hl'⟩ * n⁻¹ ∈ L' := by
      simpa using L'.mul_mem hl₁ h3
    exact (hmemL' _).mp h4
  have hnormE : ∀ n : ↥(Lgen M (LB M Q B)), (n : G) ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ∀ x ∈ cubeE 3 AM.K, ρ n * x * (ρ n)⁻¹ ∈ cubeE 3 AM.K := by
    intro n hn x hx
    have hxC : C * x * C⁻¹ ∈ cubeE 3 AM.K := mul_mem (mul_mem hCE hx) (inv_mem hCE)
    rw [← himgE] at hxC
    obtain ⟨y, hy, hyx⟩ := hxC
    have hyE : (y : G) ∈ D.Y ⊔ D.Fb ⊔ D.Fc := Subgroup.mem_subgroupOf.mp hy
    have hconj := conj_E0_eq hCt hSplit hB1 hB2 hT hH D n.2 hn
    have hnyn : (n : G) * y * (n : G)⁻¹ ∈ D.Y ⊔ D.Fb ⊔ D.Fc := by
      rw [← hconj]; exact ⟨y, hyE, by simp [MulAut.conj_apply]⟩
    have hy' : ι n * y * (ι n)⁻¹ ∈ (D.Y ⊔ D.Fb ⊔ D.Fc).subgroupOf (H0 M Z) :=
      Subgroup.mem_subgroupOf.mpr (by simpa [ι] using hnyn)
    have h5 : ρ0 (ι n * y * (ι n)⁻¹) ∈ cubeE 3 AM.K := by
      rw [← himgE]; exact Subgroup.mem_map_of_mem ρ0 hy'
    have h6 : ρ n * x * (ρ n)⁻¹ = C⁻¹ * ρ0 (ι n * y * (ι n)⁻¹) * C := by
      have hx' : x = C⁻¹ * ρ0 y * C := by rw [hyx]; group
      rw [hρ n, map_mul, map_mul, map_inv, hx']
      group
    rw [h6]
    exact mul_mem (mul_mem (inv_mem hCE) h5) hCE
  have hnorm : ∀ n : ↥(Lgen M (LB M Q B)),
      ρ n ∈ Subgroup.normalizer
        (cubeU 3 AM.K : Set (Cube 3 AM.K ≃ₗ[AM.K] Cube 3 AM.K)) →
      (∀ x ∈ cubeE 3 AM.K, ρ n * x * (ρ n)⁻¹ ∈ cubeE 3 AM.K) ∧
        (∀ x ∈ cubeE 3 AM.K, (ρ n)⁻¹ * x * ρ n ∈ cubeE 3 AM.K) := by
    intro n hn
    refine ⟨hnormE n (hnormLB n hn), fun x hx => ?_⟩
    have hn' : ((n⁻¹ : ↥(Lgen M (LB M Q B))) : G) ∈ Subgroup.normalizer (LB M Q B : Set G) := by
      simpa using inv_mem (hnormLB n hn)
    have h := hnormE n⁻¹ hn' x hx
    simpa [map_inv] using h
  obtain ⟨S, hLS, hrel⟩ := exists_sylow_index_two hqK L' hLpg ρ hker' hρL hnorm
  set S₁ : Subgroup G := (S : Subgroup ↥(Lgen M (LB M Q B))).map
    (Lgen M (LB M Q B)).subtype with hS₁
  have hLS₁ : LB M Q B ≤ S₁ := fun x hx =>
    ⟨⟨x, hLBL hx⟩, hLS ((hmemL' _).mpr hx), rfl⟩
  have hS₁L : S₁ ≤ Lgen M (LB M Q B) := Subgroup.map_subtype_le _
  have hS₁pg : IsPGroup 2 ↥S₁ := S.isPGroup'.map (Lgen M (LB M Q B)).subtype
  have hS₁sub : S₁.subgroupOf (Lgen M (LB M Q B)) = (S : Subgroup ↥(Lgen M (LB M Q B))) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  refine ⟨S₁, ⟨hQLB.trans hLS₁, hS₁L, ?_, ?_⟩, hLS₁, ?_⟩
  · haveI hN : (Q.subgroupOf S₁).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
      fun x hx => hc.hyp.Q_normal.2 (hLH (hS₁L hx)).1
    exact ⟨hN, hS₁pg.to_quotient (Q.subgroupOf S₁)⟩
  · rw [Subgroup.relIndex, hS₁sub]
    exact Sylow.not_dvd_index S
  · have h1 : (LB M Q B).relIndex S₁ = L'.relIndex S := by
      have e := Subgroup.relIndex_map_map_of_injective (f := (Lgen M (LB M Q B)).subtype)
        L' (S : Subgroup ↥(Lgen M (LB M Q B))) (Subgroup.subtype_injective _)
      rw [Subgroup.map_subgroupOf_eq_of_le hLBL] at e
      exact e
    rw [h1]
    exact hrel

end Lift

end CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.Smith23E1.B6


theorem b6_of (_hD : CaseBDataStatement) (hCt : CtStructureStatement)
    (hSplit : RtSplitStatement) (_hN : NtConjLBStatement) (hB1 : B1Statement)
    (hB2 : B2Statement) (hT : TripleStatement) : B6Statement := by
  intro G _ _ M Q Z B t hH D
  exact ⟨LB_le_E0 hSplit hH D, E0_le_Lgen hH D,
    fun n hn hnN => conj_E0_eq hCt hSplit hB1 hB2 hT hH D hn hnN,
    exists_S1 hCt hSplit hB1 hB2 hT hH D⟩

end CFSG.RankThree.GF2n.Smith81.Smith23E1

end
