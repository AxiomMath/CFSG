module

public import CFSG.RankThree.GF2n.Stroth80.Sec101SatRoots
public import CFSG.RankThree.GF2n.Stroth80.Sec111Norm
public import CFSG.RankThree.GF2n.Stroth80.Sec101SLPt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec10Hyp.comm_of_mem_normalizer (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {C D : Subgroup G} (hC : IsRootB M B C) (hD : IsRootB M B D) {τ : G}
    (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q) (hτN : τ ∈ Subgroup.normalizer (LB M Q C : Set G)) :
    ∀ c ∈ C, ∀ d ∈ D, c * d = d * c := by
  obtain ⟨g, hgM, hDg⟩ := hD.exists_conj hC
  have hcC : Ctx M Q Z C := hC.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  have hne : conjSubgroup g (LB M Q C) ⊓ Subgroup.normalizer (LB M Q C : Set G) ≠ Q := by
    intro h
    apply hτQ
    rw [← h]
    refine ⟨?_, hτN⟩
    rw [← hcC.LB_conj hgM, ← hDg]
    exact hτ
  have h36 := stroth_3_6 h34 hcC HC.width HC.n_gt HC.noA2 HC.gen hgM hne
  intro c hc' d hd
  rw [hDg] at hd
  exact h36 c hc' d hd

private theorem inv_not_mem_normalizer_sup_Z_of_not_mem_normalizer_LB (hc : Ctx M Q Z B)
    {D : Subgroup G} (hD : IsRootB M B D) {σ : G} (hσM : σ ∈ M)
    (hσN : σ ∉ Subgroup.normalizer (LB M Q D : Set G)) :
    σ⁻¹ ∉ Subgroup.normalizer ((D ⊔ Z : Subgroup G) : Set G) := by
  have hcD : Ctx M Q Z D := hD.ctx hc
  intro h
  exact hσN (hcD.mem_normalizer_LB_of_normalizer hσM
    (by simpa using (Subgroup.normalizer _).inv_mem h))

private theorem sup_Z_ne_of_not_mem_normalizer_LB (hc : Ctx M Q Z B) {D : Subgroup G}
    (hD : IsRootB M B D) {σ : G} (hσM : σ ∈ M)
    (hσN : σ ∉ Subgroup.normalizer (LB M Q D : Set G)) :
    D ⊔ Z ≠ conjSubgroup σ⁻¹ D ⊔ Z := by
  have hcD : Ctx M Q Z D := hD.ctx hc
  have hσDZ := inv_not_mem_normalizer_sup_Z_of_not_mem_normalizer_LB hc hD hσM hσN
  intro h
  apply hσDZ
  apply conjSubgroup_eq_self_iff.mp
  rw [conjSubgroup_sup', hcD.conj_Z_eq (M.inv_mem hσM), ← h]

private theorem conj_le_of_ne_sup_Z (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {X' : Subgroup G} (hX' : IsClique101 M Q Z B X')
    (hsat' : IsSaturated101 M Q Z B X') {D : Subgroup G} (hD : IsRootB M B D)
    (hDX' : D ≤ X') {σ τ : G} (hσ : σ⁻¹ ∈ M) (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hτD' : τ ∈ LB M Q (conjSubgroup σ⁻¹ D))
    (hne : D ⊔ Z ≠ conjSubgroup σ⁻¹ D ⊔ Z) :
    conjSubgroup σ⁻¹ D ≤ X' := by
  have hcD : Ctx M Q Z D := hD.ctx hc
  have hD' : IsRootB M B (conjSubgroup σ⁻¹ D) := hD.conj hσ
  have hR : Rt M (LB M Q D) τ ≠ LB M Q D := hD.Rt_ne H hD' hτD' hne
  refine (sec39_conjB_le_Vt hσ ?_).trans
    (IsSaturated101.Vt_le h34 H hX' hsat' hD hDX' hτ hτQ hR)
  rw [← hcD.LB_conj hσ]
  exact hτD'

private theorem conj_le_sup_of_comm (hc : Ctx M Q Z B) {X X' : Subgroup G}
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X) (hDX' : D ≤ X')
    {σ : G} (hσ : σ ∈ LB M Q C) (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c)
    (hD'X' : conjSubgroup σ⁻¹ D ≤ X') : conjSubgroup σ⁻¹ D ≤ Z ⊔ D := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  intro y hy
  have hδ : σ * y * σ⁻¹ ∈ D := by simpa using mem_conjSubgroup.mp hy
  have hyδ : y = σ⁻¹ * (σ * y * σ⁻¹) * σ := by group
  set δ := σ * y * σ⁻¹ with hδdef
  have hδQ : δ⁻¹ ∈ Q := Q.inv_mem (hX'.le_Q (hDX' hδ))
  have hδN : δ⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
    Subgroup.mem_normalizer_fintype fun c hc' => by
      rw [show δ⁻¹ * c * δ⁻¹⁻¹ = c by rw [inv_inv, mul_assoc, hCD c hc' δ hδ]; group]
      exact hc'
  have h1 : ⁅δ⁻¹, σ⁻¹⁆ ∈ Q ⊓ QB C :=
    hcC.comm_mem_inf_QB_of_mem_normalizer hδQ hδN ((LB M Q C).inv_mem hσ)
  have e : ⁅δ⁻¹, σ⁻¹⁆ = δ⁻¹ * y := by rw [commutatorElement_def, hyδ]; group
  have h2 : ⁅δ⁻¹, σ⁻¹⁆ ∈ X' := by
    rw [e]
    exact X'.mul_mem (X'.inv_mem (hDX' hδ)) (hD'X' hy)
  have h3 : ⁅δ⁻¹, σ⁻¹⁆ ∈ Z :=
    IsSaturated101.inf_QB_le_Z hc hsat hX' hXX' hC hCX ⟨h2, h1.2⟩
  have hy' : y = δ * ⁅δ⁻¹, σ⁻¹⁆ := by rw [e]; group
  rw [hy']
  exact (Z ⊔ D).mul_mem (Subgroup.mem_sup_right hδ) (Subgroup.mem_sup_left h3)

private theorem sup_Z_eq_of_le_sup (hc : Ctx M Q Z B) {D : Subgroup G} (hD : IsRootB M B D)
    {D' : Subgroup G} (hD' : Ctx M Q Z D') (hle : D' ≤ Z ⊔ D) :
    D' ⊔ Z = D ⊔ Z := by
  have hcD : Ctx M Q Z D := hD.ctx hc
  obtain ⟨p, hpQ, hpD⟩ := hcD.exists_conj_of_le_ZB hD' hle
  have e := hcD.conj_sup_Z_of_mem_Q hpQ
  rw [conjSubgroup_sup', hcD.conj_Z_eq (hc.hyp.Q_normal.1 hpQ)] at e
  rw [← hpD, e]

theorem IsSaturated101.mem_normalizer_of_comm (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {X X' : Subgroup G} (hsat : IsSaturated101 M Q Z B X)
    (hX' : IsClique101 M Q Z B X') (hsat' : IsSaturated101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X) (hD : IsRootB M B D)
    (hDX' : D ≤ X') {σ τ : G} (hσ : σ ∈ LB M Q C) (hτ : τ ∈ LB M Q D) (hτQ : τ ∉ Q)
    (hτN : τ ∈ Subgroup.normalizer (LB M Q C : Set G)) (hστ : ⁅σ, τ⁆ ∈ Q) :
    σ ∈ Subgroup.normalizer (LB M Q D : Set G) := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  have hσM : σ ∈ M := hcC.LB_le_M hσ
  have hσM' : σ⁻¹ ∈ M := M.inv_mem hσM
  have hCD := H.comm_of_mem_normalizer h34 hC hD hτ hτQ hτN
  by_contra hσN
  have hne := sup_Z_ne_of_not_mem_normalizer_LB hc hD hσM hσN
  have hτD' : τ ∈ LB M Q (conjSubgroup σ⁻¹ D) := by
    rw [hcD.LB_conj hσM', mem_conjSubgroup, inv_inv]
    have h1 : σ * τ * σ⁻¹ = ⁅σ, τ⁆ * τ := by rw [commutatorElement_def]; group
    rw [h1]
    exact (LB M Q D).mul_mem (sec39_Q_le_LB hστ) hτ
  have hD'X' := conj_le_of_ne_sup_Z h34 H hX' hsat' hD hDX' hσM' hτ hτQ hτD' hne
  have hle := conj_le_sup_of_comm hc hsat hX' hXX' hC hCX hDX' hσ hCD hD'X'
  exact hne (sup_Z_eq_of_le_sup hc hD ((hD.conj hσM').ctx hc) hle).symm

theorem IsSaturated101.exists_not_mem_normalizer (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X X' : Subgroup G}
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {C D : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X) (hD : IsRootB M B D)
    (hDX' : D ≤ X') (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) :
    ∃ l ∈ LB M Q C, l ∉ Subgroup.normalizer (LB M Q D : Set G) := by
  by_contra hall
  push Not at hall
  have hcC : Ctx M Q Z C := hC.ctx hc
  have hcD : Ctx M Q Z D := hD.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  have HD : Sec10Hyp hcD n := hD.sec10 H
  have hZ := IsSaturated101.inf_QB_le_Z hc hsat hX' hXX' hC hCX
  have h34C : Conc34 M Q Z C := h34 G M Q Z C hcC n HC.width HC.n_gt HC.noA2 HC.gen
  have hDle : D ≤ Q ⊓ QB C := by
    refine h34C D (fun d hd => ⟨hX'.le_Q (hDX' hd),
      Subgroup.mem_centralizer_iff.mpr fun c hc' => hCD c hc' d hd⟩) fun x hx t ht => ?_
    have htDZ : t ∈ Subgroup.normalizer ((D ⊔ Z : Subgroup G) : Set G) :=
      (hcD.mem_normalizer_LB_iff' HD.width HD.n_gt HD.noA2 (hcC.LB_le_M ht)).mp (hall t ht)
    have hxN : x ∈ Subgroup.normalizer (C : Set G) :=
      Subgroup.mem_normalizer_fintype fun c hc' => by
        rw [show x * c * x⁻¹ = c by rw [← hCD c hc' x hx]; group]
        exact hc'
    have h1 : ⁅x, t⁆ ∈ Q ⊓ QB C := hcC.comm_mem_inf_QB_of_mem_normalizer (hX'.le_Q (hDX' hx)) hxN ht
    have h2 : ⁅t, x⁆ ∈ X' := by
      rw [commutatorElement_def]
      have h4 : t * x * t⁻¹ ∈ D ⊔ Z :=
        (Subgroup.mem_normalizer_iff.mp htDZ x).mp (Subgroup.mem_sup_left hx)
      exact X'.mul_mem (sup_le hDX' hX'.Z_le h4) (X'.inv_mem (hDX' hx))
    have h3 : ⁅t, x⁆ ∈ QB C := by
      rw [← commutatorElement_inv]; exact (QB C).inv_mem h1.2
    exact Subgroup.mem_sup_right (hZ ⟨h2, h3⟩)
  exact hD.not_le_Z hc ((le_inf hDX' (hDle.trans inf_le_right)).trans hZ)

end CFSG.RankThree.GF2n.Stroth80
