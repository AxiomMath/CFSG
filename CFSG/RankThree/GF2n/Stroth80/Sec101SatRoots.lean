module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Dim
public import CFSG.RankThree.GF2n.Stroth80.Sec101Fix

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem IsRootB.not_le_Z (hc : Ctx M Q Z B) {E : Subgroup G} (hE : IsRootB M B E) :
    ¬ E ≤ Z := by
  intro hEZ
  have hbot : E = ⊥ := by
    have h := (hE.ctx hc).inf_eq_bot
    rwa [inf_eq_right.mpr hEZ] at h
  have hcard : Nat.card E = Nat.card Z := (hE.isZConjugate hc).card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have := hc.hyp.q4
  omega

theorem IsSaturated101.conj_eq_of_mem_normalizer (hc : Ctx M Q Z B) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G}
    (hC : IsRootB M B C) (hCX : C ≤ X) {g : G} (hg : g ∈ M)
    (hgN : g ∈ Subgroup.normalizer ((C ⊔ Z : Subgroup G) : Set G)) :
    conjSubgroup g X = X := by
  have hgC : conjSubgroup g C ≤ X ⊓ conjSubgroup g X := by
    refine le_inf ?_ (Subgroup.map_mono hCX)
    calc conjSubgroup g C ≤ conjSubgroup g (C ⊔ Z) := Subgroup.map_mono le_sup_left
      _ = C ⊔ Z := conjSubgroup_eq_self_iff.mpr hgN
      _ ≤ X := sup_le hCX hX.Z_le
  rcases IsSaturated101.inf_eq hc hX hsat hg with h | h
  · exact absurd (hgC.trans h.le) ((hC.conj hg).not_le_Z hc)
  · exact h

theorem IsSaturated101.mem_normalizer_of_mem_normalizer_LB {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    {g : G} (hg : g ∈ M) (hgN : g ∈ Subgroup.normalizer (LB M Q C : Set G)) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  have hgCZ := (hcC.mem_normalizer_LB_iff' HC.width HC.n_gt HC.noA2 hg).mp hgN
  exact conjSubgroup_eq_self_iff.mp
    (IsSaturated101.conj_eq_of_mem_normalizer hc hX hsat hC hCX hg hgCZ)

theorem IsRootB.conj_inf_QB_of_mem_normalizer {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {C : Subgroup G} (hC : IsRootB M B C) {g : G} (hg : g ∈ M)
    (hgN : g ∈ Subgroup.normalizer (LB M Q C : Set G)) :
    conjSubgroup g (Q ⊓ QB C) = Q ⊓ QB C := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  have hgCZ := (hcC.mem_normalizer_LB_iff' HC.width HC.n_gt HC.noA2 hg).mp hgN
  have hle : conjSubgroup g C ≤ Z ⊔ C := by
    calc conjSubgroup g C ≤ conjSubgroup g (C ⊔ Z) := Subgroup.map_mono le_sup_left
      _ = C ⊔ Z := conjSubgroup_eq_self_iff.mpr hgCZ
      _ = Z ⊔ C := sup_comm _ _
  obtain ⟨p, hpQ, hp⟩ := hcC.exists_conj_of_le_ZB ((hC.conj hg).ctx hc) hle
  rw [conjSubgroup_inf, hcC.conj_Q_eq hg, ← QB_conj, ← hp, hcC.conj_inf_QB_of_mem_Q hpQ]

theorem IsSaturated101.LB_inf_eq_of_inf_eq (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {X X' : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) (hXX' : X ⊓ X' = Z) {C D : Subgroup G}
    (hC : IsRootB M B C) (hCX : C ≤ X) (hD : IsRootB M B D) (hDX' : D ≤ X') :
    LB M Q C ⊓ LB M Q D = Q := by
  obtain ⟨g, hgM, hDg⟩ := hD.exists_conj hC
  have hLBD : LB M Q D = conjSubgroup g (LB M Q C) := by rw [hDg, (hC.ctx hc).LB_conj hgM]
  by_contra hne
  have hne' : LB M Q C ⊓ conjSubgroup g (LB M Q C) ≠ Q := by rwa [← hLBD]
  have hXg : conjSubgroup g X = X := IsSaturated101.conj_eq_of_LB h34 H hX hsat hC hCX hgM hne'
  have hDX : D ≤ X := by
    rw [hDg]
    calc conjSubgroup g C ≤ conjSubgroup g X := Subgroup.map_mono hCX
      _ = X := hXg
  exact hD.not_le_Z hc ((le_inf hDX hDX').trans hXX'.le)

theorem Sec10Hyp.four_le (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) : 4 ≤ n := by
  obtain ⟨t, ht, htQ, hsl⟩ := H.ex
  obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
  have := stroth6SLDim_of_34 h34 G M Q Z B hc n t (H.toSec5 ht htQ) m hm2 (Or.inl hslm)
  omega

theorem Ctx.comm_mem_centralizer_of_mem_LB (hc : Ctx M Q Z B) {y τ : G} (hy : y ∈ Q)
    (hτ : τ ∈ LB M Q B) : ⁅y, τ⁆ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
  obtain ⟨s, hs, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB hτ
  have hs' : s ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := by rw [← hc.QB_inf_M_eq]; exact hs
  have h1 := hc.comm_mem_centralizer_B hy hs'
  have hyq : ⁅y, q⁆ ∈ Z := Smith81.comm_mem_Z hc.hyp hy hq
  have hsz : s * ⁅y, q⁆ * s⁻¹ = ⁅y, q⁆ := by
    rw [(Subgroup.mem_centralizer_iff.mp hs'.2 _ hyq).symm]; group
  have e : ⁅y, s * q⁆ = ⁅y, s⁆ * (s * ⁅y, q⁆ * s⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, hsz]
  refine (Q ⊓ Subgroup.centralizer (B : Set G)).mul_mem h1 ⟨hc.Z_le_Q hyq, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun b hb => (Smith81.Z_central hc.hyp hyq (hc.le hb)).symm

end CFSG.RankThree.GF2n.Stroth80
