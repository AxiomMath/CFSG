module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPairs
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem A01_le_L : t.d.A 0 ⊔ t.d.A 1 ≤ c.L := by
  rw [← t.hdL]
  exact (show t.d.A 0 ⊔ t.d.A 1 ≤ t.d.AA by rw [t.d.AA_def]; exact le_sup_left).trans
    t.d.AA_le_L

private theorem A01_le_M : t.d.A 0 ⊔ t.d.A 1 ≤ c.S.M := t.A01_le_L.trans c.hyp81.1

@[expose] noncomputable def CQL : Subgroup G := t.d.N ⊓ Subgroup.centralizer (c.L : Set G)

private theorem CQL_def : t.CQL = t.d.N ⊓ Subgroup.centralizer (c.L : Set G) := rfl

private theorem CQL_isPGroup : IsPGroup 2 ↥t.CQL :=
  (SylowThreeData.N_isPGroup t.d).to_le inf_le_left

private theorem map_conj_CQL (m : G) (hm : m ∈ c.S.M) :
    t.CQL.map (MulAut.conj m).toMonoidHom = t.CQL := by
  have hN : t.d.N.map (MulAut.conj m).toMonoidHom = t.d.N := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M hm)
  have hL : (Subgroup.centralizer (c.L : Set G)).map (MulAut.conj m).toMonoidHom =
      Subgroup.centralizer (c.L : Set G) := by
    have hmap : c.L.map (MulAut.conj m).toMonoidHom = c.L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.le_normalizer_L hm)
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_mulEquiv, hmap]
  rw [t.CQL_def, Subgroup.map_inf_eq _ _ _ (MulAut.conj m).injective, hN, hL]

private theorem M_le_normalizer_CQL : c.S.M ≤ Subgroup.normalizer (t.CQL : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact t.map_conj_CQL m hm

theorem le_M_of_isTwoLocal {p : ℕ} (hN : t.PairNormalizerLe p)
    {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H)
    (hB : t.d.A 0 ⊔ t.d.A 1 ≤ H) : H ≤ c.S.M := by
  have hB3 : IsPGroup 3 ↥(t.d.A 0 ⊔ t.d.A 1) :=
    IsPGroup.to_le t.d.hS.isPGroup (sup_le (t.d.A_le_S 0) (t.d.A_le_S 1))
  have hBrank : 2 ≤ CFSG.Open.pRank 3 (t.d.A 0 ⊔ t.d.A 1) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl (t.d.isElemAbelian_A_sup_A 0 1)
      (t.d.card_A_sup_A (by decide))
  have hΓ : CFSG.Open.rankThreeGamma 1 3 (t.d.A 0 ⊔ t.d.A 1) ≤ c.S.M :=
    sSup_le fun N hNmem => by
      obtain ⟨Q, hQ, hk, rfl⟩ := hNmem
      refine hN.normalizer_le (by decide) hQ ?_
      intro hbot
      have h3 : 3 ∣ Nat.card Q := CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three hk
      rw [hbot, Subgroup.card_bot] at h3
      omega
  exact c.theoremC 3 Nat.prime_three (by norm_num) (t.d.A 0 ⊔ t.d.A 1) t.A01_le_M hB3 hBrank hΓ
    H hH hB

theorem isTI_CQL {p : ℕ} (hN : t.PairNormalizerLe p) :
    CFSG.CGT.Timmesfeld75.IsTI t.CQL := by
  intro g
  by_cases hbot : t.CQL ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hx1G : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨hxCQL, hxCQLg⟩ := Subgroup.mem_inf.mp x.2
  obtain ⟨hxN, hxL⟩ := Subgroup.mem_inf.mp hxCQL
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers (x : G)) :=
    (SylowThreeData.N_isPGroup t.d).to_le (Subgroup.zpowers_le.mpr hxN)
  have hxne : Subgroup.zpowers (x : G) ≠ ⊥ := by
    intro h
    have hxmem : (x : G) ∈ Subgroup.zpowers (x : G) := Subgroup.mem_zpowers _
    rw [h] at hxmem
    exact hx1G (Subgroup.mem_bot.mp hxmem)
  have hH : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G)) :=
    ⟨Subgroup.zpowers (x : G), hxne, hx2, rfl⟩
  have hB_le_H : t.d.A 0 ⊔ t.d.A 1 ≤
      Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G) := by
    intro b hb
    have hconj : b * (x : G) * b⁻¹ = (x : G) := by
      rw [Subgroup.mem_centralizer_iff.mp hxL b (t.A01_le_L hb), mul_assoc, mul_inv_cancel,
        mul_one]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show Subgroup.zpowers (b * (x : G) * b⁻¹) = Subgroup.zpowers (x : G)
    rw [hconj]
  have hBconj_le_H : CFSG.CGT.Timmesfeld75.conjSubgroup g (t.d.A 0 ⊔ t.d.A 1) ≤
      Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G) := by
    intro y hy
    have hy' : y ∈ (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom := hy
    have hyL : y ∈ c.L.map (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono t.A01_le_L hy'
    have hxLg : (x : G) ∈ Subgroup.centralizer
        ((c.L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      rw [← CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_mulEquiv]
      exact Subgroup.map_mono inf_le_right hxCQLg
    have hconj : y * (x : G) * y⁻¹ = (x : G) := by
      rw [Subgroup.mem_centralizer_iff.mp hxLg y hyL, mul_assoc, mul_inv_cancel, mul_one]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show Subgroup.zpowers (y * (x : G) * y⁻¹) = Subgroup.zpowers (x : G)
    rw [hconj]
  have hHleM : Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G) ≤ c.S.M :=
    t.le_M_of_isTwoLocal hN hH hB_le_H
  have hBgM : CFSG.CGT.Timmesfeld75.conjSubgroup g (t.d.A 0 ⊔ t.d.A 1) ≤ c.S.M :=
    hBconj_le_H.trans hHleM
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext z
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hB_le_Mg : t.d.A 0 ⊔ t.d.A 1 ≤ c.S.M.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hBgM
    rwa [CFSG.CGT.Timmesfeld75.conjSubgroup, Subgroup.map_map, hcomp, Subgroup.map_id] at h1
  have hMg2 : CFSG.Open.IsTwoLocal (c.S.M.map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.isTwoLocal_conj c.S.maxLocal.1 g
  have hMgle : c.S.M.map (MulAut.conj g⁻¹).toMonoidHom ≤ c.S.M :=
    t.le_M_of_isTwoLocal hN hMg2 hB_le_Mg
  have hcomp' : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext z
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hM_le_Mg : c.S.M ≤ c.S.M.map (MulAut.conj g).toMonoidHom := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hMgle
    rwa [Subgroup.map_map, hcomp', Subgroup.map_id] at h1
  have hMeq : c.S.M.map (MulAut.conj g).toMonoidHom = c.S.M :=
    (Subgroup.eq_of_le_of_card_ge hM_le_Mg
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])).symm
  have hgM : g ∈ c.S.M := by
    have hg : g ∈ Subgroup.normalizer (c.S.M : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hMeq
    rwa [CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_eq_of_isMaxTwoLocal c.S.maxLocal] at hg
  have hCQLeq : CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL = t.CQL := t.map_conj_CQL g hgM
  rw [hCQLeq]
  exact inf_idem t.CQL

theorem normalizer_CQL {p : ℕ} (hN : t.PairNormalizerLe p)
    (hne : t.CQL ≠ ⊥) : Subgroup.normalizer (t.CQL : Set G) = c.S.M := by
  refine le_antisymm ?_ t.M_le_normalizer_CQL
  have hH : CFSG.Open.IsTwoLocal (Subgroup.normalizer (t.CQL : Set G)) :=
    ⟨t.CQL, hne, t.CQL_isPGroup, rfl⟩
  exact t.le_M_of_isTwoLocal hN hH (t.A01_le_M.trans t.M_le_normalizer_CQL)

theorem isTI_of_le_CQL {p : ℕ} (hN : t.PairNormalizerLe p)
    {V : Subgroup G} (hV : V ≤ t.CQL)
    (hVM : c.S.M ≤ Subgroup.normalizer (V : Set G)) : CFSG.CGT.Timmesfeld75.IsTI V := by
  intro g
  by_cases hbot : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  have hCQLne : t.CQL ≠ ⊥ := by
    intro h
    apply hbot
    have hVbot : V = ⊥ := le_bot_iff.mp (hV.trans (le_of_eq h))
    simp [hVbot]
  have hne : t.CQL ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL ≠ ⊥ := by
    intro h
    apply hbot
    refine le_antisymm ?_ bot_le
    rw [← h]
    exact inf_le_inf hV (Subgroup.map_mono hV)
  have hgM : g ∈ c.S.M := by
    rcases t.isTI_CQL hN g with h | h
    · exact absurd h hne
    · have hle : t.CQL ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL := by
        calc t.CQL = t.CQL ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL := h.symm
          _ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL := inf_le_right
      have heq : CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL = t.CQL :=
        (Subgroup.eq_of_le_of_card_ge hle (by
          rw [show CFSG.CGT.Timmesfeld75.conjSubgroup g t.CQL
              = t.CQL.map (MulAut.conj g).toMonoidHom from rfl,
            Subgroup.card_map_of_injective (MulAut.conj g).injective])).symm
      have hmem : g ∈ Subgroup.normalizer (t.CQL : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        exact heq
      rwa [t.normalizer_CQL hN hCQLne] at hmem
  have hVg : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVM hgM)
  rw [hVg]
  exact inf_idem V

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
