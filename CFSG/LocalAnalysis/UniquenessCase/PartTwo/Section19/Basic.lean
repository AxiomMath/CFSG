module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inCalV0_of_hyp125 {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hne : V₀ ≠ ⊥) : InCalV0 D.M V₀ V := by
  rcases h.1 with ⟨-, hbot⟩ | h2
  · exact absurd hbot hne
  · exact h2.1

theorem IOf_le_M (D : Data G) (p : ℕ) {L : Subgroup G} (hL : L ≤ D.M) : IOf D p L ≤ D.M := by
  unfold IOf
  split_ifs with h
  · refine iSup_le fun K => iSup_le fun hK => ?_
    exact hK.1.1.le
  · refine iSup_le fun K => iSup_le fun hK => ?_
    obtain ⟨m, hm, rfl⟩ := hK
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact D.M.mul_mem (D.M.mul_mem hm (hL hy)) (D.M.inv_mem hm)

theorem A_le_M_of_ctx19_10 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r) : A ≤ D.M :=
  h.hA.trans (IOf_le_M D p (S17.calLp_subset_calC D p h.hyp.hL).1.le)

theorem isMulCommutative_of_isZModSq {X : Type} [Group X] {n : ℕ} (h : IsZModSq X n) :
    IsMulCommutative X := by
  obtain ⟨e⟩ := h
  refine ⟨⟨fun x y => ?_⟩⟩
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

theorem card_eq_of_isZModSq {A : Subgroup G} {n : ℕ} (hA : IsZModSq A n) :
    Nat.card A = (2 ^ n - 1) * (2 ^ n - 1) := by
  obtain ⟨e⟩ := hA
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1)) = (2 ^ n - 1) * (2 ^ n - 1)
  rw [Nat.card_prod, Nat.card_zmod]

theorem le_centralizer_of_isMulCommutative_of_le {A A₀ : Subgroup G}
    (hcomm : IsMulCommutative ↥A) (hA₀ : A₀ ≤ A) : A ≤ centralizer (A₀ : Set G) :=
  (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm).trans (Subgroup.centralizer_le hA₀)

theorem isTI_of_hyp123_of_ne_bot {M T V₀ V : Subgroup G} (h : Hyp123 M T V₀ V)
    (hne : V₀ ≠ ⊥) : CFSG.CGT.Timmesfeld75.IsTI V₀ := by
  rcases h with ⟨-, rfl⟩ | ⟨h0, -, -⟩
  · exact absurd rfl hne
  · exact h0.2.2.2.1

theorem isTI_of_hyp19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) : CFSG.CGT.Timmesfeld75.IsTI V₀ := by
  refine isTI_of_hyp123_of_ne_bot h.hyp125.1 ?_
  rintro rfl
  have hbig := h.big
  simp [mSub, CFSG.Quasithin.rk_bot] at hbig

theorem IOf_normal (D : Data G) (p : ℕ) {L : Subgroup G} (hL : L ∈ calC D.M) :
    ((IOf D p L).subgroupOf D.M).Normal := by
  have key : ∀ (S : Set (Subgroup G)),
      (∀ g ∈ D.M, ∀ K ∈ S, K.map (MulAut.conj g).toMonoidHom ∈ S) →
      D.M ≤ normalizer (⨆ K ∈ S, K : Subgroup G) := by
    intro S hS g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simp only [Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup_le fun K => iSup_le fun hK => ?_
      exact le_iSup₂ (f := fun K (_ : K ∈ S) => K) (K.map (MulAut.conj g).toMonoidHom)
        (hS g hg K hK)
    · refine iSup_le fun K => iSup_le fun hK => ?_
      have hmem : K.map (MulAut.conj g⁻¹).toMonoidHom ∈ S :=
        hS g⁻¹ (D.M.inv_mem hg) K hK
      have hcomp : (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
        ext x
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨z, hz, rfl⟩ := hy
          convert hz using 2
          group
        · intro hx
          refine ⟨MulAut.conj g⁻¹ x, ⟨x, hx, rfl⟩, ?_⟩
          simp only [MulAut.conj_apply]
          group
      rw [← hcomp]
      exact le_iSup₂ (f := fun K' (_ : K' ∈ S) => K'.map (MulAut.conj g).toMonoidHom) _ hmem
  have hIleM : IOf D p L ≤ D.M := IOf_le_M D p hL.1.le
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hIleM]
  by_cases hj : S17.jM D p = 4
  · have hIeq : IOf D p L = ⨆ K ∈ S17.calLp D p, K := by simp [IOf, hj]
    rw [hIeq]
    refine key (S17.calLp D p) fun g hg K hK => ?_
    have hgM : D.M.map (MulAut.conj g).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    refine ⟨UC6S846.calC_map D.M (MulAut.conj g) hgM hK.1, ?_⟩
    have hcard : Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card K :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact ⟨hK.2.1, hcard ▸ hK.2.2⟩
  · have hIeq : IOf D p L = conjClosure D.M L := by simp [IOf, hj]
    rw [hIeq]
    exact TwelveTwentyThree.le_normalizer_conjClosure D.M L

theorem le_normalizer_IOf (D : Data G) {p : ℕ} {L : Subgroup G} (hL : L ∈ calC D.M) :
    D.M ≤ normalizer (IOf D p L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (IOf_le_M D p hL.1.le)).mp
    (IOf_normal D p hL)

theorem evenRank_eq_three_of_ctx {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r) : evenRank G = 3 := by
  have hset := h.h1910
  unfold Setting1910 at hset
  exact hset.1

theorem odd_card_of_ctx19_10 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r) :
    Odd (Nat.card A) := by
  rw [card_eq_of_isZModSq h.hAcard]
  have hn0 : S17.nOf L ≠ 0 := by
    intro h0
    have hc := card_eq_of_isZModSq h.hAcard
    rw [h0] at hc
    norm_num at hc
    exact Nat.card_pos.ne' hc
  have hpow : Even (2 ^ S17.nOf L) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨2 ^ k, ?_⟩
    rw [hk, pow_succ]
    ring
  have hodd : Odd (2 ^ S17.nOf L - 1) :=
    Nat.Even.sub_odd (Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))) hpow odd_one
  exact hodd.mul hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
