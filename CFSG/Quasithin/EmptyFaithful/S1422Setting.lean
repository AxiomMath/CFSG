module

public import CFSG.Quasithin.EmptyFaithful.S1422Local
public import CFSG.Quasithin.EmptyFaithful.S142Basic
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

structure Lemma1422Data {G : Type*} [Group G] (T M Y : Subgroup G) : Prop where
  le : Y ≤ M
  normalizes : M ≤ Subgroup.normalizer (Y : Set G)
  quot : Nonempty (OTwoQuot (Y ⊔ T) ≃* Equiv.Perm (Fin 3))
  unique : IsUniqueM (Y ⊔ T) M
  centralizes : T ⊓ Subgroup.centralizer (Y : Set G) = ⊥
  generate : M ≤ (Y ⊔ T) ⊔ (M ⊓ Subgroup.centralizer (VZ T M : Set G))

@[expose] def Stage1422Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M →
    ∃ Y : Subgroup G, Lemma1422Data T M Y

@[expose] def Stage1426VleQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M →
    ∀ H : Subgroup G, IsHStar T M H → VZ T M ≤ pCoreOf 2 H

structure Setting1422 {G : Type} [Group G] [Finite G] (T M Y H : Subgroup G) : Prop where
  hyp : Hyp1421 G T M
  star : IsHStar T M H
  data : Lemma1422Data T M Y
  small : SmallQuot H

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem exists_sylow (S : Setting1422 T M Y H) : ∃ P : Sylow 2 G, (P : Subgroup G) = T :=
  S.hyp.toQTFE14.exists_sylow

theorem T_le_H (S : Setting1422 T M Y H) : T ≤ H := S.star.1.1

omit [Finite G] in
theorem T_le_YT : T ≤ Y ⊔ T := le_sup_right

theorem T_le_M (S : Setting1422 T M Y H) : T ≤ M := S.hyp.m_max.1.2

theorem YT_le_M (S : Setting1422 T M Y H) : Y ⊔ T ≤ M := sup_le S.data.le S.T_le_M

theorem not_H_le_M (S : Setting1422 T M Y H) : ¬ H ≤ M := S.star.2.1

theorem not_H_le_YT (S : Setting1422 T M Y H) : ¬ H ≤ Y ⊔ T := fun h =>
  S.not_H_le_M (h.trans S.YT_le_M)

theorem isSylow_H (S : Setting1422 T M Y H) : IsSylowTwoOf T H := by
  obtain ⟨P, hP⟩ := S.exists_sylow
  subst hP
  exact isSylowTwoOf_of_sylow P S.T_le_H

theorem isSylow_YT (S : Setting1422 T M Y H) : IsSylowTwoOf T (Y ⊔ T) := by
  obtain ⟨P, hP⟩ := S.exists_sylow
  subst hP
  exact isSylowTwoOf_of_sylow P T_le_YT

theorem charTwo_H (S : Setting1422 T M Y H) : CharTwo H := by
  obtain ⟨P, hP⟩ := S.exists_sylow
  exact charTwo_of_le S.hyp.qtke.2.1 P (hP ▸ S.T_le_H) le_rfl
    (hP ▸ S.star.1 : InH (P : Subgroup G) H)

theorem charTwo_YT (S : Setting1422 T M Y H) : CharTwo (Y ⊔ T) := by
  obtain ⟨P, hP⟩ := S.exists_sylow
  have hMH : InH (P : Subgroup G) M := hP ▸ inH_of_inM S.hyp.m_max.1
  exact charTwo_of_le S.hyp.qtke.2.1 P (hP ▸ T_le_YT) (hP ▸ S.YT_le_M) hMH

theorem H_le_centralizer (S : Setting1422 T M Y H) :
    H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  (S.hyp.isUniqueM_centralizer S.star.1 S.not_H_le_M).1.2

theorem center_YT (S : Setting1422 T M Y H) :
    ∀ x ∈ Y ⊔ T, (∀ y ∈ Y ⊔ T, x * y = y * x) → x = 1 := by
  intro x hx hc
  have hO : pCoreOf 2 (Y ⊔ T) ≤ T := isSylowTwoOf_pCoreOf_le S.isSylow_YT
  have hOle : pCoreOf 2 (Y ⊔ T) ≤ Y ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 (Y ⊔ T) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc y (hOle hy)).symm
  have hxO : x ∈ pCoreOf 2 (Y ⊔ T) := S.charTwo_YT ⟨hx, hxC⟩
  have hxY : x ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc y ((le_sup_left : Y ≤ Y ⊔ T) hy)).symm
  have : x ∈ T ⊓ Subgroup.centralizer (Y : Set G) := ⟨hO hxO, hxY⟩
  rw [S.data.centralizes, Subgroup.mem_bot] at this
  exact this

theorem exists_central_H (S : Setting1422 T M Y H) :
    ∃ x ∈ H, x ≠ 1 ∧ ∀ y ∈ H, x * y = y * x := by
  have hne := S.hyp.toQTFE14.omegaOneCenter_ne_bot
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have haT : (a : G) ∈ T := (quasithinOmegaOneCenter_le_center T a.2).1
  refine ⟨a, S.T_le_H haT, fun h => ha (Subtype.ext h), fun y hy => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (S.H_le_centralizer hy) a a.2)

theorem card_quot_YT (S : Setting1422 T M Y H) :
    Nat.card (OTwoQuot (Y ⊔ T)) = 2 ^ 1 * 3 := by
  obtain ⟨e⟩ := S.data.quot
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem inf_normalizer_YT (S : Setting1422 T M Y H) :
    (Y ⊔ T) ⊓ Subgroup.normalizer (T : Set G) = T :=
  inf_normalizer_eq_of_card_quot S.isSylow_YT le_rfl (by norm_num) (by decide) S.card_quot_YT

theorem borelOf_YT (S : Setting1422 T M Y H) : borelOf (Y ⊔ T) T = T := by
  unfold borelOf
  rw [inf_eq_left.mpr T_le_YT]
  exact S.inf_normalizer_YT

variable (hSz : Nat.card ↥(Sz 0) = 20)
include hSz

theorem exists_card_H (S : Setting1422 T M Y H) :
    ∃ k r : ℕ, 1 ≤ k ∧ r.Prime ∧ Odd r ∧ Nat.card (OTwoQuot H) = 2 ^ k * r :=
  S.small.exists_card hSz

theorem inf_normalizer_H (S : Setting1422 T M Y H) : H ⊓ Subgroup.normalizer (T : Set G) = T := by
  obtain ⟨k, r, hk, hr, hr2, hcard⟩ := S.exists_card_H hSz
  exact inf_normalizer_eq_of_card_quot S.isSylow_H hk hr hr2 hcard

theorem index_H (S : Setting1422 T M Y H) : ∃ r : ℕ, r.Prime ∧ (T.subgroupOf H).index = r := by
  obtain ⟨k, r, hk, hr, hr2, hcard⟩ := S.exists_card_H hSz
  exact ⟨r, hr, index_sylow_eq_of_card_quot S.isSylow_H hr2 hcard⟩

theorem H_inf_M (S : Setting1422 T M Y H) : H ⊓ M = T := by
  obtain ⟨r, hr, hidx⟩ := S.index_H hSz
  have hTle : T ≤ H ⊓ M := le_inf S.T_le_H S.T_le_M
  rcases eq_or_eq_of_le_of_index_prime hTle inf_le_left hr hidx with h | h
  · exact h
  · exact absurd (h ▸ inf_le_right) S.not_H_le_M

theorem H_inf_YT (S : Setting1422 T M Y H) : H ⊓ (Y ⊔ T) = T := by
  obtain ⟨r, hr, hidx⟩ := S.index_H hSz
  have hTle : T ≤ H ⊓ (Y ⊔ T) := le_inf S.T_le_H T_le_YT
  rcases eq_or_eq_of_le_of_index_prime hTle inf_le_left hr hidx with h | h
  · exact h
  · exact absurd (h ▸ inf_le_right) S.not_H_le_YT

theorem borelOf_H (S : Setting1422 T M Y H) : borelOf H T = T := by
  unfold borelOf
  rw [inf_eq_left.mpr S.T_le_H]
  exact S.inf_normalizer_H hSz

theorem bigB_eq (S : Setting1422 T M Y H) : bigB H (Y ⊔ T) T = T := by
  unfold bigB
  rw [S.borelOf_H hSz, S.borelOf_YT]
  simp

end Setting1422

section Aux

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem SmallQuot.isRankOneListed {H : Subgroup G} (h : SmallQuot H) :
    IsRankOneListed (oTwoQuot ↥H) := by
  obtain h | h | h := h
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨0, ⟨e⟩⟩)
  · obtain ⟨e⟩ := h
    exact isRankOneListed_perm_three e

theorem isQuasithinSub_of_qtke (hK : quasithinIsQTKECat G) (X : Subgroup G) :
    IsQuasithinSub X := by
  intro p hp hp2 R _ hR1 hR2
  have hloc : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hR1, hR2, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
    (pRank_le_two_of_isTwoLocal hK hloc hp hp2)

end Aux

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}
variable (hSz : Nat.card ↥(Sz 0) = 20)
include hSz

theorem hyp111 (S : Setting1422 T M Y H) : Hyp111 H (Y ⊔ T) T := by
  obtain ⟨P, hP⟩ := S.exists_sylow
  have hEven : quasithinEvenCharacteristic G := S.hyp.qtke.2.1
  have hHc : CharTwo H := by
    have := charTwo_of_le hEven P (hP ▸ S.T_le_H) le_rfl (hP ▸ S.star.1 : InH (P : Subgroup G) H)
    exact this
  have hYTc : CharTwo (Y ⊔ T) := by
    have hMH : InH (P : Subgroup G) M := hP ▸ inH_of_inM S.hyp.m_max.1
    exact charTwo_of_le hEven P (hP ▸ T_le_YT) (hP ▸ S.YT_le_M) hMH
  have hTH : T ≤ Subgroup.normalizer (H : Set G) := S.T_le_H.trans Subgroup.le_normalizer
  have hTY : T ≤ Subgroup.normalizer ((Y ⊔ T : Subgroup G) : Set G) :=
    T_le_YT.trans Subgroup.le_normalizer
  refine ⟨⟨inferInstance, S.hyp.sylow.1, hTH, ?_, S.small.isRankOneListed, ?_, ?_⟩,
    ⟨inferInstance, S.hyp.sylow.1, hTY, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [inf_eq_left.mpr S.T_le_H]; exact S.isSylow_H
  · rw [S.borelOf_YT]; exact hTH
  · rw [S.borelOf_YT, sup_of_le_left S.T_le_H, sup_of_le_left S.T_le_H]; exact hHc
  · rw [inf_eq_left.mpr T_le_YT]; exact S.isSylow_YT
  · obtain ⟨e⟩ := S.data.quot
    exact isRankOneListed_perm_three e
  · rw [S.borelOf_H hSz]; exact hTY
  · rw [S.borelOf_H hSz, sup_of_le_left (T_le_YT (T := T) (Y := Y)),
      sup_of_le_left (T_le_YT (T := T) (Y := Y))]; exact hYTc
  ·
    by_contra hne
    have hQ2 : IsPGroup 2 (pCoreOf 2 (H ⊔ (Y ⊔ T) ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (H ⊔ (Y ⊔ T) ⊔ T) : Set G)) :=
      ⟨_, hne, hQ2, rfl⟩
    obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
    have hG0 : H ⊔ (Y ⊔ T) ⊔ T ≤ K :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hle
    have hKM : K = M := S.data.unique.2 K ⟨hK, le_sup_right.trans (le_sup_left.trans hG0)⟩
    exact S.not_H_le_M (hKM ▸ (le_sup_left.trans (le_sup_left.trans hG0)))

theorem normal_clause (S : Setting1422 T M Y H) :
    (T.subgroupOf (T ⊔ borelOf H T)).Normal := by
  rw [S.borelOf_H hSz, sup_idem, Subgroup.subgroupOf_self]
  exact Subgroup.normal_top

theorem f112_list (hF : F112LegacyPrintedError) (S : Setting1422 T M Y H) :
    F112ListBare H (Y ⊔ T) T ∨ F112ListBare (Y ⊔ T) H T := by
  obtain ⟨L1', L2', hL, -, hList, -⟩ := hF G H (Y ⊔ T) T (S.hyp111 hSz)
    (isQuasithinSub_of_qtke S.hyp.qtke _) (Or.inl (S.normal_clause hSz))
  rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hList
  · exact Or.inr hList

end Setting1422

end CFSG.Quasithin
