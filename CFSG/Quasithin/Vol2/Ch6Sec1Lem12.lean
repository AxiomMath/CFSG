module

public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem10

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem centralizer_singleton_eq_ZS (h : Hyp611Nat G T M L V n) {b : G} (hb : b ∈ ch6S T L V)
    (hbV : b ∉ Subgroup.centralizer (V : Set G)) :
    V ⊓ Subgroup.centralizer ({b} : Set G) = ch6ZS T L V := by
  have hle : ch6ZS T L V ≤ V ⊓ Subgroup.centralizer ({b} : Set G) := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hb.2 z hz).symm⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_ZS]
  exact h.data.card_fixed_le_two_pow ⟨b, h.toHyp611.T_le_normalizer hb.1⟩
    (h.T_le_normalizer_L hb.1) hbV

theorem le_S_of_centralizer_eq (h : Hyp611Nat G T M L V n) {A : Subgroup G} (hAT : A ≤ T)
    (hC : V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) =
      V ⊓ Subgroup.centralizer (A : Set G)) :
    A ≤ ch6S T L V := by
  intro a ha
  refine ⟨hAT ha, ?_⟩
  by_contra haZ
  by_cases hBV : A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.centralizer (V : Set G)
  ·
    have hV : V ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
      rw [← hC]
      exact le_inf le_rfl fun v hv => Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp (hBV hb) v hv).symm
    apply haZ
    refine Subgroup.centralizer_le h.ZS_le (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hV hv).2 a ha).symm
  · obtain ⟨b, hbB, hbV⟩ := Set.not_subset.mp hBV
    have hbS : b ∈ ch6S T L V := ⟨hAT hbB.1, hbB.2⟩
    have h2 : ch6ZS T L V ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
      rw [← hC]
      exact fun z hz => ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun c hc =>
        (Subgroup.mem_centralizer_iff.mp hc.2 z hz).symm⟩
    apply haZ
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (Subgroup.mem_centralizer_iff.mp (h2 hz).2 a ha).symm

theorem le_S_of_le_conj (h : Hyp611Nat G T M L V n)
    (hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n) {g : G} {A : Subgroup G}
    (hAg : A ≤ conjSubgroup V g) (hAT : A ≤ T) (hw : mQuot (conjSubgroup V g) A + 2 ≤ n) :
    A ≤ ch6S T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.toHyp611.isElemAbelian
  have hAe : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
  have hAB : mQuot A (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ 1 := by
    have h1 := card_mul_relIndex_of_le
      (inf_le_left : A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ A)
    have h2 := h.card_le_two_mul_inf_ZS hAT hAe
    have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := Nat.card_pos
    have h3 : (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)).relIndex A ≤ 2 := by
      have : Nat.card ↥(A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) *
          (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)).relIndex A ≤
          Nat.card ↥(A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) * 2 := by
        rw [h1, mul_comm]
        exact h2
      exact Nat.le_of_mul_le_mul_left this hpos
    have h0 := relIndex_ne_zero' A (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
    unfold mQuot
    rcases (show (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)).relIndex A = 1 ∨
        (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)).relIndex A = 2 by omega) with hr | hr
    · rw [hr]
      simp
    · rw [hr, padicValNat_self]
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer
  have hAN : A ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) := le_inf hAg (hAT.trans hTN)
  have hBN : A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) := inf_le_left.trans hAN
  have hA7 := e3_7 hV hAN (by rw [hs hV]; omega)
  have hBadd : mQuot (conjSubgroup V g) (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) =
      mQuot A (A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) + mQuot (conjSubgroup V g) A :=
    mQuot_add inf_le_left hAg
  have hB7 := e3_7 hV hBN (by rw [hs hV, hBadd]; omega)
  exact h.le_S_of_centralizer_eq hAT (hB7.trans hA7.symm)

end Hyp611Nat

theorem stmt6_1_12 (h331 : Stmt3_3_1) (h6110 : Stmt6_1_10) : Stmt6_1_12 := by
  intro G _ _ T M L V n h
  have hV := h.toHyp611.isElemAbelian
  have hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n := fun hV =>
    ((h6110 G T M L V n h).2.1 hV).1
  have hkey : ∀ i : ℕ, i + 2 ≤ n → wClos V i T ≤ ch6S T L V := by
    intro i hi
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := hA
    exact h.le_S_of_le_conj hs hAg hAT (by rw [hm]; exact hi)
  refine ⟨?_, fun hn => ?_, hkey 0 (by have := h.two_le; omega)⟩
  ·
    obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
    obtain ⟨⟨-, -, huniq⟩, -, ⟨H, hH⟩, -⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
    have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
    rw [← hMeq] at hH
    have hTH : T ≤ H := hH.1.1
    have hSH : IsSylowIn 2 T H :=
      E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
        hTH le_top
    have h319 := e3_19 hV hSH (i := 0) (h.nParam_eq_one H hH)
      (by rw [hs hV]; have := h.two_le; omega)
    by_contra hcon
    push Not at hcon
    obtain ⟨hW, hC⟩ := hcon
    apply hH.2.1
    rw [← h319]
    exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hW)
  ·
    have hW1 := hkey 1 (by omega)
    refine le_inf (h.ZS_le.trans h.toHyp611.le_T) fun z hz => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hW1 hw).2 z hz).symm

end CFSG.Quasithin.H13
