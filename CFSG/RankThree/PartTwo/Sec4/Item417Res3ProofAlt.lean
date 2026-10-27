module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofOutData
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofA6
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2
import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA7

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


namespace Res417Three

theorem pRank_le_two_of_not_dvd {X : Type*} [Group X] [Finite X] {p : ℕ}
    (h : ¬ p ^ 3 ∣ Nat.card X) : CFSG.pRank p X ≤ 2 := by
  refine csSup_le' ?_
  rintro r ⟨B, -, hr⟩
  by_contra hr1
  exact h ((Nat.pow_dvd_pow p (by omega : 3 ≤ r)).trans
    (hr ▸ Subgroup.card_subgroup_dvd_card B))

@[expose] def K417OutA8 : Prop :=
  Nonempty (alternatingGroup (Fin 8) ≃* projSL 4 (GaloisField 2 1)) ∧
    ∀ D : Subgroup (alternatingGroup (Fin 8)), CFSG.Assembly.IsElemAbelian 3 D →
      Nat.card D = 9 → Nonempty (autIn ⊤ D ≃* DihedralGroup 4)

@[expose] def K417OutA9 : Prop :=
  ∀ D : Subgroup (alternatingGroup (Fin 9)), IsDatum417 (alternatingGroup (Fin 9)) D →
    Nat.card D = 27 ∧ Nonempty (autIn ⊤ D ≃* Equiv.Perm (Fin 4))

end Res417Three

open Res417Three

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerOutConf417.not_isExtOf (h : IsInnerOutConf417 L A E c m) {Y : Type*} [Group Y]
    (hY : Subgroup.center Y = ⊥)
    (hext : IsExtOf (L ⧸ aschbacherSolvableCore 3 L) Y (Multiplicative (ZMod 3))) : False := by
  have hq := (CFSG.LocalCores.quasisimple_central_quotient h.2.2.1.1
    (aschbacherSolvableCore 3 L) (aschbacherSolvableCore_le_center h.2.2.1.1)).1
  have h3 := ((isTripleCover_iff_isExtOf hq hY).mpr hext).1
  rw [h.2.2.2.2.2.2.2.2.2.2.1, Subgroup.card_bot] at h3
  omega

theorem IsInnerOutConf417.theta_eq_bot_of_alt (h : IsInnerOutConf417 L A E c m) {n : ℕ}
    (hn : 5 ≤ n) (φ : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin n)) :
    aschbacherSolvableCore 3 L = ⊥ := by
  have : Group.IsPerfect L := h.2.2.1.1.1
  refine theta_eq_bot_of_two_three h.2.1 h.2.2.1 fun p hp hp3 => ?_
  exact CFSG.RankThree.PartOne.Mult.alternating_center_small_primes hn
    (h.centerEquiv.trans φ) hp hp3

noncomputable def IsInnerOutConf417.altEquiv (h : IsInnerOutConf417 L A E c m) {n : ℕ}
    (hn : 5 ≤ n) (φ : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin n)) :
    L ≃* alternatingGroup (Fin n) :=
  (Res417.thetaQuotEquivOfEqBot (h.theta_eq_bot_of_alt hn φ)).symm.trans φ

theorem IsInnerOutConf417.alt417_of_alt7 (h : IsInnerOutConf417 L A E c m)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) : Alt417 L A m := by
  set ψ := h.altEquiv (by norm_num) φ
  have hm3 : m = 3 := h.eq_three_of_pRank_le_two (h.centerEquiv.trans φ)
    (pRank_le_two_of_not_dvd fun h27 => by
      have h1 := h27.trans (card_alternatingGroup_dvd 7)
      revert h1
      decide)
  obtain ⟨-, hD, ⟨eA⟩⟩ := h.datum ψ
  rw [hm3] at hD
  obtain ⟨e7⟩ := Res423Two.nonempty_autIn_alt7 (MulEquiv.refl _) hD
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hm3, ⟨ψ⟩, ⟨eA.trans e7⟩⟩)))

theorem IsInnerOutConf417.alt417_of_alt8 (hA8 : K417OutA8) (h : IsInnerOutConf417 L A E c m)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 8)) : Alt417 L A m := by
  set ψ := h.altEquiv (by norm_num) φ
  have hm3 : m = 3 := h.eq_three_of_pRank_le_two (h.centerEquiv.trans φ)
    (pRank_le_two_of_not_dvd fun h27 => by
      have h1 := h27.trans (card_alternatingGroup_dvd 8)
      revert h1
      decide)
  obtain ⟨hdat, hD, ⟨eA⟩⟩ := h.datum ψ
  rw [hm3] at hD
  obtain ⟨⟨e48⟩, haut⟩ := hA8
  obtain ⟨eD⟩ := haut _ hdat.1 hD
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨hm3, Or.inr (Or.inr (Or.inl ⟨ψ.trans e48⟩)), ⟨eA.trans eD⟩⟩))))))))))

theorem IsInnerOutConf417.alt417_of_alt9 (hA9 : K417OutA9) (h : IsInnerOutConf417 L A E c m)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 9)) : Alt417 L A m := by
  set ψ := h.altEquiv (by norm_num) φ
  obtain ⟨hdat, hD, ⟨eA⟩⟩ := h.datum ψ
  obtain ⟨h27, ⟨eD⟩⟩ := hA9 _ hdat
  have hm4 : m = 4 := by
    rw [h27] at hD
    have hm := three_le_of_isQuad h.2.2.2.2.1
    have h1 : 3 ^ (m - 1) = 3 ^ 3 := by rw [← hD]; norm_num
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
    omega
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm4, ⟨ψ⟩, ⟨eA.trans eD⟩⟩))))

theorem item417OutAlt_of (hA8 : K417OutA8) (hA9 : K417OutA9) : Item417OutAlt := by
  intro G _ _ L A E c m hconf hL
  rcases hL with ⟨n, hn, ⟨φ⟩⟩ | hext | hext
  · rcases (show n ≤ 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 by omega) with h5 | rfl | rfl | rfl | rfl
    · exfalso
      refine hconf.false_of_pRank_le_one (hconf.centerEquiv.trans φ)
        (pRank_le_one_of_not_dvd fun h9 => ?_)
      have h1 := h9.trans ((card_alternatingGroup_dvd n).trans
        (Nat.factorial_dvd_factorial h5))
      revert h1
      decide
    · exact (hconf.false_of_noSix
        (noSix_alternatingGroup_six.of_mulEquiv (hconf.centerEquiv.trans φ))).elim
    · exact hconf.alt417_of_alt7 φ
    · exact hconf.alt417_of_alt8 hA8 φ
    · exact hconf.alt417_of_alt9 hA9 φ
  · exact (hconf.not_isExtOf (alternatingGroup.center_eq_bot (by simp)) hext).elim
  · exact (hconf.not_isExtOf (alternatingGroup.center_eq_bot (by simp)) hext).elim

end Certs

end CFSG.RankThree.PartTwo.Sec4
