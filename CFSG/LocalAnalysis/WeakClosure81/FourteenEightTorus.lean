module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightBender
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightLift
public import CFSG.LocalAnalysis.WeakClosure81.SixFourSz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GH74.Uniqueness.Bender
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem exists_isFixedPointFreeTorus_of_benderType
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {K : Subgroup G}
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l) {r i : ℕ}
    (hB : BenderType (↥(LOf V g) ⧸ K.subgroupOf (LOf V g)) r i 1)
    (hcard : Nat.card ((V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) = 2 ^ r) :
    ∃ Y : Subgroup G, IsFixedPointFreeTorus M V g Y := by
  have hsup := map_subgroupOf_sup_eq_top (K := K) h
  rw [map_subgroupOf_conjSubgroup_eq hlL hlV] at hsup
  obtain ⟨T, hT⟩ := exists_torusData_of_benderType hB (isElemAbelian_map_subgroupOf (K := K) h)
    hcard hsup
  exact exists_isFixedPointFreeTorus_of_torusData h hgen hKset hlL hlV hT

theorem exists_isFixedPointFreeTorus
    (h : Hyp64 n M V₀ V g) : ∃ Y : Subgroup G, IsFixedPointFreeTorus M V g Y := by
  have hgen := genHyp_of_hyp64 h
  obtain ⟨-, K, hKnorm, hKset, hQuot, ⟨l, hlL, hlV⟩, -, -, -⟩ := h.inCalOStar
  haveI : (K.subgroupOf (LOf V g)).Normal := hKnorm
  have hrel := card_map_subgroupOf_eq_relIndex (K := K) h hKset
  rcases hQuot.1 with ⟨r, hL2⟩ | ⟨r, hSz⟩ | hdi
  · have hcard := card_image_eq_two_pow h hKset hQuot.2 hL2
    rcases Nat.lt_or_ge r 2 with hr | hr
    · have hr1 : r = 1 := by have := one_le_of_isL2 hL2; omega
      subst hr1
      exact ⟨⊥, isFixedPointFreeTorus_bot (by rw [← hrel, hcard, pow_one])⟩
    · obtain ⟨e⟩ := nonempty_psl_equiv_of_isL2 (one_le_of_isL2 hL2) hL2
      exact exists_isFixedPointFreeTorus_of_benderType h hgen hKset hlL hlV
        (.linear r hr e) hcard
  · have hcard := card_image_eq_two_pow_of_sz h hKset hQuot.2 hSz
    obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hSz
    exact exists_isFixedPointFreeTorus_of_benderType h hgen hKset hlL hlV
      (.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))) hcard
  · exact ⟨⊥, isFixedPointFreeTorus_bot (relIndex_two_of_dihedral h hKset hdi)⟩

theorem hyp64_of_weakClosureSetting {D : Data G} (h : WeakClosureSetting D V₀ V)
    (hO : InCalOStar n D.M V₀ V g) : Hyp64 n D.M V₀ V g :=
  ⟨h.pair.elemAbelian, h.pair.le, h.normalizer_eq, h.pair.le_normalizer₀,
    fun h0 => (h.ti₀ h0).1, h.normalizer₀, hO⟩

theorem w3Lem148Torus_holds :
    W3Lem148Torus G := by
  intro D V₀ V h _ g hO
  obtain ⟨Y, hY⟩ := exists_isFixedPointFreeTorus (hyp64_of_weakClosureSetting h hO)
  exact ⟨Y, hY.1⟩

end CFSG.LocalAnalysis.WeakClosure81
