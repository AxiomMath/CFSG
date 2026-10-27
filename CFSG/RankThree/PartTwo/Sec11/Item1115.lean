module

public import CFSG.RankThree.PartTwo.Sec11.RFacts
public import CFSG.RankThree.PartTwo.Sec11.Item1113
public import CFSG.RankThree.PartTwo.Sec11.Final

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem Sec11Data.R_le_normalizer_A (h113 : Item113) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    R ≤ Subgroup.normalizer (A : Set G) :=
  le_normalizer_of_eq_closure (h113 G A c L a R Y h.toSec11Std).1

theorem Sec11Data.sec11P_le_normalizer_A (h113 : Item113) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) :
    sec11P R g ≤ Subgroup.normalizer (A : Set G) :=
  sup_le (h.R_le_normalizer_A h113) (Subgroup.zpowers_le.mpr h.g_mem.2)

theorem Sec11Data.inf_normalizer_L (h45 : Sec4.Item4_5) (h113 : Item113) {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) :
    sec11P R g ⊓ Subgroup.normalizer (L : Set G) = R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 h.ne_one
  have hRc := le_centralizer_of_le_normalizer_zpowers hc3' h.isSylowOf.isPGroup h.isSylowOf.le
  have hRL := le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 h.ne_one
    h.isSylowOf.isPGroup hRc L h.mem_thetaComponentsAt
  have hPA := h.sec11P_le_normalizer_A h113
  have hcC := c_mem_thetaQuotCentralizer h.mem_thetaComponentsAt
  have hPH : sec11P R g ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rintro y ⟨hyP, hyN⟩
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    have h1 : y * c * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hPA hyP) c).mp h.mem_A
    have h2 : y * c * y⁻¹ ∈ Sec4.thetaQuotCentralizer L :=
      (Subgroup.mem_normalizer_iff.mp
        (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L hyN) c).mp hcC
    have h3 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer h1 h2
    rw [h.sectionCentralizer_eq] at h3
    exact h3
  apply le_antisymm
  · exact (h.isSylowOf.eq_of_le (le_inf le_sup_left hRL) hPH
      (h.isPGroup_sec11P.to_le inf_le_left)).le
  · exact le_inf le_sup_left hRL

theorem normalizer_le_normalizer_innerPreimage (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (innerPreimage L : Set G) := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨hzN, hzI⟩ := mem_innerPreimage_iff.mp hz
  have hm : n * z * n⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hzN) (Subgroup.inv_mem _ hn)
  refine mem_innerPreimage_iff.mpr ⟨hm, ?_⟩
  have e : (⟨n * z * n⁻¹, hm⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨n, hn⟩ * ⟨z, hzN⟩ * (⟨n, hn⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
  change (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) _ ∈ _
  rw [e, map_mul, map_mul, map_inv]
  exact (KFacts.isInnerAut_conj_iff _ _).mpr hzI

theorem Sec11Data.R_le_normalizer_V (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) :
    R ≤ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 h.ne_one
  have hRc := le_centralizer_of_le_normalizer_zpowers hc3' h.isSylowOf.isPGroup h.isSylowOf.le
  have hRL := le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 h.ne_one
    h.isSylowOf.isPGroup hRc L h.mem_thetaComponentsAt
  rw [← h.inf_innerPreimage_eq]
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hI := normalizer_le_normalizer_innerPreimage L (hRL hy)
  constructor
  · rintro ⟨hz1, hz2⟩
    exact ⟨R.mul_mem (R.mul_mem hy hz1) (R.inv_mem hy),
      (Subgroup.mem_normalizer_iff.mp hI z).mp hz2⟩
  · rintro ⟨hz1, hz2⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hI z).mpr hz2⟩
    have e : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [e]
    exact R.mul_mem (R.mul_mem (R.inv_mem hy) hz1) hy

theorem Sec11Std.a_not_mem_innerPreimage {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) : a ∉ innerPreimage L := by
  intro ha
  obtain ⟨haN, hin⟩ := mem_innerPreimage_iff.mp ha
  exact h.toHyp81.not_isInnerAut_induced hin

theorem Sec11Data.r_not_mem_innerPreimage {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    r ∉ innerPreimage L := by
  intro hr
  apply h.toSec11Std.a_not_mem_innerPreimage
  have hsR : s ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  have hrR : r ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  have hs : s ∈ innerPreimage L := by
    have := (h.inf_innerPreimage_eq).ge (Subgroup.subset_closure (by simp) : s ∈ _)
    exact this.2
  have hle : Subgroup.closure ({r, s} : Set G) ≤ innerPreimage L := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [hr, hs]
  exact hle h.a_mem_closure

theorem Sec11Data.r_not_mem_V {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    r ∉ Subgroup.closure ({s, x} : Set G) := by
  rw [← h.inf_innerPreimage_eq]
  exact fun hr => h.r_not_mem_innerPreimage hr.2

theorem Sec11Data.a_not_mem_V {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    a ∉ Subgroup.closure ({s, x} : Set G) := by
  rw [← h.inf_innerPreimage_eq]
  exact fun ha => h.toSec11Std.a_not_mem_innerPreimage ha.2

theorem Sec11Data.normalizer_P_le_normalizer_V (h45 : Sec4.Item4_5) (h113 : Item113)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  rintro n ⟨hnH, hnP⟩
  have hnL := h.toSec11Std.normalizer_le_normalizer_L h45 hnH
  have hnI := normalizer_le_normalizer_innerPreimage L hnL
  have hPL := h.inf_normalizer_L h45 h113
  rw [← h.inf_innerPreimage_eq, ← hPL]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hnN : n ∈ Subgroup.normalizer
      ((Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) := Subgroup.le_normalizer hnL
  constructor
  · rintro ⟨⟨hz1, hz2⟩, hz3⟩
    exact ⟨⟨(Subgroup.mem_normalizer_iff.mp hnP z).mp hz1,
      (Subgroup.mem_normalizer_iff.mp hnN z).mp hz2⟩,
      (Subgroup.mem_normalizer_iff.mp hnI z).mp hz3⟩
  · rintro ⟨⟨hz1, hz2⟩, hz3⟩
    exact ⟨⟨(Subgroup.mem_normalizer_iff.mp hnP z).mpr hz1,
      (Subgroup.mem_normalizer_iff.mp hnN z).mpr hz2⟩,
      (Subgroup.mem_normalizer_iff.mp hnI z).mpr hz3⟩

theorem Sec11Data.commutator_mem_V (h45 : Sec4.Item4_5) (h113 : Item113)
    (hOA : OutAbelian1016) {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) {y : G} (hy : y ∈ R) :
    ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
      n * y * n⁻¹ * y⁻¹ ∈ Subgroup.closure {s, x} := by
  rintro n ⟨hnH, hnP⟩
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 h.ne_one
  have hRc := le_centralizer_of_le_normalizer_zpowers hc3' h.isSylowOf.isPGroup h.isSylowOf.le
  have hRL := le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 h.ne_one
    h.isSylowOf.isPGroup hRc L h.mem_thetaComponentsAt
  have hnL := h.toSec11Std.normalizer_le_normalizer_L h45 hnH
  have hI := commutator_mem_innerPreimage hOA h.isList1016 hnL (hRL hy)
  have hyP : y ∈ sec11P R g := le_sup_left (a := R) hy
  have hP : n * y * n⁻¹ * y⁻¹ ∈ sec11P R g :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hnP y).mp hyP) (Subgroup.inv_mem _ hyP)
  have hN : n * y * n⁻¹ * y⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnL (hRL hy))
      (Subgroup.inv_mem _ hnL)) (Subgroup.inv_mem _ (hRL hy))
  have hR : n * y * n⁻¹ * y⁻¹ ∈ R := by
    rw [← h.inf_normalizer_L h45 h113]
    exact ⟨hP, hN⟩
  rw [← h.inf_innerPreimage_eq]
  exact ⟨hR, hI⟩

end CFSG.RankThree.PartTwo.Sec11
