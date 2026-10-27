module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsGrp
public import CFSG.Quasithin.EmptyFaithful.S146Six
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Cmp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47HvA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_not_le_pCoreOf {D : Data G} {V₀ V : Subgroup G} (hV : InCalV D.M V) {g z : G}
    (hO : InCalOStar 1 D.M V₀ V g) (hz : z ∈ V ⊓ conjSubgroup V g) :
    ¬ V ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
  intro hVQ
  obtain ⟨hInO, K, hKn, hKset, hQ, ⟨l, hlL, hVl⟩, -, -, -⟩ := hO
  haveI : (K.subgroupOf (V ⊔ conjSubgroup V g)).Normal := hKn
  let S : Type := ↥(V ⊔ conjSubgroup V g) ⧸ K.subgroupOf (V ⊔ conjSubgroup V g)
  have hVH : V ≤ centralizer ({z} : Set G) := by
    haveI : IsMulCommutative ↥V := hV.2.2.2.1
    intro v hv
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    simpa using congrArg Subtype.val (mul_comm' (⟨z, hz.1⟩ : V) ⟨v, hv⟩)
  have hVgH : conjSubgroup V g ≤ centralizer ({z} : Set G) := by
    have hVg2 : IsElemAbelian 2 (conjSubgroup V g) :=
      CFSG.LocalAnalysis.WeakClosure81.isElemAbelian_conjSubgroup' hV.2.2.2 g
    haveI : IsMulCommutative ↥(conjSubgroup V g) := hVg2.1
    intro v hv
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    simpa using congrArg Subtype.val
      (mul_comm' (⟨z, hz.2⟩ : conjSubgroup V g) ⟨v, hv⟩)
  have hLH : V ⊔ conjSubgroup V g ≤ centralizer ({z} : Set G) := sup_le hVH hVgH
  have hlH : l ∈ centralizer ({z} : Set G) := hLH hlL
  have hVgQ : conjSubgroup V g ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
    rw [hVl]
    calc conjSubgroup V l
        ≤ conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) l :=
          E3.conjSubgroup_mono_left l hVQ
      _ = pCoreOf 2 (centralizer ({z} : Set G)) :=
          s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hlH
  have hLQ : V ⊔ conjSubgroup V g ≤ pCoreOf 2 (centralizer ({z} : Set G)) :=
    sup_le hVQ hVgQ
  have hPL : IsPGroup 2 ↥(V ⊔ conjSubgroup V g) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (centralizer ({z} : Set G))).to_le hLQ
  have hPLq : IsPGroup 2 S := hPL.to_quotient (K.subgroupOf (V ⊔ conjSubgroup V g))
  rcases hQ.1 with ⟨r, hL2⟩ | hrest
  ·
    have hc : StatedClassicalModel S .PSL 2 2 r :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL2
    have h3 : 3 ∣ Nat.card S :=
      CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two hc
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hPLq
    rw [hk] at h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · rcases hrest with ⟨r, hSz⟩ | ⟨m, hm, hDih⟩
    ·
      have hn : 1 < r := by
        obtain ⟨a, ha, hr, -⟩ :=
          CFSG.LocalAnalysis.WeakClosure81.exists_mulEquiv_sz_of_isSz hSz
        omega
      have hSzQ : CFSG.Quasithin.IsSz r S :=
        (CFSG.Blueprint.LieModel.twistedB2_iff.mp hSz).2
      exact CFSG.LocalAnalysis.WeakClosure81.not_isPGroup_two_of_isL2OrSz hn
        (Or.inr hSzQ) hPLq
    ·
      obtain ⟨e⟩ := hDih
      have hcardS : Nat.card S = 2 * m := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have hm1 : m = 1 := by
        by_contra hmne
        exact (CFSG.Quasithin.H13.not_isPGroup_two_of_card_odd (X := S) (e := 1) (m := m)
          hm hmne (by rw [hcardS]; norm_num)) hPLq
      have hcardS1 : Nat.card S = 2 := by rw [hcardS, hm1]
      have hK_le_L : K ≤ V ⊔ conjSubgroup V g := by
        intro k hk
        have hk' : k ∈ ((conjSubgroup V g ⊓ D.M : Subgroup G) : Set G) *
            ((V ⊓ conjSubgroup D.M g : Subgroup G) : Set G) := by
          rw [← hKset]
          exact hk
        rw [Set.mem_mul] at hk'
        obtain ⟨a, ha, b, hb, rfl⟩ := hk'
        exact (V ⊔ conjSubgroup V g).mul_mem
          ((le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g) ha.1)
          ((le_sup_left : V ≤ V ⊔ conjSubgroup V g) hb.1)
      have hK_le_M : K ≤ D.M := by
        intro k hk
        have hk' : k ∈ ((conjSubgroup V g ⊓ D.M : Subgroup G) : Set G) *
            ((V ⊓ conjSubgroup D.M g : Subgroup G) : Set G) := by
          rw [← hKset]
          exact hk
        rw [Set.mem_mul] at hk'
        obtain ⟨a, ha, b, hb, rfl⟩ := hk'
        exact D.M.mul_mem ha.2 (hV.2.1 hb.1)
      have hMg_eq : conjSubgroup D.M g = normalizer ((conjSubgroup V g : Subgroup G) : Set G) := by
        rw [← CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_normalizer V g,
          normalizer_eq_of_inCalV D hV]
      have hVg_le_Mg : conjSubgroup V g ≤ conjSubgroup D.M g := by
        rw [hMg_eq]
        exact Subgroup.le_normalizer
      have hK_le_Mg : K ≤ conjSubgroup D.M g := by
        intro k hk
        have hk' : k ∈ ((conjSubgroup V g ⊓ D.M : Subgroup G) : Set G) *
            ((V ⊓ conjSubgroup D.M g : Subgroup G) : Set G) := by
          rw [← hKset]
          exact hk
        rw [Set.mem_mul] at hk'
        obtain ⟨a, ha, b, hb, rfl⟩ := hk'
        exact (conjSubgroup D.M g).mul_mem (hVg_le_Mg ha.1) hb.2
      have hnotVK : ¬ V ≤ K := fun hVK => hInO.2.1 (hVK.trans hK_le_Mg)
      have hrelL : K.relIndex (V ⊔ conjSubgroup V g) = 2 := by
        show Nat.card S = 2
        exact hcardS1
      rcases CFSG.Quasithin.eq_or_eq_of_relIndex_eq_two (A := K) (B := K ⊔ V)
        (C := V ⊔ conjSubgroup V g) le_sup_left (sup_le hK_le_L le_sup_left) hrelL with hEq | hEq
      · exact hnotVK (hEq ▸ le_sup_right)
      · have hLM : V ⊔ conjSubgroup V g ≤ D.M := by
          rw [← hEq]
          exact sup_le hK_le_M hV.2.1
        exact hInO.1.1 (le_sup_right.trans hLM)

theorem s16c1_card_eq_two_mul_uOne {D : Data G} {V₀ V : Subgroup G} (hV : InCalV D.M V) {g z : G}
    (hO : InCalOStar 1 D.M V₀ V g) (hz : z ∈ V ⊓ conjSubgroup V g)
    (hle : Nat.card ↥V ≤ 2 * Nat.card ↥(uOne V z)) :
    Nat.card ↥V = 2 * Nat.card ↥(uOne V z) ∧
      Nat.card ↥(starImg (centralizer ({z} : Set G)) V) = 2 := by
  have hmul := s16c1_card_starImg_mul_card_uOne hV.2.2.2 hz.1
  have hU : 0 < Nat.card ↥(uOne V z) := Nat.card_pos
  have hstar : 0 < Nat.card ↥(starImg (centralizer ({z} : Set G)) V) := Nat.card_pos
  have hne : Nat.card ↥(starImg (centralizer ({z} : Set G)) V) ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hmul
    apply s16c1_not_le_pCoreOf hV hO hz
    have hUV : uOne V z = V :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : uOne V z ≤ V) (le_of_eq hmul.symm)
    rw [← hUV]
    exact inf_le_right
  have hle2 : Nat.card ↥(starImg (centralizer ({z} : Set G)) V) ≤ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ hU
    rw [hmul]
    exact hle
  have h2 : Nat.card ↥(starImg (centralizer ({z} : Set G)) V) = 2 := by omega
  refine ⟨?_, h2⟩
  rw [h2] at hmul
  exact hmul.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
