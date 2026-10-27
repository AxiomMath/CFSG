module

public import CFSG.Quasithin.Vol2.Ch1Fitting
public import CFSG.Quasithin.Vol2.Ch1Residual
public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.EmptyFaithful.S152RDef
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch1Local

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem charTwo_of_charTwo_inf_centralizer {H : Subgroup G} {z : G} (hz : z ∈ pCoreOf 2 H)
    (h : CharTwo (H ⊓ Subgroup.centralizer ({z} : Set G))) : CharTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 H with hR
  set Hz := H ⊓ Subgroup.centralizer ({z} : Set G) with hHz
  set N := H ⊓ Subgroup.centralizer (R : Set G) with hN
  have hNH : N ≤ H := inf_le_left
  have hNHz : N ≤ Hz := fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun a ha => by
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact Subgroup.mem_centralizer_iff.mp hx.2 a hz⟩
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf H H
      (Subgroup.centralizer (R : Set G)) Subgroup.le_normalizer
      ((le_normalizer_pCoreOf 2 H).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer R))
  have hnorm : (N.subgroupOf Hz).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNHz).mpr (inf_le_left.trans hHN)
  have hCN : CharTwo N := CharTwo.of_normal h hNHz hnorm
  have hsub : pCoreOf 2 N ≤ R :=
    A4.pCoreOf_le_of_subnormal 2 (A3.subnormal_of_normal hNH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN))
  intro x hx
  have hxN : x ∈ N := hx
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 N : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hsub) hx.2
  exact hsub (hCN ⟨hxN, hxC⟩)

theorem mem_pCoreOf_two_of_centralizes {H K : Subgroup G} (hKH : K ∈ cComp H)
    (hq : ¬ CFSG.IsQuasisimple ↥K) {z : G} (hzK : z ∈ K) (hz2 : z ^ 2 = 1)
    (hz : ∀ q : ℕ, q.Prime → ∀ x ∈ pCoreOf q K, x * z = z * x) : z ∈ pCoreOf 2 K := by
  have hperf : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKH
  have hns : ¬ Group.IsSolvable ↥K := not_isSolvable_of_mem_cComp hKH
  have hmax : ∀ P : Subgroup ↥K, P.Normal → P = ⊤ ∨ Group.IsSolvable P := by
    intro P hP
    rcases normal_eq_top_or_map_le_solvRad hKH P with h | h
    · exact Or.inl h
    · right
      have hs : Group.IsSolvable ↥(solvRad K) := solvRad_isSolvable K
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion h).comp
          (P.equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom)
        ((Subgroup.inclusion_injective h).comp
          (P.equivMapOfInjective K.subtype K.subtype_injective).injective)
  have hy2 : (⟨z, hzK⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
  have hyc : ∀ p : ℕ, p.Prime → ∀ x ∈ CFSG.pCore p ↥K, x * (⟨z, hzK⟩ : ↥K) = ⟨z, hzK⟩ * x := by
    intro p hp x hx
    have hxG : (x : G) ∈ pCoreOf p K := by
      exact ⟨x, hx, rfl⟩
    exact Subtype.ext (hz p hp x hxG)
  have h := mem_pCore_two_of_centralizes_pCores hperf hmax hns hq hy2 hyc
  exact ⟨_, h, rfl⟩

theorem lemma_1_2_11 (hK : quasithinIsQTKECat G) {T H K : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hH : pCoreOf 2 H ≠ ⊥) (hTH : IsSylowTwoOf (T ⊓ H) H) (hKH : K ∈ cComp H) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hzK : z ∈ K) (hzTH : z ∈ T ⊓ H)
    (ha : ∃ U : Subgroup G, U ≤ H ∧ IsElemAbelian 2 U ∧
      z ∈ ⁅U, opResidual 2 (H ⊓ Subgroup.normalizer (U : Set G))⁆)
    (hb : T ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ T ⊓ H) :
    CFSG.IsQuasisimple ↥K ∨ CharTwo H := by
  by_cases hq : CFSG.IsQuasisimple ↥K
  · exact Or.inl hq
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUH, hU, hzU⟩ := ha
  have hT' : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo hT le_top
  have hZle : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
    rw [quasithinOmegaOneCenter, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hz
  have hzTc : ∀ t ∈ T, t * z = z * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp (hZle hz).2 t ht
  have hOH : pCoreOf 2 H ≤ T ⊓ H := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTH
  have hcen : ∀ q : ℕ, q.Prime → ∀ x ∈ pCoreOf q K, x * z = z * x := by
    intro q hq' x hx
    have : Fact q.Prime := ⟨hq'⟩
    have hxH : x ∈ pCoreOf q H := A4.pCoreOf_le_of_subnormal q (subnormal_of_mem_cComp hKH) hx
    by_cases hq2 : q = 2
    · subst hq2
      exact hzTc x (hOH hxH).1
    · have hzc := centralizes_pCoreOf_of_mem_commutator hK hH hUH hU hq' hq2 hzU
      exact Subgroup.mem_centralizer_iff.mp hzc x hxH
  have hzOK : z ∈ pCoreOf 2 K := mem_pCoreOf_two_of_centralizes hKH hq hzK hz2 hcen
  have hzOH : z ∈ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKH) hzOK
  refine charTwo_of_charTwo_inf_centralizer hzOH ?_
  set M := Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) with hM
  set N := H ⊓ Subgroup.centralizer ({z} : Set G) with hN
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; simp)
  have hzne : Subgroup.zpowers z ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hz1
  have hMloc : IsTwoLocal M := ⟨_, hzne, hzp, rfl⟩
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => by
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact (hzTc t ht).symm
  have hTM : T ≤ M := hTc.trans (centralizer_singleton_le_normalizer_zpowers z)
  have hNM : N ≤ M := inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers z)
  have hOHN : pCoreOf 2 H ≤ N := fun x hx => ⟨(hOH hx).2, hTc (hOH hx).1⟩
  have hOHO : pCoreOf 2 H ≤ pCoreOf 2 N :=
    le_pCoreOf_of_le_normalizer hOHN
      (inf_le_left.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hMS : pCoreOf 2 M ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hT' hTM)
  have hC : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ N := by
    intro x hx
    have hxT : x ∈ T := hMS hx.1
    have hxcH : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOHO) hx.2
    have hxH : x ∈ H := (hb ⟨hxT, hxcH⟩).2
    refine ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact (hzTc x hxT).symm
  exact charTwo_of_isTwoLocal_of_pCore_centralizer_le hK.2.1 hT' hMloc hTM hNM hC

end CFSG.Quasithin
