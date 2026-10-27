module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Defs
import CFSG.GroupTheory.PCoreSurjective
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth in
theorem prime_not_dvd_card_relPPrimeCore {q : ℕ} (hq : q.Prime) (N : Subgroup G) :
    ¬ q ∣ Nat.card (relPPrimeCore q N) :=
  (Nat.Prime.coprime_iff_not_dvd hq).1 (AlmostSimple.coprime_card_relPPrimeCore hq N)

theorem pRank_map_mk'_eq {N X J : Subgroup G} [(J.subgroupOf N).Normal] {q : ℕ}
    (hq : q.Prime) (hXN : X ≤ N) (hJN : J ≤ N) (hJ : ¬ q ∣ Nat.card J) :
    Open.pRank q ((X.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N))) =
      Open.pRank q X := by
  have hker : ¬ q ∣ Nat.card ↥(MonoidHom.ker (QuotientGroup.mk' (J.subgroupOf N))) := by
    rw [QuotientGroup.ker_mk']
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv]
  rw [CFSG.pRank_map_eq_of_not_dvd_card_ker _ (QuotientGroup.mk'_surjective _) hq hker]
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.pRank_subgroupOf hq.one_lt hXN

private theorem ncl_le_normalizer {N B' : Subgroup G} :
    N ≤ Subgroup.normalizer ((ncl N B') : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun n hn x hx => ?_
  have hx' : x ∈ Subgroup.closure {y : G | ∃ g ∈ N, ∃ b ∈ B', y = g * b * g⁻¹} := hx
  show n * x * n⁻¹ ∈ Subgroup.closure {y : G | ∃ g ∈ N, ∃ b ∈ B', y = g * b * g⁻¹}
  refine Subgroup.closure_induction
    (p := fun y _ => n * y * n⁻¹ ∈
      Subgroup.closure {y : G | ∃ g ∈ N, ∃ b ∈ B', y = g * b * g⁻¹})
    (fun y hy => ?_) (by simp) (fun y z _ _ hy hz => ?_) (fun y _ hy => ?_) hx'
  · obtain ⟨g, hg, b, hb, rfl⟩ := hy
    exact Subgroup.subset_closure ⟨n * g, N.mul_mem hn hg, b, hb, by group⟩
  · have heq : n * (y * z) * n⁻¹ = (n * y * n⁻¹) * (n * z * n⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ hy hz
  · have heq : n * y⁻¹ * n⁻¹ = (n * y * n⁻¹)⁻¹ := by group
    rw [heq]
    exact Subgroup.inv_mem _ hy

private theorem le_ncl {N B' : Subgroup G} : B' ≤ ncl N B' := fun _ hb =>
  Subgroup.subset_closure ⟨1, N.one_mem, _, hb, by simp⟩

private theorem ncl_le {N B' : Subgroup G} (hB'N : B' ≤ N) : ncl N B' ≤ N := by
  rw [ncl]
  refine (Subgroup.closure_le N).mpr fun y hy => ?_
  obtain ⟨g, hg, b, hb, rfl⟩ := hy
  exact N.mul_mem (N.mul_mem hg (hB'N hb)) (N.inv_mem hg)

private theorem ncl_comap_normal {N B' : Subgroup G} (hB'N : B' ≤ N) :
    (Subgroup.comap N.subtype (ncl N B')).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (ncl_le hB'N)).mpr ncl_le_normalizer

private theorem ncl_subgroupOf_eq_normalClosure {N B' : Subgroup G} (hB'N : B' ≤ N) :
    (ncl N B').subgroupOf N = normalClosure ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  haveI := ncl_comap_normal hB'N
  refine Subgroup.map_subtype_inj.mp ?_
  rw [Subgroup.map_subgroupOf_eq_of_le (ncl_le hB'N)]
  refine le_antisymm ?_ ?_
  · rw [ncl]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨g, hg, b, hb, rfl⟩ := hy
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * (⟨b, hB'N hb⟩ : ↥N) * (⟨g, hg⟩ : ↥N)⁻¹, ?_, rfl⟩
    exact (Subgroup.normalClosure_normal (s := ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N))
      (G := ↥N)).conj_mem _
      (Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.mpr hb)) _
  · rw [Subgroup.map_le_iff_le_comap]
    exact Subgroup.normalClosure_le_normal fun x hx =>
      le_ncl (Subgroup.mem_subgroupOf.mp hx)

theorem map_ncl_eq_normalClosure {N B' K J : Subgroup G} [(J.subgroupOf N).Normal]
    (hB'N : B' ≤ N) (hB'K : B' ≤ K) (hKN : K ≤ ncl N B') :
    ((ncl N B').subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) =
      normalClosure (((K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) :
        Subgroup (↥N ⧸ J.subgroupOf N)) : Set (↥N ⧸ J.subgroupOf N)) := by
  have hs : Subgroup.map (QuotientGroup.mk' (J.subgroupOf N))
      (normalClosure ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N)) =
      normalClosure ((QuotientGroup.mk' (J.subgroupOf N)) ''
        ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N)) :=
    Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)
  rw [ncl_subgroupOf_eq_normalClosure hB'N, hs]
  have h1 : (QuotientGroup.mk' (J.subgroupOf N)) '' ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N) ⊆
      (QuotientGroup.mk' (J.subgroupOf N)) '' ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (hB'K (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
  have h2 : (QuotientGroup.mk' (J.subgroupOf N)) '' ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) ⊆
      normalClosure ((QuotientGroup.mk' (J.subgroupOf N)) ''
        ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ normalClosure ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [← ncl_subgroupOf_eq_normalClosure hB'N]
      exact Subgroup.mem_subgroupOf.mpr (hKN (Subgroup.mem_subgroupOf.mp hx))
    have hm : QuotientGroup.mk' (J.subgroupOf N) x ∈
        Subgroup.map (QuotientGroup.mk' (J.subgroupOf N))
          (normalClosure ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N)) :=
      Subgroup.mem_map.mpr ⟨x, hx', rfl⟩
    rwa [hs] at hm
  refine le_antisymm ?_ ?_
  · haveI : (normalClosure ((QuotientGroup.mk' (J.subgroupOf N)) ''
        ((K.subgroupOf N : Subgroup ↥N) : Set ↥N))).Normal := Subgroup.normalClosure_normal
    refine Subgroup.normalClosure_le_normal (h1.trans ?_)
    exact Subgroup.le_normalClosure
      (H := (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)))
  · haveI : (normalClosure ((QuotientGroup.mk' (J.subgroupOf N)) ''
        ((B'.subgroupOf N : Subgroup ↥N) : Set ↥N))).Normal := Subgroup.normalClosure_normal
    exact Subgroup.normalClosure_le_normal h2

theorem commutator_map_mk'_eq {N K J : Subgroup G} [(J.subgroupOf N).Normal] (hKN : K ≤ N)
    (hK : ⁅K, K⁆ = K) :
    ⁅(K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)),
        (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N))⁆ =
      (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) := by
  have hKK : ⁅K.subgroupOf N, K.subgroupOf N⁆ = K.subgroupOf N := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKN, hK]
  calc ⁅(K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)),
        (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N))⁆
      = (⁅K.subgroupOf N, K.subgroupOf N⁆).map (QuotientGroup.mk' (J.subgroupOf N)) :=
        (Subgroup.map_commutator _ _ _).symm
    _ = (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) := by rw [hKK]

private theorem card_subgroupOf_inf_dvd {K J : Subgroup G} :
    Nat.card ((J ⊓ K).subgroupOf K) ∣ Nat.card J := by
  have h1 : Nat.card ((J ⊓ K).subgroupOf K) = Nat.card ↥(J ⊓ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h2 : Nat.card ↥(J ⊓ K) = Nat.card ↥((J ⊓ K).subgroupOf J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.toEquiv
  rw [h1, h2]
  exact Subgroup.card_subgroup_dvd_card _

private theorem not_three_dvd_card_subgroupOf_inf {K J : Subgroup G} (hJ : ¬ 3 ∣ Nat.card J) :
    ¬ 3 ∣ Nat.card ((J ⊓ K).subgroupOf K) :=
  fun h => hJ (h.trans (card_subgroupOf_inf_dvd (K := K) (J := J)))

private theorem subgroupOf_inf_normal {N K J : Subgroup G} [(J.subgroupOf N).Normal]
    (hKN : K ≤ N) : ((J ⊓ K).subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff inf_le_right]
  intro h k hh hk
  have hmem : (⟨h, hKN hh.2⟩ : ↥N) ∈ J.subgroupOf N := Subgroup.mem_subgroupOf.mpr hh.1
  have hconj : (⟨k, hKN hk⟩ : ↥N) * ⟨h, hKN hh.2⟩ * (⟨k, hKN hk⟩ : ↥N)⁻¹ ∈ J.subgroupOf N :=
    (Subgroup.Normal.conj_mem (inferInstance : (J.subgroupOf N).Normal) _ hmem _)
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hconj,
    K.mul_mem (K.mul_mem hk hh.2) (K.inv_mem hk)⟩

private theorem three_dvd_card_bar2 {K : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hK : IsL2 (Bar2 K) m) : 3 ∣ Nat.card (Bar2 K) := by
  have hcard := CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two (X := Bar2 K) hK
  rw [hcard, CFSG.RankThree.PartOne.S12K.ordA_one_eq (by omega : 1 ≤ m)]
  refine dvd_mul_of_dvd_right ?_ _
  have h4 : (2 ^ m) ^ 2 = 4 ^ m := by
    calc (2 ^ m) ^ 2 = 2 ^ (m * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * m) := by rw [mul_comm]
      _ = (2 ^ 2) ^ m := by rw [pow_mul]
      _ = 4 ^ m := by norm_num
  rw [h4]
  have hmod : (4 : ℕ) ^ m ≡ 1 [MOD 3] := by
    have h1 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    simpa using h1.pow m
  have hpos : 0 < 4 ^ m := pow_pos (by norm_num) m
  exact (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm

private theorem subgroupOf_inf_le_pCore {N K J : Subgroup G} [(J.subgroupOf N).Normal] {m : ℕ}
    (hKN : K ≤ N) (hJ : ¬ 3 ∣ Nat.card J) (hm : 2 ≤ m) (hK : IsL2 (Bar2 K) m) :
    (J ⊓ K).subgroupOf K ≤ pCore 2 ↥K := by
  set A : Subgroup ↥K := (J ⊓ K).subgroupOf K with hA
  set πK : ↥K →* Bar2 K := QuotientGroup.mk' (pCore 2 ↥K) with hπK
  have hnorm : (A.map πK).Normal :=
    (subgroupOf_inf_normal hKN).map πK (QuotientGroup.mk'_surjective _)
  have h3 : ¬ 3 ∣ Nat.card ↥(A.map πK) := fun h =>
    not_three_dvd_card_subgroupOf_inf (K := K) (J := J) hJ
      (h.trans (Subgroup.card_map_dvd A πK))
  haveI : IsSimpleGroup (Bar2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hK
  have hbot : A.map πK = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map πK) with h | h
    · exact h
    · rw [h, Subgroup.card_top] at h3
      exact absurd (three_dvd_card_bar2 hm hK) h3
  have hker : πK.ker = pCore 2 ↥K := QuotientGroup.ker_mk' _
  rw [← hker]
  exact (Subgroup.map_eq_bot_iff A).mp hbot

theorem isL2_bar2_map_mk' {N K J : Subgroup G} [(J.subgroupOf N).Normal] {m : ℕ} (hKN : K ≤ N)
    (hJN : J ≤ N) (hJ : ¬ 3 ∣ Nat.card J) (hm : 2 ≤ m) (hK : IsL2 (Bar2 K) m) :
    IsL2 (Bar2 ((K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)))) m := by
  let f : ↥K →* ↥((K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N))) :=
    ((QuotientGroup.mk' (J.subgroupOf N)).comp (Subgroup.inclusion hKN)).codRestrict _
      (fun x => Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKN x,
        Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hfker : f.ker = (J ⊓ K).subgroupOf K := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' (J.subgroupOf N) (Subgroup.inclusion hKN x) = 1 :=
        congrArg Subtype.val hx
      have h2 : (Subgroup.inclusion hKN x : ↥N) ∈ J.subgroupOf N :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hKN x)).mp h1
      exact ⟨Subgroup.mem_subgroupOf.mp h2, x.2⟩
    · rintro ⟨hx, -⟩
      have h1 : QuotientGroup.mk' (J.subgroupOf N) (Subgroup.inclusion hKN x) = 1 :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hKN x)).mpr (Subgroup.mem_subgroupOf.mpr hx)
      exact Subtype.ext h1
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp z.2
    refine ⟨⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩, Subtype.ext ?_⟩
    have h1 : (f ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩).1 =
        QuotientGroup.mk' (J.subgroupOf N) a := rfl
    rw [h1]
    exact haz
  have hker : IsPGroup 2 f.ker := by
    rw [hfker]
    exact IsPGroup.to_le (pCore_isPGroup (p := 2) (G := ↥K))
      (subgroupOf_inf_le_pCore hKN hJ hm hK)
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hfsurj hker
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hK

theorem card_map_mk'_eq {N D₀ J : Subgroup G} [(J.subgroupOf N).Normal] (hD₀N : D₀ ≤ N)
    (hJN : J ≤ N) (hcop : Nat.Coprime (Nat.card D₀) (Nat.card J)) :
    Nat.card ((D₀.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N))) = Nat.card D₀ := by
  have hdisj : D₀.subgroupOf N ⊓ J.subgroupOf N = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀N).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv]
    exact hcop
  have hinj : Function.Injective fun x : ↥(D₀.subgroupOf N) =>
      QuotientGroup.mk' (J.subgroupOf N) (x : ↥N) := by
    intro x y hxy
    have hmem : (x : ↥N)⁻¹ * (y : ↥N) ∈ J.subgroupOf N :=
      (QuotientGroup.eq).mp hxy
    have hmem' : (x : ↥N)⁻¹ * (y : ↥N) ∈ D₀.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      exact (D₀.subgroupOf N).mul_mem ((D₀.subgroupOf N).inv_mem x.2) y.2
    have hone : (x : ↥N)⁻¹ * (y : ↥N) = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hmem', hmem⟩
      rwa [hdisj, Subgroup.mem_bot] at this
    have hxy' : (x : ↥N) = (y : ↥N) := by
      calc (x : ↥N) = (x : ↥N) * ((x : ↥N)⁻¹ * (y : ↥N)) := by rw [hone, mul_one]
        _ = (y : ↥N) := by group
    exact Subtype.ext hxy'
  have hmap : Subgroup.map ((QuotientGroup.mk' (J.subgroupOf N)).comp
      (D₀.subgroupOf N).subtype) (⊤ : Subgroup ↥(D₀.subgroupOf N)) =
      (D₀.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) := by
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
  have h := Subgroup.card_map_of_injective (f := (QuotientGroup.mk' (J.subgroupOf N)).comp
    (D₀.subgroupOf N).subtype) hinj (K := ⊤)
  rw [hmap, Subgroup.card_top, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀N).toEquiv] at h
  exact h

theorem mk'_mem_normalizer_map {N K J : Subgroup G} [(J.subgroupOf N).Normal] (hKN : K ≤ N)
    (hJN : J ≤ N) {x : ↥N} (hx : (x : G) ∈ normalizer ((K ⊔ J : Subgroup G) : Set G)) :
    QuotientGroup.mk' (J.subgroupOf N) x ∈
      normalizer (((K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) :
        Subgroup (↥N ⧸ J.subgroupOf N)) : Set (↥N ⧸ J.subgroupOf N)) := by
  have hsub : (K ⊔ J : Subgroup G).subgroupOf N = K.subgroupOf N ⊔ J.subgroupOf N :=
    Subgroup.subgroupOf_sup hKN hJN
  have key : ∀ (y : ↥N), (y : G) ∈ normalizer ((K ⊔ J : Subgroup G) : Set G) →
      ∀ z ∈ (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)),
      QuotientGroup.mk' (J.subgroupOf N) y * z * (QuotientGroup.mk' (J.subgroupOf N) y)⁻¹ ∈
        (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) := by
    intro y hy z hz
    obtain ⟨kN, hkN, rfl⟩ := Subgroup.mem_map.mp hz
    have hkN' : (kN : G) ∈ K := Subgroup.mem_subgroupOf.mp hkN
    have hconj : (y : G) * (kN : G) * (y : G)⁻¹ ∈ K ⊔ J :=
      ((Subgroup.mem_normalizer_iff.mp hy) _).mp (Subgroup.mem_sup_left hkN')
    have hconjN : (y : G) * (kN : G) * (y : G)⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem y.2 (hKN hkN')) (N.inv_mem y.2)
    have hmem : (⟨(y : G) * (kN : G) * (y : G)⁻¹, hconjN⟩ : ↥N) ∈
        K.subgroupOf N ⊔ J.subgroupOf N := by
      rw [← hsub]
      exact Subgroup.mem_subgroupOf.mpr hconj
    obtain ⟨k', hk', j, hj, hkj⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hj1 : QuotientGroup.mk' (J.subgroupOf N) j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    have hxkN : QuotientGroup.mk' (J.subgroupOf N) ⟨(y : G) * (kN : G) * (y : G)⁻¹, hconjN⟩ =
        QuotientGroup.mk' (J.subgroupOf N) y * QuotientGroup.mk' (J.subgroupOf N) kN *
          (QuotientGroup.mk' (J.subgroupOf N) y)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have heq : QuotientGroup.mk' (J.subgroupOf N) y * QuotientGroup.mk' (J.subgroupOf N) kN *
        (QuotientGroup.mk' (J.subgroupOf N) y)⁻¹ = QuotientGroup.mk' (J.subgroupOf N) k' := by
      rw [← hxkN, hkj.symm, map_mul, hj1, mul_one]
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨k', hk', rfl⟩
  refine (Subgroup.mem_normalizer_iff).mpr fun z => ⟨key x hx z, fun hz => ?_⟩
  have h := key x⁻¹ (Subgroup.inv_mem _ hx)
    (QuotientGroup.mk' (J.subgroupOf N) x * z * (QuotientGroup.mk' (J.subgroupOf N) x)⁻¹) hz
  rw [map_inv] at h
  simpa [mul_assoc] using h

theorem map_mk'_le_normalizer_map {N T K J : Subgroup G} [(J.subgroupOf N).Normal]
    (hKN : K ≤ N) (hJN : J ≤ N) (hT : T ≤ normalizer ((K ⊔ J : Subgroup G) : Set G)) :
    (T.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) ≤
      normalizer (((K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) :
        Subgroup (↥N ⧸ J.subgroupOf N)) : Set (↥N ⧸ J.subgroupOf N)) := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  exact mk'_mem_normalizer_map hKN hJN (hT (Subgroup.mem_subgroupOf.mp ht))

theorem commutator_mem_of_mk'_mem_centralizer {N D₀ J : Subgroup G} [(J.subgroupOf N).Normal]
    (hD₀N : D₀ ≤ N) {x : ↥N}
    (hx : QuotientGroup.mk' (J.subgroupOf N) x ∈
      centralizer (((D₀.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) :
        Subgroup (↥N ⧸ J.subgroupOf N)) : Set (↥N ⧸ J.subgroupOf N))) :
    ∀ d ∈ D₀, (x : G) * d * (x : G)⁻¹ * d⁻¹ ∈ J := by
  intro d hd
  set dN : ↥N := ⟨d, hD₀N hd⟩ with hdN
  have hdmem : QuotientGroup.mk' (J.subgroupOf N) dN ∈
      (D₀.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) :=
    Subgroup.mem_map.mpr ⟨dN, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  have hcomm : QuotientGroup.mk' (J.subgroupOf N) dN *
      QuotientGroup.mk' (J.subgroupOf N) x =
      QuotientGroup.mk' (J.subgroupOf N) x *
        QuotientGroup.mk' (J.subgroupOf N) dN :=
    (Subgroup.mem_centralizer_iff.mp hx) _ hdmem
  have hmemN : (x : G) * d * (x : G)⁻¹ * d⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem x.2 (hD₀N hd)) (N.inv_mem x.2)) (N.inv_mem (hD₀N hd))
  have heq : (⟨(x : G) * d * (x : G)⁻¹ * d⁻¹, hmemN⟩ : ↥N) =
      x * dN * x⁻¹ * dN⁻¹ := by
    ext
    rfl
  have h1 : QuotientGroup.mk' (J.subgroupOf N) ⟨(x : G) * d * (x : G)⁻¹ * d⁻¹, hmemN⟩ = 1 := by
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem le_sup_of_map_mk'_eq {N X K J : Subgroup G} [(J.subgroupOf N).Normal] (hXN : X ≤ N)
    (h : (X.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) =
      (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N))) :
    X ≤ K ⊔ J := by
  intro x hx
  set xN : ↥N := ⟨x, hXN hx⟩ with hxN
  have hxmem : QuotientGroup.mk' (J.subgroupOf N) xN ∈
      (K.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N)) := by
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨xN, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨kN, hkN, hkEq⟩ := Subgroup.mem_map.mp hxmem
  obtain ⟨zN, hzN, hzEq⟩ := (QuotientGroup.mk'_eq_mk' (J.subgroupOf N)).mp hkEq
  have hxEq : x = (kN : G) * (zN : G) := by
    have := congrArg Subtype.val hzEq
    simpa using this.symm
  rw [hxEq]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hkN) (Subgroup.mem_subgroupOf.mp hzN)

theorem isSylowOf_map_mk' {N T J : Subgroup G} [(J.subgroupOf N).Normal]
    (hT : IsSylowOf 2 T N) :
    IsSylowOf 2 ((T.subgroupOf N).map (QuotientGroup.mk' (J.subgroupOf N))) ⊤ := by
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  rw [← hQ]
  exact ⟨Sylow.subtype (Sylow.mapSurjective (f := QuotientGroup.mk' (J.subgroupOf N))
    (QuotientGroup.mk'_surjective _) Q) le_top, by
      rw [Sylow.coe_subtype, Sylow.coe_mapSurjective, Subgroup.map_subgroupOf_eq_of_le le_top]⟩

theorem false_of_isSylowOf_le_normalizer (hF : KU3Facts) {Y : Type} [Group Y] [Finite Y]
    {X K T : Subgroup Y} {f : ℕ} (hX : IsU3 ↥X f) (hf : 4 ≤ f) (hfe : Even f) (hXn : X.Normal)
    (hKX : K ≤ X) (hK : ⁅K, K⁆ = K) (hL2 : IsL2 (Bar2 K) f) (hT : IsSylowOf 2 T ⊤)
    (hTK : T ≤ normalizer (K : Set Y)) : False := by
  have hK' : ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKX, hK]
  have hL2' : IsL2 (Bar2 (K.subgroupOf X)) f := by
    obtain ⟨e⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.nonempty_bar2_equiv_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hKX)
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2
  have hTX : IsSylowOf 2 (T ⊓ X) X :=
    IsSylowOf.inf_of_le_normalizer hT le_top (by rw [Subgroup.normalizer_eq_top X])
  obtain ⟨T₂, hT₂⟩ := hTX.exists_sylow_eq_subgroupOf
  refine (hF (X := ↥X) (f := f) hX hf hfe (K.subgroupOf X) hK' hL2').2.1 T₂ ?_
  rw [hT₂]
  refine Subgroup.le_normalizer_iff.mpr fun t ht k hk => ?_
  exact Subgroup.mem_subgroupOf.mpr
    ((Subgroup.mem_normalizer_iff.mp (hTK (Subgroup.mem_subgroupOf.mp ht).1)) _
      |>.mp (Subgroup.mem_subgroupOf.mp hk))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
