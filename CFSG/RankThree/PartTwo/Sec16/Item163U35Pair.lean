module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35CE
import CFSG.RankThree.PartTwo.Sec16.Item163U35Y
import CFSG.RankThree.PartTwo.Sec16.Item163U35Pt
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35Facts
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1421
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y : Subgroup G}

namespace Conf684

private theorem mem_scriptQ_sup (h : Conf684 A c L Y) {w a g : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (haA : a ∈ A)
    (haz : a ∉ Subgroup.zpowers c) (hgX : g ∈ xA A) :
    ((CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
        Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom))
      ∈ scriptQ A (lB A) := by
  have hQ : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    Res163U35Facts.pCoreOf_mem_scriptQ h.sec15R h.mem_y h.case3 h.item1444 h.item146
  have hQw : (CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ∈
      scriptQ A (lB A) :=
    rank3II_14_4_5_lB hwA hQ
  have hgA : g ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G)
      (pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G)) hgX)
  have hQwg : ((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom).map
      (MulAut.conj g).toMonoidHom ∈ scriptQ A (lB A) :=
    rank3II_14_4_5_lB hgA hQw
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      h.sec15R.toSec13Data.isElemAbelian.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hACn : A ≤ Subgroup.normalizer
      (Subgroup.centralizer ({a} : Set G) : Set G) :=
    hAC.trans Subgroup.le_normalizer
  have hgC : g ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)
      (pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G)) hgX)
  have hCg : (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({a} : Set G) := by
    have hga : g * a * g⁻¹ = a := by
      have h := Subgroup.mem_centralizer_iff.mp hgC a (by simp)
      rw [← h]
      group
    have hz : (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers a := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (g * a * g⁻¹) = Subgroup.zpowers a
      rw [hga]
    have hCe : Subgroup.centralizer ({a} : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    calc (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom
        = Subgroup.centralizer ((Subgroup.zpowers a).map
            (MulAut.conj g).toMonoidHom : Subgroup G) := by rw [hCe, map_conj_centralizer]
      _ = Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by rw [hz]
      _ = Subgroup.centralizer ({a} : Set G) := hCe.symm
  have hP₁mem : (CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)) ∈
      scriptQ A (lB A) :=
    mem_scriptQ_of_le hQ inf_le_left (Late.le_normalizer_inf hQ.1.2.2 hACn)
  have hP₂eq : (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom) ⊓
        Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom =
      ((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom).map
          (MulAut.conj g).toMonoidHom ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hCg]
  have hP₂mem : ((((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom) ⊓
        Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom) ∈
      scriptQ A (lB A) := by
    rw [hP₂eq]
    exact mem_scriptQ_of_le hQwg inf_le_left (Late.le_normalizer_inf hQwg.1.2.2 hACn)
  have hPΔ : ((CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
        (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
          Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom)) ≤
      delta A (lB A) (Subgroup.centralizer ({a} : Set G)) :=
    sup_le (le_delta hP₁mem inf_le_right)
      (le_delta hP₂mem (hP₂eq.le.trans inf_le_right))
  exact mem_scriptQ_of_le (h.delta_centralizer_mem_scriptQ haA haz) hPΔ
    (le_normalizer_sup hP₁mem.1.2.2 hP₂mem.1.2.2)

private theorem exists_twoGroup (h : Conf684 A c L Y) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) :
    ∃ a g : G, a ∈ A ∧ a ∉ Subgroup.zpowers c ∧ g ∈ xA A ∧
      (CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)) ≠ ⊥ ∧
      (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
          Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom) ≠ ⊥ ∧
      ((CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
        (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
          Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom))
        ∈ scriptQ A (lB A) ∧
      IsPGroup 2 ↑((CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
        (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
          Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom)) := by
  obtain ⟨a, haA, haz, hP₁ne, hP₂ne'⟩ :=
    Res163U35Facts.exists_a h.sec15R h.mem_y h.case3 hwA hwL
  have ha1 : a ≠ 1 := fun h1 => haz (h1 ▸ Subgroup.one_mem _)
  obtain ⟨g, hgX, hP2grp⟩ :=
    Res163U35Facts.exists_x h.sec15R h.mem_y h.case3 h.item1444 h.item146 h.item143
      hwA hwL haA ha1 haz
  have hP₂ne : ((((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom) ⊓
      Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom) ≠ ⊥ := by
    intro hbot
    apply hP₂ne'
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hbot
  exact ⟨a, g, haA, haz, hgX, hP₁ne, hP₂ne, mem_scriptQ_sup h hwA haA haz hgX, hP2grp⟩

private theorem mem_normalizer_inf_of_map_conj_eq (h : Conf684 A c L Y) {v w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) (hvX : v ∈ xA A)
    (hY : Y.map (MulAut.conj (v * w)).toMonoidHom = Y) :
    w ∈ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G) := by
  set J : Subgroup G := Y ⊓ L with hJ
  have hvC : v ∈ Subgroup.centralizer (L : Set G) :=
    Res163U35Facts.xA_le_centralizer h.sec15R h.mem_y h.case3 hvX
  have hwNL : w ∈ Subgroup.normalizer (L : Set G) :=
    Conf684.normalizer_le_normalizer h hwA
  have hJwL : J.map (MulAut.conj w).toMonoidHom ≤ L := by
    calc J.map (MulAut.conj w).toMonoidHom ≤ L.map (MulAut.conj w).toMonoidHom :=
          Subgroup.map_mono inf_le_right
      _ = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hwNL
  have hvJw : v ∈ Subgroup.centralizer
      ((J.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJwL) hvC
  have hJw : (J.map (MulAut.conj w).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      J.map (MulAut.conj w).toMonoidHom :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ hvJw)
  have hJvw : J.map (MulAut.conj (v * w)).toMonoidHom =
      J.map (MulAut.conj w).toMonoidHom :=
    (Late.map_conj_map_conj J v w).symm.trans hJw
  have hJvwY : J.map (MulAut.conj (v * w)).toMonoidHom ≤ Y :=
    (Subgroup.map_mono inf_le_left).trans_eq hY
  have hJvwL : J.map (MulAut.conj (v * w)).toMonoidHom ≤ L := hJvw.le.trans hJwL
  have hJvwle : J.map (MulAut.conj (v * w)).toMonoidHom ≤ J :=
    le_inf hJvwY hJvwL
  have hJwle : J.map (MulAut.conj w).toMonoidHom ≤ J := hJvw ▸ hJvwle
  have hcard : Nat.card (J.map (MulAut.conj w).toMonoidHom) = Nat.card J :=
    Subgroup.card_map_of_injective (MulAut.conj w).injective
  have heq : J.map (MulAut.conj w).toMonoidHom = J :=
    Subgroup.eq_of_le_of_card_ge hJwle (by rw [hcard])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

private theorem not_two_conj (h : Conf684 A c L Y) {w g : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) (hgX : g ∈ xA A)
    (hwN : w ∉ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G))
    {K : Subgroup G} {x₁ x₂ : G} (hx₁ : x₁ ∈ xA A) (hx₂ : x₂ ∈ xA A)
    (hK₁ : K = Y.map (MulAut.conj x₁).toMonoidHom)
    (hK₂ : K = (Y.map (MulAut.conj (g * w)).toMonoidHom).map
      (MulAut.conj x₂).toMonoidHom) : False := by
  have hvX : x₁⁻¹ * x₂ * g ∈ xA A :=
    mul_mem (mul_mem (inv_mem hx₁) hx₂) hgX
  have hYeq : Y.map (MulAut.conj ((x₁⁻¹ * x₂ * g) * w)).toMonoidHom = Y := by
    have hK : Y.map (MulAut.conj x₁).toMonoidHom =
        (Y.map (MulAut.conj (g * w)).toMonoidHom).map
          (MulAut.conj x₂).toMonoidHom := hK₁.symm.trans hK₂
    have h := congrArg
      (fun S : Subgroup G => S.map (MulAut.conj x₁⁻¹).toMonoidHom) hK
    simp only [Late.map_conj_map_conj] at h
    rw [inv_mul_cancel, Late.map_conj_one] at h
    have hvw : (x₁⁻¹ * x₂ * g) * w = x₁⁻¹ * (x₂ * (g * w)) := by group
    rw [hvw]
    exact h.symm
  exact hwN (mem_normalizer_inf_of_map_conj_eq h hwA hwL hvX hYeq)

theorem exists_ce684 (h : Conf684 A c L Y) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L)
    (hwN : w ∉ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G)) :
    ∃ K₁ K₂ T₁ T₂ : Subgroup G, CE684 A L K₁ K₂ T₁ T₂ := by
  obtain ⟨a, g, haA, haz, hgX, hP₁ne, hP₂ne, hPmem, hP2grp⟩ :=
    exists_twoGroup h hwA hwL
  obtain ⟨T, hT, hPT⟩ := Proof1413.exists_scriptQPiStar_top
    (U := (CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
        Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom))
    ⟨⟨hPmem, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hP2grp⟩
  obtain ⟨K, hTK⟩ := Conf684.exists_isZeta h hT
  have hQ : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    Res163U35Facts.pCoreOf_mem_scriptQ h.sec15R h.mem_y h.case3 h.item1444 h.item146
  have hQpi : CFSG.Open.pCoreOf 2 Y ∈
      scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2) := by
    refine ⟨⟨hQ, (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans Subgroup.le_normalizer⟩, ?_⟩
    exact (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
  obtain ⟨S, hQS, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2))) hQpi
  have hSY : IsZeta A L S Y := ⟨h.mem_y, h.meets, hS⟩
  have hgA : g ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G)
      (pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G)) hgX)
  have huA : g * w ∈ Subgroup.normalizer (A : Set G) := mul_mem hgA hwA
  have hSY' : IsZeta A L (S.map (MulAut.conj (g * w)).toMonoidHom)
      (Y.map (MulAut.conj (g * w)).toMonoidHom) :=
    Conf684.map_conj_isZeta h huA hSY
  have hTS : T ⊓ S ≠ ⊥ := by
    intro hbot
    apply hP₁ne
    refine le_bot_iff.mp ?_
    calc CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G)
        ≤ T ⊓ S := le_inf (le_sup_left.trans hPT) (inf_le_left.trans hQS)
      _ = ⊥ := hbot
  have hP₂S' : ((((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom) ⊓
        Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom) ≤
      S.map (MulAut.conj (g * w)).toMonoidHom := by
    calc ((((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom) ⊓
          Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom)
        ≤ ((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := Subgroup.map_mono inf_le_left
      _ = (CFSG.Open.pCoreOf 2 Y).map (MulAut.conj (g * w)).toMonoidHom :=
          Late.map_conj_map_conj _ g w
      _ ≤ S.map (MulAut.conj (g * w)).toMonoidHom := Subgroup.map_mono hQS
  have hTS' : T ⊓ S.map (MulAut.conj (g * w)).toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hP₂ne
    refine le_bot_iff.mp ?_
    calc ((((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom) ⊓
          Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom)
        ≤ T ⊓ S.map (MulAut.conj (g * w)).toMonoidHom :=
          le_inf (le_sup_right.trans hPT) hP₂S'
      _ = ⊥ := hbot
  by_cases hconj₁ : ∃ x ∈ xA A, K = Y.map (MulAut.conj x).toMonoidHom
  · obtain ⟨x₁, hx₁, hK₁⟩ := hconj₁
    by_cases hconj₂ : ∃ x ∈ xA A,
        K = (Y.map (MulAut.conj (g * w)).toMonoidHom).map (MulAut.conj x).toMonoidHom
    · obtain ⟨x₂, hx₂, hK₂⟩ := hconj₂
      exact (not_two_conj h hwA hwL hgX hwN hx₁ hx₂ hK₁ hK₂).elim
    · exact ⟨K, Y.map (MulAut.conj (g * w)).toMonoidHom, T,
        S.map (MulAut.conj (g * w)).toMonoidHom, hTK, hSY', hTS', hconj₂⟩
  · exact ⟨K, Y, T, S, hTK, hSY, hTS, hconj₁⟩

end Conf684

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
