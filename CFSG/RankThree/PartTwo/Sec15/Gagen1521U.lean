module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521Defs
public import CFSG.RankThree.PartTwo.Sec15.Gagen1521UTools
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofCon

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

open Proof1521

theorem step1521UConj_of_qStar
    (hSN : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
        ∃ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≤ Subgroup.normalizer (Y : Set G))
    (h1411 : Item1411_1R) (h146 : Item146S14) (hq0 : Step1517Q0) (hT : Step1521T)
    (hcy : Step1521CY) : Step1521UConj := by
  intro G _ _ A c L h Y hctx p P hP X hX hPX hP0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hPT⟩ := hT G A c L h Y hctx p P hP X hX hPX hP0
  obtain ⟨S, hS, hSY⟩ := hSN G A c L h Y hctx
  obtain ⟨w, hw, rfl⟩ := h1411 G A c L h S hS T hT
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  obtain ⟨-, -, -, -, -, -, hYL, -, hΩ⟩ := hctx.concl1515
  obtain ⟨-, h9, -⟩ := Proof1517.point_facts h hctx
  have h3 : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3 (normalizer_le_of_omegaA_eq hΩ hwA)
  set P' := P.map (MulAut.conj w⁻¹).toMonoidHom with hP'def
  have hP' : Data1519 A (lB A) L p P' := data1519_map_conj hP (inv_mem hwA) (inv_mem hwL)
  have hconj : ∀ s : Set G,
      (MulAut.conj w⁻¹).toMonoidHom '' ((MulAut.conj w).toMonoidHom '' s) = s := by
    intro s
    rw [Set.image_image]
    have hfun : (fun x => (MulAut.conj w⁻¹).toMonoidHom
        ((MulAut.conj w).toMonoidHom x)) = id := by
      funext x
      change (MulAut.conj w⁻¹) ((MulAut.conj w) x) = x
      simp only [MulAut.conj_apply, inv_inv]
      group
    rw [hfun, Set.image_id]
  have hS' : (MulAut.conj w⁻¹).toMonoidHom '' (S.map (MulAut.conj w).toMonoidHom : Set G) =
      (S : Set G) := by
    rw [← Subgroup.coe_map, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
  have hP'' : (MulAut.conj w⁻¹).toMonoidHom '' (P : Set G) = (P' : Set G) := by
    rw [hP'def, Subgroup.coe_map]
  have hP'S : ((P' ⊔ S : Subgroup G) : Set G) = (S : Set G) * (P' : Set G) := by
    have hmap : (P' ⊔ S).map (MulAut.conj w).toMonoidHom =
        P ⊔ S.map (MulAut.conj w).toMonoidHom := by
      rw [Subgroup.map_sup, hP'def, Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
    have h1 : (MulAut.conj w).toMonoidHom '' ((P' ⊔ S : Subgroup G) : Set G) =
        (S.map (MulAut.conj w).toMonoidHom : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_map, hmap, hPT]
    calc ((P' ⊔ S : Subgroup G) : Set G)
        = (MulAut.conj w⁻¹).toMonoidHom '' ((MulAut.conj w).toMonoidHom ''
            ((P' ⊔ S : Subgroup G) : Set G)) := (hconj _).symm
      _ = (MulAut.conj w⁻¹).toMonoidHom ''
            ((S.map (MulAut.conj w).toMonoidHom : Set G) * (P : Set G)) := by rw [h1]
      _ = (MulAut.conj w⁻¹).toMonoidHom '' (S.map (MulAut.conj w).toMonoidHom : Set G) *
            (MulAut.conj w⁻¹).toMonoidHom '' (P : Set G) :=
          Set.image_mul (MulAut.conj w⁻¹).toMonoidHom
      _ = (S : Set G) * (P' : Set G) := by rw [hS', hP'']
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := h.toSec13Data.le_centralizer
  have hP'L : P' ≤ L := by
    rw [hP'def]
    calc P.map (MulAut.conj w⁻¹).toMonoidHom
        ≤ L.map (MulAut.conj w⁻¹).toMonoidHom := Subgroup.map_mono hP.2.2.2.2.2.1.1.2
      _ = L := Late.map_conj_eq_of_mem_normalizer (inv_mem hwL)
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := h.toSec13Data.A_le_centralizer
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    (CFSG.RankThree.PartTwo.Sec14.mem_scriptQ_iff.mp hS.prop.1.1).2.1
  have hOS : CFSG.Open.pCoreOf 2 Y ≤ S :=
    pCoreOf_two_le_of_mem_qStar h.isE27 (h146 G A c L h.toSec14Std) hS hSY
      (hq0 G A c L h Y hctx)
  refine ⟨Y, P', ⁅S, Subgroup.zpowers c⁆, hctx, hP', ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hU
    refine hcy G A c L h Y hctx p P hP ?_
    have hSC : S ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hU
    exact hOS.trans (hSC.trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c))))
  ·
    have hUS : ⁅S, Subgroup.zpowers c⁆ ≤ S :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        (Subgroup.zpowers_le.mpr (hAS h.toSec13Data.mem_A))
    exact (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2 |>.to_le hUS
  ·
    have hK : ((S ⊔ A : Subgroup G) : Set G) ⊆
        (S : Set G) * (Subgroup.centralizer ({c} : Set G) : Set G) := by
      rw [Subgroup.coe_mul_of_right_le_normalizer_left S A hAS]
      exact Set.mul_subset_mul_left hAc
    exact le_sup_right.trans (le_normalizer_commutator_of_subset_mul le_sup_left hK)
  ·
    have hK : ((P' ⊔ S : Subgroup G) : Set G) ⊆
        (S : Set G) * (Subgroup.centralizer ({c} : Set G) : Set G) := by
      rw [hP'S]
      exact Set.mul_subset_mul_left (hP'L.trans hLc)
    exact le_sup_left.trans (le_normalizer_commutator_of_subset_mul le_sup_right hK)
  ·
    have hOn : L ⊓ Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
      inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    have hYmul : (Y : Set G) ⊆
        (CFSG.Open.pCoreOf 2 Y : Set G) * ((L ⊓ Y : Subgroup G) : Set G) := by
      intro y hy
      rw [hYL, sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hOn] at hy
      exact hy
    have hK : ((S ⊔ Y : Subgroup G) : Set G) ⊆
        (S : Set G) * (Subgroup.centralizer ({c} : Set G) : Set G) := by
      rw [Subgroup.coe_mul_of_left_le_normalizer_right S Y hSY]
      intro x hx
      obtain ⟨s, hs, y, hy, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨t, ht, a, ha, hta⟩ := Set.mem_mul.mp (hYmul hy)
      exact Set.mem_mul.mpr ⟨s * t, S.mul_mem hs (hOS ht), a,
        hLc (Subgroup.mem_inf.mp ha).1, by rw [← hta]; group⟩
    exact le_sup_right.trans (le_normalizer_commutator_of_subset_mul le_sup_left hK)

theorem step1521UConj_of_T (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R)
    (h146 : Item146S14) (hq0 : Step1517Q0) (hT : Step1521T) (hcy : Step1521CY) :
    Step1521UConj :=
  step1521UConj_of_qStar (by
    intro G _ _ A c L h Y hctx
    exact Sec16.exists_qStar_le_normalizer (h153 G A c L h) (hobs G A c L h) hctx.mem_y0Star)
    h1411 h146 hq0 hT hcy

end CFSG.RankThree.PartTwo.Sec15
