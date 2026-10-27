module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Inner
import CFSG.RankThree.PartTwo.Sec14.Ronan148JTools
import CFSG.RankThree.PartTwo.Sec14.Ronan148NCentTools
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofImg
import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
import CFSG.RankThree.PartTwo.Sec10.Item101
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec14.Main148
  CFSG.RankThree.PartTwo.Sec14.HJRes2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Res148BD4

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_zpowers_eq {a : G} (ha : a ∈ A) :
    img148 A Y (Subgroup.zpowers a) = Subgroup.zpowers (alpha148 A Y a ha) := by
  refine le_antisymm (img148_zpowers_le ha) ?_
  rw [Subgroup.zpowers_le]
  exact mem_img148_iff.mpr ⟨a, Subgroup.mem_sup_right ha, Subgroup.mem_zpowers a, rfl⟩

omit [Finite G] in
theorem mem_centralizer_img148 {X : Subgroup G} {g : G} (hg : g ∈ Y ⊔ A)
    (hXg : X ≤ Subgroup.centralizer ({g} : Set G)) :
    img148 A Y X ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  intro x hx
  obtain ⟨w, hwM, hwX, rfl⟩ := mem_img148_iff.mp hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hXg hwX))

theorem img148_le_pPrimeCoreOf148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) {J W : Subgroup G} (hJY : J ≤ Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {e b : G} (he : e ∈ A) (hb : b ∈ A)
    (hWJ : W ≤ J)
    (hWc : W ≤ Subgroup.centralizer ((Subgroup.closure ({e, b} : Set G) : Subgroup G) : Set G))
    (hWO : W ≤ pPrimeCoreOf 3
      (Y ⊓ Subgroup.centralizer ((Subgroup.closure ({e, b} : Set G) : Subgroup G) : Set G))) :
    img148 A Y W ≤ pPrimeCoreOf 3 (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} ⊓
      Subgroup.centralizer {alpha148 A Y b hb}) := by
  set D : Subgroup G := Subgroup.closure ({e, b} : Set G) with hDdef
  have hDA : D ≤ A := by
    rw [hDdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact he
    · exact hb
  have hD3 : IsPGroup 3 D := isPGroup_three_of_pow148 fun d hd => hA3 d (hDA hd)
  set O := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (D : Set G)) with hOdef
  set M := img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} ⊓
    Subgroup.centralizer {alpha148 A Y b hb} with hMdef
  set X := img148 A Y O ⊓ M with hXdef
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hOM : O ≤ Y ⊔ A := (pPrimeCoreOf_le 3 _).trans (inf_le_left.trans le_sup_left)
  have heD : e ∈ D := Subgroup.subset_closure (Set.mem_insert e _)
  have hbD : b ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem e rfl)
  have hWX : img148 A Y W ≤ X := by
    refine le_inf (img148_mono hWO) (le_inf (le_inf (img148_mono hWJ) ?_) ?_)
    · exact mem_centralizer_img148 (Subgroup.mem_sup_right he)
        (hWc.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heD)))
    · exact mem_centralizer_img148 (Subgroup.mem_sup_right hb)
        (hWc.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbD)))
  refine hWX.trans (le_pPrimeCoreOf inf_le_right (fun m hm => ?_) ?_)
  · refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hm⟩
    obtain ⟨⟨hmJ, hme⟩, hmb⟩ := hm
    have hcomm : ∀ (g : G) (hg : g ∈ ({e, b} : Set G)),
        QuotientGroup.mk' (ker148 A Y) (⟨g, (Set.pair_subset (Subgroup.mem_sup_right he)
          (Subgroup.mem_sup_right hb)) hg⟩ : ↥(Y ⊔ A)) ∈
        Subgroup.centralizer ((Subgroup.zpowers m : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rcases hg with rfl | rfl
      · exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
          (show m ∈ Subgroup.centralizer {alpha148 A Y g he} from hme)) k).eq
      · exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
          (show m ∈ Subgroup.centralizer {alpha148 A Y g hb} from hmb)) k).eq
    have hDm := Ronan148J.img148_closure_le_centralizer
      (Set.pair_subset (Subgroup.mem_sup_right he) (Subgroup.mem_sup_right hb)) hcomm
    have hmD : m ∈ Subgroup.centralizer (img148 A Y D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact ((Subgroup.mem_centralizer_iff.mp (hDm hx) m (Subgroup.mem_zpowers m))).symm
    obtain ⟨x, hxM, hxJ, hxD, rfl⟩ :=
      Ronan148N.exists_lift_centralizer148 hAY hJY hDA (hDA.trans hAJ) hD3 hmJ hmD
    have hxO : x ∈ Subgroup.normalizer (O : Set G) :=
      le_normalizer_pPrimeCoreOf 3 _ ⟨hJY hxJ, hxD⟩
    exact img148_le_normalizer (Subgroup.zpowers_le.mpr hxO)
      (mem_img148_iff.mpr ⟨x, hxM, Subgroup.mem_zpowers x, rfl⟩)
  · exact Nat.Coprime.coprime_dvd_right
      ((Subgroup.card_dvd_of_le inf_le_left).trans (card_img148_dvd hOM))
      (coprime_card_pPrimeCoreOf 3 _)

theorem mem_sup_of_alpha148_mem148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) {J W : Subgroup G} (hJY : J ≤ Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {b : G} (hb : b ∈ A)
    (hWb : W ≤ Subgroup.centralizer ({b} : Set G)) (hWM : W ≤ Y ⊔ A)
    (hmem : alpha148 A Y b hb ∈
      ⁅img148 A Y W, img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y b hb}⁆) :
    b ∈ ⁅W, Subgroup.centralizer ({b} : Set G)⁆ ⊔
      (pPrimeCoreOf 3 Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  rw [img148_inf_centralizer_alpha148 hAY hJM hAJ hb (hA3 b hb),
    ← img148_commutator_eq hWM (inf_le_left.trans hJM)] at hmem
  obtain ⟨w, hwM, hwmem, hwb⟩ := mem_img148_iff.mp hmem
  have hwO : w⁻¹ * b ∈ pPrimeCoreOf 3 Y :=
    mk'_ker148_eq_iff.mp (hwb.trans (alpha148_eq_mk' hb))
  have hcomC : ⁅W, J ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
      Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact (Subgroup.centralizer ({b} : Set G)).mul_mem
      ((Subgroup.centralizer ({b} : Set G)).mul_mem
        ((Subgroup.centralizer ({b} : Set G)).mul_mem (hWb hx) hy.2)
        ((Subgroup.centralizer ({b} : Set G)).inv_mem (hWb hx)))
      ((Subgroup.centralizer ({b} : Set G)).inv_mem hy.2)
  have hwC : w ∈ Subgroup.centralizer ({b} : Set G) := hcomC hwmem
  have hw' : w ∈ ⁅W, Subgroup.centralizer ({b} : Set G)⁆ :=
    Subgroup.commutator_mono le_rfl inf_le_right hwmem
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hR : w⁻¹ * b ∈ pPrimeCoreOf 3 Y ⊓ Subgroup.centralizer ({b} : Set G) :=
    ⟨hwO, (Subgroup.centralizer ({b} : Set G)).mul_mem
      ((Subgroup.centralizer ({b} : Set G)).inv_mem hwC) hbC⟩
  set M := ⁅W, Subgroup.centralizer ({b} : Set G)⁆ ⊔
    (pPrimeCoreOf 3 Y ⊓ Subgroup.centralizer ({b} : Set G)) with hMdef
  have h1 : w ∈ M := (le_sup_left : ⁅W, Subgroup.centralizer ({b} : Set G)⁆ ≤ M) hw'
  have h2 : w⁻¹ * b ∈ M :=
    (le_sup_right : pPrimeCoreOf 3 Y ⊓ Subgroup.centralizer ({b} : Set G) ≤ M) hR
  have hmul := M.mul_mem h1 h2
  simpa using hmul

end Quot

theorem commutator_zpowers_eq148 {A D W : Subgroup G} (hA : Late.IsE27 A) (hD : IsHyperplane A D)
    {a : G} (haA : a ∈ A) (haD : a ∉ D) (hWD : W ≤ Subgroup.centralizer (D : Set G))
    (hWA : W = ⁅W, A⁆) : W = ⁅W, Subgroup.zpowers a⁆ := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA' : A = Subgroup.zpowers a ⊔ D := by
    rw [sup_comm]
    exact Proof1418Res2.eq_sup_zpowers_of_not_mem hA hD haA haD
  have hle : ⁅W, A⁆ ≤ ⁅W, Subgroup.zpowers a⁆ := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    rw [hA'] at hx
    obtain ⟨k, d, hd, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers
      (fun d hd => hAc d (hD.1 hd) a haA) hx
    have hwd : w * d = d * w := (Subgroup.mem_centralizer_iff.mp (hWD hw) d hd).symm
    have key : ⁅w, a ^ k * d⁆ = ⁅w, a ^ k⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc w * (a ^ k * d) * w⁻¹ * (a ^ k * d)⁻¹ = w * a ^ k * (d * w⁻¹) * d⁻¹ * a ^ (-k) := by
            group
        _ = w * a ^ k * (w⁻¹ * d) * d⁻¹ * a ^ (-k) := by
            rw [show d * w⁻¹ = w⁻¹ * d by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hwd, ← mul_assoc, inv_mul_cancel, one_mul]]
        _ = w * a ^ k * w⁻¹ * (a ^ k)⁻¹ := by group
    rw [key]
    exact Subgroup.commutator_mem_commutator hw (Subgroup.zpow_mem_zpowers a k)
  refine le_antisymm (hWA.le.trans hle) ?_
  calc ⁅W, Subgroup.zpowers a⁆ ≤ ⁅W, A⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr haA)
    _ = W := hWA.symm

theorem center_eq_bot_of_trialityD4
    {S : Type} [Group S] {n : ℕ} (hm : ChevalleyExceptionalModel S .trialityD4 2 n) :
    Subgroup.center S = ⊥ := by
  obtain ⟨K, _, _, _, σ, hK, hσ, -, hf, -, ⟨φ⟩⟩ :=
    Sec4.Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  rw [eq_bot_iff]
  intro x hx
  have hφx : φ x ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [hZ, Subgroup.mem_bot] at hφx
  rw [Subgroup.mem_bot]
  exact φ.injective (hφx.trans φ.map_one.symm)

end Res148BD4

open Res148BD4

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
