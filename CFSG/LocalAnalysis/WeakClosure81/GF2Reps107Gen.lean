module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Base
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107GenAux1
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Sev
import CFSG.GH74.Orders.LieType
import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise ArithmeticFunction.Omega

private theorem w107_card_of_lieModel_u43 {S : Type} [Group S]
    (h : LieModel S .PSU 4 3 1) : Nat.card S = 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
  rw [CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1)
    (by norm_num) (by norm_num) h]
  decide

private theorem w107_card_outer_u43 {S : Type} [Group S]
    (h : LieModel S .PSU 4 3 1) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 ^ 3 := by
  have hcl : StatedClassicalModel S .PSU 4 3 1 := h.statedClassicalModel (by decide)
  have hcard :=
    (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound S 4 3 1 hcl).2.2.1
  norm_num at hcard
  rw [hcard]
  norm_num

private theorem w107_card_mulAut_dvd {S : Type} [Group S] [Finite S]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 ^ 3) :
    Nat.card (MulAut S) ∣ Nat.card S * 2 ^ 3 := by
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) ∣
      Nat.card S := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    exact Subgroup.card_range_dvd _
  rw [← Subgroup.card_mul_index
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S), Subgroup.index_eq_card]
  exact mul_dvd_mul hinner hout

private theorem w107_commSub_normalClosure_eq_top {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    {t : MulAut W} (ht2 : orderOf t = 2) :
    commSub (⊤ : Subgroup W)
      (Subgroup.closure {s : MulAut W | ∃ g ∈ Y, s = g⁻¹ * t * g}) = ⊤ := by
  classical
  set S : Set (MulAut W) := {s | ∃ g ∈ Y, s = g⁻¹ * t * g} with hSdef
  set N : Subgroup (MulAut W) := Subgroup.closure S with hNdef
  have hNnormal : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    rw [hNdef] at hn ⊢
    refine Subgroup.closure_induction (p := fun n _ => y * n * y⁻¹ ∈ Subgroup.closure S)
      ?_ ?_ ?_ ?_ hn
    · rintro s ⟨g, hg, rfl⟩
      refine Subgroup.subset_closure ⟨g * y⁻¹, Y.mul_mem hg (Y.inv_mem hy), ?_⟩
      group
    · simp
    · intro a b _ _ iha ihb
      rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group]
      exact Subgroup.mul_mem _ iha ihb
    · intro a _ iha
      rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ iha
  have hstabY : StableUnder Y (commSub (⊤ : Subgroup W) N) :=
    stableUnder_commSub (H := Y) (X := N) hNnormal (fun _ _ _ _ => Subgroup.mem_top _)
  have hstabL : StableUnder L (commSub (⊤ : Subgroup W) N) :=
    fun l hl => hstabY l (hctx.2.2.1 hl)
  obtain ⟨-, -, -, -, -, hIrr⟩ := hctx
  rcases hIrr.2.2.2 (commSub (⊤ : Subgroup W) N) hstabL bot_le le_top with hbot | htop
  · exfalso
    have hfix : (⊤ : Subgroup W) ≤ fixV N := commSub_eq_bot_iff.mp hbot
    have htN : t ∈ N := by
      rw [hNdef]
      exact Subgroup.subset_closure ⟨1, Y.one_mem, by simp⟩
    have ht1 : t = 1 := by
      ext w
      exact mem_fixV.mp (hfix (Subgroup.mem_top w)) t htN
    rw [ht1, orderOf_one] at ht2
    norm_num at ht2
  · exact htop

private theorem w107_card_dvd_of_ctx {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hU : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1)
    (hZ : Nat.card (Subgroup.center ↥L) = 3) :
    Nat.card ↥Y ∣ 3 * (2 ^ 10 * 3 ^ 6 * 5 * 7) := by
  classical
  have hLY : L ≤ Y := hctx.2.2.1
  have : (L.subgroupOf Y).Normal := w135_normal_of_ctx hctx
  let e : L.subgroupOf Y ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  let ρ : ↥Y →* MulAut ↥L :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L.subgroupOf Y))
  have hgen : L.subgroupOf Y = genFittingFStar ↥Y := by
    obtain ⟨-, -, -, hF, -, -⟩ := hctx
    rw [← hF, Fstar]
    exact Subgroup.comap_map_eq_self_of_injective (f := Y.subtype) Y.subtype_injective _
  have hker_cent : ∀ y : ρ.ker, ((y : ↥Y)) ∈
      Subgroup.centralizer (((L.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) := by
    intro y
    have hy1 : MulAut.conjNormal (H := L.subgroupOf Y) (y : ↥Y) = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one]
      exact y.2
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h3 : MulAut.conjNormal (H := L.subgroupOf Y) (y : ↥Y) (⟨l, hl⟩ : L.subgroupOf Y) =
        ⟨l, hl⟩ := by
      rw [hy1]; rfl
    have h4 : (y : ↥Y) * l * (y : ↥Y)⁻¹ = l := by
      simpa [MulAut.conjNormal_apply] using congrArg Subtype.val h3
    calc l * (y : ↥Y) = ((y : ↥Y) * l * (y : ↥Y)⁻¹) * (y : ↥Y) := by rw [h4]
      _ = (y : ↥Y) * l := by group
  have hkerL : ρ.ker ≤ L.subgroupOf Y := by
    intro y hy
    have hle : Subgroup.centralizer (((L.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) ≤
        genFittingFStar ↥Y := by
      simpa [hgen] using
        (CFSG.ClassicalInvolution.Q3.centralizer_genFittingFStar_le (X := ↥Y))
    have hmem : (y : ↥Y) ∈ genFittingFStar ↥Y := hle (hker_cent ⟨y, hy⟩)
    rwa [← hgen] at hmem
  have hcenterL : ∀ y : ρ.ker,
      Subgroup.inclusion hkerL y ∈ Subgroup.center (L.subgroupOf Y) := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have h := (Subgroup.mem_centralizer_iff.mp (hker_cent y)) (l : ↥Y) l.2
    simpa using h
  have hcenter : ∀ y : ρ.ker, e (Subgroup.inclusion hkerL y) ∈ Subgroup.center ↥L := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp (hcenterL y) g'
  let ψ : ρ.ker →* Subgroup.center ↥L :=
    (e.toMonoidHom.comp (Subgroup.inclusion hkerL)).codRestrict (Subgroup.center ↥L) hcenter
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h2 : e (Subgroup.inclusion hkerL a) = e (Subgroup.inclusion hkerL b) :=
      congrArg Subtype.val hab
    exact Subgroup.inclusion_injective hkerL (e.injective h2)
  have hker3 : Nat.card ρ.ker ∣ 3 := by
    have h := Subgroup.card_dvd_of_injective ψ hψinj
    rwa [hZ] at h
  have hrange : Nat.card ρ.range ∣ 2 ^ 10 * 3 ^ 6 * 5 * 7 := by
    have h1 : Nat.card ρ.range ∣ Nat.card (MulAut ↥L) := Subgroup.card_subgroup_dvd_card ρ.range
    have h2 : Nat.card (MulAut ↥L) ∣ Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) := by
      have : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1
      exact Subgroup.card_dvd_of_injective
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L)
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L)
    have h3 : Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) ∣
        (2 ^ 7 * 3 ^ 6 * 5 * 7) * 2 ^ 3 := by
      have hS := w107_card_mulAut_dvd (S := ↥L ⧸ Subgroup.center ↥L) (w107_card_outer_u43 hU)
      rwa [w107_card_of_lieModel_u43 hU] at hS
    calc Nat.card ρ.range ∣ Nat.card (MulAut ↥L) := h1
      _ ∣ Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) := h2
      _ ∣ (2 ^ 7 * 3 ^ 6 * 5 * 7) * 2 ^ 3 := h3
      _ = 2 ^ 10 * 3 ^ 6 * 5 * 7 := by norm_num
  have hcardY : Nat.card ↥Y = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [← Subgroup.card_mul_index (H := ρ.ker), Subgroup.index_ker]
  rw [hcardY]
  exact mul_dvd_mul hker3 hrange

theorem w107_rk_le_fifty_seven {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hU : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1)
    (hZ : Nat.card (Subgroup.center ↥L) = 3) {t : MulAut W} (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) : rk W ≤ 57 := by
  classical
  set S : Set (MulAut W) := {s | ∃ g ∈ Y, s = g⁻¹ * t * g} with hSdef
  have htop : commSub (⊤ : Subgroup W) (Subgroup.closure S) = ⊤ := by
    rw [hSdef]
    exact w107_commSub_normalClosure_eq_top hctx ht2
  have hSle : ∀ s ∈ S, rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers s)) ≤ 3 := by
    intro s hs
    rw [hSdef] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    rw [rk_commSub_zpowers_conj hW t g]
    exact w107_rk_commSub_zpowers_le_three hm
  have hTsub : (↑((Set.toFinite S).toFinset) : Set (MulAut W)) ⊆ S := by
    intro x hx
    rwa [Set.Finite.coe_toFinset] at hx
  have hchain := w107_rk_commSub_closure_le (W := W) 3 S hSle (Set.toFinite S).toFinset hTsub
  rw [Set.Finite.coe_toFinset] at hchain
  have hNle : Subgroup.closure S ≤ Y := by
    rw [Subgroup.closure_le]
    rintro s ⟨g, hg, rfl⟩
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem hg) htY) hg
  have hdvd : Nat.card ↥(Subgroup.closure S) ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hNle
  have hOm : Ω (Nat.card ↥(Subgroup.closure S)) ≤ 19 :=
    w107_cardFactors_le_nineteen (hdvd.trans (w107_card_dvd_of_ctx hctx hU hZ))
  calc rk W = rk ↥(commSub (⊤ : Subgroup W) (Subgroup.closure S)) := by rw [htop, rk_top]
    _ ≤ 3 * Ω (Nat.card ↥(Subgroup.closure S)) := hchain
    _ ≤ 3 * 19 := Nat.mul_le_mul_left 3 hOm
    _ = 57 := by norm_num

end CFSG.LocalAnalysis.WeakClosure81
