module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107TripleDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Three
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Sev
import CFSG.GroupTheory.E3Params
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

private lemma w107t_commutator_mul_center {X : Type*} [Group X] {k₁ k₂ z₁ z₂ : X}
    (hz₁ : z₁ ∈ Subgroup.center X) (hz₂ : z₂ ∈ Subgroup.center X) :
    ⁅k₁ * z₁, k₂ * z₂⁆ = ⁅k₁, k₂⁆ := by
  have hz₁c : ∀ x, Commute z₁ x := fun x => (Subgroup.mem_center_iff.1 hz₁ x).symm
  have hz₂c : ∀ x, Commute x z₂ := fun x => (Subgroup.mem_center_iff.1 hz₂ x)
  calc ⁅k₁ * z₁, k₂ * z₂⁆
      = k₁ * ⁅z₁, k₂ * z₂⁆ * k₁⁻¹ * ⁅k₁, k₂ * z₂⁆ :=
        commutatorElement_mul_left_eq_conj_mul k₁ z₁ (k₂ * z₂)
    _ = k₁ * 1 * k₁⁻¹ * ⁅k₁, k₂ * z₂⁆ := by
        rw [(hz₁c (k₂ * z₂)).commutator_eq]
    _ = k₁ * 1 * k₁⁻¹ * (⁅k₁, k₂⁆ * k₂ * ⁅k₁, z₂⁆ * k₂⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj]
    _ = ⁅k₁, k₂⁆ := by
        rw [(hz₂c k₁).commutator_eq]
        group

private lemma w107t_eq_top_of_mul_center {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    {H : Subgroup X} (h : ∀ x : X, ∃ k ∈ H, ∃ z ∈ Subgroup.center X, x = k * z) :
    H = ⊤ := by
  rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := h a
  obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := h b
  rw [w107t_commutator_mul_center hz₁ hz₂]
  exact H.mul_mem (H.mul_mem (H.mul_mem hk₁ hk₂) (H.inv_mem hk₁)) (H.inv_mem hk₂)

private lemma w107t_commSub_top_sup_le {W : Type} [CommGroup W]
    (X Y : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (X ⊔ Y) ≤
      commSub (⊤ : Subgroup W) X ⊔ commSub (⊤ : Subgroup W) Y := by
  have h := CFSG.Quasithin.Asc81c.Pf.commSub_iSup (fun b : Bool => cond b X Y)
  rw [iSup_bool_eq, iSup_bool_eq] at h
  exact h.le

private lemma w107t_rk_sup_le {W : Type} [CommGroup W] [Finite W]
    (U V : Subgroup W) : rk ↥(U ⊔ V) ≤ rk U + rk V := by
  have h := rk_sup_add_rk_inf U V
  omega

private lemma w107t_rk_commSub_zpowers_le_two {W : Type} [CommGroup W] [Finite W]
    {d : MulAut W} (hcost : E3.mQuot ⊤ (fixV (Subgroup.zpowers d)) ≤ 2) :
    rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) ≤ 2 := by
  rw [← commV_eq_commSub, ← rkIdx_fixV_zpowers, ← CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  exact hcost

theorem w107_false_of_involution_cost_two {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hgen : U43TripleGen) {K : Subgroup (MulAut W)}
    (hq : IsQuasisimple ↥K) (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (hLie : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 4 3 1)
    (htop : commSub (⊤ : Subgroup W) K = ⊤) {d : MulAut W} (hdK : d ∈ K) (hd2 : orderOf d = 2)
    (hcost : E3.mQuot ⊤ (fixV (Subgroup.zpowers d)) ≤ 2) : False := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  let δ : ↥K := ⟨d, hdK⟩
  have hd2' : d ^ 2 = 1 := by rw [← hd2]; exact pow_orderOf_eq_one d
  have hδord : orderOf δ = 2 := by rw [← Subgroup.orderOf_coe δ]; exact hd2
  have hδ2 : δ ^ 2 = 1 := by rw [← hδord]; exact pow_orderOf_eq_one δ
  have hπδ : π δ ≠ 1 := by
    intro h
    have hmem : δ ∈ Subgroup.center ↥K := by
      have h' : (δ : ↥K ⧸ Subgroup.center ↥K) = 1 := h
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥K) δ).mp h'
    have h2 : orderOf (⟨δ, hmem⟩ : ↥(Subgroup.center ↥K)) = 2 := by
      rw [Subgroup.orderOf_mk, hδord]
    have hdvd := orderOf_dvd_natCard (⟨δ, hmem⟩ : ↥(Subgroup.center ↥K))
    rw [h2, hZ] at hdvd
    exact absurd hdvd (by norm_num)
  have hπδ2 : (π δ) ^ 2 = 1 := by rw [← map_pow, hδ2, map_one]
  obtain ⟨a, b, c, habc⟩ :=
    hgen (↥K ⧸ Subgroup.center ↥K) hLie (π δ) hπδ2 hπδ
  obtain ⟨a', ha'⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk_surjective b
  obtain ⟨c', hc'⟩ := QuotientGroup.mk_surjective c
  have hπa : π a' = a := ha'
  have hπb : π b' = b := hb'
  have hπc : π c' = c := hc'
  set t₁ : ↥K := a' * δ * a'⁻¹ with ht₁
  set t₂ : ↥K := b' * δ * b'⁻¹ with ht₂
  set t₃ : ↥K := c' * δ * c'⁻¹ with ht₃
  set H : Subgroup ↥K := Subgroup.closure ({t₁, t₂, t₃} : Set ↥K) with hHdef
  set u₁ : MulAut W := (a' : MulAut W) * d * (a' : MulAut W)⁻¹ with hu₁def
  set u₂ : MulAut W := (b' : MulAut W) * d * (b' : MulAut W)⁻¹ with hu₂def
  set u₃ : MulAut W := (c' : MulAut W) * d * (c' : MulAut W)⁻¹ with hu₃def
  have hπt₁ : π t₁ = a * π δ * a⁻¹ := by
    rw [ht₁, map_mul, map_mul, map_inv, hπa]
  have hπt₂ : π t₂ = b * π δ * b⁻¹ := by
    rw [ht₂, map_mul, map_mul, map_inv, hπb]
  have hπt₃ : π t₃ = c * π δ * c⁻¹ := by
    rw [ht₃, map_mul, map_mul, map_inv, hπc]
  have himg : π '' ({t₁, t₂, t₃} : Set ↥K) =
      ({a * π δ * a⁻¹, b * π δ * b⁻¹, c * π δ * c⁻¹} : Set (↥K ⧸ Subgroup.center ↥K)) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hπt₁, hπt₂, hπt₃]
  have hmap : H.map π = ⊤ := by
    rw [hHdef, MonoidHom.map_closure, himg, habc]
  have hH : H = ⊤ := by
    refine w107t_eq_top_of_mul_center hq.1 (fun k => ?_)
    have hmemtop : π k ∈ H.map π := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨h, hhH, hhk⟩ := Subgroup.mem_map.mp hmemtop
    have hzk : h⁻¹ * k ∈ Subgroup.center ↥K := by
      have h1 : π (h⁻¹ * k) = 1 := by rw [map_mul, map_inv, hhk, inv_mul_cancel]
      have h2 : (h⁻¹ * k : ↥K ⧸ Subgroup.center ↥K) = 1 := h1
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥K) (h⁻¹ * k)).mp h2
    exact ⟨h, hhH, h⁻¹ * k, hzk, by group⟩
  have hKtop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hu₁ : K.subtype t₁ = u₁ := by rw [ht₁, hu₁def]; rfl
  have hu₂ : K.subtype t₂ = u₂ := by rw [ht₂, hu₂def]; rfl
  have hu₃ : K.subtype t₃ = u₃ := by rw [ht₃, hu₃def]; rfl
  have himg2 : K.subtype '' ({t₁, t₂, t₃} : Set ↥K) =
      ({u₁, u₂, u₃} : Set (MulAut W)) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hu₁, hu₂, hu₃]
  have hsub : H.map K.subtype = Subgroup.closure ({u₁, u₂, u₃} : Set (MulAut W)) := by
    rw [hHdef, MonoidHom.map_closure, himg2]
  have hclosure : Subgroup.closure ({u₁, u₂, u₃} : Set (MulAut W)) = K := by
    rw [← hsub, hH, hKtop]
  have hKle : K ≤ Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ⊔ Subgroup.zpowers u₃ := by
    rw [← hclosure, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers u₁))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₂))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u₃)
  have hcomm_le : commSub (⊤ : Subgroup W) K ≤
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
        commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ⊔
        commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃) := by
    calc commSub (⊤ : Subgroup W) K
        ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ⊔
            Subgroup.zpowers u₃) := commSub_mono le_rfl hKle
      _ ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃) :=
          w107t_commSub_top_sup_le _ _
      _ ≤ (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃) :=
          sup_le_sup_right (w107t_commSub_top_sup_le _ _) _
  have hrk₁ : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁)) ≤ 2 := by
    have h : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁)) =
        rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
      have harg : ((a' : MulAut W)⁻¹)⁻¹ * d * (a' : MulAut W)⁻¹ = u₁ := by
        rw [inv_inv, hu₁def]
      have hc := rk_commSub_zpowers_conj hW d (a' : MulAut W)⁻¹
      rw [harg] at hc
      exact hc
    rw [h]
    exact w107t_rk_commSub_zpowers_le_two hcost
  have hrk₂ : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ≤ 2 := by
    have h : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) =
        rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
      have harg : ((b' : MulAut W)⁻¹)⁻¹ * d * (b' : MulAut W)⁻¹ = u₂ := by
        rw [inv_inv, hu₂def]
      have hc := rk_commSub_zpowers_conj hW d (b' : MulAut W)⁻¹
      rw [harg] at hc
      exact hc
    rw [h]
    exact w107t_rk_commSub_zpowers_le_two hcost
  have hrk₃ : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃)) ≤ 2 := by
    have h : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃)) =
        rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
      have harg : ((c' : MulAut W)⁻¹)⁻¹ * d * (c' : MulAut W)⁻¹ = u₃ := by
        rw [inv_inv, hu₃def]
      have hc := rk_commSub_zpowers_conj hW d (c' : MulAut W)⁻¹
      rw [harg] at hc
      exact hc
    rw [h]
    exact w107t_rk_commSub_zpowers_le_two hcost
  have hsup_le : rk ↥((commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
      commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ⊔
      commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃)) ≤ 6 := by
    have h12 := w107t_rk_sup_le (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁))
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂))
    have h123 := w107t_rk_sup_le (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
      commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂))
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃))
    omega
  have hrkW : rk W ≤ 6 := by
    calc rk W = rk ↥(commSub (⊤ : Subgroup W) K) := by rw [htop, rk_top]
      _ ≤ rk ↥((commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃)) := rk_mono hcomm_le
      _ ≤ 6 := hsup_le
  exact w107_false_of_rk_le_six hW hLie hrkW

end CFSG.LocalAnalysis.WeakClosure81
