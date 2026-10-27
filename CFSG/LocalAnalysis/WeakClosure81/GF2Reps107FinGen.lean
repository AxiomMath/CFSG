module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107TripleDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Sev
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)

theorem w107_rk_le_three_mul_rk_commSub {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hgen : U43TripleGen) {K : Subgroup (MulAut W)}
    (hq : IsQuasisimple ↥K) (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hLie : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 4 3 1)
    (htop : commSub (⊤ : Subgroup W) K = ⊤) {d : MulAut W} (hdK : d ∈ K) (hd2 : d ^ 2 = 1)
    (hd1 : d ≠ 1) :
    rk W ≤ 3 * rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  let δ : ↥K := ⟨d, hdK⟩
  have hdord : orderOf d = 2 := orderOf_eq_prime hd2 hd1
  have hδord : orderOf δ = 2 := by rw [← Subgroup.orderOf_coe δ]; exact hdord
  have hδ2 : δ ^ 2 = 1 := by rw [← hδord]; exact pow_orderOf_eq_one δ
  have hπδ : π δ ≠ 1 := by
    intro h
    have hmem : δ ∈ Subgroup.center ↥K := by
      have h' : (δ : ↥K ⧸ Subgroup.center ↥K) = 1 := h
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥K) δ).mp h'
    have h2 : orderOf (⟨δ, hmem⟩ : ↥(Subgroup.center ↥K)) = 2 := by
      rw [Subgroup.orderOf_mk, hδord]
    have hdvd := orderOf_dvd_natCard (⟨δ, hmem⟩ : ↥(Subgroup.center ↥K))
    rw [h2] at hdvd
    exact absurd hdvd hZ.not_two_dvd_nat
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
    refine CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.eq_top_of_mul_center
      hq.1.commutator_eq_top (fun k => ?_)
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
    have hcomm12 : commSub (⊤ : Subgroup W)
        (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ⊔ Subgroup.zpowers u₃) ≤
        commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) ⊔
          commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃) := by
      have h := CFSG.Quasithin.Asc81c.Pf.commSub_iSup (W := W)
        (fun b : Bool => cond b (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂)
          (Subgroup.zpowers u₃))
      rw [iSup_bool_eq, iSup_bool_eq] at h
      exact h.le
    have hcomm123 : commSub (⊤ : Subgroup W)
        (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) ≤
        commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
          commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂) := by
      have h := CFSG.Quasithin.Asc81c.Pf.commSub_iSup (W := W)
        (fun b : Bool => cond b (Subgroup.zpowers u₁) (Subgroup.zpowers u₂))
      rw [iSup_bool_eq, iSup_bool_eq] at h
      exact h.le
    calc commSub (⊤ : Subgroup W) K
        ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ⊔
            Subgroup.zpowers u₃) := commSub_mono le_rfl hKle
      _ ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃) := hcomm12
      _ ≤ (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃) :=
          sup_le_sup_right hcomm123 _
  have hrk₁ : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁)) =
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
    have harg : ((a' : MulAut W)⁻¹)⁻¹ * d * (a' : MulAut W)⁻¹ = u₁ := by
      rw [inv_inv, hu₁def]
    have hc := rk_commSub_zpowers_conj hW d (a' : MulAut W)⁻¹
    rw [harg] at hc
    exact hc
  have hrk₂ : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) =
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
    have harg : ((b' : MulAut W)⁻¹)⁻¹ * d * (b' : MulAut W)⁻¹ = u₂ := by
      rw [inv_inv, hu₂def]
    have hc := rk_commSub_zpowers_conj hW d (b' : MulAut W)⁻¹
    rw [harg] at hc
    exact hc
  have hrk₃ : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃)) =
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
    have harg : ((c' : MulAut W)⁻¹)⁻¹ * d * (c' : MulAut W)⁻¹ = u₃ := by
      rw [inv_inv, hu₃def]
    have hc := rk_commSub_zpowers_conj hW d (c' : MulAut W)⁻¹
    rw [harg] at hc
    exact hc
  have hsum : rk ↥((commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
      commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ⊔
      commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃)) ≤
      3 * rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := by
    have h12 := rk_sup_add_rk_inf (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁))
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂))
    have h123 := rk_sup_add_rk_inf (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
      commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂))
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃))
    omega
  calc rk W = rk ↥(commSub (⊤ : Subgroup W) K) := by rw [htop, rk_top]
    _ ≤ rk ↥((commSub (⊤ : Subgroup W) (Subgroup.zpowers u₁) ⊔
          commSub (⊤ : Subgroup W) (Subgroup.zpowers u₂)) ⊔
          commSub (⊤ : Subgroup W) (Subgroup.zpowers u₃)) := rk_mono hcomm_le
    _ ≤ 3 * rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers d)) := hsum

end CFSG.LocalAnalysis.WeakClosure81
