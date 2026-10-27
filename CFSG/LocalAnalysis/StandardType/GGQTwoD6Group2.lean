module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Group
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardAL

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace QTwoD6

open CFSG.StandardType.QTwoLin

private lemma ggQ2d6l_coord_reflLin {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {F : N.V ≃ₗ[ZMod 3] V7} (φ : MulAut ↥Bs)
    (h : GGIsReflection 3 φ) : IsReflLin (ggCoord N F φ) := by
  have : Finite N.V := Finite.of_equiv (Additive ↥Bs) N.model.toEquiv
  obtain ⟨c, f, hc, hf⟩ := exists_of_ggIsReflection (p := 3) N.model h
  have heq : ggLin (p := 3) N.model φ = Module.reflection hc :=
    ggLin_eq_reflection N.model hc hf
  have hstd : CFSG.StandardType.IsReflLin (ggLinConj F (ggLin (p := 3) N.model φ)) :=
    (ggLinConj_isReflLin F (ggLin N.model φ)).mpr ⟨c, f, hc, heq⟩
  have : IsReflLin (ggCoord N F φ) := by
    rw [isReflLin_iff_std]
    exact hstd
  exact this

private lemma ggQ2d6l_model_simple_refl {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y' : G} {K' : Subgroup G}
    (M' : GGQTwoModel 3 Bs x y' D L J K') (k : M'.ι) :
    GGIsReflection 3 (M'.simple k) := by
  have hfx : M'.root k (M'.coroot k) = 2 := by
    rw [M'.pairing k k, M'.isCartan.1 k]; norm_num
  exact ggIsReflection_of_eq_reflection (p := 3) (by norm_num) M'.model hfx
    (ggLin_eq_reflection M'.model hfx (M'.simple_apply k))

private lemma ggQ2d6l_coord_injective {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} (F : N.V ≃ₗ[ZMod 3] V7) :
    Function.Injective (ggCoord N F) := by
  intro φ ψ h
  have h' : ggLinConj F (ggLin N.model φ) = ggLinConj F (ggLin N.model ψ) := h
  exact ggLin_injective N.model ((ggLinConj F).injective h')

private lemma ggQ2d6l_mem_closure_iff {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} (F : N.V ≃ₗ[ZMod 3] V7) {x y : G} (hx : x ∈ Bs) (hy : y ∈ Bs)
    (d : ↥Bs) :
    (d : G) ∈ Subgroup.closure ({x, y} : Set G) ↔
      F (N.model (Additive.ofMul d)) ∈ Submodule.span (ZMod 3)
        {F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))),
         F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)))} := by
  have hmap : Subgroup.map (Subgroup.subtype Bs)
      (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs)) =
      Subgroup.closure ({x, y} : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨s, hs, hsx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with hs | hs
      · rw [← hsx, hs]; simp
      · rw [← hsx, hs]; simp
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · exact ⟨⟨x, hx⟩, by simp, hg.symm⟩
      · exact ⟨⟨y, hy⟩, by simp, hg.symm⟩
  have hmem : (d : G) ∈ Subgroup.closure ({x, y} : Set G) ↔
      d ∈ Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs) := by
    rw [← hmap, Subgroup.mem_map]
    constructor
    · rintro ⟨e, he, heq⟩
      have hed : e = d := Subtype.ext heq
      rw [hed] at he
      exact he
    · intro hd
      exact ⟨d, hd, rfl⟩
  rw [hmem]
  constructor
  · intro hd
    refine Subgroup.closure_induction
      (p := fun g _ => F (N.model (Additive.ofMul g)) ∈ Submodule.span (ZMod 3)
        {F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))),
         F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)))}) ?_ ?_ ?_ ?_ hd
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Submodule.mem_span_of_mem (by simp)
      · exact Submodule.mem_span_of_mem (by simp)
    · rw [show Additive.ofMul (1 : ↥Bs) = 0 from rfl, map_zero, map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [ofMul_mul, map_add, map_add]
      exact Submodule.add_mem _ ha hb
    · intro a _ ha
      rw [ofMul_inv, map_neg, map_neg]
      exact Submodule.neg_mem _ ha
  · intro hd
    rw [Submodule.mem_span_pair] at hd
    obtain ⟨c, e, hce⟩ := hd
    have h1 : c • F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) =
        F (N.model (Additive.ofMul ((⟨x, hx⟩ : ↥Bs) ^ c.val))) := by
      calc c • F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs)))
          = (c.val : ZMod 3) • F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) := by
              rw [show (c.val : ZMod 3) = c from ZMod.natCast_zmod_val c]
        _ = c.val • F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) :=
              Nat.cast_smul_eq_nsmul (ZMod 3) c.val _
        _ = F (c.val • N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) :=
              (AddMonoidHom.map_nsmul (F.toLinearMap.toAddMonoidHom) c.val _).symm
        _ = F (N.model (c.val • Additive.ofMul (⟨x, hx⟩ : ↥Bs))) := by
              rw [show N.model (c.val • Additive.ofMul (⟨x, hx⟩ : ↥Bs)) =
                c.val • N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) from
                AddMonoidHom.map_nsmul N.model.toAddMonoidHom c.val _]
        _ = F (N.model (Additive.ofMul ((⟨x, hx⟩ : ↥Bs) ^ c.val))) := by
              rw [ofMul_pow]
    have h2 : e • F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
        F (N.model (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ e.val))) := by
      calc e • F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)))
          = (e.val : ZMod 3) • F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) := by
              rw [show (e.val : ZMod 3) = e from ZMod.natCast_zmod_val e]
        _ = e.val • F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) :=
              Nat.cast_smul_eq_nsmul (ZMod 3) e.val _
        _ = F (e.val • N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) :=
              (AddMonoidHom.map_nsmul (F.toLinearMap.toAddMonoidHom) e.val _).symm
        _ = F (N.model (e.val • Additive.ofMul (⟨y, hy⟩ : ↥Bs))) := by
              rw [show N.model (e.val • Additive.ofMul (⟨y, hy⟩ : ↥Bs)) =
                e.val • N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) from
                AddMonoidHom.map_nsmul N.model.toAddMonoidHom e.val _]
        _ = F (N.model (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ e.val))) := by
              rw [ofMul_pow]
    have h3 : F (N.model (Additive.ofMul
        ((⟨x, hx⟩ : ↥Bs) ^ c.val * (⟨y, hy⟩ : ↥Bs) ^ e.val))) =
        F (N.model (Additive.ofMul d)) := by
      rw [ofMul_mul, map_add, map_add, ← h1, ← h2, hce]
    have h4 : (⟨x, hx⟩ : ↥Bs) ^ c.val * (⟨y, hy⟩ : ↥Bs) ^ e.val = d :=
      N.model.injective (F.injective h3)
    have hsx : (⟨x, hx⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    have hsy : (⟨y, hy⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    rw [← h4]
    exact Subgroup.mul_mem _ (pow_mem hsx c.val) (pow_mem hsy e.val)

private lemma ggQ2d6l_span_eq (ℓ : V7) (hℓ : ℓ ∈ Dplane)
    (hℓ0 : ℓ ∉ Submodule.span (ZMod 3) {e0}) :
    Submodule.span (ZMod 3) {ℓ, e0} = Dplane := by
  have hℓ' : ℓ ∈ Submodule.span (ZMod 3) ({e0, wb} : Set V7) := hℓ
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hℓ'
  have hb : b ≠ 0 := by
    intro hb0
    apply hℓ0
    rw [← hab, hb0, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e0))
  have hwb : wb = b⁻¹ • (ℓ - a • e0) := by
    have hb' : ℓ - a • e0 = b • wb := by rw [← hab]; abel
    rw [hb', smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hwb_mem : wb ∈ Submodule.span (ZMod 3) {ℓ, e0} := by
    rw [hwb]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  apply le_antisymm
  · rw [Submodule.span_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact hℓ
    · exact Submodule.subset_span (by simp)
  · rw [Dplane, Submodule.span_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact hwb_mem

theorem ggQ2d6_AL_reflGen {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y' : G} {K' : Subgroup G}
    (M' : GGQTwoModel 3 Bs x y' D L J K') {K : Subgroup G} {N : GGQ2NbrDatum 3 Bs K}
    {b : N.Λ} {y : G} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) :
    linAL L N Fr.F = Subgroup.closure {g | g ∈ linAL L N Fr.F ∧ IsReflLin g} := by
  have _ := hS
  apply le_antisymm
  · rw [linAL, M'.automizer_L, MonoidHom.map_closure, Set.image_image]
    apply Subgroup.closure_mono
    rintro g ⟨k, hk, rfl⟩
    exact ⟨Subgroup.mem_closure_of_mem ⟨k, hk, rfl⟩,
      ggQ2d6l_coord_reflLin (M'.simple k) (ggQ2d6l_model_simple_refl M' k)⟩
  · rw [Subgroup.closure_le]
    intro g hg
    exact hg.1

theorem ggQ2d6_card_AL {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) {y' : G} {K' : Subgroup G}
    (M' : GGQTwoModel 3 Bs x y' D L J K') {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hb : N.IsD6Fork b}
    {hy : y ∈ Bs} (hJ : ggAutomizer J Bs = Subgroup.closure (N.simple '' {k | k ≠ b}))
    (Fr : GGQ2D6Frame N b hy) : 1440 < Nat.card (linAL L N Fr.F) := by
  have _ := hnb
  have hcard : Nat.card (linAL L N Fr.F) = Nat.card ↥(ggAutomizer L Bs) := by
    rw [linAL]
    exact Subgroup.card_map_of_injective (ggQ2d6l_coord_injective Fr.F)
  rw [hcard]
  exact ggQ2_D6_card_AL_gt hS rfl N b hb hJ M'

theorem ggQ2d6_W6_sup_linAL_le_map {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {y : G} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) :
    W6 ⊔ linAL L N Fr.F ≤ (ggAutomizer (L ⊔ K) Bs).map (ggCoord N Fr.F) := by
  have _ := hS
  have hK : W6 ≤ (ggAutomizer K Bs).map (ggCoord N Fr.F) := by
    rw [W6, N.automizer_K, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro g ⟨i, rfl⟩
    exact (show simpleD6 i ∈ ggCoord N Fr.F '' Set.range N.simple from
      ⟨N.simple (Fr.e i), ⟨Fr.e i, rfl⟩, ggQ2_d6_coord_simple Fr i⟩)
  refine sup_le ?_ ?_
  · exact hK.trans (Subgroup.map_mono (ggAutomizer_mono Bs le_sup_right))
  · exact Subgroup.map_mono (ggAutomizer_mono Bs le_sup_left)

theorem ggQ2d6_mem_D_iff {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x : G}
    {D : Subgroup G} {y : G} {K : Subgroup G} {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ}
    {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) (hD : D = Subgroup.closure {x, y}) (hx : x ∈ Bs)
    (hell : ggEll N Fr.F hx ∈ Dplane)
    (hell0 : ggEll N Fr.F hx ∉ Submodule.span (ZMod 3) {e0}) (d : ↥Bs) :
    (d : G) ∈ D ↔ Fr.F (N.model (Additive.ofMul d)) ∈ Dplane := by
  have hspan : Submodule.span (ZMod 3)
      {Fr.F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))), e0} = Dplane := by
    rw [show Fr.F (N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) = ggEll N Fr.F hx from rfl]
    exact ggQ2d6l_span_eq (ggEll N Fr.F hx) hell hell0
  rw [hD, ← hspan]
  have hmain := ggQ2d6l_mem_closure_iff (N := N) Fr.F hx hy d
  simpa only [Fr.F_y] using hmain

theorem ggQ2d6_g1_stable {G : Type} [Group G] {Bs : Subgroup G} {y : G} (hy : y ∈ Bs)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) {φ : MulAut ↥Bs}
    (hφu : φ u ∈ Subgroup.zpowers u) :
    φ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  have hy_mem : (⟨y, hy⟩ : ↥Bs) ∈ Subgroup.zpowers u :=
    mem_zpowers_mk_of_coe_mem u.2 (hu.symm ▸ Subgroup.mem_zpowers y)
  have hu_mem : u ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) :=
    mem_zpowers_mk_of_coe_mem hy (hu ▸ Subgroup.mem_zpowers (u : G))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_mem
  have h1 : φ ⟨y, hy⟩ = (φ u) ^ k := by rw [← hk, map_zpow]
  have h2 : (φ u) ^ k ∈ Subgroup.zpowers u := by
    have := (Subgroup.zpowers_le (g := φ u) (H := Subgroup.zpowers u)).mpr hφu
    exact this (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have h3 : Subgroup.zpowers u ≤ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) :=
    Subgroup.zpowers_le.mpr hu_mem
  rw [h1]
  exact h3 h2

theorem ggQ2d6_phi_e0 {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G} {N :
    GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (Fr : GGQ2D6Frame N b hy) (φ : MulAut ↥Bs)
    (hfix : φ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs)) :
    ggCoord N Fr.F φ e0 ∈ Submodule.span (ZMod 3) {e0} := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfix
  have hcoord : ggCoord N Fr.F φ e0 = Fr.F (N.model (Additive.ofMul (φ ⟨y, hy⟩))) := by
    rw [ggQ2_d6_coord_apply]
    rw [show Fr.F.symm e0 = N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) by
          rw [← Fr.F_y, LinearEquiv.symm_apply_apply]]
    rw [ggLin_apply_ofMul]
  rw [hcoord, ← hk]
  have hz : Fr.F (N.model (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ k))) = (k : ZMod 3) • e0 := by
    rw [ofMul_zpow]
    rw [show N.model (k • Additive.ofMul (⟨y, hy⟩ : ↥Bs)) =
        k • N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) from
      AddMonoidHom.map_zsmul N.model.toAddMonoidHom k _]
    rw [show Fr.F (k • N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
        k • Fr.F (N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) from
      AddMonoidHom.map_zsmul (Fr.F.toLinearMap.toAddMonoidHom) k _]
    rw [Fr.F_y]
    exact (Int.cast_smul_eq_zsmul (ZMod 3) k e0).symm
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e0))

end QTwoD6

end CFSG.StandardType

end
