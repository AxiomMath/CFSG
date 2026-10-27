module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2x_model_nsmul {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

private lemma ggQ2x_model_zsmul {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (n : ℤ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_zsmul n (Additive.ofMul b)

private lemma ggQ2x_mem_closure_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (d : ↥Bs) :
    (d : G) ∈ Subgroup.closure ({x, y} : Set G) ↔
      M.model (Additive.ofMul d) ∈ Submodule.span (ZMod p) {M.xV, M.yV} := by
  have hmap : Subgroup.map (Subgroup.subtype Bs)
      (Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs)) =
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
      · exact ⟨⟨x, M.hx⟩, by simp, hg.symm⟩
      · exact ⟨⟨y, M.hy⟩, by simp, hg.symm⟩
  have hmem : (d : G) ∈ Subgroup.closure ({x, y} : Set G) ↔
      d ∈ Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs) := by
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
      (p := fun g _ => M.model (Additive.ofMul g) ∈ Submodule.span (ZMod p) {M.xV, M.yV})
      ?_ ?_ ?_ ?_ hd
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · change M.xV ∈ Submodule.span (ZMod p) {M.xV, M.yV}
        exact Submodule.mem_span_of_mem (by simp)
      · change M.yV ∈ Submodule.span (ZMod p) {M.xV, M.yV}
        exact Submodule.mem_span_of_mem (by simp)
    · rw [show Additive.ofMul (1 : ↥Bs) = 0 from rfl, map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [ofMul_mul, map_add]
      exact Submodule.add_mem _ ha hb
    · intro a _ ha
      rw [ofMul_inv, map_neg]
      exact Submodule.neg_mem _ ha
  · intro hd
    rw [Submodule.mem_span_pair] at hd
    obtain ⟨c, e, hce⟩ := hd
    have h1 : c • M.xV = M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ c.val)) := by
      rw [show M.xV = M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) from rfl]
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2x_model_nsmul M c.val (⟨x, M.hx⟩ : ↥Bs),
        ← ofMul_pow]
    have h2 : e • M.yV = M.model (Additive.ofMul ((⟨y, M.hy⟩ : ↥Bs) ^ e.val)) := by
      rw [show M.yV = M.model (Additive.ofMul (⟨y, M.hy⟩ : ↥Bs)) from rfl]
      conv_lhs => rw [← ZMod.natCast_zmod_val e]
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2x_model_nsmul M e.val (⟨y, M.hy⟩ : ↥Bs),
        ← ofMul_pow]
    have h3 : M.model (Additive.ofMul
        ((⟨x, M.hx⟩ : ↥Bs) ^ c.val * (⟨y, M.hy⟩ : ↥Bs) ^ e.val)) =
        M.model (Additive.ofMul d) := by
      rw [ofMul_mul, map_add, ← h1, ← h2, hce]
    have h4 : (⟨x, M.hx⟩ : ↥Bs) ^ c.val * (⟨y, M.hy⟩ : ↥Bs) ^ e.val = d :=
      Additive.ofMul.injective (M.model.injective h3)
    have hsx : (⟨x, M.hx⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    have hsy : (⟨y, M.hy⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    rw [← h4]
    exact Subgroup.mul_mem _ (pow_mem hsx c.val) (pow_mem hsy e.val)

private lemma ggQ2x_zpowers_iff_span {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (a b : ↥Bs) :
    Subgroup.zpowers a = Subgroup.zpowers b ↔
      Submodule.span (ZMod p) {M.model (Additive.ofMul a)} =
        Submodule.span (ZMod p) {M.model (Additive.ofMul b)} := by
  have key : ∀ c d : ↥Bs, c ∈ Subgroup.zpowers d →
      M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} := by
    intro c d h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hm, ofMul_zpow]
    rw [ggQ2x_model_zsmul M m d]
    rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have key' : ∀ c d : ↥Bs,
      M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} →
      c ∈ Subgroup.zpowers d := by
    intro c d h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨k, hk⟩ := h
    rw [← ZMod.natCast_zmod_val k, Nat.cast_smul_eq_nsmul,
      ← ggQ2x_model_nsmul M k.val d, ← ofMul_pow] at hk
    have h2 : Additive.ofMul (d ^ k.val) = Additive.ofMul c := M.model.injective hk
    have h3 : d ^ k.val = c := Additive.ofMul.injective h2
    rw [← h3]
    exact Subgroup.npow_mem_zpowers d k.val
  constructor
  · intro h
    have hab : a ∈ Subgroup.zpowers b := by rw [← h]; exact Subgroup.mem_zpowers a
    have hba : b ∈ Subgroup.zpowers a := by rw [h]; exact Subgroup.mem_zpowers b
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact key a b hab
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact key b a hba
  · intro h
    have hab : M.model (Additive.ofMul a) ∈
        Submodule.span (ZMod p) {M.model (Additive.ofMul b)} := by
      rw [← h]; exact Submodule.mem_span_singleton_self _
    have hba : M.model (Additive.ofMul b) ∈
        Submodule.span (ZMod p) {M.model (Additive.ofMul a)} := by
      rw [h]; exact Submodule.mem_span_singleton_self _
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact key' a b hab
    · rw [Subgroup.zpowers_le]
      exact key' b a hba

theorem ggQ2_orbit_iff {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G}
    (M : GGQTwoModel p Bs x y D L J K) (hp2 : p ≠ 2) (u : ↥Bs) :
    GGOrbitStableAt p Bs u ↔ ∀ φ ∈ M.linGroup, ∃ r ∈ reflGp M.linGroup,
      Submodule.span (ZMod p) {φ (M.model (Additive.ofMul u))} =
        Submodule.span (ZMod p) {r (M.model (Additive.ofMul u))} := by
  constructor
  · intro h φ hφ
    rw [GGQTwoModel.linGroup, Subgroup.mem_map] at hφ
    obtain ⟨φa, hφa, rfl⟩ := hφ
    obtain ⟨ra, hra, hz⟩ := h φa hφa
    refine ⟨ggLin (p := p) M.model ra, ?_, ?_⟩
    · rw [← ggQ2_reflGp_map M hp2, Subgroup.mem_map]
      exact ⟨ra, hra, rfl⟩
    · rw [ggLin_apply_ofMul, ggLin_apply_ofMul]
      exact (ggQ2x_zpowers_iff_span M (φa u) (ra u)).mp hz
  · intro h φ hφ
    have hφ' : ggLin (p := p) M.model φ ∈ M.linGroup := by
      rw [GGQTwoModel.linGroup, Subgroup.mem_map]
      exact ⟨φ, hφ, rfl⟩
    obtain ⟨r, hr, hsp⟩ := h (ggLin (p := p) M.model φ) hφ'
    rw [← ggQ2_reflGp_map M hp2, Subgroup.mem_map] at hr
    obtain ⟨ra, hra, rfl⟩ := hr
    refine ⟨ra, hra, ?_⟩
    rw [ggLin_apply_ofMul, ggLin_apply_ofMul] at hsp
    exact (ggQ2x_zpowers_iff_span M (φ u) (ra u)).mpr hsp

theorem ggQ2_D_eq_span {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x y : G} {L D J K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) :
    ∀ v : M.V, v ∈ Submodule.span (ZMod p) {M.xV, M.yV} ↔
      ∃ d : ↥Bs, (d : G) ∈ D ∧ M.model (Additive.ofMul d) = v := by
  have hD : D = Subgroup.closure ({x, y} : Set G) := hnb.2.1
  subst hD
  intro v
  constructor
  · intro hv
    refine ⟨Additive.toMul (M.model.symm v), ?_, ?_⟩
    · rw [ggQ2x_mem_closure_iff M,
        show Additive.ofMul (Additive.toMul (M.model.symm v)) = M.model.symm v from
          Equiv.apply_symm_apply Additive.ofMul (M.model.symm v),
        AddEquiv.apply_symm_apply M.model v]
      exact hv
    · rw [show Additive.ofMul (Additive.toMul (M.model.symm v)) = M.model.symm v from
          Equiv.apply_symm_apply Additive.ofMul (M.model.symm v)]
      exact AddEquiv.apply_symm_apply M.model v
  · rintro ⟨d, hd, rfl⟩
    exact (ggQ2x_mem_closure_iff M d).mp hd

end CFSG.StandardType

end
