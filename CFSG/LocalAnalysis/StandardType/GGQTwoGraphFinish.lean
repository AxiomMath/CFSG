module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoSwapAB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private lemma ggQ2gf_model_nsmul {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

private lemma ggQ2gf_mem_closure_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (d : ↥Bs) :
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
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2gf_model_nsmul M c.val (⟨x, M.hx⟩ : ↥Bs),
        ← ofMul_pow]
    have h2 : e • M.yV = M.model (Additive.ofMul ((⟨y, M.hy⟩ : ↥Bs) ^ e.val)) := by
      rw [show M.yV = M.model (Additive.ofMul (⟨y, M.hy⟩ : ↥Bs)) from rfl]
      conv_lhs => rw [← ZMod.natCast_zmod_val e]
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2gf_model_nsmul M e.val (⟨y, M.hy⟩ : ↥Bs),
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

theorem ggQ2_weyl_le_G0 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x y : G} {L D J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (hnb : GGNbr p B x D J y K) :
    M.parabL Set.univ ≤ (ggAutomizer (ggG0 p B x L D J) Bs).map (ggLin (p := p) M.model) := by
  rw [ggQ2_parabL_eq_map]
  refine Subgroup.map_mono ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  by_cases hk : k = M.a
  · have hkK : M.simple k ∈ ggAutomizer K Bs := by
      rw [M.automizer_K]
      refine Subgroup.subset_closure ⟨k, ?_, rfl⟩
      intro hkb
      exact M.a_ne_b (hk.symm.trans hkb)
    exact ggAutomizer_mono Bs (le_ggG0_of_ggNbr hnb) hkK
  · have hkL : M.simple k ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨k, hk, rfl⟩
    exact ggAutomizer_mono Bs (le_ggG0_left p B x L D J) hkL

theorem ggQ2_finish_of_weyl {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (h : ∃ w' ∈ M.toLin.weyl, ∀ v ∈ Submodule.span (ZMod p) {M.xV, M.yV},
      w' (ggLin (p := p) M.model φ v) ∈ Submodule.span (ZMod p) {M.xV, M.yV}) :
    φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  obtain ⟨w', hw'weyl, hw'⟩ := h
  have hw'parabL : w' ∈ M.parabL Set.univ := hw'weyl
  obtain ⟨ψ, hψ, hψw⟩ := Subgroup.mem_map.mp (ggQ2_weyl_le_G0 M hnb hw'parabL)
  refine ggQ2_finish_of_le hLB hP hS hAJ hK1 hnb (le_refl _) hφ hψ (fun b hbD => ?_)
  have hbspan : M.model (Additive.ofMul b) ∈ Submodule.span (ZMod p) {M.xV, M.yV} :=
    (ggQ2gf_mem_closure_iff M b).mp (by rw [← hnb.2.1]; exact hbD)
  have hspan' : M.model (Additive.ofMul ((ψ * φ) b)) ∈
      Submodule.span (ZMod p) {M.xV, M.yV} := by
    have heq : M.model (Additive.ofMul ((ψ * φ) b)) =
        w' (ggLin (p := p) M.model φ (M.model (Additive.ofMul b))) := by
      rw [← ggLin_apply_ofMul (p := p) M.model (ψ * φ) b, map_mul,
        LinearEquiv.mul_apply, hψw]
      rfl
    rw [heq]
    exact hw' _ hbspan
  rw [hnb.2.1]
  exact (ggQ2gf_mem_closure_iff M ((ψ * φ) b)).mpr hspan'

end CFSG.StandardType

end
