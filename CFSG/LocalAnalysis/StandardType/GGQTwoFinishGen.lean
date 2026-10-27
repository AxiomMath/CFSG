module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCor81
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem ggQ2_finish_of_le {G : Type} [Group G] [Finite G] {p : ℕ} (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {H : Subgroup G} (hH : H ≤ ggG0 p B x L D J)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs) (hψ : ψ ∈ ggAutomizer H Bs)
    (hD : ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D) :
    φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  obtain ⟨g, -, hgBs, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  obtain ⟨k, hkH, hkBs, hψk⟩ := mem_ggAutomizer_iff.mp hψ
  have hψφg : ∀ b : ↥Bs, (((ψ * φ) b : ↥Bs) : G) = (k * g) * b * (k * g)⁻¹ := by
    intro b
    rw [MulAut.mul_apply, hψk (φ b), hφg b]
    group
  have hxmem : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert x {y})
  have hymem : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hxBs : x ∈ Bs := hDBs hxmem
  have hyBs : y ∈ Bs := hDBs hymem
  have hconj_x : (k * g) * x * (k * g)⁻¹ ∈ D := by
    have h := hD ⟨x, hxBs⟩ hxmem
    rwa [hψφg ⟨x, hxBs⟩] at h
  have hconj_y : (k * g) * y * (k * g)⁻¹ ∈ D := by
    have h := hD ⟨y, hyBs⟩ hymem
    rwa [hψφg ⟨y, hyBs⟩] at h
  let E : Subgroup G :=
    { carrier := {d : G | (k * g) * d * (k * g)⁻¹ ∈ D}
      one_mem' := by simpa using D.one_mem
      mul_mem' := by
        intro a b ha hb
        change (k * g) * (a * b) * (k * g)⁻¹ ∈ D
        have h : (k * g) * (a * b) * (k * g)⁻¹ =
            ((k * g) * a * (k * g)⁻¹) * ((k * g) * b * (k * g)⁻¹) := by group
        rw [h]
        exact D.mul_mem ha hb
      inv_mem' := by
        intro a ha
        change (k * g) * a⁻¹ * (k * g)⁻¹ ∈ D
        have h : (k * g) * a⁻¹ * (k * g)⁻¹ = ((k * g) * a * (k * g)⁻¹)⁻¹ := by group
        rw [h]
        exact D.inv_mem ha }
  have hDleE : D ≤ E := by
    rw [hnb.2.1]
    refine (Subgroup.closure_le E).mpr ?_
    intro d hd
    rw [Set.mem_insert_iff] at hd
    rcases hd with hd_eq | hd_mem
    · rw [hd_eq]
      exact hconj_x
    · rw [Set.mem_singleton_iff] at hd_mem
      rw [hd_mem]
      exact hconj_y
  have hmN : (k * g) ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hkBs hgBs
  have hmD : (k * g) ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_fintype (S := (D : Set G))
      (fun n hn => show (k * g) * n * (k * g)⁻¹ ∈ D from hDleE hn)
  have hmG0 : (k * g) ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    ggQ2_normalizer_inf_le hLB hP hS.1 hAJ hK1 (Subgroup.mem_inf.mpr ⟨hmN, hmD⟩)
  have hkG0 : k ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    Subgroup.le_normalizer (hH hkH)
  have hgG0 : g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
    have h : k⁻¹ * (k * g) ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hkG0) hmG0
    simpa using h
  exact mem_ggAutomizer_iff.mpr ⟨g, hgG0, hgBs, hφg⟩

private lemma ggQ2fg_model_nsmul {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

private theorem ggQ2fg_ggLin_simple {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (k : M.ι) : ggLin (p := p) M.model (M.simple k) = M.toLin.simpleRefl k := by
  refine LinearEquiv.ext fun v => ?_
  rw [M.simple_apply]
  exact (Module.reflection_apply v (M.toLin.root_coroot_self k)).symm

private theorem ggQ2fg_image_eq {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (S : Set M.ι) :
    ggLin (p := p) M.model '' (M.simple '' S) = M.toLin.simpleRefl '' S := by
  ext t
  constructor
  · rintro ⟨φ, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (ggQ2fg_ggLin_simple M k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨M.simple k, ⟨k, hk, rfl⟩, ggQ2fg_ggLin_simple M k⟩

theorem ggQ2_parabL_eq_map {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (S : Set M.ι) :
    M.parabL S = (Subgroup.closure (M.simple '' S)).map (ggLin (p := p) M.model) := by
  rw [show M.parabL S = Subgroup.closure (M.toLin.simpleRefl '' S) from rfl,
    MonoidHom.map_closure, ggQ2fg_image_eq]
  rfl

private lemma ggQ2fg_mem_closure_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
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
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2fg_model_nsmul M c.val (⟨x, M.hx⟩ : ↥Bs),
        ← ofMul_pow]
    have h2 : e • M.yV = M.model (Additive.ofMul ((⟨y, M.hy⟩ : ↥Bs) ^ e.val)) := by
      rw [show M.yV = M.model (Additive.ofMul (⟨y, M.hy⟩ : ↥Bs)) from rfl]
      conv_lhs => rw [← ZMod.natCast_zmod_val e]
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2fg_model_nsmul M e.val (⟨y, M.hy⟩ : ↥Bs),
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

theorem ggQ2_bridge {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (hDxy : D = Subgroup.closure {x, y}) {S : Set M.ι} {H : Subgroup G}
    (hH : M.parabL S = (ggAutomizer H Bs).map (ggLin (p := p) M.model)) {φ : MulAut ↥Bs}
    (h : ∃ w' ∈ M.parabL S, ∀ v ∈ Submodule.span (ZMod p) {M.xV, M.yV},
      w' (ggLin (p := p) M.model φ v) ∈ Submodule.span (ZMod p) {M.xV, M.yV}) :
    ∃ ψ ∈ ggAutomizer H Bs, ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D := by
  obtain ⟨w', hw'parabL, hw'⟩ := h
  rw [hH] at hw'parabL
  obtain ⟨ψ, hψ, hψw⟩ := Subgroup.mem_map.mp hw'parabL
  refine ⟨ψ, hψ, fun b hbD => ?_⟩
  have hbspan : M.model (Additive.ofMul b) ∈ Submodule.span (ZMod p) {M.xV, M.yV} :=
    (ggQ2fg_mem_closure_iff M b).mp (by rw [← hDxy]; exact hbD)
  have hspan' : M.model (Additive.ofMul ((ψ * φ) b)) ∈
      Submodule.span (ZMod p) {M.xV, M.yV} := by
    have heq : M.model (Additive.ofMul ((ψ * φ) b)) =
        w' (ggLin (p := p) M.model φ (M.model (Additive.ofMul b))) := by
      rw [← ggLin_apply_ofMul (p := p) M.model (ψ * φ) b, map_mul,
        LinearEquiv.mul_apply, hψw]
    rw [heq]
    exact hw' _ hbspan
  rw [hDxy]
  exact (ggQ2fg_mem_closure_iff M ((ψ * φ) b)).mpr hspan'

end CFSG.StandardType

end
