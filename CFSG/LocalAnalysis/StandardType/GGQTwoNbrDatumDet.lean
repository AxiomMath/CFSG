module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPmWDatum
public import CFSG.LocalAnalysis.StandardType.GGQTwoPosInLCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishK
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def GGQ2NbrDatum.toWDatum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) : GGQ2WDatum p where
  Λ := N.Λ
  coxeter := N.coxeter
  cartan := N.cartan
  V := N.V
  coroot := N.coroot
  root := N.root
  isWeyl := N.isWeyl
  isCartan := N.isCartan
  pairing := N.pairing

private theorem ggQ2nd_g1_stable {G : Type} [Group G] {Bs : Subgroup G} {y : G} (hy : y ∈ Bs)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) {φ : MulAut ↥Bs}
    (hφu : φ u ∈ Subgroup.zpowers u) :
    φ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hφu
  have hymem : y ∈ Subgroup.zpowers (u : G) := by
    rw [hu]
    exact Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hymem
  have huy : (⟨y, hy⟩ : ↥Bs) = u ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hk]
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨r, ?_⟩
  calc (⟨y, hy⟩ : ↥Bs) ^ r = (u ^ k) ^ r := by rw [huy]
    _ = u ^ (k * r) := (zpow_mul u k r).symm
    _ = u ^ (r * k) := by rw [mul_comm]
    _ = (u ^ r) ^ k := zpow_mul u r k
    _ = (φ u) ^ k := by rw [hr]
    _ = φ (u ^ k) := (map_zpow φ u k).symm
    _ = φ ⟨y, hy⟩ := by rw [← huy]

private lemma ggQ2nd_model_nsmul {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) (n : ℕ) (b : ↥Bs) :
    N.model (n • Additive.ofMul b) = n • N.model (Additive.ofMul b) :=
  (N.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

private lemma ggQ2nd_mem_closure_iff {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) {x y : G} (hx : x ∈ Bs) (hy : y ∈ Bs)
    (d : ↥Bs) :
    (d : G) ∈ Subgroup.closure ({x, y} : Set G) ↔
      N.model (Additive.ofMul d) ∈ Submodule.span (ZMod p)
        {N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs)),
         N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} := by
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
      (p := fun g _ => N.model (Additive.ofMul g) ∈ Submodule.span (ZMod p)
        {N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs)),
         N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))})
      ?_ ?_ ?_ ?_ hd
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Submodule.mem_span_of_mem (by simp)
      · exact Submodule.mem_span_of_mem (by simp)
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
    have h1 : c • N.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) =
        N.model (Additive.ofMul ((⟨x, hx⟩ : ↥Bs) ^ c.val)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2nd_model_nsmul N c.val (⟨x, hx⟩ : ↥Bs),
        ← ofMul_pow]
    have h2 : e • N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) =
        N.model (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ e.val)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val e]
      rw [Nat.cast_smul_eq_nsmul, ← ggQ2nd_model_nsmul N e.val (⟨y, hy⟩ : ↥Bs),
        ← ofMul_pow]
    have h3 : N.model (Additive.ofMul
        ((⟨x, hx⟩ : ↥Bs) ^ c.val * (⟨y, hy⟩ : ↥Bs) ^ e.val)) =
        N.model (Additive.ofMul d) := by
      rw [ofMul_mul, map_add, ← h1, ← h2, hce]
    have h4 : (⟨x, hx⟩ : ↥Bs) ^ c.val * (⟨y, hy⟩ : ↥Bs) ^ e.val = d :=
      Additive.ofMul.injective (N.model.injective h3)
    have hsx : (⟨x, hx⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    have hsy : (⟨y, hy⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    rw [← h4]
    exact Subgroup.mul_mem _ (pow_mem hsx c.val) (pow_mem hsy e.val)

private lemma ggQ2nd_zpowers_subtype_iff {G : Type} [Group G] {Bs : Subgroup G} {y : G}
    (hy : y ∈ Bs) (b : ↥Bs) :
    (b : G) ∈ Subgroup.zpowers y ↔ b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private lemma ggQ2nd_model_span_iff {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) {y : G} (hy : y ∈ Bs) (b : ↥Bs) :
    N.model (Additive.ofMul b) ∈
        Submodule.span (ZMod p) {N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} ↔
      b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have h1 : c.val • N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) =
        N.model (Additive.ofMul b) := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val, ZMod.natCast_zmod_val]
      exact hc
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Additive.ofMul.injective
    apply N.model.injective
    rw [ofMul_pow, ggQ2nd_model_nsmul]
    exact h1
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hk]
    have h1 : N.model (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ k)) =
        k • N.model (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
      rw [ofMul_zpow]
      exact (N.model.toAddMonoidHom).map_zsmul k (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
    rw [h1, ← Int.cast_smul_eq_zsmul (R := ZMod p) k]
    exact Submodule.smul_mem _ (k : ZMod p) (Submodule.mem_span_singleton_self _)

private theorem ggQ2nd_finrank_le_card_add_one {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p)
    (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u}) :
    Module.finrank (ZMod p) D.V ≤ Fintype.card D.Λ + 1 := by
  classical
  by_cases hfd : FiniteDimensional (ZMod p) D.V
  swap
  · rw [Module.finrank_of_not_finite hfd]
    omega
  have : FiniteDimensional (ZMod p) D.V := hfd
  let Φ : D.V →ₗ[ZMod p] (D.Λ →₀ ZMod p) :=
    { toFun := fun v => Finsupp.equivFunOnFinite.symm (fun i => D.root i v)
      map_add' := by intro a b; ext i; simp
      map_smul' := by intro c a; ext i; simp }
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hr : Module.finrank (ZMod p) (LinearMap.range Φ) ≤ Fintype.card D.Λ := by
    have h := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_finsupp_self] at h
  have hle : LinearMap.ker Φ ≤ Submodule.span (ZMod p) {u} := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [← hfix v]
    intro g hg
    have hv0 : ∀ i : D.Λ, D.root i v = 0 := fun i =>
      congrFun (congrArg Finsupp.equivFunOnFinite hv) i
    refine Subgroup.closure_induction (p := fun g _ => g v = v) ?_ ?_ ?_ ?_ hg
    · rintro g ⟨i, rfl⟩
      rw [GGQ2WDatum.simpleRefl, Module.reflection_apply, hv0 i, zero_smul, sub_zero]
    · rfl
    · intro g h _ _ hg hh
      rw [LinearEquiv.mul_apply, hh, hg]
    · intro g _ hg
      have h1 : g.symm (g v) = v := g.symm_apply_apply v
      rw [hg] at h1
      exact h1
  have hsp : Module.finrank (ZMod p) (Submodule.span (ZMod p) {u}) ≤ 1 := by
    by_cases h0 : u = 0
    · rw [h0, Submodule.span_zero_singleton, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton h0]
  have hk : Module.finrank (ZMod p) (LinearMap.ker Φ) ≤ 1 :=
    (Submodule.finrank_mono hle).trans hsp
  calc Module.finrank (ZMod p) D.V
      = Module.finrank (ZMod p) (LinearMap.range Φ) +
        Module.finrank (ZMod p) (LinearMap.ker Φ) := hrn.symm
    _ ≤ Fintype.card D.Λ + 1 := Nat.add_le_add hr hk

theorem GGQ2NbrDatum.weyl_eq_map {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (N : GGQ2NbrDatum p Bs K) :
    N.toWDatum.weyl = (ggAutomizer K Bs).map (ggLin (p := p) N.model) := by
  have hsimple : ∀ i : N.Λ, ggLin (p := p) N.model (N.simple i) = N.toWDatum.simpleRefl i := by
    intro i
    refine LinearEquiv.ext fun v => ?_
    rw [N.simple_apply]
    exact (Module.reflection_apply v (N.toWDatum.root_coroot_self i)).symm
  have hrange : Set.range N.toWDatum.simpleRefl
      = ggLin (p := p) N.model '' Set.range N.simple := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨N.simple i, ⟨i, rfl⟩, hsimple i⟩
    · rintro ⟨φ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hsimple i).symm⟩
  rw [show N.toWDatum.weyl = Subgroup.closure (Set.range N.toWDatum.simpleRefl) from rfl]
  rw [hrange, N.automizer_K, MonoidHom.map_closure]
  rfl

theorem ggQ2_gammaNbr_of_datumPM (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (N : GGQ2NbrDatum p Bs K)
    (hpm : ∀ u₀ : N.toWDatum.V, u₀ ≠ 0 →
      (∀ v : N.toWDatum.V, (∀ g ∈ N.toWDatum.weyl, g v = v) ↔
        v ∈ Submodule.span (ZMod p) {u₀}) →
      Module.finrank (ZMod p) N.toWDatum.V ≤ Fintype.card N.toWDatum.Λ + 1 →
      4 ≤ Module.finrank (ZMod p) N.toWDatum.V → TransvectionFree N.toWDatum.weyl →
      ∀ T : N.toWDatum.V ≃ₗ[ZMod p] N.toWDatum.V,
        T ∈ Subgroup.normalizer (N.toWDatum.weyl : Set (N.toWDatum.V ≃ₗ[ZMod p] N.toWDatum.V)) →
        ∃ w ∈ N.toWDatum.weyl, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
          ∀ v : N.toWDatum.V, T (w v) - ε • v ∈ Submodule.span (ZMod p) {u₀})
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) :
    GGGammaAt p B Bs x L D J u := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hxmem : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert x {y})
  have hymem : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hxBs : x ∈ Bs := hDBs hxmem
  have hyBs : y ∈ Bs := hDBs hymem
  let D' : GGQ2WDatum 3 :=
    { Λ := N.Λ
      coxeter := N.coxeter
      cartan := N.cartan
      V := N.V
      coroot := N.coroot
      root := N.root
      isWeyl := N.isWeyl
      isCartan := N.isCartan
      pairing := N.pairing }
  have hpm' : ∀ u₀ : D'.V, u₀ ≠ 0 →
      (∀ v : D'.V, (∀ g ∈ D'.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u₀}) →
      Module.finrank (ZMod 3) D'.V ≤ Fintype.card D'.Λ + 1 →
      4 ≤ Module.finrank (ZMod 3) D'.V → TransvectionFree D'.weyl →
      ∀ T : D'.V ≃ₗ[ZMod 3] D'.V, T ∈ Subgroup.normalizer (D'.weyl : Set (D'.V ≃ₗ[ZMod 3] D'.V)) →
        ∃ w ∈ D'.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
          ∀ v : D'.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u₀} := hpm
  have hweyl : D'.weyl = (ggAutomizer K Bs).map (ggLin (p := 3) N.model) :=
    GGQ2NbrDatum.weyl_eq_map N
  intro φ hφ hφu
  have hφy : φ ⟨y, hyBs⟩ ∈ Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs) :=
    ggQ2nd_g1_stable hyBs hu hφu
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    ggQ2_nbrLineStab_normalizes hLB hP hH hAJS hK1 hnb hyBs hφ hφy
  let T : D'.V ≃ₗ[ZMod 3] D'.V := ggLin (p := 3) N.model φ
  have hTnorm : T ∈ Subgroup.normalizer (D'.weyl : Set (D'.V ≃ₗ[ZMod 3] D'.V)) := by
    rw [hweyl]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) N.model)
      (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  have hfix2 : ∀ v : D'.V, (∀ g ∈ D'.weyl, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} := by
    intro v
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, N.model (Additive.ofMul b) = v :=
      ⟨Additive.toMul (N.model.symm v), by simp⟩
    rw [hweyl]
    have hmapfix : (∀ g ∈ (ggAutomizer K Bs).map (ggLin (p := 3) N.model),
        g (N.model (Additive.ofMul b)) = N.model (Additive.ofMul b)) ↔
        N.model (Additive.ofMul b) ∈ ggFixedSubmodule (p := 3) N.model (ggAutomizer K Bs) := by
      rw [mem_ggFixedSubmodule_iff]
      constructor
      · intro h ψ hψ
        exact h (ggLin (p := 3) N.model ψ) (Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩)
      · rintro h g hg
        obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
        exact h ψ hψ
    have hZiff : (b : G) ∈ ggBarCentralizer 3 Bs K ↔
        b ∈ Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs) := by
      constructor
      · intro hb
        exact (ggQ2nd_zpowers_subtype_iff hyBs b).mp
          (hK1 y K hnb (b : G) hb.1 hb.2.2)
      · intro hb
        have hby : (b : G) ∈ Subgroup.zpowers y :=
          (ggQ2nd_zpowers_subtype_iff hyBs b).mpr hb
        have htr := (hnb.1.2.2.2.2.2 (b : G)).mpr hby
        exact ⟨hBstar.1 htr.1, htr.2.1, htr.2.2⟩
    exact hmapfix.trans ((N.fixed_ZK b).trans (hZiff.trans
      (ggQ2nd_model_span_iff N hyBs b).symm))
  have hy0 : N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, hyBs⟩ : ↥Bs) = 0 :=
      N.model.injective (by rw [map_zero]; exact h)
    have h1' : (⟨y, hyBs⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hnb.1.2.2.1 (Subtype.ext_iff.mp h1')
  have : Finite N.V := Finite.of_equiv (Additive ↥Bs) N.model.toEquiv
  have hcard_bs : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) N.V := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card N.V := Nat.card_congr N.model.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) N.V :=
        (FiniteField.pow_finrank_eq_natCard 3 N.V).symm
  have h4 : 4 ≤ Module.finrank (ZMod 3) N.V := by
    have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    rw [hcard_bs] at hp4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp4
  have hdim : Module.finrank (ZMod 3) D'.V ≤ Fintype.card D'.Λ + 1 :=
    ggQ2nd_finrank_le_card_add_one D' (N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) hfix2
  have hTF : TransvectionFree D'.weyl := by
    intro g hg htr
    rw [hweyl] at hg
    obtain ⟨ψ, hψK, hψg⟩ := Subgroup.mem_map.mp hg
    obtain ⟨w0, χ, hw0, hχ, hχw0, hgv⟩ := htr
    have hψtop : ψ ∈ ggInduced ⊤ Bs := by
      have h1 : ψ ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hψK
      rwa [ggAutomizer_eq] at h1
    exact hH.2.2.2.1 ψ hψtop (ggIsTransvection_of_apply N.model hw0 hχ hχw0 (fun v => by
      exact hψg ▸ hgv v))
  obtain ⟨w, hw, ε, hε, hwε⟩ :=
    hpm' (N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) hy0 hfix2 hdim h4 hTF T hTnorm
  have hw' : T * w * T⁻¹ ∈ D'.weyl :=
    (Subgroup.mem_normalizer_iff.mp hTnorm w).mp hw
  have hstab : ∀ v ∈ Submodule.span (ZMod 3)
      {N.model (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)),
       N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))},
      (T * w * T⁻¹) (ggLin (p := 3) N.model φ v) ∈ Submodule.span (ZMod 3)
      {N.model (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)),
       N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} := by
    intro v hv
    have hTv : (T * w * T⁻¹) (T v) = T (w v) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      congr 2
      exact T.symm_apply_apply v
    change (T * w * T⁻¹) (T v) ∈ _
    rw [hTv]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (hwε v)
    have hs' : T (w v) = ε • v + s • N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) := by
      rw [hs]
      abel
    rw [hs']
    exact Submodule.add_mem _ (Submodule.smul_mem _ ε hv)
      (Submodule.smul_mem _ s (Submodule.subset_span (by simp)))
  rw [hweyl] at hw'
  obtain ⟨ψ, hψK, hψw⟩ := Subgroup.mem_map.mp hw'
  have hD : ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D := by
    intro b hbD
    have hbspan : N.model (Additive.ofMul b) ∈ Submodule.span (ZMod 3)
        {N.model (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)),
         N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} :=
      (ggQ2nd_mem_closure_iff N hxBs hyBs b).mp (by rw [← hnb.2.1]; exact hbD)
    have hspan' : N.model (Additive.ofMul ((ψ * φ) b)) ∈ Submodule.span (ZMod 3)
        {N.model (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)),
         N.model (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} := by
      have heq : N.model (Additive.ofMul ((ψ * φ) b)) =
          (T * w * T⁻¹) (ggLin (p := 3) N.model φ (N.model (Additive.ofMul b))) := by
        rw [← ggLin_apply_ofMul (p := 3) N.model (ψ * φ) b, map_mul,
          LinearEquiv.mul_apply, hψw]
      rw [heq]
      exact hstab _ hbspan
    rw [hnb.2.1]
    exact (ggQ2nd_mem_closure_iff N hxBs hyBs ((ψ * φ) b)).mpr hspan'
  exact ggQ2_finishK hLB hP hS hAJS hK1 hnb hφ hψK hD

theorem ggQ2_gammaNbr_of_detDatum (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (N : GGQ2NbrDatum p Bs K) (hdet0 : ((N.cartan.det : ℤ) : ZMod p) = 0) (hpos : N.Pos)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) :
    GGGammaAt p B Bs x L D J u := by
  subst hp
  have hker : ∃ κ : N.Λ → ZMod 3, κ ≠ 0 ∧
      ∀ i : N.Λ, ∑ j : N.Λ, (N.cartan i j : ZMod 3) * κ j = 0 := by
    have hdet' : ((Int.castRingHom (ZMod 3)).mapMatrix N.cartan).det = 0 := by
      rw [← RingHom.map_det]
      exact hdet0
    obtain ⟨κ, hκ0, hκ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
    refine ⟨κ, hκ0, fun i => ?_⟩
    simpa [Matrix.mulVec, dotProduct] using congrFun hκ i
  have hpos' : LinearIndependent (ZMod 3) N.toWDatum.coroot ∨
      Module.finrank (ZMod 3) N.toWDatum.V = Fintype.card N.toWDatum.Λ + 1 := hpos
  exact ggQ2_gammaNbr_of_datumPM hLB hP h5 hS rfl hI1 hnb N
    (fun u₀ hu0 hfix hdim h4 hTF T hT =>
      GGQ2WDatum.pmW_of_ker N.toWDatum u₀ hu0 hfix hker hdim h4 hTF hpos' T hT) hu

end CFSG.StandardType

end
