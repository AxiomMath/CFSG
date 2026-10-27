module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_shapeFull_linear {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {C : Matrix Λ Λ ℤ} (hdet : ((C.det : ℤ) : ZMod p) ≠ 0) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hdim : Module.finrank (ZMod p) V = Fintype.card Λ + 1) {v : V} (hv0 : v ≠ 0)
    (hv : ∀ i, α i v = 0) :
    LinearIndependent (ZMod p) h ∧ v ∉ Submodule.span (ZMod p) (Set.range h) ∧
      Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) {v} = ⊤ ∧
      (LinearMap.pi α).ker = Submodule.span (ZMod p) {v} := by
  classical
  let D : Matrix Λ Λ (ZMod p) := C.map (Int.castRingHom (ZMod p))
  have hDdet : D.det ≠ 0 := by
    change (C.map (fun x : ℤ => (x : ZMod p))).det ≠ 0
    rw [← Int.cast_det C]
    exact hdet
  have hLI : LinearIndependent (ZMod p) h := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hvec : D.mulVec c = 0 := by
      ext i
      have h := congrArg (α i) hc
      simp only [map_sum, map_smul, hpair, map_zero] at h
      simpa [D, Matrix.mulVec, dotProduct, mul_comm, smul_eq_mul] using h
    intro i
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hDdet hvec) i
  have hnotmem : v ∉ Submodule.span (ZMod p) (Set.range h) := by
    intro hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hmem
    have hvec : D.mulVec c = 0 := by
      ext i
      have h := congrArg (α i) hc
      simp only [map_sum, map_smul, hpair, hv i, map_zero] at h
      simpa [D, Matrix.mulVec, dotProduct, mul_comm, smul_eq_mul] using h
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hDdet hvec
    apply hv0
    calc v = ∑ j, c j • h j := hc.symm
      _ = 0 := by simp [hc0]
  have hdisj : Submodule.span (ZMod p) (Set.range h) ⊓
      Submodule.span (ZMod p) {v} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z ⟨hzH, hzS⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzS
    rw [← hc] at hzH
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · exfalso
      apply hnotmem
      have hzv : v = c⁻¹ • (c • v) := by
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hzv]
      exact Submodule.smul_mem _ _ hzH
  have hsup : Submodule.span (ZMod p) (Set.range h) ⊔
      Submodule.span (ZMod p) {v} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod p) (Set.range h)) (Submodule.span (ZMod p) {v})
    rw [hdisj, finrank_bot, finrank_span_eq_card hLI, finrank_span_singleton hv0,
      add_zero] at hfin
    rw [hfin, hdim]
  have hker : (LinearMap.pi α).ker = Submodule.span (ZMod p) {v} := by
    apply le_antisymm
    · intro z hz
      rw [LinearMap.mem_ker] at hz
      have hzmem : z ∈ Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) {v} := by rw [hsup]; exact Submodule.mem_top
      obtain ⟨s, hs, w, hw, hzw⟩ := Submodule.mem_sup.mp hzmem
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hs
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hw
      have hspi : ∀ i, α i s = 0 := by
        intro i
        have hzi : α i z = 0 := congrFun hz i
        rw [show z = s + w from hzw.symm, map_add, ← ht, map_smul, hv i, smul_zero,
          add_zero] at hzi
        exact hzi
      have hvec : D.mulVec c = 0 := by
        ext i
        have h := hspi i
        rw [← hc] at h
        simp only [map_sum, map_smul, hpair, smul_eq_mul] at h
        simpa [D, Matrix.mulVec, dotProduct, mul_comm, smul_eq_mul] using h
      have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hDdet hvec
      have hs0 : s = 0 := by rw [← hc]; simp [hc0]
      rw [show z = s + w from hzw.symm, hs0, zero_add]
      exact hw
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr (by funext i; exact hv i)
  exact ⟨hLI, hnotmem, hsup, hker⟩

theorem exists_ggQ2LDatum_shapeFull {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G]
    [Finite G] {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs)
    (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hxL : x ∉ L)
    (hNT : GGNoTransvection p Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (hent : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1 ∨ C i j = -2)
    (hT : SecFiveRootRefl.CartanTree C) (hdet : ((C.det : ℤ) : ZMod p) ≠ 0)
    (hW : GGWeylOfType p M (ggAutomizer L Bs)) (hcard : Nat.card Bs = p ^ (Fintype.card Λ + 1))
    {lab : LargeEvenLabel} (hlab : GGQ2LabelWeyl lab M) :
    ∃ D : GGQ2LDatum p Bs L x, GGQ2LabelWeyl lab D.coxeter ∧ D.ShapeFull ∧
      Module.finrank (ZMod p) D.V = Fintype.card D.Λ + 1 := by
  classical
  obtain ⟨V, iadd, imod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  letI : AddCommGroup V := iadd
  letI : Module (ZMod p) V := imod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hVcard : Nat.card V = p ^ (Fintype.card Λ + 1) := by
    rw [← card_eq_of_ggLin ιV, hcard]
  have hdim : Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hVcard] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  obtain ⟨e, he⟩ := hW
  have hind : ∀ φ ∈ ggAutomizer L Bs, φ ∈ ggInduced ⊤ Bs :=
    fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ
  obtain ⟨h, α, hα, hrefl, hpair⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_iso (p := p) hp2 hNT hC hent hT e he hind ιV
  let simple : Λ → MulAut ↥Bs :=
    fun i => ((e (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hsimple_apply : ∀ i w, ggLin (p := p) ιV (simple i) w = w - α i w • h i :=
    fun i w => by rw [hrefl i]; exact Module.reflection_apply w (hα i)
  have hmap : ((Subgroup.subtype (ggAutomizer L Bs)).comp e.toMonoidHom) '' Set.range M.simple =
      Set.range simple := by
    ext x
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
  have hfr : ((Subgroup.subtype (ggAutomizer L Bs)).comp e.toMonoidHom).range =
      ggAutomizer L Bs := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact (e m).2
    · intro hx
      obtain ⟨m, hm⟩ := e.surjective ⟨x, hx⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  have hsimple_eq : (M.toCoxeterSystem).simple = M.simple := by
    funext i
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  have hsimple_range : Set.range M.simple = Set.range (M.toCoxeterSystem).simple := by
    rw [hsimple_eq]
  have hAL : ggAutomizer L Bs = Subgroup.closure (Set.range simple) := by
    have hc : Subgroup.closure (Set.range simple) = ggAutomizer L Bs := by
      rw [← hmap, ← MonoidHom.map_closure, hsimple_range,
        (M.toCoxeterSystem).subgroup_closure_range_simple, Subgroup.map_top, hfr]
    exact hc.symm
  let xV : V := ιV (Additive.ofMul ⟨x, hxBs⟩)
  have hxVfix : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := p) ιV φ xV = xV := by
    intro φ hφ
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    have hgx : g * x = x * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
    have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      apply Subtype.ext
      rw [hg]
      change g * x * g⁻¹ = x
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hgx]
        _ = x := by group
    change ggLin (p := p) ιV φ (ιV (Additive.ofMul ⟨x, hxBs⟩)) = xV
    rw [ggLin_apply_ofMul, hφx]
  have hxV0 : xV ≠ 0 := by
    intro h
    apply hx1
    have h1 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
      apply ιV.injective
      simpa [xV] using h
    have h2 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      simpa using Additive.ofMul.injective h1
    exact congrArg (fun b : ↥Bs => (b : G)) h2
  have hhi : ∀ i, h i ≠ 0 := by
    intro i h0
    have h2 : (2 : ZMod p) = 0 := by rw [← hα i, h0, map_zero]
    exact zmod_two_ne_zero hp2 h2
  have hroot_xV : ∀ i, α i xV = 0 := by
    intro i
    have hsi : simple i ∈ ggAutomizer L Bs := by
      rw [hAL]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfix := hxVfix (simple i) hsi
    have heq := hsimple_apply i xV
    rw [hfix] at heq
    have hzero : α i xV • h i = 0 := sub_eq_self.mp heq.symm
    exact (smul_eq_zero.mp hzero).resolve_right (hhi i)
  have hlin := ggQ2_shapeFull_linear (p := p) hdet h α hpair hdim hxV0 hroot_xV
  have hfixed_x : ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs) =
      Submodule.span (ZMod p) {xV} := by
    apply le_antisymm
    · intro v hv
      have hroot_v : ∀ i, α i v = 0 := by
        intro i
        have hsi : simple i ∈ ggAutomizer L Bs := by
          rw [hAL]
          exact Subgroup.subset_closure ⟨i, rfl⟩
        have hfix := mem_ggFixedSubmodule_iff.mp hv (simple i) hsi
        have heq := hsimple_apply i v
        rw [hfix] at heq
        have hzero : α i v • h i = 0 := sub_eq_self.mp heq.symm
        exact (smul_eq_zero.mp hzero).resolve_right (hhi i)
      have hvker : v ∈ (LinearMap.pi α).ker := by
        rw [LinearMap.mem_ker]
        funext i
        exact hroot_v i
      rw [hlin.2.2.2] at hvker
      exact hvker
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_ggFixedSubmodule_iff.mpr hxVfix
  let D : GGQ2LDatum p Bs L x :=
    { Λ := Λ
      coxeter := M
      cartan := C
      V := V
      model := ιV
      hx := hxBs
      simple := simple
      coroot := h
      root := α
      isWeyl := hM
      isCartan := hC
      pairing := hpair
      simple_apply := hsimple_apply
      automizer_L := hAL
      fixed_x := hfixed_x }
  refine ⟨D, ?_, ?_, ?_⟩
  · change GGQ2LabelWeyl lab M
    exact hlab
  · exact ⟨hxL, hlin.1, hlin.2.1, hlin.2.2.1⟩
  · exact hdim

end CFSG.StandardType

end
