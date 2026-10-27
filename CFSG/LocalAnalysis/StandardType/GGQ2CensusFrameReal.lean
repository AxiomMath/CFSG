module

public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

section Image

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {V : Type} [AddCommGroup V]
  [Module (ZMod p) V]

theorem ggLinImage_inf_left (ι : Additive ↥Bs ≃+ V) (P : Subgroup G) :
    ggLinImage (p := p) ι (Bs ⊓ P) = ggLinImage ι P := by
  ext v
  rw [mem_ggLinImage, mem_ggLinImage, Subgroup.mem_inf]
  exact and_iff_right (Additive.toMul (ι.symm v)).2

theorem finrank_ggLinImage_of_card [Fact p.Prime] [FiniteDimensional (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {D : Subgroup G} (hD : D ≤ Bs) {n : ℕ} (hcard : Nat.card D = p ^ n) :
    finrank (ZMod p) (ggLinImage (p := p) ι D) = n := by
  have h1 : Nat.card (ggLinImage (p := p) ι D) = p ^ n := by
    rw [card_ggLinImage, inf_of_le_right hD, hcard]
  have h2 : Nat.card (ggLinImage (p := p) ι D) =
      p ^ finrank (ZMod p) (ggLinImage (p := p) ι D) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h2.symm.trans h1)

end Image

namespace GGQ2Frame

@[expose] def RawInsideMoved (R : RawFrameData) : Prop :=
  ∀ c : R.Code, R.admissible c → ∃ g ∈ R.normalizerGroup c, ∃ v ∈ R.inside c, g v ≠ v

namespace Realization

variable {G : Type} [Group G] {H E : Subgroup G} {R : RawFrameData}

theorem normalizerGroup_apply_of_mem_cent (real : Realization H E R) {c : R.Code}
    (hc : R.admissible c) {g : R.V ≃ₗ[ZMod 3] R.V} (hg : g ∈ R.normalizerGroup c) {v : R.V}
    (hv : v ∈ R.cent c) : g v = v := by
  have hg' : g ∈ (ggAutomizer (real.component c) E).map (ggLin (p := 3) real.coord) := by
    rwa [real.normalizer_eq c hc]
  obtain ⟨φ, hφmem, hφg⟩ := Subgroup.mem_map.mp hg'
  set b : ↥E := Additive.toMul (real.coord.symm v) with hbdef
  have hbX : (b : G) ∈ Subgroup.centralizer (real.component c : Set G) := by
    refine (mem_ggLinImage (p := 3) real.coord _ v).mp ?_
    rwa [real.cent_eq c hc]
  let K : Subgroup (MulAut ↥E) :=
    { carrier := {φ | φ b = b}
      one_mem' := by simp
      mul_mem' := by
        intro φ ψ hφ hψ
        show (φ * ψ) b = b
        rw [MulAut.mul_apply, hψ, hφ]
      inv_mem' := by
        intro φ hφ
        show φ⁻¹ b = b
        simpa using (congrArg (fun x => φ⁻¹ x) hφ).symm }
  have hK : ggAutomizer (real.component c) E ≤ K := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro φ hφ
    rw [ggInduced] at hφ
    obtain ⟨g', hg'X, -, hφ'⟩ := hφ
    show φ b = b
    apply Subtype.ext
    rw [hφ' b]
    have hcomm : g' * (b : G) = (b : G) * g' :=
      (Subgroup.mem_centralizer_iff.mp hbX) g' hg'X
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : φ b = b := hK hφmem
  have hbcoord : real.coord (Additive.ofMul b) = v := by
    rw [hbdef]
    simp
  rw [← hφg, ← hbcoord, ggLin_apply_ofMul, hfix]

variable [Finite G]

theorem component_eq_of_normalizerGroup_eq (real : Realization H E R) (hmov : RawInsideMoved R)
    {c c' : R.Code} (hc : R.admissible c) (hc' : R.admissible c') {M : Subgroup G}
    (hX : IsComponentOf (real.component c) M) (hX' : IsComponentOf (real.component c') M)
    (h : R.normalizerGroup c = R.normalizerGroup c') : real.component c = real.component c' := by
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hX hX' with heq | hbot
  · exact heq
  · exfalso
    obtain ⟨g, hg, v, hv, hgv⟩ := hmov c hc
    have hg' : g ∈ R.normalizerGroup c' := h ▸ hg
    have hv' : v ∈ R.cent c' := by
      have h1 : v ∈ ggLinImage (p := 3) real.coord (real.component c) := by
        rwa [real.inside_eq c hc]
      have h2 : v ∈ ggLinImage (p := 3) real.coord
          (Subgroup.centralizer (real.component c' : Set G)) :=
        ggLinImage_mono real.coord
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) h1
      rwa [real.cent_eq c' hc'] at h2
    exact hgv (normalizerGroup_apply_of_mem_cent real hc' hg' hv')

omit [Finite G] in
private theorem ggInduced_map_conj_of_mem_abelian {E S : Subgroup G} {x : G}
    (hxE : x ∈ E) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ggInduced (S.map (MulAut.conj x).toMonoidHom) E = ggInduced S E := by
  have hxN : x ∈ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer hxE
  have hxinN : x⁻¹ ∈ Subgroup.normalizer (E : Set G) := Subgroup.inv_mem _ hxN
  have hconj : ∀ (g b : G), g ∈ Subgroup.normalizer (E : Set G) → b ∈ E →
      x * g * x⁻¹ * b * (x * g * x⁻¹)⁻¹ = g * b * g⁻¹ := by
    intro g b hgN hbE
    have hxb : x * b = b * x := hE x hxE b hbE
    have hxb' : x⁻¹ * b * x = b := by
      rw [mul_assoc, ← hxb, ← mul_assoc, inv_mul_cancel, one_mul]
    have hgbE : g * b * g⁻¹ ∈ E := by
      have hmap : E.map (MulAut.conj g).toMonoidHom = E :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
      have hmem : (MulAut.conj g) b ∈ E.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨b, hbE, rfl⟩
      rwa [hmap, MulAut.conj_apply] at hmem
    have hxgb : x * (g * b * g⁻¹) * x⁻¹ = g * b * g⁻¹ := by
      have hcomm : x * (g * b * g⁻¹) = (g * b * g⁻¹) * x := hE x hxE _ hgbE
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    calc x * g * x⁻¹ * b * (x * g * x⁻¹)⁻¹
        = x * (g * (x⁻¹ * b * x) * g⁻¹) * x⁻¹ := by group
      _ = x * (g * b * g⁻¹) * x⁻¹ := by rw [hxb']
      _ = g * b * g⁻¹ := hxgb
  ext φ
  constructor
  · rintro ⟨g', hg'S, hg'N, hφ⟩
    obtain ⟨g, hgS, hg_eq⟩ := Subgroup.mem_map.mp hg'S
    have hgN : g ∈ Subgroup.normalizer (E : Set G) := by
      have hg_eq' : g = x⁻¹ * g' * x := by
        rw [← hg_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hg_eq']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxinN hg'N) hxN
    refine ⟨g, hgS, hgN, ?_⟩
    intro b
    rw [hφ b, ← hg_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      hconj g (b : G) hgN b.2]
  · rintro ⟨g, hgS, hgN, hφ⟩
    refine ⟨x * g * x⁻¹, ?_, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨g, hgS, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hgN) hxinN
    · intro b
      rw [hφ b, hconj g (b : G) hgN b.2]

theorem mem_normalizer_component (real : Realization H E R) (hmov : RawInsideMoved R)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {A : Subgroup G} (hA : A ≤ E) {c : R.Code}
    (hc : R.admissible c) (hocc : R.occurs (ggLinImage (p := 3) real.coord A) c) {x : G}
    (hxE : x ∈ E) (hxH : x ∈ Subgroup.normalizer (H : Set G)) :
    x ∈ Subgroup.normalizer (real.component c : Set G) := by
  set X : Subgroup G := real.component c with hXdef
  set e : G →* G := (MulAut.conj x).toMonoidHom with hedef
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hE x hxE a (hA ha)).symm
  have hH : H.map e = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxH
  have hC : (Subgroup.centralizer (A : Set G)).map e = Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxC)
  have hM : (H ⊓ Subgroup.centralizer (A : Set G)).map e =
      H ⊓ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hH, hC]
  have hX : IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) :=
    (real.occurs_iff A hA X).mpr ⟨c, hc, hocc, hXdef⟩
  set X' : Subgroup G := X.map e with hX'def
  have hX'comp : IsComponentOf X' (H ⊓ Subgroup.centralizer (A : Set G)) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hX x
    rwa [hM] at h1
  obtain ⟨c'', hc'', hocc'', hX''⟩ := (real.occurs_iff A hA X').mp hX'comp
  have hclos : ggAutomizer (real.component c'') E = ggAutomizer (real.component c) E := by
    rw [ggAutomizer, ggAutomizer, ← hX'', ← hXdef,
      ggInduced_map_conj_of_mem_abelian hxE hE]
  have hnorm : R.normalizerGroup c'' = R.normalizerGroup c := by
    rw [← real.normalizer_eq c'' hc'', ← real.normalizer_eq c hc, hclos]
  have hX'comp' : IsComponentOf (real.component c'') (H ⊓ Subgroup.centralizer (A : Set G)) :=
    hX'' ▸ hX'comp
  have hcomp : real.component c'' = real.component c :=
    component_eq_of_normalizerGroup_eq real hmov hc'' hc hX'comp' hX hnorm
  have hXeq : X' = X := by
    rw [hX'', hcomp, ← hXdef]
  have hxnorm : x ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show Subgroup.map e X = X
    rw [← hX'def, hXeq]
  exact hxnorm

omit [Finite G] in
theorem exists_mem_component_ne_one (real : Realization H E R) (hmov : RawInsideMoved R)
    {c : R.Code} (hc : R.admissible c) : ∃ b ∈ E, b ∈ real.component c ∧ b ≠ 1 := by
  obtain ⟨g, -, v, hv, hgv⟩ := hmov c hc
  have hvne : v ≠ 0 := by
    rintro rfl
    exact hgv (map_zero g)
  set b : ↥E := Additive.toMul (real.coord.symm v) with hbdef
  refine ⟨(b : G), b.2, ?_, ?_⟩
  · have h1 : v ∈ ggLinImage (p := 3) real.coord (real.component c) := by
      rwa [real.inside_eq c hc]
    exact (mem_ggLinImage (p := 3) real.coord (real.component c) v).mp h1
  · intro hb
    apply hvne
    have hb' : b = 1 := Subtype.ext hb
    have h0 : real.coord.symm v = 0 := by
      simpa [hbdef] using congrArg Additive.ofMul hb'
    simpa using congrArg real.coord h0

omit [Finite G] in
theorem commutator_component_ne_bot (real : Realization H E R) (hmov : RawInsideMoved R)
    {j k : R.Code} (hj : R.admissible j) (hk : R.admissible k)
    (hjk : R.normalizerGroup j ≤ R.normalizerGroup k) :
    ⁅real.component j, real.component k⁆ ≠ ⊥ := by
  intro hbot
  obtain ⟨g, hg, v, hv, hgv⟩ := hmov j hj
  have hgk : g ∈ R.normalizerGroup k := hjk hg
  have hvk : v ∈ R.cent k := by
    have h1 : v ∈ ggLinImage (p := 3) real.coord (real.component j) := by
      rwa [real.inside_eq j hj]
    have h2 : v ∈ ggLinImage (p := 3) real.coord
        (Subgroup.centralizer (real.component k : Set G)) :=
      ggLinImage_mono real.coord
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) h1
    rwa [real.cent_eq k hk] at h2
  exact hgv (normalizerGroup_apply_of_mem_cent real hk hgk hvk)

end Realization

end GGQ2Frame

end CFSG.StandardType

end
