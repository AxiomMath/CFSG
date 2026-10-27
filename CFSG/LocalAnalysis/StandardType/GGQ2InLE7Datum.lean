module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafSel
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Frame

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

section Datum

variable {G : Type} [Group G] [Finite G] {H Bs K : Subgroup G} {R : RawFrameData}

@[expose] noncomputable def inLNbrDatum (real : Realization H Bs R) {k : R.Code}
    (hkadm : R.admissible k) (hkcomp : real.component k = K) (e : Fin 6 → R.Root)
    (ε : Fin 6 → ℤˣ) (cox : CoxeterMatrix (Fin 6)) (C : Matrix (Fin 6) (Fin 6) ℤ)
    (hW : GGIsWeylMatrix cox) (hC : GGIntCartan cox C)
    (hpair : ∀ i i', ((ε i : ℤ) * ε i') * R.pairing (e i) (e i') = C i i')
    (hnorm : R.normalizerGroup k = Subgroup.closure (R.reflection '' Set.range e))
    (hZ : ∀ b : ↥Bs, real.coord (Additive.ofMul b) ∈
        ggFixedSubmodule (p := 3) real.coord (ggAutomizer K Bs) ↔
        (b : G) ∈ ggBarCentralizer 3 Bs K) :
    GGQ2NbrDatum 3 Bs K where
  Λ := Fin 6
  coxeter := cox
  cartan := C
  V := R.V
  model := real.coord
  simple := fun i => ggLinInv real.coord (R.reflection (e i))
  coroot := fun i => ((ε i : ℤ) : ZMod 3) • R.coroot (e i)
  root := fun i => ((ε i : ℤ) : ZMod 3) • R.root (e i)
  isWeyl := hW
  isCartan := hC
  pairing := fun i j => by
    rw [LinearMap.smul_apply, map_smul, R.pairing_eq, ← hpair i j, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  simple_apply := fun i w => by
    have hε : ((ε i : ℤ) : ZMod 3) * ((ε i : ℤ) : ZMod 3) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    rw [ggLin_ggLinInv, R.reflection_apply, LinearMap.smul_apply, smul_eq_mul, smul_smul,
      mul_right_comm, hε, one_mul]
  automizer_K := by
    have h1 : (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) = R.normalizerGroup k := by
      have h := real.normalizer_eq k hkadm
      rwa [hkcomp] at h
    have h2 := eq_closure_ggLinInv_of_map_eq (p := 3) real.coord (h1.trans hnorm)
    rw [h2, Set.image_image, ← Set.range_comp]
    rfl
  fixed_ZK := hZ

end Datum

theorem ggQ2_fixedZK_of_K1 {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {D J : Subgroup G} {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hK1 : GGQTwoK1 3 B Bs x D J) (hy : y ∈ Bs) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (hfix : ∀ v : V, v ∈ ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) ↔
      v ∈ Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))}) (b : ↥Bs) :
    ι (Additive.ofMul b) ∈ ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) ↔
      (b : G) ∈ ggBarCentralizer 3 Bs K := by
  have hZiff : (b : G) ∈ ggBarCentralizer 3 Bs K ↔ b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
    constructor
    · intro hb
      exact (QTwoD6.ggQ2d6_zpowers_subtype_iff hy b).mp (hK1 y K hnb (b : G) hb.1 hb.2.2)
    · intro hb
      have hby : (b : G) ∈ Subgroup.zpowers y := (QTwoD6.ggQ2d6_zpowers_subtype_iff hy b).mpr hb
      have htr := (hnb.1.2.2.2.2.2 (b : G)).mpr hby
      exact ⟨b.2, htr.2.1, htr.2.2⟩
  exact (hfix _).trans ((QTwoD6.ggQ2d6_model_span_iff ι hy b).trans hZiff.symm)

theorem fixed_closure_reflections_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {κ : Type}
    (r : κ → (V ≃ₗ[ZMod 3] V)) (α : κ → Dual (ZMod 3) V) (h : κ → V)
    (hr : ∀ i w, r i w = w - α i w • h i) (hα : ∀ i, α i (h i) = 2) (S : Set κ) (v : V) :
    (∀ g ∈ Subgroup.closure (r '' S), g v = v) ↔ ∀ i ∈ S, α i v = 0 := by
  have hne : ∀ i, h i ≠ 0 := by
    intro i h0
    have h2 := hα i
    rw [h0, map_zero] at h2
    exact absurd h2 (by decide)
  constructor
  · intro hv i hi
    have hfix : r i v = v := hv _ (Subgroup.subset_closure ⟨i, hi, rfl⟩)
    rw [hr, sub_eq_self, smul_eq_zero] at hfix
    exact hfix.resolve_right (hne i)
  · intro hv g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := hg
      rw [hr, hv i hi, zero_smul, sub_zero]
    | one => rfl
    | mul g g' _ _ hg hg' => rw [LinearEquiv.mul_apply, hg', hg]
    | inv g _ hg =>
      calc g⁻¹ v = g⁻¹ (g v) := by rw [hg]
        _ = v := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem ggQ2_fixed_excRaw_four {G : Type} [Group G] [Finite G] {H Bs K : Subgroup G}
    (real : Realization H Bs (excRaw 4)) {k : Finset (ExcRaw.Root 4)}
    (hkadm : (excRaw 4).admissible k) (hkcomp : real.component k = K) (v : (excRaw 4).V) :
    v ∈ ggFixedSubmodule (p := 3) real.coord (ggAutomizer K Bs) ↔ v ∈ (excRaw 4).cent k := by
  have h1 : (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) =
      Subgroup.closure ((excRaw 4).reflection ''
        {i : ExcRaw.Root 4 | i ∈ k}) := by
    have h := real.normalizer_eq k hkadm
    rw [hkcomp] at h
    rw [h]
    show ExcRaw.normalizerGroup 4 k = ExcRaw.weyl 4 k
    simp only [ExcRaw.normalizerGroup]
    simp
  have h2 : (∀ φ ∈ ggAutomizer K Bs, ggLin (p := 3) real.coord φ v = v) ↔
      ∀ g ∈ (ggAutomizer K Bs).map (ggLin (p := 3) real.coord), g v = v := by
    constructor
    · intro h g hg
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
      exact h φ hφ
    · intro h φ hφ
      exact h _ (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩)
  have h3 := fixed_closure_reflections_iff (excRaw 4).reflection (excRaw 4).root
    (excRaw 4).coroot (excRaw 4).reflection_apply
    (fun i => by rw [(excRaw 4).pairing_eq, (excRaw 4).pairing_self]; norm_num)
    {i : ExcRaw.Root 4 | i ∈ k} v
  refine (mem_ggFixedSubmodule_iff (p := 3)).trans (h2.trans ?_)
  rw [h1]
  refine h3.trans ?_
  change _ ↔ v ∈ (⨅ i ∈ k, LinearMap.ker ((excRaw 4).root i) : Submodule (ZMod 3) (excRaw 4).V)
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

end CFSG.StandardType.GGQ2Frame

end
