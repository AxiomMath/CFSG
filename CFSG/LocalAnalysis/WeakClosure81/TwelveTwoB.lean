module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section Algebra

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_fixed_vector_of_isPGroup (ρ : G →* LGL 2 V) {P : Subgroup G} (hP : IsPGroup 2 P)
    {W : Submodule (ZMod 2) V} (hW : ∀ g ∈ P, ∀ w ∈ W, ρ g w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ g ∈ P, ρ g w = w := by
  letI : MulAction ↥P ↥W :=
    { smul := fun g w => ⟨ρ g.1 w.1, hW g.1 g.2 w.1 w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ρ (1 : G) w.1 = w.1
        rw [map_one]
        rfl)
      mul_smul := fun g h w => Subtype.ext (by
        show ρ ((g : G) * (h : G)) w.1 = ρ (g : G) (ρ (h : G) w.1)
        rw [map_mul]
        rfl) }
  have hd_ne : Module.finrank (ZMod 2) W ≠ 0 := by
    intro h
    exact hW0 (Submodule.finrank_eq_zero.mp h)
  have hdvd : 2 ∣ Nat.card ↥W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod]
    exact dvd_pow_self 2 hd_ne
  have hfix0 : (0 : ↥W) ∈ MulAction.fixedPoints ↥P ↥W := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (by
      show ρ g.1 (0 : V) = 0
      rw [map_zero])
  obtain ⟨b, hb, hbne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point (p := 2) (G := ↥P) hP
      (↥W) hdvd hfix0
  refine ⟨b.1, b.2, ?_, ?_⟩
  · rintro hb0
    exact hbne (Subtype.ext (by simpa using hb0.symm))
  · intro g hg
    have hfixg : (⟨g, hg⟩ : ↥P) • b = b := (MulAction.mem_fixedPoints.mp hb) ⟨g, hg⟩
    exact congrArg (fun w : ↥W => (w : V)) hfixg

theorem exists_eq_commutator_of_fpf [Finite G] {S : Subgroup G} {x : G}
    (hx : x ∈ normalizer (S : Set G)) (hfpf : ∀ s ∈ S, s * x = x * s → s = 1) {s : G}
    (hs : s ∈ S) : ∃ s' ∈ S, s = s'⁻¹ * (x * s' * x⁻¹) := by
  classical
  haveI : Finite ↥S := inferInstance
  let φ : ↥S → ↥S := fun s' =>
    ⟨s'.1⁻¹ * (x * s'.1 * x⁻¹),
      S.mul_mem (S.inv_mem s'.2) ((Subgroup.mem_normalizer_iff.mp hx s'.1).mp s'.2)⟩
  have hφ_inj : Function.Injective φ := by
    intro s' s'' h
    have heq : s'.1⁻¹ * (x * s'.1 * x⁻¹) = s''.1⁻¹ * (x * s''.1 * x⁻¹) := by
      have := congrArg Subtype.val h
      simpa [φ] using this
    set u : G := s''.1 * s'.1⁻¹ with hu
    have huS : u ∈ S := S.mul_mem s''.2 (S.inv_mem s'.2)
    have hcomm : x * u = u * x := by
      have h1 : s''.1 * (s'.1⁻¹ * (x * s'.1 * x⁻¹)) = x * s''.1 * x⁻¹ := by
        rw [heq]
        group
      have h2 : s''.1 * s'.1⁻¹ * x * s'.1 = x * s''.1 := by
        calc s''.1 * s'.1⁻¹ * x * s'.1
            = (s''.1 * (s'.1⁻¹ * (x * s'.1 * x⁻¹))) * x := by group
          _ = (x * s''.1 * x⁻¹) * x := by rw [h1]
          _ = x * s''.1 := by group
      have h3 : s''.1 * s'.1⁻¹ * x = x * s''.1 * s'.1⁻¹ := by
        calc s''.1 * s'.1⁻¹ * x
            = (s''.1 * s'.1⁻¹ * x * s'.1) * s'.1⁻¹ := by group
          _ = (x * s''.1) * s'.1⁻¹ := by rw [h2]
          _ = x * s''.1 * s'.1⁻¹ := by group
      rw [hu]
      calc x * (s''.1 * s'.1⁻¹) = x * s''.1 * s'.1⁻¹ := by group
        _ = s''.1 * s'.1⁻¹ * x := h3.symm
        _ = (s''.1 * s'.1⁻¹) * x := by group
    have hu1 : u = 1 := hfpf u huS hcomm.symm
    apply Subtype.ext
    have hsu : s''.1 * s'.1⁻¹ = 1 := by rw [← hu]; exact hu1
    exact (mul_inv_eq_one.mp hsu).symm
  have hφ_surj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ_inj
  obtain ⟨s', hs'⟩ := hφ_surj ⟨s, hs⟩
  exact ⟨s'.1, s'.2, by
    have := congrArg Subtype.val hs'
    simpa [φ] using this.symm⟩

theorem card_add_one_le_card_of_free (ρ : G →* LGL 2 V) {T : Subgroup G}
    {Y : Submodule (ZMod 2) V} (hY : ∀ x ∈ T, ∀ y ∈ Y, ρ x y ∈ Y) (hY0 : Y ≠ ⊥)
    (hfree : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ Y, ρ x y = y → y = 0) :
    Nat.card T + 1 ≤ Nat.card Y := by
  classical
  obtain ⟨y₀, hy₀Y, hy₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  let f : ↥T → {y : ↥Y // y ≠ 0} := fun x =>
    ⟨⟨ρ x.1 y₀, hY x.1 x.2 y₀ hy₀Y⟩, by
      intro h
      apply hy₀0
      exact (ρ x.1).injective (by
        have h' : ρ x.1 y₀ = 0 := by
          have := congrArg (fun w : ↥Y => (w : V)) h
          simpa using this
        rw [h', map_zero])⟩
  have hf_inj : Function.Injective f := by
    intro x x' hxx'
    have hρ : ρ x.1 y₀ = ρ x'.1 y₀ := by
      have := congrArg (fun w : {y : ↥Y // y ≠ 0} => ((w.1 : ↥Y) : V)) hxx'
      simpa [f] using this
    have hfix : ρ ((x : G)⁻¹ * (x' : G)) y₀ = y₀ := by
      rw [map_mul, map_inv, LinearEquiv.mul_apply, ← hρ]
      exact (ρ (x : G)).symm_apply_apply y₀
    have hmem : (x : G)⁻¹ * (x' : G) ∈ T := T.mul_mem (T.inv_mem x.2) x'.2
    by_contra hne
    have hne' : (x : G)⁻¹ * (x' : G) ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.mp h))
    exact hy₀0 (hfree ((x : G)⁻¹ * (x' : G)) hmem hne' y₀ hy₀Y hfix)
  have hcard : Nat.card {y : ↥Y // y ≠ 0} + 1 = Nat.card ↥Y := by
    haveI : Fintype ↥Y := Fintype.ofFinite _
    haveI : Fintype {y : ↥Y // y ≠ 0} := Fintype.ofFinite _
    have h : Fintype.card {y : ↥Y // y ≠ 0} = Fintype.card ↥Y - 1 := by
      rw [Fintype.card_subtype_compl (p := fun y : ↥Y => y = 0),
        Fintype.card_subtype_eq (0 : ↥Y)]
    rw [Nat.card_eq_fintype_card (α := {y : ↥Y // y ≠ 0}), h]
    have hYpos : 1 ≤ Fintype.card ↥Y := Fintype.card_pos_iff.mpr ⟨⟨y₀, hy₀Y⟩⟩
    have hYcard : Fintype.card ↥Y = Nat.card ↥Y := (Nat.card_eq_fintype_card).symm
    omega
  exact le_trans (Nat.add_le_add_right (Nat.card_le_card_of_injective f hf_inj) 1)
    (le_of_eq hcard)

@[expose] def RegularOnNonzero (ρ : G →* LGL 2 V) (T : Subgroup G)
    (Z : Submodule (ZMod 2) V) : Prop :=
  (∀ x ∈ T, x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0) ∧
    ∀ z ∈ Z, z ≠ 0 → ∀ z' ∈ Z, z' ≠ 0 → ∃ x ∈ T, ρ x z = z'

theorem regularOnNonzero_of_card (ρ : G →* LGL 2 V) {T : Subgroup G}
    {Z : Submodule (ZMod 2) V} (hZ : ∀ x ∈ T, ∀ z ∈ Z, ρ x z ∈ Z) (hZ0 : Z ≠ ⊥)
    (hfree : ∀ x ∈ T, x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0)
    (hcard : Nat.card T + 1 = Nat.card Z) : RegularOnNonzero ρ T Z := by
  classical
  refine ⟨hfree, ?_⟩
  intro z hz hz0 z' hz' hz'0
  let f : ↥T → {y : ↥Z // y ≠ 0} := fun x =>
    ⟨⟨ρ x.1 z, hZ x.1 x.2 z hz⟩, by
      intro h
      apply hz0
      exact (ρ x.1).injective (by
        have h' : ρ x.1 z = 0 := by
          have := congrArg (fun w : ↥Z => (w : V)) h
          simpa using this
        rw [h', map_zero])⟩
  have hf_inj : Function.Injective f := by
    intro x x' hxx'
    have hρ : ρ x.1 z = ρ x'.1 z := by
      have := congrArg (fun w : {y : ↥Z // y ≠ 0} => ((w.1 : ↥Z) : V)) hxx'
      simpa [f] using this
    have hfix : ρ ((x : G)⁻¹ * (x' : G)) z = z := by
      rw [map_mul, map_inv, LinearEquiv.mul_apply, ← hρ]
      exact (ρ (x : G)).symm_apply_apply z
    have hmem : (x : G)⁻¹ * (x' : G) ∈ T := T.mul_mem (T.inv_mem x.2) x'.2
    by_contra hne
    have hne' : (x : G)⁻¹ * (x' : G) ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.mp h))
    exact hz0 (hfree ((x : G)⁻¹ * (x' : G)) hmem hne' z hz hfix)
  have hcardβ : Nat.card {y : ↥Z // y ≠ 0} = Nat.card T := by
    haveI : Fintype ↥Z := Fintype.ofFinite _
    haveI : Fintype {y : ↥Z // y ≠ 0} := Fintype.ofFinite _
    have h : Fintype.card {y : ↥Z // y ≠ 0} = Fintype.card ↥Z - 1 := by
      rw [Fintype.card_subtype_compl (p := fun y : ↥Z => y = 0),
        Fintype.card_subtype_eq (0 : ↥Z)]
    rw [Nat.card_eq_fintype_card (α := {y : ↥Z // y ≠ 0}), h]
    have hZpos : 1 ≤ Fintype.card ↥Z := Fintype.card_pos_iff.mpr ⟨⟨z, hz⟩⟩
    have hZcard : Fintype.card ↥Z = Nat.card T + 1 := by
      rw [← Nat.card_eq_fintype_card (α := ↥Z), ← hcard]
    omega
  have hbij : Function.Bijective f :=
    hf_inj.bijective_of_nat_card_le (le_of_eq hcardβ)
  obtain ⟨x, hx⟩ := hbij.2 ⟨⟨z', hz'⟩, by simpa using hz'0⟩
  exact ⟨x, x.2, by
    have := congrArg (fun w : {y : ↥Z // y ≠ 0} => ((w.1 : ↥Z) : V)) hx
    simpa [f] using this⟩

theorem eq_zero_of_mem_commSpace_of_fixed (ρ : G →* LGL 2 V) {T : Subgroup G}
    (hT : Odd (Nat.card T)) (W : Submodule (ZMod 2) V) {y : V}
    (hy : y ∈ commSpace (T.map ρ) W) (hfix : ∀ x ∈ T, ρ x y = y) : y = 0 := by
  classical
  have hT0 : Nat.card T ≠ 0 := by
    obtain ⟨k, hk⟩ := hT
    omega
  haveI : Finite ↥T := Nat.finite_of_card_ne_zero hT0
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  let e : V →ₗ[ZMod 2] V := ∑ x : ↥T, ((ρ x.1 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
  have hS : ∀ v : V, e v = ∑ x : ↥T, (ρ x.1 : V ≃ₗ[ZMod 2] V) v := fun v => by
    simp [e, LinearMap.sum_apply]
  have hS2 : ∀ (x₀ : ↥T) (u : V), e (ρ x₀.1 u) = e u := by
    intro x₀ u
    rw [hS, hS]
    refine Fintype.sum_equiv (Equiv.mulRight x₀) _ _ (fun x => ?_)
    show (ρ (x : G)) ((ρ (x₀ : G)) u) = (ρ ((x : G) * (x₀ : G))) u
    rw [map_mul]
    rfl
  have hker : commSpace (T.map ρ) W ≤ LinearMap.ker e := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨k, hk, u, hu, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hk
    show e (ρ x₀ u - u) = 0
    rw [map_sub, hS2 ⟨x₀, hx₀⟩ u, sub_self]
  have hy0 : e y = 0 := LinearMap.mem_ker.mp (hker hy)
  have hfix_e : e y = y := by
    rw [hS]
    have hsum : (∑ x : ↥T, (ρ x.1 : V ≃ₗ[ZMod 2] V) y) = ∑ _x : ↥T, y :=
      Finset.sum_congr rfl (fun x _ => hfix x.1 x.2)
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
      ← Nat.cast_smul_eq_nsmul (ZMod 2) (Nat.card T) y, ZMod.natCast_eq_one_iff_odd.mpr hT,
      one_smul]
  exact hfix_e.symm.trans hy0

theorem map_mem_commSpace_map (ρ : G →* LGL 2 V) {T : Subgroup G} {W : Submodule (ZMod 2) V}
    (hW : ∀ x ∈ T, ∀ w ∈ W, ρ x w ∈ W) {x : G} (hx : x ∈ T) {y : V}
    (hy : y ∈ commSpace (T.map ρ) W) : ρ x y ∈ commSpace (T.map ρ) W := by
  induction hy using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨k, hk, u, hu, rfl⟩ := hv
      obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hk
      have hkx : x * x₀ * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hx hx₀) (T.inv_mem hx)
      have hux : ρ x u ∈ W := hW x hx u hu
      have hgen : ρ (x * x₀ * x⁻¹) (ρ x u) - ρ x u ∈ commSpace (T.map ρ) W :=
        sub_mem_commSpace (K := T.map ρ) (U := W) (Subgroup.mem_map_of_mem ρ hkx) hux
      have h1 : ρ x (ρ x₀ u) = ρ (x * x₀) u := by
        rw [← LinearEquiv.mul_apply, ← map_mul]
      have h2 : ρ (x * x₀ * x⁻¹) (ρ x u) = ρ (x * x₀) u := by
        rw [← LinearEquiv.mul_apply, ← map_mul]
        rw [show (x * x₀ * x⁻¹) * x = x * x₀ by group]
      have heq : ρ x (ρ x₀ u - u) = ρ (x * x₀ * x⁻¹) (ρ x u) - ρ x u := by
        rw [map_sub, h1, h2]
      rw [heq]
      exact hgen
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ha

theorem card_submodule_eq_two_pow_finrank (W : Submodule (ZMod 2) V) :
    Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod]

end Algebra

end CFSG.LocalAnalysis.WeakClosure81
