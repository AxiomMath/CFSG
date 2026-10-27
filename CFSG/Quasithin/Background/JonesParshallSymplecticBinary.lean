module

public import CFSG.Quasithin.Background.JonesParshallWords
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveInvariants
public import CFSG.ClassicalGroups.Alternating.TransvectionGenerationTwo
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticCentralizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Alternating

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def binarySymplecticNatural (b : LinearMap.BilinForm (ZMod 2) E) :
    Representation (ZMod 2) (bilinIsometryGroup b) E where
  toFun s := ((s : LinearMap.GeneralLinearGroup (ZMod 2) E) : E →ₗ[ZMod 2] E)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem binarySymplecticNatural_apply (b : LinearMap.BilinForm (ZMod 2) E)
    (s : bilinIsometryGroup b) (x : E) :
    binarySymplecticNatural b s x = OddQuadraticFive.sE s x :=
  rfl

@[expose] def transvectionLine (b : LinearMap.BilinForm (ZMod 2) E) (v : E) :
    Submodule (ZMod 2) (Module.Dual (ZMod 2) E) :=
  Submodule.span (ZMod 2) {b.flip v}

theorem dual_tau_eq {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.IsAlt) (v : E)
    (ℓ : Module.Dual (ZMod 2) E) :
    Representation.dual (binarySymplecticNatural b) (OddQuadraticFive.tau hb v) ℓ =
      ℓ + (ℓ v) • (b.flip v) := by
  have htau_inv : (OddQuadraticFive.tau hb v)⁻¹ = OddQuadraticFive.tau hb v :=
    Subtype.ext (BinarySymplecticTransvection.inv_eq hb v)
  ext x
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, htau_inv,
    binarySymplecticNatural_apply, LinearMap.comp_apply]
  rw [OddQuadraticFive.sE_tau, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [show (b.flip v) x = b x v from rfl]
  ring

theorem dual_cocycle_transvection_mem_span {b : LinearMap.BilinForm (ZMod 2) E}
    (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (c : Z1 (Representation.dual (binarySymplecticNatural b))) (v : E) :
    (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) ∈
      Submodule.span (ZMod 2) {b.flip v} := by
  have hc1 : (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) 1 = 0 := by
    have h := c.2 1 1
    simp only [one_mul, map_one, Module.End.one_apply] at h
    rw [add_self_eq_zero_zmod_two] at h
    exact h
  by_cases hv : v = 0
  · subst v
    rw [show OddQuadraticFive.tau hb 0 = 1 from by
      apply Subtype.ext
      exact BinarySymplecticTransvection.zero_eq_one hb, hc1]
    exact Submodule.zero_mem _
  have hval_v : ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v)) v = 0 := by
    have h := c.2 (OddQuadraticFive.tau hb v) (OddQuadraticFive.tau hb v)
    have htau_sq : OddQuadraticFive.tau hb v * OddQuadraticFive.tau hb v = 1 :=
      Subtype.ext (BinarySymplecticTransvection.mul_self hb v)
    rw [htau_sq, hc1, dual_tau_eq hb v] at h
    have hz : ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) v) • (b.flip v) = 0 := by
      have h' : (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
          ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
            ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) v) • (b.flip v)) = 0 := h.symm
      rw [← add_assoc, add_self_eq_zero_zmod_two, zero_add] at h'
      exact h'
    obtain ⟨x, hx⟩ := BinarySymplecticTransvection.exists_apply_eq_one hnd hv
    have hx' := congrArg (fun f : Module.Dual (ZMod 2) E => f x) hz
    simp only [LinearMap.smul_apply, LinearMap.zero_apply] at hx'
    change ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) v) • b x v = 0 at hx'
    rw [hx, smul_eq_mul, mul_one] at hx'
    exact hx'
  have hker : ∀ w : E, (b.flip v) w = 0 →
      ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v)) w = 0 := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    by_cases hwv : w = v
    · rw [hwv]
      exact hval_v
    have hφv : b.flip v ≠ 0 := by
      intro hzero
      exact hv (hnd.2 v fun x => by
        have hx := congrArg (fun f : Module.Dual (ZMod 2) E => f x) hzero
        change b x v = 0 at hx
        exact hx)
    have hφw : b.flip w ≠ 0 := by
      intro hzero
      exact hw0 (hnd.2 w fun x => by
        have hx := congrArg (fun f : Module.Dual (ZMod 2) E => f x) hzero
        change b x w = 0 at hx
        exact hx)
    have hφne : b.flip v ≠ b.flip w := by
      intro heq
      exact hwv (sub_eq_zero.mp (hnd.2 (v - w) fun x => by
        have hx := congrArg (fun f : Module.Dual (ZMod 2) E => f x) heq
        change b x v = b x w at hx
        rw [map_sub, hx, sub_self])).symm
    have hw' : b w v = 0 := by
      change b w v = 0 at hw
      exact hw
    have hvw : b v w = 0 := by
      rwa [BinarySymplecticTransvection.symm_apply hb] at hw'
    have hcomm_gl : binarySymplecticTransvection b hb v *
        binarySymplecticTransvection b hb w =
          binarySymplecticTransvection b hb w *
            binarySymplecticTransvection b hb v := by
      rw [← symplecticTransvection_one_eq_binarySymplecticTransvection hb v,
        ← symplecticTransvection_one_eq_binarySymplecticTransvection hb w]
      exact symplecticTransvection_comm hb hvw 1 1
    have hcomm : OddQuadraticFive.tau hb v * OddQuadraticFive.tau hb w =
        OddQuadraticFive.tau hb w * OddQuadraticFive.tau hb v := by
      apply Subtype.ext
      exact hcomm_gl
    have hprod : (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v * OddQuadraticFive.tau hb w) =
        (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w * OddQuadraticFive.tau hb v) := by
      rw [hcomm]
    have h1 := c.2 (OddQuadraticFive.tau hb v) (OddQuadraticFive.tau hb w)
    have h2 := c.2 (OddQuadraticFive.tau hb w) (OddQuadraticFive.tau hb v)
    rw [← hprod] at h2
    have heq : (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
        Representation.dual (binarySymplecticNatural b) (OddQuadraticFive.tau hb v)
          ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w)) =
        (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
          Representation.dual (binarySymplecticNatural b) (OddQuadraticFive.tau hb w)
            ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v)) := h1.symm.trans h2
    rw [dual_tau_eq hb v ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w)),
      dual_tau_eq hb w ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v))] at heq
    have hindep : ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) v) • (b.flip v) =
        ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) w) • (b.flip w) := by
      have heq' : (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
          ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
            ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) v) • (b.flip v)) =
          (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
            ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
              ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) w) • (b.flip w)) := by
        calc
          (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
              ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
                ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) v) • (b.flip v)) =
            (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
              (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
                ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) v) • (b.flip v) := by abel
          _ = (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
              ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
                ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) v) • (b.flip v)) := by abel
          _ = (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
              ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
                ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) w) • (b.flip w)) := heq
          _ = (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) +
              ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) +
                ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) w) • (b.flip w)) := by abel
      exact add_left_cancel (add_left_cancel heq')
    have hsum : ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb w) v) • (b.flip v) +
        ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) w) • (b.flip w) = 0 := by
      rw [hindep, add_self_eq_zero_zmod_two]
    exact (OddQuadraticFive.smul_add_smul_eq_zero hφv hφw hφne hsum).2
  obtain ⟨u, hu⟩ := BinarySymplecticTransvection.exists_apply_eq_one hnd hv
  have hline : ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) u) • (b.flip v) =
      (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) := by
    ext x
    have hmem : (b.flip v) (x + b x v • u) = 0 := by
      rw [map_add, map_smul]
      change b x v + (b x v) • b u v = 0
      rw [hu, smul_eq_mul, mul_one, add_self_eq_zero_zmod_two]
    have h0 := hker (x + b x v • u) hmem
    rw [map_add, map_smul] at h0
    have hx : ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
        (OddQuadraticFive.tau hb v) u) • (b.flip v x) =
        (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
          (OddQuadraticFive.tau hb v) x := by
      have h0' : (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
          (OddQuadraticFive.tau hb v) x =
          (b x v) • (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
            (OddQuadraticFive.tau hb v) u :=
        OddQuadraticFive.eq_of_add_eq_zero_zmod2 h0
      rw [h0']
      change ((c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
        (OddQuadraticFive.tau hb v) u) • (b x v) =
        (b x v) • (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
          (OddQuadraticFive.tau hb v) u
      rw [smul_eq_mul, smul_eq_mul, mul_comm]
    simpa only [LinearMap.smul_apply] using hx
  exact Submodule.mem_span_singleton.mpr ⟨(c : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (OddQuadraticFive.tau hb v) u, hline⟩

@[expose] noncomputable def transvectionEvaluation {b : LinearMap.BilinForm (ZMod 2) E}
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (s : Finset E) :
    Z1 (Representation.dual (binarySymplecticNatural b)) →ₗ[ZMod 2]
      ((i : s) → transvectionLine b (i : E)) where
  toFun c i :=
    ⟨(c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
        (OddQuadraticFive.tau hb (i : E)),
      dual_cocycle_transvection_mem_span hb hnd c (i : E)⟩
  map_add' c d := by
    funext i
    exact Subtype.ext rfl
  map_smul' a c := by
    funext i
    exact Subtype.ext rfl

theorem exists_tau_generating_finset [FiniteDimensional (ZMod 2) E]
    {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    ∃ s : Finset E, (∀ x ∈ s, x ≠ 0) ∧
      s.card ≤ Module.finrank (ZMod 2) E + 1 ∧
        Subgroup.closure (OddQuadraticFive.tau hb '' (s : Set E)) = ⊤ := by
  obtain ⟨s, hs_ne, hs_card, hs_gen⟩ :=
    exists_card_le_closure_symplecticTransvection_eq_two
      (K := ZMod 2) (V := E) (B := b) (by rw [Nat.card_zmod]) hb hnd
  refine ⟨s, hs_ne, hs_card, ?_⟩
  have hgen_bin : Subgroup.closure
      ((fun x => binarySymplecticTransvection b hb x) '' (s : Set E)) =
        bilinIsometryGroup b := by
    simpa only [symplecticTransvection_one_eq_binarySymplecticTransvection hb] using hs_gen
  let j : bilinIsometryGroup b →* LinearMap.GeneralLinearGroup (ZMod 2) E :=
    (bilinIsometryGroup b).subtype
  have hmap : Subgroup.map j
      (Subgroup.closure (OddQuadraticFive.tau hb '' (s : Set E))) =
        bilinIsometryGroup b := by
    rw [MonoidHom.map_closure]
    have himg : j '' (OddQuadraticFive.tau hb '' (s : Set E)) =
        (fun x => binarySymplecticTransvection b hb x) '' (s : Set E) := by
      ext g
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨OddQuadraticFive.tau hb y, ⟨y, hy, rfl⟩, rfl⟩
    rw [himg, hgen_bin]
  have hmap_top : Subgroup.map j (⊤ : Subgroup (bilinIsometryGroup b)) =
      bilinIsometryGroup b := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective (bilinIsometryGroup b).subtype_injective
    (hmap.trans hmap_top.symm)

theorem transvectionEvaluation_injective {b : LinearMap.BilinForm (ZMod 2) E}
    (hb : b.IsAlt) (hnd : b.Nondegenerate) {s : Finset E}
    (hs : Subgroup.closure (OddQuadraticFive.tau hb '' (s : Set E)) = ⊤) :
    Function.Injective (transvectionEvaluation hb hnd s) := by
  intro c d hcd
  let μ : bilinIsometryGroup b →* AddMonoid.End (Module.Dual (ZMod 2) E) :=
    { toFun := fun g =>
        (Representation.dual (binarySymplecticNatural b) g).toAddMonoidHom
      map_one' := by
        apply AddMonoid.End.ext (Module.Dual (ZMod 2) E)
        intro x
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        apply AddMonoid.End.ext (Module.Dual (ZMod 2) E)
        intro x
        rw [map_mul]
        rfl }
  let f : Z1 (Representation.dual (binarySymplecticNatural b)) := c - d
  have hmem : (f : bilinIsometryGroup b → Module.Dual (ZMod 2) E) ∈ Z1A μ := by
    intro g h
    change (f : bilinIsometryGroup b → Module.Dual (ZMod 2) E) (g * h) =
      (f : bilinIsometryGroup b → Module.Dual (ZMod 2) E) g +
        (Representation.dual (binarySymplecticNatural b) g)
          ((f : bilinIsometryGroup b → Module.Dual (ZMod 2) E) h)
    exact f.2 g h
  have hvanish : ∀ t ∈ (OddQuadraticFive.tau hb '' (s : Set E)),
      (f : bilinIsometryGroup b → Module.Dual (ZMod 2) E) t = 0 := by
    rintro _ ⟨i, hi, rfl⟩
    have hval : (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
        (OddQuadraticFive.tau hb i) =
        (d : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
          (OddQuadraticFive.tau hb i) := by
      have h := congrFun hcd ⟨i, hi⟩
      exact congrArg Subtype.val h
    change (c : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
        (OddQuadraticFive.tau hb i) -
      (d : bilinIsometryGroup b → Module.Dual (ZMod 2) E)
        (OddQuadraticFive.tau hb i) = 0
    rw [hval, sub_self]
  have hzero : (f : bilinIsometryGroup b → Module.Dual (ZMod 2) E) = 0 :=
    eq_zero_of_vanish_closure hmem hs hvanish
  exact Subtype.ext (sub_eq_zero.mp hzero)

theorem finrank_transvectionEvaluation_codomain [FiniteDimensional (ZMod 2) E]
    {b : LinearMap.BilinForm (ZMod 2) E}
    (hnd : b.Nondegenerate) {s : Finset E} (hs : ∀ x ∈ s, x ≠ 0) :
    Module.finrank (ZMod 2) ((i : s) → transvectionLine b (i : E)) = s.card := by
  haveI : ∀ i : s, Module.Free (ZMod 2) (transvectionLine b (i : E)) :=
    fun i => Module.Free.of_divisionRing (ZMod 2) (transvectionLine b (i : E))
  rw [Module.finrank_pi_fintype]
  have hline : ∀ i : s, Module.finrank (ZMod 2) (transvectionLine b (i : E)) = 1 := by
    intro i
    apply finrank_span_singleton
    intro hzero
    exact hs (i : E) i.2 (hnd.2 (i : E) fun x => by
      have hx := congrArg (fun f : Module.Dual (ZMod 2) E => f x) hzero
      simpa [LinearMap.flip_apply] using hx)
  calc
    ∑ i : s, Module.finrank (ZMod 2) (transvectionLine b (i : E)) =
        ∑ _ : s, (1 : ℕ) := Finset.sum_congr rfl fun i _ => hline i
    _ = Fintype.card s := by simp
    _ = s.card := Fintype.card_coe s

theorem finrank_Z1_binarySymplecticNatural_dual_le [FiniteDimensional (ZMod 2) E]
    {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    Module.finrank (ZMod 2)
      (Z1 (Representation.dual (binarySymplecticNatural b))) ≤
        Module.finrank (ZMod 2) E + 1 := by
  obtain ⟨s, hs_ne, hs_card, hs_gen⟩ := exists_tau_generating_finset hb hnd
  let ev := transvectionEvaluation hb hnd s
  have hev : Function.Injective ev := transvectionEvaluation_injective hb hnd hs_gen
  have hle : Module.finrank (ZMod 2) (Z1 (Representation.dual (binarySymplecticNatural b))) ≤
      Module.finrank (ZMod 2) ((i : s) → transvectionLine b (i : E)) :=
    LinearMap.finrank_le_finrank_of_injective hev
  rw [finrank_transvectionEvaluation_codomain hnd hs_ne] at hle
  omega

@[expose] noncomputable def coboundaryToZ1 (b : LinearMap.BilinForm (ZMod 2) E) :
    Module.Dual (ZMod 2) E →ₗ[ZMod 2]
      Z1 (Representation.dual (binarySymplecticNatural b)) :=
  LinearMap.codRestrict (Z1 (Representation.dual (binarySymplecticNatural b)))
    (coboundary (Representation.dual (binarySymplecticNatural b)))
    (fun x => B1_le_Z1 (Representation.dual (binarySymplecticNatural b))
      (LinearMap.mem_range_self _ x))

theorem coboundaryToZ1_eq_zero {b : LinearMap.BilinForm (ZMod 2) E}
    (hb : b.IsAlt) (hnd : b.Nondegenerate)
    {ℓ : Module.Dual (ZMod 2) E} (h : coboundaryToZ1 b ℓ = 0) : ℓ = 0 := by
  have hinv : ∀ g : bilinIsometryGroup b,
      Representation.dual (binarySymplecticNatural b) g ℓ = ℓ := by
    intro g
    have hg : (coboundary (Representation.dual (binarySymplecticNatural b)) ℓ) g = 0 := by
      have hfun := congrArg
        (fun x : Z1 (Representation.dual (binarySymplecticNatural b)) =>
          (x : bilinIsometryGroup b → Module.Dual (ZMod 2) E) g) h
      simpa [coboundaryToZ1] using hfun
    exact sub_eq_zero.mp hg
  have hℓ : ∀ (s : bilinIsometryGroup b) x, ℓ (OddQuadraticFive.sE s x) = ℓ x := by
    intro s x
    have hval : ℓ (((binarySymplecticNatural b) s⁻¹) (OddQuadraticFive.sE s x)) =
        ℓ (OddQuadraticFive.sE s x) := by
      simpa only [Representation.dual_apply, Module.Dual.transpose_apply,
        LinearMap.comp_apply] using
        congrArg (fun f : Module.Dual (ZMod 2) E => f (OddQuadraticFive.sE s x)) (hinv s)
    rw [show (binarySymplecticNatural b) s⁻¹ (OddQuadraticFive.sE s x) = x from by
      change OddQuadraticFive.sE s⁻¹ (OddQuadraticFive.sE s x) = x
      exact OddQuadraticFive.sE_inv_apply s x] at hval
    exact hval.symm
  ext x
  exact OddQuadraticFive.eq_zero_of_invariant_linear hb hnd ℓ hℓ x

theorem coboundaryToZ1_injective {b : LinearMap.BilinForm (ZMod 2) E}
    (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    Function.Injective (coboundaryToZ1 b) := by
  intro ℓ ℓ' h
  have hzero : coboundaryToZ1 b (ℓ - ℓ') = 0 := by
    rw [map_sub, h, sub_self]
  have hℓ : ℓ - ℓ' = 0 := coboundaryToZ1_eq_zero hb hnd hzero
  exact sub_eq_zero.mp hℓ

theorem finrank_B1_binarySymplecticNatural_dual [FiniteDimensional (ZMod 2) E]
    {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    Module.finrank (ZMod 2) (B1 (Representation.dual (binarySymplecticNatural b))) =
      Module.finrank (ZMod 2) E := by
  have hδ : Function.Injective (coboundaryToZ1 b) := coboundaryToZ1_injective hb hnd
  have hcob : Function.Injective
      (coboundary (Representation.dual (binarySymplecticNatural b))) := by
    intro x y h
    apply hδ
    exact Subtype.ext h
  rw [B1, LinearMap.finrank_range_of_inj hcob, Subspace.dual_finrank_eq]

theorem finrank_H1_binarySymplecticNatural_dual_le_one [FiniteDimensional (ZMod 2) E]
    {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    Module.finrank (ZMod 2)
      (H1 (Representation.dual (binarySymplecticNatural b))) ≤ 1 := by
  haveI : Finite E := Module.finite_of_finite (ZMod 2)
  haveI : Finite (Module.Dual (ZMod 2) E) := Module.finite_of_finite (ZMod 2)
  haveI : Finite (E →ₗ[ZMod 2] E) :=
    Finite.of_injective (fun f : E →ₗ[ZMod 2] E => (f : E → E))
      (fun f g h => LinearMap.ext fun x => congrFun h x)
  haveI : Finite (LinearMap.GeneralLinearGroup (ZMod 2) E) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup (ZMod 2) E =>
      (u : Module.End (ZMod 2) E)) (fun u v h => Units.ext h)
  haveI : Finite (bilinIsometryGroup b) := Subtype.finite
  haveI : Finite (bilinIsometryGroup b → Module.Dual (ZMod 2) E) := Pi.finite
  haveI : Finite (Z1 (Representation.dual (binarySymplecticNatural b))) := Subtype.finite
  haveI : Finite (B1 (Representation.dual (binarySymplecticNatural b))) := Subtype.finite
  haveI : Finite (H1 (Representation.dual (binarySymplecticNatural b))) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI : Fintype (Z1 (Representation.dual (binarySymplecticNatural b))) := Fintype.ofFinite _
  letI : Fintype (B1 (Representation.dual (binarySymplecticNatural b))) := Fintype.ofFinite _
  letI : Fintype (H1 (Representation.dual (binarySymplecticNatural b))) := Fintype.ofFinite _
  have hZcard : Nat.card (Z1 (Representation.dual (binarySymplecticNatural b))) =
      2 ^ Module.finrank (ZMod 2)
        (Z1 (Representation.dual (binarySymplecticNatural b))) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hBcard : Nat.card (B1 (Representation.dual (binarySymplecticNatural b))) =
      2 ^ Module.finrank (ZMod 2)
        (B1 (Representation.dual (binarySymplecticNatural b))) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hHcard : Nat.card (H1 (Representation.dual (binarySymplecticNatural b))) =
      2 ^ Module.finrank (ZMod 2)
        (H1 (Representation.dual (binarySymplecticNatural b))) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hZle : Nat.card (Z1 (Representation.dual (binarySymplecticNatural b))) ≤
      2 * 2 ^ Module.finrank (ZMod 2) E := by
    calc
      Nat.card (Z1 (Representation.dual (binarySymplecticNatural b))) =
          2 ^ Module.finrank (ZMod 2)
            (Z1 (Representation.dual (binarySymplecticNatural b))) := hZcard
      _ ≤ 2 ^ (Module.finrank (ZMod 2) E + 1) :=
        Nat.pow_le_pow_right (by norm_num)
          (finrank_Z1_binarySymplecticNatural_dual_le hb hnd)
      _ = 2 * 2 ^ Module.finrank (ZMod 2) E := by
        rw [pow_succ]
        ring
  have hBeq : Nat.card (B1 (Representation.dual (binarySymplecticNatural b))) =
      2 ^ Module.finrank (ZMod 2) E := by
    rw [hBcard, finrank_B1_binarySymplecticNatural_dual hb hnd]
  have hHle : Nat.card (H1 (Representation.dual (binarySymplecticNatural b))) ≤ 2 := by
    have hcard := card_H1_mul (Representation.dual (binarySymplecticNatural b))
    have hBpos : 0 < Nat.card (B1 (Representation.dual (binarySymplecticNatural b))) :=
      Nat.card_pos
    have hmul : Nat.card (H1 (Representation.dual (binarySymplecticNatural b))) *
        Nat.card (B1 (Representation.dual (binarySymplecticNatural b))) ≤
          2 * Nat.card (B1 (Representation.dual (binarySymplecticNatural b))) := by
      calc
        Nat.card (H1 (Representation.dual (binarySymplecticNatural b))) *
            Nat.card (B1 (Representation.dual (binarySymplecticNatural b))) =
            Nat.card (Z1 (Representation.dual (binarySymplecticNatural b))) := hcard
        _ ≤ 2 * 2 ^ Module.finrank (ZMod 2) E := hZle
        _ = 2 * Nat.card (B1 (Representation.dual (binarySymplecticNatural b))) := by
          rw [hBeq]
    exact Nat.le_of_mul_le_mul_right hmul hBpos
  have hfinle : 2 ^ Module.finrank (ZMod 2)
      (H1 (Representation.dual (binarySymplecticNatural b))) ≤ 2 := by
    rw [← hHcard]
    exact hHle
  by_contra h
  have h2 : 2 ≤ Module.finrank (ZMod 2)
      (H1 (Representation.dual (binarySymplecticNatural b))) := by omega
  have h4 : 4 ≤ 2 ^ Module.finrank (ZMod 2)
      (H1 (Representation.dual (binarySymplecticNatural b))) := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h2
    norm_num at this ⊢
    exact this
  omega

end CFSG.Quasithin.JonesParshall
