module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module CFSG.Quasithin.SmithCurtis CFSG.HardMathSupport.GuralnickMalle
open scoped TensorProduct MonoidAlgebra

private theorem c2slomqsc_splitOver_of_isAlgClosed {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {k : Type} [Field k] [IsAlgClosed k] : SplitOver k H := by
  intro h _
  refine ⟨orderOf h, pow_orderOf_eq_one h, ?_⟩
  have hpos : 0 < orderOf h := orderOf_pos h
  let f : Polynomial k := Polynomial.X ^ orderOf h - 1
  have hm : f.Monic := Polynomial.monic_X_pow_sub_C (1 : k) (Nat.ne_of_gt hpos)
  have heq := (IsAlgClosed.splits f).eq_prod_roots_of_monic hm
  refine ⟨f.roots.toList, ?_⟩
  have hlist : Multiset.map (fun a => Polynomial.X - Polynomial.C a) f.roots =
      ((f.roots.toList.map fun a => (Polynomial.X - Polynomial.C a : Polynomial k) : List _) :
        Multiset _) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [hlist, Multiset.prod_coe] at heq
  exact heq

private theorem c2slomqsc_finrank_range_sub_one_eq_mul {G W : Type} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W)
    [ρ.IsIrreducible] {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) = 2 ^ s) (k : Type)
    [Field k] [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k] (g : G) :
    finrank (ZMod 2) (LinearMap.range (ρ g - 1)) =
      s * finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g - 1)) := by
  classical
  set R := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) with hR
  have h1 := CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.card_eq_pow_finrank_extendScalars
    ρ k
  have h2 :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.card_fixSubGen_eq_pow_finrank_extendScalars
      ρ k (Subgroup.zpowers g)
  rw [hE, ← pow_mul] at h1 h2
  have hfixW : fixSubGen ρ (Subgroup.zpowers g) = LinearMap.ker (ρ g - 1) := by
    ext v
    rw [mem_fixSubGen, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · exact fun h => h g (Subgroup.mem_zpowers g)
    · intro h a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hfix : ∀ m : ℕ, ρ (g ^ m) v = v := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, map_mul, Module.End.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · simpa using hfix m
      · have h' := hfix m
        rw [_root_.zpow_neg, zpow_natCast]
        calc ρ (g ^ m)⁻¹ v = ρ (g ^ m)⁻¹ (ρ (g ^ m) v) := by rw [h']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hfixR : fixSubGen R (Subgroup.zpowers g) = LinearMap.ker (R g - 1) := by
    ext v
    rw [mem_fixSubGen, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · exact fun h => h g (Subgroup.mem_zpowers g)
    · intro h a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hfix : ∀ m : ℕ, R (g ^ m) v = v := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, map_mul, Module.End.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · simpa using hfix m
      · have h' := hfix m
        rw [_root_.zpow_neg, zpow_natCast]
        calc R (g ^ m)⁻¹ v = R (g ^ m)⁻¹ (R (g ^ m) v) := by rw [h']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hW : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rwa [Nat.card_zmod] at this
  have hC : Nat.card (fixSubGen ρ (Subgroup.zpowers g)) =
      2 ^ finrank (ZMod 2) (fixSubGen ρ (Subgroup.zpowers g)) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixSubGen ρ (Subgroup.zpowers g))
    rwa [Nat.card_zmod] at this
  have hd1 : finrank (ZMod 2) W = s * finrank k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G)
      ρ.asModule] ρ.asModule) :=
    Nat.pow_right_injective le_rfl (hW.symm.trans h1)
  have hd2 : finrank (ZMod 2) (fixSubGen ρ (Subgroup.zpowers g)) =
      s * finrank k (fixSubGen R (Subgroup.zpowers g)) :=
    Nat.pow_right_injective le_rfl (hC.symm.trans h2)
  rw [hfixW] at hd2
  rw [hfixR] at hd2
  haveI : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have hrn1 := LinearMap.finrank_range_add_finrank_ker (ρ g - 1)
  have hrn2 := LinearMap.finrank_range_add_finrank_ker (R g - 1)
  have hrn2' : finrank k (LinearMap.range (R g - 1)) +
      finrank k (LinearMap.ker (R g - 1)) =
      finrank k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) := hrn2
  have hs2 : s * finrank k (LinearMap.range (R g - 1)) +
      s * finrank k (LinearMap.ker (R g - 1)) =
      s * finrank k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) := by
    rw [← mul_add, hrn2']
  omega

theorem omq_endfield_scaffold {G : Type} [Group G] [Finite G] {B : Type} {M : CoxeterMatrix B}
    {Weyl : Type} [Group Weyl] [Finite Weyl] {cs : CoxeterSystem M Weyl}
    (D : CurtisDatum G cs 2) {F : Type}
    [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible] :
    ∃ (k : Type) (_ : Field k) (_ : CharP k 2) (_ : IsAlgClosed k)
      (_ : Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k) (_ : F →+* k) (s : ℕ)
      (y : k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule)
      (χ : G → k) (μ : B → k),
      0 < s ∧ Nat.card (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) = 2 ^ s ∧
      IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) ∧
      D.IsCurtisType (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ μ ∧
      (∀ h ∈ D.H, χ h ^ 2 ^ s = χ h) ∧
      (∀ g : G, Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) =
        s * Module.finrank k (LinearMap.range
          (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g - 1))) ∧
      (∀ g : G,
        CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g = 1 ↔ ρ g = 1) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  haveI : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  let k := AlgebraicClosure E
  haveI : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  haveI : Finite ρ.asModule := CFSG.HardMathSupport.GuralnickMalle.finite_asModule ρ
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ρ.asModule
  haveI : Finite (ρ.asModule → ρ.asModule) :=
    Finite.of_equiv (Fin n → Fin n) (Equiv.arrowCongr e e).symm
  haveI : Finite E :=
    Finite.of_injective (fun f : E => (f : ρ.asModule → ρ.asModule)) LinearMap.coe_injective
  let ι : F →+* k :=
    (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
      (K := E) (F₀ := F) (p := 2)).some
  have hsplit : SplitOver k D.H := c2slomqsc_splitOver_of_isAlgClosed
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  obtain ⟨y, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hsimp
  obtain ⟨s, hs, hcard⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.exists_card_endField_eq_two_pow ρ
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ι, s, y, χ, μ,
    hs, hcard, hsimp, ht, ?_, ?_, ?_⟩
  · intro h hh
    have := CFSG.HardMathSupport.GuralnickMalle.isCurtisType_chi_pow_card ρ D k ht hh
    rwa [hcard] at this
  · intro g
    exact c2slomqsc_finrank_range_sub_one_eq_mul ρ hcard k g
  · intro g
    exact CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
      ρ k g

end CFSG.LocalAnalysis.WeakClosure81
