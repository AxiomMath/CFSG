module

public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

section Lang

theorem lang_conjugator_D4 {K : Type} [Field K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL TwistTag.D4.tag L) (hn : n ∈ adjointGroup TwistTag.D4.tag L) :
    ∃ g0 : ModGL TwistTag.D4.tag L, g0 ∈ adjointGroup TwistTag.D4.tag L ∧
      twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).2
    TwistTag.D4 1
  obtain ⟨g, hg⟩ := hLang ⟨n, hn⟩
  refine ⟨(g : ModGL TwistTag.D4.tag L), g.2, ?_⟩
  have h1 : S g = g * ⟨n, hn⟩ := by
    rw [hg, mul_inv_cancel_left]
  have h2 := hS g
  rw [h1, zpow_one] at h2
  exact h2.symm.trans (by rfl)

end Lang

section Torus

variable {L : Type} [Field L]

theorem d4_perm_symm_apply (i : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.perm.symm (TwistTag.D4.perm i) = i :=
  TwistTag.D4.perm.symm_apply_apply i

theorem permLattice_symm_permLattice (y : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm.symm (permLattice TwistTag.D4.perm y) = y := by
  funext i
  change y (TwistTag.D4.perm.symm (TwistTag.D4.perm i)) = y i
  rw [Equiv.symm_apply_apply]

theorem twisted_weylTuple_eq_iff_D4 (Fr : L →+* L) (v : WeylGroup TwistTag.D4.tag)
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.D4.perm.symm x)
    (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    weylTuple v (fun i => Units.map Fr.toMonoidHom (a (TwistTag.D4.perm.symm i))) = a ↔
      a ∈ fixedCharTuples M Fr := by
  set ρ := TwistTag.D4.perm with hρdef
  have hchar : ∀ u, rootChar (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))) u =
      Units.map Fr.toMonoidHom (rootChar a (permLattice ρ.symm u)) := by
    intro u
    rw [rootChar_map_tuple Fr (fun i => a (ρ.symm i)) u, rootChar_permLattice a ρ.symm u]
  constructor
  · intro h y
    have h1 : rootChar a (v • permLattice ρ y) =
        rootChar (weylTuple v (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))))
          (v • permLattice ρ y) := by rw [h]
    rw [rootChar_weylTuple, inv_smul_smul, hchar, permLattice_symm_permLattice,
      hv (permLattice ρ y), permLattice_symm_permLattice] at h1
    exact h1
  · intro ha
    funext i
    have e1 : weylTuple v (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))) i =
        Units.map Fr.toMonoidHom (rootChar a (permLattice ρ.symm (v⁻¹ • Pi.single i 1))) := by
      rw [weylTuple, hchar]
    rw [e1]
    have h2 := ha (permLattice ρ.symm (v⁻¹ • Pi.single i 1))
    rw [← h2, ← hv, smul_inv_smul, CTTorus.rootChar_single]

theorem twistedTorus_D4_eq_map [IsAlgClosed L] (Fr : L →+* L)
    (v : WeylGroup TwistTag.D4.tag)
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.D4.perm.symm x) :
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)
        (twistHom TwistTag.D4 L Fr) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom TwistTag.D4.tag L) := by
  have key : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
      canonicalRep (coxeterSystem TwistTag.D4.tag) L v *
          twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag a) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)⁻¹ =
            rootDiagUnit TwistTag.D4.tag a ↔
        a ∈ fixedCharTuples M Fr := fun a => by
    rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit,
      (rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)).eq_iff]
    exact twisted_weylTuple_eq_iff_D4 Fr v M hv a
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hx).1
    exact ⟨a, (key a).1 (mem_twistedTorusOf.1 hx).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup a, (key a).2 ha⟩

theorem twistedTorus_D4_eq_map_of_weylImage [IsAlgClosed L] (Fr : L →+* L)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (v : WeylGroup TwistTag.D4.tag) (hv0 : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = v)
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.D4.perm.symm x) :
    twistedTorusOf n (twistHom TwistTag.D4 L Fr) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom TwistTag.D4.tag L) := by
  rw [twistedTorusOf_eq_of_weylImage hn v hv0 _ fun b =>
    ⟨_, twistHom_rootDiagUnit_eq (t := TwistTag.D4) (σ := Fr) b⟩]
  exact twistedTorus_D4_eq_map Fr v M hv

end Torus

section Embedding

@[expose] def triEmb (K : Type) [Field K] (σ : K ≃+* K) (L : Type) [Field L] [Algebra K L] :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag L :=
  (baseChangeGL (algebraMap K L)).comp (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype

variable {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

theorem triEmb_apply (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triEmb K σ L y = baseChangeGL (algebraMap K L) (y : ModGL TwistTag.D4.tag K) :=
  rfl

theorem triEmb_injective : Function.Injective (triEmb K σ L) :=
  (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)

theorem triEmb_mem_adjointGroup (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triEmb K σ L y ∈ adjointGroup TwistTag.D4.tag L :=
  baseChangeGL_mem_adjointGroup _
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le _ _ _ y.2)).1

theorem triEmb_fixed (Fr : L →+* L)
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L))
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    twistHom TwistTag.D4 L Fr (triEmb K σ L y) = triEmb K σ L y := by
  change twistHom TwistTag.D4 L Fr (baseChangeGL (algebraMap K L) (y : ModGL TwistTag.D4.tag K)) =
    baseChangeGL (algebraMap K L) (y : ModGL TwistTag.D4.tag K)
  rw [twistHom_baseChangeGL (algebraMap K L) hcomm,
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le _ _ _ y.2)).2]

theorem triEmb_range {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    (triEmb K σ L).range =
      adjointGroup TwistTag.D4.tag L ⊓
        (twistHom TwistTag.D4 L Fr).eqLocus (MonoidHom.id _) := by
  obtain ⟨-, hfix, -, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f
    hℓ hf K hK L 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) Fr hFr
  have h1 : (triEmb K σ L).range =
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1]
  refine SetLike.coe_injective ?_
  rw [← hfix]
  ext x
  simp only [pow_one, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf]
  rfl

theorem triEmb_rational {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    ∀ (X : Subgroup (ModGL TwistTag.D4.tag L)) [Finite X], X ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ X, twistHom TwistTag.D4 L Fr x = x) →
      (triEmb K σ L).range.relIndex X ∣ 1 ∧
        ∀ p : ℕ, p.Prime → 3 < p → ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ X →
          IsPGroup p P → P ≤ (triEmb K σ L).range := by
  intro X _ hXC hXF
  have hXr : X ≤ (triEmb K σ L).range := by
    rw [triEmb_range hℓ hf hK hσ Fr hFr]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hXC hx, hXF x hx⟩
  exact ⟨Subgroup.relIndex_eq_one.2 hXr ▸ dvd_rfl, fun p _ _ P hPX _ => hPX.trans hXr⟩

end Embedding

end CFSG.RankThree.PartOne.KGD
