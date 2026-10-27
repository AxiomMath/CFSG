module

public import CFSG.RankThree.PartOne.KE.CTColumns
public import CFSG.RankThree.PartOne.KE.CTRational
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (charVal)
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)
open scoped Matrix Polynomial

section Fixed

variable {L : Type} [Field L]

theorem e6_perm_symm_apply (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm.symm i = TwistTag.E6.perm i := by
  revert i
  decide

theorem e6_perm_symm_symm_apply (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm.symm (TwistTag.E6.perm.symm i) = i := by
  revert i
  decide

theorem twisted_weylTuple_eq_iff (Fr : L →+* L) (v : WeylGroup TwistTag.E6.tag)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    (a : Fin TwistTag.E6.tag.rank → Lˣ) :
    weylTuple v (fun i => Units.map Fr.toMonoidHom (a (TwistTag.E6.perm.symm i))) = a ↔
      a ∈ fixedCharTuples M Fr := by
  set ρ := TwistTag.E6.perm with hρdef
  have hρ2 : ∀ y : Fin TwistTag.E6.tag.rank → ℤ, permLattice ρ (permLattice ρ y) = y := by
    intro y
    funext i
    change y (ρ.symm (ρ.symm i)) = y i
    rw [e6_perm_symm_symm_apply]
  have hρ3 : ∀ y : Fin TwistTag.E6.tag.rank → ℤ, permLattice ρ.symm y = permLattice ρ y := by
    intro y
    funext i
    change y (ρ.symm.symm i) = y (ρ.symm i)
    rw [Equiv.symm_symm, e6_perm_symm_apply]
  have hchar : ∀ u, rootChar (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))) u =
      Units.map Fr.toMonoidHom (rootChar a (permLattice ρ u)) := by
    intro u
    rw [rootChar_map_tuple Fr (fun i => a (ρ.symm i)) u, ← hρ3, rootChar_permLattice a ρ.symm u]
  constructor
  · intro h y
    have h1 : rootChar a (v • permLattice ρ y) =
        rootChar (weylTuple v (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))))
          (v • permLattice ρ y) := by rw [h]
    rw [rootChar_weylTuple, inv_smul_smul, hchar, hρ2, hv (permLattice ρ y), hρ2] at h1
    exact h1
  · intro ha
    funext i
    have e1 : weylTuple v (fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))) i =
        Units.map Fr.toMonoidHom (rootChar a (permLattice ρ (v⁻¹ • Pi.single i 1))) := by
      rw [weylTuple, hchar]
    rw [e1]
    have h2 := ha (permLattice ρ (v⁻¹ • Pi.single i 1))
    rw [← h2, ← hv, smul_inv_smul, CTTorus.rootChar_single]

theorem twistedTorus_E6_eq_map [IsAlgClosed L] (Fr : L →+* L) (v : WeylGroup TwistTag.E6.tag)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) :
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
        (twistHom TwistTag.E6 L Fr) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom TwistTag.E6.tag L) := by
  have key : ∀ a : Fin TwistTag.E6.tag.rank → Lˣ,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
          twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ = rootDiagUnit TwistTag.E6.tag a ↔
        a ∈ fixedCharTuples M Fr := fun a => by
    rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit,
      (rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L)).eq_iff]
    exact twisted_weylTuple_eq_iff Fr v M hv a
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hx).1
    exact ⟨a, (key a).1 (mem_twistedTorusOf.1 hx).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup a, (key a).2 ha⟩

end Fixed

theorem cyclic_sylow_twisted_E6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    (b : Fin TwistTag.E6.tag.rank → ℤ)
    (hlin : LinearIndependent ℤ fun j : Fin TwistTag.E6.tag.rank => (M ^ (j : ℕ)) *ᵥ b)
    (hspan : Submodule.span ℤ
      (Set.range fun j : Fin TwistTag.E6.tag.rank => (M ^ (j : ℕ)) *ᵥ b) = ⊤)
    (hdet : M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1)
    (hne : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0)
    (hreg : ∀ z : Fin TwistTag.E6.tag.rank → ZMod p, z ≠ 0 →
      ((M.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z = ((ℓ ^ f : ℕ) : ZMod p) • z →
      ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → charVal z α ≠ 0)
    (hord : p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p =
      p ^ (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs.factorization p) :
    ∃ k : ℕ, CyclicSylowConclusion' (twistedE6RootGroup K σ) p
      (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs (3 ^ k) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, hRcard, hpp⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hyΓ : ∀ y : twistedE6RootGroup K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    fun y => graphFixedRootGroup_le _ _ _ y.2
  have hιC : ∀ y, ι y ∈ adjointGroup TwistTag.E6.tag L := fun y =>
    baseChangeGL_mem_adjointGroup _ ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ y)).1
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      change algebraMap K L (σ c) = Fr (algebraMap K L c)
      rw [hσ, hFr, map_pow]
  have hιΦ : ∀ y, twistHom TwistTag.E6 L Fr (ι y) = ι y := fun y => by
    change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L) (y : ModGL _ K)) =
      baseChangeGL (algebraMap K L) (y : ModGL _ K)
    rw [twistHom_baseChangeGL (algebraMap K L) hcomm,
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ y)).2]
  have hrat : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ι.range.relIndex X ∣ 3 ^ k ∧
        ∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
          IsPGroup p' P → P ≤ ι.range := by
    intro X _ hXC hXF
    have hXR : X ≤ R := fun x hx => (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    refine ⟨relIndex_dvd_of_le_of_index_dvd hXR (hk ▸ dvd_rfl), fun p' hp' hp'3 P hPX hP => ?_⟩
    have : Finite P :=
      Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
    exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp' Nat.prime_three (by omega) hk hP
  have hcent : ∀ (M' : Type) [Field M'] [Finite M'], p ∣ Nat.card M'ˣ →
      ∀ {x : ModGL TwistTag.E6.tag M'}, x ∈ torusGroup TwistTag.E6.tag M' → orderOf x = p →
      (∀ a : Fin TwistTag.E6.tag.rank → M'ˣ, x = rootDiagUnit TwistTag.E6.tag a →
        ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → rootChar a α ≠ 1) →
      adjointGroup TwistTag.E6.tag M' ⊓ Subgroup.centralizer {x} =
        torusGroup TwistTag.E6.tag M' :=
    fun M' _ _ hpM x hxH hxp hreg' =>
      E_regular_large_prime_toral_centralizer TwistTag.E6.tag (Or.inl rfl) M' hp hp7 hpM hxH hxp
        hreg'
  have hcentL : ∀ x ∈ torusGroup TwistTag.E6.tag L, orderOf x = p →
      (∀ a : Fin TwistTag.E6.tag.rank → Lˣ, x = rootDiagUnit TwistTag.E6.tag a →
        ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → rootChar a α ≠ 1) →
      ∀ y ∈ adjointGroup TwistTag.E6.tag L, y * x = x * y → y ∈ torusGroup TwistTag.E6.tag L :=
    fun x hxH hxp hreg' y hy hcomm' => by
      have : Algebra.IsAlgebraic K L := inferInstance
      exact torus_of_commuting_regular K hp hcent hxH hxp hreg' hy hcomm'
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v M hv
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.E6.tag L) := rootDiagUnit_injective
  obtain ⟨hcycT, hcardT⟩ := isCyclic_and_card_fixedCharTuples M b hlin hspan Fr (q := ℓ ^ f) hFr
    (ℓ := ℓ) hℓ (dvd_pow_self ℓ (by omega)) hdet hne
  have hcyc : IsCyclic (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) := by
    rw [hT0]
    exact (Subgroup.equivMapOfInjective (fixedCharTuples M Fr) (rootDiagUnitHom _ L)
      hinj0).isCyclic.1 hcycT
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective hinj0]
    exact hcardT
  have hregT : ∀ x ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr), orderOf x = p →
      ∀ a : Fin TwistTag.E6.tag.rank → Lˣ, x = rootDiagUnit TwistTag.E6.tag a →
        ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → rootChar a α ≠ 1 := by
    intro x hx hxp a hxa α hα
    rw [hT0] at hx
    obtain ⟨a', ha', rfl⟩ := hx
    have hxa' : rootDiagUnit TwistTag.E6.tag a' = rootDiagUnit TwistTag.E6.tag a := hxa
    have haa : a' = a := rootDiagUnit_injective hxa'
    rw [← haa]
    have hxp' : orderOf (rootDiagUnit TwistTag.E6.tag a') = p := hxp
    exact rootChar_ne_one_of_column_regular M Fr hFr hp ha'
      (pow_eq_one_of_orderOf_rootDiagUnit hxp') (ne_one_of_orderOf_rootDiagUnit hp hxp') hreg hα
  have hordC : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs.factorization p := by
    have h1 := hpp p hp (by omega)
    have h2 : Nat.card C' = Nat.card (twistedE6RootGroup K σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [h2, hRcard] at h1
    rw [h1]
    exact hord
  exact ⟨k, cyclic_sylow_of_twisted_torus (3 ^ k) ι hι hιC (twistHom TwistTag.E6 L Fr) hιΦ
    (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) g0 hg0C hg0 hp (by omega)
    (Int.natAbs_ne_zero.2 hne) hrat hcentL hcyc hcard hregT hordC⟩

end CFSG.RankThree.PartOne.KE
