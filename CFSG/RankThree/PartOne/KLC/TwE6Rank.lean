module

public import CFSG.RankThree.PartOne.KLC.TwistedTorusRank
public import CFSG.RankThree.PartOne.KE.CTTwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)

open scoped Matrix

section Eigen

variable {L : Type} [Field L]

theorem eigTuple_mem_fixedCharTuples {τ : Tag} {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {p : ℕ} {ξ₁ ξ₂ : Lˣ} (h₁ : ξ₁ ^ p = 1) (h₂ : ξ₂ ^ p = 1)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (U : Fin 2 → Fin τ.rank → ℤ)
    (hfix : ∀ (s : Fin 2) (k : Fin τ.rank), (∑ l, U s l * M l k) ≡ (q : ℤ) * U s k [ZMOD p]) :
    eigTuple ξ₁ ξ₂ U ∈ fixedCharTuples M Fr := by
  classical
  rw [mem_fixedCharTuples_iff]
  intro u
  rw [rootChar_eigTuple, rootChar_eigTuple]
  have key : ∀ s : Fin 2, (∑ i, U s i * (M *ᵥ u) i) ≡ (q : ℤ) * ∑ i, U s i * u i [ZMOD p] := by
    intro s
    have e1 : ∑ i, U s i * (M *ᵥ u) i = ∑ k, (∑ i, U s i * M i k) * u k := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e1, Finset.mul_sum, ← ZMod.intCast_eq_intCast_iff]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := (ZMod.intCast_eq_intCast_iff _ _ p).2 (hfix s k)
    push_cast at h
    rw [h]
    ring
  have hFru : ∀ c : Lˣ, Units.map Fr.toMonoidHom c = c ^ q := fun c =>
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  rw [map_mul, hFru, hFru, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  · refine zpow_eq_zpow_of_modEq' h₁ ?_
    rw [mul_comm]
    exact key 0
  · refine zpow_eq_zpow_of_modEq' h₂ ?_
    rw [mul_comm]
    exact key 1

end Eigen

section Hom

variable {L : Type} [Field L]

theorem smul_apply_eq_sum {τ : Tag} (v : WeylGroup τ) (Wm : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hW : ∀ k l : Fin τ.rank, (v • (Pi.single k 1 : Fin τ.rank → ℤ)) l = Wm l k)
    (x : Fin τ.rank → ℤ) (i : Fin τ.rank) : (v • x) i = ∑ k, Wm i k * x k := by
  have hv : x = ∑ k, x k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : v • x = ∑ k, x k • (v • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm v (x k) _
  rw [hw, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, hW k i, smul_eq_mul, mul_comm]

variable [IsAlgClosed L]

theorem exists_hom_twistedE6_of_eigen {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ}
    (hp : p.Prime) (hpL : (p : L) ≠ 0) (v : WeylGroup TwistTag.E6.tag)
    (Wm : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hW : ∀ k l : Fin TwistTag.E6.tag.rank,
      (v • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = Wm l k)
    (U : Fin 2 → Fin TwistTag.E6.tag.rank → ℤ) (i j : Fin TwistTag.E6.tag.rank)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin TwistTag.E6.tag.rank),
      (∑ l, U s l * Wm l (TwistTag.E6.perm k)) ≡ (q : ℤ) * U s k [ZMOD p]) :
    ∃ φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL TwistTag.E6.tag L,
      Function.Injective φ ∧
      φ.range ≤ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
        (twistHom TwistTag.E6 L Fr) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  set M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    Matrix.of fun i k => Wm i (TwistTag.E6.perm k) with hM
  have hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x := by
    intro x
    funext i
    rw [smul_apply_eq_sum v Wm hW x i]
    change _ = ∑ k, Wm i (TwistTag.E6.perm k) * x (TwistTag.E6.perm.symm k)
    simp only [e6_perm_symm_apply]
    exact (Equiv.sum_comp TwistTag.E6.perm fun k => Wm i k * x k).symm
  have hT := twistedTorus_E6_eq_map Fr v M hv
  let ψ : (rootsOfUnity p L) × (rootsOfUnity p L) →* (Fin TwistTag.E6.tag.rank → Lˣ) :=
    { toFun := fun z => eigTuple (z.1 : Lˣ) (z.2 : Lˣ) U
      map_one' := by
        funext l
        simp [eigTuple]
      map_mul' := fun z z' => by
        simpa using eigTuple_mul (z.1 : Lˣ) (z.2 : Lˣ) (z'.1 : Lˣ) (z'.2 : Lˣ) U }
  let φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL TwistTag.E6.tag L :=
    (rootDiagUnitHom TwistTag.E6.tag L).comp ψ
  have hφ : ∀ z, φ z = rootDiagUnit TwistTag.E6.tag (eigTuple (z.1 : Lˣ) (z.2 : Lˣ) U) :=
    fun z => rfl
  have hroot : ∀ z : (rootsOfUnity p L) × (rootsOfUnity p L),
      (z.1 : Lˣ) ^ p = 1 ∧ (z.2 : Lˣ) ^ p = 1 :=
    fun z => ⟨(mem_rootsOfUnity p _).1 z.1.2, (mem_rootsOfUnity p _).1 z.2.2⟩
  refine ⟨φ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro z hz
    rw [hφ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have hA : (z.1 : Lˣ) ^ U 0 i * (z.2 : Lˣ) ^ U 1 i = 1 := congrFun hb i
    have hB : (z.1 : Lˣ) ^ U 0 j * (z.2 : Lˣ) ^ U 1 j = 1 := congrFun hb j
    obtain ⟨hm1, hm2'⟩ := hroot z
    have h1 := zpow_minor_eq_one' hA hB
    have h2 := zpow_minor_eq_one' (x := (z.2 : Lˣ)) (y := (z.1 : Lˣ)) (by rwa [mul_comm] at hA)
      (by rwa [mul_comm] at hB)
    have h2' : (z.2 : Lˣ) ^ (U 0 i * U 1 j - U 0 j * U 1 i) = 1 := by
      have : U 1 i * U 0 j - U 1 j * U 0 i = -(U 0 i * U 1 j - U 0 j * U 1 i) := by ring
      rw [this, zpow_neg, inv_eq_one] at h2
      exact h2
    have e1 := zpow_eq_one_of_coprime' hm1 h1 hdet
    have e2 := zpow_eq_one_of_coprime' hm2' h2' hdet
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · rintro _ ⟨z, rfl⟩
    rw [hT]
    obtain ⟨hm1, hm2'⟩ := hroot z
    exact ⟨_, eigTuple_mem_fixedCharTuples hFr hm1 hm2' M U fun s k => by
      simpa [hM] using hfix s k, rfl⟩

end Hom

section PRank


theorem two_le_pRank_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (v : WeylGroup TwistTag.E6.tag)
    (Wm : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hW : ∀ k l : Fin TwistTag.E6.tag.rank,
      (v • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = Wm l k)
    (U : Fin 2 → Fin TwistTag.E6.tag.rank → ℤ) (i j : Fin TwistTag.E6.tag.rank)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin TwistTag.E6.tag.rank),
      (∑ l, U s l * Wm l (TwistTag.E6.perm k)) ≡ ((ℓ ^ f : ℕ) : ℤ) * U s k [ZMOD p]) :
    2 ≤ CFSG.pRank p (twistedE6RootGroup K σ) := by
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
  have : Finite (twistedE6RootGroup K σ) := Subtype.finite
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hpL : (p : L) ≠ 0 := fun h0 => hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1
    ((CharP.cast_eq_zero_iff L ℓ p).1 h0)).symm
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
  have hrat : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
        ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hP
    have hXR : X ≤ R := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    have : Finite P :=
      Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
    exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp Nat.prime_three (by omega) hk hP
  obtain ⟨φ, hφinj, hφT⟩ := exists_hom_twistedE6_of_eigen hFr hp hpL v Wm hW U i j hdet hfix
  have hcard : Nat.card ((rootsOfUnity p L) × (rootsOfUnity p L)) = p ^ 2 := by
    rw [Nat.card_prod, card_rootsOfUnity_eq hp hpL, sq]
  have hpow : ∀ a : (rootsOfUnity p L) × (rootsOfUnity p L), a ^ p = 1 := fun a =>
    Prod.ext (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 a.1.2))
      (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 a.2.2))
  exact le_pRank_of_twistedTorus ι hι (twistHom TwistTag.E6 L Fr)
    (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) g0 hg0C hg0 hp hrat
    (fun a b => mul_comm a b) hpow hcard φ hφinj hφT

end PRank

end CFSG.RankThree.PartOne.KLC
