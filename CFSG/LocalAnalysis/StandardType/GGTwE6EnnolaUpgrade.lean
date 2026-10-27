module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6LeviLang
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

theorem root_add_single_check : ∀ r ∈ TwistTag.E6.tag.artifactRoots,
    ∀ k : Fin TwistTag.E6.tag.rank,
      (∀ l : Fin TwistTag.E6.tag.rank, r.getD l 0 + (if l = k then 1 else 0) = 0) ∨
        ∃ j : Fin TwistTag.E6.tag.rank,
          (∑ l, TwistTag.E6.tag.cartan j l * (r.getD l 0 + if l = k then 1 else 0)) ∣ 4 := by
  decide +kernel

section Norm


theorem add_eq_zero_of_forall_dvd_iform {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ} (h₁ : IsRoot TwistTag.E6.tag β₁)
    (h₂ : IsRoot TwistTag.E6.tag β₂) (h : ∀ x, (p : ℤ) ∣ iform x (β₁ + β₂)) : β₁ + β₂ = 0 := by
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 h₂
  have e : β₁ + w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      w • (w⁻¹ • β₁ + (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) := by
    rw [smul_add, smul_inv_smul]
  have h' : ∀ x, (p : ℤ) ∣
      iform x (w⁻¹ • β₁ + (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) := fun x => by
    have hx := h (w • x)
    rwa [e, iform_smul] at hx
  have hget : ∀ l : Fin TwistTag.E6.tag.rank,
      (List.ofFn (w⁻¹ • β₁)).getD l 0 = (w⁻¹ • β₁) l := fun l => by
    simp [List.getD_eq_getElem?_getD]
  rcases root_add_single_check _ (isRoot_iff_mem_artifactRoots.1 (IsRoot.smul h₁ w⁻¹)) k with
    h0 | ⟨j, hj⟩
  · have h00 : w⁻¹ • β₁ + (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) = 0 := funext fun l => by
      simpa [hget, Pi.single_apply] using h0 l
    rw [e, h00, smul_zero]
  · exfalso
    have h4 : (p : ℤ) ∣ 4 := (h' (Pi.single j 1)).trans (by
      rw [iform_single_left, show TwistTag.E6.tag.symmetrizer = 1 from rfl, Matrix.one_apply_eq,
        one_mul]
      simpa [hget, Pi.single_apply] using hj)
    have h4' : p ∣ 2 ^ 2 := by exact_mod_cast h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4'))

theorem smul_permLattice_eq_neg_of_conj {L : Type} [Field L] {Fr : L →+* L} {q p : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) {ζ : Lˣ}
    (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (v : WeylGroup TwistTag.E6.tag)
    (h : rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ)) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) :
    v • permLattice TwistTag.E6.perm γ = -γ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [twistHom_rootDiagUnit_eq, rootDiagUnit_eq_conj_canonicalRep_iff] at h
  have hFζ : Units.map Fr.toMonoidHom ζ = ζ ^ q :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  have hq1 : ζ ^ ((q : ℤ) + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpq
    have e : (q : ℤ) + 1 = ((p * c : ℕ) : ℤ) := by exact_mod_cast hc
    rw [e, zpow_natCast, pow_mul, hζ, one_pow]
  have e : (fun i => Units.map Fr.toMonoidHom (corootTuple γ ζ (TwistTag.E6.perm.symm i))) =
      fun i => corootTuple γ (ζ ^ q) (TwistTag.E6.perm.symm i) := funext fun i => by
    show Units.map Fr.toMonoidHom (ζ ^ _) = (ζ ^ q) ^ _
    rw [map_zpow, hFζ]
  have hdvd : ∀ x, (p : ℤ) ∣ iform x (v⁻¹ • γ + permLattice TwistTag.E6.perm γ) := fun x => by
    rw [← orderOf_eq_prime hζ hζ1, orderOf_dvd_iff_zpow_eq_one]
    have hx := h x
    rw [e, ← rootChar_permLattice (corootTuple γ (ζ ^ q)) TwistTag.E6.perm.symm x,
      CFSG.StandardType.TwE6RootKill.rootChar_corootTuple,
      CFSG.StandardType.TwE6RootKill.rootChar_corootTuple] at hx
    have e1 : iform (v • x) γ = iform x (v⁻¹ • γ) := by
      rw [← iform_smul v⁻¹ (v • x) γ, inv_smul_smul]
    have e2 : iform (permLattice TwistTag.E6.perm.symm x) γ =
        iform x (permLattice TwistTag.E6.perm γ) := by
      have e3 := permLattice_symm_permLattice TwistTag.E6.perm.symm x
      rw [Equiv.symm_symm] at e3
      rw [← iform_permLattice_E6 (permLattice TwistTag.E6.perm.symm x) γ, e3]
    rw [e1, e2, ← zpow_natCast, ← zpow_mul] at hx
    rw [iform_add_right, zpow_add, hx, ← zpow_add, ← add_one_mul, zpow_mul, hq1, one_zpow]
  have h0 := add_eq_zero_of_forall_dvd_iform hp hp2 (IsRoot.smul hγ v⁻¹)
    (hγ.permLattice TwistTag.E6.cartan_perm) hdvd
  rw [eq_neg_of_add_eq_zero_right h0, smul_neg, smul_inv_smul]

end Norm

section Upgrade


theorem twE6EnnolaUpgrade_holds : TwE6EnnolaUpgrade := by
  intro K _ _ σ q hK hσ h2 p hp hpq Fr hFr v g0 hg0C hg0 t ht γ hγ ζ hζ hζ1 hcor
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := ringChar.of_eq h2
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hdvd : q ∣ 2 ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0] at h1
      norm_num at h1
    · exact h0
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).1 hpq
    exact absurd (Nat.le_of_dvd one_pos h1) (by norm_num)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr' : Fr = iterateFrobenius (AlgebraicClosure K) 2 f :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def]
  have hfix := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
    (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hf hK σ hσ Fr hFr
      (Subgroup.mem_map_of_mem _ ht))).2
  have hvγ := smul_permLattice_eq_neg_of_conj hFr hp hp2 hpq hγ hζ hζ1 v (by
    rw [← hcor, map_mul, map_mul, map_inv, hg0, hfix]
    group)
  have hu : (v * e6HRReflProd⁻¹) • γ = γ := by
    have h1 : e6HRReflProd⁻¹ • γ = -permLattice TwistTag.E6.perm γ := by
      rw [inv_smul_eq_iff, smul_neg, w0_smul_permLattice, neg_neg]
    rw [mul_smul, h1, smul_neg, hvγ, neg_neg]
  have hnu := canonicalRep_closure_mem_familyGroup (L := AlgebraicClosure K)
    (fun _ : Unit => corootTuple γ ζ) (mem_closure_rootReflection_of_smul_eq hγ ζ hu)
  obtain ⟨k, hk, hkm⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K)
    (v * e6HRReflProd⁻¹) e6HRReflProd
  rw [inv_mul_cancel_right] at hkm
  have hc : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) e6HRReflProd)⁻¹ ∈
        familyGroup (K := AlgebraicClosure K) (fun _ : Unit => corootTuple γ ζ) := by
    rw [eq_inv_mul_of_mul_eq hkm.symm, mul_assoc, mul_inv_cancel_right]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) hnu
  obtain ⟨z, hz, hzc⟩ := exists_twFrob_w0_eq_mul (L := AlgebraicClosure K) (ℓ := 2) hf
    (fun _ : Unit => corootTuple γ ζ) _ hc
  rw [← hFr', twFrob_apply] at hzc
  have hzC := mem_familyCentralizer.1 (familyGroup_le_familyCentralizer _ hz)
  refine ⟨e6HRReflProd, w0_smul_permLattice, g0 * z⁻¹, mul_mem hg0C (inv_mem hzC.1), ?_, ?_⟩
  · rw [map_mul, map_inv, hg0, eq_inv_mul_of_mul_eq (mul_inv_eq_iff_eq_mul.1 hzc)]
    group
  · have hzd : rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) * z =
        z * rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) :=
      mul_inv_eq_iff_eq_mul.1 (hzC.2 ())
    rw [show (g0 * z⁻¹)⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * (g0 * z⁻¹) =
      z * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0) * z⁻¹ by group,
      hcor, ← hzd, mul_inv_cancel_right]

end Upgrade

end CFSG.StandardType.TwE6RootAs

end
