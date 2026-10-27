module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldThreeFourHolds
public import Certificates.Certificate830101
import CFSG.LocalAnalysis.StandardType.GGTwE6PlaneEnnolaWeyl
import CFSG.LocalAnalysis.StandardType.GGTwE6LeviLang

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TwE6RootKill
  CFSG.StandardType.TwE6RootAs CFSG.RankThree.Chevalley


theorem exists_twLangData_ennola {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAI : A ≤ twistedE6InndiagGL K σ) (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A)
    (hU : TwNormTwo K σ A) :
    ∃ D : TwLangData K σ (2 ^ n) A, D.c = 1 ∧ ∀ γ, D.v • permLattice TwistTag.E6.perm γ = -γ := by
  classical
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h0 => by
    subst h0
    norm_num at h3
  obtain ⟨D, hc⟩ := exists_twLangData_of_twNormTwo' hK hσ h3 hAI hA hcard hU
  haveI : CharP K 2 := charP_two_of_card_sq hK
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : ((2 ^ n : ℕ) : ZMod 3) = -1 := by
    have h0 : ((2 ^ n + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h3
    push_cast at h0 ⊢
    exact eq_neg_of_add_eq_zero_left h0
  haveI : NeZero ((3 : ℕ) : K) := ⟨fun h => by
    have h' := (CharP.cast_eq_zero_iff K 2 3).1 h
    norm_num at h'⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 3
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ 3 :=
    ⟨_, IsPrimitiveRoot.isUnit_unit (by norm_num) hζ0⟩
  have hlog : ∀ x ∈ A, ∃ y : Fin TwistTag.E6.tag.rank → ZMod 3,
      rootDiagUnit TwistTag.E6.tag (fun k => ζ ^ ((y k).val : ℤ)) =
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0 ∧
      ∀ i, ∑ k, ((wkMatrix D.v⁻¹ i k : ℤ) : ZMod 3) * y k = 0 := fun x hx => by
    obtain ⟨y, h1, h2⟩ := exists_wkLog D hq hζ hx (hA.2 x hx)
    refine ⟨y, ?_, h2⟩
    rw [h1, hc, one_mul, inv_one, mul_one]
  choose y hy1 hy2 using hlog
  have hinj : Function.Injective fun x : A => y x.1 x.2 := fun x x' hxx => by
    have h : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x.1 * D.g0 =
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x'.1 * D.g0 := by
      rw [← hy1 x.1 x.2, ← hy1 x'.1 x'.2]
      simp only at hxx
      rw [hxx]
    exact Subtype.ext (baseChangeGL_injective _ (mul_left_cancel (mul_right_cancel h)))
  have hcl := mem_closure_rootReflection_of_wkMatrix (p := 3) (by norm_num)
    (Y := Set.range fun x : A => y x.1 x.2)
    (by rw [Nat.card_range_of_injective hinj]; exact hcard) w0_smul_permLattice D.v (by
      rintro _ ⟨x, rfl⟩ i
      exact hy2 x.1 x.2 i)
  obtain ⟨a, ha⟩ : ∃ a : A → Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      a = fun x k => ζ ^ ((y x.1 x.2 k).val : ℤ) := ⟨_, rfl⟩
  have hd : ∀ x (hx : x ∈ A), rootDiagUnit TwistTag.E6.tag (a ⟨x, hx⟩) =
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0 := fun x hx => by
    rw [ha]
    exact hy1 x hx
  have hS : {β | IsRoot TwistTag.E6.tag β ∧ ∀ y' ∈ Set.range fun x : A => y x.1 x.2,
      ∑ k, y' k * ((β k : ℤ) : ZMod 3) = 0} ⊆ familyKernel a := fun β hβ =>
    ⟨hβ.1, fun x => by
      rw [ha]
      exact (rootChar_val_eq_one_iff_wk hζ _ β).2 (hβ.2 _ ⟨x, rfl⟩)⟩
  have hnu := canonicalRep_closure_mem_familyGroup (L := AlgebraicClosure K) a
    (Subgroup.closure_mono (Set.image_mono hS) hcl)
  obtain ⟨k, hk, hkm⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K)
    (D.v * e6HRReflProd⁻¹) e6HRReflProd
  rw [inv_mul_cancel_right] at hkm
  have hcM : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) e6HRReflProd)⁻¹ ∈
        familyGroup (K := AlgebraicClosure K) a := by
    rw [eq_inv_mul_of_mul_eq hkm.symm, mul_assoc, mul_inv_cancel_right]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) hnu
  have hFr : D.Fr = iterateFrobenius (AlgebraicClosure K) 2 n :=
    RingHom.ext fun c => by rw [D.hFr, iterateFrobenius_def]
  obtain ⟨z, hz, hzc⟩ := exists_twFrob_w0_eq_mul (L := AlgebraicClosure K) (ℓ := 2) hn a _ hcM
  rw [← hFr, twFrob_apply] at hzc
  have hzC := mem_familyCentralizer.1 (familyGroup_le_familyCentralizer _ hz)
  have hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr (D.g0 * z⁻¹) =
      D.g0 * z⁻¹ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
        e6HRReflProd := by
    rw [map_mul, map_inv, D.hg0, eq_inv_mul_of_mul_eq (mul_inv_eq_iff_eq_mul.1 hzc)]
    group
  have hFix : ∀ x' ∈ A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr x' = x' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ D.Fr D.hFr
        (Subgroup.mem_map_of_mem _ (hAI hx)))).2
  have hT : ∀ x' ∈ A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      (D.g0 * z⁻¹)⁻¹ * x' * (D.g0 * z⁻¹) ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rintro _ ⟨x, hx, rfl⟩
    have hzd : rootDiagUnit TwistTag.E6.tag (a ⟨x, hx⟩) * z =
        z * rootDiagUnit TwistTag.E6.tag (a ⟨x, hx⟩) :=
      mul_inv_eq_iff_eq_mul.1 (hzC.2 ⟨x, hx⟩)
    rw [show (D.g0 * z⁻¹)⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x *
        (D.g0 * z⁻¹) = z * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0) *
          z⁻¹ by group, ← hd x hx, ← hzd, mul_inv_cancel_right]
    exact rootDiagUnit_mem_torusGroup _
  refine ⟨⟨e6HRReflProd, D.Fr, D.hFr, D.g0 * z⁻¹, mul_mem D.hg0C (inv_mem hzC.1), hg0, 1,
    one_mem _, fun x hx => ?_⟩, rfl, w0_smul_permLattice⟩
  simp only [one_mul, inv_one, mul_one]
  exact mem_lang_torus_of_datum _ hFix hg0 hT _ (Subgroup.mem_map_of_mem _ hx)

end CFSG.StandardType.TwE6FieldCore

end
