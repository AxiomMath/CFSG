module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenLayer
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] noncomputable def twLangHom
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    (g0 : ModGL τ (AlgebraicClosure K)) :
    Multiplicative (Fin τ.rank → ZMod p) →* ModGL τ (AlgebraicClosure K) where
  toFun t := g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹
  map_one' := by
    change g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ (0 : Fin τ.rank → ZMod p)) *
      g0⁻¹ = 1
    have h0 : TableBExc.E6Three.zetaVec ζ hζ (0 : Fin τ.rank → ZMod p) = 1 := by
      funext i
      simpa [TableBExc.E6Three.zetaVec]
    rw [h0, rootDiagUnit_one]
    group
  map_mul' x y := by
    change g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ (x.toAdd + y.toAdd)) * g0⁻¹ =
      (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ x.toAdd) * g0⁻¹) *
        (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ y.toAdd) * g0⁻¹)
    rw [ExcFrames.zetaVec_add, rootDiagUnit_mul]
    group

theorem units_map_fr_zetaVec_apply
    {τ : Tag} {K : Type} [Field K] {p q : ℕ} [Fact p.Prime] (hpq : p ∣ q + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1) (t : Fin τ.rank → ZMod p)
    (i : Fin τ.rank) :
    Units.map Fr.toMonoidHom (TableBExc.E6Three.zetaVec ζ hζ t i) =
      (TableBExc.E6Three.zetaVec ζ hζ t i)⁻¹ := by
  have hq : (((q : ℤ)) : ZMod p) = -1 := by
    have h1 : (((q : ℤ)) : ZMod p) + 1 = 0 := by
      rw [← Int.cast_one, ← Int.cast_add]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (q + 1 : ℤ) p).2 (by exact_mod_cast hpq)
    exact add_eq_zero_iff_eq_neg.mp h1
  have hmap : ∀ u : (AlgebraicClosure K)ˣ, Units.map Fr.toMonoidHom u = u ^ q := by
    intro u
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hFr (u : AlgebraicClosure K)
  rw [hmap]
  rw [TableBExc.E6Three.zetaVec, ← zpow_natCast (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
    (.ofAdd (t i))) q, TableBExc.E6Three.zmodPowHom_zpow, hq, neg_one_mul,
    ofAdd_neg, map_inv]

theorem canonicalRep_mul_twistHom_zetaVec
    {K : Type} [Field K] {p q : ℕ} [Fact p.Prime] (hpq : p ∣ q + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ i : Fin TwistTag.E6.tag.rank,
      v • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = -Pi.single (TwistTag.E6.perm i) 1)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1) (t : Fin TwistTag.E6.tag.rank → ZMod p) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t)) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) := by
  have hρ2 : ∀ i : Fin TwistTag.E6.tag.rank,
      TwistTag.E6.perm.symm (TwistTag.E6.perm.symm i) = i := by decide
  have hvinv : ∀ i : Fin TwistTag.E6.tag.rank,
      v⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        -Pi.single (TwistTag.E6.perm.symm i) 1 := by
    intro i
    have h1 := hv (TwistTag.E6.perm.symm i)
    rw [Equiv.apply_symm_apply] at h1
    have h2 := congrArg (fun u => v⁻¹ • u) h1
    simp only [inv_smul_smul, smul_neg] at h2
    rw [h2, neg_neg]
  rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit]
  congr 1
  funext i
  simp only [weylTuple]
  rw [hvinv i, ← neg_one_smul ℤ (Pi.single (TwistTag.E6.perm.symm i) 1 :
    Fin TwistTag.E6.tag.rank → ℤ), rootChar_zsmul, rootChar_single, zpow_neg_one]
  simp only [hρ2]
  rw [units_map_fr_zetaVec_apply hpq hFr hζ t i, inv_inv]

theorem twistHom_twLangHom
    {K : Type} [Field K] {p q : ℕ} [Fact p.Prime] (hpq : p ∣ q + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ i : Fin TwistTag.E6.tag.rank,
      v • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = -Pi.single (TwistTag.E6.perm i) 1)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1) (t : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p)) :
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr (twLangHom hζ g0 t) = twLangHom hζ g0 t := by
  have h := canonicalRep_mul_twistHom_zetaVec hpq hFr hv hζ t.toAdd
  change twistHom TwistTag.E6 (AlgebraicClosure K) Fr
    (g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹) =
    g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹
  rw [map_mul, map_mul, map_inv, hg0]
  calc _ = g0 * (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t.toAdd)) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹) * g0⁻¹ := by
        group
    _ = _ := by rw [h]

theorem exists_phiTwoTorus_twE6
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ i : Fin TwistTag.E6.tag.rank,
      v • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = -Pi.single (TwistTag.E6.perm i) 1)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {p : ℕ} [Fact p.Prime] (hpq : p ∣ 2 ^ n + 1)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    ∃ T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ↥(RecipeExcLang.twInndiagGroup K σ),
      Function.Injective T ∧
      (∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t) : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) =
          g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹) := by
  classical
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let φ := twLangHom (τ := TwistTag.E6.tag) hζ g0
  have hfix : ∀ t, twistHom TwistTag.E6 (AlgebraicClosure K) Fr (φ t) = φ t := fun t =>
    twistHom_twLangHom hpq hFr hv hg0 hζ t
  have hle : ∀ t, φ t ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    intro t
    have ht : φ t = g0 * rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec ζ hζ t.toAdd) * g0⁻¹ := rfl
    rw [ht]
    exact mul_mem (mul_mem hg0C (ExcFrames.rootDiagUnit_mem_adjointGroup _)) (inv_mem hg0C)
  have hrat : ∀ t, φ t ∈ (RecipeExcLang.twInndiagGroup K σ).map (baseChangeGL ι) := by
    intro t
    rw [← CFSG.HardMathSupport.C14ExcBridgeTwE6.twisted_fixed_eq_map hn hK σ hσ Fr hFr]
    exact (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2
      ⟨hle t, hfix t⟩
  let B : ↥(RecipeExcLang.twInndiagGroup K σ) →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (baseChangeGL ι).comp (RecipeExcLang.twInndiagGroup K σ).subtype
  have hBinj : Function.Injective B := by
    intro a b hab
    refine Subtype.ext (baseChangeGL_injective (f := ι) ?_)
    simpa [B] using hab
  have hBrange : B.range = (RecipeExcLang.twInndiagGroup K σ).map (baseChangeGL ι) := by
    show ((baseChangeGL ι).comp (RecipeExcLang.twInndiagGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hrangeB : ∀ t, φ t ∈ B.range := fun t => by rw [hBrange]; exact hrat t
  let e : ↥(RecipeExcLang.twInndiagGroup K σ) ≃* B.range := MonoidHom.ofInjective hBinj
  let T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ↥(RecipeExcLang.twInndiagGroup K σ) :=
    e.symm.toMonoidHom.comp (φ.codRestrict B.range fun t => hrangeB t)
  have hTval : ∀ t : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p),
      baseChangeGL ι ((T t : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) = φ t := by
    intro t
    change B (T t) = φ t
    exact MonoidHom.apply_ofInjective_symm hBinj
      ((φ.codRestrict B.range fun t => hrangeB t) t)
  refine ⟨T, ?_, fun t => ?_⟩
  · intro a b hab
    have hφ : φ a = φ b := by rw [← hTval a, ← hTval b, hab]
    have hd : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) := by
      have h := congrArg (fun x : ModGL TwistTag.E6.tag (AlgebraicClosure K) => g0⁻¹ * x * g0) hφ
      have ha : φ a = g0 * rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) * g0⁻¹ := rfl
      have hb : φ b = g0 * rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) * g0⁻¹ := rfl
      rw [ha, hb] at h
      calc
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) =
            g0⁻¹ * (g0 * rootDiagUnit TwistTag.E6.tag
              (TableBExc.E6Three.zetaVec ζ hζ a.toAdd) * g0⁻¹) * g0 := by group
        _ = g0⁻¹ * (g0 * rootDiagUnit TwistTag.E6.tag
              (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) * g0⁻¹) * g0 := h
        _ = rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ b.toAdd) := by group
    have hz : TableBExc.E6Three.zetaVec ζ hζ a.toAdd = TableBExc.E6Three.zetaVec ζ hζ b.toAdd :=
      CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' hd
    exact Multiplicative.ext (TableBExc.E6Three.zetaVec_injective hζo hζ hz)
  · rw [hTval]
    rfl

end CFSG.StandardType.PhiTwoRootGen

end
