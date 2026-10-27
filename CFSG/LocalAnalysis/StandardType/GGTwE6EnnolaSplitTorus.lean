module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.HardMathSupport.Malle.E27Lie.ExcCross

theorem units_hom_eq_one_of_pow {Ω H : Type*} [Field Ω] [IsAlgClosed Ω] [Group H] (f : Ωˣ →* H)
    {N : ℕ} (hN : 0 < N) (hf : ∀ c, f c ^ N = 1) (c : Ωˣ) : f c = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : Ω) hN
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact c.ne_zero hz.symm
  have hc : c = Units.mk0 z hz0 ^ N :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])
  rw [hc, map_pow, hf]


theorem IsLongest.smul_eq_neg {v : WeylGroup TwistTag.E6.tag} (hv : IsLongest v)
    (α : Fin TwistTag.E6.tag.rank → ℤ) :
    v • α = -permLattice TwistTag.E6.perm α ∧ v⁻¹ • α = -permLattice TwistTag.E6.perm α := by
  have h0 : ReversesSigns ((coxeterSystem TwistTag.E6.tag).wordProd e6W0Word) :=
    reversesSigns_of_negPerm e6W0_smul
  have hr : ReversesSigns v := reversesSigns_of_forall_length_le hv
  rw [hr.inv.eq h0, hr.eq h0, e6W0_smul]
  exact ⟨rfl, rfl⟩

theorem canonicalRep_twistHom_rootDiagUnit {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {v : WeylGroup TwistTag.E6.tag} (hv : IsLongest v)
    (a : Fin TwistTag.E6.tag.rank → Lˣ) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ =
      (rootDiagUnit TwistTag.E6.tag a ^ q)⁻¹ := by
  rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit]
  change _ = (rootDiagUnitHom TwistTag.E6.tag L a ^ q)⁻¹
  rw [← map_pow, ← map_inv]
  change rootDiagUnit _ _ = rootDiagUnit _ _
  congr 1
  funext i
  rw [weylTuple, (hv.smul_eq_neg _).2, permLattice_single, rootChar_neg6,
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single]
  simp only [Equiv.symm_apply_apply, Pi.inv_apply, Pi.pow_apply]
  congr 1
  ext
  simp [hFr]

theorem cochar_eq_one_of_isLongest {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hq : 0 < q) (hFr : ∀ c, Fr c = c ^ q) {v : WeylGroup TwistTag.E6.tag} (hv : IsLongest v)
    (ν : Lˣ →* ModGL TwistTag.E6.tag L) (hT : ∀ c, ν c ∈ torusGroup TwistTag.E6.tag L)
    (hF : ∀ c, ν (c ^ q) = canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
      twistHom TwistTag.E6 L Fr (ν c) * (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) :
    ν = 1 := by
  refine MonoidHom.ext fun c => units_hom_eq_one_of_pow ν (Nat.mul_pos two_pos hq) (fun c => ?_) c
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hT c)
  have h := hF c
  rw [map_pow, ha, canonicalRep_twistHom_rootDiagUnit hFr hv] at h
  rw [ha, mul_comm, pow_mul, sq]
  exact mul_eq_one_iff_eq_inv.2 h

theorem twistHom_eq_of_mem_twistedE6InndiagGL {K : Type} [Field K] (σ : K ≃+* K)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ twistedE6InndiagGL K σ) :
    twistHom TwistTag.E6 K σ.toRingHom g = g := by
  have hle : twistedE6InndiagGL K σ ≤
      (twistHom TwistTag.E6 K σ.toRingHom).eqLocus (MonoidHom.id _) := by
    refine sup_le (fun x hx => ?_) ?_
    · exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
        (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hx)).2
    · rintro _ ⟨u, rfl⟩
      change twistHom TwistTag.E6 K σ.toRingHom
          (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) =
        rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)
      exact twistHom_rootDiagUnit fun i => compatDiag_perm u i
  exact hle hg

theorem baseChangeGL_mem_adjointGroup_twistHom_eq {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ}
    (hσ : ∀ c, σ c = c ^ q) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ q) {g : ModGL TwistTag.E6.tag K} (hg : g ∈ twistedE6InndiagGL K σ) :
    baseChangeGL (algebraMap K (AlgebraicClosure K)) g ∈
        adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) g) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) g := by
  refine ⟨map_twistedE6InndiagGL_le σ _ (fun c => ?_) ⟨g, hg, rfl⟩, ?_⟩
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure K) (c : K)) (n := 3) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact (map_ne_zero _).2 c.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  · have hcomp : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
        Fr.comp (algebraMap K (AlgebraicClosure K)) :=
      RingHom.ext fun c => by simp [hσ, hFr]
    rw [twistHom_baseChangeGL (t := TwistTag.E6) _ hcomp g,
      twistHom_eq_of_mem_twistedE6InndiagGL σ hg]

end CFSG.StandardType.TwE6RootKill

end
