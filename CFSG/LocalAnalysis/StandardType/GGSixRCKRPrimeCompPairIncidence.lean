module

public import CFSG.LocalAnalysis.StandardType.ExcPos.RootPairStabilizer
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly
import CFSG.LocalAnalysis.StandardType.ExcPos.StableOppositePairLang
import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialUnitaryOrbit
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ConnectedJoint
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor
import TauCeti.GroupTheory.FixedSubgroup
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.LieKnownR2.ExcPos CFSG.StandardType.F4ExplicitPos.ConnectedJoint

theorem rckStep_eq_frobTwist
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) :
    ∃ (e : ℕ) (Q : ModGL τ GGL), 1 ≤ e ∧ S.D.step = frobTwistGL τ GGL 2 e Q ∧
      ∀ g ∈ adjointGroup τ GGL, S.D.step g ∈ adjointGroup τ GGL := by
  obtain ⟨hpow, hcast⟩ := S.hqpow
  obtain ⟨ℓ, k, hℓ, hk, hq⟩ := (isPrimePow_nat_iff _).mp hpow
  have h2 : (2 : ℕ) ∣ S.D.q := (CharP.cast_eq_zero_iff GGL 2 S.D.q).mp hcast
  have hℓ2 : ℓ = 2 := by
    rw [← hq] at h2
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  subst hℓ2
  obtain ⟨Q, -, hQA, hQ⟩ := S.exists_step_frobTwist_adjoint (r := 2) (e := k) hq.symm
  refine ⟨k, Q, hk, MonoidHom.ext hQ, fun g hg => ?_⟩
  rw [hQ g, frobTwistGL_apply]
  have h1 := entrywiseFrobGL_mem (τ := τ) (L := GGL) 2 k hg
  have h3 : Q * entrywiseFrobGL τ GGL 2 k g * Q⁻¹ ∈
      (adjointGroup τ GGL).map (MulAut.conj Q).toMonoidHom := ⟨_, h1, rfl⟩
  rwa [hQA] at h3

theorem exists_unit_zpow_disjoint_rootChar {τ : Tag} (a : Fin τ.rank → GGLˣ) :
    ∃ t : GGLˣ, (∀ n : ℕ, 0 < n → n ≤ 4 → t ^ n ≠ 1) ∧
      ∀ (v : Fin τ.rank → ℤ) (n : ℤ), rootChar a v * t ^ n = 1 → t ^ n = 1 := by
  classical
  have hfin : ∀ i, IsOfFinOrder (a i) := fun i =>
    CFSG.RankThree.PartOne.KLCE.isOfFinOrder_of_isAlgebraic (K := ZMod 2) (L := GGL) (a i)
  let m : ℕ := ∏ i, orderOf (a i)
  have hmpos : 0 < m := Finset.prod_pos fun i _ => (hfin i).orderOf_pos
  have hmdvd : ∀ i, orderOf (a i) ∣ m := fun i =>
    Finset.dvd_prod_of_mem (fun i => orderOf (a i)) (Finset.mem_univ i)
  have hm : ∀ i, a i ^ m = 1 := fun i =>
    (orderOf_dvd_iff_pow_eq_one).mp (hmdvd i)
  have hroot : ∀ v : Fin τ.rank → ℤ, rootChar a v ^ m = 1 := by
    intro v
    have hterm : ∀ i, (a i ^ v i) ^ m = 1 := by
      intro i
      rw [← zpow_natCast, ← zpow_mul, mul_comm (v i) (m : ℤ), zpow_mul, zpow_natCast,
        hm i, one_zpow]
    rw [rootChar, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => hterm i
  obtain ⟨r, hrle, hrprime⟩ := Nat.exists_infinite_primes (max 4 m + 1)
  have hr4 : 4 < r := by omega
  have hrm : m < r := by omega
  have hrc : (r : GGL) ≠ 0 := by
    intro h0
    have h2r : 2 ∣ r := (CharP.cast_eq_zero_iff GGL 2 r).mp h0
    have h2eq : r = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hrprime).mp h2r).symm
    omega
  obtain ⟨t, ht⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := GGL) (n := r) hrc
  have htr : t ^ (r : ℤ) = 1 := by
    rw [zpow_natCast, ← ht, pow_orderOf_eq_one]
  refine ⟨t, ?_, ?_⟩
  · intro n hn hn4 htn
    have hdvd : r ∣ n := by
      rw [← ht]
      exact orderOf_dvd_of_pow_eq_one htn
    have := Nat.le_of_dvd hn hdvd
    omega
  · intro v n h
    have hsm : (t ^ n) ^ m = 1 := by
      rw [eq_inv_of_mul_eq_one_right h, inv_pow, hroot v, inv_one]
    have hsr : (t ^ n) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm n (r : ℤ), zpow_mul, htr, one_zpow]
    have hcop : Nat.Coprime r m :=
      (hrprime.coprime_iff_not_dvd).mpr fun hd => by
        have := Nat.le_of_dvd hmpos hd
        omega
    have h1 : orderOf (t ^ n) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hsr)
        (orderOf_dvd_of_pow_eq_one hsm)
    exact orderOf_eq_one_iff.mp h1

theorem exists_inv_mul_frobTwistGL_eq_of_kernelRoots
    {τ : Tag} (b : Fin τ.rank → GGLˣ) {e : ℕ} (he : 1 ≤ e) (Q : ModGL τ GGL)
    (hQ : ∀ g ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom b)),
      frobTwistGL τ GGL 2 e Q g ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom b))) :
    ∀ c ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom b)),
      ∃ x ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom b)),
        x⁻¹ * frobTwistGL τ GGL 2 e Q x = c := by
  have hZ := isConnectedAlgebraicSubgroup_torus_sup_rootSpan_no117
    (τ := τ) (k := GGL) (S := kernelRoots (rootCharHom b))
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction (p := 2) hZ he Q hQ
  exact hlang

theorem rckCompPairIncidence
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    {i : KernelComponent (rootCharHom a)} {γ α : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) (hα : α ∈ componentRoots (rootCharHom a) i)
    {z w : ModGL τ GGL}
    (hz : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (hw : w ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (h₁ : ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom)
    (h₂ : ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom)
    (h₃ : ((rootSubgroup τ GGL α).map (MulAut.conj w).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL α).map (MulAut.conj w).toMonoidHom)
    (h₄ : ((rootSubgroup τ GGL (-α)).map (MulAut.conj w).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL (-α)).map (MulAut.conj w).toMonoidHom) :
    ∃ k ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)), S.D.step k = k ∧
      ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map (MulAut.conj k).toMonoidHom =
        (rootSubgroup τ GGL α).map (MulAut.conj w).toMonoidHom ∧
      ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map
          (MulAut.conj k).toMonoidHom =
        (rootSubgroup τ GGL (-α)).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨e, Q, he, hstep, _⟩ := rckStep_eq_frobTwist S
  rw [hstep] at h₁ h₂ h₃ h₄
  have hFA : ∀ g ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)),
      frobTwistGL τ GGL 2 e Q g ∈
        torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) := by
    intro g hg
    rw [← hstep]
    exact step_mem_toralRootGroup S hT hg
  obtain ⟨y, hy, hyα⟩ :=
    exists_mem_closure_rootReflection_smul_eq_of_mem_componentRoots hτ hγ hα
  let n : ModGL τ GGL := canonicalRep (coxeterSystem τ) GGL y
  have hn : n ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) :=
    canonicalRep_mem_torus_sup_rootSpan_kernelRoots hy
  have hγr : IsRoot τ γ := hγ.1.1
  have hcomp : (MulAut.conj (w * n)).toMonoidHom =
      (MulAut.conj w).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hW : ((rootSubgroup τ GGL γ).map (MulAut.conj (w * n)).toMonoidHom) =
      (rootSubgroup τ GGL α).map (MulAut.conj w).toMonoidHom := by
    rw [hcomp, ← Subgroup.map_map,
      CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := GGL) y hγr, hyα]
  have hW' : ((rootSubgroup τ GGL (-γ)).map (MulAut.conj (w * n)).toMonoidHom) =
      (rootSubgroup τ GGL (-α)).map (MulAut.conj w).toMonoidHom := by
    rw [hcomp, ← Subgroup.map_map,
      CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := GGL) y (IsRoot.neg hγr),
      smul_neg, hyα]
  let Q₁ : ModGL τ GGL := z⁻¹ * Q * entrywiseFrobGL τ GGL 2 e z
  have hF₁ : ∀ x, frobTwistGL τ GGL 2 e Q₁ x =
      z⁻¹ * frobTwistGL τ GGL 2 e Q (z * x * z⁻¹) * z := by
    intro x
    rw [frobTwistGL_apply, frobTwistGL_apply]
    dsimp only [Q₁]
    simp only [map_mul, map_inv]
    group
  obtain ⟨h, hhA, hFh, hV, hV'⟩ :=
    exists_fixed_conj_pair_of_lang (frobTwistGL τ GGL 2 e Q)
      (frobTwistGL τ GGL 2 e Q₁) hFA hz (mul_mem hw hn) rfl rfl hW hW' h₁ h₂ h₃ h₄ hF₁ (by
        intro hstab c hc
        obtain ⟨t, ht, hind⟩ := exists_unit_zpow_disjoint_rootChar a
        let b : Fin τ.rank → GGLˣ :=
          a * CFSG.ClassicalInvolution.ModelFacts.Levi.thetaDiag γ t
        have hb :
            (torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a))) ⊓
                Subgroup.normalizer (rootSubgroup τ GGL γ : Set (ModGL τ GGL)) ⊓
                Subgroup.normalizer (rootSubgroup τ GGL (-γ) : Set (ModGL τ GGL)) =
              torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom b)) :=
          torusGroup_sup_rootSpan_kernelRoots_inf_normalizer_eq hτ a hγr t ht hind
        have hQb : ∀ g ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom b)),
            frobTwistGL τ GGL 2 e Q₁ g ∈
              torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom b)) := by
          intro g hg
          rw [← hb] at hg ⊢
          exact hstab g hg
        obtain ⟨x, hx, hxeq⟩ :=
          exists_inv_mul_frobTwistGL_eq_of_kernelRoots b he Q₁ hQb c
            (by rw [← hb]; exact hc)
        refine ⟨x, ?_, hxeq⟩
        rw [hb]
        exact hx)
  refine ⟨h, hhA, ?_, hV, hV'⟩
  rw [hstep]
  exact hFh

theorem conj_rationalComponent_eq_of_mem_torus_sup_rootSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (h1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) {k : ModGL τ L}
    (hk : k ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hks : S.D.step k = k) :
    (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj k).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hkM : k ∈ S.D.model :=
    S.D.mem_model.2 ⟨torus_sup_rootSpan_le_adjointGroup _ hk, hks⟩
  have hmodel : S.D.model.map (MulAut.conj k).toMonoidHom = S.D.model :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hkM)
  have hΓ : S.Γ.map (MulAut.conj k).toMonoidHom = S.Γ := by
    change ⁅S.D.model, S.D.model⁆.map _ = ⁅S.D.model, S.D.model⁆
    rw [Subgroup.map_commutator, hmodel]
  have hspan : (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).map
      (MulAut.conj k).toMonoidHom =
        rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [F4ExplicitPos.CommonFactor.rationalRoots_eq_componentRoots_of_orbitLength_one
      (i := i) (h1 := h1)]
    have hkn : k ∈ Subgroup.normalizer
        (rootSpan τ L (componentRoots (rootCharHom a) i) : Set (ModGL τ L)) :=
      sup_le (torusGroup_le_normalizer_rootSpan (fun α hα => isRoot_of_mem_componentRoots hα))
        (rootSpan_le_normalizer (K := L) i) hk
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 hkn
  have hspanEq : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map
      (MulAut.conj k).toMonoidHom = rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    change (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ).map _ =
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, hspan, hΓ]
  change (⁅rationalSpan S.ρ S.Γ (rootCharHom a) i,
    rationalSpan S.ρ S.Γ (rootCharHom a) i⁆).map _ =
      ⁅rationalSpan S.ρ S.Γ (rootCharHom a) i,
        rationalSpan S.ρ S.Γ (rootCharHom a) i⁆
  rw [Subgroup.map_commutator, hspanEq]

end CFSG.StandardType.RCKRP

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum

open CFSG.Blueprint.Chevalley

theorem map_conj_inf_eqLocus_eq_inf_model
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {k : ModGL τ L} (hk : D.step k = k) {U V : Subgroup (ModGL τ L)}
    (hUV : U.map (MulAut.conj k).toMonoidHom = V) (hV : V ≤ adjointGroup τ L) :
    (U ⊓ D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj k).toMonoidHom = V ⊓ D.model := by
  have hE : (D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj k).toMonoidHom =
      D.step.eqLocus (MonoidHom.id _) :=
    TauCeti.map_fixedSubgroup_eq (MulAut.conj k) (by
      refine MonoidHom.ext fun x => ?_
      simp [MulAut.conj_apply, map_mul, map_inv, hk])
  rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, hUV, hE, LangDatum.model,
    ← inf_assoc, inf_eq_left.2 hV]

end CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum

end
