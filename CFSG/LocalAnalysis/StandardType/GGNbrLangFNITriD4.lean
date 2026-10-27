module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIExcTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.RootTw

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.PerfectAutomorphisms


private theorem fniT_mulAut_congr_conj {R R' : Type} [Group R] [Group R'] (e : R ≃* R') (r : R) :
    MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext y
  change e (r * e.symm y * r⁻¹) = e r * y * (e r)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem kgFieldRestrictionCont_triD4 {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hsub : RecipeExcLang.markIDImage (IsRoot TwistTag.D4.tag) K
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊆
        LargeEvenInnSet (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    KGFieldRestrictionCont p
      (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (RecipeExcLang.markIDImage (IsRoot TwistTag.D4.tag) K
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK3
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have hOneModel := kgfniTw_hOne_model (t := TwistTag.D4) hp hp2 hn hK σ hσ
  intro f hf hord h hh hhp hcomm J₀ hJ₀ f' hf'
  by_cases hh1 : h = 1
  · exact hOneModel f hf hord h hh hhp hcomm hh1 J₀ hJ₀ f' hf'
  ·
    let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
    let Rmod := LargeEvenCenterQuot C
    let eC : Rmod ≃* C := centerQuotEquivOfBot hZ
    have hin : h ∈ LargeEvenInnSet Rmod := hsub hh
    obtain ⟨c, hc⟩ := hin
    obtain ⟨δ, hδeq⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.excTw_exists_fieldActor_of_mem_markField
        (t := TwistTag.D4) σ hf
    have hδp : orderOf δ = p := by
      rw [← CFSG.LocalAnalysis.GLTheoremA.K155X.excTriD4_orderOf_fieldActor (K := K) hn hK σ hσ δ,
        ← hδeq, MulEquiv.orderOf_eq, hord]
    have hEh : MulAut.congr eC h = MulAut.conj (eC c) := by
      rw [hc.symm, fniT_mulAut_congr_conj]
    have hcomm' : MulAut.conj (eC c) * fieldActor σ δ =
        fieldActor σ δ * MulAut.conj (eC c) := by
      have h1 := congrArg (MulAut.congr eC) hcomm
      rw [map_mul, map_mul, hEh, hδeq] at h1
      exact h1
    have hfixδ : fieldActor σ δ (eC c) = eC c := by
      have h1 : MulAut.conj (fieldActor σ δ (eC c)) = MulAut.conj (eC c) := by
        refine mul_right_cancel (b := fieldActor σ δ) ?_
        rw [← CFSG.LieType.Chevalley.mulAut_mul_conj, ← hcomm']
      exact CFSG.LocalAnalysis.GLTheoremA.K155X.excTw_conj_injective hZ h1
    have hpC : (eC c : C) ^ p = 1 := by
      have h1 : (MulAut.conj (eC c)) ^ p = 1 := by
        rw [← hEh, ← map_pow, hhp, map_one]
      have h2 : MulAut.conj ((eC c) ^ p) = 1 := by
        rw [map_pow]
        exact h1
      exact CFSG.LocalAnalysis.GLTheoremA.K155X.excTw_conj_injective hZ
        (h2.trans (map_one _).symm)
    have hp1 : (eC c : ModGL TwistTag.D4.tag K) ^ p = 1 := by
      simpa [Subgroup.coe_pow] using congrArg (fun x : C => (x : ModGL TwistTag.D4.tag K)) hpC
    have hc1 : (eC c : ModGL TwistTag.D4.tag K) ≠ 1 := by
      intro h1
      apply hh1
      rw [hc.symm]
      have hc' : c = 1 := eC.injective (Subtype.ext h1)
      rw [hc']
      exact map_one (MulAut.conj : Rmod →* MulAut Rmod)
    have hp0 : p % 3 ≠ 0 := by
      intro h0
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.dvd_of_mod_eq_zero h0)).symm
    have hjp : p % 3 * p % 3 = 1 := by
      rw [Nat.mul_mod, Nat.mod_mod]
      have h1 : p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases h1 with h1 | h1 <;> rw [h1]
    obtain ⟨e, k, T, hep, he1, hT, hk, hcop⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.excTw_frob_root (m := 3) (a := 2 * (p % 3)) hp
        (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)) hn (by norm_num)
        hK σ hσ (by rw [mul_assoc]; omega) δ hδp
    have hKe : Nat.card K = (2 ^ (e * p)) ^ 3 := by rw [hK, hep]
    let φ : MulAut C := fieldActor (t := TwistTag.D4) (K := K) σ (σ ^ (2 * (p % 3)) * T)
    have hfixφ : φ (eC c) = eC c := by
      change fieldActor (t := TwistTag.D4) (K := K) σ (σ ^ (2 * (p % 3)) * T) (eC c) = eC c
      rw [← hk, ← fieldActorHom_apply (t := TwistTag.D4), map_pow]
      have hpowfix : ∀ m : ℕ, ((fieldActorHom σ) δ ^ m) (eC c) = eC c := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [pow_succ, MulAut.mul_apply, fieldActorHom_apply, hfixδ]
          exact ih
      exact hpowfix k
    have hσ' : ∀ c, σ c = c ^ (2 ^ (e * p)) := by
      intro c
      rw [hep]
      exact hσ c
    have hfixφ' : diagramMap TwistTag.D4 K ^ (p % 3) *
        Units.map (entrywiseHom T.toRingHom) (eC c : ModGL TwistTag.D4.tag K) *
        (diagramMap TwistTag.D4 K ^ (p % 3))⁻¹ = (eC c : ModGL TwistTag.D4.tag K) := by
      rw [← CFSG.LocalAnalysis.GLTheoremA.K155X.excTriD4_coe_fieldActor_mul
        hK σ hσ (p % 3) T (eC c)]
      exact congrArg (fun x : C => (x : ModGL TwistTag.D4.tag K)) hfixφ
    obtain ⟨SL, Rt, a, ι, hSLq, hq0, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_frobRoot_triD4
        hp hp2 he1 hjp hKe σ hσ' T.toRingHom hT (MulAut.conj (eC c))
        (φ) (eC c : ModGL TwistTag.D4.tag K) (eC c).2
        (fun c' => rfl)
        (fun c' => CFSG.LocalAnalysis.GLTheoremA.K155X.excTriD4_coe_fieldActor_mul
          hK σ hσ (p % 3) T c') hp1 hc1 hfixφ'
    haveI : Finite C :=
      Finite.of_injective (Subtype.val : C → ModGL TwistTag.D4.tag K) Subtype.val_injective
    have hφeq : φ = MulAut.congr eC (f ^ k) := by
      change fieldActor (t := TwistTag.D4) (K := K) σ (σ ^ (2 * (p % 3)) * T) =
        MulAut.congr eC (f ^ k)
      rw [← hk, ← fieldActorHom_apply (t := TwistTag.D4), map_pow]
      change (fieldActor σ δ) ^ k = MulAut.congr eC (f ^ k)
      rw [← hδeq, ← map_pow]
    exact kgFieldRestriction_of_langSetup hp hp2 eC k SL Rt he1 hq0 hTa hap ha1 hfa ι hι hrange
      (fun c' => by rw [hEh]; exact hβ c') (fun c' => by rw [← hφeq]; exact hφ c') J₀ hJ₀ f' hf'


theorem kgFieldRestrictionOn_triality : KGFieldRestrictionOn (kgfniRow .triality) := by
  intro p lab hp hp2 hlab ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, -⟩ := hrow
  simp only [KGFNIFamily.tagCase] at htag
  subst htag
  have hp3 : p ≠ 3 := fun hp3 => ht3 ⟨rfl, hp3⟩
  exact kgFieldRestrictionOn_of_excTw_model (t := TwistTag.D4) hlab rfl fun K _ _ σ hK hσ =>
    kgFieldRestrictionCont_triD4 hp hp2 hp3 hlab.1 hK σ hσ
      (CFSG.LocalAnalysis.GLTheoremA.K155X.excTw_transport
        (Q := fun R _ I _ => I ⊆ LargeEvenInnSet R) σ hσ (excTw_perfect hlab.1 hK σ hσ)
        (TableBExcSmallRest.chevIDImage_subset_inn_triD4 hlab.1 K hK))

end CFSG.StandardType

end
