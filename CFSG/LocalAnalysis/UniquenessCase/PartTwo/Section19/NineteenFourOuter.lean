module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOuterFactor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPMember
public import CFSG.GroupTheory.SwapMulSwapConj
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBS5
public import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem calP19_4_nonempty_of_outer (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    {A J : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hA5 : ¬ (J = L ∧ IsU3 (Bar2 L) 2))
    (hout : ¬ A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T))
    (hτ : E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G)) :
    (calP19_4 D L K J A).Nonempty := by
  classical
  obtain ⟨hTJ, a, haA, F, hFLK, hFJ, hAlt, hτF, hcore, hAτ, haN, houter⟩ :=
    outer_factor_19_4 h hA hJ hA5 hout hτ
  have haτ : a ∈ E1.tauOf (J ⊔ D.T) D.T A := hAτ haA
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, g, hAg, -⟩ := hA
  have hAelem : IsElemAbelian 2 A :=
    E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ g |>.mono hAg
  have ha2 : a * a = 1 := by
    have h1 := hAelem.2 a haA
    simpa [pow_two] using h1
  obtain ⟨θ⟩ := hAlt
  set ξ : MulAut (alternatingGroup (Fin 5)) :=
    MulAut.congr θ (UC6S846.rhoL F ⟨a, haN⟩) with hξdef
  set ζ : Equiv.Perm (Fin 5) := L139A5.autA5.symm ξ with hζdef
  have hξζ : L139A5.autA5 ζ = ξ := MulEquiv.apply_symm_apply _ _
  have hζspec : ∀ y : Bar2 F,
      ((θ (UC6S846.rhoL F ⟨a, haN⟩ y) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        ζ * ((θ y : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * ζ⁻¹ := by
    intro y
    have h1 : ξ (θ y) = θ (UC6S846.rhoL F ⟨a, haN⟩ y) := by simp [hξdef, MulAut.congr_apply]
    rw [← h1, ← hξζ]
    exact MulAut.conjNormal_apply ζ (θ y)
  have hξ2 : ξ * ξ = 1 := by
    have h1 : (⟨a, haN⟩ : ↥(normalizer (F : Set G))) * ⟨a, haN⟩ = 1 := by
      apply Subtype.ext
      exact ha2
    have h2 : UC6S846.rhoL F ⟨a, haN⟩ * UC6S846.rhoL F ⟨a, haN⟩ = 1 := by
      rw [← map_mul, h1, map_one]
    calc ξ * ξ = MulAut.congr θ (UC6S846.rhoL F ⟨a, haN⟩) *
          MulAut.congr θ (UC6S846.rhoL F ⟨a, haN⟩) := by rw [hξdef]
      _ = MulAut.congr θ (UC6S846.rhoL F ⟨a, haN⟩ * UC6S846.rhoL F ⟨a, haN⟩) := by
          rw [map_mul]
      _ = 1 := by rw [h2, map_one]
  have hζ2 : ζ * ζ = 1 := by
    rw [hζdef, ← map_mul, hξ2]
    exact map_one _
  have hζvalt : ζ ∉ alternatingGroup (Fin 5) := by
    intro hζmem
    apply houter
    set σ : alternatingGroup (Fin 5) := ⟨ζ, hζmem⟩ with hσdef
    have hξconj : ξ = L139A5.autA5 ζ := hξζ.symm
    have hconjσ : L139A5.autA5 ζ = MulAut.conj σ := by
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rw [MulAut.conj_apply]
      exact MulAut.conjNormal_apply ζ y
    have hρinner : UC6S846.rhoL F ⟨a, haN⟩ = MulAut.conj (θ.symm σ) := by
      have h1 : MulAut.congr θ.symm ξ = MulAut.congr θ.symm (L139A5.autA5 ζ) := by
        rw [hξconj]
      have h2 : MulAut.congr θ.symm ξ = UC6S846.rhoL F ⟨a, haN⟩ := by
        rw [hξdef]
        apply MulEquiv.ext
        intro y
        simp [MulAut.congr_apply]
      rw [← h2, h1, hconjσ,
        CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
    rw [hρinner]
    exact ⟨θ.symm σ, rfl⟩
  have hζodd : Equiv.Perm.sign ζ = -1 := (Int.units_eq_one_or _).resolve_left fun h1 =>
    hζvalt (Equiv.Perm.mem_alternatingGroup.mpr h1)
  obtain ⟨i, j, hij, hζswap⟩ := H13.GM22.perm5_isSwap_of_odd_involution hζ2 hζodd
  let ψ : ↥(E1.tauOf (J ⊔ D.T) D.T A) →* Equiv.Perm (Fin 5) :=
    (L139A5.autA5.symm.toMonoidHom.comp (MulAut.congr θ).toMonoidHom).comp
      ((UC6S846.rhoL F).comp (Subgroup.inclusion hτF))
  have hψa : ψ ⟨a, haτ⟩ = ζ := by
    have heq : (⟨a, hτF haτ⟩ : ↥(normalizer (F : Set G))) = ⟨a, haN⟩ := Subtype.ext rfl
    show L139A5.autA5.symm (MulAut.congr θ (UC6S846.rhoL F ⟨a, hτF haτ⟩)) = ζ
    rw [heq]
  have hψfix : ∃ c : Fin 5, ∀ t : ↥(E1.tauOf (J ⊔ D.T) D.T A), ψ t c = c := by
    let : MulAction ↥(E1.tauOf (J ⊔ D.T) D.T A) (Fin 5) := MulAction.compHom (Fin 5) ψ
    have hτ2 : IsPGroup 2 ↥(E1.tauOf (J ⊔ D.T) D.T A) :=
      D.sylowM.isPGroup.to_le (E1.tauOf_le _ _ _)
    have hndvd : ¬ 2 ∣ Nat.card (Fin 5) := by simp
    obtain ⟨c, hc⟩ := hτ2.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) hndvd
    refine ⟨c, fun t => ?_⟩
    have h1 := (MulAction.mem_fixedPoints.mp hc) t
    rwa [MulAction.compHom_smul_def] at h1
  obtain ⟨c, hc⟩ := hψfix
  have hζc : ζ c = c := by
    have h1 := hc ⟨a, haτ⟩
    rwa [hψa] at h1
  have hci : c ≠ i := by
    intro h
    have h1 : Equiv.swap i j c = c := by rw [← hζswap]; exact hζc
    rw [h] at h1
    rw [Equiv.swap_apply_left] at h1
    exact hij h1.symm
  have hcj : c ≠ j := by
    intro h
    have h1 : Equiv.swap i j c = c := by rw [← hζswap]; exact hζc
    rw [h] at h1
    rw [Equiv.swap_apply_right] at h1
    exact hij h1
  set tc : Equiv.Perm (Fin 5) := Equiv.swap i j * Equiv.swap j c with htceq
  have htc : tc.IsThreeCycle := by
    rw [htceq, Equiv.swap_comm i j]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hij.symm hcj.symm hci.symm
  have htcAlt : tc ∈ alternatingGroup (Fin 5) := htc.mem_alternatingGroup
  have htc3 : tc ^ 3 = 1 := by rw [← htc.orderOf]; exact pow_orderOf_eq_one tc
  have htcne : tc ≠ 1 := htc.ne_one
  set xbar : Bar2 F := θ.symm ⟨tc, htcAlt⟩ with hxbdef
  have hθxb : θ xbar = ⟨tc, htcAlt⟩ := MulEquiv.apply_symm_apply θ _
  have hΘxb : ((θ xbar : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = tc := by
    rw [hθxb]
  have hxbar3 : xbar ^ 3 = 1 := by
    apply θ.injective
    rw [map_pow, map_one, hθxb]
    exact Subtype.ext htc3
  have hxbarne : xbar ≠ 1 := by
    intro h
    apply htcne
    have h1 : ((θ xbar : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = tc := hΘxb
    rw [h] at h1
    have h2 : ((θ (1 : Bar2 F) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1 := by
      simp
    rw [h2] at h1
    exact h1.symm
  have hρaxbar : UC6S846.rhoL F ⟨a, haN⟩ xbar = xbar⁻¹ := by
    apply θ.injective
    apply Subtype.ext
    rw [hζspec xbar, map_inv, Subgroup.coe_inv, hζswap, hΘxb]
    rw [htceq, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, ← mul_assoc,
      Equiv.swap_mul_self, one_mul]
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥F) xbar
  have hker2 : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥F)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hmemker : y ^ 3 ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥F)).ker := by
    rw [MonoidHom.mem_ker, map_pow, hy, hxbar3]
  obtain ⟨m, hm⟩ := hker2 ⟨_, hmemker⟩
  have hy3 : (y : ↥F) ^ (3 * 2 ^ m) = 1 := by
    have h1 := congrArg (fun z : (QuotientGroup.mk' (CFSG.pCore 2 ↥F)).ker =>
      ((z : ↥F) : ↥F)) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    rw [← pow_mul] at h1
    exact h1
  set x : ↥F := y ^ 2 ^ m with hxdef
  have hximg : (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x = xbar ^ 2 ^ m := by
    rw [hxdef, map_pow, hy]
  have hx3 : x ^ 3 = 1 := by
    have h1 : (y : ↥F) ^ (2 ^ m * 3) = 1 := by
      rw [mul_comm (2 ^ m) 3]
      exact hy3
    rw [hxdef, ← pow_mul]
    exact h1
  have hw3 : (xbar ^ (2 ^ m)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm (2 ^ m) 3, pow_mul, hxbar3, one_pow]
  have hxbar2m : xbar ^ 2 ^ m ≠ 1 := by
    intro h
    have hdvd : orderOf xbar ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr h
    have h3 : orderOf xbar = 3 := orderOf_eq_prime hxbar3 hxbarne
    rw [h3] at hdvd
    have h2 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hxne : x ≠ 1 := by
    intro h
    apply hxbar2m
    rw [← hximg, h, map_one]
  have hxord : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx3 hxne
  set X : Subgroup G := Subgroup.zpowers (x : G) with hXdef
  have hXcard : Nat.card X = 3 := by
    rw [hXdef, Nat.card_zpowers, hxord]
  have hXJ : X ≤ J := Subgroup.zpowers_le.mpr (hFJ x.2)
  have hρax : UC6S846.rhoL F ⟨a, haN⟩ ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) =
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x)⁻¹ := by
    simp only [hximg, map_pow, hρaxbar, inv_pow]
  have hρtxbar : ∀ (t : G) (ht : t ∈ E1.tauOf (J ⊔ D.T) D.T A),
      UC6S846.rhoL F ⟨t, hτF ht⟩ xbar = xbar ∨
        UC6S846.rhoL F ⟨t, hτF ht⟩ xbar = xbar⁻¹ := by
    intro t ht
    set ζt : Equiv.Perm (Fin 5) :=
      L139A5.autA5.symm (MulAut.congr θ (UC6S846.rhoL F ⟨t, hτF ht⟩)) with hζtdef
    have hζt' : L139A5.autA5 ζt = MulAut.congr θ (UC6S846.rhoL F ⟨t, hτF ht⟩) :=
      MulEquiv.apply_symm_apply _ _
    have hfixc : ζt c = c := hc ⟨t, ht⟩
    have hcommρ : UC6S846.rhoL F ⟨a, haN⟩ * UC6S846.rhoL F ⟨t, hτF ht⟩ =
        UC6S846.rhoL F ⟨t, hτF ht⟩ * UC6S846.rhoL F ⟨a, haN⟩ := by
      have hta : ⁅t, a⁆ ∈ pCoreOf 2 (J ⊔ D.T) := (E1.mem_tauOf.mp ht).2.2 a haA
      have htaN : ⁅t, a⁆ ∈ normalizer (F : Set G) := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hτF ht) haN)
          (Subgroup.inv_mem _ (hτF ht))) (Subgroup.inv_mem _ haN)
      have h1 : UC6S846.rhoL F ⟨⁅t, a⁆, htaN⟩ = 1 :=
        UC6S846.rhoL_eq_one_of_mem_pCoreOf (hFJ.trans (le_sup_left : J ≤ J ⊔ D.T)) htaN hta
      have hprod : (⟨t, hτF ht⟩ : ↥(normalizer (F : Set G))) * ⟨a, haN⟩ *
          ⟨t, hτF ht⟩⁻¹ * ⟨a, haN⟩⁻¹ = ⟨⁅t, a⁆, htaN⟩ := rfl
      have h5 : UC6S846.rhoL F ⟨t, hτF ht⟩ * UC6S846.rhoL F ⟨a, haN⟩ *
          (UC6S846.rhoL F ⟨t, hτF ht⟩)⁻¹ * (UC6S846.rhoL F ⟨a, haN⟩)⁻¹ =
          UC6S846.rhoL F (⟨t, hτF ht⟩ * ⟨a, haN⟩ * ⟨t, hτF ht⟩⁻¹ * ⟨a, haN⟩⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have h2 : UC6S846.rhoL F ⟨t, hτF ht⟩ * UC6S846.rhoL F ⟨a, haN⟩ *
          (UC6S846.rhoL F ⟨t, hτF ht⟩)⁻¹ * (UC6S846.rhoL F ⟨a, haN⟩)⁻¹ = 1 := by
        rw [h5, hprod]
        exact h1
      have h3 : UC6S846.rhoL F ⟨t, hτF ht⟩ * UC6S846.rhoL F ⟨a, haN⟩ *
          (UC6S846.rhoL F ⟨t, hτF ht⟩)⁻¹ = UC6S846.rhoL F ⟨a, haN⟩ :=
        mul_inv_eq_one.mp h2
      calc UC6S846.rhoL F ⟨a, haN⟩ * UC6S846.rhoL F ⟨t, hτF ht⟩
          = (UC6S846.rhoL F ⟨t, hτF ht⟩ * UC6S846.rhoL F ⟨a, haN⟩ *
              (UC6S846.rhoL F ⟨t, hτF ht⟩)⁻¹) * UC6S846.rhoL F ⟨t, hτF ht⟩ := by
            rw [h3]
        _ = UC6S846.rhoL F ⟨t, hτF ht⟩ * UC6S846.rhoL F ⟨a, haN⟩ := by group
    have hcommζ : ζt * ζ = ζ * ζt := by
      have hρ : MulAut.congr θ (UC6S846.rhoL F ⟨t, hτF ht⟩ *
          UC6S846.rhoL F ⟨a, haN⟩) =
          MulAut.congr θ (UC6S846.rhoL F ⟨a, haN⟩ *
            UC6S846.rhoL F ⟨t, hτF ht⟩) := by
        rw [hcommρ]
      have h2 := congrArg (fun f => L139A5.autA5.symm f) hρ
      simpa only [map_mul] using h2
    have hcomm' : ζt * Equiv.swap i j = Equiv.swap i j * ζt := by
      rw [← hζswap]
      exact hcommζ
    have hθt : ((θ (UC6S846.rhoL F ⟨t, hτF ht⟩ xbar) : alternatingGroup (Fin 5)) :
        Equiv.Perm (Fin 5)) = ζt * tc * ζt⁻¹ := by
      have h1 : (MulAut.congr θ (UC6S846.rhoL F ⟨t, hτF ht⟩)) (θ xbar) =
          θ (UC6S846.rhoL F ⟨t, hτF ht⟩ xbar) := by
        simp [MulAut.congr_apply]
      have h2 := MulAut.conjNormal_apply ζt (θ xbar)
      rw [hΘxb] at h2
      rw [← h1, ← hζt']
      exact h2
    rcases CFSG.GroupTheory.conj_swap_mul_swap_eq_or_eq_inv hij hci hcj hcomm' hfixc with h | h
    · left
      apply θ.injective
      apply Subtype.ext
      rw [hθt, h, hΘxb]
    · right
      apply θ.injective
      apply Subtype.ext
      rw [hθt, h, map_inv, Subgroup.coe_inv, hΘxb]
  have htx : ∀ (t : G) (ht : t ∈ E1.tauOf (J ⊔ D.T) D.T A),
      t * (x : G) * t⁻¹ ∈ X ⊔ pCoreOf 2 (J ⊔ D.T) := by
    intro t ht
    have htxF : t * (x : G) * t⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hτF ht) (x : G)).mp x.2
    have himg : (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) ⟨t * (x : G) * t⁻¹, htxF⟩ =
        UC6S846.rhoL F ⟨t, hτF ht⟩ ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) := by
      show (QuotientGroup.mk (⟨t * (x : G) * t⁻¹, htxF⟩ : ↥F) : Bar2 F) =
        UC6S846.rhoL F ⟨t, hτF ht⟩ (QuotientGroup.mk x)
      rw [UC6S846.rhoL_mk]
      congr 1
    have hρt : UC6S846.rhoL F ⟨t, hτF ht⟩ ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) =
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) ∨
      UC6S846.rhoL F ⟨t, hτF ht⟩ ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) =
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x)⁻¹ := by
      rcases hρtxbar t ht with h | h
      · left; rw [hximg, map_pow, h]
      · right; rw [hximg, map_pow, h, inv_pow]
    have hdiv : ∀ (h : UC6S846.rhoL F ⟨t, hτF ht⟩ ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) =
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x)),
        (t * (x : G) * t⁻¹) * (x : G)⁻¹ ∈ pCoreOf 2 F := by
      intro h
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) ⟨t * (x : G) * t⁻¹, htxF⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x := by rw [himg, h]
      have h2 : (⟨t * (x : G) * t⁻¹, htxF⟩ : ↥F) / x ∈ CFSG.pCore 2 ↥F := by
        rw [← QuotientGroup.eq_iff_div_mem]
        exact h1
      have h3 : ((⟨t * (x : G) * t⁻¹, htxF⟩ : ↥F) / x : ↥F) ∈ CFSG.pCore 2 ↥F := h2
      rw [← CFSG.mem_openPCoreOf_iff] at h3
      simpa [Subgroup.coe_div, div_eq_mul_inv] using h3
    have hdiv' : ∀ (h : UC6S846.rhoL F ⟨t, hτF ht⟩ ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) =
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x)⁻¹),
        (t * (x : G) * t⁻¹) * (x : G) ∈ pCoreOf 2 F := by
      intro h
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) ⟨t * (x : G) * t⁻¹, htxF⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x⁻¹ := by rw [himg, h, map_inv]
      have h2 : (⟨t * (x : G) * t⁻¹, htxF⟩ : ↥F) / x⁻¹ ∈ CFSG.pCore 2 ↥F := by
        rw [← QuotientGroup.eq_iff_div_mem]
        exact h1
      have h3 : ((⟨t * (x : G) * t⁻¹, htxF⟩ : ↥F) / x⁻¹ : ↥F) ∈ CFSG.pCore 2 ↥F := h2
      rw [← CFSG.mem_openPCoreOf_iff] at h3
      have h4 : ((⟨t * (x : G) * t⁻¹, htxF⟩ : ↥F) / x⁻¹ : ↥F) =
          ⟨(t * (x : G) * t⁻¹) * (x : G), by
            exact F.mul_mem htxF x.2⟩ := Subtype.ext (by simp [div_eq_mul_inv])
      rw [h4] at h3
      exact h3
    rcases hρt with h | h
    · have h3 := hdiv h
      have hurw : t * (x : G) * t⁻¹ = ((t * (x : G) * t⁻¹) * (x : G)⁻¹) * (x : G) := by group
      rw [hurw]
      exact (X ⊔ pCoreOf 2 (J ⊔ D.T)).mul_mem (Subgroup.mem_sup_right (hcore h3))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers (x : G)))
    · have h3 := hdiv' h
      have hurw : t * (x : G) * t⁻¹ = ((t * (x : G) * t⁻¹) * (x : G)) * (x : G)⁻¹ := by group
      rw [hurw]
      exact (X ⊔ pCoreOf 2 (J ⊔ D.T)).mul_mem (Subgroup.mem_sup_right (hcore h3))
        (Subgroup.mem_sup_left (X.inv_mem (Subgroup.mem_zpowers (x : G))))
  have hτX : E1.tauOf (J ⊔ D.T) D.T A ≤
      normalizer ((X ⊔ pCoreOf 2 (J ⊔ D.T) : Subgroup G) : Set G) := by
    intro t ht
    have htNQ : t ∈ normalizer (pCoreOf 2 (J ⊔ D.T) : Set G) := by
      have htJT : t ∈ J ⊔ D.T :=
        (le_sup_right : D.T ≤ J ⊔ D.T) ((E1.tauOf_le (J ⊔ D.T) D.T A) ht)
      exact (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (J ⊔ D.T))) htJT
    have hmapX : X.map (MulAut.conj t).toMonoidHom ≤ X ⊔ pCoreOf 2 (J ⊔ D.T) := by
      rintro z ⟨w, hw, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have h1 : (MulAut.conj t).toMonoidHom ((x : G) ^ k) = (t * (x : G) * t⁻¹) ^ k := by
        rw [map_zpow]
        congr 1
      rw [h1]
      exact (X ⊔ pCoreOf 2 (J ⊔ D.T)).zpow_mem (htx t ht) k
    have hmapQ : (pCoreOf 2 (J ⊔ D.T)).map (MulAut.conj t).toMonoidHom =
        pCoreOf 2 (J ⊔ D.T) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htNQ
    have hle : (X ⊔ pCoreOf 2 (J ⊔ D.T)).map (MulAut.conj t).toMonoidHom ≤
        X ⊔ pCoreOf 2 (J ⊔ D.T) := by
      rw [Subgroup.map_sup, hmapQ]
      exact sup_le hmapX le_sup_right
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hax : ⁅a, (x : G)⁆ ∉ pCoreOf 2 (J ⊔ D.T) := by
    intro hQ
    have hmem1 : a * (x : G) * a⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp haN (x : G)).mp x.2
    have haxF : ⁅a, (x : G)⁆ ∈ F := by
      rw [commutatorElement_def]
      exact F.mul_mem hmem1 (F.inv_mem x.2)
    have hO2 : ⁅a, (x : G)⁆ ∈ pCoreOf 2 F :=
      CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (hFJ.trans (le_sup_left : J ≤ J ⊔ D.T)) ⟨haxF, hQ⟩
    have himg1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) ⟨⁅a, (x : G)⁆, haxF⟩ = 1 := by
      show (QuotientGroup.mk (⟨⁅a, (x : G)⁆, haxF⟩ : ↥F) : Bar2 F) = 1
      rw [QuotientGroup.eq_one_iff]
      exact (CFSG.mem_openPCoreOf_iff ⟨⁅a, (x : G)⁆, haxF⟩).mp hO2
    have h1 : (⟨⁅a, (x : G)⁆, haxF⟩ : ↥F) = ⟨a * (x : G) * a⁻¹, hmem1⟩ * x⁻¹ := by
      apply Subtype.ext
      show ⁅a, (x : G)⁆ = a * (x : G) * a⁻¹ * (x : G)⁻¹
      rw [commutatorElement_def]
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥F)) ⟨a * (x : G) * a⁻¹, hmem1⟩ =
        UC6S846.rhoL F ⟨a, haN⟩ ((QuotientGroup.mk' (CFSG.pCore 2 ↥F)) x) := by
      show (QuotientGroup.mk (⟨a * (x : G) * a⁻¹, hmem1⟩ : ↥F) : Bar2 F) =
        UC6S846.rhoL F ⟨a, haN⟩ (QuotientGroup.mk x)
      rw [UC6S846.rhoL_mk]
      congr 1
    rw [h1, map_mul, map_inv, h2, hρax, hximg] at himg1
    have hw2 : (xbar ^ (2 ^ m)) ^ 2 = 1 := by
      calc (xbar ^ (2 ^ m)) ^ 2 =
          ((xbar ^ (2 ^ m))⁻¹ * (xbar ^ (2 ^ m))⁻¹)⁻¹ := by group
        _ = 1 := by rw [himg1, inv_one]
    have hword : orderOf (xbar ^ (2 ^ m)) = 3 := orderOf_eq_prime hw3 hxbar2m
    have hdvd : orderOf (xbar ^ (2 ^ m)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hw2
    rw [hword] at hdvd
    omega
  exact ⟨_, sup_tauOf_mem_calP19_4 h hAgamma hJ Nat.prime_three (by norm_num) hXcard hXJ hτX
    ⟨a, haA, (x : G), Subgroup.mem_zpowers (x : G), hax⟩
    (Or.inr ⟨rfl, F, hFLK, Subgroup.zpowers_le.mpr x.2, hτF⟩)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
