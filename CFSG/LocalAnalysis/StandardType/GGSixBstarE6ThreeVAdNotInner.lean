module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFaithful
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeTorus
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.HardMathSupport.Lang.Proving.CubeClassField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section VAdNotInner

open TableBExc.E6Three

variable {K : Type} [Field K] [Fintype K]

theorem vAd_not_le_innerAut (h9 : ¬ 9 ∣ Nat.card K - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    ¬ vAd (K := K) ζ hζ ≤
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  classical
  intro hv
  let x₀ : Fin Tag.E6.rank → ZMod 3 := Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1
  let a : Fin Tag.E6.rank → Kˣ := TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ x₀
  let X : Multiplicative (Fin Tag.E6.rank → ZMod 3) := Multiplicative.ofAdd x₀
  have hgen : diag3 ζ hζ X ∈ (MulAut.conj :
      adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
    hv ⟨X, rfl⟩
  obtain ⟨c, hc⟩ := hgen
  have hdiag : diag3 (K := K) ζ hζ X = rootDiagAutHom .E6 K a := rfl
  let z : TableBExc.E6Three.hatGroup .E6 K :=
    ⟨(c : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹,
      ⟨c, c.2, a⁻¹, by rw [rootDiagUnit_inv]⟩⟩
  have hconj_all : ∀ h : adjointGroup .E6 K,
      (c : ModGL .E6 K) * (h : ModGL .E6 K) * (c : ModGL .E6 K)⁻¹ =
        rootDiagUnit .E6 a * (h : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹ := by
    intro h
    have e := congrArg (fun φ : MulAut (adjointGroup .E6 K) =>
      ((φ h : adjointGroup .E6 K) : ModGL .E6 K)) (hc.trans hdiag)
    simpa [MulAut.conj_apply, rootDiagAutHom, rootDiagAut, coe_rootDiagAut] using e
  have hz : TableBExc.E6Three.hatAut .E6 K z = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [TableBExc.E6Three.coe_hatAut_apply]
    have hfix : (c : ModGL .E6 K) * ((rootDiagAut .E6 K a⁻¹ h : adjointGroup .E6 K) :
        ModGL .E6 K) * (c : ModGL .E6 K)⁻¹ = (h : ModGL .E6 K) := by
      have e := hconj_all (rootDiagAut .E6 K a⁻¹ h)
      rw [coe_rootDiagAut] at e
      rw [show (rootDiagUnit .E6 a)⁻¹ = rootDiagUnit .E6 a⁻¹ from rootDiagUnit_inv a] at e
      calc (c : ModGL .E6 K) * (rootDiagAut .E6 K a⁻¹ h : adjointGroup .E6 K) *
            (c : ModGL .E6 K)⁻¹
          = rootDiagUnit .E6 a * (rootDiagUnit .E6 a⁻¹ * (h : ModGL .E6 K) *
              (rootDiagUnit .E6 a⁻¹)⁻¹) * (rootDiagUnit .E6 a)⁻¹ := e
        _ = (h : ModGL .E6 K) := by
          rw [← rootDiagUnit_inv]
          group
    have hfix' : (c : ModGL .E6 K) * ((rootDiagUnit .E6 a)⁻¹ * (h : ModGL .E6 K) *
        rootDiagUnit .E6 a) * (c : ModGL .E6 K)⁻¹ = (h : ModGL .E6 K) := by
      rw [coe_rootDiagAut, ← rootDiagUnit_inv] at hfix
      exact hfix
    have hcinv : (rootDiagUnit .E6 a)⁻¹ * (h : ModGL .E6 K) * rootDiagUnit .E6 a =
        (c : ModGL .E6 K)⁻¹ * (h : ModGL .E6 K) * (c : ModGL .E6 K) := by
      calc (rootDiagUnit .E6 a)⁻¹ * (h : ModGL .E6 K) * rootDiagUnit .E6 a
          = (c : ModGL .E6 K)⁻¹ * ((c : ModGL .E6 K) * ((rootDiagUnit .E6 a)⁻¹ *
              (h : ModGL .E6 K) * rootDiagUnit .E6 a) * (c : ModGL .E6 K)⁻¹) *
              (c : ModGL .E6 K) := by group
        _ = (c : ModGL .E6 K)⁻¹ * (h : ModGL .E6 K) * (c : ModGL .E6 K) := by rw [hfix']
    show ((c : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹) * (h : ModGL .E6 K) *
        ((c : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹)⁻¹ = (h : ModGL .E6 K)
    calc ((c : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹) * (h : ModGL .E6 K) *
          ((c : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹)⁻¹
        = (c : ModGL .E6 K) * ((rootDiagUnit .E6 a)⁻¹ * (h : ModGL .E6 K) *
            rootDiagUnit .E6 a) * (c : ModGL .E6 K)⁻¹ := by group
      _ = (c : ModGL .E6 K) * ((c : ModGL .E6 K)⁻¹ * (h : ModGL .E6 K) *
            (c : ModGL .E6 K)) * (c : ModGL .E6 K)⁻¹ := by rw [hcinv]
      _ = (h : ModGL .E6 K) := by group
  have hz1 : z = 1 := hatAut_injective (τ := .E6) hz
  have hdaC : rootDiagUnit .E6 a ∈ adjointGroup .E6 K := by
    have hval : ((z : TableBExc.E6Three.hatGroup .E6 K) : ModGL .E6 K) = 1 :=
      congrArg Subtype.val hz1
    have h1 : (c : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹ = 1 := by
      rw [← hval]
    have h2 : (c : ModGL .E6 K)⁻¹ = (rootDiagUnit .E6 a)⁻¹ :=
      inv_eq_of_mul_eq_one_right h1
    have hceq : rootDiagUnit .E6 a = (c : ModGL .E6 K) := by
      calc rootDiagUnit .E6 a = ((rootDiagUnit .E6 a)⁻¹)⁻¹ := by group
        _ = ((c : ModGL .E6 K)⁻¹)⁻¹ := by rw [← h2]
        _ = (c : ModGL .E6 K) := by group
    rw [hceq]
    exact c.2
  have hdaT : rootDiagUnit .E6 a ∈ torusGroup .E6 K :=
    CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup (τ := .E6) a hdaC
  obtain ⟨q, hq⟩ := exists_cartanChar_eq_of_mem_torusGroup (τ := .E6) (K := K) hdaT
  have haeq : a = cartanChar q := rootDiagUnit_injective (τ := .E6) hq
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [← Nat.card_units K]
    exact hζo ▸ orderOf_dvd_natCard ζ
  have hcube_cartan : ∃ u : Kˣ, u ^ 3 = ∏ i, cartanChar q i ^ NoOffRest.kE6 i := by
    have hT : ∀ j : Fin Tag.E6.rank, ∃ t : ℤ,
        ∑ i, (Tag.E6.cartan j i : ℤ) * NoOffRest.kE6 i = 3 * t := by
      intro j
      have h : (3 : ℤ) ∣ ∑ i, (Tag.E6.cartan j i : ℤ) * NoOffRest.kE6 i := by
        revert j
        decide +kernel
      exact ⟨_, by rw [mul_comm]; exact (Int.ediv_mul_cancel h).symm⟩
    choose t ht using hT
    refine ⟨∏ j, q j ^ t j, ?_⟩
    have step1 : (∏ i, cartanChar q i ^ NoOffRest.kE6 i) =
        ∏ j, q j ^ (∑ i, (Tag.E6.cartan j i : ℤ) * NoOffRest.kE6 i) := by
      simp only [cartanChar]
      trans ∏ i, ∏ j, (q j ^ (Tag.E6.cartan j i : ℤ)) ^ NoOffRest.kE6 i
      · refine Finset.prod_congr rfl fun i _ => ?_
        exact (Finset.prod_zpow (s := Finset.univ) (n := NoOffRest.kE6 i)
          (f := fun j => q j ^ (Tag.E6.cartan j i : ℤ))).symm
      · trans ∏ j, ∏ i, (q j ^ (Tag.E6.cartan j i : ℤ)) ^ NoOffRest.kE6 i
        · exact Finset.prod_comm
        · refine Finset.prod_congr rfl fun j _ => ?_
          have h : (∏ i, (q j ^ (Tag.E6.cartan j i : ℤ)) ^ NoOffRest.kE6 i) =
              ∏ i, q j ^ ((Tag.E6.cartan j i : ℤ) * NoOffRest.kE6 i) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [zpow_mul]
          rw [h, Finset.prod_zpow_eq_zpow_sum]
    have step2 : (∏ j, q j ^ (∑ i, (Tag.E6.cartan j i : ℤ) * NoOffRest.kE6 i)) =
        (∏ j, q j ^ t j) ^ 3 := by
      have h : (∏ j, q j ^ (∑ i, (Tag.E6.cartan j i : ℤ) * NoOffRest.kE6 i)) =
          ∏ j, (q j ^ t j) ^ 3 := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [ht j, mul_comm, ← zpow_natCast (q j ^ t j) 3, ← zpow_mul]
        norm_num
      rw [h, ← Finset.prod_pow]
    rw [step1, step2]
  have hprod : (∏ i : Fin Tag.E6.rank, a i ^ NoOffRest.kE6 i) = ζ := by
    let f : Fin Tag.E6.rank → Kˣ := fun i => a i ^ NoOffRest.kE6 i
    change (∏ i, f i) = ζ
    let i0 : Fin Tag.E6.rank := ⟨0, by decide⟩
    have hk0 : NoOffRest.kE6 i0 = 1 := by decide
    have ha0 : a i0 = ζ := by
      dsimp [a, x₀, i0]
      rw [TableBExc.E6Three.zetaVec_apply, Pi.single_eq_same, ZMod.val_one]
      norm_num [NoOffRest.kE6]
    have hf0 : f i0 = ζ := by
      dsimp [f]
      rw [ha0, hk0]
      exact zpow_one ζ
    have hother : ∀ b ∈ Finset.univ, b ≠ i0 → f b = 1 := by
      intro b _ hb
      dsimp [f, a, x₀]
      rw [TableBExc.E6Three.zetaVec_apply, Pi.single_eq_of_ne hb, ZMod.val_zero, pow_zero,
        one_zpow]
    calc (∏ i, f i) = f i0 :=
          Finset.prod_eq_single (s := Finset.univ) (f := f) i0 hother (by simp)
      _ = ζ := hf0
  have hcube : ∃ u : Kˣ, u ^ 3 = ζ := by
    obtain ⟨u, hu⟩ := hcube_cartan
    refine ⟨u, ?_⟩
    rw [hu, ← haeq]
    exact hprod
  have hpow : ζ ^ ((Nat.card K - 1) / 3) = 1 :=
    (CFSG.HardMathSupport.Lang.Proving.exists_cube_iff_pow_eq_one h3 ζ).1 hcube
  have hdvd : 3 ∣ (Nat.card K - 1) / 3 := by
    have := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rwa [hζo] at this
  apply h9
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  rw [← Nat.mul_div_cancel' h3, ht]
  ring

end VAdNotInner

end NoOffE6Three

end CFSG.StandardType
