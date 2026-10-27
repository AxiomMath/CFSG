module

public import CFSG.LocalAnalysis.StandardType.GGKG87BSCBridge
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryLift
public import CFSG.LieType.CentralExt.CoprimeLift

public noncomputable section

namespace CFSG.StandardType.E4bOriginalLift

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.LieType.Steinberg.CentralExt
open CFSG.HardMathSupport.Timmesfeld.CrossChar (minBC)
open CFSG.SeitzReduction.F4Pilot (twistedIsogenyC coe_twistedIsogenyC
  ker_twistedIsogenyC twistedIsogenyC_surjective)
open CFSG.StandardType.TwE6FixedA2SL3
open CFSG.StandardType.E4bLift
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ n) ^ 2)
  {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
  {ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n}
  {J : Type} [Group J] [Finite J]
  {ψ : J →* TwE6Delta.RecipeR K n}
  (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
  (hperf : commutator J = ⊤)
  {F : Type} [Field F] [Finite F]
  (ι : K →+* F) (t : ↥(e6Data_valid.minGroup F))

@[expose] def originalM : J →* ModGL Tag.E6 F :=
  (MulAut.conj ((e6Isogeny F t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)).toMonoidHom.comp
    ((baseChangeGL (τ := Tag.E6) ι).comp
      ((twistedE6RootGroup K σ).subtype.comp
        (ε.symm.toMonoidHom.comp ψ)))

@[expose] def originalMR : TwE6Delta.RecipeR K n →* ModGL Tag.E6 F :=
  (MulAut.conj ((e6Isogeny F t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)).toMonoidHom.comp
    ((baseChangeGL (τ := Tag.E6) ι).comp
      ((twistedE6RootGroup K σ).subtype.comp ε.symm.toMonoidHom))

theorem originalM_eq_comp_originalMR :
    originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t =
      (originalMR (K := K) (F := F) (σ := σ) (ε := ε) ι t).comp ψ :=
  rfl

@[expose] def originalI :
    ↥(fixedGroup K σ.toRingHom) →* ↥(e6Data_valid.minGroup F) :=
  (MulAut.conj t).toMonoidHom.comp
    ((minBC e6Data_valid ι).comp (fixedGroup K σ.toRingHom).subtype)

theorem hσ_toRingHom (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∀ c, σ.toRingHom c = c ^ 2 ^ n := by
  intro c
  simpa using hσ c

@[expose] def originalQ0 (hn : 1 ≤ n) :
    ↥(fixedGroup K σ.toRingHom) →* TwE6Delta.RecipeR K n :=
  ε.toMonoidHom.comp (twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ))

theorem originalI_injective :
    Function.Injective (originalI (K := K) (F := F) (σ := σ) ι t) := by
  intro x y h
  apply Subtype.ext
  apply CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
    e6Data_valid ι
  exact (MulAut.conj t).injective h

theorem originalI_pi (u : ↥(fixedGroup K σ.toRingHom)) :
    ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      ((e6Isogeny F t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
        baseChangeGL ι
          ((e6Isogeny K (u : e6Data_valid.minGroup K) :
            ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
      ((e6Isogeny F t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)⁻¹ := by
  simp only [originalI, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_minBC]
  rfl


theorem originalQ0_apply (hn : 1 ≤ n) (u : ↥(fixedGroup K σ.toRingHom)) :
    originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u =
      ε (twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ) u) :=
  rfl

theorem originalM_apply (j : J) :
    originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t j =
      ((MulAut.conj ((e6Isogeny F t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F))
        ((baseChangeGL (τ := Tag.E6) ι)
          (((ε.symm (ψ j) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)))) :=
  rfl

theorem originalM_eq_pi_originalI (hn : 1 ≤ n)
    (u : ↥(fixedGroup K σ.toRingHom)) {j : J}
    (hj : ψ j = originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u) :
    originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t j =
      ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) := by
  have hε : (ε.symm (ψ j) : ↥(twistedE6RootGroup K σ)) =
      twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ) u := by
    apply ε.injective
    rw [MulEquiv.apply_symm_apply]
    exact hj
  rw [originalM_apply, hε, originalI_pi]
  rw [coe_twistedIsogenyC]
  rfl


theorem exists_u_originalI_eq_ahat (hn : 1 ≤ n) (hF : 4 < Nat.card F)
    (h3 : 3 ∣ 2 ^ n + 1) {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {d : J} (hd : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t d =
      ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F))
    (u0 : ↥(fixedGroup K σ.toRingHom))
    (hu0 : originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u0 = ψ d) :
    ∃ u : ↥(fixedGroup K σ.toRingHom),
      originalI (K := K) (F := F) (σ := σ) ι t u = fixedA2Ahat (F := F) hF ω ∧
        u ^ 3 = 1 ∧
        originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u = ψ d := by
  let ahat : ↥(e6Data_valid.minGroup F) := fixedA2Ahat (F := F) hF ω
  let a : ModGL Tag.E6 F :=
    ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
      ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
  have hπu0 : ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u0) :
      ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) := by
    have hε : (twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ) u0 :
        ↥(twistedE6RootGroup K σ)) = ε.symm (ψ d) := by
      apply ε.injective
      rw [MulEquiv.apply_symm_apply]
      simpa only [originalQ0_apply] using hu0
    have hπK' : ((e6IsogenyT K (u0 : e6Data_valid.minGroup K) :
        ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) =
        ((twistedE6RootGroup K σ).subtype (ε.symm (ψ d)) :
          ModGL TwistTag.E6.tag K) := by
      rw [← coe_twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ) u0]
      exact congrArg Subtype.val hε
    have hπK : ((e6Isogeny K (u0 : e6Data_valid.minGroup K) :
        ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        ((twistedE6RootGroup K σ).subtype (ε.symm (ψ d)) : ModGL Tag.E6 K) := by
      change ((e6IsogenyT K (u0 : e6Data_valid.minGroup K) :
        ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) =
        ((twistedE6RootGroup K σ).subtype (ε.symm (ψ d)) :
          ModGL TwistTag.E6.tag K)
      exact hπK'
    rw [originalI_pi, hπK]
    change ((e6Isogeny F t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
        baseChangeGL (τ := Tag.E6) ι
          ((twistedE6RootGroup K σ).subtype (ε.symm (ψ d)) : ModGL Tag.E6 K) *
      ((e6Isogeny F t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)⁻¹ =
        ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
          ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
    rw [← hd, originalM_apply]
    rfl
  have hπahat : ((e6Isogeny F ahat : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) := by
    rw [fixedA2Ahat_pi]
  let z : ↥(e6Data_valid.minGroup F) :=
    (originalI (K := K) (F := F) (σ := σ) ι t u0)⁻¹ * ahat
  have hzdef : z = (originalI (K := K) (F := F) (σ := σ) ι t u0)⁻¹ * ahat := rfl
  have hπu0' : e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u0) =
      fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :=
    Subtype.ext hπu0
  have hπahat' : e6Isogeny F ahat =
      fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :=
    fixedA2Ahat_pi (F := F) hF ω
  have hzker : z ∈ (e6Isogeny F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπu0', hπahat', inv_mul_cancel]
  have hzcenter : z ∈ Subgroup.center ↥(e6Data_valid.minGroup F) :=
    CFSG.StandardType.E4bLift.ker_e6Isogeny_le_center (F := F) hzker
  have hzmap : z ∈ (Subgroup.center ↥(fixedGroup K σ.toRingHom)).map
      ((minBC e6Data_valid ι).comp (fixedGroup K σ.toRingHom).subtype) := by
    rw [CFSG.StandardType.KG87B.center_minBC_eq_center hn hK σ hσ ι h3]
    exact hzcenter
  obtain ⟨z0, hz0, hz0eq⟩ := Subgroup.mem_map.1 hzmap
  have hiz0 : originalI (K := K) (F := F) (σ := σ) ι t z0 = z := by
    rw [originalI, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hz0eq]
    have hcomm : t * z = z * t := Subgroup.mem_center_iff.1 hzcenter t
    rw [hcomm, mul_inv_cancel_right]
  have hz0ker_mod : ((twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ) z0 :
      ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) = 1 := by
    rw [coe_twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ) z0]
    apply baseChangeGL_injective ι
    change (baseChangeGL (τ := Tag.E6) ι)
        ((e6Isogeny K (z0 : e6Data_valid.minGroup K) :
          ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
      (baseChangeGL (τ := Tag.E6) ι) 1
    rw [← CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_minBC, map_one]
    change ((e6Isogeny F (((minBC e6Data_valid ι).comp
      (fixedGroup K σ.toRingHom).subtype) z0) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) = 1
    rw [hz0eq]
    change ((e6Isogeny F z : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) = 1
    rw [MonoidHom.mem_ker.mp hzker]
    simp
  have hz0ker : z0 ∈ (twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ)).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hz0ker_mod
  have hq0z0 : originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn z0 = 1 := by
    rw [originalQ0_apply]
    rw [MonoidHom.mem_ker.mp hz0ker, map_one]
  refine ⟨u0 * z0, ?_, ?_, ?_⟩
  · rw [map_mul, hiz0]
    rw [hzdef]
    group
    rfl
  · apply originalI_injective (F := F)
    rw [map_pow, map_mul, hiz0, hzdef]
    rw [mul_inv_cancel_left, fixedA2Ahat_pow_three (F := F) hF hω3, map_one]
  · rw [map_mul, hu0, hq0z0, mul_one]


@[expose] abbrev originalN (hker : ψ.ker ≤ Subgroup.center J) : Subgroup J :=
  TableBU.twoPartOf ψ.ker hker (Nat.card J)

theorem originalN_le_ker (hker : ψ.ker ≤ Subgroup.center J) :
    originalN (ψ := ψ) hker ≤ ψ.ker :=
  TableBU.twoPartOf_le ψ.ker hker (Nat.card J)

theorem originalN_le_center (hker : ψ.ker ≤ Subgroup.center J) :
    originalN (ψ := ψ) hker ≤ Subgroup.center J :=
  (originalN_le_ker (ψ := ψ) hker).trans hker

theorem originalN_coprime_three (hker : ψ.ker ≤ Subgroup.center J) :
    Nat.Coprime 3 (Nat.card (originalN (ψ := ψ) hker)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp
    (TableBU.isPGroup_twoPartOf ψ.ker hker (Nat.card J))
  rw [ha]
  exact Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)

@[expose] def originalPi (hker : ψ.ker ≤ Subgroup.center J) :
    J →* J ⧸ originalN (ψ := ψ) hker :=
  QuotientGroup.mk' (originalN (ψ := ψ) hker)

@[expose] def originalPsiBar (hker : ψ.ker ≤ Subgroup.center J) :
    J ⧸ originalN (ψ := ψ) hker →* TwE6Delta.RecipeR K n :=
  QuotientGroup.lift (originalN (ψ := ψ) hker) ψ
    (originalN_le_ker (ψ := ψ) hker)

theorem originalPsiBar_mk (hker : ψ.ker ≤ Subgroup.center J) (j : J) :
    originalPsiBar (ψ := ψ) hker (originalPi (ψ := ψ) hker j) = ψ j :=
  QuotientGroup.lift_mk (originalN (ψ := ψ) hker)
    (originalN_le_ker (ψ := ψ) hker) j

theorem originalPsiBar_ker_le_center (hker : ψ.ker ≤ Subgroup.center J) :
    (originalPsiBar (ψ := ψ) hker).ker ≤
      Subgroup.center (J ⧸ originalN (ψ := ψ) hker) := by
  intro y hy
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (originalN (ψ := ψ) hker) y
  have hz : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, ← originalPsiBar_mk (ψ := ψ) hker z]
    exact hy
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (originalN (ψ := ψ) hker) w
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz) v]

theorem originalH_perfect (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    commutator ↥(fixedGroup K σ.toRingHom) = ⊤ := by
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c :=
    CFSG.SeitzReduction.F4Pilot.involutive_of_natCard_eq hK (hσ_toRingHom hσ)
  have h4 : 4 ≤ Nat.card K :=
    CFSG.SeitzReduction.F4Pilot.four_le_natCard_of_eq hn hK
  exact (CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isPerfect_of_four_le_card
    σ.toRingHom hθ h4).commutator_eq_top

theorem originalN_map_v (hker : ψ.ker ≤ Subgroup.center J) (v : MulAut J)
    (w : MulAut (TwE6Delta.RecipeR K n))
    (hψv : ∀ j, ψ (v j) = w (ψ j)) :
    (originalN (ψ := ψ) hker).map v.toMonoidHom = originalN (ψ := ψ) hker := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ ψ.ker ∧ y ^ 2 ^ Nat.card J = 1 :=
      TableBU.mem_twoPartOf.mp
        (show y ∈ TableBU.twoPartOf ψ.ker hker (Nat.card J) from hy)
    refine TableBU.mem_twoPartOf.mpr ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      change ψ (v y) = 1
      rw [hψv y, hy'.1, map_one]
    · rw [← map_pow, hy'.2, map_one]
  · intro hx
    have hx' : x ∈ ψ.ker ∧ x ^ 2 ^ Nat.card J = 1 :=
      TableBU.mem_twoPartOf.mp
        (show x ∈ TableBU.twoPartOf ψ.ker hker (Nat.card J) from hx)
    have hmem : v.symm x ∈ ψ.ker ∧ (v.symm x) ^ 2 ^ Nat.card J = 1 := by
      refine ⟨?_, ?_⟩
      · apply w.injective
        rw [← hψv (v.symm x), MulEquiv.apply_symm_apply, hx'.1, map_one]
      · apply v.injective
        rw [map_pow, MulEquiv.apply_symm_apply, hx'.2, map_one]
    refine ⟨v.symm x, ?_, ?_⟩
    · exact TableBU.mem_twoPartOf.mpr hmem
    · exact v.apply_symm_apply x

@[expose] def originalVbar (hker : ψ.ker ≤ Subgroup.center J) (v : MulAut J)
    (w : MulAut (TwE6Delta.RecipeR K n))
    (hψv : ∀ j, ψ (v j) = w (ψ j)) :
    J ⧸ originalN (ψ := ψ) hker →* J ⧸ originalN (ψ := ψ) hker :=
  (QuotientGroup.congr (originalN (ψ := ψ) hker) (originalN (ψ := ψ) hker) v
    (originalN_map_v (ψ := ψ) hker v w hψv)).toMonoidHom

theorem originalVbar_mk (hker : ψ.ker ≤ Subgroup.center J) (v : MulAut J)
    (w : MulAut (TwE6Delta.RecipeR K n))
    (hψv : ∀ j, ψ (v j) = w (ψ j)) (j : J) :
    originalVbar (ψ := ψ) hker v w hψv (originalPi (ψ := ψ) hker j) =
      originalPi (ψ := ψ) hker (v j) :=
  QuotientGroup.congr_mk (originalN (ψ := ψ) hker)
    (originalN (ψ := ψ) hker) v (originalN_map_v (ψ := ψ) hker v w hψv) j

theorem originalPsiBar_originalVbar (hker : ψ.ker ≤ Subgroup.center J)
    (v : MulAut J) (w : MulAut (TwE6Delta.RecipeR K n))
    (hψv : ∀ j, ψ (v j) = w (ψ j)) (y : J ⧸ originalN (ψ := ψ) hker) :
    originalPsiBar (ψ := ψ) hker
        (originalVbar (ψ := ψ) hker v w hψv y) =
      w (originalPsiBar (ψ := ψ) hker y) := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (originalN (ψ := ψ) hker) y
  change originalPsiBar (ψ := ψ) hker
      (originalVbar (ψ := ψ) hker v w hψv (originalPi (ψ := ψ) hker j)) =
    w (originalPsiBar (ψ := ψ) hker (originalPi (ψ := ψ) hker j))
  rw [originalVbar_mk, originalPsiBar_mk, originalPsiBar_mk, hψv]


theorem originalI_comp_Phi_eq_conj (hn : 1 ≤ n) (hψ : Function.Surjective ψ)
    {v : MulAut J} {w : MulAut (TwE6Delta.RecipeR K n)}
    (hψv : ∀ j, ψ (v j) = w (ψ j))
    (Xhat : ↥(e6Data_valid.minGroup F))
    {X : ↥(adjointGroup Tag.E6 F)} (hXhat : e6Isogeny F Xhat = X)
    (hmodel : ∀ j, originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t (v j) =
      ((X : ModGL Tag.E6 F) *
        originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t j *
        (X : ModGL Tag.E6 F)⁻¹))
    {Φ : MulAut ↥(fixedGroup K σ.toRingHom)}
    (hΦ : ∀ u, originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn (Φ u) =
      w (originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u)) :
    (originalI (K := K) (F := F) (σ := σ) ι t).comp Φ.toMonoidHom =
      (MulAut.conj Xhat).toMonoidHom.comp
        (originalI (K := K) (F := F) (σ := σ) ι t) := by
  haveI : Group.IsPerfect ↥(fixedGroup K σ.toRingHom) :=
    ⟨originalH_perfect (K := K) (σ := σ) hn hK hσ⟩
  apply CFSG.ClassicalInvolution.ModelFacts.OrthAut.eq_of_inv_mul_mem_center
  intro u
  apply CFSG.StandardType.E4bLift.ker_e6Isogeny_le_center (F := F)
  rw [MonoidHom.mem_ker]
  obtain ⟨j, hj⟩ := hψ (originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u)
  have hmj : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t j =
      ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) :=
    originalM_eq_pi_originalI (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
      (hK := hK) (hσ := hσ) (ι := ι) (t := t) hn u hj
  have hvj : ψ (v j) = originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn (Φ u) := by
    rw [hψv j, hj, hΦ u]
  have hmvj : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ι t (v j) =
      ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t (Φ u)) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) :=
    originalM_eq_pi_originalI (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
      (hK := hK) (hσ := hσ) (ι := ι) (t := t) hn (Φ u) hvj
  have hconj : ((e6Isogeny F ((MulAut.conj Xhat) (originalI (K := K) (F := F) (σ := σ) ι t u)) :
      ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      ((X : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
        ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u) :
          ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
      ((X : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)⁻¹ := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hXhat]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have htarget : ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t (Φ u)) :
      ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      ((X : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
        ((e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u) :
          ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
      ((X : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)⁻¹ := by
    rw [← hmvj, hmodel j, hmj]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [map_mul, map_inv]
  have hconj' : e6Isogeny F ((MulAut.conj Xhat) (originalI (K := K) (F := F) (σ := σ) ι t u)) =
      X * e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u) * X⁻¹ :=
    Subtype.ext hconj
  have htarget' : e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t (Φ u)) =
      X * e6Isogeny F (originalI (K := K) (F := F) (σ := σ) ι t u) * X⁻¹ :=
    Subtype.ext htarget
  rw [hconj', htarget']
  group

theorem originalVbar_comp_alpha_eq (hn : 1 ≤ n)
    {hker : ψ.ker ≤ Subgroup.center J}
    {α : ↥(fixedGroup K σ.toRingHom) →*
      J ⧸ originalN (ψ := ψ) hker}
    (hαq : ∀ u, originalPsiBar (ψ := ψ) hker (α u) =
      originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u)
    {v : MulAut J} {w : MulAut (TwE6Delta.RecipeR K n)}
    (hψv : ∀ j, ψ (v j) = w (ψ j))
    {Φ : MulAut ↥(fixedGroup K σ.toRingHom)}
    (hΦ : ∀ u, originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn (Φ u) =
      w (originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u)) :
    (originalVbar (ψ := ψ) hker v w hψv).comp α =
      α.comp Φ.toMonoidHom := by
  haveI : Group.IsPerfect ↥(fixedGroup K σ.toRingHom) :=
    ⟨originalH_perfect (K := K) (σ := σ) hn hK hσ⟩
  apply CFSG.ClassicalInvolution.ModelFacts.OrthAut.eq_of_inv_mul_mem_center
  intro u
  apply originalPsiBar_ker_le_center (ψ := ψ) hker
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [originalPsiBar_originalVbar, hαq u]
  have hαΦ : originalPsiBar (ψ := ψ) hker (α (Φ u)) =
      w (originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u) := by
    rw [hαq (Φ u), hΦ u]
  rw [hαΦ]
  group

theorem originalQ0_surjective (hn : 1 ≤ n) :
    Function.Surjective (originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn) :=
  ε.surjective.comp
    (twistedIsogenyC_surjective hn hK σ.toRingHom (hσ_toRingHom hσ))

theorem originalQ0_ker_le_center (hn : 1 ≤ n) :
    (originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn).ker ≤
      Subgroup.center ↥(fixedGroup K σ.toRingHom) := by
  intro x hx
  rw [← ker_twistedIsogenyC hn hK σ.toRingHom (hσ_toRingHom hσ)]
  rw [MonoidHom.mem_ker]
  exact (map_eq_one_iff ε ε.injective).1 (by
    simpa only [originalQ0_apply] using MonoidHom.mem_ker.mp hx)

theorem originalPsiBar_eq_quotientLift (hker : ψ.ker ≤ Subgroup.center J) :
    originalPsiBar (ψ := ψ) hker =
      QuotientGroup.lift (originalN (ψ := ψ) hker) ψ
        (TableBU.twoPartOf_le ψ.ker hker (Nat.card J)) := by
  apply MonoidHom.ext
  intro y
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (originalN (ψ := ψ) hker) y
  change originalPsiBar (ψ := ψ) hker (originalPi (ψ := ψ) hker j) =
    QuotientGroup.lift (originalN (ψ := ψ) hker) ψ
      (TableBU.twoPartOf_le ψ.ker hker (Nat.card J))
      (j : J ⧸ originalN (ψ := ψ) hker)
  rw [originalPsiBar_mk, QuotientGroup.lift_mk]

theorem exists_originalCube_covariance (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
    (hperf : commutator J = ⊤)
    (hF : 4 < Nat.card F)
    (h3 : 3 ∣ 2 ^ n + 1) {ζ ω : Fˣ} (hζ : ζ ^ 3 = ω)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {d : J}
    (hd : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) (ι := ι) (t := t) d =
      ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)) :
    ∃ c : J, c ^ 3 = 1 ∧ c ≠ 1 ∧ ψ c = ψ d ∧
      ∀ (v : MulAut J) (w : MulAut (TwE6Delta.RecipeR K n)),
        (∀ j, ψ (v j) = w (ψ j)) →
        ∀ (X : ↥(adjointGroup Tag.E6 F)),
          (∀ j, originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
              (ι := ι) (t := t) (v j) =
            (X : ModGL Tag.E6 F) *
              originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
                (ι := ι) (t := t) j *
              (X : ModGL Tag.E6 F)⁻¹) →
          ∀ (B : SL(3, F)),
            fixedA2AdjRho (F := F) B =
              X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ζ) * X⁻¹ →
            ∀ (m : ℤ),
              X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) * X⁻¹ =
                (fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω)) ^ m →
              v c = c ^ m := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let q0 : ↥(fixedGroup K σ.toRingHom) →* TwE6Delta.RecipeR K n :=
    originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn
  have hq0s : Function.Surjective q0 :=
    originalQ0_surjective (K := K) (σ := σ) (ε := ε) hK hσ hn
  have hq0k : q0.ker ≤ Subgroup.center ↥(fixedGroup K σ.toRingHom) :=
    originalQ0_ker_le_center (K := K) (σ := σ) (ε := ε) hK hσ hn
  obtain ⟨u0, hu0⟩ := hq0s (ψ d)
  obtain ⟨u, hiu, hu3, hq0u⟩ :=
    exists_u_originalI_eq_ahat (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
      (hK := hK) (hσ := hσ) (ι := ι) (t := t) hn hF h3 hω3 hω1 hd u0 hu0
  obtain ⟨α, hαs, hαlift, hαk⟩ :=
    CFSG.StandardType.KG87B.exists_surjective_fixedGroup_mod_twoPart
      (n := n) hn hK σ hσ ε hψ hker hperf
  have hψbar_lift : originalPsiBar (ψ := ψ) hker =
      QuotientGroup.lift (originalN (ψ := ψ) hker) ψ
        (TableBU.twoPartOf_le ψ.ker hker (Nat.card J)) :=
    originalPsiBar_eq_quotientLift (ψ := ψ) hker
  have hαq : ∀ u, originalPsiBar (ψ := ψ) hker (α u) =
      originalQ0 (K := K) (σ := σ) (ε := ε) hK hσ hn u := by
    intro u
    rw [hψbar_lift, hαlift u, originalQ0_apply]
  let cbar : J ⧸ originalN (ψ := ψ) hker := α u
  let p : J →* J ⧸ originalN (ψ := ψ) hker := originalPi (ψ := ψ) hker
  let c : J := CFSG.LieType.CentralExt.pLift 3 p cbar
  have hp_ker : p.ker = originalN (ψ := ψ) hker := by
    dsimp [p]
    rw [originalPi, QuotientGroup.ker_mk']
  have hpcen : p.ker ≤ Subgroup.center J := by
    rw [hp_ker]
    exact originalN_le_center (ψ := ψ) hker
  have hnot3 : ¬ 3 ∣ Nat.card p.ker := by
    rw [hp_ker]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mp
      (originalN_coprime_three (ψ := ψ) hker)
  have hcbar3 : cbar ^ 3 = 1 := by
    dsimp [cbar]
    calc (α u) ^ 3 = α (u ^ 3) := (map_pow α u 3).symm
      _ = α 1 := by rw [hu3]
      _ = 1 := map_one α
  have hcbar_pe : ∃ k : ℕ, orderOf cbar = 3 ^ k :=
    CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one
      (p := 3) (n := 1) (by simpa using hcbar3)
  have hpc : p c = cbar := by
    dsimp [c]
    exact CFSG.LieType.CentralExt.map_pLift (p := 3) (π := p)
      (QuotientGroup.mk'_surjective (originalN (ψ := ψ) hker)) hnot3 hcbar_pe
  have hc3 : c ^ 3 = 1 := by
    have h := CFSG.LieType.CentralExt.pLift_pow (p := 3) (π := p)
      (QuotientGroup.mk'_surjective (originalN (ψ := ψ) hker)) hpcen hnot3 hcbar_pe 3
    rw [hcbar3] at h
    rw [CFSG.LieType.CentralExt.pLift_one (p := 3) (π := p) hpcen hnot3] at h
    exact h.symm
  have hψc : ψ c = ψ d := by
    rw [← originalPsiBar_mk (ψ := ψ) hker c]
    rw [show originalPi (ψ := ψ) hker c = cbar from hpc]
    dsimp [cbar]
    exact (hαq u).trans hq0u
  have hcne : c ≠ 1 := by
    intro hc1
    have hψd1 : ψ d = 1 := by rw [← hψc, hc1, map_one]
    have hMd1 : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
        (ι := ι) (t := t) d = 1 := by
      simp [originalM_eq_comp_originalMR, hψd1]
    have hscalar1 : fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) = 1 := by
      apply Subtype.ext
      change ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) = (1 : ModGL Tag.E6 F)
      rw [← hd, hMd1]
    exact fixedA2Scalar_ne_one (F := F) hω1
      (fixedA2AdjRho_injective (F := F) (by simpa using hscalar1))
  refine ⟨c, hc3, hcne, hψc, ?_⟩
  intro v w hψv X hXmodel B hB m hXω
  obtain ⟨Xhat, hXhat⟩ := e6Isogeny_surjective F X
  obtain ⟨Φ, hΦ⟩ := CFSG.StandardType.KG87B.exists_lift_fixedGroup
    (n := n) (K := K) hn hK σ hσ (q := q0) hq0s hq0k w
  have hcomp := originalI_comp_Phi_eq_conj (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
    (hK := hK) (hσ := hσ) (ι := ι) (t := t) hn hψ hψv Xhat hXhat hXmodel hΦ
  have hIu : originalI (K := K) (F := F) (σ := σ) (ι := ι) (t := t) (Φ u) =
      Xhat * originalI (K := K) (F := F) (σ := σ) (ι := ι) (t := t) u * Xhat⁻¹ := by
    have h := DFunLike.congr_fun hcomp u
    change originalI (K := K) (F := F) (σ := σ) (ι := ι) (t := t) (Φ u) =
      (MulAut.conj Xhat)
        (originalI (K := K) (F := F) (σ := σ) (ι := ι) (t := t) u) at h
    simpa [MulAut.conj_apply] using h
  have hIu' : originalI (K := K) (F := F) (σ := σ) (ι := ι) (t := t) (Φ u) =
      Xhat * fixedA2Ahat (F := F) hF ω * Xhat⁻¹ := by
    rw [hIu, hiu]
  have hcube := fixedA2Ahat_conj_zpow_of_cube_preimage (F := F) hF Xhat hXhat
    ζ ω hζ B hB m hXω
  have hiPhi : originalI (K := K) (F := F) (σ := σ) (ι := ι) (t := t) (Φ u) =
      originalI (K := K) (F := F) (σ := σ) (ι := ι) (t := t) (u ^ m) := by
    rw [hIu', hcube, map_zpow, hiu]
  have hPhiu : Φ u = u ^ m :=
    originalI_injective (K := K) (F := F) (σ := σ) (ι := ι) (t := t) hiPhi
  have hvbar : originalVbar (ψ := ψ) hker v w hψv (α u) = (α u) ^ m := by
    have hcomp2 := originalVbar_comp_alpha_eq (K := K) (σ := σ) (ε := ε) (ψ := ψ)
      (hK := hK) (hσ := hσ) hn (hker := hker) hαq hψv hΦ
    have h := DFunLike.congr_fun hcomp2 u
    change originalVbar (ψ := ψ) hker v w hψv (α u) = α (Φ u) at h
    rw [hPhiu, map_zpow] at h
    exact h
  have hpow : p (v c) = p (c ^ m) := by
    calc p (v c) = originalVbar (ψ := ψ) hker v w hψv (p c) :=
          (originalVbar_mk (ψ := ψ) hker v w hψv c).symm
      _ = originalVbar (ψ := ψ) hker v w hψv (α u) := by rw [hpc]
      _ = (α u) ^ m := hvbar
      _ = (p c) ^ m := by rw [hpc]
      _ = p (c ^ m) := (map_zpow p c m).symm
  have hvc_pe : ∃ k : ℕ, orderOf (v c) = 3 ^ k :=
    CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one
      (p := 3) (n := 1) (by
        calc (v c) ^ 3 = v (c ^ 3) := (map_pow v c 3).symm
          _ = v 1 := by rw [hc3]
          _ = 1 := map_one v)
  have hcm_pe : ∃ k : ℕ, orderOf (c ^ m) = 3 ^ k :=
    CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one
      (p := 3) (n := 1) (by
        calc (c ^ m) ^ 3 = (c ^ m) ^ (3 : ℤ) := (zpow_natCast (c ^ m) 3).symm
          _ = c ^ (m * 3) := (zpow_mul c m 3).symm
          _ = c ^ (3 * m) := by rw [mul_comm]
          _ = (c ^ 3) ^ m := zpow_mul c 3 m
          _ = 1 := by simp [hc3])
  exact CFSG.LieType.CentralExt.eq_of_pElement (p := 3) (π := p)
    hpcen hnot3 hpow hvc_pe hcm_pe

theorem exists_fixedA2Scalar_preimage_of_torus_normalizer
    {Ω : Type} [Field Ω] (κ : F →+* Ω) (σF : Ω →+* Ω)
    (hσF : ∀ b : Ω, σF b = b ^ Nat.card F)
    {X : ↥(adjointGroup Tag.E6 F)} {ζ : Fˣ}
    (hX : baseChangeGL (τ := Tag.E6) κ (X : ModGL Tag.E6 F) ∈
      Subgroup.normalizer (CFSG.StandardType.TwE6E4bTorus.fixedA2Torus Ω)) :
    ∃ B : SL(3, F),
      fixedA2AdjRho (F := F) B =
        X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ζ) * X⁻¹ := by
  classical
  let T : ModGL Tag.E6 Ω := baseChangeGL (τ := Tag.E6) κ (X : ModGL Tag.E6 F)
  let S : ModGL Tag.E6 Ω :=
    fixedA2Rho Ω (Matrix.SpecialLinearGroup.map κ (fixedA2Scalar (F := F) ζ))
  have hmap : Matrix.SpecialLinearGroup.map κ (fixedA2Scalar (F := F) ζ) =
      diagSL3 (Units.map κ ζ) (Units.map κ ((ζ : Fˣ) ^ 2)) := by
    rw [fixedA2Scalar_eq_diagSL3 (F := F) ζ]
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [diagSL3, Matrix.map_apply, Units.coe_map]
  have hS : S ∈ CFSG.StandardType.TwE6E4bTorus.fixedA2Torus Ω := by
    refine ⟨(Units.map κ ζ, Units.map κ ((ζ : Fˣ) ^ 2)), ?_⟩
    dsimp [S]
    rw [hmap]
  have hZS : T * S * T⁻¹ ∈ CFSG.StandardType.TwE6E4bTorus.fixedA2Torus Ω :=
    ((Subgroup.mem_set_normalizer_iff.mp hX) S).mp hS
  obtain ⟨q, hq⟩ := hZS
  change fixedA2Rho Ω (diagSL3 q.1 q.2) = T * S * T⁻¹ at hq
  let Z : ModGL Tag.E6 F :=
    (X : ModGL Tag.E6 F) * fixedA2Rho F (fixedA2Scalar (F := F) ζ) *
      (X : ModGL Tag.E6 F)⁻¹
  have hbase : baseChangeGL (τ := Tag.E6) κ Z =
      fixedA2Rho Ω (diagSL3 q.1 q.2) := by
    have h : baseChangeGL (τ := Tag.E6) κ Z = T * S * T⁻¹ := by
      dsimp [Z, T, S]
      rw [map_mul, map_mul, map_inv, baseChangeGL_fixedA2Rho]
    rw [h, hq]
  obtain ⟨A, hA, -⟩ := exists_preimage_fixedA2Rho_of_fixedField
    (K := F) (L := Ω) κ σF (fixedField_iff_frobenius_eq κ σF hσF)
    Z (diagSL3 q.1 q.2) hbase
  refine ⟨A, ?_⟩
  apply Subtype.ext
  rw [fixedA2AdjRho_coe, hA]
  rfl

theorem exists_originalCube_covariance_of_normalizer (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
    (hperf : commutator J = ⊤)
    (hF : 4 < Nat.card F)
    (h3 : 3 ∣ 2 ^ n + 1) {ζ ω : Fˣ} (hζ : ζ ^ 3 = ω)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {d : J}
    (hd : originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) (ι := ι) (t := t) d =
      ((fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :
        ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F))
    {Ω : Type} [Field Ω] (κ : F →+* Ω) (σF : Ω →+* Ω)
    (hσF : ∀ b : Ω, σF b = b ^ Nat.card F) :
    ∃ c : J, c ^ 3 = 1 ∧ c ≠ 1 ∧ ψ c = ψ d ∧
      ∀ (v : MulAut J) (w : MulAut (TwE6Delta.RecipeR K n)),
        (∀ j, ψ (v j) = w (ψ j)) →
        ∀ (X : ↥(adjointGroup Tag.E6 F)),
          (∀ j, originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
              (ι := ι) (t := t) (v j) =
            (X : ModGL Tag.E6 F) *
              originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
                (ι := ι) (t := t) j *
              (X : ModGL Tag.E6 F)⁻¹) →
          (baseChangeGL (τ := Tag.E6) κ (X : ModGL Tag.E6 F) ∈
            Subgroup.normalizer (CFSG.StandardType.TwE6E4bTorus.fixedA2Torus Ω)) →
          ∀ (m : ℤ),
            X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) * X⁻¹ =
              (fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω)) ^ m →
            v c = c ^ m := by
  obtain ⟨c, hc3, hcne, hψc, hcov⟩ :=
    exists_originalCube_covariance (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
      (ι := ι) (t := t) hn hK hσ hψ hker hperf hF h3 hζ hω3 hω1 hd
  refine ⟨c, hc3, hcne, hψc, ?_⟩
  intro v w hψv X hXmodel hXnorm m hXω
  obtain ⟨B, hB⟩ := exists_fixedA2Scalar_preimage_of_torus_normalizer
    (F := F) κ σF hσF (X := X) (ζ := ζ) hXnorm
  exact hcov v w hψv X hXmodel B hB m hXω

end CFSG.StandardType.E4bOriginalLift
