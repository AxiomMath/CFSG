module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.Quasithin.H13.VolIAltCoverG2
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.SteinbergCBI16Faithful
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Eight
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtIrr
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQSL2RootCommutator
import CFSG.Quasithin.Vol2.Ch11SecOE2D
import CFSG.Quasithin.Vol2.Ch12Sec2GlueHatA6
import CFSG.Quasithin.Background.JonesParshallCurtisClassify
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import Certificates.Certificate17000
public import Certificates.Certificate17001
public import Certificates.Certificate17022
public import Certificates.Certificate17026
public import Certificates.Certificate17028
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.Quasithin.Background.B5Inputs
public import CFSG.Quasithin.Background.JonesParshallCurtisWeyl
public import CFSG.Quasithin.Background.JonesParshallG2H1
public import CFSG.Quasithin.Background.JonesParshallSp4Two
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Rep
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type} [CommGroup W]

theorem s16nt_row_g2
    [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hUc : commSub U L = U) (hZ : Z ≤ fixV L) (h : G2NaturalDerived L U Z 1) :
    3 * rk ↥Z ≤ rk ↥U := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := h
  letI := hKf
  letI := hKfin
  have hK2 : Nat.card K = 2 := by rw [hKcard, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKf2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hKf2, pow_one])
  have hmod : Nat.card (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Mod = 2 ^ 6 := by
    simpa using CFSG.Quasithin.H13.VolI.card_zornQSec (K := K) hK2
  have hD : S16BoundCover (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) 1 := by
    intro V _ _ hV2 H Z' hZ' hcomm hreal'
    have hder : G2NaturalDerived H ⊤ Z' 1 := ⟨K, hKf, hKfin, hKcard, hreal'⟩
    rcases CFSG.Quasithin.H13.VolI.g2NaturalCover_holds V hV2 H Z' hZ' hcomm hder with
      h1 | ⟨h2, -⟩
    · rw [h1, Subgroup.card_bot]
      norm_num
    · exact le_of_eq h2
  exact s16nt_goal_of_model hD (by norm_num) hmod hW2 hUc hZ hreal

private noncomputable def w183_quotBotEquiv {M : Type*} [CommGroup M] (S K : Subgroup M)
    (hK : K = ⊥) : (↥S ⧸ K.subgroupOf S) ≃* ↥S :=
  (QuotientGroup.quotientMulEquivOfEq (by rw [hK, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

private noncomputable def w183_natQuotEquiv (D : FFModel) (hs : D.sec = ⊤) (hk : D.ker = ⊥) :
    D.Mod ≃* D.Amb :=
  (w183_quotBotEquiv D.sec D.ker hk).trans
    ((MulEquiv.subgroupCongr hs).trans Subgroup.topEquiv)

private theorem w183_natQuotEquiv_mk (D : FFModel) (hs : D.sec = ⊤) (hk : D.ker = ⊥)
    (m : ↥D.sec) : w183_natQuotEquiv D hs hk (QuotientGroup.mk m) = (m : D.Amb) := rfl

private noncomputable def w183_natAut {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (γ : Matrix.GeneralLinearGroup ι K) : MulAut (Multiplicative (ι → K)) where
  toFun x := Multiplicative.ofAdd
    (Matrix.mulVec (γ : Matrix ι ι K) (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd
    (Matrix.mulVec ((γ⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)
      (Multiplicative.toAdd x))
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel]
    simp
  right_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  map_mul' x y := by simp [Matrix.mulVec_add]

private noncomputable def w183_natActHomGL {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] : Matrix.GeneralLinearGroup ι K →* MulAut (Multiplicative (ι → K)) where
  toFun := w183_natAut
  map_one' := by
    ext x
    simp [w183_natAut]
  map_mul' γ δ := by
    ext x
    simp [w183_natAut, Matrix.mulVec_mulVec, Units.val_mul]

private noncomputable def w183_natActHom {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    ↥Γ →* MulAut (Multiplicative (ι → K)) :=
  w183_natActHomGL.comp Γ.subtype

private theorem w183_isIrreducible_of_forall_submodule {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V] (ρ : Representation (ZMod 2) G V)
    (h : ∀ U : Submodule (ZMod 2) V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ρ.IsIrreducible := by
  haveI : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⊥, ⊤, fun h' => ?_⟩
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial V)
    have h1 : (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule :=
      congrArg Subrepresentation.toSubmodule h'
    have h2 : (⊥ : Submodule (ZMod 2) V) = ⊤ := h1
    have h3 : x - y ∈ (⊥ : Submodule (ZMod 2) V) := h2 ▸ Submodule.mem_top
    exact hxy (sub_eq_zero.mp ((Submodule.mem_bot (ZMod 2)).mp h3))
  refine ⟨fun Z => ?_⟩
  rcases h Z.toSubmodule (fun g u hu => Z.apply_mem_toSubmodule g hu) with h1 | h1
  · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h1)

theorem s16nt_row_a7 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} (hUc : commSub U L = U) (hZ : Z ≤ fixV L) (h : A7Four L U Z) :
    3 * rk ↥Z ≤ rk ↥U := by
  obtain ⟨α, hreal⟩ := h
  have hDact : (FFModel.a7Four α).IsActionModel := FFModel.a7Four_isActionModel α
  let e : (FFModel.a7Four α).Mod ≃* Multiplicative (Fin 4 → ZMod 2) :=
    w183_natQuotEquiv (FFModel.a7Four α) rfl rfl
  let ρ : Representation (ZMod 2) ↥(alternatingGroup (Fin 7)) (Fin 4 → ZMod 2) :=
    { toFun := fun γ => Matrix.mulVecLin
        (((α (altLift7 γ) : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)))
      map_one' := by
        simp only [map_one]
        ext v i
        simp [Matrix.mulVecLin_apply]
      map_mul' := fun γ δ => by
        simp only [map_mul]
        ext v i
        simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] }
  have hlift_inj : Function.Injective (altLift7 : ↥(alternatingGroup (Fin 7)) →*
      ↥(alternatingGroup (Fin 8))) := by
    intro a b hab
    apply Subtype.ext
    apply Equiv.Perm.viaEmbeddingHom_injective (Fin.castSuccEmb : Fin 7 ↪ Fin 8)
    exact congrArg (fun x : ↥(alternatingGroup (Fin 8)) => (x : Equiv.Perm (Fin 8))) hab
  have he : ∀ m : ↥(FFModel.a7Four α).sec,
      e (QuotientGroup.mk m) = (m : (FFModel.a7Four α).Amb) :=
    fun m => w183_natQuotEquiv_mk (FFModel.a7Four α) rfl rfl m
  have hρ : ∀ (γ : (FFModel.a7Four α).Gam) (q : (FFModel.a7Four α).Mod),
      e (hDact.modAct γ q) = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd (e q))) := by
    intro γ q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hDact.modAct_apply, hDact.modEnd_mk]
    simp only [he]
    rfl
  have hρinj : Function.Injective ρ := by
    intro γ δ hγδ
    have hmat : (((α (altLift7 γ) : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2))) =
        (((α (altLift7 δ) : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2))) := by
      ext i j
      have h := congrArg (fun f : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) =>
        f (Pi.single j 1) i) hγδ
      simpa [ρ, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h
    exact hlift_inj (α.injective (Units.ext hmat))
  have hdinj : Function.Injective (Representation.dual ρ) := by
    intro γ δ hγδ
    have h1 : ρ γ⁻¹ = ρ δ⁻¹ := by
      have h2 : (ρ γ⁻¹).dualMap = (ρ δ⁻¹).dualMap := by
        simpa only [LinearMap.dualMap, Representation.dual_apply] using hγδ
      have h3 : (ρ γ⁻¹).dualMap.dualMap = (ρ δ⁻¹).dualMap.dualMap :=
        congrArg LinearMap.dualMap h2
      exact (Module.dualMap_dualMap_eq_iff (R := ZMod 2) (M := Fin 4 → ZMod 2)
        (M' := Fin 4 → ZMod 2)).mp h3
    exact inv_inj.mp (hρinj h1)
  have hdim : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) = 4 := by
    rw [Subspace.dual_finrank_eq (K := ZMod 2) (V := Fin 4 → ZMod 2),
      Module.finrank_fin_fun (ZMod 2)]
  have hH1 : Module.finrank (ZMod 2)
      (CFSG.Quasithin.JonesParshall.H1 (Representation.dual ρ)) ≤ 0 := by
    have h := CFSG.Quasithin.SteinbergCB.I16.finrank_H1_faithful_alt7
      (ρ := Representation.dual ρ) (MulEquiv.refl (FFModel.a7Four α).Gam) hdinj hdim
    simp [h]
  have hDcov : S16BoundCover (FFModel.a7Four α) 0 := by
    haveI : Finite (FFModel.a7Four α).Gam := by
      change Finite ↥(alternatingGroup (Fin 7))
      infer_instance
    exact s16nt_cover_of_h1_model hDact e ρ hρ hH1
  have hmod : Nat.card (FFModel.a7Four α).Mod = 2 ^ 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin 4)]
    norm_num [Nat.card_zmod, Fintype.card_fin]
  exact s16nt_goal_of_model hDcov (by norm_num) hmod hW2 hUc hZ hreal

theorem w183_cover_nat_tripleA6Six {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K))
    (hdet : ∀ g ∈ Γ₀,
      (((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det = 1)
    (hhat : IsHat ↥Γ₀ ↥(alternatingGroup (Fin 6)))
    (hcen : ∀ g ∈ Subgroup.center ↥Γ₀, ∃ c : K,
      (((g : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    S16BoundCover (FFModel.nat Γ₀) 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  refine s16nt_cover_of_h1 (Γ := Γ₀) (c := 0) ?_
  have hrep : ∀ (g : ↥Γ₀) (w : Multiplicative (Fin 3 → K)),
      w183_natActHom Γ₀ g w =
        Multiplicative.ofAdd ((s16ntNatRep Γ₀ g) (Multiplicative.toAdd w)) := by
    intro g w
    simp [w183_natActHom, w183_natActHomGL, w183_natAut, s16ntNatRep, Matrix.mulVecLin]
  let H : Subgroup (MulAut (Multiplicative (Fin 3 → K))) := (w183_natActHom Γ₀).range
  have hφinj : Function.Injective (w183_natActHom Γ₀) := by
    intro g h hgh
    refine Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.mpr fun v => ?_))
    have h1 : (s16ntNatRep Γ₀ g) v = (s16ntNatRep Γ₀ h) v :=
      Multiplicative.ofAdd.injective (by
        have h2 := congrArg (fun F : MulAut (Multiplicative (Fin 3 → K)) =>
          F (Multiplicative.ofAdd v)) hgh
        simpa [hrep] using h2)
    simpa [s16ntNatRep, Matrix.mulVecLin] using h1
  have eH : ↥Γ₀ ≃* ↥H := MonoidHom.ofInjective hφinj
  obtain ⟨hQ, hcard, hquot⟩ := hhat
  haveI : Group.IsPerfect ↥Γ₀ := by
    first | exact hQ.1 | exact Group.isPerfect_def.mpr hQ.1
  have hperf : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := (eH : ↥Γ₀ →* ↥H)) eH.surjective
  have hcenter : Nat.card (Subgroup.center ↥H) = 3 := by
    rw [← Subgroup.map_center_eq (eH : ↥Γ₀ ≃* ↥H),
      Subgroup.card_map_of_injective (f := (eH : ↥Γ₀ →* ↥H)) eH.injective, hcard]
  have hcenterMap : (Subgroup.center ↥H).map (eH.symm : ↥H →* ↥Γ₀) =
      Subgroup.center ↥Γ₀ :=
    Subgroup.map_center_eq (eH.symm : ↥H ≃* ↥Γ₀)
  obtain ⟨hqhat⟩ := hquot
  have hquotH : Nonempty (↥H ⧸ Subgroup.center ↥H ≃* ↥(alternatingGroup (Fin 6))) :=
    ⟨(QuotientGroup.congr (Subgroup.center ↥H) (Subgroup.center ↥Γ₀)
      (eH.symm : ↥H ≃* ↥Γ₀) hcenterMap).trans hqhat⟩
  have hV2 : ∀ v : Multiplicative (Fin 3 → K), v ^ 2 = 1 := by
    have h2 : ∀ x : Fin 3 → K, x + x = 0 := fun x => by
      ext i
      exact CharTwo.add_self_eq_zero (x i)
    intro v
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact h2 _
  have hVcard : Nat.card (Multiplicative (Fin 3 → K)) = 2 ^ 6 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hK,
      Nat.card_eq_fintype_card (α := Fin 3)]
    norm_num
  obtain ⟨-, hsubirr⟩ := CFSG.Quasithin.H13.hatA6SixIrreducible
    (Multiplicative (Fin 3 → K)) hV2 hVcard H hperf hcenter hquotH
  have hsubmod : ∀ U : Submodule (ZMod 2) (Fin 3 → K),
      (∀ g, ∀ v ∈ U, (s16ntNatRep Γ₀) g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hWinv : ∀ h ∈ H, ∀ w ∈ U.toAddSubgroup.toSubgroup,
        (h : MulAut (Multiplicative (Fin 3 → K))) w ∈ U.toAddSubgroup.toSubgroup := by
      intro h hh w hw
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hh
      rw [Multiplicative.mem_toSubgroup] at hw ⊢
      rw [hrep]
      simpa using hU g (Multiplicative.toAdd w) hw
    rcases hsubirr U.toAddSubgroup.toSubgroup hWinv with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hmem : Multiplicative.ofAdd v ∈ U.toAddSubgroup.toSubgroup := by
        rw [Multiplicative.mem_toSubgroup]
        simpa using hv
      rw [hbot] at hmem
      exact Multiplicative.ofAdd.injective (by simpa using hmem)
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hmem : Multiplicative.ofAdd v ∈ U.toAddSubgroup.toSubgroup := by
        rw [htop]; trivial
      rw [Multiplicative.mem_toSubgroup] at hmem
      simpa using hmem
  have hρirr : (s16ntNatRep Γ₀).IsIrreducible :=
    w183_isIrreducible_of_forall_submodule (s16ntNatRep Γ₀) hsubmod
  have hρinj : Function.Injective (s16ntNatRep Γ₀) := by
    intro g h hgh
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    have h1 : (s16ntNatRep Γ₀ g) v = (s16ntNatRep Γ₀ h) v :=
      congrArg (fun f : (Fin 3 → K) →ₗ[ZMod 2] (Fin 3 → K) => f v) hgh
    simpa [s16ntNatRep, Matrix.mulVecLin] using h1
  have hdinj : Function.Injective (Representation.dual (s16ntNatRep Γ₀)) := by
    intro g h hgh
    have h1 : (s16ntNatRep Γ₀) g⁻¹ = (s16ntNatRep Γ₀) h⁻¹ := by
      have h2 : ((s16ntNatRep Γ₀) g⁻¹).dualMap =
          ((s16ntNatRep Γ₀) h⁻¹).dualMap := by
        simpa only [LinearMap.dualMap, Representation.dual_apply] using hgh
      have h3 : ((s16ntNatRep Γ₀) g⁻¹).dualMap.dualMap =
          ((s16ntNatRep Γ₀) h⁻¹).dualMap.dualMap :=
        congrArg LinearMap.dualMap h2
      exact (Module.dualMap_dualMap_eq_iff (R := ZMod 2) (M := Fin 3 → K)
        (M' := Fin 3 → K)).mp h3
    exact inv_inj.mp (hρinj h1)
  have hdimV : Module.finrank (ZMod 2) (Fin 3 → K) = 6 := by
    haveI : Module.Finite (ZMod 2) (Fin 3 → K) := Module.Finite.of_finite
    have h1 : Nat.card (Fin 3 → K) = 2 ^ Module.finrank (ZMod 2) (Fin 3 → K) := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 3 → K)
      rwa [Nat.card_zmod] at h
    have hcard : Nat.card (Fin 3 → K) = 2 ^ 6 := by
      rw [Nat.card_fun, hK, Nat.card_eq_fintype_card (α := Fin 3)]
      norm_num
    have h2 : 2 ^ Module.finrank (ZMod 2) (Fin 3 → K) = 2 ^ 6 := by
      rw [← h1]; exact hcard
    exact Nat.pow_right_injective (le_refl 2) h2
  have hdim6 : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → K)) = 6 := by
    rw [Subspace.dual_finrank_eq (K := ZMod 2) (V := Fin 3 → K)]
    exact hdimV
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (Subgroup.center ↥Γ₀) := isCyclic_of_prime_card hcard
  haveI : IsCyclic (Multiplicative (ZMod 3)) := inferInstance
  let e : Subgroup.center ↥Γ₀ ≃* Multiplicative (ZMod 3) :=
    mulEquivOfCyclicCardEq (by rw [hcard]; exact (Nat.card_zmod 3).symm)
  have hdualirr : (Representation.dual (s16ntNatRep Γ₀)).IsIrreducible :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ.isIrreducible_dual
      (s16ntNatRep Γ₀) hρirr
  exact le_of_eq (CFSG.Quasithin.SteinbergCB.I16.finrank_H1_faithful_center e hdinj
    hdualirr (by rw [hdim6]; norm_num))

theorem s16nt_row_a6 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} (hUc : commSub U L = U) (hZ : Z ≤ fixV L) (h : TripleA6Six L U Z) :
    3 * rk ↥Z ≤ rk ↥U := by
  obtain ⟨K, hKf, hKfin, Γ₀, hKcard, hdet, hhat, hcen, hreal⟩ := h
  letI := hKf
  letI := hKfin
  have hcov : S16BoundCover (FFModel.nat Γ₀) 0 :=
    w183_cover_nat_tripleA6Six hKcard Γ₀ hdet hhat hcen
  have hmod : Nat.card (FFModel.nat Γ₀).Mod = 2 ^ 6 := by
    rw [s16nt_card_natMod, hKcard]
    norm_num
  exact s16nt_goal_of_model hcov (by norm_num) hmod hW2 hUc hZ hreal

theorem s16nt_row_sp6 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hirr : commSub ⊤ L ∈ irrSet L)
    (h : IsSpn ↥L 6 1 ∧ E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 8) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hSpn, hdim8⟩ := h
  have hU0 : commSub ⊤ L ≠ ⊥ := by
    intro hbot
    have hZ : commSub ⊤ L ⊓ fixV L = commSub ⊤ L := by simp [hbot]
    have hlt := hirr.2.1
    rw [hZ] at hlt
    exact (lt_irrefl _) hlt
  rcases rSp6SmallMod_holds (show S16SmSpinH1 from finrank_H1_irreducible_eight) W hW2 L
    (commSub ⊤ L) hSpn hU0 hirr.1 (le_of_eq hdim8) with ⟨-, hZbot, -⟩ | ⟨hq6, -⟩
  · rw [hZbot]
    simp [rk]
  · omega

theorem s16nt_row_l52
    [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hirr : commSub ⊤ L ∈ irrSet L)
    (h : IsLn ↥L 5 1 ∧ E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 10) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hL, hdim10⟩ := h
  obtain ⟨eL⟩ := CFSG.Quasithin.Vol2.Ch11.OE2.nonempty_sl_of_lieModel (d := 5) hL
  exact s16nt_goal_of_irr_h1 hW2 hirr hdim10 (by norm_num) fun Q _ _ _ ρ hρ hdim =>
    le_of_eq (CFSG.Quasithin.JonesParshall.Curtis.finrank_H1_irreducible_ten
      (θ := eL) hρ hdim)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
