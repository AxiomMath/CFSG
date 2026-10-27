module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFour

public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import Certificates.Certificate13723
public import Certificates.Certificate13724
public import Certificates.Certificate19953
public import Certificates.Certificate8081
public import Certificates.Certificate8080

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModel
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Lift
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixReduced
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixCover
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULin
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGLieModelPSULabel

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev suPermSubgroup {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {a | SUPerm p b a}
  one_mem' := ⟨1, by intro i; simp⟩
  mul_mem' := by
    rintro a c ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨σ * τ, fun i => ?_⟩
    rw [LinearEquiv.mul_apply, hτ i, hσ (τ i)]
    rfl
  inv_mem' := by
    rintro a ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun i => ?_⟩
    have h := congrArg (fun v => a⁻¹ v) (hσ (σ⁻¹ i))
    simpa using h.symm

private lemma mem_suPermSubgroup {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V)
    {a : V ≃ₗ[ZMod p] V} : a ∈ suPermSubgroup (p := p) b ↔ SUPerm p b a := Iff.rfl

private noncomputable def permEquivSuPerm {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) :
    Equiv.Perm (Fin m) ≃* suPermSubgroup (p := p) b where
  toFun σ := ⟨b.equiv b σ, by
    change SUPerm p b (b.equiv b σ)
    exact ⟨σ, fun i => by rw [Module.Basis.equiv_apply]⟩⟩
  invFun a := Classical.choose ((mem_suPermSubgroup (p := p) b).mp a.2)
  left_inv σ := by
    apply Equiv.ext
    intro i
    have h1 : b.equiv b σ (b i) = b (σ i) := by rw [Module.Basis.equiv_apply]
    have h2 := Classical.choose_spec
      (show SUPerm p b (b.equiv b σ) from ⟨σ, fun i => by rw [Module.Basis.equiv_apply]⟩) i
    exact b.injective (h2.symm.trans h1)
  right_inv a := by
    apply Subtype.ext
    change b.equiv b (Classical.choose
      ((mem_suPermSubgroup (p := p) b).mp a.2)) = (a : V ≃ₗ[ZMod p] V)
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change (b.equiv b (Classical.choose
      ((mem_suPermSubgroup (p := p) b).mp a.2))) (b i) = (a : V ≃ₗ[ZMod p] V) (b i)
    rw [Module.Basis.equiv_apply]
    exact (Classical.choose_spec
      ((mem_suPermSubgroup (p := p) b).mp a.2) i).symm
  map_mul' σ τ := by
    apply Subtype.ext
    change b.equiv b (σ * τ) = b.equiv b σ * b.equiv b τ
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    simp [Module.Basis.equiv_apply, Equiv.Perm.mul_apply]

theorem su_fullWeylRank_of_model
    {p : ℕ} [Fact p.Prime] {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {b : Module.Basis (Fin m) (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : ∀ a, a ∈ A ↔ SUPerm p b a)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (ML : CoxeterMatrix Λ) (hWM : GGIsWeylMatrix ML)
    (f : ML.Group ≃* ↥A) (hm : 2 ≤ m) :
    Fintype.card Λ = m - 1 := by
  classical
  have hAeq : A = suPermSubgroup (p := p) b := by
    apply Subgroup.ext
    intro a
    exact hA a
  let eA : ↥A ≃* ↥(suPermSubgroup (p := p) b) := MulEquiv.subgroupCongr hAeq
  let ePerm : ↥(suPermSubgroup (p := p) b) ≃* Equiv.Perm (Fin m) :=
    (permEquivSuPerm (p := p) b).symm
  obtain ⟨eType0, -⟩ := ggCoxeterA_mulEquivPerm (m - 1)
  have hsub : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
  let eType : (CoxeterMatrix.A (m - 1)).Group ≃* Equiv.Perm (Fin m) := by
    rw [hsub] at eType0
    exact eType0
  let e : ML.Group ≃* (CoxeterMatrix.A (m - 1)).Group :=
    (f.trans eA).trans (ePerm.trans eType.symm)
  have hm1 : 1 ≤ m - 1 := by omega
  have hAweyl : GGIsWeylMatrix (CoxeterMatrix.A (m - 1)) :=
    ggHLT_weyl_A (n := m - 1) hm1
  have hrank := ggWeylTypeData_rank_eq_of_mulEquiv hWM hAweyl e
  simpa [Nat.card_eq_fintype_card] using hrank

theorem su_exact2_left_weylRank
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {_B Bs L _D J K : Subgroup G} {x : G} {m : ℕ}
    {τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs}
    (hcm : SUCoordModel p Bs L m τ) (_hp3 : p = 3) (hm7 : 7 ≤ m) (_hm3 : ¬ 3 ∣ m)
    (hx : x ∈ Bs) (hτ : τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨x, hx⟩)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ) (_ML : CoxeterMatrix Λ),
      S.card = 2 ∧ Fintype.card Λ = m - 1 ∧
        Fintype.card {i : Λ // i ∉ S} = m - 3 := by
  classical
  obtain ⟨V, hV, hVp, ι, b, hb, hperm⟩ :=
    su_linearModel_of_coord hcm hx hτ
  obtain ⟨Λ, hΛF, hΛD, S, Λa, hΛaF, hΛaD, ML, CL, MK, CK, V', hV', hV'p, ι', φ, h', α,
    hS, hΛa1, hΛa3, hWM, hCL, hWMK, hCK, htyp, hlin, hrefl, hCLmat, hCKmat, hsel, hfL,
    hfK, hgenL, hgenK, hdel, hgenJ⟩ := hD
  obtain ⟨fL, -⟩ := hfL
  let eLin : ↥(ggAutomizer L Bs) ≃*
      ↥((ggAutomizer L Bs).map (ggLin (p := p) ι)) :=
    Subgroup.equivMapOfInjective _ _ (ggLin_injective (p := p) ι)
  have hfull : Fintype.card Λ = m - 1 :=
    su_fullWeylRank_of_model (p := p) (m := m) (V := V) (b := b)
      (A := (ggAutomizer L Bs).map (ggLin (p := p) ι)) (hA := hperm)
      (ML := ML) (hWM := hWM) (f := fL.trans eLin) (by omega)
  have hsurv : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S)]
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    rw [hsub]
  refine ⟨Λ, hΛF, hΛD, S, ML, hS, hfull, ?_⟩
  rw [hsurv, hfull, hS, Nat.sub_sub]

private theorem unitaryExact2_labL_of_innerDiag {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L) :
    GGHdRo7SULabL p L := by
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hS, _, _⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, htag, hn, h6, hndvd⟩ := hS
  exact ⟨lab, hlab, hhas, hp3, htag, hn, h6, hndvd⟩

theorem su_exact2_left_weylRank_of_marking
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (m : ℕ) (_τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs)
      (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ) (_ML : CoxeterMatrix Λ),
      p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧ S.card = 2 ∧ Fintype.card Λ = m - 1 ∧
        Fintype.card {i : Λ // i ∉ S} = m - 3 := by
  obtain ⟨labL, hlabL, hhasL, hp3, htag, hn, h6, h3m⟩ := unitaryExact2_labL_of_innerDiag hM
  obtain ⟨m, hx, τ, -, hm7, hm3, hτ, hcm⟩ :=
    hdRo7SULCoordAux_modelCfg (hdRo7SULCoordAux_hyp_of_resHyp hH) hRig
      ⟨labL, hlabL, hhasL, hp3, htag, hn, h6, h3m⟩
  obtain ⟨Λ, hΛF, hΛD, S, ML, hS, hfull, hsurv⟩ :=
    su_exact2_left_weylRank (p := p) (m := m) (τ := τ) (_B := B) (_D := D)
      hcm hp3 hm7 hm3 hx hτ hD
  exact ⟨m, τ, Λ, hΛF, hΛD, S, ML, hp3, hm7, hm3, hS, hfull, hsurv⟩

theorem ggResRowAt_SUCorank2_of_label_lieModel
    {G : Type} [Group G] {p : ℕ} {_Bs L J _K : Subgroup G}
    (labL : LargeEvenLabel) (hΛL : LargeEvenInLambda2 labL)
    (hHasL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) (htag : labL.tag = .twA) (hn : labL.n = 1)
    (h6 : 6 ≤ labL.rank) (h3m : ¬ 3 ∣ labL.rank + 1)
    (hJLie : CFSG.Blueprint.LieModel
      (↥J ⧸ Subgroup.center ↥J) .PSU (labL.rank - 1) 2 1) :
    GGResRowAt ggRowSUCorank2 p J L := by
  let labJ : LargeEvenLabel := ⟨.twA, labL.rank - 2, 1⟩
  have hr4 : 2 ≤ labL.rank - 2 := by omega
  have hJΛ : LargeEvenInLambda2 labJ := by
    dsimp [labJ, LargeEvenInLambda2]
    refine ⟨by norm_num, hr4, ?_⟩
    intro h
    omega
  have hJHas : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
    have hdim : labL.rank - 2 + 1 = labL.rank - 1 := by omega
    have hmodel : CFSG.Blueprint.LieModel
        (↥J ⧸ Subgroup.center ↥J) .PSU (labL.rank - 2 + 1) 2 1 := by
      simpa [hdim] using hJLie
    have hcomp := CFSG.StandardType.TableCRes.ggCompLabelAt_twA
      (r := labL.rank - 2) (f := 1) hr4 (by norm_num) (by intro h; omega) hmodel
    exact hcomp.2.2.1
  refine ⟨labJ, labL, hJΛ, hΛL, hJHas, hHasL, ?_⟩
  exact ⟨hp3, rfl, rfl, htag, hn, by dsimp [labJ]; omega, h6, h3m⟩

end CFSG.StandardType.HdRo7SU

end

public section

theorem su_center_eq_bot_of_not_dvd_three {F : Type} [Field F] [Finite F]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F) {m : ℕ}
    (hm : 1 ≤ m) (hm3 : ¬ 3 ∣ m) :
    Subgroup.center (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F m) = ⊥ := by
  have hcenter := CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars h m
  refine Subgroup.card_eq_one.mp ?_
  rw [hcenter, CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars h hm]
  have hcop : Nat.Coprime m 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
  simpa using hcop.gcd_eq_one


namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open CFSG.StandardType.LineU

private lemma inf_centralizer_eq_of_conj_eq {G : Type} [Group G] {L : Subgroup G} {e y : G}
    (h : ∀ l : L, (e : G) * l * e⁻¹ = (y : G) * l * y⁻¹) :
    L ⊓ Subgroup.centralizer ({(e : G)} : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
  ext l
  constructor
  · intro hl
    rw [Subgroup.mem_inf] at hl ⊢
    refine ⟨hl.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    have hle : (e : G) * l = l * e := by
      simpa using (Subgroup.mem_centralizer_iff.mp hl.2) e (by simp)
    have hll : (e : G) * l * e⁻¹ = l := by
      rw [hle]
      group
    have hy : (y : G) * l * y⁻¹ = l := by
      rw [← h ⟨l, hl.1⟩, hll]
    have h1 : (y : G) * l = l * y := by
      calc (y : G) * l = (y * l * y⁻¹) * y := by group
        _ = l * y := by rw [hy]
    exact h1
  · intro hl
    rw [Subgroup.mem_inf] at hl ⊢
    refine ⟨hl.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    have hly : (y : G) * l = l * y := by
      simpa using (Subgroup.mem_centralizer_iff.mp hl.2) y (by simp)
    have hll : (y : G) * l * y⁻¹ = l := by
      rw [hly]
      group
    have he : (e : G) * l * e⁻¹ = l := by
      rw [h ⟨l, hl.1⟩, hll]
    have h1 : (e : G) * l = l * e := by
      calc (e : G) * l = (e * l * e⁻¹) * e := by group
        _ = l * e := by rw [he]
    exact h1

private theorem center_eq_bot_of_surjective_ker_eq_bot {F : Type} [Field F] [Finite F]
    {m : ℕ} {L : Type} [Group L]
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F m) →* L}
    (hsurj : Function.Surjective φ) (hker : φ.ker = ⊥)
    (hZ : Subgroup.center (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F m) = ⊥) :
    Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨g, rfl⟩ := hsurj z
  have hginj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hgZ : g ∈ Subgroup.center
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F m) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply hginj
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hz) (φ t)
  rw [hZ] at hgZ
  have hg1 : g = 1 := by simpa using hgZ
  rw [hg1, map_one]
  exact Subgroup.one_mem ⊥

private theorem su_ker_eq_bot_of_scalar {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (hm : 1 ≤ m) (hm3 : ¬ 3 ∣ m) {L : Type} [Group L]
    {φ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F m) →* L}
    (hker : ∀ g : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        diagonal (fun _ => c)) :
    φ.ker = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  obtain ⟨c, hc⟩ := hker g hg
  have hdet1 : (((g : GL (Fin m) F).det : Fˣ) : F) = 1 := by
    change Matrix.det ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1
    exact ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hF).1 g.2).1
  have hdetc : (((g : GL (Fin m) F).det : Fˣ) : F) = c ^ m := by
    change Matrix.det ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = c ^ m
    rw [congrArg Matrix.det hc]
    simp [Matrix.det_diagonal]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [hdet1, h0] at hdetc
    have hm0 : m ≠ 0 := by omega
    simp [zero_pow hm0] at hdetc
  let cu : Fˣ := Units.mk0 c hc0
  have hgGL : (g : GL (Fin m) F) = Matrix.GeneralLinearGroup.scalar (Fin m) cu := by
    apply Units.ext
    have hdiag : diagonal (fun _ : Fin m => c) =
        diagonal (algebraMap F (Fin m → F) cu) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [cu, Pi.algebraMap_apply]
      · simp [Matrix.diagonal, hij]
    rw [hc, hdiag]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar]
  have hcent : g ∈ Subgroup.center
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F m) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    change (t : GL (Fin m) F) * (g : GL (Fin m) F) =
      (g : GL (Fin m) F) * (t : GL (Fin m) F)
    rw [hgGL]
    exact (Matrix.GeneralLinearGroup.scalar_commute cu (t : GL (Fin m) F)).symm
  have hZ := su_center_eq_bot_of_not_dvd_three hF hm hm3
  rw [hZ] at hcent
  simpa using hcent

private theorem su_diagModel_of_data
    {G : Type} [Group G] [Finite G] {L Bs : Subgroup G}
    {F : Type} [Field F] [Finite F] {m : ℕ} (hFcard : Nat.card F = 4)
    (hm7 : 7 ≤ m) (hm3 : ¬ 3 ∣ m)
    {θ : (↥L ⧸ Subgroup.center ↥L) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)}
    (hnorm : Bs ≤ Subgroup.normalizer (L : Set G))
    (hcommL : commutator ↥L = ⊤)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    {I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)))}
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ I, LargeEvenInduces θ
      (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hIle : I ⊆ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F 2))
      (LargeEvenGUSet (Fin m) F 2)) :
    ∃ φ : ↥(unitarySU 2 1 F m) →* L, Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
        ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
          diagonal (fun _ => c)) ∧
      ∀ a ∈ (ggGamma L hnorm).range, ∃ t : Fin m → F, LineU.ActsDiagU φ a t := by
  classical
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hFcard (by norm_num)
  let ψ : ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin m) F 2) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    exact (QuotientGroup.eq_one_iff z).mp (θ.injective (by simpa [ψ] using hz))
  let A : Subgroup (MulAut ↥L) := (ggGamma L hnorm).range
  have hAel : CFSG.Open.IsElemAbelian 3 A := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show ggGamma L hnorm a * ggGamma L hnorm b =
        ggGamma L hnorm b * ggGamma L hnorm a
      rw [← map_mul, ← map_mul]
      congr 1
      exact hBs.1.is_comm.comm a b
    · rintro _ ⟨a, rfl⟩
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 a.1 a.2)
      rw [← map_pow, ha3, map_one]
  have hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F 2))
      (LargeEvenGUSet (Fin m) F 2), ∀ l : L, x (ψ l) = ψ (a l) := by
    rintro a ⟨b, rfl⟩
    obtain ⟨xaut, hxautI, hxautind⟩ := hI b⁻¹ (inv_mem b.2)
    refine ⟨xaut, hIle hxautI, ?_⟩
    intro l
    exact hxautind l (ggGamma L hnorm b l) (by
      simp only [ggGamma_coe]
      group)
  have hcov : UnitaryCoverAt 1 m F :=
    LineU.unitaryUniversalCover 1 m F hFcard (by omega) (by
      intro h
      have := congrArg Prod.fst h
      omega)
  obtain ⟨φ, hφsurj, hφker, hdiag⟩ :=
    LineU.exists_diagModel_coprime hFcard (by norm_num) (by omega) Nat.prime_three
      (by norm_num) hm3 hcov hψsurj hψker hcommL hAel hAI
  exact ⟨φ, hφsurj, hφker, hdiag⟩



private lemma diag_conj_mem_blockSU {F : Type} [Field F] {m : ℕ} {I : Finset (Fin m)}
    {D : GL (Fin m) F} {t : Fin m → F}
    (hDt : ((D : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal t)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)))
    {x : ↥(unitarySU 2 1 F m)} (hx : x ∈ TableBUE.blockSU (K := F) (n := 1) I) :
    conjN D hD x ∈ TableBUE.blockSU (K := F) (n := 1) I := by
  rw [TableBUE.mem_blockSU] at hx ⊢
  rw [coe_conjN]
  have hmul : ((D : Matrix (Fin m) (Fin m) F) * ((D⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) =
      (1 : Matrix (Fin m) (Fin m) F) := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmul' : (diagonal t) * ((D⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    simpa [hDt] using hmul
  have ht : ∀ i, t i ≠ 0 := by
    intro i h0
    have h := congrFun (congrFun hmul' i) i
    rw [Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h
    exact zero_ne_one h
  have hDinv : ((D⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      diagonal (fun i => (t i)⁻¹) := by
    ext i j
    have h := congrFun (congrFun hmul' i) j
    rw [Matrix.diagonal_mul] at h
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      have h1 : t i * ((D⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i i = 1 := by
        simpa using h
      exact eq_inv_of_mul_eq_one_right h1
    · rw [Matrix.diagonal_apply_ne _ hij]
      have h' : t i * ((D⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j = 0 := by
        simpa [Matrix.one_apply_ne hij] using h
      exact (mul_eq_zero.mp h').resolve_left (ht i)
  intro i j hij
  rw [Units.val_mul, Units.val_mul, hDt, hDinv, Matrix.mul_assoc,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij' : i = j
  · subst hij'
    have hi : i ∉ I := by
      rcases hij with hi | hi
      · exact hi
      · exact hi
    rw [hx i i (Or.inl hi), Matrix.one_apply_eq]
    simpa using mul_inv_cancel₀ (ht i)
  · rw [hx i j hij, Matrix.one_apply_ne hij']
    ring

public theorem su_left_block_component_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L) (hp3 : p = 3) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
      (φ : ↥(unitarySU 2 1 F m) →* L) (I : Finset (Fin m))
      (hnorm : Bs ≤ Subgroup.normalizer (L : Set G))
      (hdiag : ∀ a ∈ (ggGamma L hnorm).range,
        ∃ t : Fin m → F, ActsDiagU φ a t)
      (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
        ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
          diagonal (fun _ => c)),
      Nat.card F = 4 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧ Function.Surjective φ ∧
      J = (TableBUE.blockSU (K := F) (n := 1) I).map (L.subtype.comp φ) ∧ 4 ≤ I.card ∧
      Bs ≤ Subgroup.normalizer (J : Set G) ∧
      (∃ ρ : ↥(unitarySU 2 1 F I.card) →* J, Function.Surjective ρ ∧
        ρ.ker ≤ Subgroup.center ↥(unitarySU 2 1 F I.card)) ∧
      CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSU I.card 2 1 := by
  classical
  obtain ⟨m, F, hFld, hFfin, θ, Im, hFcard, hm7, hm3, hnorm, hIm, hIle⟩ :=
    hdRo7SULCoordAux_markingDataCfg (hdRo7SULCoordAux_hyp_of_resHyp hH) hRig
      (unitaryExact2_labL_of_innerDiag hM)
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hFcard (by norm_num)
  have hBs : CFSG.Open.IsElemAbelian 3 Bs := by
    simpa [hp3] using hH.1.2.1.2.1
  have hcommL : commutator ↥L = ⊤ := hM.1
  obtain ⟨φ, hφsurj, hφker, hdiag⟩ :=
    su_diagModel_of_data (I := Im) (θ := θ) hFcard hm7 hm3 hnorm hcommL hBs hIm hIle
  have hφkerbot : φ.ker = ⊥ := su_ker_eq_bot_of_scalar hF (by omega) hm3 hφker
  have hZSU : Subgroup.center (unitarySU 2 1 F m) = ⊥ :=
    su_center_eq_bot_of_not_dvd_three hF (by omega) hm3
  have hZL : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_surjective_ker_eq_bot hφsurj hφkerbot hZSU
  obtain ⟨hPre, -⟩ := hH.1.2.2
  obtain ⟨-, hDel, -, hxD, -, hJcomp, -⟩ := hPre
  obtain ⟨hSHat, hNeighbor⟩ := hH.2.2.2.2.1
  have hyB : y ∈ B := hSHat.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hDeq : D = Subgroup.closure ({x, y} : Set G) := hNeighbor.1
  have hyD : y ∈ D := by
    rw [hDeq]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨-, -, -, -, -, -, hSStar, -⟩ := hH.1.1
  have hLCx : L ≤ Subgroup.centralizer ({x} : Set G) := hSStar.2.2.2.1.1
  obtain ⟨φy, hφyI, hφyind⟩ := hIm y hyBs
  have hφeq : φy = ggLAut L θ ⟨y⁻¹, hnorm (inv_mem hyBs)⟩ :=
    eq_ggLAut_of_induces (L := L) (θ := θ) (hnorm hyBs) hφyind
  have hy3 : y ^ 3 = 1 := by
    simpa [hp3] using hDel.2 y hyD
  have hyinv3 : (⟨y⁻¹, hnorm (inv_mem hyBs)⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    change (y⁻¹) ^ 3 = (1 : G)
    rw [inv_pow, hy3, inv_one]
  have hφp : φy ^ 3 = 1 := by
    rw [hφeq, ← map_pow, hyinv3, map_one]
  have hφyIm : φy ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F 2))
      (LargeEvenGUSet (Fin m) F 2) := by
    exact hIle hφyI
  obtain ⟨r, hr⟩ := TableBUE.mem_range_conj_of_pow_eq_one (h := hF) (K := F) (n := 1)
    (d := m) (p := 3) hFcard (by omega) (by
    intro hc
    have := congrArg Prod.fst hc
    omega) Nat.prime_three (by norm_num) hm3 hφyIm hφp
  let q : ↥L ⧸ Subgroup.center ↥L := θ.symm r⁻¹
  let e : ↥L := Quotient.out q
  have heq : QuotientGroup.mk e = q := Quotient.out_eq' q
  have hθe : θ (QuotientGroup.mk e) = r⁻¹ := by
    rw [heq]
    exact θ.apply_symm_apply r⁻¹
  have hae : ggGamma L hnorm ⟨y, hyBs⟩ = (MulAut.conj e : MulAut ↥L) := by
    ext l
    have hquot : θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l)) =
        r⁻¹ * θ (QuotientGroup.mk l) * r := by
      have hpre : φy (θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l))) =
          θ (QuotientGroup.mk l) := by
        refine hφyind (ggGamma L hnorm ⟨y, hyBs⟩ l) l ?_
        simp only [ggGamma_coe]
        group
      have hφyval : φy (θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l))) =
          r * θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l)) * r⁻¹ := by
        have := congrArg (fun f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)) =>
          f (θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l)))) hr
        simpa [MulAut.conj_apply] using this.symm
      have hconj : r * θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l)) * r⁻¹ =
          θ (QuotientGroup.mk l) := by
        rw [← hφyval]
        exact hpre
      have hconj' : θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l)) =
          r⁻¹ * θ (QuotientGroup.mk l) * r := by
        calc θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l)) =
            r⁻¹ * (r * θ (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l)) * r⁻¹) * r := by group
          _ = r⁻¹ * θ (QuotientGroup.mk l) * r := by rw [hconj]
      exact hconj' 
    have hq : (QuotientGroup.mk (ggGamma L hnorm ⟨y, hyBs⟩ l) :
        ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk (e * l * e⁻¹) := by
      apply θ.injective
      rw [hquot]
      have hmk : (QuotientGroup.mk (e * l * e⁻¹) :
          ↥L ⧸ Subgroup.center ↥L) =
          QuotientGroup.mk e * QuotientGroup.mk l * (QuotientGroup.mk e)⁻¹ := by
        simp [mul_assoc]
      rw [hmk, map_mul, map_mul, map_inv, hθe, inv_inv]
    have hz : (e * l * e⁻¹)⁻¹ * ggGamma L hnorm ⟨y, hyBs⟩ l ∈
        Subgroup.center ↥L := QuotientGroup.eq.mp hq.symm
    rw [hZL] at hz
    have hz1 : (e * l * e⁻¹)⁻¹ * ggGamma L hnorm ⟨y, hyBs⟩ l = 1 := by
      simpa using hz
    have hz1G : (((e * l * e⁻¹)⁻¹ * ggGamma L hnorm ⟨y, hyBs⟩ l : ↥L) : G) = 1 := by
      rw [hz1]
      rfl
    have hEqL : (ggGamma L hnorm ⟨y, hyBs⟩ l : ↥L) = e * l * e⁻¹ := by
      calc (ggGamma L hnorm ⟨y, hyBs⟩ l : ↥L) = (e * l * e⁻¹) *
            ((e * l * e⁻¹)⁻¹ * ggGamma L hnorm ⟨y, hyBs⟩ l) := by group
        _ = e * l * e⁻¹ := by rw [hz1, mul_one]
    exact congrArg Subtype.val hEqL
  obtain ⟨t, ht⟩ := hdiag (ggGamma L hnorm ⟨y, hyBs⟩) ⟨⟨y, hyBs⟩, rfl⟩
  obtain ⟨D0, hD0norm, hD0diag, hD0act⟩ := ht
  let δ : Fin m → Fˣ := fun i => Units.mk0 (t i) (ActsDiagU.ne_zero
    ⟨D0, hD0norm, hD0diag, hD0act⟩ i)
  have hD0δ : D0 = CFSG.SectionRank.OddCover.diagHom m δ := by
    apply Units.ext
    rw [hD0diag]
    rw [CFSG.SectionRank.OddCover.coe_diagHom]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [δ]
    · simp [Matrix.diagonal, hij]
  have hpair : (e, CFSG.SectionRank.OddCover.diagHom m δ) ∈ SUTorus.suPairs φ := by
    refine ⟨?_, ?_⟩
    · simpa [hD0δ] using hD0norm
    · intro u v hv
      have hvD : (v : GL (Fin m) F) = D0 * u * D0⁻¹ := by
        simpa [hD0δ] using hv
      have hv' : v = conjN D0 hD0norm u := Subtype.ext hvD
      rw [hv']
      calc e * φ u * e⁻¹ = (MulAut.conj e) (φ u) := by rw [MulAut.conj_apply]
      _ = ggGamma L hnorm ⟨y, hyBs⟩ (φ u) := by rw [hae]
      _ = φ (conjN D0 hD0norm u) := hD0act u
  have hCD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext l
    constructor
    · intro hl
      rw [Subgroup.mem_inf] at hl ⊢
      refine ⟨hl.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_centralizer_iff.mp hl.2) y (by
          rw [hDeq]
          exact Subgroup.subset_closure (by simp))
    · intro hl
      rw [Subgroup.mem_inf] at hl ⊢
      refine ⟨hl.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hxd : x * l = l * x := Subgroup.mem_centralizer_iff.mp (hLCx hl.1) x (by simp)
      have hyd : y * l = l * y := Subgroup.mem_centralizer_iff.mp hl.2 y (by simp)
      have hsub : ({x, y} : Set G) ⊆ Subgroup.centralizer ({l} : Set G) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · change z ∈ Subgroup.centralizer ({l} : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst w
          exact hxd.symm
        · change z ∈ Subgroup.centralizer ({l} : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst w
          exact hyd.symm
      have hle : D ≤ Subgroup.centralizer ({l} : Set G) := by
        rw [hDeq]
        exact (Subgroup.closure_le (Subgroup.centralizer ({l} : Set G))).mpr hsub
      have hcl : d ∈ Subgroup.centralizer ({l} : Set G) := hle hd
      exact (Subgroup.mem_centralizer_iff.mp hcl l (by simp)).symm
  have hcentEq : L ⊓ Subgroup.centralizer ({(e : G)} : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) :=
    inf_centralizer_eq_of_conj_eq (L := L) (e := e) (y := y) (fun l => by
      have h := congrArg (fun f : MulAut ↥L => (f l : G)) hae
      simpa [ggGamma_coe, MulAut.conj_apply] using h.symm)
  have hJcompE : IsComponentOf J (L ⊓ Subgroup.centralizer ({(e : G)} : Set G)) := by
    rw [hcentEq, ← hCD]
    exact hJcomp
  let ψ : ↥(unitarySU 2 1 F m) →* G := L.subtype.comp φ
  have hψkerbot : ψ.ker = ⊥ := by
    apply le_antisymm
    · intro z hz
      rw [MonoidHom.mem_ker] at hz
      have hzφ : φ z = 1 := by
        apply Subtype.ext
        simpa [ψ] using hz
      have hz' : z ∈ φ.ker := MonoidHom.mem_ker.mpr hzφ
      rw [hφkerbot] at hz'
      simpa using hz'
    · exact bot_le
  have hψpair : ((e : G), CFSG.SectionRank.OddCover.diagHom m δ) ∈ SUTorus.suPairs ψ := by
    refine ⟨hpair.1, ?_⟩
    intro u v hv
    simpa [ψ] using congrArg Subtype.val (hpair.2 u v hv)
  have hψrange : ψ.range = L := by
    ext g
    constructor
    · rintro ⟨z, hz⟩
      rw [← hz]
      exact (φ z).2
    · intro hg
      obtain ⟨z, hz⟩ := hφsurj ⟨g, hg⟩
      exact ⟨z, by simp [ψ, hz]⟩
  have hJblock : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer ({(e : G)} : Set G)) := by
    rw [hψrange]
    exact hJcompE
  obtain ⟨n, hm_eq⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  subst m
  obtain ⟨I, hI4, hIconst, hJeq⟩ :=
    SUTorus.exists_blockSU_of_isComponentOf_two (m := n) hF (by rw [hψkerbot]; exact bot_le) hψpair hJblock
  have hVq : (I.card, 2 ^ 1) ≠ (3, 2) := by
    intro hc
    have := congrArg Prod.fst hc
    omega
  have hJLie : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSU I.card 2 1 := by
    have h0 := SUTorus.lieModel_map_blockSU (f := 1) (n := n + 1) hF
      (ψ := ψ) (by rw [hψkerbot]; exact bot_le) (V := I) (by omega) hVq
    rw [hJeq]
    simpa [ψ] using h0
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) := by
    have hstep : ∀ c ∈ Bs, ∀ x ∈ J, c * x * c⁻¹ ∈ J := by
      intro c hc x hx
      rw [hJeq] at hx ⊢
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨t, ht⟩ := hdiag (ggGamma L hnorm ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨D, hDnorm, hDdiag, hDact⟩ := ht
      have hmem : conjN D hDnorm u ∈ TableBUE.blockSU (K := F) (n := 1) I :=
        diag_conj_mem_blockSU hDdiag hDnorm hu
      have hconj : c * ψ u * c⁻¹ = ψ (conjN D hDnorm u) := by
        have := congrArg Subtype.val (hDact u)
        simpa [ψ, ggGamma_coe] using this
      rw [hconj]
      exact Subgroup.mem_map_of_mem _ hmem
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hstep b hb z hz
    · intro hz
      have hz' := hstep b⁻¹ (inv_mem hb) (b * z * b⁻¹) hz
      simpa [mul_assoc] using hz'
  obtain ⟨ρ, hρsurj, hρker⟩ :=
    SUTorus.exists_hom_of_eq_map_blockSU hF (by rw [hψkerbot]; exact bot_le) hJeq
  refine ⟨n + 1, F, hFld, hFfin, φ, I, hnorm, hdiag, hφker, hFcard, ?_, ?_, hφsurj,
    by simpa [ψ] using hJeq, hI4, hNJ, ⟨ρ, hρsurj, hρker⟩, hJLie⟩
  · omega
  · omega




private theorem ker_le_center_of_unitaryModel
    {F : Type} [Field F] {m : ℕ}
    {J : Type} [Group J]
    (ψ : ↥(unitarySU 2 1 F m) →* J) (hM : UnitTB.Model ψ) :
    ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 F m) := by
  intro g hg
  obtain ⟨c, hc⟩ := hM.ker g hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private theorem lieModel_of_unitaryModel
    {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (hm : 3 ≤ m) (hmq : (m, 2 ^ 1) ≠ (3, 2))
    {J : Type} [Group J] [Finite J]
    (ψ : ↥(unitarySU 2 1 F m) →* J) (hM : UnitTB.Model ψ) :
    CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .PSU m 2 1 := by
  have hperf : Group.IsPerfect ↥(unitarySU 2 1 F m) :=
    (CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_unitarySU
      (h := hF) (p := 2) (f := 1) (K := F) (m := m) hm hmq).1
  obtain ⟨eZ⟩ := CFSG.OddStandard.HigherRank.F3.nonempty_quotient_center_equiv_of_central_cover
    ψ hM.surj (ker_le_center_of_unitaryModel ψ hM) hperf
  have hSU : CFSG.Blueprint.LieModel
      (↥(unitarySU 2 1 F m) ⧸ Subgroup.center ↥(unitarySU 2 1 F m)) .PSU m 2 1 :=
    CFSG.StandardType.SUFacts.lieModel_quotient_center_of_mulEquiv_unitarySU
      (X := ↥(unitarySU 2 1 F m)) hF hm hmq (MulEquiv.refl _)
  exact CFSG.Blueprint.LieModel.of_mulEquiv eZ hSU

public theorem su_exact2_left_row_of_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L) (hp3 : p = 3)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowSUCorank2 p J L := by
  classical
  obtain ⟨m, F, hFld, hFfin, φ, _I, hnorm, hdiag, hφker, hFcard, hm7, hm3, hφsurj,
    _hJeq, _hI4, _hNJ, _hcover, _hJLie⟩ :=
    su_left_block_component_of_marking hH hRig hM hp3
  letI : Field F := hFld
  letI : Finite F := hFfin
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hFcard (by norm_num)
  have hφModel : UnitTB.Model φ := ⟨hF, hφsurj, hφker⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hLmodel : CFSG.Blueprint.LieModel
      (↥L ⧸ Subgroup.center ↥L) .PSU (n + 1) 2 1 :=
    lieModel_of_unitaryModel hF (by omega) (by
      intro hc
      have := congrArg Prod.fst hc
      omega) φ hφModel
  have hdiagH : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin (n + 1) → F, ActsDiagU φ a t := by
    simpa using hdiag
  obtain ⟨mJ, hmJ2, ψJ, hψJ, hψJdiag⟩ :=
    hH.exists_unitaryModel_J_of_L hφModel hdiagH
  have hmJ4 : 4 ≤ mJ := hH.unitaryModel_J_degree_ge_four_qTwo hmJ2 hψJ
  obtain ⟨rJ, rfl⟩ : ∃ rJ : ℕ, mJ = rJ + 1 := ⟨mJ - 1, by omega⟩
  have hrJ3 : 3 ≤ rJ := by omega
  have hJmodel : CFSG.Blueprint.LieModel
      (↥J ⧸ Subgroup.center ↥J) .PSU (rJ + 1) 2 1 :=
    lieModel_of_unitaryModel hF (by omega) (by
      intro hc
      have := congrArg Prod.fst hc
      omega) ψJ hψJ
  have hBsP : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hp2 : p ≠ 2 := by omega
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hF4 : Nat.card F = (2 ^ 1) ^ 2 := by norm_num [hFcard]
  letI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hF4
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eL, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF4 (by norm_num) hp2 hpq
      (by omega : 3 ≤ n) hBsP hSC hnorm hφModel hdiag
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eJ, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF4 (by norm_num) hp2 hpq
      hrJ3 hBsP hSC hH.Bs_le_normalizer_J hψJ hψJdiag
  have hWL : GGWeylTypeData n (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    have h0 : GGWeylTypeData n (Nat.card (CoxeterMatrix.A n).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A n).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := n) (by omega)))
    have hc := Nat.card_congr eL.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    simpa [hc, hz] using h0
  have hWJ : GGWeylTypeData rJ (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    have h0 : GGWeylTypeData rJ (Nat.card (CoxeterMatrix.A rJ).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rJ).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rJ) (by omega)))
    have hc := Nat.card_congr eJ.toEquiv.symm
    have hz := Nat.card_congr (Subgroup.centerCongr eJ).toEquiv
    simpa [hc, hz] using h0
  have hcardA : 1 < Nat.card (CoxeterMatrix.A rJ).Group := by
    obtain ⟨ePerm, -⟩ := ggCoxeterA_mulEquivPerm rJ
    rw [Nat.card_congr ePerm.toEquiv, Nat.card_perm]
    simp only [Nat.card_fin]
    exact Nat.one_lt_factorial.mpr (by omega)
  have hJne : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer J Bs) = 1 := by
      rw [hbot, Subgroup.card_bot]
    have h2 : Nat.card ↥(ggAutomizer J Bs) =
        Nat.card (CoxeterMatrix.A rJ).Group := Nat.card_congr eJ.toEquiv.symm
    omega
  obtain ⟨r0, hfull, hsurv⟩ := ggResLeviDatumCard_weylTypeData hD hJne
  have hLrank : n = r0 + 2 := ggWeylTypeData_rank_eq hWL hfull
  have hJrank : rJ = r0 := ggWeylTypeData_rank_eq hWJ hsurv
  have hXHas0 := ggHasLabel_of_lieModel_PSU hLmodel
  have hJHas0 := ggHasLabel_of_lieModel_PSU hJmodel
  let labX : LargeEvenLabel := ⟨.twA, n, 1⟩
  let labJ : LargeEvenLabel := ⟨.twA, rJ, 1⟩
  have hXHas : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L) := by
    have hn1 : (n + 1) - 1 = n := by omega
    rw [hn1] at hXHas0
    simpa [labX] using hXHas0
  have hJHas : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
    have hr1 : (rJ + 1) - 1 = rJ := by omega
    rw [hr1] at hJHas0
    simpa [labJ] using hJHas0
  have hXΛ : LargeEvenInLambda2 labX := by
    dsimp [labX, LargeEvenInLambda2]
    refine ⟨by norm_num, by omega, ?_⟩
    intro h
    omega
  have hJΛ : LargeEvenInLambda2 labJ := by
    dsimp [labJ, LargeEvenInLambda2]
    refine ⟨by norm_num, by omega, ?_⟩
    intro h
    omega
  refine ⟨labJ, labX, hJΛ, hXΛ, hJHas, hXHas, ?_⟩
  refine ⟨hp3, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · dsimp [labJ, labX]
    omega
  · dsimp [labX]
    omega
  · dsimp [labX]
    exact hm3

theorem su_exact2_survivor_dvd_and_ne
    {G : Type} [Group G] [Finite G]
    {p k n : ℕ} [Fact p.Prime] {Bs X J Y : Subgroup G}
    (hD : GGResLeviDatumCard k p Bs X J Y ggSelAny ggTypAny)
    (hX : ∃ c, GGWeylTypeData n (Nat.card ↥(ggAutomizer X Bs)) c)
    (hnk : k < n) (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hp2 : p ≠ 2) (hexp : ∀ b ∈ Bs, b ^ p = 1) :
    p ∣ Nat.card J ∧ ggAutomizer J Bs ≠ ⊥ := by
  exact ggResLeviDatumCard_survivor_dvd_and_ne hD hX hnk hBsJ hp2 hexp

public theorem su_exact2_right_row_of_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs K) (hp3 : p = 3) (hLB : GGLBalanceInput)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowSUCorank2 p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, _, _, _, _, _, hSK, _, _⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨-, htagK, hnK, h6K, h3mK⟩ := hSK
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmarkK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨-, labK', hlabK', hrawK⟩ :=
    ggInnerDiagOn_relabel hRig hmarkK hlabK hhasK
  obtain ⟨R₀, iR₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hrawK
  have hEqK : labK' = labK := hP₀.1
  rw [hEqK] at hrawK hP₀
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQK⟩ :=
    hdRo7SULCoordAux_twA_rawLegacy_one htagK hnK hrawK
  obtain ⟨-, -, θK, hPK⟩ := hQK
  letI : Field Fld := hFld
  letI : Finite Fld := hFldfin
  let ImK : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (labK.rank + 1)) Fld 2))) :=
    LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (labK.rank + 1)) Fld 2))
      (LargeEvenGUSet (Fin (labK.rank + 1)) Fld 2)
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 Fld :=
    TableBU.unitaryFieldData_of_card hFldcard (by norm_num)
  have hBs3 : CFSG.Open.IsElemAbelian 3 Bs := by
    simpa [hp3] using hH.1.2.1.2.1
  have hcommK : commutator ↥K = ⊤ := hM.1
  obtain ⟨φ, hφsurj, hφker, hdiagK⟩ :=
    su_diagModel_of_data (L := K) (I := ImK) (θ := θK) hFldcard
      (by omega : 7 ≤ labK.rank + 1) h3mK hPK.2.1 hcommK hBs3 hPK.2.2
      (fun _ hx => hx)
  have hφModel : UnitTB.Model φ := ⟨hF, hφsurj, hφker⟩
  have hp2 : p ≠ 2 := by omega
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hF4 : Nat.card Fld = (2 ^ 1) ^ 2 := by norm_num [hFldcard]
  letI : CharP Fld 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq
    (p := 2) (f := 1) hF4
  have hBsP : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eK, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF4 (by norm_num) hp2 hpq
      (by omega : 3 ≤ labK.rank) hBsP hSC hPK.2.1 hφModel hdiagK
  have hWK : GGWeylTypeData labK.rank (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData labK.rank
        (Nat.card (CoxeterMatrix.A labK.rank).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A labK.rank).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix
        (ggHLT_weyl_A (n := labK.rank) (by omega)))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := by
    intro b hb
    exact hH.1.2.1.2.1.2 b hb
  obtain ⟨hpJ, hJne⟩ :=
    su_exact2_survivor_dvd_and_ne hD ⟨_, hWK⟩ (by omega : 2 < labK.rank)
      hH.Bs_le_normalizer_J hp2 hexp
  have hNK : Bs ≤ Subgroup.normalizer (K : Set G) := hPK.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨hJK, hcomp⟩ :=
    isComponentOf_comap_ggFix_ggGamma_x_of_dvd hLB hH.1 hpJ hnb hNK hxBs
  obtain ⟨mJ, hmJ2, ψJ, hψJ, hψJdiag⟩ :=
    exists_unitaryModel_of_component_gamma hNK hH.Bs_le_normalizer_J hJK
      hφModel hdiagK ⟨x, hxBs⟩ hcomp
  have hmJ4 : 4 ≤ mJ := hH.unitaryModel_J_degree_ge_four_qTwo hmJ2 hψJ
  obtain ⟨rJ, rfl⟩ : ∃ rJ : ℕ, mJ = rJ + 1 := ⟨mJ - 1, by omega⟩
  have hrJ3 : 3 ≤ rJ := by omega
  have hJmodel : CFSG.Blueprint.LieModel
      (↥J ⧸ Subgroup.center ↥J) .PSU (rJ + 1) 2 1 :=
    lieModel_of_unitaryModel hF (by omega) (by
      intro hc
      have := congrArg Prod.fst hc
      omega) ψJ hψJ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eJ, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF4 (by norm_num) hp2 hpq
      hrJ3 hBsP hSC hH.Bs_le_normalizer_J hψJ hψJdiag
  have hWJ : GGWeylTypeData rJ (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    have h0 : GGWeylTypeData rJ
        (Nat.card (CoxeterMatrix.A rJ).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rJ).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rJ) (by omega)))
    have hc := Nat.card_congr eJ.toEquiv.symm
    have hz := Nat.card_congr (Subgroup.centerCongr eJ).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨r0, hfullRank, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWK
  have hJrank : rJ = r0 := ggWeylTypeData_rank_eq hWJ hsurv
  let labJ : LargeEvenLabel := ⟨.twA, rJ, 1⟩
  have hJHas : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
    have h0 := ggHasLabel_of_lieModel_PSU hJmodel
    have hr1 : (rJ + 1) - 1 = rJ := by omega
    rw [hr1] at h0
    simpa [labJ] using h0
  have hJΛ : LargeEvenInLambda2 labJ := by
    dsimp [labJ, LargeEvenInLambda2]
    refine ⟨by norm_num, by omega, ?_⟩
    intro h
    omega
  refine ⟨labJ, labK, hJΛ, hlabK, hJHas, hhasK, ?_⟩
  refine ⟨hp3, rfl, rfl, htagK, hnK, ?_, h6K, h3mK⟩
  dsimp [labJ]
  omega

open CFSG.StandardType.Line63.H5
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.PerfectCentralQuotient

variable {G : Type} [Group G] [Finite G]

theorem su_exact2_left_row_ggRowTwoNode_six
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R₀, instR₀, I₀, F₀, θ₀, hP₀⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP₀
  obtain ⟨hp3, htagL, hnL, h5L⟩ := hS
  obtain ⟨tagL, rankL, nL⟩ := labL
  simp only at htagL hnL
  cases htagL
  cases hnL
  change rankL = 5 at h5L
  have hlab5 : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    simpa [h5L] using hlabL
  have hhas5 : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L) := by
    simpa [h5L] using hhasL
  have hBs : IsElemAbelian 3 Bs := by simpa [hp3] using hH.1.tableB_facts.2.1
  have hcfg3 : GGConfig 3 B Bs x L D J := by simpa [hp3] using hH.1
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hmark := ggInnerDiagOn_relabel hRig hInn hlab5 hhas5
  have hInnMark : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
    refine largeEvenMarking_mono (fun lab' R instR I F' θ' hP' => ?_) hmark
    obtain ⟨rfl, hn, hi⟩ := hP'
    exact ⟨⟨⟨rfl, by norm_num, by norm_num, by norm_num⟩, rfl, rfl⟩,
      Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, by norm_num⟩), hn, hi⟩
  have h5 : 3 ^ 5 ≤ Nat.card Bs :=
    Line63.H5.ggUnitDvd63BstarRankInput_holds G 3 B Bs x L D J hcfg3 hInnMark
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₁, _, I₁, F₁, _, _, _, hP₁⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₁
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  have hF : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF : Nat.card F = 2 ^ 2)
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  have hSstar : LargeEvenSStar 3 B x L := by
    simpa [hp3] using hH.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hcfg3.tableB_facts.2.2.1
  have hc := card_range_ggGamma_mul_of Nat.prime_three hcfg3.tableB_facts.2.1 hxBs
    hSstar.2.2.1 hSstar.2.2.2.1.1 hSstar.2.2.2.2 hN
  have hmul : 3 ^ 4 * 3 ≤ Nat.card (ggGamma L hN).range * 3 := by
    rw [hc]
    exact h5
  have hγcard : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    Nat.le_of_mul_le_mul_right hmul (by norm_num)
  obtain ⟨hNbar, φ, hMφ, hdiagφ⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF hXperf θ hN hBs hBsI hγcard
  have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  obtain ⟨S, hS2, hJblock, hJbarComp⟩ :=
    exists_block_unitarySix_reduced_component hF hBs hN hDB hJcomp hNbar φ hMφ hdiagφ
  have hKd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hF (by norm_num)
  have hS4 : 4 ≤ S.card := by
    by_contra hlt
    have hk1 : 1 ≤ S.card := by omega
    have hk3 : S.card ≤ 3 := by omega
    haveI : Group.IsSolvable ↥(unitarySU 2 1 F S.card) :=
      WitSU.isSolvable_unitarySU_two_one hKd hk1 hk3
    have hker : ((((redMkL L).range).subtype.comp φ)).ker ≤
        Subgroup.center ↥(unitarySU 2 1 F 6) :=
      UnitTB.ker_comp_subtype_le_center hMφ
    obtain ⟨ρ, hρs, -⟩ :=
      SUTorus.exists_hom_of_eq_map_blockSU (f := 1) hKd hker hJblock
    have hsolvJbar : Group.IsSolvable ↥((J.subgroupOf (Subgroup.normalizer (L : Set G))).map
        (redMk L)) :=
      Group.isSolvable_of_surjective (f := ρ) hρs
    letI : Group.IsPerfect ↥((J.subgroupOf (Subgroup.normalizer (L : Set G))).map
        (redMk L)) := ⟨hJbarComp.2.2.1⟩
    letI : Nontrivial ↥((J.subgroupOf (Subgroup.normalizer (L : Set G))).map
        (redMk L)) := CFSG.ComponentClassification.Quasisimple.nontrivial hJbarComp.2.2
    exact Group.IsPerfect.not_isSolvable _ hsolvJbar
  let NX : Subgroup G := Subgroup.normalizer (L : Set G)
  let Jbar : Subgroup (RedGrp L) := (J.subgroupOf NX).map (redMk L)
  let Bbar : Subgroup (RedGrp L) := (redMkB hN).range
  have hJ_le_NX : J ≤ NX :=
    (hJcomp.1.trans inf_le_left).trans Subgroup.le_normalizer
  have hBJ_sub : Bs.subgroupOf NX ≤ Subgroup.normalizer (J.subgroupOf NX : Set NX) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hJ_le_NX]
    intro b hb
    exact Subgroup.mem_subgroupOf.mpr (hH.Bs_le_normalizer_J (Subgroup.mem_subgroupOf.mp hb))
  have hBJbar : Bbar ≤ Subgroup.normalizer (Jbar : Set (RedGrp L)) := by
    have h1 : (Bs.subgroupOf NX).map (redMk L) ≤
        (Subgroup.normalizer (J.subgroupOf NX : Set NX)).map (redMk L) :=
      Subgroup.map_mono hBJ_sub
    have h2 : (Subgroup.normalizer (J.subgroupOf NX : Set NX)).map (redMk L) ≤
        Subgroup.normalizer (Jbar : Set (RedGrp L)) := by
      simpa [Jbar] using
        (Subgroup.le_normalizer_map (H := J.subgroupOf NX) (redMk L))
    have hB : Bbar = (Bs.subgroupOf NX).map (redMk L) := by
      dsimp only [Bbar, redMkB]
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [hB]
    exact h1.trans h2
  obtain ⟨VL, hVLadd, hVLmod, ιL, ρL, φL, hL, αL, hNP, hρL, hφL, hlinL, hreflL, hpairL,
    ⟨eLbar, heLbar⟩, hclosL⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (f := 1) (r := 5)
      (by simpa using hF) (by norm_num) (by norm_num) (by norm_num) (by norm_num : 3 ≤ 5)
      (isElemAbelian_redB hN hBs) (redSC hN hBs (by simpa [hp3] using hH.1.2.1.2.2.2))
      hNbar hMφ hdiagφ
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm 5
  have hρeq : ∀ c : (CoxeterMatrix.A 5).Group, eLbar c = ρL (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A 5).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A 5).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heLbar k, hφL k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eLbar), map_mul (f := ePerm), map_mul (f := ρL),
          Subgroup.coe_mul]
        rw [ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eLbar), map_inv (f := ePerm), map_inv (f := ρL),
          Subgroup.coe_inv]
        rw [ih]
  have hρinj : Function.Injective ρL := by
    intro σ τ hστ
    have hσ : eLbar (ePerm.symm σ) = ρL σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
    have hτ : eLbar (ePerm.symm τ) = ρL τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
    have h1 : eLbar (ePerm.symm σ) = eLbar (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eLbar.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)) =
      S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin 6)))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJbar : ggAutomizer Jbar Bbar =
      (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)).map ρL := by
    dsimp [Jbar]
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMφ (by simpa using hF)
      Nat.prime_three (by norm_num) (by norm_num) (by norm_num : 4 ≤ 6)
      (by simpa [Bbar] using hNbar) (isElemAbelian_redB hN hBs)
      (by simpa [Bbar, NX] using redSC hN hBs (by simpa [hp3] using hH.1.2.1.2.2.2))
      hdiagφ hNP ρL hρL S
  have hcardAutJbar : Nat.card ↥(ggAutomizer Jbar Bbar) = S.card.factorial := by
    rw [hAutJbar, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hcardAut : Nat.card ↥(ggAutomizer J Bs) = Nat.card ↥(ggAutomizer Jbar Bbar) := by
    let eB := MonoidHom.ofInjective (redMkB_injective hN hBs)
    have h := ggAutomizer_redMk_eq (X := L) (Bs := Bs) (H := J) hBs hN hJ_le_NX
      hH.Bs_le_normalizer_J
    rw [h]
    exact (Subgroup.card_map_of_injective (MulAut.congr eB).injective).symm
  have hJneBar : ggAutomizer Jbar Bbar ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer Jbar Bbar) = 1 := by
      rw [hbot, Subgroup.card_bot]
    rw [hcardAutJbar] at h1
    have hlt : 1 < S.card.factorial := Nat.one_lt_factorial.mpr (by omega)
    omega
  have hJne : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer J Bs) = 1 := by
      rw [hbot, Subgroup.card_bot]
    have h2 : Nat.card ↥(ggAutomizer Jbar Bbar) = 1 := by
      rw [← hcardAut, h1]
    exact hJneBar (Subgroup.eq_bot_of_card_eq (H := ggAutomizer Jbar Bbar) h2)
  obtain ⟨r0, hfull, hsurv⟩ := ggResLeviDatumCard_weylTypeData hD hJne
  have hWLbar : GGWeylTypeData 5 (Nat.card ↥(ggAutomizer ((redMkL L).range) (redMkB hN).range))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer ((redMkL L).range) (redMkB hN).range))) := by
    have h0 : GGWeylTypeData 5 (Nat.card (CoxeterMatrix.A 5).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A 5).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := 5) (by norm_num)))
    have hc := Nat.card_congr eLbar.toEquiv.symm
    have hz := Nat.card_congr (Subgroup.centerCongr eLbar).toEquiv
    simpa [hc, hz] using h0
  have hWL : GGWeylTypeData 5 (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    let eB := MonoidHom.ofInjective (redMkB_injective hN hBs)
    have h := ggAutomizer_redMk_eq (X := L) (Bs := Bs) (H := L) hBs hN
      Subgroup.le_normalizer hN
    have hLrange : (redMkL L).range =
        (L.subgroupOf (Subgroup.normalizer (L : Set G))).map (redMk L) := by
      rw [redMkL, MonoidHom.range_comp, Subgroup.inclusion_range]
    have hmap : ggAutomizer ((redMkL L).range) (redMkB hN).range =
        (ggAutomizer L Bs).map (MulAut.congr eB).toMonoidHom := by
      rw [hLrange, h]
    let eMap := Subgroup.equivMapOfInjective (ggAutomizer L Bs)
      (MulAut.congr eB).toMonoidHom (MulAut.congr eB).injective
    let eAut := eMap.trans (MulEquiv.subgroupCongr hmap.symm)
    have hc := Nat.card_congr eAut.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eAut).toEquiv
    simpa [hc, hz] using hWLbar
  have hLrank : 5 = r0 + 2 := ggWeylTypeData_rank_eq hWL hfull
  have hWJ3 : GGWeylTypeData 3 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    have h0 : GGWeylTypeData 3 (Nat.card ↥(ggAutomizer J Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
      simpa [show r0 = 3 by omega] using hsurv
    simpa [hcardAut, hcardAutJbar] using h0
  have hfac : S.card.factorial = 24 ∨ S.card.factorial = 48 := by
    rcases hWJ3 with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h4, -, -⟩ | ⟨h6, -, -⟩ |
      ⟨h7, -, -⟩ | ⟨h8, -, -⟩ | ⟨hF4, -, -⟩ | ⟨hG2, -, -⟩
    · left
      norm_num at h
      exact h
    · right
      norm_num at h
      exact h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have hS4eq : S.card = 4 := by
    have hle : S.card ≤ 5 := by
      by_contra hle
      have h6 : 6 ≤ S.card := by omega
      have h720 : 720 ≤ S.card.factorial := by
        calc 720 = Nat.factorial 6 := by norm_num
          _ ≤ S.card.factorial := Nat.factorial_le h6
      rcases hfac with h | h <;> omega
    have hcases : S.card = 4 ∨ S.card = 5 := by omega
    rcases hcases with h4 | h5
    · exact h4
    · rw [h5] at hfac
      norm_num at hfac
  obtain ⟨χ, hχs, hχker, hχact⟩ :=
    exists_diagCover_blockSU hMφ hNbar hdiagφ (le_refl Bbar) S hJblock
      (by simpa [Bbar, Jbar, NX] using hBJbar)
  have hJbarLab : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
      (Jbar ⧸ Subgroup.center Jbar) := by
    have h := ggHasLabel_of_unitaryModel ⟨hKd, hχs, hχker⟩ (by omega : 3 ≤ S.card)
      (by
        intro hc
        have := congrArg Prod.fst hc
        omega)
    simpa [hS4eq] using h

  have hJperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJcomp.2.2.1
  letI : Group.IsPerfect ↥J := hJperf
  let fJfull : ↥J →* RedGrp L := (redMk L).comp (Subgroup.inclusion hJ_le_NX)
  have hfJfull_range : fJfull.range = Jbar := by
    dsimp [fJfull, Jbar, NX]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let fJ : ↥J →* Jbar := fJfull.codRestrict Jbar (fun j => by
    rw [← hfJfull_range]
    exact ⟨j, rfl⟩)
  have hfJ_surj : Function.Surjective fJ := by
    intro y
    have hy : (y : RedGrp L) ∈ fJfull.range := by
      rw [hfJfull_range]
      exact y.2
    rcases MonoidHom.mem_range.mp hy with ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj⟩
  have hfJ_ker : fJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have hj1 : fJfull j = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
      simpa [fJ] using h
    have htwo : ((j : G)) ∈ twoCenter L :=
      (redMk_eq_one_iff L (Subgroup.inclusion hJ_le_NX j)).mp hj1
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    exact (htwo.2.1 (j' : G) ((hJcomp.1.trans inf_le_left) j'.2)).symm
  have eJ : (↥J ⧸ Subgroup.center ↥J) ≃* (Jbar ⧸ Subgroup.center Jbar) :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence fJ hfJ_surj hfJ_ker
  have hJHas : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv eJ.symm hJbarLab
  refine ⟨⟨.twA, 3, 1⟩, ⟨.twA, 5, 1⟩, ?_, ?_, hJHas, hhas5, ?_⟩
  · unfold LargeEvenInLambda2
    norm_num
  · unfold LargeEvenInLambda2
    norm_num
  · refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
    · rw [hp3]
      norm_num
    · rw [hp3]
      norm_num
    · rfl

theorem su_exact2_left_row_ggRowTwoNode_large
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        3 ∣ lab.rank + 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨hp3, htagL, hnL, h6L, h3L⟩ := hS
  obtain ⟨tagL, rankL, nL⟩ := labL
  simp only at htagL hnL
  cases htagL
  cases hnL
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hpd : p ∣ rankL + 1 := by simpa [hp3] using h3L
  change 6 ≤ rankL at h6L
  change 3 ∣ rankL + 1 at h3L
  have hr4 : 4 ≤ rankL := by omega
  have hr5 : rankL ≠ 5 := by omega
  have hr3L : 3 ≤ rankL := by omega
  obtain ⟨Fld, hField, hFinite, hChar, hN, φ, hFcard, hModel, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_L (r := rankL) (f := 1) hRig hH hr4 hr5 hpq hpd
      hhasL hlabL
  letI : Field Fld := hField
  letI : Finite Fld := hFinite
  letI : CharP Fld 2 := hChar
  have hF4 : Nat.card Fld = (2 ^ 1) ^ 2 := hFcard
  have hBsP : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eL, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (f := 1) (r := rankL) hF4 (by norm_num)
      hp2 hpq hr3L hBsP hSC hN hModel hdiag
  have hWL : GGWeylTypeData rankL (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    have h0 : GGWeylTypeData rankL (Nat.card (CoxeterMatrix.A rankL).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankL).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix
        (ggHLT_weyl_A (n := rankL) (by omega)))
    have hc := Nat.card_congr eL.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    simpa [hc, hz] using h0
  have hdiagH : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin (rankL + 1) → Fld, LineU.ActsDiagU φ a t := by
    simpa using hdiag
  obtain ⟨mJ, hmJ2, ψJ, hψJ, hψJdiag⟩ :=
    hH.exists_unitaryModel_J_of_L hModel hdiagH
  have hmJ4 : 4 ≤ mJ := hH.unitaryModel_J_degree_ge_four_qTwo hmJ2 hψJ
  obtain ⟨rJ, rfl⟩ : ∃ rJ : ℕ, mJ = rJ + 1 := ⟨mJ - 1, by omega⟩
  have hrJ3 : 3 ≤ rJ := by omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eJ, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (f := 1) (r := rJ) hF4 (by norm_num)
      hp2 hpq hrJ3 hBsP hSC hH.Bs_le_normalizer_J hψJ hψJdiag
  have hWJ : GGWeylTypeData rJ (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    have h0 : GGWeylTypeData rJ (Nat.card (CoxeterMatrix.A rJ).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rJ).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rJ) (by omega)))
    have hc := Nat.card_congr eJ.toEquiv.symm
    have hz := Nat.card_congr (Subgroup.centerCongr eJ).toEquiv
    simpa [hc, hz] using h0
  have hcardA : 1 < Nat.card (CoxeterMatrix.A rJ).Group := by
    obtain ⟨ePerm, -⟩ := ggCoxeterA_mulEquivPerm rJ
    rw [Nat.card_congr ePerm.toEquiv, Nat.card_perm]
    simp only [Nat.card_fin]
    exact Nat.one_lt_factorial.mpr (by omega)
  have hJne : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer J Bs) = 1 := by
      rw [hbot, Subgroup.card_bot]
    have h2 : Nat.card ↥(ggAutomizer J Bs) =
        Nat.card (CoxeterMatrix.A rJ).Group := Nat.card_congr eJ.toEquiv.symm
    omega
  obtain ⟨r0, hfull, hsurv⟩ := ggResLeviDatumCard_weylTypeData hD hJne
  have hLrank : rankL = r0 + 2 := ggWeylTypeData_rank_eq hWL hfull
  have hJrank : rJ = r0 := ggWeylTypeData_rank_eq hWJ hsurv
  let labJ : LargeEvenLabel := ⟨.twA, rJ, 1⟩
  let labX : LargeEvenLabel := ⟨.twA, rankL, 1⟩
  have hXHas : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L) := hhasL
  have hJHas : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
    have h := ggHasLabel_of_unitaryModel hψJ (by omega : 3 ≤ rJ + 1)
      (by
        intro hc
        have := congrArg Prod.fst hc
        omega)
    simpa [labJ] using h
  have hJΛ : LargeEvenInLambda2 labJ := by
    dsimp [labJ, LargeEvenInLambda2]
    refine ⟨by norm_num, by omega, ?_⟩
    intro h
    omega
  have hXΛ : LargeEvenInLambda2 labX := by
    dsimp [labX]
    exact hlabL
  refine ⟨labJ, labX, hJΛ, hXΛ, hJHas, hXHas, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
  · dsimp [labJ]
    simpa using hpq
  · dsimp [labJ]
    have h : rJ + 3 = rankL + 1 := by omega
    rw [h]
    simpa [hp3] using h3L
  · dsimp [labJ, labX]
    have h : rJ + 2 = rankL := by omega
    simp [h]

theorem su_exact2_left_singular_row
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧
        3 ∣ lab.rank + 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  obtain ⟨lab, hlab, hhas, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, htag, hn, hdiv⟩ := hP.1
  have hr : 3 ≤ lab.rank := by
    have hLambda := hlab
    unfold LargeEvenInLambda2 at hLambda
    rw [htag, hn] at hLambda
    omega
  have hmark := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlab hhas
  by_cases h5 : lab.rank = 5
  · apply su_exact2_left_row_ggRowTwoNode_six hH hRig _ hD
    exact largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => by
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨hp3, htag, hn, h5⟩, hN, hI⟩) hmark
  · have h6 : 6 ≤ lab.rank := by omega
    apply su_exact2_left_row_ggRowTwoNode_large hH hRig _ hD
    exact largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => by
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨hp3, htag, hn, h6, hdiv⟩, hN, hI⟩) hmark

theorem su_exact2_right_row_ggRowTwoNode_large
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        3 ∣ lab.rank + 1) p Bs K)
    (hLB : GGLBalanceInput)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨hp3, htagK, hnK, h6K, h3K⟩ := hS
  obtain ⟨tagK, rankK, nK⟩ := labK
  simp only at htagK hnK
  cases htagK
  cases hnK
  change 6 ≤ rankK at h6K
  change 3 ∣ rankK + 1 at h3K
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hpd : p ∣ rankK + 1 := by simpa [hp3] using h3K
  have hr4 : 4 ≤ rankK := by omega
  have hr5 : rankK ≠ 5 := by omega
  have hr3K : 3 ≤ rankK := by omega
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨Fld, hField, hFinite, hChar, hN, φ, hFcard, hModel, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side hRig hH (Or.inr ⟨y, hnb⟩)
      hr4 hr5 hpq hpd hhasK hlabK
  letI : Field Fld := hField
  letI : Finite Fld := hFinite
  letI : CharP Fld 2 := hChar
  have hF4 : Nat.card Fld = (2 ^ 1) ^ 2 := hFcard
  have hBsP : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eK, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (f := 1) (r := rankK) hF4 (by norm_num)
      hp2 hpq hr3K hBsP hSC hN hModel hdiag
  have hWK : GGWeylTypeData rankK (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData rankK (Nat.card (CoxeterMatrix.A rankK).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankK).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix
        (ggHLT_weyl_A (n := rankK) (by omega)))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := by
    intro b hb
    exact hH.1.2.1.2.1.2 b hb
  obtain ⟨hpJ, hJne⟩ :=
    su_exact2_survivor_dvd_and_ne hD ⟨_, hWK⟩ (by omega : 2 < rankK)
      hH.Bs_le_normalizer_J hp2 hexp
  have hNK : Bs ≤ Subgroup.normalizer (K : Set G) := hN
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨hJK, hcomp⟩ :=
    isComponentOf_comap_ggFix_ggGamma_x_of_dvd hLB hH.1 hpJ hnb hNK hxBs
  obtain ⟨mJ, hmJ2, ψJ, hψJ, hψJdiag⟩ :=
    exists_unitaryModel_of_component_gamma hNK hH.Bs_le_normalizer_J hJK
      hModel hdiag ⟨x, hxBs⟩ hcomp
  have hmJ4 : 4 ≤ mJ := hH.unitaryModel_J_degree_ge_four_qTwo hmJ2 hψJ
  obtain ⟨rJ, rfl⟩ : ∃ rJ : ℕ, mJ = rJ + 1 := ⟨mJ - 1, by omega⟩
  have hrJ3 : 3 ≤ rJ := by omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eJ, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (f := 1) (r := rJ) hF4 (by norm_num)
      hp2 hpq hrJ3 hBsP hSC hH.Bs_le_normalizer_J hψJ hψJdiag
  have hWJ : GGWeylTypeData rJ (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    have h0 : GGWeylTypeData rJ (Nat.card (CoxeterMatrix.A rJ).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rJ).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rJ) (by omega)))
    have hc := Nat.card_congr eJ.toEquiv.symm
    have hz := Nat.card_congr (Subgroup.centerCongr eJ).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨r0, hfullRank, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWK
  have hJrank : rJ = r0 := ggWeylTypeData_rank_eq hWJ hsurv
  let labJ : LargeEvenLabel := ⟨.twA, rJ, 1⟩
  have hJHas : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
    have h := ggHasLabel_of_unitaryModel hψJ (by omega : 3 ≤ rJ + 1)
      (by
        intro hc
        have := congrArg Prod.fst hc
        omega)
    simpa [labJ] using h
  have hJΛ : LargeEvenInLambda2 labJ := by
    dsimp [labJ, LargeEvenInLambda2]
    refine ⟨by norm_num, by omega, ?_⟩
    intro h
    omega
  let labK' : LargeEvenLabel := ⟨.twA, rankK, 1⟩
  have hlabK' : LargeEvenInLambda2 labK' := by
    simpa [labK'] using hlabK
  have hhasK' : GGHasLabel labK' (↥K ⧸ Subgroup.center ↥K) := by
    simpa [labK'] using hhasK
  have hKrank : rankK = rJ + 2 := by
    omega
  refine ⟨labJ, labK', hJΛ, hlabK', hJHas, hhasK', ?_⟩
  refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
  · dsimp [labJ]
    simpa using hpq
  · dsimp [labJ]
    have h : rJ + 3 = rankK + 1 := by omega
    rw [h]
    simpa [hp3] using h3K
  · simp [labJ, labK', hKrank]

section LabelRigidity


public theorem su_exact2_left_row_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowSUCorank2 p J L := by
  obtain ⟨_, _, _, hp3, _⟩ := unitaryExact2_labL_of_innerDiag hM
  exact su_exact2_left_row_of_exact2 hH ggLabelRigidInput_holds hM hp3 hD

public theorem su_not_exact2_left_of_not_row
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L)
    (hR : ¬ GGResRowAt ggRowSUCorank2 p J L) :
    ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny :=
  fun hD => hR (su_exact2_left_row_of_marking hH hM hD)

public theorem su_not_exact2_left_of_singular_not_row
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧
        3 ∣ lab.rank + 1) p Bs L)
    (hR : ¬ GGResRowAt ggRowTwoNode p J L) :
    ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny :=
  fun hD => hR (su_exact2_left_singular_row hH ggLabelRigidInput_holds hM hD)


public theorem su_not_exact2_right_large_of_singular_not_row
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        3 ∣ lab.rank + 1) p Bs K)
    (hLB : GGLBalanceInput)
    (hR : ¬ GGResRowAt ggRowTwoNode p J K) :
    ¬ GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny :=
  fun hD => hR (su_exact2_right_row_ggRowTwoNode_large hH ggLabelRigidInput_holds hM hLB hD)

end LabelRigidity

section Q1Certificates



theorem su_exact2_right_row_ggRowTwoNode_six
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ lab.rank = 5) p Bs K)
    (hLB : GGLBalanceInput)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  have hpJ : p ∣ Nat.card J :=
    hH.prime_dvd_card_J
  obtain ⟨labK, hlabK, hhasK, R₀, instR₀, I₀, F₀, θ₀, hP₀⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS₀, -⟩ := hP₀
  obtain ⟨hp3, htagK, hnK, h5K⟩ := hS₀
  obtain ⟨tagK, rankK, nK⟩ := labK
  simp only at htagK hnK
  cases htagK
  cases hnK
  change rankK = 5 at h5K
  have hlab5 : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    simpa [h5K] using hlabK
  have hhas5 : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K) := by
    simpa [h5K] using hhasK
  have hBs3 : IsElemAbelian 3 Bs := by simpa [hp3] using hH.1.tableB_facts.2.1
  have hcfg3 : GGConfig 3 B Bs x L D J := by simpa [hp3] using hH.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hInn.le_normalizer
  have hmark := ggInnerDiagOn_relabel hRig hInn hlab5 hhas5
  obtain ⟨hKperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₁, _, I₁, F₁, _, _, _, hP₁⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₁
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  have hF : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF : Nat.card F = 2 ^ 2)
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN', hBsI⟩ := hP
  have hpq : p ∣ 2 ^ 1 + 1 := by rw [hp3]; norm_num
  have hH3 : GGResHyp 3 B Bs x L D J y K := by simpa [hp3] using hH
  have hγcard : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact four_le_card_ggGamma_of_unitary_six_side hRig hLB hH3 (Or.inr rfl)
      (by norm_num) hhas5 hlab5 (by simpa [hp3] using hpJ) hN
  obtain ⟨hNbar, φ, hMφ, hdiagφ⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF hKperf θ hN' hBs3 hBsI hγcard
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnb
  have hJcompG : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hJcompZ : IsComponentOf J
      (K ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    simpa only [CFSG.Walter.centralizer_zpowers_eq'] using hJcompG
  obtain ⟨S, hS2, hJblock, hJbarComp⟩ :=
    exists_block_unitarySix_reduced_component hF hBs3 hN
      (Subgroup.zpowers_le.mpr hxBs) hJcompZ hNbar φ hMφ hdiagφ
  have hKd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hF (by norm_num)
  have hS4 : 4 ≤ S.card := by
    by_contra hlt
    have hk1 : 1 ≤ S.card := by omega
    have hk3 : S.card ≤ 3 := by omega
    haveI : Group.IsSolvable ↥(unitarySU 2 1 F S.card) :=
      WitSU.isSolvable_unitarySU_two_one hKd hk1 hk3
    have hker : ((((redMkL K).range).subtype.comp φ)).ker ≤
        Subgroup.center ↥(unitarySU 2 1 F 6) :=
      UnitTB.ker_comp_subtype_le_center hMφ
    obtain ⟨ρ, hρs, -⟩ :=
      SUTorus.exists_hom_of_eq_map_blockSU (f := 1) hKd hker hJblock
    have hsolvJbar : Group.IsSolvable ↥((J.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (redMk K)) :=
      Group.isSolvable_of_surjective (f := ρ) hρs
    letI : Group.IsPerfect ↥((J.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (redMk K)) := ⟨hJbarComp.2.2.1⟩
    letI : Nontrivial ↥((J.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (redMk K)) := CFSG.ComponentClassification.Quasisimple.nontrivial hJbarComp.2.2
    exact Group.IsPerfect.not_isSolvable _ hsolvJbar
  let NX : Subgroup G := Subgroup.normalizer (K : Set G)
  let Jbar : Subgroup (RedGrp K) := (J.subgroupOf NX).map (redMk K)
  let Bbar : Subgroup (RedGrp K) := (redMkB hN).range
  have hJ_le_NX : J ≤ NX :=
    (hJcompG.1.trans inf_le_left).trans Subgroup.le_normalizer
  have hBJ_sub : Bs.subgroupOf NX ≤ Subgroup.normalizer (J.subgroupOf NX : Set NX) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hJ_le_NX]
    intro b hb
    exact Subgroup.mem_subgroupOf.mpr (hH.Bs_le_normalizer_J (Subgroup.mem_subgroupOf.mp hb))
  have hBJbar : Bbar ≤ Subgroup.normalizer (Jbar : Set (RedGrp K)) := by
    have h1 : (Bs.subgroupOf NX).map (redMk K) ≤
        (Subgroup.normalizer (J.subgroupOf NX : Set NX)).map (redMk K) :=
      Subgroup.map_mono hBJ_sub
    have h2 : (Subgroup.normalizer (J.subgroupOf NX : Set NX)).map (redMk K) ≤
        Subgroup.normalizer (Jbar : Set (RedGrp K)) := by
      simpa [Jbar] using
        (Subgroup.le_normalizer_map (H := J.subgroupOf NX) (redMk K))
    have hB : Bbar = (Bs.subgroupOf NX).map (redMk K) := by
      dsimp only [Bbar, redMkB]
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [hB]
    exact h1.trans h2
  obtain ⟨VK, hVKadd, hVKmod, ιK, ρK, φK, hK, αK, hNP, hρK, hφK, hlinK, hreflK, hpairK,
    ⟨eKbar, heKbar⟩, hclosK⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (f := 1) (r := 5)
      (by simpa using hF) (by norm_num) (by norm_num) (by norm_num) (by norm_num : 3 ≤ 5)
      (isElemAbelian_redB hN hBs3) (redSC hN hBs3 (by simpa [hp3] using hH.1.2.1.2.2.2))
      hNbar hMφ hdiagφ
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm 5
  have hρeq : ∀ c : (CoxeterMatrix.A 5).Group, eKbar c = ρK (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A 5).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A 5).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heKbar k, hφK k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eKbar), map_mul (f := ePerm), map_mul (f := ρK),
          Subgroup.coe_mul]
        rw [ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eKbar), map_inv (f := ePerm), map_inv (f := ρK),
          Subgroup.coe_inv]
        rw [ih]
  have hρinj : Function.Injective ρK := by
    intro σ τ hστ
    have hσ : eKbar (ePerm.symm σ) = ρK σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
    have hτ : eKbar (ePerm.symm τ) = ρK τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
    have h1 : eKbar (ePerm.symm σ) = eKbar (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eKbar.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)) =
      S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin 6)))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJbar : ggAutomizer Jbar Bbar =
      (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)).map ρK := by
    dsimp [Jbar]
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMφ (by simpa using hF)
      Nat.prime_three (by norm_num) (by norm_num) (by norm_num : 4 ≤ 6)
      (by simpa [Bbar] using hNbar) (isElemAbelian_redB hN hBs3)
      (by simpa [Bbar, NX] using redSC hN hBs3 (by simpa [hp3] using hH.1.2.1.2.2.2))
      hdiagφ hNP ρK hρK S
  have hcardAutJbar : Nat.card ↥(ggAutomizer Jbar Bbar) = S.card.factorial := by
    rw [hAutJbar, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hcardAut : Nat.card ↥(ggAutomizer J Bs) = Nat.card ↥(ggAutomizer Jbar Bbar) := by
    let eB := MonoidHom.ofInjective (redMkB_injective hN hBs3)
    have h := ggAutomizer_redMk_eq (X := K) (Bs := Bs) (H := J) hBs3 hN hJ_le_NX
      hH.Bs_le_normalizer_J
    rw [h]
    exact (Subgroup.card_map_of_injective (MulAut.congr eB).injective).symm
  have hJneBar : ggAutomizer Jbar Bbar ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer Jbar Bbar) = 1 := by
      rw [hbot, Subgroup.card_bot]
    rw [hcardAutJbar] at h1
    have hlt : 1 < S.card.factorial := Nat.one_lt_factorial.mpr (by omega)
    omega
  have hJne : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer J Bs) = 1 := by
      rw [hbot, Subgroup.card_bot]
    have h2 : Nat.card ↥(ggAutomizer Jbar Bbar) = 1 := by
      rw [← hcardAut, h1]
    exact hJneBar (Subgroup.eq_bot_of_card_eq (H := ggAutomizer Jbar Bbar) h2)
  obtain ⟨r0, hfull, hsurv⟩ := ggResLeviDatumCard_weylTypeData hD hJne
  have hWKbar : GGWeylTypeData 5 (Nat.card ↥(ggAutomizer ((redMkL K).range) (redMkB hN).range))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer ((redMkL K).range) (redMkB hN).range))) := by
    have h0 : GGWeylTypeData 5 (Nat.card (CoxeterMatrix.A 5).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A 5).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := 5) (by norm_num)))
    have hc := Nat.card_congr eKbar.toEquiv.symm
    have hz := Nat.card_congr (Subgroup.centerCongr eKbar).toEquiv
    simpa [hc, hz] using h0
  have hWK : GGWeylTypeData 5 (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    let eB := MonoidHom.ofInjective (redMkB_injective hN hBs3)
    have h := ggAutomizer_redMk_eq (X := K) (Bs := Bs) (H := K) hBs3 hN
      Subgroup.le_normalizer hN
    have hKrange : (redMkL K).range =
        (K.subgroupOf (Subgroup.normalizer (K : Set G))).map (redMk K) := by
      rw [redMkL, MonoidHom.range_comp, Subgroup.inclusion_range]
    have hmap : ggAutomizer ((redMkL K).range) (redMkB hN).range =
        (ggAutomizer K Bs).map (MulAut.congr eB).toMonoidHom := by
      rw [hKrange, h]
    let eMap := Subgroup.equivMapOfInjective (ggAutomizer K Bs)
      (MulAut.congr eB).toMonoidHom (MulAut.congr eB).injective
    let eAut := eMap.trans (MulEquiv.subgroupCongr hmap.symm)
    have hc := Nat.card_congr eAut.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eAut).toEquiv
    simpa [hc, hz] using hWKbar
  have hKrank : 5 = r0 + 2 := ggWeylTypeData_rank_eq hWK hfull
  have hWJ3 : GGWeylTypeData 3 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    have h0 : GGWeylTypeData 3 (Nat.card ↥(ggAutomizer J Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
      simpa [show r0 = 3 by omega] using hsurv
    simpa [hcardAut, hcardAutJbar] using h0
  have hfac : S.card.factorial = 24 ∨ S.card.factorial = 48 := by
    rcases hWJ3 with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h4, -, -⟩ | ⟨h6, -, -⟩ |
      ⟨h7, -, -⟩ | ⟨h8, -, -⟩ | ⟨hF4, -, -⟩ | ⟨hG2, -, -⟩
    · left
      norm_num at h
      exact h
    · right
      norm_num at h
      exact h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have hS4eq : S.card = 4 := by
    have hle : S.card ≤ 5 := by
      by_contra hle
      have h6 : 6 ≤ S.card := by omega
      have h720 : 720 ≤ S.card.factorial := by
        calc 720 = Nat.factorial 6 := by norm_num
          _ ≤ S.card.factorial := Nat.factorial_le h6
      rcases hfac with h | h <;> omega
    have hcases : S.card = 4 ∨ S.card = 5 := by omega
    rcases hcases with h4 | h5
    · exact h4
    · rw [h5] at hfac
      norm_num at hfac
  obtain ⟨χ, hχs, hχker, hχact⟩ :=
    exists_diagCover_blockSU hMφ hNbar hdiagφ (le_refl Bbar) S hJblock
      (by simpa [Bbar, Jbar, NX] using hBJbar)
  have hJbarLab : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
      (Jbar ⧸ Subgroup.center Jbar) := by
    have h := ggHasLabel_of_unitaryModel ⟨hKd, hχs, hχker⟩ (by omega : 3 ≤ S.card)
      (by
        intro hc
        have := congrArg Prod.fst hc
        omega)
    simpa [hS4eq] using h

  have hJperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJcompG.2.2.1
  letI : Group.IsPerfect ↥J := hJperf
  let fJfull : ↥J →* RedGrp K := (redMk K).comp (Subgroup.inclusion hJ_le_NX)
  have hfJfull_range : fJfull.range = Jbar := by
    dsimp [fJfull, Jbar, NX]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let fJ : ↥J →* Jbar := fJfull.codRestrict Jbar (fun j => by
    rw [← hfJfull_range]
    exact ⟨j, rfl⟩)
  have hfJ_surj : Function.Surjective fJ := by
    intro y
    have hy : (y : RedGrp K) ∈ fJfull.range := by
      rw [hfJfull_range]
      exact y.2
    rcases MonoidHom.mem_range.mp hy with ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj⟩
  have hfJ_ker : fJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have hj1 : fJfull j = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
      simpa [fJ] using h
    have htwo : ((j : G)) ∈ twoCenter K :=
      (redMk_eq_one_iff K (Subgroup.inclusion hJ_le_NX j)).mp hj1
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    exact (htwo.2.1 (j' : G) ((hJcompG.1.trans inf_le_left) j'.2)).symm
  have eJ : (↥J ⧸ Subgroup.center ↥J) ≃* (Jbar ⧸ Subgroup.center Jbar) :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence fJ hfJ_surj hfJ_ker
  have hJHas : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv eJ.symm hJbarLab
  let labK' : LargeEvenLabel := ⟨.twA, 5, 1⟩
  have hlabK' : LargeEvenInLambda2 labK' := by
    simpa [labK'] using hlab5
  have hhasK' : GGHasLabel labK' (↥K ⧸ Subgroup.center ↥K) := by
    simpa [labK'] using hhas5
  refine ⟨⟨.twA, 3, 1⟩, labK', ?_, hlabK', hJHas, hhasK', ?_⟩
  · unfold LargeEvenInLambda2
    norm_num
  · refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
    · rw [hp3]
      norm_num
    · rw [hp3]
      norm_num
    · simp [labK']

theorem su_exact2_right_singular_row
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧
        3 ∣ lab.rank + 1) p Bs K)
    (hLB : GGLBalanceInput)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  obtain ⟨lab, hlab, hhas, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, htag, hn, hdiv⟩ := hP.1
  have hr : 3 ≤ lab.rank := by
    have hLambda := hlab
    unfold LargeEvenInLambda2 at hLambda
    rw [htag, hn] at hLambda
    omega
  have hmark := ggInnerDiagOn_relabel hRig
    (hH.2.2.1.2 y K hH.2.2.2.2.1) hlab hhas
  by_cases h5 : lab.rank = 5
  · apply su_exact2_right_row_ggRowTwoNode_six hH hRig _ hLB hD
    exact largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => by
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨hp3, htag, hn, h5⟩, hN, hI⟩) hmark
  · have h6 : 6 ≤ lab.rank := by omega
    apply su_exact2_right_row_ggRowTwoNode_large hH hRig _ hLB hD
    exact largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => by
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨hp3, htag, hn, h6, hdiv⟩, hN, hI⟩) hmark

theorem su_not_exact2_right_of_singular_not_row
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧
        3 ∣ lab.rank + 1) p Bs K)
    (hLB : GGLBalanceInput)
    (hR : ¬ GGResRowAt ggRowTwoNode p J K) :
    ¬ GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny :=
  fun hD => hR (su_exact2_right_singular_row hH ggLabelRigidInput_holds hM hLB hD)

section CatalogueBalanceCertificates


theorem su_not_exact2_right_singular_original
    {p : ℕ} [Fact p.Prime] {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) p Bs K)
    (hR : ¬ GGResRowAt ggRowTwoNode p J K) :
    ¬ GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny :=
  su_not_exact2_right_of_singular_not_row hH hM
    (ggLBalanceInput_of_catalogueSchreier
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds) hR

end CatalogueBalanceCertificates

end Q1Certificates

end HdRo7SU

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open LineU TableBUE

public theorem _root_.CFSG.StandardType.GGResHyp.exists_unitaryModel_K_degreeFour
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnb : GGNbr p B x D J y K)
    {f : ℕ} (hf2 : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel (⟨.twA, 3, f⟩ : LargeEvenLabel)
      (K ⧸ Subgroup.center K)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : ↥(unitarySU 2 f F 4) →* K),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin 4 → F,
          LineU.ActsDiagU φ a t := by
  classical
  have hp : p.Prime := Fact.out
  have hInn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hΛ : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    simp
    omega
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  obtain ⟨hKperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF : Nat.card F = (2 ^ f) ^ 2 := by simpa [pow_two] using hFK
  have hF2 : Nat.card F = 2 ^ (2 * f) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hF
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm]
  have : CharP F 2 := charP_two_of_card hF2
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  have hBsI' : ∀ b (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) F (2 ^ f)))
        (LargeEvenGUSet (Fin 4) F (2 ^ f)) := by
    intro b hb
    exact ggLAut_mem_of_induces K θ hN hBsI hb
  have hf1 : 1 ≤ f := by omega
  have hpd : ¬ p ∣ 4 := not_dvd_four_of_dvd_two_pow_add_one hp hf1 hpq
  have hcov : LineU.UnitaryCoverAt f 4 F :=
    unitaryCoverAt_of_even hF hf2 (by norm_num : Even 4) (by norm_num : 4 ≤ 4)
  have hAe : IsElemAbelian p (ggGamma K hN).range := by
    obtain ⟨-, hBs, -, -, -⟩ := hH.1.tableB_facts
    exact isElemAbelian_range
      (fun a b : Bs => Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs a.2 b.2))
      (fun b : Bs => Subtype.ext (by simpa using hBs.2 b b.2))
      (ggGamma K hN)
  have hAI : ∀ a ∈ (ggGamma K hN).range,
      ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) F (2 ^ f)))
        (LargeEvenGUSet (Fin 4) F (2 ^ f)),
        ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsI' b b.2,
      fun l => ggBeta_ggQuotHom K hN θ b l⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel_coprime (L' := K) (K := F) (n := f) (d := 4) (p := p)
      hF hf1 (by norm_num : 3 ≤ 4) hp hpq hpd hcov (ggQuotHom_surjective θ)
      (ker_ggQuotHom θ).le hKperf hAe hAI
  exact ⟨F, hField, hFinite, inferInstance, hN, φ,
    ⟨hF, ⟨TableBU.unitaryFieldData_of_card hF hf1, hφs, hφker⟩, hdiag⟩⟩

end CFSG.StandardType
