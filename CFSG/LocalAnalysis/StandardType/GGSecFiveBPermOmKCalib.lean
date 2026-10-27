module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame

import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi
import CFSG.ClassicalInvolution.Q3.Q3MFOU4Lift
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSUDelta
import CFSG.LocalAnalysis.StandardType.GGResJUnitaryActorNormalization
import CFSG.ClassicalInvolution.AschTight.S19KUni
import CFSG.ClassicalInvolution.AschTight.S19KUniFL
import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
import CFSG.ClassicalInvolution.Balance.Theorem5Models
import CFSG.ClassicalInvolution.Q3.OddCoreCentral
import CFSG.ClassicalInvolution.Q3.Q3NMM11
import CFSG.ClassicalInvolution.Q3.Q3NMSl23
import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.Generic.S1.SymBlocksUni CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly CFSG.ClassicalInvolution.Q3.Q3MFOU4
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open scoped Matrix

variable {G : Type} [Group G] {p m f : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
  [Finite K] [CharP K 2]

private theorem coe_uniCast {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : UnitaryFieldData 2 f K)
    (g : unitarySU 2 f K m) :
    ((uniCast hK m g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) =
      blkGL (Fin.castSucc_injective m) (g : GL (Fin m) K) := rfl

private theorem iota1_injective {p f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : UnitaryFieldData 2 f K)
    {G : Type} [Group G] {Bs XU : Subgroup G}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin (m + 1))}
    {σ : ↥(unitarySU 2 f K (m + 1)) →* G} {χL : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL) :
    Function.Injective (σ.comp (uniCast hK m)) := by
  intro a b hab
  have h1 : σ (uniCast hK m (a * b⁻¹)) = 1 := by
    have hm : uniCast hK m (a * b⁻¹) = uniCast hK m a * (uniCast hK m b)⁻¹ := by
      rw [map_mul, map_inv]
    have hab' : σ (uniCast hK m a) = σ (uniCast hK m b) := hab
    rw [hm, map_mul, map_inv, hab', mul_inv_cancel]
  obtain ⟨c, hc⟩ := hσ.2.1 (uniCast hK m (a * b⁻¹)) h1
  have hmat : blkMat (Fin.castSucc) (((a * b⁻¹ : unitarySU 2 f K m) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = Matrix.diagonal (fun _ : Fin (m + 1) => c) := by
    have h := hc
    rw [coe_uniCast, coe_blkGL] at h
    exact h
  have hlast : c = 1 := by
    have h := congrFun (congrFun hmat (Fin.last m)) (Fin.last m)
    rw [blkMat_apply_of_not_mem_left _ (fun x => (Fin.castSucc_ne_last x).symm),
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    exact h.symm
  have hone : ((a * b⁻¹ : unitarySU 2 f K m) : GL (Fin m) K) = 1 := by
    apply Units.ext
    ext i j
    have h := congrFun (congrFun hmat (Fin.castSucc i)) (Fin.castSucc j)
    rw [blkMat_apply_ι (Fin.castSucc_injective m)] at h
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hlast] at h
      simpa [Matrix.one_apply] using h
    · rw [Matrix.diagonal_apply_ne _ (fun hh => hij (Fin.castSucc_injective m hh))] at h
      simpa [Matrix.one_apply, hij] using h
  have hab' : a * b⁻¹ = 1 := Subtype.ext hone
  exact mul_inv_eq_one.mp hab'

private theorem iota2_injective {p f m : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] {E : QuadExt F K (unitaryInvolution K 2 f)}
    (hK : UnitaryFieldData 2 f K) {G : Type} [Group G] {Bs XO : Subgroup G}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin (m + 1))}
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK) :
    Function.Injective (κ.comp (uniEmb E hK m)) :=
  hκ.1.comp (uniEmb_injective E hK m)

private noncomputable def frameDelta {G : Type} [Group G] {p f m : ℕ} {F K : Type} [Field F]
    [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    {Bs XU XO : Subgroup G} {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {σ : ↥(unitarySU 2 f K (m + 1)) →* G}
    {χL : Multiplicative (ZMod p) →* Kˣ} (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL)
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK)
    (hJ : (σ.comp (uniCast hK m)).range = (κ.comp (uniEmb E hK m)).range) :
    MulAut (unitarySU 2 f K m) :=
  ((MonoidHom.ofInjective (iota1_injective hK hσ)).trans (MulEquiv.subgroupCongr hJ)).trans
    (MonoidHom.ofInjective (iota2_injective hK hκ)).symm

private theorem frameDelta_apply {G : Type} [Group G] {p f m : ℕ} {F K : Type} [Field F]
    [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    {Bs XU XO : Subgroup G} {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {σ : ↥(unitarySU 2 f K (m + 1)) →* G}
    {χL : Multiplicative (ZMod p) →* Kˣ} (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL)
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK)
    (hJ : (σ.comp (uniCast hK m)).range = (κ.comp (uniEmb E hK m)).range)
    (g : unitarySU 2 f K m) :
    κ (uniEmb E hK m (frameDelta hK hσ hκ hJ g)) = σ (uniCast hK m g) := by
  have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective (iota2_injective hK hκ))
    ((MulEquiv.subgroupCongr hJ) (MonoidHom.ofInjective (iota1_injective hK hσ) g))
  exact congrArg (fun x => ((x : (κ.comp (uniEmb E hK m)).range) : G)) h

private theorem su_aut_normal_form {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ 2 ^ f = 2))
    (δ : MulAut (unitarySU 2 f K m)) :
    ∃ (A : GL (Fin m) K) (φ : K ≃+* K)
      (hA : ∀ g : unitarySU 2 f K m, A * glAut φ (g : GL (Fin m) K) * A⁻¹ ∈
        unitarySU 2 f K m),
      A ∈ primeFormUnitary h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K m) ∧
        ∀ g, δ g =
          CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := unitarySU 2 f K m
  let N : Subgroup H := (LargeEvenScalars (Fin m) K).subgroupOf H
  have : N.Normal := LargeEvenScalars.normal.subgroupOf H
  have hq' : (m, 2 ^ f) ≠ (3, 2) := fun hh => hq ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  obtain ⟨hperf, hcenter⟩ := isPerfect_and_center_unitarySU_of h hm hq'
  have : Group.IsPerfect H := hperf
  have hN : N = Subgroup.center H := by
    rw [show N = unitaryScalars h m from (unitaryScalars_eq h (by omega)).symm, hcenter]
  let δbar : MulAut (H ⧸ N) :=
    QuotientGroup.congr N N δ (by rw [hN, Subgroup.map_center_eq])
  have hδbar : ∀ x : H, δbar (InndiagSU.projU f m K x) = InndiagSU.projU f m K (δ x) :=
    fun x => QuotientGroup.congr_mk' N N δ _ x
  obtain ⟨B, hB, hsl⟩ := InndiagSU.exists_isSemilin (n := f) h hm hq δbar
  let φ : K ≃+* K := InndiagSU.fieldFactorU (n := f) h hm hq δbar
  have hsem : InndiagSU.IsSemilin (InndiagSU.projU f m K) δbar B φ := hsl
  let σB : H →* H :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B φ
      (fun g => InndiagSU.semilin_mem h hB φ g)
  have hσBcoe : ∀ g : H, ((σB g : H) : GL (Fin m) K) =
      B * glAut φ (g : GL (Fin m) K) * B⁻¹ := fun g => rfl
  have hproj : ∀ g : H, InndiagSU.projU f m K (σB g) = δbar (InndiagSU.projU f m K g) :=
    fun g => (hsem g (σB g) (hσBcoe g)).symm
  have hmem : ∀ g : H, (σB g)⁻¹ * δ g ∈ Subgroup.center H := by
    intro g
    have hker : InndiagSU.projU f m K ((σB g)⁻¹ * δ g) = 1 := by
      rw [map_mul, map_inv, hproj, hδbar, inv_mul_cancel]
    have h1 : (σB g)⁻¹ * δ g ∈ N := by
      have h2 : (σB g)⁻¹ * δ g ∈ (InndiagSU.projU f m K).ker := MonoidHom.mem_ker.mpr hker
      rwa [show (InndiagSU.projU f m K).ker = N from QuotientGroup.ker_mk' N] at h2
    rwa [← hN]
  have hval : ∀ g : H, δ g = σB g := by
    let χ : H →* Subgroup.center H :=
      { toFun := fun s => ⟨(σB s)⁻¹ * δ s, hmem s⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          have hc := Subgroup.mem_center_iff.mp (hmem a) (σB b)⁻¹
          simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
          calc (σB b)⁻¹ * (σB a)⁻¹ * (δ a * δ b)
              = (σB b)⁻¹ * ((σB a)⁻¹ * δ a) * δ b := by group
            _ = (σB a)⁻¹ * δ a * (σB b)⁻¹ * δ b := by rw [hc]
            _ = (σB a)⁻¹ * δ a * ((σB b)⁻¹ * δ b) := by group }
    have hker : χ.ker = ⊤ := by
      rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := H)]
      exact Abelianization.commutator_subset_ker χ
    intro g
    have hs : χ g = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g)
    have hs' : (σB g)⁻¹ * δ g = 1 := congrArg Subtype.val hs
    exact (inv_mul_eq_one.mp hs').symm
  exact ⟨B, φ, fun g => InndiagSU.semilin_mem h hB φ g, hB, fun g => hval g⟩

private theorem char_pow_two_pow_add_one {p f : ℕ} {K : Type} [Field K] [Fact p.Prime]
    (hpq : p ∣ 2 ^ f + 1) (χ : Multiplicative (ZMod p) →* Kˣ) (x : Multiplicative (ZMod p)) :
    ((χ x : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
  have hpa : (p : ℕ) • Multiplicative.toAdd x = 0 := by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hx : x ^ p = 1 := by
    have h : Multiplicative.ofAdd (Multiplicative.toAdd (x ^ p)) = Multiplicative.ofAdd 0 := by
      rw [toAdd_pow, hpa]
    simpa only [ofAdd_toAdd, ofAdd_zero] using h
  have h1 : (χ x : Kˣ) ^ p = 1 := by
    rw [← map_pow, hx, map_one]
  have hval : ((χ x : Kˣ) : K) ^ p = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) h1
  obtain ⟨k, hk⟩ := hpq
  rw [hk, pow_mul, hval, one_pow]

private noncomputable def frameDiag {p m : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)))
    (π : Equiv.Perm (Fin (m + 1))) (χ : Multiplicative (ZMod p) →* Kˣ) (b : ↥Bs) :
    GL (Fin m) K :=
  diagHom m fun i => χ (eta b (π (Fin.castSucc i)))

private theorem frameDiag_mem_normalizer {p f m : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    {Bs : Subgroup G} [Fact p.Prime] (hK : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1)
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (π : Equiv.Perm (Fin (m + 1)))
    (χ : Multiplicative (ZMod p) →* Kˣ) (b : ↥Bs) :
    frameDiag eta π χ b ∈ Subgroup.normalizer (unitarySU 2 f K m : Set (GL (Fin m) K)) :=
  OrdPFieldNsUD.diagHom_mem_normalizer hK fun _ => char_pow_two_pow_add_one hpq χ _

private theorem coe_frameDiag {p m : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)))
    (π : Equiv.Perm (Fin (m + 1))) (χ : Multiplicative (ZMod p) →* Kˣ) (b : ↥Bs) :
    ((frameDiag eta π χ b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      Matrix.diagonal fun i => ((χ (eta b (π (Fin.castSucc i))) : Kˣ) : K) :=
  coe_diagHom _

private theorem coe_frameDiag_inv {p m : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    {Bs : Subgroup G} (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)))
    (π : Equiv.Perm (Fin (m + 1))) (χ : Multiplicative (ZMod p) →* Kˣ) (b : ↥Bs) :
    (((frameDiag eta π χ b)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      Matrix.diagonal fun i => (((χ (eta b (π (Fin.castSucc i))) : Kˣ) : K))⁻¹ :=
  LineU.coe_inv_diag (coe_frameDiag eta π χ b)

private theorem uniEmb_apply {f m : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] {E : QuadExt F K (unitaryInvolution K 2 f)}
    (hK : UnitaryFieldData 2 f K) (g : unitarySU 2 f K m) (p : (F × F) × (Fin m → K)) :
    ((uniEmb E hK m g : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) p =
      (p.1, ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ p.2) := by
  rw [uniEmb, MonoidHom.comp_apply, suEmb_apply]
  rfl

private theorem coe_uniCast_mat {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : UnitaryFieldData 2 f K) (g : unitarySU 2 f K m) :
    (((uniCast hK m g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      blkMat (Fin.castSucc) ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
  rw [coe_uniCast, coe_blkGL]

private theorem omK_conj_uniEmb {G : Type} [Group G] {p f m : ℕ} {F K : Type} [Field F]
    [Field K] [Algebra F K] [Finite K] [CharP K 2] [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1)
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    {Bs XO : Subgroup G} {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK) (b : ↥Bs) (g : unitarySU 2 f K m) :
    (b : G) * κ (uniEmb E hK m g) * (b : G)⁻¹ =
      κ (uniEmb E hK m (LineU.conjN (frameDiag eta π χK b)
        (frameDiag_mem_normalizer hK hpq eta π χK b) g)) := by
  obtain ⟨T, hT, hc⟩ := hκ.2.2.2 b
  have hTinv : ∀ v : (F × F) × (Fin m → K),
      (((T : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))⁻¹) v =
        (v.1, fun i => (((χK (eta b (π (Fin.castSucc i))) : Kˣ) : K))⁻¹ * v.2 i) := by
    intro v
    have h1 : ((T : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (v.1, fun i => (((χK (eta b (π (Fin.castSucc i))) : Kˣ) : K))⁻¹ * v.2 i) = v := by
      rw [hT]
      refine Prod.ext rfl (funext fun i => ?_)
      exact mul_inv_cancel_left₀ (Units.ne_zero _) (v.2 i)
    have h2 := congrArg (fun z => (((T : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))⁻¹) z) h1
    simpa using h2.symm
  rw [hc]
  have hEq : T * uniEmb E hK m g * T⁻¹ =
      uniEmb E hK m (LineU.conjN (frameDiag eta π χK b)
        (frameDiag_mem_normalizer hK hpq eta π χK b) g) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hTinv v, uniEmb_apply, hT, uniEmb_apply, LineU.coe_conjN,
      Units.val_mul, Units.val_mul, coe_frameDiag, coe_frameDiag_inv, Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    refine Prod.ext rfl ?_
    have hdiag : ∀ (u y : Fin m → K),
        (Matrix.diagonal u).mulVec y = fun i => u i * y i := by
      intro u y
      funext i
      rw [Matrix.mulVec_diagonal]
    rw [hdiag, hdiag]
  rw [hEq]

private theorem uniL_conj_uniCast {G : Type} [Group G] {p f m : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1) (hK : UnitaryFieldData 2 f K)
    {Bs XU : Subgroup G} {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {σ : ↥(unitarySU 2 f K (m + 1)) →* G}
    {χL : Multiplicative (ZMod p) →* Kˣ} (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL)
    (b : ↥Bs) (g : unitarySU 2 f K m) :
    (b : G) * σ (uniCast hK m g) * (b : G)⁻¹ =
      σ (uniCast hK m (LineU.conjN (frameDiag eta π χL b)
        (frameDiag_mem_normalizer hK hpq eta π χL b) g)) := by
  obtain ⟨D, hD, hDm, hc⟩ := hσ.2.2.2 b
  rw [hc]
  have hEq : LineU.conjN D hD (uniCast hK m g) =
      uniCast hK m (LineU.conjN (frameDiag eta π χL b)
        (frameDiag_mem_normalizer hK hpq eta π χL b) g) := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [LineU.coe_conjN, Units.val_mul, Units.val_mul, hDm, LineU.coe_inv_diag hDm,
      coe_uniCast, coe_blkGL, coe_uniCast_mat, LineU.coe_conjN, Units.val_mul, Units.val_mul,
      coe_frameDiag, coe_frameDiag_inv]
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
          blkMat_apply_of_not_mem_left (i := Fin.last m) _
            (fun x => (Fin.castSucc_ne_last x).symm) (Fin.last m),
          blkMat_apply_of_not_mem_left (i := Fin.last m) _
            (fun x => (Fin.castSucc_ne_last x).symm) (Fin.last m),
          Matrix.one_apply_eq, mul_one, mul_inv_cancel₀ (Units.ne_zero _)]
      · rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
          blkMat_apply_of_not_mem_left (i := Fin.last m) _
            (fun x => (Fin.castSucc_ne_last x).symm) (Fin.castSucc b),
          blkMat_apply_of_not_mem_left (i := Fin.last m) _
            (fun x => (Fin.castSucc_ne_last x).symm) (Fin.castSucc b),
          Matrix.one_apply_ne (fun h => Fin.castSucc_ne_last b h.symm), mul_zero, zero_mul]
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
          blkMat_apply_of_not_mem_right (j := Fin.last m) _ _
            (fun y => (Fin.castSucc_ne_last y).symm),
          blkMat_apply_of_not_mem_right (j := Fin.last m) _ _
            (fun y => (Fin.castSucc_ne_last y).symm),
          Matrix.one_apply_ne (fun h => Fin.castSucc_ne_last a h), mul_zero, zero_mul]
      · rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
          blkMat_apply_ι (Fin.castSucc_injective m),
          blkMat_apply_ι (Fin.castSucc_injective m),
          Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hEq]

private theorem frameDelta_conj {G : Type} [Group G] {p f m : ℕ} {F K : Type} [Field F]
    [Field K] [Algebra F K] [Finite K] [CharP K 2] [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1)
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    {Bs XU XO : Subgroup G} {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {σ : ↥(unitarySU 2 f K (m + 1)) →* G}
    {χL : Multiplicative (ZMod p) →* Kˣ} (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL)
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK)
    (hJ : (σ.comp (uniCast hK m)).range = (κ.comp (uniEmb E hK m)).range) (b : ↥Bs)
    (g : unitarySU 2 f K m) :
    frameDelta hK hσ hκ hJ (LineU.conjN (frameDiag eta π χL b)
        (frameDiag_mem_normalizer hK hpq eta π χL b) g) =
      LineU.conjN (frameDiag eta π χK b) (frameDiag_mem_normalizer hK hpq eta π χK b)
        (frameDelta hK hσ hκ hJ g) := by
  apply iota2_injective hK hκ
  simp only [MonoidHom.comp_apply]
  rw [frameDelta_apply, ← omK_conj_uniEmb hpq hK hκ b, frameDelta_apply,
    ← uniL_conj_uniCast hpq hK hσ b g]

private theorem exists_scalar_frameDiag {G : Type} [Group G] {p f m : ℕ} {F K : Type} [Field F]
    [Field K] [Algebra F K] [Finite K] [CharP K 2] [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1)
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    {Bs XU XO : Subgroup G} {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {σ : ↥(unitarySU 2 f K (m + 1)) →* G}
    {χL : Multiplicative (ZMod p) →* Kˣ} (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL)
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK)
    (hJ : (σ.comp (uniCast hK m)).range = (κ.comp (uniEmb E hK m)).range)
    {A : GL (Fin m) K} {φ : K ≃+* K}
    (hA : ∀ g : unitarySU 2 f K m, A * glAut φ (g : GL (Fin m) K) * A⁻¹ ∈ unitarySU 2 f K m)
    (hδ : ∀ g, frameDelta hK hσ hκ hJ g =
      CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) (b : ↥Bs) :
    ∃ c : Kˣ, A * glAut φ (frameDiag eta π χL b) =
      Matrix.GeneralLinearGroup.scalar (Fin m) c * frameDiag eta π χK b * A := by
  have hδcoe : ∀ g : unitarySU 2 f K m,
      ((frameDelta hK hσ hκ hJ g : unitarySU 2 f K m) : GL (Fin m) K) =
        A * glAut φ (g : GL (Fin m) K) * A⁻¹ := by
    intro g
    rw [hδ g, CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom]
  have hcomm : ∀ s : unitarySU 2 f K m,
      ((frameDiag eta π χK b)⁻¹ * (A * glAut φ (frameDiag eta π χL b) * A⁻¹)) *
        (s : GL (Fin m) K) =
        (s : GL (Fin m) K) *
          ((frameDiag eta π χK b)⁻¹ * (A * glAut φ (frameDiag eta π χL b) * A⁻¹)) := by
    intro s
    obtain ⟨g, rfl⟩ : ∃ g : unitarySU 2 f K m, frameDelta hK hσ hκ hJ g = s :=
      ⟨(frameDelta hK hσ hκ hJ).symm s, MulEquiv.apply_symm_apply _ s⟩
    have h1 := congrArg (fun x : unitarySU 2 f K m => (x : GL (Fin m) K))
      (frameDelta_conj hpq hK hσ hκ hJ b g)
    rw [hδcoe (LineU.conjN (frameDiag eta π χL b)
        (frameDiag_mem_normalizer hK hpq eta π χL b) g),
      LineU.coe_conjN (frameDiag eta π χL b) (frameDiag_mem_normalizer hK hpq eta π χL b) g,
      LineU.coe_conjN (frameDiag eta π χK b) (frameDiag_mem_normalizer hK hpq eta π χK b)
        (frameDelta hK hσ hκ hJ g)] at h1
    have hgl : glAut φ ((frameDiag eta π χL b) * (g : GL (Fin m) K) *
        (frameDiag eta π χL b)⁻¹) =
        glAut φ (frameDiag eta π χL b) * glAut φ (g : GL (Fin m) K) *
          (glAut φ (frameDiag eta π χL b))⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hgl, hδcoe g] at h1
    have h1' : (A * glAut φ (frameDiag eta π χL b) * A⁻¹) *
        ((frameDelta hK hσ hκ hJ g : unitarySU 2 f K m) : GL (Fin m) K) *
        (A * glAut φ (frameDiag eta π χL b) * A⁻¹)⁻¹ =
        frameDiag eta π χK b * ((frameDelta hK hσ hκ hJ g : unitarySU 2 f K m) :
          GL (Fin m) K) * (frameDiag eta π χK b)⁻¹ := by
      rw [hδcoe g]
      convert h1 using 1
      group
    calc (frameDiag eta π χK b)⁻¹ * (A * glAut φ (frameDiag eta π χL b) * A⁻¹) *
          ((frameDelta hK hσ hκ hJ g : unitarySU 2 f K m) : GL (Fin m) K)
        = (frameDiag eta π χK b)⁻¹ *
            ((A * glAut φ (frameDiag eta π χL b) * A⁻¹) *
              ((frameDelta hK hσ hκ hJ g : unitarySU 2 f K m) : GL (Fin m) K) *
              (A * glAut φ (frameDiag eta π χL b) * A⁻¹)⁻¹) *
            (A * glAut φ (frameDiag eta π χL b) * A⁻¹) := by group
      _ = (frameDiag eta π χK b)⁻¹ *
            (frameDiag eta π χK b *
              ((frameDelta hK hσ hκ hJ g : unitarySU 2 f K m) : GL (Fin m) K) *
              (frameDiag eta π χK b)⁻¹) *
            (A * glAut φ (frameDiag eta π χL b) * A⁻¹) := by rw [h1']
      _ = ((frameDelta hK hσ hκ hJ g : unitarySU 2 f K m) : GL (Fin m) K) *
            ((frameDiag eta π χK b)⁻¹ *
              (A * glAut φ (frameDiag eta π χL b) * A⁻¹)) := by group
  obtain ⟨c, hc⟩ :=
    ResJUnitaryActor.exists_scalar_of_commute_unitarySU (f := f) (n := m) hK hcomm
  refine ⟨c, ?_⟩
  have hP : A * glAut φ (frameDiag eta π χL b) * A⁻¹ =
      frameDiag eta π χK b * Matrix.GeneralLinearGroup.scalar (Fin m) c := by
    have h2 : frameDiag eta π χK b *
        ((frameDiag eta π χK b)⁻¹ * (A * glAut φ (frameDiag eta π χL b) * A⁻¹)) =
        frameDiag eta π χK b * Matrix.GeneralLinearGroup.scalar (Fin m) c := by
      rw [hc]
    simpa [mul_assoc] using h2
  calc A * glAut φ (frameDiag eta π χL b)
      = A * glAut φ (frameDiag eta π χL b) * A⁻¹ * A := by group
    _ = (frameDiag eta π χK b * Matrix.GeneralLinearGroup.scalar (Fin m) c) * A := by
        rw [hP]
    _ = Matrix.GeneralLinearGroup.scalar (Fin m) c * frameDiag eta π χK b * A := by
        rw [Commute.eq (commute_scalar c (frameDiag eta π χK b))]

private theorem calib_single {K : Type} [Field K] {m : ℕ} (hm : 3 ≤ m) (A : GL (Fin m) K)
    (k : Fin m) {ζ ξ c : K} (hζ : ζ ≠ 1) (hξ : ξ ≠ 1)
    (h : (A : Matrix (Fin m) (Fin m) K) * Matrix.diagonal (fun i => if i = k then ζ else 1) =
      c • Matrix.diagonal (fun i => if i = k then ξ else 1) * (A : Matrix (Fin m) (Fin m) K)) :
    c = 1 ∧ ζ = ξ ∧
      ∀ i, i ≠ k →
        (A : Matrix (Fin m) (Fin m) K) i k = 0 ∧ (A : Matrix (Fin m) (Fin m) K) k i = 0 := by
  classical
  have hentry : ∀ i j, (A : Matrix (Fin m) (Fin m) K) i j *
      (if j = k then ζ else 1) = c * ((if i = k then ξ else 1) *
        (A : Matrix (Fin m) (Fin m) K) i j) := by
    intro i j
    have h' := congrFun (congrFun h i) j
    simpa only [Matrix.mul_diagonal, Matrix.smul_mul, Matrix.diagonal_mul, Matrix.smul_apply,
      smul_eq_mul] using h'
  have hunit : (A : Matrix (Fin m) (Fin m) K).det ≠ 0 := by
    refine Matrix.det_ne_zero_of_left_inverse
      (B := ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) ?_
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hzero_of_c : c ≠ 1 → ∀ i j, i ≠ k → j ≠ k →
      (A : Matrix (Fin m) (Fin m) K) i j = 0 := by
    intro hc i j hik hjk
    have h1 := hentry i j
    rw [if_neg hjk, if_neg hik, mul_one, one_mul] at h1
    have h2 : (1 - c) * (A : Matrix (Fin m) (Fin m) K) i j = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  have hc1 : c = 1 := by
    by_contra hc
    have hzero := hzero_of_c hc
    obtain ⟨i₁, hi₁, -⟩ := LineU.exists_not_mem_two hm k k
    obtain ⟨i₂, hi₂, hi₂'⟩ := LineU.exists_not_mem_two hm k i₁
    by_cases hxy : (A : Matrix (Fin m) (Fin m) K) i₂ k = 0 ∧
        (A : Matrix (Fin m) (Fin m) K) i₁ k = 0
    · have hv : Matrix.vecMul ((Pi.single i₁ (1 : K) : Fin m → K))
          (A : Matrix (Fin m) (Fin m) K) = 0 := by
        rw [Matrix.single_vecMul, one_smul]
        funext j
        by_cases hjk : j = k
        · rw [hjk]
          exact hxy.2
        · simpa using hzero i₁ j hi₁ hjk
      have hne : (Pi.single i₁ (1 : K) : Fin m → K) ≠ 0 := by
        intro h0
        have h1 := congrFun h0 i₁
        rw [Pi.single_eq_same] at h1
        exact one_ne_zero h1
      exact hunit ((Matrix.exists_vecMul_eq_zero_iff).mp ⟨_, hne, hv⟩)
    · push Not at hxy
      have hne : ((Pi.single i₁ ((A : Matrix (Fin m) (Fin m) K) i₂ k) : Fin m → K) -
          Pi.single i₂ ((A : Matrix (Fin m) (Fin m) K) i₁ k)) ≠ 0 := by
        intro h0
        have hx0 : (A : Matrix (Fin m) (Fin m) K) i₂ k = 0 := by
          have h1 := congrFun h0 i₁
          rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi₂'), sub_zero] at h1
          exact h1
        have hy0 : (A : Matrix (Fin m) (Fin m) K) i₁ k = 0 := by
          have h1 := congrFun h0 i₂
          rw [Pi.sub_apply, Pi.single_eq_of_ne hi₂', Pi.single_eq_same, zero_sub] at h1
          exact neg_eq_zero.mp h1
        exact hxy hx0 hy0
      have hv : Matrix.vecMul ((Pi.single i₁ ((A : Matrix (Fin m) (Fin m) K) i₂ k) :
          Fin m → K) - Pi.single i₂ ((A : Matrix (Fin m) (Fin m) K) i₁ k))
          (A : Matrix (Fin m) (Fin m) K) = 0 := by
        rw [Matrix.sub_vecMul, Matrix.single_vecMul, Matrix.single_vecMul]
        funext j
        by_cases hjk : j = k
        · subst hjk
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply, Pi.zero_apply]
          ring
        · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply, Pi.zero_apply]
          rw [hzero i₁ j hi₁ hjk, hzero i₂ j hi₂ hjk]
          ring
      exact hunit ((Matrix.exists_vecMul_eq_zero_iff).mp ⟨_, hne, hv⟩)
  have hik : ∀ i, i ≠ k → (A : Matrix (Fin m) (Fin m) K) i k = 0 := by
    intro i hi
    have h1 := hentry i k
    rw [if_pos rfl, if_neg hi, hc1, one_mul, one_mul] at h1
    have h2 : (A : Matrix (Fin m) (Fin m) K) i k * (ζ - 1) = 0 := by
      rw [mul_sub, mul_one, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hζ)
  have hki : ∀ i, i ≠ k → (A : Matrix (Fin m) (Fin m) K) k i = 0 := by
    intro i hi
    have h1 := hentry k i
    rw [if_neg hi, if_pos rfl, hc1, mul_one, one_mul] at h1
    have h2 : (1 - ξ) * (A : Matrix (Fin m) (Fin m) K) k i = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hξ))
  have hkk : (A : Matrix (Fin m) (Fin m) K) k k ≠ 0 := by
    intro h0
    have hcol : ∀ i, (A : Matrix (Fin m) (Fin m) K) i k = 0 := by
      intro i
      by_cases hik' : i = k
      · subst hik'
        exact h0
      · exact hik i hik'
    have hv : Matrix.mulVec (A : Matrix (Fin m) (Fin m) K)
        ((Pi.single k (1 : K) : Fin m → K)) = 0 := by
      rw [Matrix.mulVec_single_one]
      funext i
      exact hcol i
    have hne : (Pi.single k (1 : K) : Fin m → K) ≠ 0 := by
      intro h1
      have h2 := congrFun h1 k
      rw [Pi.single_eq_same] at h2
      exact one_ne_zero h2
    exact hunit ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨_, hne, hv⟩)
  have hxi : ζ = ξ := by
    have h1 := hentry k k
    rw [if_pos rfl, if_pos rfl, hc1, one_mul] at h1
    exact mul_left_cancel₀ hkk (by rw [h1, mul_comm])
  exact ⟨hc1, hxi, fun i hi => ⟨hik i hi, hki i hi⟩⟩

private theorem calib_of_frameDiag {G : Type} [Group G] {p m : ℕ} {K : Type} [Field K]
    [Fact p.Prime] (hm : 3 ≤ m) {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (π : Equiv.Perm (Fin (m + 1)))
    {χL χK : Multiplicative (ZMod p) →* Kˣ} (hχL : Function.Injective χL)
    (hχK : Function.Injective χK) {A : GL (Fin m) K} {φ : K ≃+* K}
    (hcal : ∀ b : ↥Bs, ∃ c : Kˣ, A * glAut φ (frameDiag eta π χL b) =
      Matrix.GeneralLinearGroup.scalar (Fin m) c * frameDiag eta π χK b * A) :
    (∀ x, φ (χL x : K) = (χK x : K)) ∧
      ∀ i j, i ≠ j → (A : Matrix (Fin m) (Fin m) K) i j = 0 := by
  classical
  let g₀ : Multiplicative (ZMod p) := Multiplicative.ofAdd 1
  have hg₀ne : g₀ ≠ 1 := by
    intro h
    have h1 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective h
    exact one_ne_zero h1
  have hχLg₀ : ((χL g₀ : Kˣ) : K) ≠ 1 := by
    intro h
    apply hg₀ne
    apply hχL
    rw [show (1 : Multiplicative (ZMod p)) = 1 from rfl, map_one]
    exact Units.ext h
  have hχKg₀ : ((χK g₀ : Kˣ) : K) ≠ 1 := by
    intro h
    apply hg₀ne
    apply hχK
    rw [show (1 : Multiplicative (ZMod p)) = 1 from rfl, map_one]
    exact Units.ext h
  have hζ : φ (((χL g₀ : Kˣ) : K)) ≠ 1 := by
    intro h
    apply hχLg₀
    apply φ.injective
    rwa [map_one]
  have hstep : ∀ k : Fin m,
      φ (((χL g₀ : Kˣ) : K)) = ((χK g₀ : Kˣ) : K) ∧
        ∀ i, i ≠ k → (A : Matrix (Fin m) (Fin m) K) i k = 0 ∧
          (A : Matrix (Fin m) (Fin m) K) k i = 0 := by
    intro k
    let b : ↥Bs := eta.symm (Pi.mulSingle (π (Fin.castSucc k)) g₀)
    have hb : ∀ i : Fin m, eta b (π (Fin.castSucc i)) = if i = k then g₀ else 1 := by
      intro i
      have h1 : eta b = Pi.mulSingle (π (Fin.castSucc k)) g₀ := MulEquiv.apply_symm_apply eta _
      rw [h1, Pi.mulSingle_apply]
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hik, if_neg (fun h => hik (Fin.castSucc_injective m (π.injective h)))]
    obtain ⟨c, hc⟩ := hcal b
    have hDL : ((glAut φ (frameDiag eta π χL b) : GL (Fin m) K) :
        Matrix (Fin m) (Fin m) K) =
        Matrix.diagonal (fun i => if i = k then φ (((χL g₀ : Kˣ) : K)) else 1) := by
      rw [coe_glAut, coe_frameDiag, Matrix.diagonal_map (map_zero φ)]
      congr 1
      funext i
      rw [hb i]
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik]
      · rw [if_neg hik, if_neg hik]
        simp
    have hDK : ((frameDiag eta π χK b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        Matrix.diagonal (fun i => if i = k then ((χK g₀ : Kˣ) : K) else 1) := by
      rw [coe_frameDiag]
      congr 1
      funext i
      rw [hb i]
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik]
      · rw [if_neg hik, if_neg hik]
        simp
    have hcs : (Matrix.GeneralLinearGroup.scalar (Fin m) c : Matrix (Fin m) (Fin m) K) =
        (c : K) • (1 : Matrix (Fin m) (Fin m) K) := by
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      rw [Matrix.scalar_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
    have hcmat : (A : Matrix (Fin m) (Fin m) K) *
        ((glAut φ (frameDiag eta π χL b) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        (Matrix.GeneralLinearGroup.scalar (Fin m) c : Matrix (Fin m) (Fin m) K) *
          ((frameDiag eta π χK b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
          (A : Matrix (Fin m) (Fin m) K) := by
      have h := congrArg (fun x : GL (Fin m) K => (x : Matrix (Fin m) (Fin m) K)) hc
      simpa only [Units.val_mul] using h
    have hcal' : (A : Matrix (Fin m) (Fin m) K) *
        Matrix.diagonal (fun i => if i = k then φ (((χL g₀ : Kˣ) : K)) else 1) =
        (c : K) • Matrix.diagonal (fun i => if i = k then ((χK g₀ : Kˣ) : K) else 1) *
          (A : Matrix (Fin m) (Fin m) K) := by
      calc (A : Matrix (Fin m) (Fin m) K) *
            Matrix.diagonal (fun i => if i = k then φ (((χL g₀ : Kˣ) : K)) else 1)
          = (A : Matrix (Fin m) (Fin m) K) *
              ((glAut φ (frameDiag eta π χL b) : GL (Fin m) K) :
                Matrix (Fin m) (Fin m) K) := by rw [hDL]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin m) c : Matrix (Fin m) (Fin m) K) *
              ((frameDiag eta π χK b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
              (A : Matrix (Fin m) (Fin m) K) := hcmat
        _ = ((c : K) • (1 : Matrix (Fin m) (Fin m) K)) *
              ((frameDiag eta π χK b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
              (A : Matrix (Fin m) (Fin m) K) := by rw [hcs]
        _ = (c : K) • Matrix.diagonal
              (fun i => if i = k then ((χK g₀ : Kˣ) : K) else 1) *
              (A : Matrix (Fin m) (Fin m) K) := by
            rw [hDK, Matrix.smul_mul, Matrix.one_mul]
    obtain ⟨-, hζξ, hv⟩ := calib_single hm A k hζ hχKg₀ hcal'
    exact ⟨hζξ, hv⟩
  have hg₀ : φ (((χL g₀ : Kˣ) : K)) = ((χK g₀ : Kˣ) : K) :=
    (hstep ⟨0, by omega⟩).1
  have hgen : ∀ x : Multiplicative (ZMod p),
      φ (((χL x : Kˣ) : K)) = ((χK x : Kˣ) : K) := by
    intro x
    have hx : x = g₀ ^ (Multiplicative.toAdd x).val := by
      have ha : ((Multiplicative.toAdd x).val : ℕ) • (1 : ZMod p) = Multiplicative.toAdd x := by
        rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      calc x = Multiplicative.ofAdd (Multiplicative.toAdd x) := (ofAdd_toAdd x).symm
        _ = Multiplicative.ofAdd ((Multiplicative.toAdd x).val • (1 : ZMod p)) := by rw [ha]
        _ = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd x).val :=
            ofAdd_nsmul _ _
        _ = g₀ ^ (Multiplicative.toAdd x).val := rfl
    have hχLx : ((χL x : Kˣ) : K) =
        (((χL g₀ : Kˣ) : K)) ^ (Multiplicative.toAdd x).val := by
      conv_lhs => rw [hx]
      rw [map_pow, Units.val_pow_eq_pow_val]
    have hχKx : ((χK x : Kˣ) : K) =
        (((χK g₀ : Kˣ) : K)) ^ (Multiplicative.toAdd x).val := by
      conv_lhs => rw [hx]
      rw [map_pow, Units.val_pow_eq_pow_val]
    rw [hχLx, hχKx, map_pow, hg₀]
  exact ⟨hgen, fun i j hij => ((hstep j).2 i hij).1⟩

private theorem exists_diagHom_of_diag {f m : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData 2 f K) {A : GL (Fin m) K}
    (hA : A ∈ primeFormUnitary hK (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K m))
    (hdiag : ∀ i j, i ≠ j → (A : Matrix (Fin m) (Fin m) K) i j = 0) :
    ∃ a : Fin m → Kˣ, A = diagHom m a ∧ ∀ i, ((a i : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
  have hmem : ((A : Matrix (Fin m) (Fin m) K).map hK.bar)ᵀ *
      (1 : Matrix (Fin m) (Fin m) K) * (A : Matrix (Fin m) (Fin m) K) = 1 := by
    have h := mem_primeFormUnitary.mp hA
    simpa using h
  have hnorm : ∀ i, hK.bar ((A : Matrix (Fin m) (Fin m) K) i i) *
      ((A : Matrix (Fin m) (Fin m) K) i i) = 1 := by
    intro i
    have h := congrFun (congrFun hmem i) i
    rw [Matrix.mul_one, Matrix.mul_apply] at h
    have hsingle : (∑ j, ((A : Matrix (Fin m) (Fin m) K).map hK.bar)ᵀ i j *
        (A : Matrix (Fin m) (Fin m) K) j i) =
        ((A : Matrix (Fin m) (Fin m) K).map hK.bar)ᵀ i i *
          (A : Matrix (Fin m) (Fin m) K) i i := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _ hji
        simp [Matrix.transpose_apply, Matrix.map_apply, hdiag j i hji]
      · intro hi
        simp at hi
    rw [hsingle] at h
    simpa [Matrix.transpose_apply, Matrix.map_apply] using h
  have hne : ∀ i, (A : Matrix (Fin m) (Fin m) K) i i ≠ 0 := by
    intro i h0
    have h := hnorm i
    rw [h0] at h
    simp at h
  refine ⟨fun i => Units.mk0 ((A : Matrix (Fin m) (Fin m) K) i i) (hne i), ?_, ?_⟩
  · apply Units.ext
    ext i j
    rw [coe_diagHom]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Units.val_mk0]
    · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  · intro i
    rw [Units.val_mk0]
    have h := hnorm i
    rw [hK.bar_apply, ← pow_succ] at h
    exact h

private theorem glAut_symm_glAut {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (φ : K ≃+* K) (g : GL ι K) : glAut φ.symm (glAut φ g) = g := by
  apply Units.ext
  ext i j
  rw [coe_glAut, coe_glAut, Matrix.map_apply, Matrix.map_apply]
  simp

private theorem glAut_diagHom {n : ℕ} {K : Type} [Field K] (φ : K ≃+* K) (u : Fin n → Kˣ) :
    glAut φ (diagHom n u) = diagHom n (fun i => Units.map (φ : K →* K) (u i)) := by
  apply Units.ext
  ext i j
  rw [coe_glAut, coe_diagHom, coe_diagHom]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Units.coe_map]
    rfl
  · rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij,
      map_zero]

private theorem blkMat_map_of_ringEquiv {k m : ℕ} {F : Type} [Field F] {ι : Fin k → Fin m}
    (φ : F ≃+* F) (A : Matrix (Fin k) (Fin k) F) :
    (blkMat ι A).map φ = blkMat ι (A.map φ) := by
  have hL : (selL F ι).map φ = selL F ι := by
    ext a j
    simp only [Matrix.map_apply, selL_apply]
    split_ifs <;> simp
  have hLt : ((selL F ι)ᵀ).map φ = (selL F ι)ᵀ := by rw [Matrix.transpose_map, hL]
  have hN : (A - 1).map φ = A.map φ - 1 := by
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ)]
  unfold blkMat
  rw [Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ),
    Matrix.map_mul, Matrix.map_mul, hL, hLt, hN]

private theorem diagHom_lastCases {m : ℕ} {K : Type} [Field K] (u : Fin m → Kˣ) :
    diagHom (m + 1) (Fin.lastCases (1 : Kˣ) u) =
      blkGL (Fin.castSucc_injective m) (diagHom m u) := by
  apply Units.ext
  ext i j
  rw [coe_diagHom, coe_blkGL]
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [Matrix.diagonal_apply_eq, Fin.lastCases_last,
        blkMat_apply_of_not_mem_left _ (fun x => (Fin.castSucc_ne_last x).symm) (Fin.last m),
        Matrix.one_apply_eq]
      simp
    · rw [Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last b).symm,
        blkMat_apply_of_not_mem_left _ (fun x => (Fin.castSucc_ne_last x).symm) (Fin.castSucc b),
        Matrix.one_apply_ne (fun h => Fin.castSucc_ne_last b h.symm)]
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last a),
        blkMat_apply_of_not_mem_right _ _ (fun y => (Fin.castSucc_ne_last y).symm),
        Matrix.one_apply_ne (fun h => Fin.castSucc_ne_last a h)]
    · rw [blkMat_apply_ι (Fin.castSucc_injective m), coe_diagHom]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.diagonal_apply_eq, Fin.lastCases_castSucc, Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ (fun h => hab (Fin.castSucc_injective m h)),
          Matrix.diagonal_apply_ne _ hab]

theorem exists_uniLFrame_calibrated [Finite G] [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1)
    {E : QuadExt F K (unitaryInvolution K 2 f)} (hK : UnitaryFieldData 2 f K)
    (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ 2 ^ f = 2))
    {Bs XU XO : Subgroup G} {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin (m + 1))} {σ : ↥(unitarySU 2 f K (m + 1)) →* G}
    {χL : Multiplicative (ZMod p) →* Kˣ} (hσ : GGSecFiveBPermUniLFrame Bs XU eta π σ χL)
    {κ : normOmega E m →* G} {χK : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs XO eta π κ χK)
    (hJ : (σ.comp (uniCast hK m)).range = (κ.comp (uniEmb E hK m)).range) :
    ∃ σ' : ↥(unitarySU 2 f K (m + 1)) →* G,
      GGSecFiveBPermUniLFrame Bs XU eta π σ' χK ∧
        ∀ g, κ (uniEmb E hK m g) = σ' (uniCast hK m g) := by
  classical
  obtain ⟨A, φ, hA, hAU, hδ⟩ := su_aut_normal_form hK hm hq (frameDelta hK hσ hκ hJ)
  obtain ⟨hφχ, hdiag⟩ := calib_of_frameDiag hm eta π hσ.2.2.1 hκ.2.2.1
    (exists_scalar_frameDiag hpq hK hσ hκ hJ hA hδ)
  obtain ⟨a, rfl, ha⟩ := exists_diagHom_of_diag hK hAU hdiag
  let t : Fin (m + 1) → Kˣ :=
    Fin.lastCases (1 : Kˣ) (fun i => (Units.map (φ.symm : K →* K) (a i))⁻¹)
  set Â : GL (Fin (m + 1)) K := diagHom (m + 1) t with hÂdef
  have ha' : ∀ i, (a i) ^ (2 ^ f + 1) = 1 := fun i => Units.ext (by simpa using ha i)
  have ht : ∀ i, ((t i : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
    intro i
    have h : (t i) ^ (2 ^ f + 1) = 1 := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [t]
        rw [Fin.lastCases_last]
        simp
      · simp only [t]
        rw [Fin.lastCases_castSucc, inv_pow, ← map_pow, ha' j, map_one, inv_one]
    simpa using congrArg (fun u : Kˣ => (u : K)) h
  have hÂnorm : Â ∈ Subgroup.normalizer
      (unitarySU 2 f K (m + 1) : Set (GL (Fin (m + 1)) K)) :=
    OrdPFieldNsUD.diagHom_mem_normalizer hK ht
  have hglAut_mem : ∀ g : unitarySU 2 f K (m + 1),
      glAut φ.symm (g : GL (Fin (m + 1)) K) ∈ unitarySU 2 f K (m + 1) := by
    intro g
    have h := InndiagSU.semilin_mem (h := hK) (B := (1 : GL (Fin (m + 1)) K))
      (one_mem _) (φ := φ.symm) (u := g)
    simpa using h
  have hΘ : ∀ g : unitarySU 2 f K (m + 1),
      Â * glAut φ.symm (g : GL (Fin (m + 1)) K) * Â⁻¹ ∈ unitarySU 2 f K (m + 1) := by
    intro g
    exact (Subgroup.mem_normalizer_iff.mp hÂnorm (glAut φ.symm (g : GL (Fin (m + 1)) K))).mp
      (hglAut_mem g)
  let Θ : unitarySU 2 f K (m + 1) →* unitarySU 2 f K (m + 1) :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom Â φ.symm hΘ
  let σ' : unitarySU 2 f K (m + 1) →* G := σ.comp Θ
  have hΘcoe : ∀ g : unitarySU 2 f K (m + 1),
      ((Θ g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) =
        Â * glAut φ.symm (g : GL (Fin (m + 1)) K) * Â⁻¹ := fun g => rfl
  have hΘsurj : Function.Surjective Θ := by
    intro s
    have hmem : Â⁻¹ * (s : GL (Fin (m + 1)) K) * Â ∈ unitarySU 2 f K (m + 1) := by
      refine (Subgroup.mem_normalizer_iff.mp hÂnorm _).mpr ?_
      have : Â * (Â⁻¹ * (s : GL (Fin (m + 1)) K) * Â) * Â⁻¹ =
          (s : GL (Fin (m + 1)) K) := by group
      rw [this]
      exact s.2
    have hmem2 : glAut φ (Â⁻¹ * (s : GL (Fin (m + 1)) K) * Â) ∈
        unitarySU 2 f K (m + 1) := by
      have h := InndiagSU.semilin_mem (h := hK) (B := (1 : GL (Fin (m + 1)) K))
        (one_mem _) (φ := φ) (u := ⟨_, hmem⟩)
      simpa using h
    refine ⟨⟨glAut φ (Â⁻¹ * (s : GL (Fin (m + 1)) K) * Â), hmem2⟩, ?_⟩
    apply Subtype.ext
    rw [hΘcoe, glAut_symm_glAut]
    group
  refine ⟨σ', ?_, ?_⟩
  · refine ⟨?_, ?_, hκ.2.2.1, ?_⟩
    · rw [show σ' = σ.comp Θ from rfl, MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr hΘsurj, Subgroup.map_top]
      exact hσ.1
    · intro g hg
      have hg' : σ (Θ g) = 1 := hg
      obtain ⟨c, hc⟩ := hσ.2.1 (Θ g) hg'
      have hc0 : c ≠ 0 := by
        intro h0
        have hdet : (((Θ g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K).det ≠ 0 := by
          have hB : ((((Θ g)⁻¹ : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
              (((Θ g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
            have e : (((Θ g)⁻¹ : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) =
                (((Θ g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K))⁻¹ := rfl
            rw [e, ← Units.val_mul, inv_mul_cancel, Units.val_one]
          exact Matrix.det_ne_zero_of_left_inverse hB
        rw [hc, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin] at hdet
        exact hdet (by rw [h0]; exact zero_pow (by omega))
      refine ⟨φ c, ?_⟩
      set S : GL (Fin (m + 1)) K :=
        Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (Units.mk0 c hc0) with hSdef
      have hSmat : ((S : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
          Matrix.diagonal (fun _ : Fin (m + 1) => c) := by
        rw [hSdef, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
      have hcGL : ((Θ g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) = S := by
        apply Units.ext
        rw [hSmat]
        exact hc
      have hSg : Â * glAut φ.symm ((g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) *
          Â⁻¹ = S := by
        rw [← hΘcoe g, hcGL]
      have hgl : glAut φ.symm ((g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) = S := by
        calc glAut φ.symm ((g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K)
            = Â⁻¹ * (Â * glAut φ.symm ((g : unitarySU 2 f K (m + 1)) :
                GL (Fin (m + 1)) K) * Â⁻¹) * Â := by group
          _ = Â⁻¹ * S * Â := by rw [hSg]
          _ = S := by
              rw [hSdef, mul_assoc,
                (Commute.eq (commute_scalar (Units.mk0 c hc0) Â)).symm]
              group
      have hgS : ((g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) = glAut φ S := by
        have h := congrArg (glAut φ) hgl
        have h2 : glAut φ (glAut φ.symm ((g : unitarySU 2 f K (m + 1)) :
            GL (Fin (m + 1)) K)) = ((g : unitarySU 2 f K (m + 1)) :
              GL (Fin (m + 1)) K) := by
          simpa using glAut_symm_glAut (φ := φ.symm) ((g : unitarySU 2 f K (m + 1)) :
            GL (Fin (m + 1)) K)
        rw [h2] at h
        exact h
      rw [hgS, coe_glAut, hSmat, Matrix.diagonal_map (map_zero φ)]
    · intro b
      let D : GL (Fin (m + 1)) K := diagHom (m + 1) (fun k => χK (eta b (π k)))
      have hD : D ∈ Subgroup.normalizer
          (unitarySU 2 f K (m + 1) : Set (GL (Fin (m + 1)) K)) :=
        OrdPFieldNsUD.diagHom_mem_normalizer hK
          (fun k => char_pow_two_pow_add_one hpq χK _)
      refine ⟨D, hD, ?_, ?_⟩
      · exact coe_diagHom _
      · intro s
        obtain ⟨D0, hD0, hD0m, hD0c⟩ := hσ.2.2.2 b
        have hDeq : D0 = diagHom (m + 1) (fun k => χL (eta b (π k))) := by
          apply Units.ext
          rw [hD0m, coe_diagHom]
        have hsymm : ∀ x : Multiplicative (ZMod p),
            (φ.symm : K →* K) ((χK x : Kˣ) : K) = ((χL x : Kˣ) : K) := by
          intro x
          rw [← hφχ x]
          exact φ.symm_apply_apply _
        have hunits : ∀ k : Fin (m + 1),
            Units.map (φ.symm : K →* K) (χK (eta b (π k))) = χL (eta b (π k)) := by
          intro k
          apply Units.ext
          simpa only [Units.coe_map] using hsymm (eta b (π k))
        have hrel : (diagHom (m + 1) (fun k => χL (eta b (π k))) : GL (Fin (m + 1)) K) =
            Â * glAut φ.symm D * Â⁻¹ := by
          rw [show D = diagHom (m + 1) (fun k => χK (eta b (π k))) from rfl, glAut_diagHom]
          simp only [hunits]
          rw [hÂdef, ← map_inv, ← map_mul, ← map_mul]
          congr 1
          funext k
          simp only [Pi.mul_apply, Pi.inv_apply]
          rw [mul_comm (t k) (χL (eta b (π k))), mul_assoc, mul_inv_cancel, mul_one]
        have h1 : ((LineU.conjN D0 hD0 (Θ s) : unitarySU 2 f K (m + 1)) :
            GL (Fin (m + 1)) K) = D0 * (Â * glAut φ.symm (s : GL (Fin (m + 1)) K) * Â⁻¹) *
              D0⁻¹ := by
          rw [LineU.coe_conjN, hΘcoe]
        have h2 : ((Θ (LineU.conjN D hD s) : unitarySU 2 f K (m + 1)) :
            GL (Fin (m + 1)) K) =
              Â * glAut φ.symm (D * (s : GL (Fin (m + 1)) K) * D⁻¹) * Â⁻¹ := by
          rw [hΘcoe, LineU.coe_conjN]
        have hconj : LineU.conjN D0 hD0 (Θ s) = Θ (LineU.conjN D hD s) := by
          apply Subtype.ext
          rw [h1, h2, hDeq, hrel, map_mul, map_mul, map_inv]
          group
        calc (b : G) * σ' s * (b : G)⁻¹
            = σ (LineU.conjN D0 hD0 (Θ s)) := hD0c (Θ s)
          _ = σ (Θ (LineU.conjN D hD s)) := by rw [hconj]
          _ = σ' (LineU.conjN D hD s) := rfl
  · intro g
    let a' : Fin m → Kˣ := fun i => (Units.map (φ.symm : K →* K) (a i))⁻¹
    let A' : GL (Fin m) K := diagHom m a'
    have hta' : ∀ i : Fin m, ((a' i : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
      intro i
      have h := ht (Fin.castSucc i)
      simp only [t, Fin.lastCases_castSucc] at h
      simpa [a'] using h
    have hA'norm : A' ∈ Subgroup.normalizer (unitarySU 2 f K m : Set (GL (Fin m) K)) :=
      OrdPFieldNsUD.diagHom_mem_normalizer hK hta'
    have hgφ : glAut φ.symm ((g : unitarySU 2 f K m) : GL (Fin m) K) ∈ unitarySU 2 f K m := by
      have h := InndiagSU.semilin_mem (h := hK) (B := (1 : GL (Fin m) K)) (one_mem _)
        (φ := φ.symm) (u := g)
      simpa using h
    let g' : unitarySU 2 f K m :=
      LineU.conjN A' hA'norm ⟨glAut φ.symm ((g : unitarySU 2 f K m) : GL (Fin m) K), hgφ⟩
    have hg'coe : ((g' : unitarySU 2 f K m) : GL (Fin m) K) =
        A' * glAut φ.symm ((g : unitarySU 2 f K m) : GL (Fin m) K) * A'⁻¹ :=
      LineU.coe_conjN A' hA'norm ⟨glAut φ.symm ((g : unitarySU 2 f K m) : GL (Fin m) K), hgφ⟩
    have hφa : ∀ i : Fin m, Units.map (φ : K →* K)
        ((Units.map (φ.symm : K →* K) (a i))⁻¹) = (a i)⁻¹ := by
      intro i
      rw [map_inv]
      congr 1
      apply Units.ext
      rw [Units.coe_map, Units.coe_map]
      exact φ.apply_symm_apply _
    have hφA' : glAut φ A' = (diagHom m a)⁻¹ := by
      rw [show A' = diagHom m a' from rfl, glAut_diagHom, ← map_inv]
      congr 1
      funext i
      simpa only [Pi.inv_apply] using hφa i
    have hδg' : frameDelta hK hσ hκ hJ g' = g := by
      apply Subtype.ext
      rw [hδ g', CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
        hg'coe, map_mul, map_mul, map_inv, hφA']
      have h2 : glAut φ (glAut φ.symm ((g : unitarySU 2 f K m) : GL (Fin m) K)) =
          ((g : unitarySU 2 f K m) : GL (Fin m) K) := by
        simpa using glAut_symm_glAut (φ := φ.symm) ((g : unitarySU 2 f K m) :
          GL (Fin m) K)
      rw [h2]
      group
    have hÂblk : Â = blkGL (Fin.castSucc_injective m) A' := by
      rw [hÂdef]
      exact diagHom_lastCases a'
    have hglAut_blk : ∀ x : GL (Fin m) K,
        glAut φ.symm (blkGL (Fin.castSucc_injective m) x) =
          blkGL (Fin.castSucc_injective m) (glAut φ.symm x) := by
      intro x
      apply Units.ext
      rw [coe_glAut, coe_blkGL, blkMat_map_of_ringEquiv, coe_blkGL, coe_glAut]
    have hΘg : Θ (uniCast hK m g) = uniCast hK m g' := by
      apply Subtype.ext
      rw [hΘcoe, coe_uniCast, coe_uniCast, hglAut_blk, hÂblk, ← map_mul, ← map_inv,
        ← map_mul, hg'coe]
    calc κ (uniEmb E hK m g)
        = κ (uniEmb E hK m (frameDelta hK hσ hκ hJ g')) := by rw [hδg']
      _ = σ (uniCast hK m g') := frameDelta_apply hK hσ hκ hJ g'
      _ = σ (Θ (uniCast hK m g)) := by rw [hΘg]
      _ = σ' (uniCast hK m g) := rfl

end CFSG.StandardType

end
