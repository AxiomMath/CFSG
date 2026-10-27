
module

public import CFSG.Sporadic.Co1Block.PermBase
import all CFSG.Sporadic.Co1Block.PermBase

public import CFSG.Sporadic.Co1Block.PermCheck
public import CFSG.Sporadic.Schreier.Co1AutTrivial
public import CFSG.Monster.B.Co2.PermArr
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Co1Block.PermCheckInputs
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabFix
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import Certificates.Data.CFSGNative.Co1.Data

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective toVecD_zero rowsMatrix rowsMatrix_apply
  rowsMatrix_mulRows rowsMatrix_idRows)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native Matrix

theorem perm_facts :
    certVecs[0]! = CFSG.Sporadic.Co1Schreier.Native.stabVec 0 ∧
    mulRows 24 (CFSG.Sporadic.Co1Schreier.Native.inv (certBasisRows certVecs))
      (certBasisRows certVecs) = idRows 24 ∧
    (∀ i < 98280, certVecs[i]! < 2 ^ 24 ∧ certVecs[i]! ≠ 0 ∧
      ((posTable 24 certVecs)[certVecs[i]!]!).toNat = i ∧
      vecMulN 24 (transposeRows 24 CFSG.Sporadic.Co1Schreier.Native.aR) certVecs[i]! =
        certVecs[(certAct 0)[i]!]! ∧
      vecMulN 24 (transposeRows 24 CFSG.Sporadic.Co1Schreier.Native.bR) certVecs[i]! =
        certVecs[(certAct 1)[i]!]!) ∧
    isInvA 98280 (certAct 0) (invCand 98280 (certAct 0)) = true ∧
    isInvA 98280 (certAct 1) (invCand 98280 (certAct 1)) = true := by
  have h := perm_check
  simp only [permCheckOf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h0⟩, hb⟩, hall⟩, h1⟩, h2⟩ := h
  exact ⟨h0, hb, fun i hi => by
    obtain ⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩ := hall i hi
    exact ⟨h3, h4, h5, h6, h7⟩, h1, h2⟩

theorem certVecs_lt
    {i : ℕ} (hi : i < 98280) : certVecs[i]! < 2 ^ 24 := (perm_facts.2.2.1 i hi).1

theorem certVec_ne_zero
    {i : ℕ} (hi : i < 98280) : certVec i ≠ 0 := by
  intro h
  rw [certVec, ← toVecD_zero 24] at h
  exact (perm_facts.2.2.1 i hi).2.1 (toVecD_injective (certVecs_lt hi) (by norm_num) h)

theorem certVec_injective {i j : ℕ} (hi : i < 98280) (hj : j < 98280)
    (h : certVec i = certVec j) : i = j := by
  have e := toVecD_injective (certVecs_lt hi) (certVecs_lt hj) h
  rw [← (perm_facts.2.2.1 i hi).2.2.1, ← (perm_facts.2.2.1 j hj).2.2.1, e]

theorem certVec_zero : certVec 0 = stabVecOf 0 := by
  rw [certVec, perm_facts.1]
  rfl

theorem certBasis_isUnit :
    IsUnit (rowsMatrix 24 (certBasisRows certVecs)) := by
  have h := congrArg (rowsMatrix 24) perm_facts.2.1
  rw [rowsMatrix_mulRows, rowsMatrix_idRows] at h
  exact IsUnit.of_mul_eq_one_right _ h

theorem certBasis_linearIndependent :
    LinearIndependent (ZMod 2) fun t : Fin 24 => certVec (certBasisIdx.getD t 0) := by
  have h := Matrix.linearIndependent_rows_iff_isUnit.2 certBasis_isUnit
  have e : (rowsMatrix 24 (certBasisRows certVecs)).row =
      fun t : Fin 24 => certVec (certBasisIdx.getD t 0) :=
    funext rowsMatrix_certBasisRows_row
  rwa [e] at h

theorem certBasis_span :
    Submodule.span (ZMod 2) (Set.range fun t : Fin 24 => certVec (certBasisIdx.getD t 0)) = ⊤ :=
  certBasis_linearIndependent.span_eq_top_of_card_eq_finrank
    (by rw [Fintype.card_fin, Module.finrank_fin_fun])

theorem rep_certGen
    {k : ℕ} (hk : k < 2) : Rep 98280 (certAct k) (certGen k) := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · exact (rep_permOfArr perm_facts.2.2.2.1).1
  · exact (rep_permOfArr perm_facts.2.2.2.2).1

theorem A₁_mulVec (i : Fin 98280) :
    ((A₁ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec i = certVec (certGen 0 i) := by
  rw [certVec, MRep.mulVec rep_A₁, Native.act, (perm_facts.2.2.1 i i.2).2.2.2.1,
    rep_certGen (k := 0) (by norm_num) i]
  rfl

theorem A₂_mulVec (i : Fin 98280) :
    ((A₂ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec i = certVec (certGen 1 i) := by
  rw [certVec, MRep.mulVec rep_A₂, Native.act, (perm_facts.2.2.1 i i.2).2.2.2.2,
    rep_certGen (k := 1) (by norm_num) i]
  rfl

theorem ncard_certX : certX.ncard = 98280 := by
  rw [certX_eq_range, ← Set.image_univ, Set.ncard_image_of_injective _ fun i j h =>
    Fin.ext (certVec_injective i.2 j.2 h), Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem mulVec_mem_certX
    {g : GL24} (hg : g ∈ GA) {w : Vec24} (hw : w ∈ certX) :
    ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ certX := by
  refine mulVec_mem_of_closure certX_finite ?_ g hg w hw
  intro x hx v hv
  obtain ⟨i, hi, hv⟩ := hv
  rw [hv]
  rcases Set.mem_insert_iff.1 hx with h | h
  · rw [h]
    exact ⟨_, (certGen 0 ⟨i, hi⟩).2, A₁_mulVec ⟨i, hi⟩⟩
  · rw [Set.mem_singleton_iff.1 h]
    exact ⟨_, (certGen 1 ⟨i, hi⟩).2, A₂_mulVec ⟨i, hi⟩⟩

theorem certX_eq_co1X :
    certX = co1X := by
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ (by rw [ncard_certX, ncard_co1X]) certX_finite
  rw [co1X_eq_kOrbit]
  rintro _ ⟨g, hg, rfl⟩
  exact mulVec_mem_certX hg ⟨0, by norm_num, certVec_zero.symm⟩

theorem certVec_mem_co1X
    (i : Fin 98280) : certVec i ∈ co1X := by
  rw [← certX_eq_co1X]
  exact ⟨i, i.2, rfl⟩

section Restriction

attribute [local instance] xAct

@[expose] noncomputable def certXEquiv :
    Fin 98280 ≃ co1X :=
  Equiv.ofBijective (fun i => ⟨certVec i, certVec_mem_co1X i⟩)
    ⟨fun i j h => Fin.ext (certVec_injective i.2 j.2 (congrArg Subtype.val h)), by
      rintro ⟨v, hv⟩
      rw [← certX_eq_co1X] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      exact ⟨⟨i, hi⟩, rfl⟩⟩

theorem certXEquiv_apply
    (i : Fin 98280) : (certXEquiv i : Vec24) = certVec i := rfl

@[expose] noncomputable def certRhoHom :
    GA →* Equiv.Perm (Fin 98280) :=
  certXEquiv.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom GA co1X)

theorem certRhoHom_apply
    (g : GA) (i : Fin 98280) :
    certRhoHom g i = certXEquiv.symm (g • certXEquiv i) := rfl

theorem certVec_rho
    (g : GA) (i : Fin 98280) :
    certVec (certRhoHom g i) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec i := by
  have h := congrArg Subtype.val (certXEquiv.apply_symm_apply (g • certXEquiv i))
  rw [← certRhoHom_apply, certXEquiv_apply, xAct_val, certXEquiv_apply] at h
  exact h

theorem certRhoHom_injective :
    Function.Injective certRhoHom := by
  intro g h hgh
  have hf := xAct_faithful
  refine hf.eq_of_smul_eq_smul fun x => ?_
  obtain ⟨i, rfl⟩ := certXEquiv.surjective x
  have := congrArg (fun σ : Equiv.Perm (Fin 98280) => certXEquiv (σ i)) hgh
  simpa only [certRhoHom_apply, Equiv.apply_symm_apply] using this

theorem certRhoHom_seed
    {g : GA} {k : ℕ}
    (hg : ∀ i : Fin 98280, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec i =
      certVec (certGen k i)) : certRhoHom g = certGen k := by
  refine Equiv.ext fun i => Fin.ext (certVec_injective (Fin.isLt _) (Fin.isLt _) ?_)
  rw [certVec_rho, hg]

theorem certRhoHom_A₁ :
    certRhoHom ⟨A₁, A₁_mem⟩ = certGen 0 :=
  certRhoHom_seed A₁_mulVec

theorem certRhoHom_A₂ :
    certRhoHom ⟨A₂, A₂_mem⟩ = certGen 1 :=
  certRhoHom_seed A₂_mulVec

theorem certRhoHom_range :
    certRhoHom.range = certP := by
  rw [MonoidHom.range_eq_map, ← closure_A₁_A₂, MonoidHom.map_closure, Set.image_pair,
    certRhoHom_A₁, certRhoHom_A₂]
  rfl

@[expose] noncomputable def certRho :
    GA ≃* certP :=
  (MonoidHom.ofInjective certRhoHom_injective).trans (MulEquiv.subgroupCongr certRhoHom_range)

theorem certRho_apply
    (g : GA) : (certRho g : Equiv.Perm (Fin 98280)) = certRhoHom g := rfl

end Restriction

@[expose] noncomputable def certCo1Equiv :
    CFSG.Blueprint.NativeSporadic.Co1 ≃* certP :=
  co1MatEquiv.trans certRho

theorem fam_co1_faithful_permutation_action :
    (∀ i < 98280, certVec i ≠ 0) ∧
    (∀ i < 98280, ∀ j < 98280, certVec i = certVec j → i = j) ∧
    certBasisIdx =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 26] ∧
    LinearIndependent (ZMod 2) (fun t : Fin 24 => certVec (certBasisIdx.getD t 0)) ∧
    Submodule.span (ZMod 2) (Set.range fun t : Fin 24 => certVec (certBasisIdx.getD t 0)) = ⊤ ∧
    (∀ i : Fin 98280,
      CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed1 *ᵥ
        certVec i = certVec (certGen 0 i)) ∧
    (∀ i : Fin 98280,
      CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed2 *ᵥ
        certVec i = certVec (certGen 1 i)) ∧
    GA = Subgroup.closure {A₁, A₂} ∧
    ((A₁ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed1 ∧
    ((A₂ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed2 ∧
    (∀ (g : GA) (i : Fin 98280), certVec ((certRho g : Equiv.Perm (Fin 98280)) i) =
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec i) ∧
    (certRho ⟨A₁, A₁_mem⟩ : Equiv.Perm (Fin 98280)) = certGen 0 ∧
    (certRho ⟨A₂, A₂_mem⟩ : Equiv.Perm (Fin 98280)) = certGen 1 ∧
    (∀ u : CFSG.Blueprint.NativeSporadic.Co1,
      (((co1MatEquiv u : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = u.val.val ∧
      certCo1Equiv u = certRho (co1MatEquiv u) ∧
      ∀ i : Fin 98280,
        certVec ((certCo1Equiv u : Equiv.Perm (Fin 98280)) i) = u.val.val *ᵥ certVec i) := by
  refine ⟨fun _ hi => certVec_ne_zero hi, fun _ hi _ hj h => certVec_injective hi hj h, rfl,
    certBasis_linearIndependent, certBasis_span, fun i => ?_, fun i => ?_, GA_eq, val_A₁_eq,
    val_A₂_eq, certVec_rho, certRhoHom_A₁, certRhoHom_A₂, fun u => ⟨co1MatEquiv_val u, rfl,
    fun i => ?_⟩⟩
  · rw [← val_A₁_eq]
    exact A₁_mulVec i
  · rw [← val_A₂_eq]
    exact A₂_mulVec i
  · show certVec (certRhoHom (co1MatEquiv u) i) = _
    rw [certVec_rho, co1MatEquiv_val]

end CFSG.Sporadic.Co1Block
