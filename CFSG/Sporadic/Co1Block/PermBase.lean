
module

public import CFSG.Sporadic.Co1Block.PermCheckBase
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

@[expose] noncomputable def certVec (i : ℕ) : Vec24 := toVecD 24 certVecs[i]!

@[expose] def certX : Set Vec24 := {w | ∃ i < 98280, w = certVec i}

@[expose] noncomputable def certGen (k : ℕ) : Equiv.Perm (Fin 98280) := permOfArr 98280 (certAct k)

@[expose] noncomputable def certP : Subgroup (Equiv.Perm (Fin 98280)) :=
  Subgroup.closure {certGen 0, certGen 1}

theorem certBasisIdx_lt : ∀ t < 24, certBasisIdx.getD t 0 < 98280 := by
  decide

theorem certBasisRows_size (V : Array ℕ) : (certBasisRows V).size = 24 := by
  simp [certBasisRows, certBasisIdx]

theorem certBasisRows_get (V : Array ℕ) {t : ℕ} (ht : t < 24) :
    (certBasisRows V)[t]! = V[certBasisIdx.getD t 0]! := by
  have hl : t < certBasisIdx.length := by simpa [certBasisIdx] using ht
  rw [certBasisRows, getElem!_pos _ t (by simpa using hl)]
  simp [List.getElem?_eq_getElem hl]

theorem rowsMatrix_certBasisRows_row (t : Fin 24) :
    (rowsMatrix 24 (certBasisRows certVecs)).row t = certVec (certBasisIdx.getD t 0) := by
  funext j
  have hs : (t : ℕ) < (certBasisRows certVecs).size := by rw [certBasisRows_size]; exact t.2
  rw [Matrix.row_apply, rowsMatrix_apply, certVec, ← certBasisRows_get certVecs t.2,
    Array.getElem?_eq_getElem hs, Option.getD_some,
    getElem!_pos (certBasisRows certVecs) (t : ℕ) hs]

theorem val_A₁_eq :
    ((A₁ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
    CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed1 := val_A₁

theorem val_A₂_eq :
    ((A₂ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
    CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed2 := val_A₂

theorem certX_eq_range : certX = Set.range fun i : Fin 98280 => certVec i := by
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

theorem certX_finite : certX.Finite := by
  rw [certX_eq_range]
  exact Set.finite_range _

theorem mulVec_mem_of_closure {T : Set Vec24} (hT : T.Finite) {s : Set GL24}
    (hs : ∀ g ∈ s, ∀ w ∈ T, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T) :
    ∀ g ∈ Subgroup.closure s, ∀ w ∈ T,
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hs g hg
  | one => intro w hw; rwa [Units.val_one, one_mulVec]
  | mul g h _ _ ihg ihh =>
    intro w hw
    rw [Units.val_mul, ← mulVec_mulVec]
    exact ihg _ (ihh w hw)
  | inv g _ ihg => exact inv_mapsTo hT ihg

section Restriction

attribute [local instance] xAct

theorem closure_A₁_A₂ :
    Subgroup.closure ({⟨A₁, A₁_mem⟩, ⟨A₂, A₂_mem⟩} : Set GA) = ⊤ :=
  CFSG.Sporadic.SmallF2.closure_ab CFSG.Sporadic.Co1.Native.co1Data

end Restriction

theorem seedMonoid_eq_closure :
    CFSG.Blueprint.NativeSporadic.seedMonoid 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed1
      CFSG.Blueprint.NativeSporadic.Co1Seed2 =
      Submonoid.closure {((A₁ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)),
        ((A₂ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))} := by
  rw [CFSG.Blueprint.NativeSporadic.seedMonoid, val_A₁_eq, val_A₂_eq]

theorem val_mem_seedMonoid {g : GL24} (hg : g ∈ GA) :
    (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) ∈
      CFSG.Blueprint.NativeSporadic.seedMonoid 2 24 1 CFSG.Blueprint.NativeSporadic.Co1Seed1
        CFSG.Blueprint.NativeSporadic.Co1Seed2 := by
  rw [seedMonoid_eq_closure]
  have hg' : g ∈ (Subgroup.closure ({A₁, A₂} : Set GL24)).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid_of_finite] at hg'
  have := Submonoid.mem_map_of_mem (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))) hg'
  rw [MonoidHom.map_mclosure, Set.image_pair, Units.coeHom_apply, Units.coeHom_apply,
    Units.coeHom_apply] at this
  exact this

@[expose] noncomputable def gaToCo1 :
    GA →* CFSG.Blueprint.NativeSporadic.Co1 where
  toFun g := ⟨⟨(g : GL24), val_mem_seedMonoid g.2⟩, ⟨((g : GL24)⁻¹ : GL24),
      val_mem_seedMonoid (GA.inv_mem g.2)⟩, Subtype.ext (g : GL24).val_inv,
    Subtype.ext (g : GL24).inv_val⟩
  map_one' := Units.ext (Subtype.ext rfl)
  map_mul' _ _ := Units.ext (Subtype.ext rfl)

theorem gaToCo1_val (g : GA) :
    (gaToCo1 g).val.val = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := rfl

theorem gaToCo1_injective :
    Function.Injective gaToCo1 := fun g h e =>
  Subtype.ext (Units.ext (by rw [← gaToCo1_val, ← gaToCo1_val, e]))

theorem gaToCo1_bijective : Function.Bijective gaToCo1 := by
  have : Finite GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  refine (Function.Injective.bijective_of_nat_card_le gaToCo1_injective ?_)
  rw [card_GA_eq, CFSG.Sporadic.Co1.card_Co1]

@[expose] noncomputable def co1MatEquiv :
    CFSG.Blueprint.NativeSporadic.Co1 ≃* GA :=
  (MulEquiv.ofBijective gaToCo1 gaToCo1_bijective).symm

theorem co1MatEquiv_val (u : CFSG.Blueprint.NativeSporadic.Co1) :
    (((co1MatEquiv u : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = u.val.val := by
  rw [← gaToCo1_val]
  exact congrArg (fun v : CFSG.Blueprint.NativeSporadic.Co1 => v.val.val)
    ((MulEquiv.ofBijective gaToCo1 gaToCo1_bijective).apply_symm_apply u)

end CFSG.Sporadic.Co1Block
