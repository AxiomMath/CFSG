
module

public import CFSG.Monster.B.TwoA.Base.SevenPairA
public import CFSG.Monster.B.TwoA.Base.FrameBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.ToLin
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.Co2.MatrixCertBase
public import CFSG.Monster.B.Co2.MatrixIsoBase
public import CFSG.Monster.B.Co2.Order
public import CFSG.Monster.B.Co2.SimpleBase
public import CFSG.Monster.B.Short.Faithful22
public import CFSG.Monster.B.Short.ParityCentralizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.Sporadic.Mathieu

open scoped Pointwise

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

@[expose] def ePair (x y : Fin 24) : Fin 24 → ZMod 2 := Pi.single x 1 + Pi.single y 1

abbrev e01 : Fin 24 → ZMod 2 := ePair 0 1

theorem e01_add_self : e01 + e01 = 0 := by decide

@[expose] def Zsub : Submodule (ZMod 2) (Fin 24 → ZMod 2) := C ⊔ Submodule.span (ZMod 2) {e01}

theorem mem_Zsub_iff (v : Fin 24 → ZMod 2) : v ∈ Zsub ↔ v ∈ C ∨ v + e01 ∈ C := by
  rw [Zsub, Submodule.mem_sup]
  constructor
  · rintro ⟨c, hc, s, hs, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hs
    rcases zmod2_cases a with rfl | rfl
    · left
      rw [zero_smul, add_zero]
      exact hc
    · right
      rw [one_smul, add_assoc, e01_add_self, add_zero]
      exact hc
  · rintro (h | h)
    · exact ⟨v, h, 0, Submodule.zero_mem _, add_zero v⟩
    · refine ⟨v + e01, h, e01, Submodule.mem_span_singleton_self _, ?_⟩
      rw [add_assoc, e01_add_self, add_zero]

instance : DecidablePred (· ∈ Zsub) := fun v => decidable_of_iff _ (mem_Zsub_iff v).symm

abbrev Zcoc : Type := (Fin 24 → ZMod 2) ⧸ Zsub

@[expose] def zPair (x y : Fin 24) : Zcoc := Submodule.Quotient.mk (ePair x y)

theorem zPair_comm (x y : Fin 24) : zPair x y = zPair y x := by
  rw [zPair, zPair, ePair, ePair, add_comm]

@[expose] def labA (ℓ : Fin 8) : Fin 24 := ⟨2 * ℓ, by have := ℓ.isLt; omega⟩

@[expose] def labB (ℓ : Fin 8) : Fin 24 := ⟨2 * ℓ + 1, by have := ℓ.isLt; omega⟩

theorem labA_ne_labB (ℓ : Fin 8) : labA ℓ ≠ labB ℓ := by
  intro h
  have := congrArg Fin.val h
  simp only [labA, labB] at this
  omega

@[expose] def digit (ℓ : ℕ) (i : ℕ) : ZMod 2 := if ℓ.testBit i then 1 else 0

theorem mk_eq_mk_of {v w : Fin 24 → ZMod 2} (h : v - w ∈ Zsub) :
    (Submodule.Quotient.mk v : Zcoc) = Submodule.Quotient.mk w :=
  (Submodule.Quotient.eq _).2 h

theorem mk_sum_fin {n : ℕ} (f : Fin n → Fin 24 → ZMod 2) :
    (Submodule.Quotient.mk (∑ i, f i) : Zcoc) = ∑ i, Submodule.Quotient.mk (f i) :=
  map_sum (Zsub.mkQ) f Finset.univ

@[expose] def vb3 : Fin 3 → Fin 24 → ZMod 2 := ![ePair 2 3, ePair 4 5, ePair 8 9]

@[expose] def zb3 : Fin 3 → Zcoc := fun i => Submodule.Quotient.mk (vb3 i)

theorem lab3_rel : ∀ ℓ : Fin 8, ℓ ≠ 0 →
    ePair (labA ℓ) (labB ℓ) - ∑ i : Fin 3, digit ℓ i • vb3 i ∈ Zsub := by
  decide +kernel

theorem zPair_lab3 (ℓ : Fin 8) (hℓ : ℓ ≠ 0) :
    zPair (labA ℓ) (labB ℓ) = ∑ i : Fin 3, digit ℓ i • zb3 i := by
  rw [zPair, mk_eq_mk_of (lab3_rel ℓ hℓ), mk_sum_fin]
  simp only [zb3, Submodule.Quotient.mk_smul]

theorem indep3_rel : ∀ c : Fin 3 → ZMod 2, ∑ i, c i • vb3 i ∈ Zsub → c = 0 := by
  decide +kernel

theorem linearIndependent_zb3 : LinearIndependent (ZMod 2) zb3 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h : ∑ i, c i • vb3 i ∈ Zsub := by
    rw [← Submodule.Quotient.mk_eq_zero, mk_sum_fin]
    simpa only [zb3, Submodule.Quotient.mk_smul] using hc
  exact congrFun (indep3_rel c h)

@[expose] def Z3 : Submodule (ZMod 2) Zcoc := Submodule.span (ZMod 2) (Set.range zb3)

@[expose] noncomputable def basis3 : Module.Basis (Fin 3) (ZMod 2) Z3 :=
  Module.Basis.span linearIndependent_zb3

theorem coe_basis3 (i : Fin 3) : (basis3 i : Zcoc) = zb3 i :=
  congrArg Subtype.val (Module.Basis.span_apply _ i)

theorem A3_cases : ∀ D ∈ A3, ∃ ℓ : Fin 8, ℓ ≠ 0 ∧ D = duad (labA ℓ) (labB ℓ) (labA_ne_labB ℓ) := by
  intro D hD
  simp only [A3, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩

theorem zPair_eq_of_duad_eq {x y a b : Fin 24} (hxy : x ≠ y) (hab : a ≠ b)
    (h : duad x y hxy = duad a b hab) : zPair x y = zPair a b := by
  have h1 := congrArg Subtype.val h
  rw [duad_val, duad_val, pair_eq_pair_iff hxy hab] at h1
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact zPair_comm _ _

@[expose] def labelOf (x y : Fin 24) : ℕ := if x.val / 2 = y.val / 2 then x.val / 2 else 0

theorem labelOf_comm (x y : Fin 24) : labelOf x y = labelOf y x := by
  unfold labelOf
  by_cases h : x.val / 2 = y.val / 2
  · rw [ite_eq_left h, ite_eq_left h.symm, h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem labelOf_duad {x y a b : Fin 24} (hxy : x ≠ y) (hab : a ≠ b)
    (h : duad x y hxy = duad a b hab) : labelOf x y = labelOf a b := by
  have h1 := congrArg Subtype.val h
  rw [duad_val, duad_val, pair_eq_pair_iff hxy hab] at h1
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact labelOf_comm _ _

theorem labelOf_lab (ℓ : Fin 8) : labelOf (labA ℓ) (labB ℓ) = ℓ := by
  fin_cases ℓ <;> rfl

theorem zPair_of_mem_A3 {x y : Fin 24} (hxy : x ≠ y) (h : duad x y hxy ∈ A3) :
    zPair x y = ∑ i : Fin 3, digit (labelOf x y) i • zb3 i := by
  obtain ⟨ℓ, hℓ, hD⟩ := A3_cases _ h
  rw [zPair_eq_of_duad_eq hxy _ hD, labelOf_duad hxy _ hD, labelOf_lab]
  exact zPair_lab3 ℓ hℓ

theorem zPair_mem_Z3 {x y : Fin 24} (hxy : x ≠ y) (h : duad x y hxy ∈ A3) : zPair x y ∈ Z3 := by
  rw [zPair_of_mem_A3 hxy h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

@[expose] def permLin (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑p⁻¹

theorem permLin_apply (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) :
    permLin p x = permWord p x := rfl

theorem permLin_single (p : Equiv.Perm (Fin 24)) (x : Fin 24) :
    permLin p (Pi.single x 1) = Pi.single (p x) 1 := by
  funext j
  change (Pi.single x 1 : Fin 24 → ZMod 2) (p⁻¹ j) =
    (Pi.single (p x) 1 : Fin 24 → ZMod 2) j
  simp only [Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem permLin_ePair (p : Equiv.Perm (Fin 24)) (x y : Fin 24) :
    permLin p (ePair x y) = ePair (p x) (p y) := by
  rw [ePair, map_add, permLin_single, permLin_single, ePair]

theorem permLin_mul (p q : Equiv.Perm (Fin 24)) : permLin (p * q) = permLin p ∘ₗ permLin q :=
  LinearMap.ext fun x => (permWord_mul q p x)

theorem Zsub_le_comap {p : AutPerm} (hp : p ∈ Ppair) :
    Zsub ≤ Zsub.comap (permLin (p : Equiv.Perm (Fin 24))) := by
  rw [Zsub, sup_le_iff]
  constructor
  · intro x hx
    exact Submodule.mem_sup_left (permWord_mem_of_mem_AutPerm p.2 hx)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    change permLin (p : Equiv.Perm (Fin 24)) (ePair 0 1) ∈ Zsub
    rw [permLin_ePair]
    have h01 : ePair 0 1 ∈ Zsub := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    rcases (mem_Ppair_iff p).1 hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1]; exact h01
    · rw [h0, h1, ePair, add_comm]; exact h01

@[expose] def zAct (p : Ppair) : Zcoc →ₗ[ZMod 2] Zcoc :=
  Submodule.mapQ Zsub Zsub (permLin ((p : AutPerm) : Equiv.Perm (Fin 24))) (Zsub_le_comap p.2)

theorem zAct_zPair (p : Ppair) (x y : Fin 24) :
    zAct p (zPair x y) =
      zPair (((p : AutPerm) : Equiv.Perm (Fin 24)) x)
        (((p : AutPerm) : Equiv.Perm (Fin 24)) y) := by
  rw [zPair, zAct, Submodule.mapQ_apply, permLin_ePair]
  rfl

theorem zAct_mul (p q : Ppair) : zAct (p * q) = zAct p ∘ₗ zAct q := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  change Submodule.Quotient.mk (permLin _ x) = Submodule.Quotient.mk (permLin _ (permLin _ x))
  rw [show (((p * q : Ppair) : AutPerm) : Equiv.Perm (Fin 24)) =
    ((p : AutPerm) : Equiv.Perm (Fin 24)) * ((q : AutPerm) : Equiv.Perm (Fin 24)) from rfl,
    permLin_mul]
  rfl

theorem zAct_one : zAct 1 = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  rfl

theorem duad_smul_mem_A3 {p : AutPerm} (hp : p ∈ FA3) {x y : Fin 24} (hxy : x ≠ y)
    (h : duad x y hxy ∈ A3) :
    duad ((p : Equiv.Perm (Fin 24)) x) ((p : Equiv.Perm (Fin 24)) y)
      ((p : Equiv.Perm (Fin 24)).injective.ne hxy) ∈ A3 := by
  have hs : p • A3 = A3 := (Subgroup.mem_inf.1 hp).2
  have h1 : p • duad x y hxy ∈ p • A3 := Finset.smul_mem_smul_finset h
  rw [hs] at h1
  have e : p • duad x y hxy = duad ((p : Equiv.Perm (Fin 24)) x) ((p : Equiv.Perm (Fin 24)) y)
      ((p : Equiv.Perm (Fin 24)).injective.ne hxy) := Subtype.ext (by
    change p • ((duad x y hxy : Set.powersetCard (Fin 24) 2) : Finset (Fin 24)) = _
    rw [duad_val, duad_val, Finset.smul_finset_insert, Finset.smul_finset_singleton]
    rfl)
  rw [e] at h1
  exact h1

@[expose] def bpA3 : Fin 3 → Fin 24 := ![2, 4, 8]

@[expose] def bpB3 : Fin 3 → Fin 24 := ![3, 5, 9]

theorem zb3_eq (j : Fin 3) : zb3 j = zPair (bpA3 j) (bpB3 j) := by
  fin_cases j <;> rfl

theorem bp3_mem (j : Fin 3) : ∃ h : bpA3 j ≠ bpB3 j, duad (bpA3 j) (bpB3 j) h ∈ A3 := by
  fin_cases j <;> decide

theorem zAct_mem_Z3 {p : AutPerm} (hp : p ∈ FA3) {z : Zcoc} (hz : z ∈ Z3) :
    zAct ⟨p, FA3_le_Ppair hp⟩ z ∈ Z3 := by
  have hle : Z3 ≤ Z3.comap (zAct ⟨p, FA3_le_Ppair hp⟩) := by
    rw [Z3, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨hj, hA⟩ := bp3_mem i
    change zAct _ (zb3 i) ∈ Z3
    rw [zb3_eq, zAct_zPair]
    exact zPair_mem_Z3 _ (duad_smul_mem_A3 hp hj hA)
  exact hle hz

@[expose] noncomputable def linEnd3 : FA3 →* Module.End (ZMod 2) Z3 where
  toFun p := (zAct ⟨p, FA3_le_Ppair p.2⟩).restrict fun _ hz => zAct_mem_Z3 p.2 hz
  map_one' := LinearMap.ext fun z => Subtype.ext (by
    change zAct 1 z = z
    rw [zAct_one, LinearMap.id_apply])
  map_mul' p q := LinearMap.ext fun z => Subtype.ext
    (LinearMap.congr_fun (zAct_mul ⟨p, FA3_le_Ppair p.2⟩ ⟨q, FA3_le_Ppair q.2⟩) (z : Zcoc))

@[expose] noncomputable def glHom3 : FA3 →* GL (Fin 3) (ZMod 2) :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv basis3).toMulEquiv).toMonoidHom.comp
    linEnd3.toHomUnits

theorem glHom3_apply (p : FA3) :
    ((glHom3 p : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      Matrix.of fun (i j : Fin 3) => digit (labelOf (((p : AutPerm) : Equiv.Perm (Fin 24))
        (bpA3 j)) (((p : AutPerm) : Equiv.Perm (Fin 24)) (bpB3 j))) i := by
  set N : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun (i j : Fin 3) =>
    digit (labelOf (((p : AutPerm) : Equiv.Perm (Fin 24)) (bpA3 j))
      (((p : AutPerm) : Equiv.Perm (Fin 24)) (bpB3 j))) i with hN
  have hlin : linEnd3 p = Matrix.toLin basis3 basis3 N := by
    refine basis3.ext fun j => Subtype.ext ?_
    rw [Matrix.toLin_self, Submodule.coe_sum]
    change zAct _ (basis3 j : Zcoc) = _
    rw [coe_basis3, zb3_eq, zAct_zPair]
    obtain ⟨hj, hA⟩ := bp3_mem j
    rw [zPair_of_mem_A3 _ (duad_smul_mem_A3 p.2 hj hA)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, coe_basis3]
    rfl
  change LinearMap.toMatrix basis3 basis3 (linEnd3 p) = N
  rw [hlin, LinearMap.toMatrix_toLin]

end CFSG.Monster.B.TwoA
