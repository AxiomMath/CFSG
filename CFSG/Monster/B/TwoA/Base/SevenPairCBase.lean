
module

public import CFSG.Monster.B.TwoA.Base.SevenPairB
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.TwoA.Base.SevenPairCInputs
public import CFSG.Monster.B.TwoA.Base.SevenPairAInputs
public import Certificates.Data.CFSGNative.Mathieu.M24
public import Certificates.Data.CFSGNative.Mathieu.M22

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.Sporadic.Mathieu

open scoped Pointwise

def vb2 : Fin 2 → Fin 24 → ZMod 2 := ![ePair 2 3, ePair 4 5]

def zb2 : Fin 2 → Zcoc := fun i => Submodule.Quotient.mk (vb2 i)

theorem lab2_rel : ∀ ℓ : Fin 4, ℓ ≠ 0 →
    ePair (labA ⟨ℓ, by omega⟩) (labB ⟨ℓ, by omega⟩) - ∑ i : Fin 2, digit ℓ i • vb2 i ∈ Zsub := by
  decide +kernel

theorem zPair_lab2 (ℓ : Fin 4) (hℓ : ℓ ≠ 0) :
    zPair (labA ⟨ℓ, by omega⟩) (labB ⟨ℓ, by omega⟩) = ∑ i : Fin 2, digit ℓ i • zb2 i := by
  rw [zPair, mk_eq_mk_of (lab2_rel ℓ hℓ), mk_sum_fin]
  simp only [zb2, Submodule.Quotient.mk_smul]

theorem indep2_rel : ∀ c : Fin 2 → ZMod 2, ∑ i, c i • vb2 i ∈ Zsub → c = 0 := by
  decide +kernel

theorem linearIndependent_zb2 : LinearIndependent (ZMod 2) zb2 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h : ∑ i, c i • vb2 i ∈ Zsub := by
    rw [← Submodule.Quotient.mk_eq_zero, mk_sum_fin]
    simpa only [zb2, Submodule.Quotient.mk_smul] using hc
  exact congrFun (indep2_rel c h)

def Z2 : Submodule (ZMod 2) Zcoc := Submodule.span (ZMod 2) (Set.range zb2)

noncomputable def basis2 : Module.Basis (Fin 2) (ZMod 2) Z2 :=
  Module.Basis.span linearIndependent_zb2

theorem coe_basis2 (i : Fin 2) : (basis2 i : Zcoc) = zb2 i :=
  congrArg Subtype.val (Module.Basis.span_apply _ i)

theorem A2_cases : ∀ D ∈ A2, ∃ ℓ : Fin 4, ℓ ≠ 0 ∧
    D = duad (labA ⟨ℓ, by omega⟩) (labB ⟨ℓ, by omega⟩) (labA_ne_labB _) := by
  intro D hD
  simp only [A2, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩

theorem zPair_of_mem_A2 {x y : Fin 24} (hxy : x ≠ y) (h : duad x y hxy ∈ A2) :
    zPair x y = ∑ i : Fin 2, digit (labelOf x y) i • zb2 i := by
  obtain ⟨ℓ, hℓ, hD⟩ := A2_cases _ h
  rw [zPair_eq_of_duad_eq hxy _ hD, labelOf_duad hxy _ hD, labelOf_lab]
  exact zPair_lab2 ℓ hℓ

theorem zPair_mem_Z2 {x y : Fin 24} (hxy : x ≠ y) (h : duad x y hxy ∈ A2) : zPair x y ∈ Z2 := by
  rw [zPair_of_mem_A2 hxy h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem duad_smul_mem_A2 {p : AutPerm} (hp : p ∈ FA2) {x y : Fin 24} (hxy : x ≠ y)
    (h : duad x y hxy ∈ A2) :
    duad ((p : Equiv.Perm (Fin 24)) x) ((p : Equiv.Perm (Fin 24)) y)
      ((p : Equiv.Perm (Fin 24)).injective.ne hxy) ∈ A2 := by
  have hs : p • A2 = A2 := (Subgroup.mem_inf.1 hp).2
  have h1 : p • duad x y hxy ∈ p • A2 := Finset.smul_mem_smul_finset h
  rw [hs] at h1
  have e : p • duad x y hxy = duad ((p : Equiv.Perm (Fin 24)) x) ((p : Equiv.Perm (Fin 24)) y)
      ((p : Equiv.Perm (Fin 24)).injective.ne hxy) := Subtype.ext (by
    change p • ((duad x y hxy : Set.powersetCard (Fin 24) 2) : Finset (Fin 24)) = _
    rw [duad_val, duad_val, Finset.smul_finset_insert, Finset.smul_finset_singleton]
    rfl)
  rw [e] at h1
  exact h1

def bpA2 : Fin 2 → Fin 24 := ![2, 4]

def bpB2 : Fin 2 → Fin 24 := ![3, 5]

theorem zb2_eq (j : Fin 2) : zb2 j = zPair (bpA2 j) (bpB2 j) := by
  fin_cases j <;> rfl

theorem bp2_mem (j : Fin 2) : ∃ h : bpA2 j ≠ bpB2 j, duad (bpA2 j) (bpB2 j) h ∈ A2 := by
  fin_cases j <;> decide

theorem zAct_mem_Z2 {p : AutPerm} (hp : p ∈ FA2) {z : Zcoc} (hz : z ∈ Z2) :
    zAct ⟨p, FA2_le_Ppair hp⟩ z ∈ Z2 := by
  have hle : Z2 ≤ Z2.comap (zAct ⟨p, FA2_le_Ppair hp⟩) := by
    rw [Z2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨hj, hA⟩ := bp2_mem i
    change zAct _ (zb2 i) ∈ Z2
    rw [zb2_eq, zAct_zPair]
    exact zPair_mem_Z2 _ (duad_smul_mem_A2 hp hj hA)
  exact hle hz

noncomputable def linEnd2 : FA2 →* Module.End (ZMod 2) Z2 where
  toFun p := (zAct ⟨p, FA2_le_Ppair p.2⟩).restrict fun _ hz => zAct_mem_Z2 p.2 hz
  map_one' := LinearMap.ext fun z => Subtype.ext (by
    change zAct 1 z = z
    rw [zAct_one, LinearMap.id_apply])
  map_mul' p q := LinearMap.ext fun z => Subtype.ext
    (LinearMap.congr_fun (zAct_mul ⟨p, FA2_le_Ppair p.2⟩ ⟨q, FA2_le_Ppair q.2⟩) (z : Zcoc))

noncomputable def glHom2 : FA2 →* GL (Fin 2) (ZMod 2) :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv basis2).toMulEquiv).toMonoidHom.comp
    linEnd2.toHomUnits

theorem glHom2_apply (p : FA2) :
    ((glHom2 p : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      Matrix.of fun (i j : Fin 2) => digit (labelOf (((p : AutPerm) : Equiv.Perm (Fin 24))
        (bpA2 j)) (((p : AutPerm) : Equiv.Perm (Fin 24)) (bpB2 j))) i := by
  set N : Matrix (Fin 2) (Fin 2) (ZMod 2) := Matrix.of fun (i j : Fin 2) =>
    digit (labelOf (((p : AutPerm) : Equiv.Perm (Fin 24)) (bpA2 j))
      (((p : AutPerm) : Equiv.Perm (Fin 24)) (bpB2 j))) i with hN
  have hlin : linEnd2 p = Matrix.toLin basis2 basis2 N := by
    refine basis2.ext fun j => Subtype.ext ?_
    rw [Matrix.toLin_self, Submodule.coe_sum]
    change zAct _ (basis2 j : Zcoc) = _
    rw [coe_basis2, zb2_eq, zAct_zPair]
    obtain ⟨hj, hA⟩ := bp2_mem j
    rw [zPair_of_mem_A2 _ (duad_smul_mem_A2 p.2 hj hA)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, coe_basis2]
    rfl
  change LinearMap.toMatrix basis2 basis2 (linEnd2 p) = N
  rw [hlin, LinearMap.toMatrix_toLin]

def wit1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13, 19, 18, 17, 16, 21, 20, 23, 22]
  invFun := ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13, 19, 18, 17, 16, 21, 20, 23, 22]
  left_inv := by decide
  right_inv := by decide

def wit2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 17, 16, 21, 20, 19, 18, 23, 22]
  invFun := ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 17, 16, 21, 20, 19, 18, 23, 22]
  left_inv := by decide
  right_inv := by decide

def wit3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21]
  left_inv := by decide
  right_inv := by decide

def wit4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]
  left_inv := by decide
  right_inv := by decide

def wit5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 20, 23, 21, 22, 16, 18, 19, 17]
  invFun := ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 20, 23, 21, 22, 16, 18, 19, 17]
  left_inv := by decide
  right_inv := by decide

theorem wit1_mem : wit1 ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem wit2_mem : wit2 ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem wit3_mem : wit3 ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem wit4_mem : wit4 ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem wit5_mem : wit5 ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem mem_FA2_of {p : AutPerm} (h0 : (p : Equiv.Perm (Fin 24)) 0 = 0)
    (h1 : (p : Equiv.Perm (Fin 24)) 1 = 1)
    (hc : (p : Equiv.Perm (Fin 24)) * sig2 * (p : Equiv.Perm (Fin 24))⁻¹ = sig2) : p ∈ FA2 :=
  ⟨mem_Ppair_of_fix p h0 h1, (mem_stabilizer_A2_iff p).2 hc⟩

theorem mem_FA3_of {p : AutPerm} (h0 : (p : Equiv.Perm (Fin 24)) 0 = 0)
    (h1 : (p : Equiv.Perm (Fin 24)) 1 = 1)
    (hc : (p : Equiv.Perm (Fin 24)) * sig3 * (p : Equiv.Perm (Fin 24))⁻¹ = sig3) : p ∈ FA3 :=
  ⟨mem_Ppair_of_fix p h0 h1, (mem_stabilizer_A3_iff p).2 hc⟩

theorem decMat_codeMat2 : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), decMat 2 (codeMat 2 A) = A := by
  decide +kernel

theorem codeMat_decMat2 : ∀ m < 16, codeMat 2 (decMat 2 m) = m := by decide +kernel

theorem decMat_codeMat3 : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), decMat 3 (codeMat 3 A) = A := by
  decide +kernel

theorem codeMat_decMat3 : ∀ m < 512, codeMat 3 (decMat 3 m) = m := by decide +kernel

theorem matW2_sq : ∀ k : Fin 2, matW2 k * matW2 k = 1 := by decide

theorem matW3_sq : ∀ k : Fin 5, matW3 k * matW3 k = 1 := by decide

def unitW2 (k : ℕ) : GL (Fin 2) (ZMod 2) :=
  if hk : k < 2 then ⟨matW2 k, matW2 k, matW2_sq ⟨k, hk⟩, matW2_sq ⟨k, hk⟩⟩ else 1

def unitW3 (k : ℕ) : GL (Fin 3) (ZMod 2) :=
  if hk : k < 5 then ⟨matW3 k, matW3 k, matW3_sq ⟨k, hk⟩, matW3_sq ⟨k, hk⟩⟩ else 1

theorem coe_unitW2 {k : ℕ} (hk : k < 2) :
    ((unitW2 k : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = matW2 k := by
  rw [unitW2, dite_eq_left hk]

theorem coe_unitW3 {k : ℕ} (hk : k < 5) :
    ((unitW3 k : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = matW3 k := by
  rw [unitW3, dite_eq_left hk]

theorem natCard_GL_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  rfl

theorem natCard_GL_three' : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
  rfl

def witF2 (k : ℕ) : FA2 :=
  if k = 0 then ⟨⟨wit1, wit1_mem⟩, mem_FA2_of rfl rfl (by decide)⟩
  else ⟨⟨wit2, wit2_mem⟩, mem_FA2_of rfl rfl (by decide)⟩

def witF3 (k : ℕ) : FA3 :=
  if k = 0 then ⟨⟨wit3, wit3_mem⟩, mem_FA3_of rfl rfl (by decide)⟩ else
  if k = 1 then ⟨⟨wit4, wit4_mem⟩, mem_FA3_of rfl rfl (by decide)⟩ else
  if k = 2 then ⟨⟨wit1, wit1_mem⟩, mem_FA3_of rfl rfl (by decide)⟩ else
  if k = 3 then ⟨⟨wit5, wit5_mem⟩, mem_FA3_of rfl rfl (by decide)⟩ else
  ⟨⟨wit2, wit2_mem⟩, mem_FA3_of rfl rfl (by decide)⟩

theorem glHom2_witF2 : ∀ k < 2, glHom2 (witF2 k) = unitW2 k := by
  intro k hk
  apply Units.ext
  rw [glHom2_apply, coe_unitW2 hk]
  interval_cases k <;> decide

theorem glHom3_witF3 : ∀ k < 5, glHom3 (witF3 k) = unitW3 k := by
  intro k hk
  apply Units.ext
  rw [glHom3_apply, coe_unitW3 hk]
  interval_cases k <;> decide

def evalMap3 : Ceq →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  (LinearMap.pi fun j : Fin 3 =>
    (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 24 => ZMod 2) (bpA3 j) +
      LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 24 => ZMod 2) (bpB3 j))).comp Ceq.subtype

theorem evalMap3_apply (c : Ceq) :
    evalMap3 c = fun j => (c : Fin 24 → ZMod 2) (bpA3 j) + (c : Fin 24 → ZMod 2) (bpB3 j) := rfl

def evalMap2 : Ceq →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  (LinearMap.pi fun j : Fin 2 =>
    (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 24 => ZMod 2) (bpA2 j) +
      LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 24 => ZMod 2) (bpB2 j))).comp Ceq.subtype

theorem evalMap2_apply (c : Ceq) :
    evalMap2 c = fun j => (c : Fin 24 → ZMod 2) (bpA2 j) + (c : Fin 24 → ZMod 2) (bpB2 j) := rfl

def evW (j : Fin 3) : Fin 24 → ZMod 2 := bvec 24 (![0x1e4444, 0xc9a050, 0xa5a500] j)

theorem evW_mem : ∀ j, evW j ∈ Ceq := by
  intro j
  rw [mem_Ceq]
  revert j
  decide +kernel

theorem evalMap3_evW : ∀ j, evalMap3 ⟨evW j, evW_mem j⟩ = Pi.single j 1 := by
  intro j
  rw [evalMap3_apply]
  revert j
  decide +kernel

theorem evalMap2_evW : ∀ j : Fin 2, evalMap2 ⟨evW j.castSucc, evW_mem _⟩ = Pi.single j 1 := by
  intro j
  rw [evalMap2_apply]
  revert j
  decide +kernel

theorem surjective_of_single {n : ℕ} (f : Ceq →ₗ[ZMod 2] (Fin n → ZMod 2)) (c : Fin n → Ceq)
    (hc : ∀ j, f (c j) = Pi.single j 1) : Function.Surjective f := by
  intro v
  refine ⟨∑ j, v j • c j, ?_⟩
  rw [map_sum]
  simp only [map_smul, hc]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem evalMap3_surjective : Function.Surjective evalMap3 :=
  surjective_of_single evalMap3 _ evalMap3_evW

theorem evalMap2_surjective : Function.Surjective evalMap2 :=
  surjective_of_single evalMap2 _ evalMap2_evW

end CFSG.Monster.B.TwoA
