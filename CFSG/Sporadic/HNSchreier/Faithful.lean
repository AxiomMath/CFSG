module

public import CFSG.Sporadic.HNSchreier.VectorData
public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import CFSG.Sporadic.HN.F5Group
import all CFSG.Blueprint.NativeSporadic
import all CFSG.Sporadic.HN.F5Group
public import Certificates.Certificate2102
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.HNSchreier.Native Matrix

abbrev X : Type := Fin hnsData.n

theorem hns_n : hnsData.n = nPts := rfl

theorem hns_d : hnsData.d = 133 := rfl

private theorem array_all_lt' {a : Array ℕ} {m : ℕ} (h : a.all (· < m) = true) :
    ∀ i < a.size, a[i]! < m := by
  intro i hi
  rw [Array.all_eq_true] at h
  have := h i hi
  rw [getElem!_pos a i hi]
  simpa using this

theorem orbit_parts : BaseFacts hnsData ∧
    bfsOrderOK hnsData.n (hnsData.orbit ()).alpha (hnsData.orbit ()).beta = true := by
  have h := orbit_cert
  unfold orbitCertChecks matrixChecks orbitChecks at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at h
  obtain ⟨hd0, hd, heA, heB, hpA, hpB, horb, hks, has, hbs, hn, hiA, hiB, hQs, hQl, hbas,
    hbfs⟩ := h
  exact ⟨⟨hd0, hd, heA, heB, hpA, hpB, f5OrbitOK_facts horb, hks, has, hbs, hn, hiA, hiB, hQs,
    array_all_lt' hQl, hbas⟩, hbfs⟩

theorem hnsBase : BaseFacts hnsData := orbit_parts.1

theorem hns_bfsOrder :
    BfsOrder (ap (hnsData.orbit ()).alpha) (ap (hnsData.orbit ()).beta) nPts := by
  have h := orbit_parts.2
  unfold bfsOrderOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

@[expose] noncomputable def PK (i : ℕ) : Vec := toVecB 133 (hnsData.orbit ()).keys[i]!

abbrev alphaT : Table := (hnsData.orbit ()).alpha

abbrev betaT : Table := (hnsData.orbit ()).beta

theorem keys_size' :
    (hnsData.orbit ()).keys.size = nPts := hnsBase.keys_size

theorem keys_canon'
    {i : ℕ} (hi : i < nPts) : canonB 133 (hnsData.orbit ()).keys[i]! = true :=
  keys_canon hnsBase hi

theorem toVecB_root : toVecB 133 (bytesOfDigits Data.rootDigits) = fixedVector := by
  funext j
  revert j
  decide +kernel

theorem PK_zero : PK 0 = fixedVector := by
  have hroot : (hnsData.orbit ()).keys[0]! = bytesOfDigits Data.rootDigits := hnsBase.vf.root
  rw [PK, hroot, toVecB_root]

theorem PK_injective : ∀ i < nPts, ∀ j < nPts, PK i = PK j → i = j :=
  fun i hi j hj h => P_injective hnsBase i hi j hj h

theorem rowsA_hns : hnsData.rowsA = rowsA := rfl

theorem rowsB_hns : hnsData.rowsB = rowsB := rfl

theorem matA_PK {i : ℕ} (hi : i < nPts) :
    ap alphaT i < nPts ∧ matA *ᵥ PK i = PK (ap alphaT i) := by
  have hi' : i < (hnsData.orbit ()).keys.size := by rw [keys_size']; exact hi
  obtain ⟨hlt, he⟩ := hnsBase.vf.alpha i hi'
  have he' : (hnsData.orbit ()).keys[ap alphaT i]! =
      mulW 133 133 (frTable 133 133 rowsA) (hnsData.orbit ()).keys[i]! := he
  refine ⟨by rw [← keys_size']; exact hlt, ?_⟩
  rw [PK, PK, he', toVecB_mulW (by norm_num) (by norm_num) _ (keys_canon' hi),
    toMatR_eq_toMat, toMat_rowsA]

theorem matB_PK {i : ℕ} (hi : i < nPts) :
    ap betaT i < nPts ∧ matB *ᵥ PK i = PK (ap betaT i) := by
  have hi' : i < (hnsData.orbit ()).keys.size := by rw [keys_size']; exact hi
  obtain ⟨hlt, he⟩ := hnsBase.vf.beta i hi'
  have he' : (hnsData.orbit ()).keys[ap betaT i]! =
      mulW 133 133 (frTable 133 133 rowsB) (hnsData.orbit ()).keys[i]! := he
  refine ⟨by rw [← keys_size']; exact hlt, ?_⟩
  rw [PK, PK, he', toVecB_mulW (by norm_num) (by norm_num) _ (keys_canon' hi),
    toMatR_eq_toMat, toMat_rowsB]

theorem orbitL_eq_PK : orbitL = (List.range nPts).map PK := by
  rw [orbitL_eq]
  exact orbitList_eq_of_bfsOrder PK_injective PK_zero
    (fun i hi => ⟨(matA_PK hi).1, (matA_PK hi).2.symm⟩)
    (fun i hi => ⟨(matB_PK hi).1, (matB_PK hi).2.symm⟩) hns_bfsOrder

theorem orbitL_length :
    orbitL.length = nPts := by rw [orbitL_eq_PK]; simp

theorem vL_eq {i : ℕ} (hi : i < nPts) : vL i = PK i := by
  rw [vL, orbitL_eq_PK, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem orbitL_nodup : orbitL.Nodup := by
  rw [orbitL_eq_PK, List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj h
  exact PK_injective i (List.mem_range.1 hi) j (List.mem_range.1 hj) h

theorem idxOf_PK
    {k : ℕ} (hk : k < nPts) : orbitL.idxOf (PK k) = k := by
  have hl : k < orbitL.length := by rw [orbitL_length]; exact hk
  have he : orbitL[k] = PK k := by
    have := vL_eq hk
    rw [vL, List.getD_eq_getElem _ _ hl] at this
    exact this
  rw [← he]
  exact orbitL_nodup.idxOf_getElem k hl

theorem firstIndex_PK
    {k : ℕ} (hk : k < nPts) : firstIndex (PK k) = k := by
  rw [firstIndex, idxOf_PK hk, orbitL_length, ite_eq_left ⟨hk, hk⟩]

theorem f0_eq {i : ℕ} (hi : i < nPts) : f0 i = ap alphaT i := by
  rw [f0, ite_eq_left (by rw [orbitL_length]; exact hi), vL_eq hi, (matA_PK hi).2,
    firstIndex_PK (matA_PK hi).1]

theorem f1_eq {i : ℕ} (hi : i < nPts) : f1 i = ap betaT i := by
  rw [f1, ite_eq_left (by rw [orbitL_length]; exact hi), vL_eq hi, (matB_PK hi).2,
    firstIndex_PK (matB_PK hi).1]

noncomputable abbrev JH : Subgroup (GL (Fin hnsData.d) (ZMod 5)) := J hnsData

noncomputable abbrev matJ (g : JH) : Matrix (Fin 133) (Fin 133) (ZMod 5) := mat hnsData g

noncomputable abbrev aJ : JH := a hnsData

noncomputable abbrev bJ : JH := b hnsData

theorem mA_hns : (mA hnsData : Matrix (Fin 133) (Fin 133) (ZMod 5)) = matA := by
  rw [matA_eq]; rfl

theorem mB_hns : (mB hnsData : Matrix (Fin 133) (Fin 133) (ZMod 5)) = matB := by
  rw [matB_eq]; rfl

theorem mat_aJ : matJ aJ = matA := by
  rw [matJ, mat_a hnsBase]
  exact mA_hns

theorem mat_bJ : matJ bJ = matB := by
  rw [matJ, mat_b hnsBase]
  exact mB_hns

theorem matJ_injective : Function.Injective matJ := mat_injective hnsData

theorem PK_smul
    (g : JH) (i : X) : PK (g • i).val = matJ g *ᵥ PK i.val := P_smul hnsBase g i

theorem mat_vL
    (g : JH) (i : X) : matJ g *ᵥ vL i = vL ((g • i : X) : ℕ) := by
  rw [vL_eq i.isLt, vL_eq (g • i).isLt, PK_smul]

theorem aJ_smul (i : X) : ((aJ • i : X) : ℕ) = f0 i := by
  rw [f0_eq i.isLt, ← idx_of_lt _ i.isLt]
  exact ((rep_a hnsBase) i i.isLt).symm

theorem bJ_smul (i : X) : ((bJ • i : X) : ℕ) = f1 i := by
  rw [f1_eq i.isLt, ← idx_of_lt _ i.isLt]
  exact ((rep_b hnsBase) i i.isLt).symm

theorem hns_faithful : FaithfulSMul JH X := faithful hnsBase

abbrev x0 : X := ⟨0, by decide⟩

theorem smul_mul_val (a g : JH) (x : X) : ((a * g) • x : X).val = (a • (g • x) : X).val :=
  congrArg Fin.val (mul_smul a g x)

theorem smul_mul_inv (g h : JH) (x : X) : (h * g⁻¹) • (g • x) = h • x := by
  rw [mul_smul, inv_smul_smul]

theorem exists_smul_zero :
    ∀ k < nPts, ∃ g : JH, ((g • x0 : X) : ℕ) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨1, by rw [one_smul]⟩
    · have hks : k < (hnsData.orbit ()).keys.size := by rw [keys_size']; exact hk
      obtain ⟨hpar, hlab⟩ := hnsBase.vf.tree k hks hk0
      obtain ⟨g, hg⟩ := ih _ hpar (by omega)
      have hlt : ((g • x0 : X) : ℕ) < nPts := (g • x0).isLt
      rcases hlab with ⟨-, he⟩ | ⟨-, he⟩
      · exact ⟨aJ * g, (smul_mul_val aJ g x0).trans ((aJ_smul _).trans ((f0_eq hlt).trans
          ((congrArg (ap alphaT) hg).trans he)))⟩
      · exact ⟨bJ * g, (smul_mul_val bJ g x0).trans ((bJ_smul _).trans ((f1_eq hlt).trans
          ((congrArg (ap betaT) hg).trans he)))⟩

theorem hns_pretransitive : MulAction.IsPretransitive JH X := by
  refine MulAction.IsPretransitive.mk ?_
  intro x y
  obtain ⟨g, hg⟩ := exists_smul_zero x.val x.isLt
  obtain ⟨h, hh⟩ := exists_smul_zero y.val y.isLt
  have hx : x = g • x0 := Fin.ext hg.symm
  have hy : y = h • x0 := Fin.ext hh.symm
  exact ⟨h * g⁻¹, by rw [hx, hy]; exact smul_mul_inv g h x0⟩

noncomputable abbrev a0 : Equiv.Perm X := MulAction.toPerm aJ

noncomputable abbrev a1 : Equiv.Perm X := MulAction.toPerm bJ

theorem a0_apply (i : X) : (a0 i : ℕ) = f0 i := aJ_smul i

theorem a1_apply (i : X) : (a1 i : ℕ) = f1 i := bJ_smul i

noncomputable abbrev PH : Subgroup (Equiv.Perm X) := Subgroup.closure {a0, a1}

noncomputable abbrev permHom : JH →* Equiv.Perm X := MulAction.toPermHom JH X

theorem permHom_injective : Function.Injective permHom := by
  intro g h hgh
  have := hns_faithful
  exact eq_of_smul_eq_smul fun x => by
    have := congrArg (fun σ : Equiv.Perm X => σ x) hgh
    simpa using this

theorem permHom_range : permHom.range = PH := by
  rw [MonoidHom.range_eq_map, ← closure_ab hnsData, MonoidHom.map_closure, Set.image_pair]
  rfl

@[expose] noncomputable def jEquivP : JH ≃* PH :=
  (MonoidHom.ofInjective permHom_injective).trans (MulEquiv.subgroupCongr permHom_range)

theorem jEquivP_apply
    (g : JH) (i : X) : ((jEquivP g : PH) : Equiv.Perm X) i = g • i := by
  rfl


noncomputable def hnEquivJ :
    Blueprint.NativeSporadic.HN ≃* JH := seedEquiv hnsBase

theorem hnEquivJ_mat
    (u : Blueprint.NativeSporadic.HN) : matJ (hnEquivJ u) = u.val.val := by
  unfold hnEquivJ
  rfl

theorem hnEquivJ_eq_aJ
    {u : Blueprint.NativeSporadic.HN} (hu : u.val.val = matA) :
    hnEquivJ u = aJ :=
  matJ_injective ((hnEquivJ_mat u).trans (hu.trans mat_aJ.symm))

theorem hnEquivJ_eq_bJ
    {u : Blueprint.NativeSporadic.HN} (hu : u.val.val = matB) :
    hnEquivJ u = bJ :=
  matJ_injective ((hnEquivJ_mat u).trans (hu.trans mat_bJ.symm))

noncomputable def hnEquivP :
    Blueprint.NativeSporadic.HN ≃* PH := hnEquivJ.trans jEquivP

theorem fam_hn_faithful_vector_orbit_action :
    fixedVector ≠ 0 ∧ orbitL.length = nPts ∧ orbitL.Nodup ∧
    (∀ i < nPts, matA *ᵥ vL i = vL (f0 i) ∧ matB *ᵥ vL i = vL (f1 i)) ∧
    (∀ i : X, (a0 i : ℕ) = f0 i ∧ (a1 i : ℕ) = f1 i) ∧
    (∀ (g : JH) (i : X), matJ g *ᵥ vL i = vL ((g • i : X) : ℕ)) ∧
    matJ aJ = matA ∧ matJ bJ = matB ∧
    FaithfulSMul JH X ∧ MulAction.IsPretransitive JH X ∧
    (∃ φ : JH ≃* PH, (φ aJ : Equiv.Perm X) = a0 ∧ (φ bJ : Equiv.Perm X) = a1 ∧
      ∀ (g : JH) (i : X), (φ g : Equiv.Perm X) i = g • i) ∧
    ∃ ψ : Blueprint.NativeSporadic.HN ≃* PH,
      (∀ u : Blueprint.NativeSporadic.HN, u.val.val = matA → (ψ u : Equiv.Perm X) = a0) ∧
      ∀ u : Blueprint.NativeSporadic.HN, u.val.val = matB → (ψ u : Equiv.Perm X) = a1 := by
  refine ⟨?_, orbitL_length, orbitL_nodup, fun i hi => ⟨?_, ?_⟩, fun i => ⟨a0_apply i,
    a1_apply i⟩, mat_vL, mat_aJ, mat_bJ, hns_faithful, hns_pretransitive,
    ⟨jEquivP, rfl, rfl, jEquivP_apply⟩, hnEquivP, fun u hu => ?_, fun u hu => ?_⟩
  · intro h
    have := congrFun h 0
    revert this
    decide +kernel
  · rw [vL_eq hi, (matA_PK hi).2, f0_eq hi, vL_eq (matA_PK hi).1]
  · rw [vL_eq hi, (matB_PK hi).2, f1_eq hi, vL_eq (matB_PK hi).1]
  · show ((jEquivP (hnEquivJ u) : PH) : Equiv.Perm X) = a0
    rw [hnEquivJ_eq_aJ hu]
    rfl
  · show ((jEquivP (hnEquivJ u) : PH) : Equiv.Perm X) = a1
    rw [hnEquivJ_eq_bJ hu]
    rfl

end CFSG.Sporadic.HNSchreier
