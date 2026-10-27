module

public import CFSG.Monster.B.Fischer.HexadQuot
public import CFSG.Monster.B.Fischer.ArrCert
public meta import CFSG.Monster.B.Fischer.HexadQuot
public meta import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.Monster.B.Fischer.HexadDiagInputs
public import Certificates.Certificate3031
public import Certificates.Certificate3030
public import Certificates.Certificate3029

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

theorem dCert_ok : arrCertOK dAct 3 dValid dKey dRoot dCert = true :=
  Certificates.certificate3031.1

theorem dCert_size : dCert.pts.size = 5760 :=
  Certificates.certificate3031.2

@[expose] noncomputable def dDec (x : Array ℕ) : Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32) :=
  (decodeN 22 (x.extract 0 22), decodeN 32 (x.extract 22 54))

@[expose] noncomputable def dGens (k : ℕ) : Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32) :=
  dDec (dGenArr k)

theorem dGenArr_fst : ∀ i < 3, (dGenArr i).extract 0 22 = gcatArr i := by decide +kernel

theorem dGenArr_snd : ∀ i < 3, (dGenArr i).extract 22 54 = alphaArr i := by decide +kernel

theorem PermArrN_gcatArr : ∀ i < 3, PermArrN 22 (gcatArr i) = true := by decide +kernel

theorem PermArrN_alphaArr : ∀ i < 3, PermArrN 32 (alphaArr i) = true := by decide +kernel

theorem extract_fst_append {a b : Array ℕ} (ha : a.size = 22) : (a ++ b).extract 0 22 = a := by
  rw [Array.extract_append, ha, Array.extract_eq_self_of_le ha.le,
    Array.extract_empty_of_stop_le_start (by omega), Array.append_empty]

theorem extract_snd_append {a b : Array ℕ} (ha : a.size = 22) (hb : b.size = 32) :
    (a ++ b).extract 22 54 = b := by
  rw [Array.extract_append, ha, Array.extract_empty_of_size_le_start (by omega),
    Array.empty_append, show 22 - 22 = 0 from rfl, show 54 - 22 = 32 from rfl,
    Array.extract_eq_self_of_le hb.le]

theorem size_extract_fst {x : Array ℕ} (hx : x.size = 54) : (x.extract 0 22).size = 22 := by
  simp [hx]

theorem size_extract_snd {x : Array ℕ} (hx : x.size = 54) : (x.extract 22 54).size = 32 := by
  simp [hx]

theorem dValid_iff {x : Array ℕ} :
    dValid x = true ↔
      x.size = 54 ∧ PermArrN 22 (x.extract 0 22) = true ∧ PermArrN 32 (x.extract 22 54) = true := by
  simp only [dValid, Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem dAct_spec : ∀ k < 3, ∀ x, dValid x = true → dDec (dAct k x) = dGens k * dDec x := by
  intro k hk x hx
  obtain ⟨hsize, h1, h2⟩ := dValid_iff.1 hx
  have hs1 : (amulN (gcatArr k) (x.extract 0 22)).size = 22 := by
    rw [amulN, Array.size_map, size_extract_fst hsize]
  have hs2 : (amulN (alphaArr k) (x.extract 22 54)).size = 32 := by
    rw [amulN, Array.size_map, size_extract_snd hsize]
  rw [dAct, dMul, dGenArr_fst k hk, dGenArr_snd k hk, dDec, dGens, dDec, dDec,
    extract_fst_append hs1, extract_snd_append hs1 hs2, dGenArr_fst k hk, dGenArr_snd k hk,
    Prod.mk_mul_mk, decodeN_amulN (PermArrN_gcatArr k hk) h1,
    decodeN_amulN (PermArrN_alphaArr k hk) h2]

theorem dKey_spec :
    ∀ a b, dValid a = true → dValid b = true → dDec a = dDec b → dKey a = dKey b := by
  intro a b ha hb h
  have := decodeN_inj (dValid_iff.1 ha).2.1 (dValid_iff.1 hb).2.1 (congrArg Prod.fst h)
  rw [dKey, dKey, this]

theorem dDec_root : dDec dRoot = 1 := by
  have h1 : (idArrN 22).size = 22 := by simp [idArrN]
  have h2 : (idArrN 32).size = 32 := by simp [idArrN]
  rw [dDec, dRoot, extract_fst_append h1, extract_snd_append h1 h2, decodeN_idArrN,
    decodeN_idArrN]
  rfl

@[expose] noncomputable def D : Subgroup (Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32)) :=
  Subgroup.closure (dGens '' {k | k < 3})

theorem D_facts :
    (∀ x, x ∈ D ↔ ∃ i < dCert.pts.size, dDec dCert.pts[i]! = x) ∧ Nat.card D = dCert.pts.size :=
  card_closure_of_arrCertOK dCert_ok dAct_spec dKey_spec dDec_root

theorem natCard_D : Nat.card D = 5760 := by rw
    [D_facts.2, dCert_size]

theorem fst_injOn_D {x y : Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32)}
    (hx : x ∈ D) (hy : y ∈ D)
    (h : x.1 = y.1) : x = y := by
  obtain ⟨i, hi, rfl⟩ := (D_facts.1 x).1 hx
  obtain ⟨j, hj, rfl⟩ := (D_facts.1 y).1 hy
  have hvi := arrCertOK_valid dCert_ok hi
  have hvj := arrCertOK_valid dCert_ok hj
  have := decodeN_inj (dValid_iff.1 hvi).2.1 (dValid_iff.1 hvj).2.1 h
  have hij : i = j := arrCertOK_keys_inj dCert_ok hi hj (by rw [dKey, dKey, this])
  rw [hij]

theorem gcatArr_spec : ∀ i : Fin 3, ∀ t : Fin 22,
    (((gKB i : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) t : ℕ) =
      (gcatArr i)[(t : ℕ)]! := by
  decide +kernel

theorem dGens_fst (i : Fin 3) :
    (dGens i).1 = ((gKB i : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) := by
  ext t
  rw [dGens, dDec, dGenArr_fst i i.2, decodeN_apply (PermArrN_gcatArr i i.2), gcatArr_spec]

@[expose] noncomputable def dFst : D →* Equiv.Perm (Fin 22) := (MonoidHom.fst _ _).comp D.subtype

theorem dFst_injective : Function.Injective dFst := fun x y h =>
  Subtype.ext (fst_injOn_D x.2 y.2 h)

theorem range_dFst :
    dFst.range = Subgroup.closure
      (Set.range fun i : Fin 3 => ((gKB i : CFSG.Blueprint.NativeSporadic.M22) :
        Equiv.Perm (Fin 22))) := by
  rw [dFst, MonoidHom.range_comp, Subgroup.range_subtype, D, MonoidHom.map_closure]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, MonoidHom.coe_fst]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k, hk⟩, (dGens_fst ⟨k, hk⟩).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨dGens i, ⟨i, i.2, rfl⟩, dGens_fst i⟩

theorem closure_gKB :
    Subgroup.closure (Set.range fun i : Fin 3 => (gKB i : CFSG.Blueprint.NativeSporadic.M22)) =
      KB := by
  set S := Set.range fun i : Fin 3 => (gKB i : CFSG.Blueprint.NativeSporadic.M22)
  have hle : Subgroup.closure S ≤ KB := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact (gKB i).2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_KB]
  have hmap : (Subgroup.closure S).map CFSG.Blueprint.NativeSporadic.M22.subtype = dFst.range := by
    rw [range_dFst, MonoidHom.map_closure]
    congr 1
    ext σ
    simp [S]
  have h1 := Subgroup.card_map_of_injective (K := Subgroup.closure S)
    (f := CFSG.Blueprint.NativeSporadic.M22.subtype)
    (Subgroup.subtype_injective CFSG.Blueprint.NativeSporadic.M22)
  rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective dFst_injective).toEquiv, natCard_D] at h1
  rw [← h1]

theorem coe_mem_range_dFst
    (k : KB) :
    ((k : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) ∈ dFst.range := by
  rw [range_dFst]
  have hk : (k : CFSG.Blueprint.NativeSporadic.M22) ∈ Subgroup.closure
      (Set.range fun i : Fin 3 => (gKB i : CFSG.Blueprint.NativeSporadic.M22)) :=
    closure_gKB.ge k.2
  have := Subgroup.mem_map_of_mem CFSG.Blueprint.NativeSporadic.M22.subtype hk
  rw [MonoidHom.map_closure, ← Set.range_comp] at this
  exact this

@[expose] noncomputable def kbIncl :
    KB →* dFst.range :=
  (CFSG.Blueprint.NativeSporadic.M22.subtype.comp KB.subtype).codRestrict dFst.range
    coe_mem_range_dFst

@[expose] noncomputable def affCode :
    KB →* Equiv.Perm (Fin 32) :=
  ((MonoidHom.snd _ _).comp D.subtype).comp
    ((MonoidHom.ofInjective dFst_injective).symm.toMonoidHom.comp kbIncl)

theorem dGens_mem_D (i : Fin 3) : dGens i ∈ D := Subgroup.subset_closure ⟨i, i.2, rfl⟩

theorem dFst_apply (d : D) : dFst d = (d : Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32)).1 := rfl

theorem kbIncl_apply
    (k : KB) :
    (kbIncl k : Equiv.Perm (Fin 22)) = ((k : CFSG.Blueprint.NativeSporadic.M22) :
      Equiv.Perm (Fin 22)) := rfl

theorem kbIncl_gKB
    (i : Fin 3) :
    kbIncl (gKB i) = MonoidHom.ofInjective dFst_injective ⟨dGens i, dGens_mem_D i⟩ := by
  refine Subtype.ext ?_
  rw [MonoidHom.ofInjective_apply, kbIncl_apply, dFst_apply]
  exact (dGens_fst i).symm

theorem affCode_apply
    (k : KB) :
    affCode k = (((MonoidHom.ofInjective dFst_injective).symm (kbIncl k) : D) :
      Equiv.Perm (Fin 22) × Equiv.Perm (Fin 32)).2 := rfl

theorem affCode_gKB
    (i : Fin 3) :
    affCode (gKB i) = (dGens i).2 := by
  have h : (MonoidHom.ofInjective dFst_injective).symm (kbIncl (gKB i)) =
      ⟨dGens i, dGens_mem_D i⟩ := by
    rw [kbIncl_gKB, MulEquiv.symm_apply_apply]
  rw [affCode_apply, h]

theorem dGens_snd_apply (i : Fin 3) {m : ℕ} (hm : m < 32) :
    ((dGens i).2 ⟨m, hm⟩ : ℕ) = alpha i m := by
  rw [dGens, dDec, dGenArr_snd i i.2, decodeN_apply (PermArrN_alphaArr i i.2)]
  simp [alphaArr, hm]

theorem affCode_gKB_apply
    (i : Fin 3)
    {m : ℕ} (hm : m < 32) :
    (affCode (gKB i) ⟨m, hm⟩ : ℕ) = alpha i m := by
  rw [affCode_gKB, dGens_snd_apply i hm]

end CFSG.Monster.B.Fischer
