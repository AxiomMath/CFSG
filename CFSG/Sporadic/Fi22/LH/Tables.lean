module

public import CFSG.Sporadic.Fi22.LH.Parts
public import CFSG.Sporadic.Fi22.LH.Defs

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tT_get {c : ℕ} (hc : c < 3510) : tT[c]! = tabOf orb c := by
  unfold tT tauAll
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem rep_tT
    {c : ℕ} (hc : c < 3510) : Rep 3510 tT[c]! (conjPt c) := by
  rw [tT_get hc]
  exact rep_cTab c hc

section Generic

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

theorem smul_val_of_rep {g : G} {T : Table} (hT : Rep 3510 T g) (i : Fin 3510) :
    (g • i).val = ap T i.val := by
  rw [hT i.val i.2, idx_of_lt g i.2]

theorem ap_lt_of_rep {g : G} {T : Table} (hT : Rep 3510 T g) {i : ℕ} (hi : i < 3510) :
    ap T i < 3510 := by
  rw [hT i hi]
  exact idx_lt g hi

end Generic

theorem ap_tT_lt
    {c i : ℕ} (hc : c < 3510) (hi : i < 3510) : ap tT[c]! i < 3510 :=
  ap_lt_of_rep (rep_tT hc) hi

theorem conjPt_smul_val {c : ℕ} (hc : c < 3510) (i : Fin 3510) :
    ((conjPt c : J) • i).val = ap tT[c]! i.val :=
  smul_val_of_rep (rep_tT hc) i

theorem conjPt_mul_conjPt {c i : ℕ} (hc : c < 3510) (hi : i < 3510) :
    conjPt c * conjPt i * conjPt c = conjPt (ap tT[c]! i) := by
  have h := conjPt_smul (conjPt c) ⟨i, hi⟩
  rw [conjPt_smul_val hc, conjPt_inv hc] at h
  exact h.symm

theorem conjPt_commute_iff
    {c i : ℕ} (hc : c < 3510) (hi : i < 3510) :
    conjPt c * conjPt i = conjPt i * conjPt c ↔ ap tT[c]! i = i := by
  have h := conjPt_mul_conjPt hc hi
  have hcc : conjPt c * conjPt c = 1 := conjPt_mul_self hc
  constructor
  · intro hcomm
    have e : conjPt (ap tT[c]! i) = conjPt i := by
      rw [← h, hcomm, mul_assoc, hcc, mul_one]
    exact conjPt_inj (by rw [orb_size]; exact ap_tT_lt hc hi) (by rw [orb_size]; exact hi) e
  · intro he
    rw [he] at h
    calc conjPt c * conjPt i = conjPt c * conjPt i * conjPt c * conjPt c := by
          rw [mul_assoc (conjPt c * conjPt i), hcc, mul_one]
      _ = conjPt i * conjPt c := by rw [h]

theorem ptD_val' (i : Fin 3510) : (ptD i : J) = conjPt i.val := rfl

theorem ptD_commute_iff (i j : Fin 3510) :
    (ptD i : J) * ptD j = ptD j * ptD i ↔ ap tT[i.val]! j.val = j.val :=
  conjPt_commute_iff i.2 j.2

theorem ptD_mul_ptD (i j : Fin 3510) :
    (ptD i : J) * ptD j * ptD i = conjPt (ap tT[i.val]! j.val) :=
  conjPt_mul_conjPt i.2 j.2

@[expose] def bset (B : Bits) : Set (Fin 3510) := {x | bitAt B x.val = true}

@[expose] noncomputable def dset (B : Bits) : Set D := ptD '' bset B

theorem mem_bset {B : Bits} {x : Fin 3510} : x ∈ bset B ↔ bitAt B x.val = true := Iff.rfl

theorem ptD_mem_dset
    {B : Bits} {i : Fin 3510} : ptD i ∈ dset B ↔ bitAt B i.val = true := by
  unfold dset
  rw [ptD.injective.mem_set_image]
  rfl

theorem mem_dset
    {B : Bits} {x : D} : x ∈ dset B ↔ bitAt B (ptD.symm x).val = true := by
  rw [← ptD.apply_symm_apply x, ptD_mem_dset, Equiv.apply_symm_apply]

theorem dset_eq_of_bitAt
    {A B : Bits} (h : ∀ x < 3510, bitAt A x = bitAt B x) :
    dset A = dset B := by
  ext y
  rw [mem_dset, mem_dset, h _ (ptD.symm y).2]

theorem bitAt_eq_of_dset_eq
    {A B : Bits} (h : dset A = dset B) {x : ℕ} (hx : x < 3510) :
    bitAt A x = bitAt B x := by
  have h' := congrArg (fun S => ptD ⟨x, hx⟩ ∈ S) h
  simp only [ptD_mem_dset, eq_iff_iff] at h'
  cases hA : bitAt A x <;> cases hB : bitAt B x <;> simp_all

theorem conjPerm_ptD
    (g : J) (i : Fin 3510) : Pair.conjPerm pair_D g (ptD i) = ptD (g • i) := by
  apply Subtype.ext
  rw [Pair.conjPerm_apply, ptD_val', ptD_val', conjPt_smul]

theorem mapsOnto_spec {T : Table} {A B : Bits} (h : mapsOnto T A B = true) {x : ℕ}
    (hx : x < 3510) : bitAt B (ap T x) = bitAt A x := by
  have := allIn_eq_true.1 h x (Nat.zero_le _) hx
  simpa using this

section Generic

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

theorem smul_mem_bset_iff {T : Table} {g : G} (hT : Rep 3510 T g) {A B : Bits}
    (h : mapsOnto T A B = true) (x : Fin 3510) : g • x ∈ bset B ↔ x ∈ bset A := by
  rw [mem_bset, mem_bset, smul_val_of_rep hT, mapsOnto_spec h x.2]

theorem image_bset {T : Table} {g : G} (hT : Rep 3510 T g) {A B : Bits}
    (h : mapsOnto T A B = true) : (fun x => g • x) '' bset A = bset B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (smul_mem_bset_iff hT h x).2 hx
  · intro hy
    refine ⟨g⁻¹ • y, (smul_mem_bset_iff hT h _).1 ?_, smul_inv_smul g y⟩
    rwa [smul_inv_smul]

end Generic

theorem conjPerm_image_ptD (g : J) (S : Set (Fin 3510)) :
    ⇑(Pair.conjPerm pair_D g) '' (ptD '' S) = ptD '' ((fun x => g • x) '' S) := by
  rw [Set.image_image, Set.image_image]
  simp only [conjPerm_ptD]

theorem conjPerm_image_dset
    {T : Table} {g : J} (hT : Rep 3510 T g) {A B : Bits}
    (h : mapsOnto T A B = true) : ⇑(Pair.conjPerm pair_D g) '' dset A = dset B := by
  unfold dset
  rw [conjPerm_image_ptD, image_bset hT h]

theorem lhData_parts :
    lhData.size = 2 ∧ ∀ i < 2, lhData[i]!.size = 351 ∧ (lhData[i]!)[0]! = 0 ∧
    (∀ k < 350, (lhData[i]!)[k]! < (lhData[i]!)[k + 1]!) ∧ (lhData[i]!)[350]! < 3510 :=
  dataOK_spec lh_parts.2.1

theorem bitAt_B_iff {i : ℕ} (hi : i < 2) {x : ℕ} (hx : x < 3510) :
    bitAt lhc.B[i]! x = true ↔ x ∈ lhData[i]! := by
  rw [memOK_spec (lh_parts.2.2.2.2.2.2.2.2.2.1 i hi).1 hx, Array.contains_iff_mem]

theorem lhRoot_eq
    (i : Fin 2) : lhRoot i = dset lhc.B[i.val]! := by
  unfold lhRoot dset bset
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [bitAt_B_iff i.2 x.2]

theorem ptD_mem_lhRoot
    {i : Fin 2} {x : Fin 3510} : ptD x ∈ lhRoot i ↔ bitAt lhc.B[i.val]! x.val :=
  by rw [lhRoot_eq, ptD_mem_dset]

end CFSG.Sporadic.Fi22
