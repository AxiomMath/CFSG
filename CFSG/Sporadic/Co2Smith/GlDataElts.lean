module

public import CFSG.Sporadic.Co2Smith.GlData
public import CFSG.Sporadic.Co2Smith.GlDataCheck

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Perm

theorem co2PermHom_apply_of_maps {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    {x y : ℕ} (hx : x < 2300) (hy : y < 2300) (h : Native.glMaps R x y = true) :
    co2PermHom g ⟨x, hx⟩ = ⟨y, hy⟩ := by
  apply Fin.ext
  apply co2Vec_injective (Fin.isLt _) hy
  have e := co2Vec_permEquiv g ⟨x, hx⟩
  rw [co2PermEquiv_apply] at e
  rw [e, co2Vec_eq hx, val_mulVec hg, beq_iff_eq.1 h, ← co2Vec_eq hy]

theorem rep_co2PermHom_of_permOK {g : K} {R p : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    (h : Native.glPermOK R p = true) : p.size = 2300 ∧ Rep 2300 p (co2PermHom g) := by
  simp only [Native.glPermOK, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun x => ?_⟩
  have hx := allLt_spec h.2 x.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
  have e := co2PermHom_apply_of_maps hg x.2 hx.1 (by
    rw [Native.glMaps, beq_iff_eq, hx.2])
  rw [e]

end Perm

theorem glElem_parts :
    Native.glLetOK = true ∧ Native.glOrdOK = true ∧ Native.glPtOK = true ∧
      Native.glCOK = true ∧ Native.glArcOK = true ∧ Native.glGenOK = true := by
  have h := glElem_check
  simp only [Native.glElemOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem glLet_spec :
    (∀ k ∈ Native.glCzLet, Native.commRows Native.glRows[k]! Native.glZ = true) ∧
    (∀ k ∈ Native.glC0Let, Native.commRows Native.glRows[k]! Native.glAl = true ∧
      Native.commRows Native.glRows[k]! Native.glGa = true) ∧
    Native.commRows Native.glU Native.glZ = true := by
  have h := glElem_parts.1
  simp only [Native.glLetOK, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

theorem glElt_val {k : ℕ} (hk : k < 22) :
    (glElt k).val.val = rowsMatrix 22 Native.glRows[k]! :=
  glL.val_eq k (glRows_size ▸ hk)

theorem z0_val' : z0.val.val = rowsMatrix 22 Native.glZ :=
  x16K_eq ▸ x16K_val

section Check

theorem glElt_mem_Cz {k : ℕ} (hk : k ∈ Native.glCzLet) : glElt k ∈ Cz := by
  have hk22 : k < 22 := by simp [Native.glCzLet] at hk; omega
  exact mem_Cz_of_comm (comm_of_commRows (glElt_val hk22) z0_val' (glLet_spec.1 k hk))

theorem glElt_mem_C0c {k : ℕ} (hk : k ∈ Native.glC0Let) : glElt k ∈ C0c := by
  have hk22 : k < 22 := by simp [Native.glC0Let] at hk; omega
  rw [mem_C0c]
  exact ⟨(comm_of_commRows (glElt_val hk22) α3K_val (glLet_spec.2.1 k hk).1).symm,
    (comm_of_commRows (glElt_val hk22) γ3K_val (glLet_spec.2.1 k hk).2).symm⟩

theorem glE_mem_C0c {w : List ℕ} (hw : ∀ k ∈ w, k ∈ Native.glC0Let) : glE w ∈ C0c :=
  glE_mem_of_letters (fun _ hk => glElt_mem_C0c hk) hw

theorem glE_mem_Cz {w : List ℕ} (hw : ∀ k ∈ w, k ∈ Native.glCzLet) : glE w ∈ Cz :=
  glE_mem_of_letters (fun _ hk => glElt_mem_Cz hk) hw

theorem α3K_mem_Cz : α3K ∈ Cz := glE_mem_Cz (by decide)

theorem γ3K_mem_Cz : γ3K ∈ Cz := glE_mem_Cz (by decide)

@[expose] noncomputable def α3c : Cz := ⟨α3K, α3K_mem_Cz⟩

@[expose] noncomputable def γ3c : Cz := ⟨γ3K, γ3K_mem_Cz⟩

theorem uK_mem_C0c : uK ∈ C0c := glE_mem_C0c (by decide)

theorem uK_mem_Cz : uK ∈ Cz := mem_Cz_of_comm (comm_of_commRows uK_val z0_val' glLet_spec.2.2)

theorem x16K_mem_C0c : x16K ∈ C0c := glE_mem_C0c (by decide)

theorem x61K_mem_C0c : x61K ∈ C0c := glE_mem_C0c (by decide)

theorem δ0hK_mem_C0c : δ0hK ∈ C0c := glE_mem_C0c (by decide)

theorem δ1hK_mem_C0c : δ1hK ∈ C0c := glE_mem_C0c (by decide)

theorem w1K_mem_C0c : w1K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem x16K_mem_C0c x61K_mem_C0c) x16K_mem_C0c

theorem w2K_mem_C0c : w2K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c w1K_mem_C0c) δ1hK_mem_C0c

theorem w3K_mem_C0c : w3K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem δ0hK_mem_C0c w2K_mem_C0c) δ0hK_mem_C0c

theorem w0K_mem_C0c : w0K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem w1K_mem_C0c w2K_mem_C0c) w3K_mem_C0c

theorem vK_mem_C0c : vK ∈ C0c := C0c.mul_mem (C0c.mul_mem uK_mem_C0c w0K_mem_C0c) uK_mem_C0c

theorem glFormK_mem_C0c (t : ℕ) : glFormK t ∈ C0c := by
  unfold glFormK
  split
  · exact uK_mem_C0c
  · split
    · exact vK_mem_C0c
    · exact C0c.one_mem

end Check

end CFSG.Sporadic.Co2Smith
