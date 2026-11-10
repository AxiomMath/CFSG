
module

public import CFSG.Monster.B.Fischer.InducedCode
public import CFSG.Monster.B.Fischer.InducedEncodingInputs

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

theorem aCat_spec : ∀ t : Fin 22, ((m22gA : Equiv.Perm (Fin 22)) t : ℕ) = aCat[(t : ℕ)]! := by
  decide +kernel

theorem bCat_spec : ∀ t : Fin 22, ((m22gB : Equiv.Perm (Fin 22)) t : ℕ) = bCat[(t : ℕ)]! := by
  decide +kernel

theorem bInvCat_spec :
    ∀ t : Fin 22, ((m22gB⁻¹ : Equiv.Perm (Fin 22)) t : ℕ) = bInvCat[(t : ℕ)]! := by
  decide +kernel

theorem m22gA_inv : (m22gA⁻¹ : Equiv.Perm (Fin 22)) = m22gA := by
  ext t
  revert t
  decide +kernel

theorem PermArrN_letterCat (z : ℤ) : PermArrN 22 (letterCat z) = true := by
  unfold letterCat
  split_ifs <;> decide +kernel

theorem decodeN_letterCat (z : ℤ) :
    decodeN 22 (letterCat z) = ((letterM22 z : CFSG.Blueprint.NativeSporadic.M22) :
      Equiv.Perm (Fin 22)) := by
  ext t
  rw [decodeN_apply (PermArrN_letterCat z)]
  unfold letterCat letterM22
  split_ifs
  · exact (aCat_spec t).symm
  · rw [Subgroup.coe_inv, m22gA_inv]
    exact (aCat_spec t).symm
  · exact (bCat_spec t).symm
  · rw [Subgroup.coe_inv]
    exact (bInvCat_spec t).symm

theorem wordCat_spec (w : List ℤ) :
    PermArrN 22 (wordCat w) = true ∧
      decodeN 22 (wordCat w) = ((wordM22 w : CFSG.Blueprint.NativeSporadic.M22) :
        Equiv.Perm (Fin 22)) := by
  induction w with
  | nil => exact ⟨PermArrN_idArrN, by rw [wordCat, List.foldr_nil, decodeN_idArrN]; rfl⟩
  | cons z w ih =>
    have e : wordCat (z :: w) = amulN (letterCat z) (wordCat w) := rfl
    rw [e]
    refine ⟨PermArrN_amulN (PermArrN_letterCat z) ih.1, ?_⟩
    rw [decodeN_amulN (PermArrN_letterCat z) ih.1, decodeN_letterCat, ih.2, wordM22, wordM22,
      List.map_cons, List.prod_cons, Subgroup.coe_mul]

def hRep (i : ℕ) : CFSG.Blueprint.NativeSporadic.M22 := wordM22 (blockWord i)

theorem hCat_spec (i : ℕ) : PermArrN 22 (hCat i) = true ∧
    decodeN 22 (hCat i) = ((hRep i : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) :=
  wordCat_spec _

def jEmb : Fin 22 ↪ Fin 24 := ⟨jCat, jCat_injective⟩

theorem B₀_eq_map_jCat : B₀ = catB₀.map jEmb := by decide

theorem map_psiHom_B₀ (k : Equiv.Perm (Fin 22)) :
    B₀.map (psiHom k).toEmbedding = (catB₀.map k.toEmbedding).map jEmb := by
  rw [B₀_eq_map_jCat, Finset.map_map, Finset.map_map]
  congr 1
  ext c
  simp [jEmb, psiHom_jCat]

theorem map_decodeN_eq_hexCat {arr : Array ℕ} (h : PermArrN 22 arr = true) :
    catB₀.map (decodeN 22 arr).toEmbedding = hexCat arr := by
  rw [hexCat, Finset.map_eq_image]
  congr 1
  funext c
  apply Fin.ext
  rw [Equiv.coe_toEmbedding, decodeN_apply h, arrFunN_val h]

theorem hexad_hRep (i : ℕ) :
    B₀.map (psiHom (hRep i)).toEmbedding = (hexCat (hCat i)).map jEmb := by
  rw [map_psiHom_B₀, ← (hCat_spec i).2, map_decodeN_eq_hexCat (hCat_spec i).1]

theorem hexad_mem_ℬ₀
    (k : CFSG.Blueprint.NativeSporadic.M22) : B₀.map (psiHom k).toEmbedding ∈ ℬ₀ :=
  map_mem_ℬ₀ k B₀_mem_ℬ₀

theorem mem_KB_of_hexad {k l : CFSG.Blueprint.NativeSporadic.M22}
    (h : B₀.map (psiHom k).toEmbedding = B₀.map (psiHom l).toEmbedding) : k⁻¹ * l ∈ KB := by
  rw [mem_KB, Subgroup.coe_mul, map_mul, map_perm_mul, ← h, ← map_perm_mul, Subgroup.coe_inv,
    map_inv, inv_mul_cancel, map_perm_one]

theorem zRel_equivalence :
    Equivalence zRel where
  refl p := ⟨1, by simp, by simp⟩
  symm := by
    rintro ⟨k, q⟩ ⟨k', q'⟩ ⟨h, h1, h2⟩
    simp only at h1 h2 ⊢
    refine ⟨h⁻¹, ?_, ?_⟩
    · rw [h1, Subgroup.coe_inv, mul_inv_cancel_right]
    · rw [h2, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
  trans := by
    rintro ⟨k, q⟩ ⟨k', q'⟩ ⟨k'', q''⟩ ⟨h, h1, h2⟩ ⟨h', h1', h2'⟩
    simp only at h1 h2 h1' h2' ⊢
    refine ⟨h' * h, ?_, ?_⟩
    · rw [h1, h1', Subgroup.coe_mul, mul_assoc]
    · rw [h2', h2, map_mul, Equiv.Perm.mul_apply]

theorem zMk_eq_iff
    {k k' : CFSG.Blueprint.NativeSporadic.M22} {q q' : Q₀} :
    zMk k q = zMk k' q' ↔ zRel (k, q) (k', q') := by
  constructor
  · intro h
    exact (zRel_equivalence.eqvGen_iff).1 (Quot.eqvGen_exact h)
  · intro h
    exact Quot.sound h

theorem hexadOf_zMk
    (k : CFSG.Blueprint.NativeSporadic.M22) (q : Q₀) :
    hexadOf (zMk k q) = B₀.map (psiHom k).toEmbedding := rfl

def decZ
    (p : Fin 77 × Q₀) : Z := zMk (hRep p.1) p.2

noncomputable def decY
    (n : ℕ) : Y :=
  if h : n < 22 then .inl (coordAt ⟨n, h⟩)
  else if n < 1046 then .inr (.inl (wv (n - 22)))
  else .inr (.inr (zMk (hRep ((n - 1046) / 32)) (qv ((n - 1046) % 32))))

end CFSG.Monster.B.Fischer
