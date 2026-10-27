module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGeneric

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup

abbrev code (σ : P16) : List ℕ := codeN 16 σ

@[expose] def cid : List ℕ := List.range 16

@[expose] def cinv (c : List ℕ) : List ℕ := (List.range 16).map fun j => c.idxOf j

@[expose] def cconj (t x : List ℕ) : List ℕ := Core.cmul (Core.cmul t x) (cinv t)

@[expose] def ccomm (a b : List ℕ) : Bool := Core.cmul a b == Core.cmul b a

@[expose] def cinvol (a : List ℕ) : Bool := a != cid && Core.cmul a a == cid

@[expose] def ccommut (a b : List ℕ) : List ℕ := Core.cmul (Core.cmul (Core.cmul a b) (cinv a)) (cinv b)

theorem code_mul (σ τ : P16) : code (σ * τ) = Core.cmul (code σ) (code τ) := codeN_mul σ τ

theorem code_one : code 1 = cid := codeN_one

theorem code_injective : Function.Injective code := codeN_injective

theorem code_inj {σ τ : P16} : code σ = code τ ↔ σ = τ := code_injective.eq_iff

theorem code_length (σ : P16) : (code σ).length = 16 := codeN_length σ

theorem code_nodup (σ : P16) : (code σ).Nodup := by
  unfold code codeN
  rw [List.nodup_ofFn]
  intro i j h
  exact σ.injective (Fin.ext h)

theorem code_getElem (σ : P16) (j : ℕ) (h : j < (code σ).length) :
    (code σ)[j] = (σ ⟨j, by simpa [code_length] using h⟩ : ℕ) := by
  simp only [code, codeN, List.getElem_ofFn]

theorem code_inv (σ : P16) : code σ⁻¹ = cinv (code σ) := by
  apply List.ext_getElem
  · simp [code_length, cinv]
  · intro j h1 h2
    have hj : j < 16 := by simpa [code_length] using h1
    simp only [cinv, List.getElem_map, List.getElem_range]
    rw [code_getElem]
    set m := σ⁻¹ ⟨j, hj⟩ with hm
    have hlt : (m : ℕ) < (code σ).length := by rw [code_length]; exact m.2
    have hget : (code σ)[(m : ℕ)] = j := by
      rw [code_getElem]
      simp [hm]
    have := List.get_idxOf (code_nodup σ) ⟨m, hlt⟩
    simp only [List.get_eq_getElem] at this
    rw [hget] at this
    exact this.symm

theorem code_conj (t x : P16) : code (t * x * t⁻¹) = cconj (code t) (code x) := by
  rw [code_mul, code_mul, code_inv, cconj]

theorem ccomm_iff {a b : P16} : ccomm (code a) (code b) = true ↔ a * b = b * a := by
  rw [ccomm, beq_iff_eq, ← code_mul, ← code_mul, code_inj]

theorem cinvol_iff {a : P16} : cinvol (code a) = true ↔ a ≠ 1 ∧ a * a = 1 := by
  rw [cinvol, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq, ← code_mul, ← code_one, code_inj,
    code_inj]

theorem code_commut (a b : P16) : code (a * b * a⁻¹ * b⁻¹) = ccommut (code a) (code b) := by
  rw [code_mul, code_mul, code_mul, code_inv, code_inv, ccommut]

structure LDesc (H : Subgroup P16) (L : List (List ℕ)) : Prop where
  mem : ∀ σ, σ ∈ H ↔ code σ ∈ L
  surj : ∀ c ∈ L, ∃ σ ∈ H, code σ = c

theorem LDesc.card {H : Subgroup P16} {L : List (List ℕ)} (h : LDesc H L) (hnd : L.Nodup) :
    Nat.card H = L.length := by
  classical
  let f : H → L.toFinset := fun x => ⟨code x, List.mem_toFinset.2 ((h.mem x).1 x.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (code_injective (congrArg Subtype.val hxy)),
      fun ⟨c, hc⟩ => ?_⟩
    obtain ⟨σ, hσ, rfl⟩ := h.surj c (List.mem_toFinset.1 hc)
    exact ⟨⟨σ, hσ⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

theorem exists_list_of_codes {S : Set P16} :
    ∀ {L : List (List ℕ)}, (∀ c ∈ L, ∃ x ∈ S, code x = c) →
      ∃ l : List P16, l.map code = L ∧ ∀ x ∈ l, x ∈ S
  | [], _ => ⟨[], rfl, by simp⟩
  | c :: L, h => by
    obtain ⟨x, hx, rfl⟩ := h c List.mem_cons_self
    obtain ⟨l, hl, hlS⟩ := exists_list_of_codes (L := L) fun d hd => h d (List.mem_cons_of_mem _ hd)
    exact ⟨x :: l, by simp [hl], by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hlS y hy⟩

@[expose] def closureC (gc : List (List ℕ)) : Subgroup P16 := closure {σ : P16 | code σ ∈ gc}

theorem ldesc_closureC {gc : List (List ℕ)} (hgc : ∀ c ∈ gc, ∃ σ : P16, code σ = c)
    {tree : List (ℕ × ℕ)} {tbl : List (List ℕ)}
    (h : Core.tblCheckC cid gc (Core.buildCodes cid gc tree) tbl = true) :
    LDesc (closureC gc) (Core.buildCodes cid gc tree) := by
  obtain ⟨gens, hg, -⟩ := exists_list_of_codes (S := Set.univ) (L := gc)
    fun c hc => by obtain ⟨σ, rfl⟩ := hgc c hc; exact ⟨σ, trivial, rfl⟩
  have hset : {σ : P16 | code σ ∈ gc} = {g | g ∈ gens} := by
    ext σ
    simp only [Set.mem_setOf_eq, ← hg, List.mem_map]
    exact ⟨fun ⟨τ, hτ, he⟩ => code_injective he ▸ hτ, fun hσ => ⟨σ, hσ, rfl⟩⟩
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tblN (n := 16) hg h
  refine ⟨fun σ => ?_, fun c hc => ?_⟩
  · rw [closureC, hset]
    exact hmem σ
  · obtain ⟨σ, hσ, he⟩ := hsurj c hc
    exact ⟨σ, by rw [closureC, hset]; exact hσ, he⟩

theorem closureC_le {gc : List (List ℕ)} {H : Subgroup P16}
    (h : ∀ σ : P16, code σ ∈ gc → σ ∈ H) : closureC gc ≤ H :=
  (closure_le _).2 fun σ hσ => h σ hσ

theorem subset_closureC {gc : List (List ℕ)} {σ : P16} (h : code σ ∈ gc) : σ ∈ closureC gc :=
  subset_closure h

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
