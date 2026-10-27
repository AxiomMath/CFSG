module

public import CFSG.Sporadic.Recognition.LyonsFinalLyInputs
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Ly.Primitive

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.CosetTable CFSG.Sporadic.He.Native CFSG.Sporadic.Ly

theorem wordM_cons (g gi : Fin 6 → Mat) (l : Fin 6 × Bool) (w : List (Fin 6 × Bool)) :
    wordM g gi (l :: w) = mulM 5 111 (letterM g gi l) (wordM g gi w) := by
  simp only [wordM, List.foldr_cons]

theorem toMat_wordM (g gi : Fin 6 → Mat) (w : List (Fin 6 × Bool)) :
    toMat 5 111 (wordM g gi w) = (w.map fun l => toMat 5 111 (letterM g gi l)).prod := by
  induction w with
  | nil => simp only [wordM, List.foldr_nil, List.map_nil, List.prod_nil, toMat_idM]
  | cons l w ih => rw [wordM_cons, toMat_mulM, ih, List.map_cons, List.prod_cons]

structure LyRelFacts (R : List (List (Fin 6 × Bool))) : Prop where
  inv : ∀ i : Fin 6, toMat 5 111 (genM i) * toMat 5 111 (genInvM i) = 1
  rel : ∀ r ∈ R, (r.map fun l => toMat 5 111 (letterM genM genInvM l)).prod = 1
  wA : (wordA.map fun l => toMat 5 111 (letterM genM genInvM l)).prod = toMat 5 111 Native.matA
  wB : (wordB.map fun l => toMat 5 111 (letterM genM genInvM l)).prod = toMat 5 111 Native.matB

theorem lyRelFacts_of_check {R : List (List (Fin 6 × Bool))} (h : lyRelCheck R = true) :
    LyRelFacts R := by
  simp only [lyRelCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun i => ?_, fun r hr => ?_, ?_, ?_⟩
  · have := congrArg (toMat 5 111) (h1 i)
    rwa [toMat_mulM, toMat_idM] at this
  · have := congrArg (toMat 5 111) (h2 r hr)
    rwa [toMat_wordM, toMat_idM] at this
  · have := congrArg (toMat 5 111) h3
    rwa [toMat_wordM] at this
  · have := congrArg (toMat 5 111) h4
    rwa [toMat_wordM] at this

section Hom

variable {R : List (List (Fin 6 × Bool))} (F : LyRelFacts R)

@[expose] noncomputable def genU (i : Fin 6) : GL (Fin 111) (ZMod 5) :=
  ⟨toMat 5 111 (genM i), toMat 5 111 (genInvM i), F.inv i, mul_eq_one_comm.1 (F.inv i)⟩

theorem val_genU (i : Fin 6) : ((genU F i : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111)
    (ZMod 5)) = toMat 5 111 (genM i) := rfl

theorem val_genU_inv (i : Fin 6) : (((genU F i)⁻¹ : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111)
    (Fin 111) (ZMod 5)) = toMat 5 111 (genInvM i) := rfl

theorem val_lift_mk (w : List (Fin 6 × Bool)) :
    ((FreeGroup.lift (genU F) (FreeGroup.mk w) : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111)
      (Fin 111) (ZMod 5)) = (w.map fun l => toMat 5 111 (letterM genM genInvM l)).prod := by
  induction w with
  | nil =>
    rw [← FreeGroup.one_eq_mk, map_one, Units.val_one]
    simp only [List.map_nil, List.prod_nil]
  | cons l w ih =>
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    have key : ((FreeGroup.lift (genU F) (FreeGroup.mk [l]) : GL (Fin 111) (ZMod 5)) :
        Matrix (Fin 111) (Fin 111) (ZMod 5)) = toMat 5 111 (letterM genM genInvM l) := by
      obtain ⟨i, b⟩ := l
      cases b
      · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of, val_genU_inv]
        simp only [letterM, Bool.false_eq_true, ite_false]
      · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of,
          val_genU]
        simp only [letterM, ite_true]
    rw [e, map_mul, Units.val_mul, ih, key, List.map_cons, List.prod_cons]

@[expose] noncomputable def lyHom : PG 6 R →* GL (Fin 111) (ZMod 5) :=
  PresentedGroup.toGroup (f := genU F) (fun r hr => by
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    apply Units.ext
    rw [val_lift_mk, F.rel w hw, Units.val_one])

theorem lyHom_mk (w : List (Fin 6 × Bool)) :
    lyHom F (PresentedGroup.mk _ (FreeGroup.mk w)) = FreeGroup.lift (genU F) (FreeGroup.mk w) :=
  rfl

theorem gA_mem_range : gA ∈ (lyHom F).range := by
  refine ⟨PresentedGroup.mk _ (FreeGroup.mk wordA), ?_⟩
  rw [lyHom_mk]
  apply Units.ext
  rw [val_lift_mk, F.wA, toMat_matA]
  rfl

theorem gB_mem_range : gB ∈ (lyHom F).range := by
  refine ⟨PresentedGroup.mk _ (FreeGroup.mk wordB), ?_⟩
  rw [lyHom_mk]
  apply Units.ext
  rw [val_lift_mk, F.wB, toMat_matB]
  rfl

theorem J_le_range : J ≤ (lyHom F).range :=
  (Subgroup.closure_le _).2 (by
    rintro x (rfl | rfl)
    · exact gA_mem_range F
    · exact gB_mem_range F)

end Hom

theorem J_eq_range_lyHom {R : List (List (Fin 6 × Bool))}
    [Finite (PG 6 R)] (F : LyRelFacts R) (hcard : Nat.card (PG 6 R) ≤ 51765179004000000) :
    J = (lyHom F).range := by
  have hrange : Nat.card (lyHom F).range ≤ Nat.card (PG 6 R) :=
    Nat.card_le_card_of_surjective (lyHom F).rangeRestrict (lyHom F).rangeRestrict_surjective
  exact Subgroup.eq_of_le_of_card_ge (J_le_range F) (by rw [card_J]; exact hrange.trans hcard)

theorem nonempty_mulEquiv_of_lyRelCheck
    {R : List (List (Fin 6 × Bool))} [Finite (PG 6 R)]
    (hcard : Nat.card (PG 6 R) ≤ 51765179004000000) (h : lyRelCheck R = true) :
    Nonempty (Blueprint.NativeSporadic.Ly ≃* PG 6 R) := by
  have hJ := J_eq_range_lyHom (lyRelFacts_of_check h) hcard
  let ψ' : PG 6 R →* J := (lyHom (lyRelFacts_of_check h)).codRestrict J fun x => hJ ▸ ⟨x, rfl⟩
  have hsurj : Function.Surjective ψ' := by
    intro y
    have hy : (y : GL (Fin 111) (ZMod 5)) ∈ (lyHom (lyRelFacts_of_check h)).range := hJ ▸ y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨e⟩ := Bridge.nonempty_mulEquiv_of_surjective ψ' hsurj hcard (le_of_eq card_J.symm)
  exact ⟨lyEquivJ.trans e⟩

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
