module

public import CFSG.Quasithin.Background.SmithB45J2Iso
public import CFSG.Quasithin.Background.SmithB45MatRep
public import Certificates.Certificate260411
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

namespace CFSG.Quasithin.J2Mod

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.J2Row
  CFSG.Quasithin.J2Bits FieldFour Matrix Module
open scoped Kronecker

theorem j2_module_checks :
    subOK tAA tBB B14 P14 = true ∧
    subOK tA14 tB14 B64 P64 = true ∧
    subOK tAAb tBBb B160 P160 = true ∧
    c6.check tA6 tB6 = true ∧
    c14.check t14A t14B = true ∧
    c36.check t36A t36B = true ∧
    c64.check t64A t64B = true ∧
    c84.check t84A t84B = true ∧
    c160.check t160A t160B = true ∧
    Matrix.trace (untab (wordT tA6 tB6 tw6)) = ω ∧
    Matrix.trace (untab (wordT t14A t14B tw14)) = ω₂ ∧
    Matrix.trace (untab (wordT t64A t64B tw64)) = ω₂ :=
  Certificates.certificate260411

abbrev G6 : Type := ↥Γ₆

@[expose] noncomputable def ga : G6 := ⟨gA, gA_mem⟩

@[expose] noncomputable def gb : G6 := ⟨gB, gB_mem⟩

theorem closure_gab : Subgroup.closure ({ga, gb} : Set G6) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (k := ({gA, gB} : Set GL6))
  have hs : ((↑) : ↥(Subgroup.closure ({gA, gB} : Set GL6)) → GL6) ⁻¹' {gA, gB} =
      ({ga, gb} : Set G6) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [hs] at h
  exact h

theorem forall_gens {F : Type*} {n : ℕ} {R : G6 → Prop} {Ka Kb : Vector (Vector F n) n}
    {p : Vector (Vector F n) n → Prop} (h : ∀ K ∈ [Ka, Kb], p K) (ha : p Ka → R ga)
    (hb : p Kb → R gb) : ∀ s ∈ ({ga, gb} : Set G6), R s := by
  rintro s (rfl | rfl)
  · exact ha (h Ka (by simp))
  · exact hb (h Kb (by simp))

@[expose] noncomputable def rep6a : G6 →* Matrix (Fin 6) (Fin 6) FieldFour :=
  (Units.coeHom _).comp Γ₆.subtype

theorem untab_tA6_eq : untab tA6 = a6.toMat := by
  decide +kernel

theorem untab_tB6_eq : untab tB6 = b6.toMat := by
  decide +kernel

theorem untab_tA6 : untab tA6 = rep6a ga :=
  untab_tA6_eq

theorem untab_tB6 : untab tB6 = rep6a gb :=
  untab_tB6_eq

section Twist

variable {G : Type*} [Group G] {n : ℕ}

@[expose] noncomputable def twist (M : G →* Matrix (Fin n) (Fin n) FieldFour) :
    G →* Matrix (Fin n) (Fin n) FieldFour :=
  (frob.mapMatrix : Matrix (Fin n) (Fin n) FieldFour →+* _).toMonoidHom.comp M

theorem twist_apply (M : G →* Matrix (Fin n) (Fin n) FieldFour) (g : G) :
    twist M g = (M g).map frob :=
  rfl

theorem untab_mapTab_frob {t : Vector (Vector FieldFour n) n}
    {M : G →* Matrix (Fin n) (Fin n) FieldFour} {g : G} (h : untab t = M g) :
    untab (mapTab frob t) = twist M g := by
  rw [untab_mapTab, h]
  rfl

theorem matrixBaseChange_twist {K : Type*} [Field K] (φ : FieldFour →+* K)
    (M : G →* Matrix (Fin n) (Fin n) FieldFour) :
    matrixBaseChange φ (twist M) = matrixBaseChange (φ.comp frob) M := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [matrixBaseChange_apply, matrixBaseChange_apply, twist_apply, Matrix.map_map]
  rfl

theorem trace_twist (M : G →* Matrix (Fin n) (Fin n) FieldFour) (g : G) :
    Matrix.trace (twist M g) = frob (Matrix.trace (M g)) := by
  rw [twist_apply, Matrix.trace, Matrix.trace, map_sum]
  rfl

end Twist

noncomputable abbrev rep6b : G6 →* Matrix (Fin 6) (Fin 6) FieldFour :=
  twist rep6a

section Reps

noncomputable abbrev repAA : G6 →* Matrix (Fin (6 * 6)) (Fin (6 * 6)) FieldFour :=
  kronRep rep6a rep6a

theorem untab_tAA : untab tAA = repAA ga := by
  rw [tAA, untab_kronTab, untab_tA6, kronRep_apply]

theorem untab_tBB : untab tBB = repAA gb := by
  rw [tBB, untab_kronTab, untab_tB6, kronRep_apply]

noncomputable abbrev rep36 : G6 →* Matrix (Fin (6 * 6)) (Fin (6 * 6)) FieldFour :=
  kronRep rep6a rep6b

theorem untab_t36A : untab t36A = rep36 ga := by
  rw [t36A, untab_kronTab, untab_mapTab_frob untab_tA6, untab_tA6, kronRep_apply]

theorem untab_t36B : untab t36B = rep36 gb := by
  rw [t36B, untab_kronTab, untab_mapTab_frob untab_tB6, untab_tB6, kronRep_apply]

theorem inv14 : untab P14 * untab B14 = 1 ∧
    ∀ g, repAA g * untab B14 = untab B14 * (untab P14 * repAA g * untab B14) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec j2_module_checks.1
  refine ⟨hPB, subInv_of_closure closure_gab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩
  · intro h
    simpa only [untab_tAA] using h
  · intro h
    simpa only [untab_tBB] using h

noncomputable def rep14a : G6 →* Matrix (Fin 14) (Fin 14) FieldFour :=
  subRep repAA (untab B14) (untab P14) inv14.1 inv14.2

theorem untab_t14A : untab t14A = rep14a ga := by
  rw [t14A, untab_mulT, untab_mulT, untab_tAA, rep14a, subRep_apply, Matrix.mul_assoc]

theorem untab_t14B : untab t14B = rep14a gb := by
  rw [t14B, untab_mulT, untab_mulT, untab_tBB, rep14a, subRep_apply, Matrix.mul_assoc]

noncomputable abbrev rep14b : G6 →* Matrix (Fin 14) (Fin 14) FieldFour :=
  twist rep14a

theorem untab_t14bA : untab t14bA = rep14b ga :=
  untab_mapTab_frob untab_t14A

theorem untab_t14bB : untab t14bB = rep14b gb :=
  untab_mapTab_frob untab_t14B

noncomputable abbrev repA14 : G6 →* Matrix (Fin (6 * 14)) (Fin (6 * 14)) FieldFour :=
  kronRep rep6a rep14a

theorem untab_tA14 : untab tA14 = repA14 ga := by
  rw [tA14, untab_kronTab, untab_tA6, untab_t14A, kronRep_apply]

theorem untab_tB14 : untab tB14 = repA14 gb := by
  rw [tB14, untab_kronTab, untab_tB6, untab_t14B, kronRep_apply]

theorem inv64 : untab P64 * untab B64 = 1 ∧
    ∀ g, repA14 g * untab B64 = untab B64 * (untab P64 * repA14 g * untab B64) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec j2_module_checks.2.1
  refine ⟨hPB, subInv_of_closure closure_gab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩
  · intro h
    simpa only [untab_tA14] using h
  · intro h
    simpa only [untab_tB14] using h

noncomputable def rep64 : G6 →* Matrix (Fin 64) (Fin 64) FieldFour :=
  subRep repA14 (untab B64) (untab P64) inv64.1 inv64.2

theorem untab_t64A : untab t64A = rep64 ga := by
  rw [t64A, untab_mulT, untab_mulT, untab_tA14, rep64, subRep_apply, Matrix.mul_assoc]

theorem untab_t64B : untab t64B = rep64 gb := by
  rw [t64B, untab_mulT, untab_mulT, untab_tB14, rep64, subRep_apply, Matrix.mul_assoc]

noncomputable abbrev rep64t : G6 →* Matrix (Fin 64) (Fin 64) FieldFour :=
  twist rep64

noncomputable abbrev rep84 : G6 →* Matrix (Fin (6 * 14)) (Fin (6 * 14)) FieldFour :=
  kronRep rep6a rep14b

theorem untab_t84A : untab t84A = rep84 ga := by
  rw [t84A, untab_kronTab, untab_tA6, untab_t14bA, kronRep_apply]

theorem untab_t84B : untab t84B = rep84 gb := by
  rw [t84B, untab_kronTab, untab_tB6, untab_t14bB, kronRep_apply]

noncomputable abbrev repAAb : G6 →* Matrix (Fin (14 * 14)) (Fin (14 * 14)) FieldFour :=
  kronRep rep14a rep14b

theorem untab_tAAb : untab tAAb = repAAb ga := by
  rw [tAAb, untab_kronTab, untab_t14A, untab_t14bA, kronRep_apply]

theorem untab_tBBb : untab tBBb = repAAb gb := by
  rw [tBBb, untab_kronTab, untab_t14B, untab_t14bB, kronRep_apply]

theorem inv160 : untab P160 * untab B160 = 1 ∧
    ∀ g, repAAb g * untab B160 = untab B160 * (untab P160 * repAAb g * untab B160) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec j2_module_checks.2.2.1
  refine ⟨hPB, subInv_of_closure closure_gab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩
  · intro h
    simpa only [untab_tAAb] using h
  · intro h
    simpa only [untab_tBBb] using h

noncomputable def rep160 : G6 →* Matrix (Fin 160) (Fin 160) FieldFour :=
  subRep repAAb (untab B160) (untab P160) inv160.1 inv160.2

theorem untab_t160A : untab t160A = rep160 ga := by
  rw [t160A, untab_mulT, untab_mulT, untab_tAAb, rep160, subRep_apply, Matrix.mul_assoc]

theorem untab_t160B : untab t160B = rep160 gb := by
  rw [t160B, untab_mulT, untab_mulT, untab_tBBb, rep160, subRep_apply, Matrix.mul_assoc]

variable {K : Type*} [Field K]

theorem isIrreducible_rep6a (φ : FieldFour →+* K) : (matrixBaseChange φ rep6a).IsIrreducible :=
  c6.isIrreducible_of_check φ rep6a untab_tA6 untab_tB6 j2_module_checks.2.2.2.1

theorem isIrreducible_rep14a (φ : FieldFour →+* K) :
    (matrixBaseChange φ rep14a).IsIrreducible :=
  c14.isIrreducible_of_check φ rep14a untab_t14A untab_t14B j2_module_checks.2.2.2.2.1

theorem isIrreducible_rep36 (φ : FieldFour →+* K) : (matrixBaseChange φ rep36).IsIrreducible :=
  c36.isIrreducible_of_check φ rep36 untab_t36A untab_t36B j2_module_checks.2.2.2.2.2.1

theorem isIrreducible_rep64 (φ : FieldFour →+* K) : (matrixBaseChange φ rep64).IsIrreducible :=
  c64.isIrreducible_of_check φ rep64 untab_t64A untab_t64B j2_module_checks.2.2.2.2.2.2.1

theorem isIrreducible_rep84 (φ : FieldFour →+* K) : (matrixBaseChange φ rep84).IsIrreducible :=
  c84.isIrreducible_of_check φ rep84 untab_t84A untab_t84B j2_module_checks.2.2.2.2.2.2.2.1

theorem isIrreducible_rep160 (φ : FieldFour →+* K) :
    (matrixBaseChange φ rep160).IsIrreducible :=
  c160.isIrreducible_of_check φ rep160 untab_t160A untab_t160B
    j2_module_checks.2.2.2.2.2.2.2.2.1

theorem isIrreducible_rep6b (φ : FieldFour →+* K) : (matrixBaseChange φ rep6b).IsIrreducible := by
  rw [matrixBaseChange_twist]
  exact isIrreducible_rep6a _

theorem isIrreducible_rep14b (φ : FieldFour →+* K) :
    (matrixBaseChange φ rep14b).IsIrreducible := by
  rw [matrixBaseChange_twist]
  exact isIrreducible_rep14a _

theorem isIrreducible_rep64t (φ : FieldFour →+* K) :
    (matrixBaseChange φ rep64t).IsIrreducible := by
  rw [matrixBaseChange_twist]
  exact isIrreducible_rep64 _

noncomputable abbrev w6 : G6 := wordG ga gb tw6

noncomputable abbrev w14 : G6 := wordG ga gb tw14

noncomputable abbrev w64 : G6 := wordG ga gb tw64

theorem trace_rep6a_w6 : Matrix.trace (rep6a w6) = ω := by
  rw [← untab_wordT rep6a untab_tA6 untab_tB6]
  exact j2_module_checks.2.2.2.2.2.2.2.2.2.1

theorem trace_rep14a_w14 : Matrix.trace (rep14a w14) = ω₂ := by
  rw [← untab_wordT rep14a untab_t14A untab_t14B]
  exact j2_module_checks.2.2.2.2.2.2.2.2.2.2.1

theorem trace_rep64_w64 : Matrix.trace (rep64 w64) = ω₂ := by
  rw [← untab_wordT rep64 untab_t64A untab_t64B]
  exact j2_module_checks.2.2.2.2.2.2.2.2.2.2.2

end Reps

theorem isIrreducible_of_finrank_eq_one {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (h : finrank k V = 1) : ρ.IsIrreducible := by
  have hs : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.2 h
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hbt
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvtop : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← hbt] at hvtop
    exact hv ((Submodule.mem_bot k).mp hvtop)
  have : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun U => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top U.toSubmodule with h0 | h0
  · left
    ext v
    rw [h0]
    rfl
  · right
    ext v
    rw [h0]
    rfl

@[expose] noncomputable def rep1 : G6 →* Matrix (Fin 1) (Fin 1) (ZMod 2) := 1

theorem isIrreducible_rep1 {K : Type*} [Field K] (φ : ZMod 2 →+* K) :
    (matrixBaseChange φ rep1).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_fin_fun K)

section Closure

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

abbrev j2Dim : Fin 10 → ℕ := ![1, 6, 6, 14, 14, 6 * 6, 64, 64, 6 * 14, 160]

theorem isEmpty_equiv_of_trace {n : ℕ} (M N : G6 →* Matrix (Fin n) (Fin n) FieldFour) (g : G6)
    (h : Matrix.trace (M g) ≠ Matrix.trace (N g)) :
    IsEmpty ((matrixBaseChange (toField k) M).Equiv (matrixBaseChange (toField k) N)) := by
  refine isEmpty_equiv_of_trace_ne g ?_
  rw [trace_matrixBaseChange, trace_matrixBaseChange]
  exact fun h' => h ((toField k).injective h')

@[expose] noncomputable def j2ClosureRep :
    ∀ i : Fin 10, Representation k G6 (Fin (j2Dim i) → k)
  | 0 => matrixBaseChange ((toField k).comp ofPrime) rep1
  | 1 => matrixBaseChange (toField k) rep6a
  | 2 => matrixBaseChange (toField k) rep6b
  | 3 => matrixBaseChange (toField k) rep14a
  | 4 => matrixBaseChange (toField k) rep14b
  | 5 => matrixBaseChange (toField k) rep36
  | 6 => matrixBaseChange (toField k) rep64
  | 7 => matrixBaseChange (toField k) rep64t
  | 8 => matrixBaseChange (toField k) rep84
  | 9 => matrixBaseChange (toField k) rep160

theorem isIrreducible_j2ClosureRep : ∀ i, (j2ClosureRep k i).IsIrreducible := by
  intro i
  fin_cases i
  · exact isIrreducible_rep1 _
  · exact isIrreducible_rep6a _
  · exact isIrreducible_rep6b _
  · exact isIrreducible_rep14a _
  · exact isIrreducible_rep14b _
  · exact isIrreducible_rep36 _
  · exact isIrreducible_rep64 _
  · exact isIrreducible_rep64t _
  · exact isIrreducible_rep84 _
  · exact isIrreducible_rep160 _

theorem trace_ne_6 : Matrix.trace (rep6a w6) ≠ Matrix.trace (rep6b w6) := by
  rw [trace_twist, trace_rep6a_w6, frob_ω]
  exact ω_ne_ω₂

theorem trace_ne_14 : Matrix.trace (rep14a w14) ≠ Matrix.trace (rep14b w14) := by
  rw [trace_twist, trace_rep14a_w14, frob_ω₂]
  exact ω_ne_ω₂.symm

theorem trace_ne_64 : Matrix.trace (rep64 w64) ≠ Matrix.trace (rep64t w64) := by
  rw [trace_twist, trace_rep64_w64, frob_ω₂]
  exact ω_ne_ω₂.symm

theorem isEmpty_equiv_j2ClosureRep (i j : Fin 10) (hij : i ≠ j) :
    IsEmpty ((j2ClosureRep k i).Equiv (j2ClosureRep k j)) := by
  by_cases hd : j2Dim i = j2Dim j
  · have hcases : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) := by
      revert i j
      decide
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact isEmpty_equiv_of_trace k rep6a rep6b w6 trace_ne_6
    · exact isEmpty_equiv_of_trace k rep6b rep6a w6 trace_ne_6.symm
    · exact isEmpty_equiv_of_trace k rep14a rep14b w14 trace_ne_14
    · exact isEmpty_equiv_of_trace k rep14b rep14a w14 trace_ne_14.symm
    · exact isEmpty_equiv_of_trace k rep64 rep64t w64 trace_ne_64
    · exact isEmpty_equiv_of_trace k rep64t rep64 w64 trace_ne_64.symm
  · exact isEmpty_equiv_of_finrank_ne (by rwa [Module.finrank_fin_fun, Module.finrank_fin_fun])

theorem j2ClosureRep_complete
    (W : Type*) [AddCommGroup W] [Module k W]
    (σ : Representation k G6 W) (hσ : σ.IsIrreducible) :
    FiniteDimensional k W ∧ ∃ i, Nonempty (σ.Equiv (j2ClosureRep k i)) := by
  have := isIrreducible_j2ClosureRep k
  have := hσ
  exact exists_equiv_of_card_pRegularClass_le 2 _ (j2ClosureRep k)
    (isEmpty_equiv_j2ClosureRep k) (card_pRegularClass_Γ₆.trans (Fintype.card_fin 10).symm.le)
    W σ

end Closure

end CFSG.Quasithin.J2Mod
