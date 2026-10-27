module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain2

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix

theorem s9c3_flag_mul {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    {M N : Matrix (Fin d) (Fin d) E}
    (hM : (∀ v ∈ A, M *ᵥ v ∈ A) ∧ (∀ v ∈ B, M *ᵥ v ∈ B))
    (hN : (∀ v ∈ A, N *ᵥ v ∈ A) ∧ (∀ v ∈ B, N *ᵥ v ∈ B)) :
    (∀ v ∈ A, (M * N) *ᵥ v ∈ A) ∧ (∀ v ∈ B, (M * N) *ᵥ v ∈ B) :=
  ⟨fun v hv => by rw [← Matrix.mulVec_mulVec]; exact hM.1 _ (hN.1 v hv),
    fun v hv => by rw [← Matrix.mulVec_mulVec]; exact hM.2 _ (hN.2 v hv)⟩

theorem s9c3_flag_one {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} :
    (∀ v ∈ A, (1 : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ A) ∧
      (∀ v ∈ B, (1 : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ B) :=
  ⟨fun v hv => by rw [Matrix.one_mulVec]; exact hv,
    fun v hv => by rw [Matrix.one_mulVec]; exact hv⟩

theorem s9c3_flag_add {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    {M N : Matrix (Fin d) (Fin d) E}
    (hM : (∀ v ∈ A, M *ᵥ v ∈ A) ∧ (∀ v ∈ B, M *ᵥ v ∈ B))
    (hN : (∀ v ∈ A, N *ᵥ v ∈ A) ∧ (∀ v ∈ B, N *ᵥ v ∈ B)) :
    (∀ v ∈ A, (M + N) *ᵥ v ∈ A) ∧ (∀ v ∈ B, (M + N) *ᵥ v ∈ B) :=
  ⟨fun v hv => by rw [Matrix.add_mulVec]; exact A.add_mem (hM.1 v hv) (hN.1 v hv),
    fun v hv => by rw [Matrix.add_mulVec]; exact B.add_mem (hM.2 v hv) (hN.2 v hv)⟩

theorem s9c3_flag_zero {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} :
    (∀ v ∈ A, (0 : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ A) ∧
      (∀ v ∈ B, (0 : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ B) :=
  ⟨fun v _ => by rw [Matrix.zero_mulVec]; exact A.zero_mem,
    fun v _ => by rw [Matrix.zero_mulVec]; exact B.zero_mem⟩

theorem s9c3_flag_alg {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} (r : E) :
    (∀ v ∈ A, (algebraMap E (Matrix (Fin d) (Fin d) E) r) *ᵥ v ∈ A) ∧
      (∀ v ∈ B, (algebraMap E (Matrix (Fin d) (Fin d) E) r) *ᵥ v ∈ B) :=
  ⟨fun v hv => by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact A.smul_mem r hv,
    fun v hv => by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact B.smul_mem r hv⟩

@[expose] def s9cFlag {E : Type} [Field E] {d : ℕ} (A B : Submodule E (Fin d → E)) :
    Subalgebra E (Matrix (Fin d) (Fin d) E) :=
  { carrier := {M | (∀ v ∈ A, M *ᵥ v ∈ A) ∧ (∀ v ∈ B, M *ᵥ v ∈ B)}
    mul_mem' := fun {a b} ha hb => s9c3_flag_mul (A := A) (B := B) (M := a) (N := b) ha hb
    one_mem' := s9c3_flag_one (A := A) (B := B)
    add_mem' := fun {a b} ha hb => s9c3_flag_add (A := A) (B := B) (M := a) (N := b) ha hb
    zero_mem' := s9c3_flag_zero (A := A) (B := B)
    algebraMap_mem' := fun r => s9c3_flag_alg (A := A) (B := B) r }

theorem s9cFlag_mapA {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M : s9cFlag A B) {v : Fin d → E} (hv : v ∈ A) :
    (M : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ A := by
  have h : (∀ v ∈ A, (M : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ A) ∧
      (∀ v ∈ B, (M : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ B) := M.2
  exact h.1 v hv

theorem s9cFlag_mapB {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M : s9cFlag A B) {v : Fin d → E} (hv : v ∈ B) :
    (M : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ B := by
  have h : (∀ v ∈ A, (M : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ A) ∧
      (∀ v ∈ B, (M : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ B) := M.2
  exact h.2 v hv

@[expose] abbrev s9cSub {E : Type} [Field E] {d : ℕ} (A B : Submodule E (Fin d → E)) : Type :=
  ↥B ⧸ A.comap B.subtype

@[expose] def s9cMk {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (v : Fin d → E) (hv : v ∈ B) : s9cSub A B :=
  Submodule.Quotient.mk (⟨v, hv⟩ : ↥B)

@[expose] noncomputable def s9c3_res {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M : s9cFlag A B) : ↥B →ₗ[E] ↥B :=
  LinearMap.restrict (Matrix.mulVecLin (M : Matrix (Fin d) (Fin d) E)) (p := B) (q := B)
    (fun v hv => s9cFlag_mapB M hv)

theorem s9c3_res_le {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M : s9cFlag A B) : A.comap B.subtype ≤ (A.comap B.subtype).comap (s9c3_res M) :=
  fun x hx => s9cFlag_mapA M (v := (x : Fin d → E)) hx

@[expose] noncomputable def s9c3_map {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M : s9cFlag A B) : Module.End E (s9cSub A B) :=
  Submodule.mapQ (A.comap B.subtype) (A.comap B.subtype) (s9c3_res M) (s9c3_res_le M)

theorem s9c3_map_mk {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M : s9cFlag A B) (y : ↥B) :
    s9c3_map M (Submodule.Quotient.mk y : s9cSub A B) =
      (Submodule.Quotient.mk (⟨(M : Matrix (Fin d) (Fin d) E) *ᵥ (y : Fin d → E),
        s9cFlag_mapB M y.2⟩ : ↥B) : s9cSub A B) :=
  rfl

theorem s9c3_map_one {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} :
    s9c3_map (1 : s9cFlag A B) = 1 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [Module.End.one_apply, s9c3_map_mk]
    congr 1
    exact Subtype.ext (Matrix.one_mulVec _)

theorem s9c3_map_mul {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M N : s9cFlag A B) : s9c3_map (M * N) = s9c3_map M * s9c3_map N := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [Module.End.mul_apply, s9c3_map_mk, s9c3_map_mk, s9c3_map_mk]
    congr 1
    exact Subtype.ext (Matrix.mulVec_mulVec (y : Fin d → E) (M : Matrix (Fin d) (Fin d) E)
      (N : Matrix (Fin d) (Fin d) E)).symm

theorem s9c3_map_zero {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} :
    s9c3_map (0 : s9cFlag A B) = 0 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [LinearMap.zero_apply, s9c3_map_mk, Submodule.Quotient.mk_eq_zero]
    show (0 : Matrix (Fin d) (Fin d) E) *ᵥ (y : Fin d → E) ∈ A
    rw [Matrix.zero_mulVec]
    exact A.zero_mem

theorem s9c3_map_add {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M N : s9cFlag A B) : s9c3_map (M + N) = s9c3_map M + s9c3_map N := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [LinearMap.add_apply, s9c3_map_mk, s9c3_map_mk, s9c3_map_mk,
      ← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (Matrix.add_mulVec (M : Matrix (Fin d) (Fin d) E)
      (N : Matrix (Fin d) (Fin d) E) (y : Fin d → E))

theorem s9c3_map_commutes {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} (r : E) :
    s9c3_map (algebraMap E (s9cFlag A B) r) = algebraMap E (Module.End E (s9cSub A B)) r := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [Module.algebraMap_end_apply, s9c3_map_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    show (algebraMap E (Matrix (Fin d) (Fin d) E) r) *ᵥ (y : Fin d → E) = r • (y : Fin d → E)
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

@[expose] noncomputable def s9cIndHom {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} :
    s9cFlag A B →ₐ[E] Module.End E (s9cSub A B) :=
  { toFun := fun M => s9c3_map M
    map_one' := s9c3_map_one
    map_mul' := fun M N => s9c3_map_mul M N
    map_zero' := s9c3_map_zero
    map_add' := fun M N => s9c3_map_add M N
    commutes' := fun r => s9c3_map_commutes r }

theorem s9cIndHom_mk {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (M : s9cFlag A B) {v : Fin d → E} (hv : v ∈ B) :
    s9cIndHom M (s9cMk v hv) = s9cMk ((M : Matrix (Fin d) (Fin d) E) *ᵥ v) (s9cFlag_mapB M hv) := by
  exact s9c3_map_mk M ⟨v, hv⟩

@[expose] def s9cOfN {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (g : N) :
    s9cFlag A B :=
  ⟨((g : GL (Fin d) E) : Matrix (Fin d) (Fin d) E), fun v hv => hA g g.2 v hv,
    fun v hv => hB g g.2 v hv⟩

theorem s9c3_ofN_mul {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (g k : N) :
    s9cOfN hA hB (g * k) = s9cOfN hA hB g * s9cOfN hA hB k :=
  rfl

theorem s9c3_ofN_one {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) :
    s9cOfN hA hB (1 : N) = 1 :=
  rfl

@[expose] noncomputable def s9c3_pull {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (W : Submodule E (s9cSub A B)) : Submodule E (Fin d → E) :=
  (W.comap (A.comap B.subtype).mkQ).map B.subtype

theorem s9c3_pull_mem {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (W : Submodule E (s9cSub A B)) (y : ↥B) :
    (y : Fin d → E) ∈ s9c3_pull W ↔ (Submodule.Quotient.mk y : s9cSub A B) ∈ W := by
  constructor
  · intro hy
    have hy' : (y : Fin d → E) ∈ (W.comap (A.comap B.subtype).mkQ).map B.subtype := hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy'
    have hzy' : z = y := Subtype.ext hzy
    subst hzy'
    exact Submodule.mem_comap.mp hz
  · intro hy
    have hy' : y ∈ W.comap (A.comap B.subtype).mkQ := Submodule.mem_comap.mpr hy
    exact Submodule.mem_map_of_mem (f := B.subtype) hy'

theorem s9c3_pull_le {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (W : Submodule E (s9cSub A B)) : s9c3_pull W ≤ B :=
  Submodule.map_subtype_le _ _

theorem s9c3_pull_ge {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)} (hAB : A ≤ B)
    (W : Submodule E (s9cSub A B)) : A ≤ s9c3_pull W := by
  intro a ha
  have haB : a ∈ B := hAB ha
  have h0 : (Submodule.Quotient.mk (⟨a, haB⟩ : ↥B) : s9cSub A B) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ha
  have hmem : (Submodule.Quotient.mk (⟨a, haB⟩ : ↥B) : s9cSub A B) ∈ W := by
    rw [h0]
    exact W.zero_mem
  exact (s9c3_pull_mem W ⟨a, haB⟩).mpr hmem

theorem s9c3_pull_inv {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B)
    (W : Submodule E (s9cSub A B))
    (hW : ∀ g : N, ∀ w ∈ W, s9cIndHom (s9cOfN hA hB g) w ∈ W) : S9cInv N (s9c3_pull W) := by
  intro g hg v hv
  have hv' : v ∈ (W.comap (A.comap B.subtype).mkQ).map B.subtype := hv
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv'
  have hzW : (Submodule.Quotient.mk z : s9cSub A B) ∈ W := Submodule.mem_comap.mp hz
  have h1 : s9cIndHom (s9cOfN hA hB ⟨g, hg⟩) (Submodule.Quotient.mk z : s9cSub A B) ∈ W :=
    hW ⟨g, hg⟩ _ hzW
  have h2 : (Submodule.Quotient.mk (⟨g *ᵥ (z : Fin d → E), s9cFlag_mapB (s9cOfN hA hB ⟨g, hg⟩) z.2⟩
      : ↥B) : s9cSub A B) ∈ W := h1
  exact (s9c3_pull_mem W _).mpr h2

theorem s9c_subq_irred {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (hAB : A ≤ B)
    (hstep : ∀ W : Submodule E (Fin d → E), S9cInv N W → A ≤ W → W ≤ B → W = A ∨ W = B)
    (W : Submodule E (s9cSub A B))
    (hW : ∀ g : N, ∀ w ∈ W, s9cIndHom (s9cOfN hA hB g) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  rcases hstep (s9c3_pull W) (s9c3_pull_inv hA hB W hW) (s9c3_pull_ge hAB W)
    (s9c3_pull_le W) with hY | hY
  · left
    rw [eq_bot_iff]
    intro w hw
    induction w using Submodule.Quotient.induction_on with
    | H y =>
      have h1 : (y : Fin d → E) ∈ s9c3_pull W := (s9c3_pull_mem W y).mpr hw
      rw [hY] at h1
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact h1
  · right
    rw [eq_top_iff]
    intro w _
    induction w using Submodule.Quotient.induction_on with
    | H y =>
      have h1 : (y : Fin d → E) ∈ s9c3_pull W := by
        rw [hY]
        exact y.2
      exact (s9c3_pull_mem W y).mp h1

@[expose] noncomputable def s9cRep {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) :
    N →* GL (Fin (Module.finrank E (s9cSub A B))) E :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix (Module.finBasis E (s9cSub A B))
        (Module.finBasis E (s9cSub A B)) (s9cIndHom (s9cOfN hA hB g))
      map_one' := by
        simp only [s9c3_ofN_one, map_one, LinearMap.toMatrix_one]
      map_mul' := fun g k => by
        simp only [s9c3_ofN_mul, map_mul, LinearMap.toMatrix_mul] }

theorem s9cRep_val {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (g : N) :
    ((s9cRep hA hB g : GL (Fin (Module.finrank E (s9cSub A B))) E) :
        Matrix (Fin (Module.finrank E (s9cSub A B))) (Fin (Module.finrank E (s9cSub A B))) E) =
      LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
        (s9cIndHom (s9cOfN hA hB g)) :=
  rfl

theorem s9c3_mat_sq {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (X : s9cFlag A B)
    (h : ((X : Matrix (Fin d) (Fin d) E) - 1) * ((X : Matrix (Fin d) (Fin d) E) - 1) = 0) :
    (LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
        (s9cIndHom X) - 1) *
      (LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
        (s9cIndHom X) - 1) = 0 := by
  have hX : (X - 1) * (X - 1) = 0 := Subtype.ext (by simpa using h)
  have hT : (s9cIndHom X - 1) * (s9cIndHom X - 1) = 0 := by
    have h2 : s9cIndHom ((X - 1) * (X - 1)) = s9cIndHom 0 := by rw [hX]
    rwa [map_mul, map_sub, map_one, map_zero] at h2
  have h1 : LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
      (s9cIndHom X - 1) = LinearMap.toMatrix (Module.finBasis E (s9cSub A B))
        (Module.finBasis E (s9cSub A B)) (s9cIndHom X) - 1 := by
    rw [map_sub, LinearMap.toMatrix_one]
  rw [← h1, ← LinearMap.toMatrix_mul, hT, map_zero]

theorem s9c3_ind_ne_one {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (t : N)
    (hnt : ∃ v ∈ B, ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ A) :
    s9cIndHom (s9cOfN hA hB t) ≠ 1 := by
  intro h
  obtain ⟨v, hvB, hvA⟩ := hnt
  apply hvA
  have h1 : (Submodule.Quotient.mk (⟨((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v,
      s9cFlag_mapB (s9cOfN hA hB t) hvB⟩ : ↥B) : s9cSub A B) =
        Submodule.Quotient.mk (⟨v, hvB⟩ : ↥B) := by
    have h2 := congrArg (fun F : Module.End E (s9cSub A B) =>
      F (Submodule.Quotient.mk (⟨v, hvB⟩ : ↥B) : s9cSub A B)) h
    exact h2
  exact Submodule.mem_comap.mp ((Submodule.Quotient.eq (A.comap B.subtype)).mp h1)

theorem s9c3_ind_rank {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (t : N)
    (u : Fin d → E) (hu : u ∈ B) (huA : u ∉ A)
    (hcov : ∀ v : Fin d → E,
      ∃ c : E, ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v = c • u)
    (hT1 : s9cIndHom (s9cOfN hA hB t) ≠ 1) :
    (LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
        (s9cIndHom (s9cOfN hA hB t)) - 1).rank = 1 := by
  have h1 : LinearMap.toMatrix (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B))
      (s9cIndHom (s9cOfN hA hB t) - 1) = LinearMap.toMatrix (Module.finBasis E (s9cSub A B))
        (Module.finBasis E (s9cSub A B)) (s9cIndHom (s9cOfN hA hB t)) - 1 := by
    rw [map_sub, LinearMap.toMatrix_one]
  rw [← h1, Matrix.rank_eq_finrank_range_toLin _ (Module.finBasis E (s9cSub A B))
    (Module.finBasis E (s9cSub A B)), Matrix.toLin_toMatrix]
  have hSne : s9cIndHom (s9cOfN hA hB t) - 1 ≠ 0 := fun h => hT1 (sub_eq_zero.mp h)
  have hpos : 1 ≤ Module.finrank E (LinearMap.range (s9cIndHom (s9cOfN hA hB t) - 1)) :=
    Submodule.one_le_finrank_iff.mpr (fun h => hSne (LinearMap.range_eq_bot.mp h))
  have hu0 : (Submodule.Quotient.mk (⟨u, hu⟩ : ↥B) : s9cSub A B) ≠ 0 :=
    fun h => huA (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero
      (A.comap B.subtype)).mp h))
  have hsub : LinearMap.range (s9cIndHom (s9cOfN hA hB t) - 1) ≤
      Submodule.span E {(Submodule.Quotient.mk (⟨u, hu⟩ : ↥B) : s9cSub A B)} := by
    rintro _ ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨c, hc⟩ := hcov (y : Fin d → E)
      have hx : (⟨((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ (y : Fin d → E),
          s9cFlag_mapB (s9cOfN hA hB t) y.2⟩ : ↥B) - y = c • (⟨u, hu⟩ : ↥B) :=
        Subtype.ext hc
      have hy : (s9cIndHom (s9cOfN hA hB t) - 1) (Submodule.Quotient.mk y : s9cSub A B) =
          c • (Submodule.Quotient.mk (⟨u, hu⟩ : ↥B) : s9cSub A B) := by
        rw [← Submodule.Quotient.mk_smul, ← hx, Submodule.Quotient.mk_sub]
        rfl
      rw [hy]
      exact (Submodule.span E _).smul_mem c (Submodule.mem_span_singleton_self _)
  have hle := Submodule.finrank_mono hsub
  rw [finrank_span_singleton hu0] at hle
  exact le_antisymm hle hpos

theorem s9c_rep_isTransvection {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B)
    (t : N) (ht : IsTransvectionK (t : GL (Fin d) E))
    (u : Fin d → E) (hu : u ∈ B) (huA : u ∉ A)
    (hcov : ∀ v : Fin d → E, ∃ c : E, ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v = c • u)
    (hnt : ∃ v ∈ B, ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ A) :
    IsTransvectionK (s9cRep hA hB t) := by
  have hT1 := s9c3_ind_ne_one hA hB t hnt
  have hsq := s9c3_mat_sq (s9cOfN hA hB t) ht.2.1
  have hrank := s9c3_ind_rank hA hB t u hu huA hcov hT1
  unfold IsTransvectionK
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hT1
    apply (LinearMap.toMatrix (Module.finBasis E (s9cSub A B))
      (Module.finBasis E (s9cSub A B))).injective
    rw [LinearMap.toMatrix_one]
    have h2 := congrArg Units.val h
    rw [Units.val_one, s9cRep_val] at h2
    exact h2
  · rw [s9cRep_val]
    exact hsq
  · rw [s9cRep_val]
    exact hrank

end CFSG.Quasithin.H13.L829N
