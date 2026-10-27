module

public import CFSG.LocalAnalysis.StandardType.GGResIITransport
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern
public import CFSG.LocalAnalysis.StandardType.GGResIConclX
public import CFSG.LocalAnalysis.StandardType.GGResILinDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResILinConcl (p : ℕ) [Fact p.Prime] {Λ : Type} [DecidableEq Λ] (b : Λ)
    (CL : Matrix Λ Λ ℤ) (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] (g : Option Λ → (V ≃ₗ[ZMod p] V))
    (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V) (x : V) : Prop :=
  (∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) ∨
    (α none (h (some b)) = 0 ∧ ∃ M₀ : CoxeterMatrix (Option Λ), GGIsWeylMatrix M₀ ∧
      GGIntCartan M₀ (ggResIGlue b CL CK)) ∨
    (5 ≤ p ∧ ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ j j' : Λ, j ≠ b ∧ j' ≠ b ∧
      GGTriBad p (ggTriMat (α (some j)) (α (some j'))
        ((α (some j)).comp (ψ⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap) (h (some j)) (h (some j'))
        (ψ (h (some j))))) ∨
    (p = 3 ∧ ∃ R : List (V ≃ₗ[ZMod p] V), (∀ k : Λ, g (some k) ∈ R) ∧
      (∀ k : Λ, ∀ r ∈ R, g (some k) * r * (g (some k))⁻¹ ∈ R) ∧
      ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ i : Λ, α (some i) (ψ⁻¹ x) = 0 ∧
        ψ * g (some i) * ψ⁻¹ ∉ R) ∨
    (p = 3 ∧ GGResILineCert p b CL g α False) ∨
    (GGResO2aCell p b CL CK (α none (h (some b))) (α (some b) (h none)) ∧
      GGResILineCert p b CL g α True) ∨
    GGResO2bCell p b CL CK (α none (h (some b))) (α (some b) (h none)) ∨
    ZS.LinWeyl p (Subgroup.closure (Set.range g))

theorem ggResIIIdx_injective {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) :
    Function.Injective (ggResIIIdx e) := by
  intro k l hkl
  induction k using Fin.lastCases with
  | last =>
    induction l using Fin.lastCases with
    | last => rfl
    | cast j => simp at hkl
  | cast i =>
    induction l using Fin.lastCases with
    | last => simp at hkl
    | cast j =>
      simp only [ggResIIIdx_castSucc, Option.some.injEq] at hkl
      rw [e.injective hkl]

theorem ggResIIIdx_eq_none {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {k : Fin (n + 1)} :
    ggResIIIdx e k = none ↔ k = Fin.last n := by
  refine ⟨fun hk => ?_, fun hk => by rw [hk, ggResIIIdx_last]⟩
  induction k using Fin.lastCases with
  | last => rfl
  | cast i => simp at hk

@[expose] noncomputable def ggResIIdxEquiv {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) :
    Fin (n + 1) ≃ Option Λ :=
  Equiv.ofBijective (ggResIIIdx e) ⟨ggResIIIdx_injective e, ggResIIIdx_surjective e⟩

section Transport

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {CL : Matrix Λ Λ ℤ}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
  {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}

@[expose] def ggResIJEquiv (e : Fin n ≃ Λ) (hib : e ib = b) :
    {i : Fin n // i ≠ ib} ≃ {i : Λ // i ≠ b} :=
  e.subtypeEquiv fun i => ⟨fun hi he => hi (e.injective (he.trans hib.symm)),
    fun hi h => hi (by rw [h, hib])⟩

omit [Fintype Λ] [DecidableEq Λ] in
theorem ggResI_lineCert_back [Finite V] (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    (hib : e ib = b) {g : Option Λ → (V ≃ₗ[ZMod p] V)} {α : Option Λ → Module.Dual (ZMod p) V}
    {P : Prop} (hc : GGResILineCertI ib C (g ∘ ggResIIIdx e) (α ∘ ggResIIIdx e) P) :
    GGResILineCert p b CL g α P := by
  obtain ⟨T, eL, hcart, hindL, z, w, F, S, hz, hw, hzL, hF0, hF, hS, hbad⟩ := hc
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  have hrange : Set.range (g ∘ ggResIIIdx e) = Set.range g := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨k, hk⟩ := ggResIIIdx_surjective e o
      exact ⟨k, by simp [hk]⟩
  refine ⟨T, eL.trans (ggResIJEquiv e hib), fun k l => ?_, ?_, z, w,
    F.map fun ψo => (ψo.1, ggResIIIdx e ψo.2), S, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_,
    hbad⟩
  · simp only [Equiv.trans_apply, ggResIJEquiv, Equiv.subtypeEquiv_apply, hCe]
    exact hcart k l
  · refine (linearIndependent_equiv (ggResIJEquiv e hib)).mp ?_
    convert hindL using 1
    funext j
    simp [ggResIJEquiv]
  · have hj' : e.symm j ≠ ib := fun h => hj (by rw [← hib, ← h, e.apply_symm_apply])
    have := hz (e.symm j) hj'
    simpa using this
  · have hj' : e.symm j ≠ ib := fun h => hj (by rw [← hib, ← h, e.apply_symm_apply])
    have := hw (e.symm j) hj'
    simpa using this
  · obtain ⟨i, hi⟩ := hzL
    exact ⟨e i, by simpa using hi⟩
  · simpa using hF0
  · intro ψo hψo
    obtain ⟨ψo₀, hψo₀, rfl⟩ := List.mem_map.mp hψo
    obtain ⟨hA, hmem, hz₀, hw₀, j, hj, hnc⟩ := hF ψo₀ hψo₀
    refine ⟨?_, by rwa [← hrange], hz₀, hw₀, e j, hne j hj, ?_⟩
    · rcases hA with hA | hA
      · exact Or.inl hA
      · exact Or.inr fun h0 => hA ((ggResIIIdx_eq_none e).mp h0)
    · simpa using hnc
  · refine hS.trans (Subgroup.closure_mono ?_)
    rintro t (⟨ψo, hψo, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨(ψo.1, ggResIIIdx e ψo.2), List.mem_map.mpr ⟨ψo, hψo, rfl⟩, rfl⟩
    · exact Or.inr ⟨e j, hne j hj, by simp⟩

theorem ggGlueI_aL (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (i : Fin n) :
    ggGlueI C ib ic e₁ e₂ (Fin.last n) i.castSucc = if i = ic then e₁ else 0 := by
  simp [ggGlueI, Fin.ext_iff]

theorem ggGlueI_La (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (i : Fin n) :
    ggGlueI C ib ic e₁ e₂ i.castSucc (Fin.last n) = if i = ic then e₂ else 0 := by
  simp [ggGlueI, Fin.ext_iff]

theorem ggGlueI_LL (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (i j : Fin n) :
    ggGlueI C ib ic e₁ e₂ i.castSucc j.castSucc = C i j := by
  simp [ggGlueI]

theorem ggGlueI_aa (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) :
    ggGlueI C ib ic e₁ e₂ (Fin.last n) (Fin.last n) = 2 := by
  simp [ggGlueI]

omit [Fintype Λ] in
theorem ggResI_std_back (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j) (hib : e ib = b)
    (hbc : ib ≠ ic)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b), CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b), CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    (hKaa : CK none none = 2) (hstd : GGResIStdShapeI C ib ic e₁ e₂) :
    ∃ M₀ : CoxeterMatrix (Option Λ), GGIsWeylMatrix M₀ ∧ GGIntCartan M₀ (ggResIGlue b CL CK) := by
  obtain ⟨M₀, hW, hC⟩ := hstd
  set ε := ggResIIdxEquiv e
  have hε : ∀ k, ε k = ggResIIIdx e k := fun k => rfl
  have hεl : ε.symm none = Fin.last n := by
    rw [Equiv.symm_apply_eq, hε, ggResIIIdx_last]
  have hεs : ∀ l : Λ, ε.symm (some l) = (e.symm l).castSucc := fun l => by
    rw [Equiv.symm_apply_eq, hε, ggResIIIdx_castSucc, e.apply_symm_apply]
  have hsb : e.symm b = ib := by rw [← hib, e.symm_apply_apply]
  refine ⟨M₀.reindex ε, l05nDP4_weyl_reindex hW ε, ?_⟩
  have hre : ggResIGlue b CL CK = Matrix.reindex ε ε (ggGlueI C ib ic e₁ e₂) := by
    ext o o'
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    cases o with
    | none =>
      cases o' with
      | none => rw [hεl, ggGlueI_aa]; exact hKaa
      | some l =>
        rw [hεl, hεs, ggGlueI_aL]
        by_cases hl : l = b
        · rw [hl, hsb, if_neg hbc]
          simp [ggResIGlue]
        · have hl' := hrow (e.symm l) (by rwa [e.apply_symm_apply])
          simp only [e.apply_symm_apply] at hl'
          simp only [ggResIGlue, dif_neg hl, hl']
    | some l =>
      cases o' with
      | none =>
        rw [hεl, hεs, ggGlueI_La]
        by_cases hl : l = b
        · rw [hl, hsb, if_neg hbc]
          simp [ggResIGlue]
        · have hl' := hcol (e.symm l) (by rwa [e.apply_symm_apply])
          simp only [e.apply_symm_apply] at hl'
          simp only [ggResIGlue, dif_neg hl, hl']
      | some l' =>
        rw [hεs, hεs, ggGlueI_LL, ← hCe, e.apply_symm_apply, e.apply_symm_apply]
        rfl
  rw [hre]
  exact hC.reindex ε

omit [Fact p.Prime] [Fintype Λ] [DecidableEq Λ] in
theorem ggResI_o2a_back (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j) (hib : e ib = b)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b), CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b), CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    {u v : ZMod p} (hc : GGResIO2aI p C ib ic e₁ e₂ u v) : GGResO2aCell p b CL CK u v := by
  obtain ⟨hp, j₀, j₁, h₀, h₁, h01, hall, c01, c10, c0b, cb0, c1b, cb1, hic, hbond⟩ := hc
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  refine ⟨hp, ⟨e j₀, hne j₀ h₀⟩, ⟨e j₁, hne j₁ h₁⟩,
    fun h => h01 (e.injective (congrArg Subtype.val h)), fun i => ?_,
    by simp [hCe, c01], by simp [hCe, c10], by simp [hCe, ← hib, c0b], by simp [hCe, ← hib, cb0],
    by simp [hCe, ← hib, c1b], by simp [hCe, ← hib, cb1], ?_⟩
  · rcases hall (e.symm i) with h | h | h
    · exact Or.inl (by simp only; rw [← h, e.apply_symm_apply])
    · exact Or.inr (Or.inl (by simp only; rw [← h, e.apply_symm_apply]))
    · exact Or.inr (Or.inr (by rw [← hib, ← h, e.apply_symm_apply]))
  rcases hic with hic | hic
  · refine ⟨⟨e j₀, hne j₀ h₀⟩, ⟨e j₁, hne j₁ h₁⟩, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · rw [hcol j₁ (hne j₁ h₁), if_neg (fun h => h01 (by rw [← hic, h]))]
    · rw [hrow j₁ (hne j₁ h₁), if_neg (fun h => h01 (by rw [← hic, h]))]
    · rw [hcol j₀ (hne j₀ h₀), hrow j₀ (hne j₀ h₀), if_pos hic.symm, if_pos hic.symm]
      exact hbond
  · refine ⟨⟨e j₁, hne j₁ h₁⟩, ⟨e j₀, hne j₀ h₀⟩, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · rw [hcol j₀ (hne j₀ h₀), if_neg (fun h => h01 (by rw [h, hic]))]
    · rw [hrow j₀ (hne j₀ h₀), if_neg (fun h => h01 (by rw [h, hic]))]
    · rw [hcol j₁ (hne j₁ h₁), hrow j₁ (hne j₁ h₁), if_pos hic.symm, if_pos hic.symm]
      exact hbond

omit [Fact p.Prime] [Fintype Λ] [DecidableEq Λ] in
theorem ggResI_o2b_back (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j) (hib : e ib = b)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b), CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b), CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    {u v : ZMod p} (hc : GGResIO2bI p C ib ic e₁ e₂ u v) : GGResO2bCell p b CL CK u v := by
  obtain ⟨hp, j₁, j₂, h₀, h₁, h₂, h01, h12, h02, hall, c01, c10, c12, c21, c02, c20, c1b, cb1,
    c0b, cb0, c2b, cb2, hbond⟩ := hc
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  refine ⟨hp, ⟨e ic, hne ic h₀⟩, ⟨e j₁, hne j₁ h₁⟩, ⟨e j₂, hne j₂ h₂⟩,
    fun h => h01 (e.injective (congrArg Subtype.val h)),
    fun h => h12 (e.injective (congrArg Subtype.val h)),
    fun h => h02 (e.injective (congrArg Subtype.val h)), fun i => ?_,
    by simp [hCe, c01], by simp [hCe, c10], by simp [hCe, c12], by simp [hCe, c21],
    by simp [hCe, c02], by simp [hCe, c20], by simp [hCe, ← hib, c1b], by simp [hCe, ← hib, cb1],
    by simp [hCe, ← hib, c0b], by simp [hCe, ← hib, cb0], by simp [hCe, ← hib, c2b],
    by simp [hCe, ← hib, cb2], ?_, ?_, ?_, ?_, ?_⟩
  · rcases hall (e.symm i) with h | h | h | h
    · exact Or.inl (by simp only; rw [← h, e.apply_symm_apply])
    · exact Or.inr (Or.inl (by simp only; rw [← h, e.apply_symm_apply]))
    · exact Or.inr (Or.inr (Or.inl (by simp only; rw [← h, e.apply_symm_apply])))
    · exact Or.inr (Or.inr (Or.inr (by rw [← hib, ← h, e.apply_symm_apply])))
  · rw [hcol j₁ (hne j₁ h₁), if_neg (Ne.symm h01)]
  · rw [hrow j₁ (hne j₁ h₁), if_neg (Ne.symm h01)]
  · rw [hcol j₂ (hne j₂ h₂), if_neg (Ne.symm h02)]
  · rw [hrow j₂ (hne j₂ h₂), if_neg (Ne.symm h02)]
  · rw [hcol ic (hne ic h₀), hrow ic (hne ic h₀), if_pos rfl, if_pos rfl]
    exact hbond

omit [Fintype Λ] [DecidableEq Λ] in
theorem ggResI_stdTable_transport {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j) (hib : e ib = b) (hbc : ib ≠ ic)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    (hKaa : CK none none = 2)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p)) :
    GGFTable (RingHom.id (ZMod p))
      (ggStdTableI (Int.cast) C ib ic e₁ e₂
        (α none (h (some b))) (α (some b) (h none)))
      (h ∘ ggResIIIdx e) 0 (α ∘ ggResIIIdx e) := by
  classical
  set ι := ggResIIIdx e with hιdef
  set h' := h ∘ ι
  set α' := α ∘ ι
  set u := α none (h (some b))
  set v := α (some b) (h none)
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  have haL : ∀ j : Fin n, α none (h (some (e j))) =
      if j.val = ic.val then ((e₁ : ℤ) : ZMod p) else if j.val = ib.val then u
        else ((0 : ℤ) : ZMod p) := by
    intro j
    by_cases hj : j = ib
    · rw [hj]
      have : ib.val ≠ ic.val := fun h => hbc (Fin.ext h)
      simp [this, hib, u]
    · have := hK none (some ⟨e j, hne j hj⟩)
      simp only [Option.map_none, Option.map_some] at this
      rw [this, hrow j (hne j hj)]
      have hj' : j.val ≠ ib.val := fun h => hj (Fin.ext h)
      by_cases hjc : j = ic
      · subst hjc
        simp
      · have : j.val ≠ ic.val := fun h => hjc (Fin.ext h)
        simp [hjc, hj', this]
  have hLa : ∀ j : Fin n, α (some (e j)) (h none) =
      if j.val = ic.val then ((e₂ : ℤ) : ZMod p) else if j.val = ib.val then v
        else ((0 : ℤ) : ZMod p) := by
    intro j
    by_cases hj : j = ib
    · rw [hj]
      have : ib.val ≠ ic.val := fun h => hbc (Fin.ext h)
      simp [this, hib, v]
    · have := hK (some ⟨e j, hne j hj⟩) none
      simp only [Option.map_none, Option.map_some] at this
      rw [this, hcol j (hne j hj)]
      have hj' : j.val ≠ ib.val := fun h => hj (Fin.ext h)
      by_cases hjc : j = ic
      · subst hjc
        simp
      · have : j.val ≠ ic.val := fun h => hjc (Fin.ext h)
        simp [hjc, hj', this]
  have haa : α none (h none) = 2 := by
    have := hK none none
    simp only [Option.map_none] at this
    rw [this, hKaa]
    norm_num
  have hT : GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h' 0 α' := by
    constructor
    · intro k l
      simp only [ggStdTableI, Vector.get_ofFn, RingHom.id_apply]
      induction k using Fin.lastCases with
      | last =>
        induction l using Fin.lastCases with
        | last => simp [h', α', ι, ggStdEntryI_aa, haa]
        | cast j =>
          simp only [h', α', ι, Function.comp_apply, ggResIIIdx_last, ggResIIIdx_castSucc,
            ggStdEntryI_aL, haL]
      | cast i =>
        induction l using Fin.lastCases with
        | last =>
          simp only [h', α', ι, Function.comp_apply, ggResIIIdx_last, ggResIIIdx_castSucc,
            ggStdEntryI_La, hLa]
        | cast j =>
          simp only [h', α', ι, Function.comp_apply, ggResIIIdx_castSucc, ggStdEntryI_LL, hL, hCe]
    · intro k
      simp only [ggStdTableI, Vector.get_ofFn, ggStdEntryI_x, map_zero, Int.cast_zero]
  exact hT

omit [Fintype Λ] in
theorem ggResI_transport [Module.Finite (ZMod p) V] [Finite V] {g : Option Λ → (V ≃ₗ[ZMod p] V)}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V} {x : V} (hp2 : p ≠ 2)
    (hg : ∀ o w, g o w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hind : LinearIndependent (ZMod p) h) (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤)
    (hxL : ∀ i : Λ, α (some i) x = 0)
    (hfix : ∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (hx0 : x ≠ 0) (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    (hdiag : ∀ i, C i i = 2) (hib : e ib = b) (hbc : ib ≠ ic)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b), CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b), CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    (hKaa : CK none none = 2) (hok : GGResIShapeOK C ib ic e₁ e₂) :
    GGResILinConcl p b CL CK g h α x := by
  classical
  set ι := ggResIIIdx e with hιdef
  set g' := g ∘ ι
  set h' := h ∘ ι
  set α' := α ∘ ι
  set u := α none (h (some b))
  set v := α (some b) (h none)
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  have hT : GGFTable (RingHom.id (ZMod p))
      (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h' 0 α' := by
    simpa only [h', α', u, v, ι] using
      ggResI_stdTable_transport e hCe hib hbc hrow hcol hKaa hL hK
  have hg' : ∀ k w, g' k w = w - α' k w • h' k := fun k w => hg _ w
  have h2' : ∀ k, α' k (h' k) = 2 := by
    intro k
    induction k using Fin.lastCases with
    | last =>
        have := hT.1 (Fin.last n) (Fin.last n)
        simpa [α', h', ι, ggStdTableI, ggStdEntryI] using this
    | cast i => simp [α', h', ι, hL, hCe, hdiag]
  have hrange_h : Set.range h' = Set.range h := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨k, hk⟩ := ggResIIIdx_surjective e o
      exact ⟨k, by simp [h', ι, hk]⟩
  have hspan' : Submodule.span (ZMod p) (Set.range h') = ⊤ := by rw [hrange_h, hspan]
  have hind' : LinearIndependent (ZMod p) h' := hind.comp ι (ggResIIIdx_injective e)
  have hx' : ∀ i : Fin n, α' i.castSucc x = 0 := fun i => by simp [α', ι, hxL]
  have hfix' : ∀ w : V, (∀ i : Fin n, α' i.castSucc w = 0) →
      w ∈ Submodule.span (ZMod p) {x} := by
    intro w hw
    exact hfix w fun i => by simpa [α', ι] using hw (e.symm i)
  have hconcl := hok p V g' h' α' x u v hp2 hg' h2' hT hspan' hind' hx' hfix' hx0
  have hrange : Set.range g' = Set.range g := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨ι k, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨k, hk⟩ := ggResIIIdx_surjective e o
      exact ⟨k, by simp [g', ι, hk]⟩
  rcases hconcl with (htv | ⟨h5, ψ, hψ, j, j', hj, hj', hbad⟩ | ⟨hp3, R, hRg, hRc, ψ, hψ, i, hi,
    hnot⟩ | hW) | ⟨hu, hstd⟩ | ⟨hp3, hline⟩ | ⟨ho2, hline⟩ | ho2
  · left
    rwa [hrange] at htv
  · right; right; left
    refine ⟨h5, ψ, by rwa [hrange] at hψ, e j, e j', hne j hj, hne j' hj', ?_⟩
    simpa [α', h', ι] using hbad
  · right; right; right; left
    refine ⟨hp3, R, fun k => ?_, fun k r hr => ?_, ψ, by rwa [hrange] at hψ, e i, by simpa [α', ι]
      using hi, by simpa [g', ι] using hnot⟩
    · simpa [g', ι] using hRg (e.symm k)
    · simpa [g', ι] using hRc (e.symm k) r hr
  · right; right; right; right; right; right; right
    rwa [hrange] at hW
  · right; left
    exact ⟨hu, ggResI_std_back e hCe hib hbc hrow hcol hKaa hstd⟩
  · right; right; right; right; left
    exact ⟨hp3, ggResI_lineCert_back e hCe hib hline⟩
  · right; right; right; right; right; left
    exact ⟨ggResI_o2a_back e hCe hib hrow hcol ho2, ggResI_lineCert_back e hCe hib hline⟩
  · right; right; right; right; right; right; left
    exact ggResI_o2b_back e hCe hib hrow hcol ho2

end Transport

end CFSG.StandardType
