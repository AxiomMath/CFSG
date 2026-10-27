module

public import CFSG.Timmesfeld.ARS.CaseHOrbit

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

@[expose] def MOrbit (R : Set (Subgroup G)) (A B B' : Subgroup G) : Prop :=
  ∃ m ∈ M R A, conjSub B m = B'

theorem MOrbit.refl (R : Set (Subgroup G)) (A B : Subgroup G) : MOrbit R A B B :=
  ⟨1, (M R A).one_mem, conjSub_one B⟩

theorem MOrbit.symm {A B B' : Subgroup G} (h : MOrbit R A B B') : MOrbit R A B' B := by
  obtain ⟨m, hm, e⟩ := h
  refine ⟨m⁻¹, (M R A).inv_mem hm, ?_⟩
  rw [← e, Plane.conjSub_conjSub_inv]

theorem MOrbit.trans {A B B' B'' : Subgroup G} (h : MOrbit R A B B') (h' : MOrbit R A B' B'') :
    MOrbit R A B B'' := by
  obtain ⟨m, hm, e⟩ := h
  obtain ⟨m', hm', e'⟩ := h'
  exact ⟨m' * m, (M R A).mul_mem hm' hm, by rw [conjSub_mul, e, e']⟩

section Connected

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

omit hH in
theorem notMem_omegaSet_of_mem_lambdaSet_lambdaSet {A D Y : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) (hY : Y ∈ lambdaSet R D) : Y ∉ omegaSet R A := fun hYΩ =>
  notMem_lambdaSet_of_opposite h hA hYΩ.2 hD (mem_lambdaSet_comm hD.1.1 hY)

theorem mem_psiSet_or_omegaSet {A X Z : Subgroup G} (hA : A ∈ R) (hX : X ∈ omegaSet R A)
    (hZ : Z ∈ lambdaSet R X) : Z ∈ psiSet R A ∨ Z ∈ omegaSet R A := by
  have hZR : Z ∈ R := hZ.1.1
  rcases eq_or_mem_of_mem h hH hA hZR with rfl | hl | hs | ho
  · exact absurd hX (notMem_omegaSet_of_mem_lambdaSet h hZR (mem_lambdaSet_comm hX.1 hZ))
  · exact absurd hZ (notMem_lambdaSet_of_opposite h hA hX.2 hl)
  · exact Or.inl hs
  · exact Or.inr ho

theorem mOrbit_of_mem_lambdaSet {A B B' : Subgroup G} (hA : A ∈ R) (hB : B ∈ omegaSet R A)
    (hB' : B' ∈ omegaSet R A) (hBB' : B' ∈ lambdaSet R B) : MOrbit R A B B' :=
  exists_conj_of_mem_lambdaSet_of_omega h hH hA hB hB' hBB'

theorem mem_omegaSet_of_le_sup {A P X₀ X : Subgroup G} (hA : A ∈ R) (hP : P ∈ psiSet R A)
    (hX₀ : X₀ ∈ lambdaSet R P) (hX₀Ω : X₀ ∈ omegaSet R A) (hXR : X ∈ R) (hXle : X ≤ P ⊔ X₀)
    (hXP : X ≠ P) : X ∈ lambdaSet R P ∧ P ⊔ X = P ⊔ X₀ ∧ X ∈ omegaSet R A := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPR : P ∈ R := hP.1
  obtain ⟨hXl, hline⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hPR hX₀ hPR le_sup_left hXR hXle (Ne.symm hXP)
  refine ⟨hXl, hline, ?_⟩
  obtain ⟨hDA, hDP⟩ := commutator_mem_lambdaSet h hA hPR hP.2
  have key : ∀ {D : Subgroup G}, D ∈ lambdaSet R A → D ≤ P ⊔ X₀ → False := by
    intro D hD hDle
    have hDX₀ : D ≠ X₀ := fun e => notMem_omegaSet_of_mem_lambdaSet h hA hD (e ▸ hX₀Ω)
    obtain ⟨hl, -⟩ := mem_lambdaSet_of_le_sup hR hiso hPR hX₀ hD.1.1 hDle hX₀Ω.1 le_sup_right hDX₀
    exact notMem_omegaSet_of_mem_lambdaSet_lambdaSet h hA hD hl hX₀Ω
  rcases eq_or_mem_of_mem h hH hA hXR with rfl | hl | hs | ho
  · exact absurd (mem_lambdaSet_comm hPR hXl) (notMem_psiSet_of_mem_lambdaSet h · hP)
  · exact (key hl hXle).elim
  ·
    have e := commutator_eq_of_mem_psiSet h hH hA hP hs hXl
    have hDX : ⁅A, P⁆ ∈ lambdaSet R X := e ▸ (commutator_mem_lambdaSet h hA hXR hs.2).2
    have hDle : ⁅A, P⁆ ≤ P ⊔ X := le_line h hH hPR hXl hPR le_sup_left hXR le_sup_right
      (Ne.symm hXP) hDA.1.1 hDP.1.2.2.symm hDX.1.2.2.symm
    exact (key hDA (hline ▸ hDle)).elim
  · exact ho

theorem opposite_of_psi_psi {A P Q X X' : Subgroup G} (hA : A ∈ R) (hP : P ∈ psiSet R A)
    (hQ : Q ∈ psiSet R A) (hPQ : Q ∈ lambdaSet R P) (hX : X ∈ lambdaSet R P)
    (hXΩ : X ∈ omegaSet R A) (hX' : X' ∈ lambdaSet R Q) (hX'Ω : X' ∈ omegaSet R A) :
    (Special R X Q ∧ ⁅X, Q⁆ = P) ∧ X' ∈ omegaSet R X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPR : P ∈ R := hP.1
  have hQR : Q ∈ R := hQ.1
  have hXR : X ∈ R := hXΩ.1
  have hPQne : P ≠ Q := fun e => notMem_lambdaSet_self (R := R) Q (e ▸ hPQ)
  obtain ⟨hDA, hDP⟩ := commutator_mem_lambdaSet h hA hPR hP.2
  have hDQ : ⁅A, P⁆ ∈ lambdaSet R Q :=
    (commutator_eq_of_mem_psiSet h hH hA hP hQ hPQ) ▸ (commutator_mem_lambdaSet h hA hQR hQ.2).2
  have hDle : ⁅A, P⁆ ≤ P ⊔ Q := le_line h hH hPR hPQ hPR le_sup_left hQR le_sup_right hPQne
    hDA.1.1 hDP.1.2.2.symm hDQ.1.2.2.symm
  have hline : ∀ Y ∈ R, Y ≤ P ⊔ Q → Y ∉ omegaSet R A := by
    intro Y hYR hYle hYΩ
    have hYD : Y ≠ ⁅A, P⁆ := fun e => notMem_omegaSet_of_mem_lambdaSet h hA hDA (e ▸ hYΩ)
    obtain ⟨hl, -⟩ :=
      mem_lambdaSet_of_le_sup hR hiso hPR hPQ hDA.1.1 hDle hYR hYle (Ne.symm hYD)
    exact notMem_omegaSet_of_mem_lambdaSet_lambdaSet h hA hDA hl hYΩ
  have hQX : Q ∉ lambdaSet R X := fun hl => hline X hXR
    (le_line h hH hPR hPQ hPR le_sup_left hQR le_sup_right hPQne hXR hX.1.2.2.symm
      (mem_lambdaSet_comm hXR hl).1.2.2.symm) hXΩ
  have hQne : Q ≠ X := fun e => notMem_omegaSet_of_mem_psiSet h hA hQ (e ▸ hXΩ)
  have hsp := special_of_mem_lambdaSet h hH hXR (mem_lambdaSet_comm hPR hX) hPQ hQX hQne
  refine ⟨hsp, ?_⟩
  have hset := setOf_omegaSet_lambdaSet h hH hXR (show Q ∈ psiSet R X from ⟨hQR, hsp.1⟩)
  rw [hsp.2, sup_comm] at hset
  have hmem : X' ∈ lambdaSet R Q \ pointsOn R (P ⊔ Q) :=
    ⟨hX', fun hp => hline X' hp.1 hp.2 hX'Ω⟩
  rw [← hset] at hmem
  exact hmem.1

theorem not_le_commutator_of_psi_psi {A P Q X X' Z : Subgroup G} (hA : A ∈ R)
    (hP : P ∈ psiSet R A) (hQ : Q ∈ psiSet R A) (hPQ : Q ∈ lambdaSet R P)
    (hX : X ∈ lambdaSet R P) (hXΩ : X ∈ omegaSet R A) (hX' : X' ∈ lambdaSet R Q)
    (hX'Ω : X' ∈ omegaSet R A) (hZ : Z ∈ lambdaSet R X) (hZm : ¬ Z ≤ P ⊔ X)
    (hZ' : X' ∈ psiSet R Z) : ¬ ⁅Z, X'⁆ ≤ Q ⊔ X' := by
  intro hWle
  have := h.finite
  have hQR : Q ∈ R := hQ.1
  have hX'R : X' ∈ R := hX'Ω.1
  have hZR : Z ∈ R := hZ.1.1
  obtain ⟨hWZ, hWX'⟩ := commutator_mem_lambdaSet h hZR hX'R hZ'.2
  have hsp := (opposite_of_psi_psi h hH hA hP hQ hPQ hX hXΩ hX' hX'Ω).1
  by_cases hWQ : ⁅Z, X'⁆ = Q
  ·
    have hZQ : Z ∈ lambdaSet R Q := hWQ ▸ mem_lambdaSet_comm hZR hWZ
    have := eq_commutator h hXΩ.1 hQR hsp.1 hZ hZQ
    rw [hsp.2] at this
    exact hZm (this ▸ le_sup_left)
  ·
    obtain ⟨hWQl, -, hWΩ⟩ := mem_omegaSet_of_le_sup h hH hA hQ hX' hX'Ω hWX'.1.1 hWle hWQ
    have hop := (opposite_of_psi_psi h hH hA hP hQ hPQ hX hXΩ hWQl hWΩ).2
    exact notMem_lambdaSet_of_opposite h hXΩ.1 hop.2 hZ (mem_lambdaSet_comm hZR hWZ)

theorem false_of_psi_psi {A P Q X X' X'' Z : Subgroup G} (hA : A ∈ R) (hP : P ∈ psiSet R A)
    (hQ : Q ∈ psiSet R A) (hPQ : Q ∈ lambdaSet R P) (hX : X ∈ lambdaSet R P)
    (hXΩ : X ∈ omegaSet R A) (hX' : X' ∈ lambdaSet R Q) (hX'Ω : X' ∈ omegaSet R A)
    (hX'' : X'' ∈ lambdaSet R Q) (hX''Ω : X'' ∈ omegaSet R A) (hX'X'' : X'' ∈ lambdaSet R X')
    (hZ : Z ∈ lambdaSet R X) (hZm : ¬ Z ≤ P ⊔ X) (hZ' : X' ∈ psiSet R Z)
    (hZ'' : X'' ∈ psiSet R Z) : False := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hQR : Q ∈ R := hQ.1
  have hX'R : X' ∈ R := hX'Ω.1
  have hZR : Z ∈ R := hZ.1.1
  have e := commutator_eq_of_mem_psiSet h hH hZR hZ' hZ'' hX'X''
  obtain ⟨hWZ, hWX'⟩ := commutator_mem_lambdaSet h hZR hX'R hZ'.2
  have hWX'' : ⁅Z, X'⁆ ∈ lambdaSet R X'' := e ▸ (commutator_mem_lambdaSet h hZR hX''Ω.1 hZ''.2).2
  have hQX' : Q ≠ X' := fun e' => notMem_omegaSet_of_mem_psiSet h hA hQ (e' ▸ hX'Ω)
  have hX'X''ne : X' ≠ X'' := fun e' => notMem_lambdaSet_self (R := R) X'' (e' ▸ hX'X'')
  have hX''le : X'' ≤ Q ⊔ X' := le_line h hH hQR hX' hQR le_sup_left hX'R le_sup_right hQX'
    hX''Ω.1 hX''.1.2.2.symm hX'X''.1.2.2.symm
  have hWle : ⁅Z, X'⁆ ≤ Q ⊔ X' := le_line h hH hQR hX' hX'R le_sup_right hX''Ω.1 hX''le
    hX'X''ne hWX'.1.1 hWX'.1.2.2.symm hWX''.1.2.2.symm
  exact not_le_commutator_of_psi_psi h hH hA hP hQ hPQ hX hXΩ hX' hX'Ω hZ hZm hZ' hWle

omit hH in
theorem ncard_lambda_psi_off {X Y P : Subgroup G} (hX : X ∈ R) (hY : Y ∈ omegaSet R X)
    (hP : P ∈ lambdaSet R X) (hPY : Y ∈ psiSet R P) :
    {Z | Z ∈ lambdaSet R X ∧ Y ∈ psiSet R Z ∧ ¬ Z ≤ X ⊔ P}.ncard =
      (linesThrough R X).ncard - 1 := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨D, -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hX hY.1 hY.2 hP
  have hPD : P = D := huniq P ⟨hP.1.1, le_sup_right, mem_psiSet_comm hP.1.1 hPY⟩
  have e : {Z | Z ∈ lambdaSet R X ∧ Y ∈ psiSet R Z ∧ ¬ Z ≤ X ⊔ P} =
      {Z | Z ∈ lambdaSet R X ∧ Y ∈ psiSet R Z} \ {P} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hZ, hYZ, hZle⟩
      exact ⟨⟨hZ, hYZ⟩, fun e => hZle (e ▸ le_sup_right)⟩
    · rintro ⟨⟨hZ, hYZ⟩, hZP⟩
      refine ⟨hZ, hYZ, fun hle => hZP ?_⟩
      rw [hPD]
      exact huniq Z ⟨hZ.1.1, hle, mem_psiSet_comm hZ.1.1 hYZ⟩
  have hmem : P ∈ {Z | Z ∈ lambdaSet R X ∧ Y ∈ psiSet R Z} := ⟨hP, hPY⟩
  rw [e, Set.ncard_sdiff_singleton_of_mem hmem, ncard_lambda_psi_of_omega h hX hY]

omit h hH in
theorem setOf_lambda_psiSet_comm {A X : Subgroup G} (hA : A ∈ R) (V : Subgroup G) :
    {Z | Z ∈ lambdaSet R X ∧ Z ∈ psiSet R A ∧ ¬ Z ≤ V} =
      {Z | Z ∈ lambdaSet R X ∧ A ∈ psiSet R Z ∧ ¬ Z ≤ V} := by
  ext Z
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨hZ, hZA, hZV⟩ => ⟨hZ, mem_psiSet_comm hA hZA, hZV⟩,
    fun ⟨hZ, hAZ, hZV⟩ => ⟨hZ, mem_psiSet_comm hZ.1.1 hAZ, hZV⟩⟩

theorem mOrbit_of_psi_psi {A P Q X₀ X₀' : Subgroup G} (hA : A ∈ R) (hq : 3 ≤ Nat.card A)
    (hP : P ∈ psiSet R A) (hQ : Q ∈ psiSet R A) (hPQ : Q ∈ lambdaSet R P)
    (hX₀ : X₀ ∈ lambdaSet R P) (hX₀Ω : X₀ ∈ omegaSet R A) (hX₀' : X₀' ∈ lambdaSet R Q)
    (hX₀'Ω : X₀' ∈ omegaSet R A) : MOrbit R A X₀ X₀' := by
  classical
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPR : P ∈ R := hP.1
  have hQR : Q ∈ R := hQ.1
  have hQP : P ∈ lambdaSet R Q := mem_lambdaSet_comm hPR hPQ
  have hL2 : 2 ≤ (linesThrough R A).ncard := by
    have hΩ := ncard_omegaSet h hH hA rfl rfl
    have hpos : 0 < (omegaSet R A).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨X₀, hX₀Ω⟩
    by_contra hlt
    rw [hΩ, show (linesThrough R A).ncard - 1 = 0 by omega] at hpos
    simp at hpos
  have hLX : ∀ X ∈ R, (linesThrough R X).ncard = (linesThrough R A).ncard := fun X hX =>
    ncard_linesThrough_eq h hA hX
  have hPmc : (pointsOn R (P ⊔ X₀) \ {P}).ncard = Nat.card A := by
    have hmem : P ∈ pointsOn R (P ⊔ X₀) := ⟨hPR, le_sup_left⟩
    rw [Set.ncard_sdiff_singleton_of_mem hmem, ncard_pointsOn h hPR hX₀, Nat.add_sub_cancel,
      hR.card_eq hPR hA]
  have hPnc : (pointsOn R (Q ⊔ X₀') \ {Q}).ncard = Nat.card A := by
    have hmem : Q ∈ pointsOn R (Q ⊔ X₀') := ⟨hQR, le_sup_left⟩
    rw [Set.ncard_sdiff_singleton_of_mem hmem, ncard_pointsOn h hQR hX₀', Nat.add_sub_cancel,
      hR.card_eq hQR hA]
  have hPm : ∀ X ∈ pointsOn R (P ⊔ X₀) \ {P},
      X ∈ lambdaSet R P ∧ P ⊔ X = P ⊔ X₀ ∧ X ∈ omegaSet R A := fun X hX =>
    mem_omegaSet_of_le_sup h hH hA hP hX₀ hX₀Ω hX.1.1 hX.1.2 fun e => hX.2 e
  have hPn : ∀ X ∈ pointsOn R (Q ⊔ X₀') \ {Q},
      X ∈ lambdaSet R Q ∧ Q ⊔ X = Q ⊔ X₀' ∧ X ∈ omegaSet R A := fun X hX =>
    mem_omegaSet_of_le_sup h hH hA hQ hX₀' hX₀'Ω hX.1.1 hX.1.2 fun e => hX.2 e
  have hfib : ∀ X ∈ pointsOn R (P ⊔ X₀) \ {P}, ∀ X' ∈ pointsOn R (Q ⊔ X₀') \ {Q},
      {Z | Z ∈ lambdaSet R X ∧ X' ∈ psiSet R Z ∧ ¬ Z ≤ P ⊔ X₀}.ncard =
        (linesThrough R A).ncard - 1 := by
    intro X hX X' hX'
    obtain ⟨hXP, hlX, hXΩ⟩ := hPm X hX
    obtain ⟨hX'Q, -, hX'Ω⟩ := hPn X' hX'
    obtain ⟨-, hop⟩ := opposite_of_psi_psi h hH hA hP hQ hPQ hXP hXΩ hX'Q hX'Ω
    obtain ⟨hsp', -⟩ := (opposite_of_psi_psi h hH hA hQ hP hQP hX'Q hX'Ω hXP hXΩ).1
    have := ncard_lambda_psi_off h hXΩ.1 hop (mem_lambdaSet_comm hPR hXP)
      (mem_psiSet_comm hX'Ω.1 ⟨hPR, hsp'⟩)
    rwa [sup_comm X P, hlX, hLX X hXΩ.1] at this
  have hfibA : ∀ X ∈ pointsOn R (P ⊔ X₀) \ {P},
      {Z | Z ∈ lambdaSet R X ∧ Z ∈ psiSet R A ∧ ¬ Z ≤ P ⊔ X₀}.ncard =
        (linesThrough R A).ncard - 1 := by
    intro X hX
    obtain ⟨hXP, hlX, hXΩ⟩ := hPm X hX
    have := ncard_lambda_psi_off h hXΩ.1 ⟨hA, hXΩ.2.symm⟩ (mem_lambdaSet_comm hPR hXP)
      (mem_psiSet_comm hA hP)
    rwa [sup_comm X P, hlX, hLX X hXΩ.1, ← setOf_lambda_psiSet_comm hA] at this
  have hfibA' : ∀ X' ∈ pointsOn R (Q ⊔ X₀') \ {Q},
      {Z | Z ∈ lambdaSet R X' ∧ Z ∈ psiSet R A ∧ ¬ Z ≤ Q ⊔ X₀'}.ncard =
        (linesThrough R A).ncard - 1 := by
    intro X' hX'
    obtain ⟨hX'Q, hlX', hX'Ω⟩ := hPn X' hX'
    have := ncard_lambda_psi_off h hX'Ω.1 ⟨hA, hX'Ω.2.symm⟩ (mem_lambdaSet_comm hQR hX'Q)
      (mem_psiSet_comm hA hQ)
    rwa [sup_comm X' Q, hlX', hLX X' hX'Ω.1, ← setOf_lambda_psiSet_comm hA] at this
  obtain ⟨T, hT⟩ : ∃ T : Set (Subgroup G × Subgroup G × Subgroup G), T =
      {x | x.1 ∈ pointsOn R (P ⊔ X₀) \ {P} ∧ x.2.1 ∈ pointsOn R (Q ⊔ X₀') \ {Q} ∧
        x.2.2 ∈ lambdaSet R x.1 ∧ x.2.1 ∈ psiSet R x.2.2 ∧ ¬ x.2.2 ≤ P ⊔ X₀} := ⟨_, rfl⟩
  have memT : ∀ x, x ∈ T ↔ (x.1 ∈ pointsOn R (P ⊔ X₀) \ {P} ∧
      x.2.1 ∈ pointsOn R (Q ⊔ X₀') \ {Q} ∧ x.2.2 ∈ lambdaSet R x.1 ∧
      x.2.1 ∈ psiSet R x.2.2 ∧ ¬ x.2.2 ≤ P ⊔ X₀) := fun x => by rw [hT]; rfl
  have hTc : T.ncard = Nat.card A * Nat.card A * ((linesThrough R A).ncard - 1) := by
    have h1 := ncard_mul_eq_ncard_mul (s := T)
      (t := (pointsOn R (P ⊔ X₀) \ {P}) ×ˢ (pointsOn R (Q ⊔ X₀') \ {Q})) (Set.toFinite _)
      (Set.toFinite _) (fun x y => x.1 = y.1 ∧ x.2.1 = y.2) (m := 1)
      (n := (linesThrough R A).ncard - 1) ?_ ?_
    · rwa [mul_one, Set.ncard_prod, hPmc, hPnc] at h1
    · intro x hx
      obtain ⟨hx1, hx2, -⟩ := (memT x).1 hx
      rw [Set.ncard_eq_one]
      refine ⟨(x.1, x.2.1), Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
      · exact Set.mem_singleton_iff.2 (Prod.ext hy.2.1.symm hy.2.2.symm)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨⟨hx1, hx2⟩, rfl, rfl⟩
    · rintro ⟨X, X'⟩ ⟨hX, hX'⟩
      have e : {x | x ∈ T ∧ x.1 = (X, X').1 ∧ x.2.1 = (X, X').2} =
          (fun Z => (X, X', Z)) '' {Z | Z ∈ lambdaSet R X ∧ X' ∈ psiSet R Z ∧ ¬ Z ≤ P ⊔ X₀} := by
        ext ⟨Y, Y', Z⟩
        constructor
        · rintro ⟨hx, rfl, rfl⟩
          obtain ⟨-, -, hZ, hZ', hZm⟩ := (memT _).1 hx
          exact ⟨Z, ⟨hZ, hZ', hZm⟩, rfl⟩
        · rintro ⟨Z', ⟨hZ, hZ', hZm⟩, he⟩
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact ⟨(memT _).2 ⟨hX, hX', hZ, hZ', hZm⟩, rfl, rfl⟩
      rw [e, Set.ncard_image_of_injective _ fun Z Z' hZZ' => by
        simp only [Prod.mk.injEq] at hZZ'
        exact hZZ'.2.2]
      exact hfib X hX X' hX'
  have hEc : ∀ (V W : Subgroup G) (S : Set (Subgroup G)), S.ncard = Nat.card A →
      (∀ X ∈ S, {Z | Z ∈ lambdaSet R X ∧ Z ∈ psiSet R A ∧ ¬ Z ≤ W}.ncard =
        (linesThrough R A).ncard - 1) →
      {x : Subgroup G × Subgroup G | x.1 ∈ S ∧ x.2 ∈ lambdaSet R x.1 ∧ x.2 ∈ psiSet R A ∧
        ¬ x.2 ≤ W}.ncard = Nat.card A * ((linesThrough R A).ncard - 1) := by
    intro _ W S hS hfS
    have h1 := ncard_mul_eq_ncard_mul (s := {x : Subgroup G × Subgroup G | x.1 ∈ S ∧
        x.2 ∈ lambdaSet R x.1 ∧ x.2 ∈ psiSet R A ∧ ¬ x.2 ≤ W}) (t := S) (Set.toFinite _)
      (Set.toFinite _) (fun x X => x.1 = X) (m := 1) (n := (linesThrough R A).ncard - 1) ?_ ?_
    · rwa [mul_one, hS] at h1
    · intro x hx
      rw [Set.ncard_eq_one]
      refine ⟨x.1, Set.ext fun X => ⟨fun hX => Set.mem_singleton_iff.2 hX.2.symm, fun hX => ?_⟩⟩
      rw [Set.mem_singleton_iff] at hX
      subst hX
      exact ⟨hx.1, rfl⟩
    · intro X hX
      have e : {x | x ∈ {x : Subgroup G × Subgroup G | x.1 ∈ S ∧ x.2 ∈ lambdaSet R x.1 ∧
          x.2 ∈ psiSet R A ∧ ¬ x.2 ≤ W} ∧ x.1 = X} =
          (fun Z => (X, Z)) '' {Z | Z ∈ lambdaSet R X ∧ Z ∈ psiSet R A ∧ ¬ Z ≤ W} := by
        ext ⟨Y, Z⟩
        constructor
        · rintro ⟨⟨-, hZ, hZA, hZW⟩, rfl⟩
          exact ⟨Z, ⟨hZ, hZA, hZW⟩, rfl⟩
        · rintro ⟨Z', ⟨hZ, hZA, hZW⟩, he⟩
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨⟨hX, hZ, hZA, hZW⟩, rfl⟩
      rw [e, Set.ncard_image_of_injective _ fun Z Z' hZZ' => by
        simp only [Prod.mk.injEq] at hZZ'
        exact hZZ'.2]
      exact hfS X hX
  have hE₁ := hEc P (P ⊔ X₀) _ hPmc hfibA
  have hE₂ := hEc Q (Q ⊔ X₀') _ hPnc hfibA'
  have hcolm : ∀ X ∈ pointsOn R (P ⊔ X₀) \ {P}, ∀ Y ∈ pointsOn R (P ⊔ X₀) \ {P}, X ≠ Y →
      Y ∈ lambdaSet R X := fun X hX Y hY hXY =>
    (mem_lambdaSet_of_le_sup hR hiso hPR hX₀ hX.1.1 hX.1.2 hY.1.1 hY.1.2 hXY).1
  have hcoln : ∀ X ∈ pointsOn R (Q ⊔ X₀') \ {Q}, ∀ Y ∈ pointsOn R (Q ⊔ X₀') \ {Q}, X ≠ Y →
      Y ∈ lambdaSet R X := fun X hX Y hY hXY =>
    (mem_lambdaSet_of_le_sup hR hiso hQR hX₀' hX.1.1 hX.1.2 hY.1.1 hY.1.2 hXY).1
  have hT₁ : {x | x ∈ T ∧ x.2.2 ∈ psiSet R A}.ncard ≤
      Nat.card A * ((linesThrough R A).ncard - 1) := by
    rw [← hE₁]
    refine Set.ncard_le_ncard_of_injOn (fun x => (x.1, x.2.2)) ?_ ?_ (Set.toFinite _)
    · rintro x ⟨hx, hZA⟩
      obtain ⟨hX, -, hZ, -, hZm⟩ := (memT x).1 hx
      exact ⟨hX, hZ, hZA, hZm⟩
    · rintro ⟨X, X', Z⟩ ⟨hx, -⟩ ⟨Y, Y', Z'⟩ ⟨hy, -⟩ e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨hX, hX', hZ, hZ', hZm⟩ := (memT _).1 hx
      obtain ⟨-, hY', -, hZ'', -⟩ := (memT _).1 hy
      by_contra hne
      have hX'Y' : X' ≠ Y' := fun e => hne (by rw [e])
      obtain ⟨hXP, hlX, hXΩ⟩ := hPm X hX
      obtain ⟨hX'Q, -, hX'Ω⟩ := hPn X' hX'
      obtain ⟨hY'Q, -, hY'Ω⟩ := hPn Y' hY'
      exact false_of_psi_psi h hH hA hP hQ hPQ hXP hXΩ hX'Q hX'Ω hY'Q hY'Ω
        (hcoln X' hX' Y' hY' hX'Y') hZ (hlX ▸ hZm) hZ' hZ''
  have hWfacts : ∀ X X' Z, (X, X', Z) ∈ T → ⁅Z, X'⁆ ∈ lambdaSet R X' ∧
      ⁅Z, X'⁆ ∈ lambdaSet R Z ∧ ¬ ⁅Z, X'⁆ ≤ Q ⊔ X₀' ∧ X ∈ psiSet R ⁅Z, X'⁆ := by
    intro X X' Z hx
    obtain ⟨hX, hX', hZ, hZ', hZm⟩ := (memT _).1 hx
    obtain ⟨hXP, hlX, hXΩ⟩ := hPm X hX
    obtain ⟨hX'Q, hlX', hX'Ω⟩ := hPn X' hX'
    have hZR : Z ∈ R := hZ.1.1
    obtain ⟨hWZ, hWX'⟩ := commutator_mem_lambdaSet h hZR hX'Ω.1 hZ'.2
    have hWR : ⁅Z, X'⁆ ∈ R := hWZ.1.1
    have hnle := not_le_commutator_of_psi_psi h hH hA hP hQ hPQ hXP hXΩ hX'Q hX'Ω hZ
      (hlX ▸ hZm) hZ'
    rw [hlX'] at hnle
    refine ⟨hWX', hWZ, hnle, hXΩ.1, ?_⟩
    obtain ⟨-, hop⟩ := opposite_of_psi_psi h hH hA hP hQ hPQ hXP hXΩ hX'Q hX'Ω
    have hXW : X ∉ lambdaSet R ⁅Z, X'⁆ := fun hl =>
      notMem_lambdaSet_of_opposite h hXΩ.1 hop.2 (mem_lambdaSet_comm hWR hl) hWX'
    have hXne : X ≠ ⁅Z, X'⁆ := by
      intro e
      rw [← e] at hWX'
      exact notMem_omegaSet_of_mem_lambdaSet h hXΩ.1 (mem_lambdaSet_comm hX'Ω.1 hWX') hop
    exact (special_of_mem_lambdaSet h hH hWR (mem_lambdaSet_comm hZR hWZ)
      (mem_lambdaSet_comm hXΩ.1 hZ) hXW hXne).1
  have hT₂ : {x | x ∈ T ∧ ⁅x.2.2, x.2.1⁆ ∈ psiSet R A}.ncard ≤
      Nat.card A * ((linesThrough R A).ncard - 1) := by
    rw [← hE₂]
    refine Set.ncard_le_ncard_of_injOn (fun x => (x.2.1, ⁅x.2.2, x.2.1⁆)) ?_ ?_
      (Set.toFinite _)
    · rintro ⟨X, X', Z⟩ ⟨hx, hWA⟩
      obtain ⟨-, hX', -⟩ := (memT _).1 hx
      obtain ⟨hWX', -, hWn, -⟩ := hWfacts X X' Z hx
      exact ⟨hX', hWX', hWA, hWn⟩
    · rintro ⟨X, X', Z⟩ ⟨hx, -⟩ ⟨Y, Y', Z'⟩ ⟨hy, -⟩ e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, e⟩ := e
      obtain ⟨hX, hX', hZ, -, -⟩ := (memT _).1 hx
      obtain ⟨hY, -, hZ'', -, -⟩ := (memT _).1 hy
      obtain ⟨hWX', hWZ, hWn, hXW⟩ := hWfacts X X' Z hx
      obtain ⟨-, hWZ', -, hYW⟩ := hWfacts Y X' Z' hy
      rw [← e] at hWZ' hYW
      obtain ⟨hXP, -, hXΩ⟩ := hPm X hX
      obtain ⟨hYP, -, hYΩ⟩ := hPm Y hY
      obtain ⟨hX'Q, hlX', hX'Ω⟩ := hPn X' hX'
      have hXY : X = Y := by
        by_contra hXY
        exact false_of_psi_psi h hH hA hQ hP hQP hX'Q hX'Ω hXP hXΩ hYP hYΩ
          (hcolm X hX Y hY hXY) hWX' (hlX' ▸ hWn) hXW hYW
      subst hXY
      have hWR : ⁅Z, X'⁆ ∈ R := hWZ.1.1
      have h1 : Z = ⁅X, ⁅Z, X'⁆⁆ :=
        eq_commutator h hXΩ.1 hWR hXW.2.symm hZ (mem_lambdaSet_comm hZ.1.1 hWZ)
      have h2 : Z' = ⁅X, ⁅Z, X'⁆⁆ :=
        eq_commutator h hXΩ.1 hWR hXW.2.symm hZ'' (mem_lambdaSet_comm hZ''.1.1 hWZ')
      exact Prod.ext rfl (Prod.ext rfl (h1.trans h2.symm))
  obtain ⟨⟨X, X', Z⟩, hx, hZΩ, hWΩ⟩ : ∃ x ∈ T, x.2.2 ∈ omegaSet R A ∧
      ⁅x.2.2, x.2.1⁆ ∈ omegaSet R A := by
    by_contra hno
    push Not at hno
    have hsub : T ⊆ {x | x ∈ T ∧ x.2.2 ∈ psiSet R A} ∪
        {x | x ∈ T ∧ ⁅x.2.2, x.2.1⁆ ∈ psiSet R A} := by
      rintro ⟨X, X', Z⟩ hx
      obtain ⟨hX, hX', hZ, -, -⟩ := (memT _).1 hx
      obtain ⟨-, -, hXΩ⟩ := hPm X hX
      obtain ⟨-, -, hX'Ω⟩ := hPn X' hX'
      obtain ⟨hWX', -, -, -⟩ := hWfacts X X' Z hx
      rcases mem_psiSet_or_omegaSet h hH hA hXΩ hZ with hZA | hZA
      · exact Or.inl ⟨hx, hZA⟩
      · rcases mem_psiSet_or_omegaSet h hH hA hX'Ω hWX' with hWA | hWA
        · exact Or.inr ⟨hx, hWA⟩
        · exact absurd hWA (hno (X, X', Z) hx hZA)
    have h1 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (Set.ncard_union_le _ _)
    rw [hTc] at h1
    have h2 := h1.trans (Nat.add_le_add hT₁ hT₂)
    have ht : 1 ≤ (linesThrough R A).ncard - 1 := by omega
    generalize (linesThrough R A).ncard - 1 = t at h2 ht
    generalize Nat.card A = q at h2 hq
    have hqt : 1 ≤ q * t := Nat.mul_pos (by omega) (by omega)
    have h3 : 3 * (q * t) ≤ q * q * t :=
      calc 3 * (q * t) ≤ q * (q * t) := Nat.mul_le_mul_right _ hq
        _ = q * q * t := (Nat.mul_assoc q q t).symm
    clear h1
    generalize q * q * t = v at h2 h3
    generalize q * t = u at h2 h3 hqt
    omega
  obtain ⟨hX, hX', hZ, hZ', -⟩ := (memT _).1 hx
  obtain ⟨hWX', hWZ, -, -⟩ := hWfacts X X' Z hx
  obtain ⟨-, -, hXΩ⟩ := hPm X hX
  obtain ⟨-, -, hX'Ω⟩ := hPn X' hX'
  have hm : MOrbit R A X₀ X := by
    by_cases hXX₀ : X₀ = X
    · rw [hXX₀]
      exact MOrbit.refl R A X
    · exact mOrbit_of_mem_lambdaSet h hH hA hX₀Ω hXΩ
        (mem_lambdaSet_of_le_sup hR hiso hPR hX₀ hX₀Ω.1 le_sup_right hX.1.1 hX.1.2 hXX₀).1
  have hn : MOrbit R A X' X₀' := by
    by_cases hXX₀ : X' = X₀'
    · rw [hXX₀]
      exact MOrbit.refl R A X₀'
    · exact mOrbit_of_mem_lambdaSet h hH hA hX'Ω hX₀'Ω
        (mem_lambdaSet_of_le_sup hR hiso hQR hX₀' hX'.1.1 hX'.1.2 hX₀'Ω.1 le_sup_right hXX₀).1
  exact hm.trans ((mOrbit_of_mem_lambdaSet h hH hA hXΩ hZΩ hZ).trans
    ((mOrbit_of_mem_lambdaSet h hH hA hZΩ hWΩ hWZ).trans
      ((mOrbit_of_mem_lambdaSet h hH hA hWΩ hX'Ω (mem_lambdaSet_comm hX'Ω.1 hWX')).trans hn)))

theorem mOrbit_of_psi {A C X Y : Subgroup G} (hA : A ∈ R) (hq : 3 ≤ Nat.card A)
    (hC : C ∈ psiSet R A) (hX : X ∈ lambdaSet R C) (hXΩ : X ∈ omegaSet R A)
    (hY : Y ∈ lambdaSet R C) (hYΩ : Y ∈ omegaSet R A) : MOrbit R A X Y := by
  classical
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hCR : C ∈ R := hC.1
  obtain ⟨hDA, hDC⟩ := commutator_mem_lambdaSet h hA hCR hC.2
  have hDR : ⁅A, C⁆ ∈ R := hDA.1.1
  have hCD : C ∈ lambdaSet R ⁅A, C⁆ := mem_lambdaSet_comm hCR hDC
  obtain ⟨Q, hQm, hQne⟩ : (pointsOn R (C ⊔ ⁅A, C⁆) \ {C, ⁅A, C⁆}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), Set.ncard_sdiff (fun Z hZ => by
        rcases hZ with rfl | rfl
        exacts [⟨hCR, le_sup_left⟩, ⟨hDR, le_sup_right⟩]),
      ncard_pointsOn h hCR hDC, Set.ncard_pair hDC.1.2.1.symm, hR.card_eq hCR hA]
    omega
  have hQC : Q ≠ C := fun e => hQne (Or.inl e)
  have hQD : Q ≠ ⁅A, C⁆ := fun e => hQne (Or.inr e)
  obtain ⟨hQCl, -⟩ := mem_lambdaSet_of_le_sup hR hiso hCR hDC hCR le_sup_left hQm.1 hQm.2
    (Ne.symm hQC)
  obtain ⟨hQDl, hlineD⟩ := mem_lambdaSet_of_le_sup hR hiso hCR hDC hDR le_sup_right hQm.1 hQm.2
    (Ne.symm hQD)
  have hQA : Q ∉ lambdaSet R A := by
    intro hQA
    have hle : Q ≤ A ⊔ ⁅A, C⁆ := le_line h hH hA hDA hA le_sup_left hDR le_sup_right
      hDA.1.2.1.symm hQm.1 hQA.1.2.2.symm hQDl.1.2.2.symm
    have hlines : ⁅A, C⁆ ⊔ Q = A ⊔ ⁅A, C⁆ := (mem_lambdaSet_of_le_sup hR hiso hA hDA hDR
      le_sup_right hQm.1 hle (Ne.symm hQD)).2
    have hCle : C ≤ A ⊔ ⁅A, C⁆ := by
      rw [← hlines, hlineD]
      exact le_sup_left
    have hCA : C ≠ A := fun e => notMem_psiSet_self h hA (e ▸ hC)
    exact notMem_psiSet_of_mem_lambdaSet h ((mem_lambdaSet_of_le_sup hR hiso hA hDA hA
      le_sup_left hCR hCle (Ne.symm hCA)).1) hC
  have hQA' : Q ≠ A := by
    intro e
    rw [e] at hQCl
    exact notMem_psiSet_of_mem_lambdaSet h (mem_lambdaSet_comm hCR hQCl) hC
  have hQψ : Q ∈ psiSet R A :=
    ⟨hQm.1, (special_of_mem_lambdaSet h hH hA hDA hQDl hQA hQA').1⟩
  obtain ⟨X', hX'Ω, hQX'⟩ : {B | B ∈ omegaSet R A ∧ Q ∈ lambdaSet R B}.Nonempty := by
    rw [setOf_omegaSet_lambdaSet h hH hA hQψ, ← Set.ncard_pos (Set.toFinite _)]
    obtain ⟨hl, -⟩ := commutator_mem_lambdaSet h hA hQm.1 hQψ.2
    rw [ncard_lambdaSet_diff_pointsOn' h hQm.1 (commutator_mem_lambdaSet h hA hQm.1 hQψ.2).2,
      ncard_lambdaSet h hQm.1, hR.card_eq hQm.1 hA]
    have hL2 : 2 ≤ (linesThrough R Q).ncard := by
      have hΩ := ncard_omegaSet h hH hA rfl rfl
      have hpos : 0 < (omegaSet R A).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨X, hXΩ⟩
      rw [ncard_linesThrough_eq h hA hQm.1]
      by_contra hlt
      rw [hΩ, show (linesThrough R A).ncard - 1 = 0 by omega] at hpos
      simp at hpos
    have h2 := Nat.mul_le_mul_right (Nat.card A) hL2
    generalize (linesThrough R Q).ncard * Nat.card A = m at h2 ⊢
    omega
  have hX' : X' ∈ lambdaSet R Q := mem_lambdaSet_comm hX'Ω.1 hQX'
  exact (mOrbit_of_psi_psi h hH hA hq hC hQψ hQCl hX hXΩ hX' hX'Ω).trans
    (mOrbit_of_psi_psi h hH hA hq hC hQψ hQCl hY hYΩ hX' hX'Ω).symm

theorem M_transitive_of_three_le {A B B' : Subgroup G} (hA : A ∈ R) (hq : 3 ≤ Nat.card A)
    (hB : B ∈ omegaSet R A) (hB' : B' ∈ omegaSet R A) : MOrbit R A B B' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBR : B ∈ R := hB.1
  have hB'R : B' ∈ R := hB'.1
  rcases eq_or_mem_of_mem h hH hBR hB'R with rfl | hl | hs | ho
  · exact MOrbit.refl R A B'
  · exact mOrbit_of_mem_lambdaSet h hH hA hB hB' hl
  ·
    obtain ⟨hCB, hCB'⟩ := commutator_mem_lambdaSet h hBR hB'R hs.2
    rcases mem_psiSet_or_omegaSet h hH hA hB hCB with hC | hC
    · exact mOrbit_of_psi h hH hA hq hC (mem_lambdaSet_comm hBR hCB) hB
        (mem_lambdaSet_comm hB'R hCB') hB'
    · exact (mOrbit_of_mem_lambdaSet h hH hA hB hC hCB).trans
        (mOrbit_of_mem_lambdaSet h hH hA hC hB' (mem_lambdaSet_comm hB'R hCB'))
  ·
    obtain ⟨D, hD⟩ := lambdaSet_nonempty hR hiso h.nondeg hBR
    obtain ⟨P₁, ⟨hP₁R, hP₁le, hP₁ψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hBR hB'R ho.2 hD
    have hP₁B : P₁ ≠ B := fun e => notMem_omegaSet_of_mem_psiSet h hB'R hP₁ψ
      (e ▸ ⟨hBR, ho.2.symm⟩)
    obtain ⟨hP₁l, -⟩ := mem_lambdaSet_of_le_sup hR hiso hBR hD hBR le_sup_left hP₁R hP₁le
      (Ne.symm hP₁B)
    obtain ⟨hP₂B', hP₂P₁⟩ := commutator_mem_lambdaSet h hB'R hP₁R hP₁ψ.2
    rcases mem_psiSet_or_omegaSet h hH hA hB hP₁l with h1 | h1 <;>
      rcases mem_psiSet_or_omegaSet h hH hA hB' hP₂B' with h2 | h2
    · exact mOrbit_of_psi_psi h hH hA hq h1 h2 hP₂P₁ (mem_lambdaSet_comm hBR hP₁l) hB
        (mem_lambdaSet_comm hB'R hP₂B') hB'
    · exact (mOrbit_of_psi h hH hA hq h1 (mem_lambdaSet_comm hBR hP₁l) hB hP₂P₁ h2).trans
        (mOrbit_of_mem_lambdaSet h hH hA h2 hB' (mem_lambdaSet_comm hB'R hP₂B'))
    · exact (mOrbit_of_mem_lambdaSet h hH hA hB h1 hP₁l).trans
        (mOrbit_of_psi h hH hA hq h2 (mem_lambdaSet_comm hP₁R hP₂P₁) h1
          (mem_lambdaSet_comm hB'R hP₂B') hB')
    · exact (mOrbit_of_mem_lambdaSet h hH hA hB h1 hP₁l).trans
        ((mOrbit_of_mem_lambdaSet h hH hA h1 h2 hP₂P₁).trans
          (mOrbit_of_mem_lambdaSet h hH hA h2 hB' (mem_lambdaSet_comm hB'R hP₂B')))

theorem mTransitive_of_three_le {A₁ : Subgroup G} (hA₁ : A₁ ∈ R) (hq : 3 ≤ Nat.card A₁) :
    MTransitive R := fun _ hA _ hB _ hB' =>
  M_transitive_of_three_le h hH hA ((h.root.card_eq hA hA₁) ▸ hq) hB hB'

theorem mTransitive_of_not_two_three {A : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard)
    (hne : ¬ (Nat.card A = 2 ∧ (linesThrough R A).ncard = 3)) : MTransitive R := by
  have := h.finite
  by_cases hq : 3 ≤ Nat.card A
  · exact mTransitive_of_three_le h hH hA hq
  have hq2 : Nat.card A = 2 := by
    have h1 : 1 < Nat.card A := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact h.root.ne_bot A hA
    omega
  rcases ncard_linesThrough_of_two h hH hA hq2 h3 with hL | hL | hL
  · exact absurd ⟨hq2, hL⟩ hne
  · exact absurd hL (ncard_linesThrough_ne_five h hH hA hq2)
  · exact mTransitive_of_nine h hH hA hq2 hL

end Connected

end CaseH

end CFSG.Timmesfeld.ARS
