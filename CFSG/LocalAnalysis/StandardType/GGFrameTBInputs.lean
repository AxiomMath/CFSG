module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly TableB

@[expose] def frameReflSet {G : Type} [Group G] {A : Subgroup G} (𝒜 : Subgroup (MulAut ↥A)) :
    Set (MulAut ↥A) :=
  {φ | φ ∈ 𝒜 ∧ GGIsReflection 3 φ}

@[expose] noncomputable def frameNonComm {G : Type} [Group G] {A : Subgroup G} (𝒜 : Subgroup (MulAut ↥A))
    (φ : MulAut ↥A) : ℕ :=
  {ψ | ψ ∈ frameReflSet 𝒜 ∧ φ * ψ ≠ ψ * φ}.ncard

@[expose] def FrameNumIs {G : Type} [Group G] {A : Subgroup G} (𝒜 : Subgroup (MulAut ↥A)) (N : ℕ)
    (d : Option ℕ) : Prop :=
  (frameReflSet 𝒜).ncard = N ∧
    match d with
    | some d => ∀ φ ∈ frameReflSet 𝒜, frameNonComm 𝒜 φ = d
    | none => ¬ ∃ d : ℕ, ∀ φ ∈ frameReflSet 𝒜, frameNonComm 𝒜 φ = d

@[expose] def FrameConn {G : Type} [Group G] {A : Subgroup G} (𝒜 : Subgroup (MulAut ↥A)) : Prop :=
  ∀ φ ∈ frameReflSet 𝒜, ∀ ψ ∈ frameReflSet 𝒜,
    Relation.ReflTransGen (fun a b => a ∈ frameReflSet 𝒜 ∧ b ∈ frameReflSet 𝒜 ∧ a * b ≠ b * a) φ ψ

@[expose] def frameTagTabled : LargeEvenLieTag → Prop
  | .twA => True
  | .A => True
  | .B => True
  | .C => True
  | .D => True
  | .twD => True
  | .twE6 => True
  | .E7 => True
  | .E8 => True
  | _ => False

@[expose] def frameTagNum : LargeEvenLieTag → ℕ → ℕ × Option ℕ
  | .twA, m => (m * (m + 1) / 2, some (2 * (m - 1)))
  | .A, m => (((m + 1) / 2) ^ 2, none)
  | .B, m => (m ^ 2, none)
  | .C, m => (m ^ 2, none)
  | .D, m =>
    if m % 2 = 0 then (m * (m - 1), some (4 * (m - 2))) else ((m - 1) ^ 2, none)
  | .twD, m =>
    if m % 2 = 1 then (m * (m - 1), some (4 * (m - 2))) else ((m - 1) ^ 2, none)
  | .E6, _ => (24, none)
  | .twE6, _ => (36, some 20)
  | .E7, _ => (63, some 32)
  | .E8, _ => (120, some 56)
  | _, _ => (0, none)

@[expose] def frameLabNum (lab : LargeEvenLabel) : ℕ × Option ℕ :=
  frameTagNum lab.tag lab.rank

@[expose] def frameTBRange (lab : LargeEvenLabel) (r : ℕ) : Prop :=
  (lab.tag = .twA → (lab.rank + 1) / 3 + 2 ≤ r) ∧ (lab.tag = .E8 → 7 ≤ r)

@[expose] def GGFrameTBNumerologyInput : Prop :=
  (∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.n = 1 → frameTagTabled lab.tag →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ r : ℕ, 6 ≤ r → frameTBRange lab r → GGTorusReflGenW 3 r R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A →
            (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (frameLabNum lab).1
                (frameLabNum lab).2 ∧
              FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
            ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S) ∧
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.n = 1 → lab.tag = .E8 →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 7 R

@[expose] def GGFrameTBVacuousInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.n = 1 → ¬ frameTagTabled lab.tag →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ r : ℕ, 6 ≤ r → ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
        (A : Subgroup (MulAut L')), ¬ GGTorusTBGroup 3 r R I L' ψ A

@[expose] def frameEndPair (n : ℕ) (N : ℕ) (d : Option ℕ) : Prop :=
  (n = 7 ∧ ((N = 21 ∧ d = some 10) ∨ (N = 30 ∧ d = some 16) ∨ (N = 36 ∧ d = some 20))) ∨
    (n = 8 ∧ ((N = 36 ∧ d = some 14) ∨ (N = 42 ∧ d = some 20) ∨ (N = 63 ∧ d = some 32)))

theorem frameTBRange_of_dimension {lab : LargeEvenLabel} {n : ℕ} (hn : n = 7 ∨ n = 8)
    (hd : lab.tag = .twA → lab.rank + 1 ≤ n + 2) (h8 : lab.tag = .E8 → n = 8) :
    frameTBRange lab (n - 1) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · have := hd ht
    rcases hn with rfl | rfl <;> omega
  · have := h8 ht
    omega

private lemma frameEnd_twA {m n : ℕ}
    (h : frameEndPair n (m * (m + 1) / 2) (some (2 * (m - 1)))) :
    (n = 7 ∧ m = 6) ∨ (n = 8 ∧ m = 8) := by
  unfold frameEndPair at h
  simp only [Option.some.injEq] at h
  rcases h with ⟨hn, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨hn, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact Or.inl ⟨hn, by omega⟩
  · obtain rfl : m = 9 := by omega
    exfalso
    omega
  · obtain rfl : m = 11 := by omega
    exfalso
    omega
  · exact Or.inr ⟨hn, by omega⟩
  · obtain rfl : m = 11 := by omega
    exfalso
    omega
  · obtain rfl : m = 17 := by omega
    exfalso
    omega

private lemma frameEnd_D {m n : ℕ}
    (h : frameEndPair n (m * (m - 1)) (some (4 * (m - 2)))) :
    (n = 7 ∧ m = 6) ∨ (n = 8 ∧ m = 7) := by
  unfold frameEndPair at h
  simp only [Option.some.injEq] at h
  rcases h with ⟨hn, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨hn, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exfalso
    omega
  · exact Or.inl ⟨hn, by omega⟩
  · obtain rfl : m = 7 := by omega
    exfalso
    omega
  · exfalso
    omega
  · exact Or.inr ⟨hn, by omega⟩
  · obtain rfl : m = 10 := by omega
    exfalso
    omega

theorem frameLab_mem_of_num {n : ℕ} {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hn : lab.n = 1) (h : frameEndPair n (frameLabNum lab).1 (frameLabNum lab).2) :
    (n = 7 ∧ ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .D ∧ lab.rank = 6) ∨
        (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1) ∨
      (n = 8 ∧ ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .twA ∧ lab.rank = 8) ∨
        (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) := by
  obtain ⟨tag, rank, nn⟩ := lab
  change nn = 1 at hn
  subst hn
  cases tag
  case twA =>
    have h' : frameEndPair n (rank * (rank + 1) / 2) (some (2 * (rank - 1))) := h
    rcases frameEnd_twA h' with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
    · exact Or.inl ⟨rfl, Or.inl ⟨rfl, hr⟩, rfl⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨rfl, hr⟩), rfl⟩
  case D =>
    by_cases hp : rank % 2 = 0
    · have h' : frameEndPair n (rank * (rank - 1)) (some (4 * (rank - 2))) := by
        have h'' : frameEndPair n (frameTagNum .D rank).1 (frameTagNum .D rank).2 := h
        simp only [frameTagNum, if_pos hp] at h''
        exact h''
      rcases frameEnd_D h' with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      · exact Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, hr⟩), rfl⟩
      · exfalso
        omega
    · have h'' : frameEndPair n (frameTagNum .D rank).1 (frameTagNum .D rank).2 := h
      simp only [frameTagNum, if_neg hp] at h''
      simp [frameEndPair] at h''
  case twD =>
    by_cases hp : rank % 2 = 1
    · have h' : frameEndPair n (rank * (rank - 1)) (some (4 * (rank - 2))) := by
        have h'' : frameEndPair n (frameTagNum .twD rank).1 (frameTagNum .twD rank).2 := h
        simp only [frameTagNum, if_pos hp] at h''
        exact h''
      rcases frameEnd_D h' with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      · exfalso
        omega
      · exact Or.inr ⟨rfl, Or.inl ⟨rfl, hr⟩, rfl⟩
    · have h'' : frameEndPair n (frameTagNum .twD rank).1 (frameTagNum .twD rank).2 := h
      simp only [frameTagNum, if_neg hp] at h''
      simp [frameEndPair] at h''
  case twE6 =>
    have hr : rank = 0 := by simpa [LargeEvenInLambda2] using hΛ
    have h' : frameEndPair n 36 (some 20) := h
    unfold frameEndPair at h'
    rcases h' with ⟨hn7, -⟩ | ⟨hn8, h'⟩
    · exact Or.inl ⟨hn7, Or.inr (Or.inr ⟨rfl, hr⟩), rfl⟩
    · simp at h'
  case E7 =>
    have hr : rank = 0 := by simpa [LargeEvenInLambda2] using hΛ
    have h' : frameEndPair n 63 (some 32) := h
    unfold frameEndPair at h'
    rcases h' with ⟨hn7, h'⟩ | ⟨hn8, -⟩
    · simp at h'
    · exact Or.inr ⟨hn8, Or.inr (Or.inr ⟨rfl, hr⟩), rfl⟩
  all_goals
    exfalso
    have h' := h
    simp [frameLabNum, frameTagNum, frameEndPair] at h'

end CFSG.StandardType.FrameRoute

end
