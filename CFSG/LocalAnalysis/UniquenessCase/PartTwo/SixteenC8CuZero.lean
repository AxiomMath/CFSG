module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuInj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix CFSG.Quasithin.SmithCurtis

@[expose] def mCox : Fin 3 → Fin 3 → ℕ := ![![1, 3, 2], ![3, 1, 4], ![2, 4, 1]]

@[expose] def altW (a b : Fin 3) : ℕ → List (Fin 3)
  | 0 => []
  | n + 1 => a :: altW b a n

@[expose] def applyMove (l : List (Fin 3)) (p : ℕ) : Option (List (Fin 3)) :=
  match l.drop p with
  | a :: b :: _ =>
    if a ≠ b ∧ (l.drop p).take (mCox a b) = altW a b (mCox a b) then
      some (l.take p ++ altW b a (mCox a b) ++ (l.drop p).drop (mCox a b))
    else none
  | _ => none

@[expose] def applyMoves : List (Fin 3) → List ℕ → Option (List (Fin 3))
  | l, [] => some l
  | l, p :: ps =>
    match applyMove l p with
    | some l' => applyMoves l' ps
    | none => none

@[expose] def cert0 : Fin 48 → List ℕ :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

@[expose] def cert1 : Fin 48 → List ℕ :=
  ![[], [], [], [], [0], [], [], [], [], [0], [0], [], [], [], [], [], [0], [0], [], [], [], [], [],
    [], [0], [0], [0], [], [], [], [], [], [0], [0], [0], [], [], [], [], [0], [0], [], [], [], [0],
    [0], [], [0]]

@[expose] def cert2 : Fin 48 → List ℕ :=
  ![[], [0], [], [], [0], [0], [], [], [], [0], [0], [0], [], [0], [], [], [0], [0, 1], [0], [0],
    [], [0, 3], [0], [], [0], [0, 1, 4], [1, 0], [0], [2, 3, 0, 3], [], [3, 0], [], [0, 3, 4, 1, 4],
    [0], [4, 1, 0], [0], [2, 3, 0, 3], [3, 0, 3, 2], [], [0, 3, 4, 1, 4], [4, 1, 0, 4, 3], [0],
    [2, 3, 0, 3, 4, 2, 1], [3, 0, 3, 2], [0, 3, 4, 1, 4, 5, 3, 2], [4, 1, 0, 4, 3],
    [1, 2, 4, 3, 0, 3, 2], [2, 3, 5, 4, 1, 0, 4, 3]]

@[expose] def certT (s : Fin 3) : Fin 48 → List ℕ := ![cert0, cert1, cert2] s

@[expose] def IsAsc (s : Fin 3) (k : Fin 48) : Prop :=
  (canW (mulTab s k)).length = (canW k).length + 1

instance (s : Fin 3) (k : Fin 48) : Decidable (IsAsc s k) := by
  unfold IsAsc
  infer_instance

theorem cert_spec : ∀ (s : Fin 3) (k : Fin 48),
    (IsAsc s k ∧ applyMoves (s :: canW k) (certT s k) = some (canW (mulTab s k))) ∨
      (¬IsAsc s k ∧ (canW k).length = (canW (mulTab s k)).length + 1 ∧
        applyMoves (canW k) (certT s k) = some (s :: canW (mulTab s k))) := by
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G6 V)

theorem evT_altW {a b : Fin 3} (hab : a ≠ b) {y : V} (hy : y ∈ fixU ρ) :
    evT ρ (altW a b (mCox a b)) y = evT ρ (altW b a (mCox a b)) y := by
  fin_cases a <;> fin_cases b <;> simp at hab <;> simp [mCox, altW, evT]
  · exact Th_braid3 ρ hy
  · exact Th_comm ρ (by decide) hy
  · exact (Th_braid3 ρ hy).symm
  · exact Th_braid4 ρ hy
  · exact Th_comm ρ (by decide) hy
  · exact (Th_braid4 ρ hy).symm

theorem evT_applyMove {l l' : List (Fin 3)} {p : ℕ} (h : applyMove l p = some l') {x : V}
    (hx : x ∈ fixU ρ) : evT ρ l x = evT ρ l' x := by
  unfold applyMove at h
  split at h
  · rename_i a b r hd
    split_ifs at h with hc
    cases h
    obtain ⟨hab, htake⟩ := hc
    have hd' : l.drop p = altW a b (mCox a b) ++ (l.drop p).drop (mCox a b) := by
      conv_lhs => rw [← List.take_append_drop (mCox a b) (l.drop p)]
      rw [htake]
    have hl : l = l.take p ++ (altW a b (mCox a b) ++ (l.drop p).drop (mCox a b)) := by
      rw [← hd', List.take_append_drop]
    conv_lhs => rw [hl]
    simp only [List.append_assoc, evT_append]
    rw [evT_altW ρ hab (evT_mem_fixU ρ _ hx)]
  · exact absurd h (by simp)

theorem evT_applyMoves {l l' : List (Fin 3)} {ms : List ℕ} (h : applyMoves l ms = some l')
    {x : V} (hx : x ∈ fixU ρ) : evT ρ l x = evT ρ l' x := by
  induction ms generalizing l with
  | nil =>
    simp only [applyMoves, Option.some.injEq] at h
    rw [h]
  | cons m ms ih =>
    simp only [applyMoves] at h
    split at h
    · rename_i l'' hm
      rw [evT_applyMove ρ hm hx]
      exact ih h
    · exact absurd h (by simp)

theorem Th_evT (s : Fin 3) (k : Fin 48) {x : V} (hx : x ∈ fixU ρ) :
    (IsAsc s k ∧ Th ρ s (evT ρ (canW k) x) = evT ρ (canW (mulTab s k)) x) ∨
      ((canW k).length = (canW (mulTab s k)).length + 1 ∧
        Th ρ s (evT ρ (canW k) x) = evT ρ (canW k) x) := by
  rcases cert_spec s k with ⟨ha, hc⟩ | ⟨_, hl, hc⟩
  · left
    refine ⟨ha, ?_⟩
    rw [← evT_cons, evT_applyMoves ρ hc hx]
  · right
    refine ⟨hl, ?_⟩
    rw [evT_applyMoves ρ hc hx, evT_cons, Th_Th ρ s (evT_mem_fixU ρ _ hx)]

theorem exists_eigen [Finite V] [Nontrivial V] :
    ∃ y ∈ fixU ρ, y ≠ 0 ∧ ∀ s : Fin 3, Th ρ s y = 0 ∨ Th ρ s y = y := by
  classical
  obtain ⟨x₀, hx₀, hx₀0⟩ := exists_fixU_ne ρ
  let S : Finset (Fin 48) := Finset.univ.filter fun k => ∃ x ∈ fixU ρ, evT ρ (canW k) x ≠ 0
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x₀, hx₀, hx₀0⟩⟩
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image (fun k => (canW k).length) hS
  obtain ⟨-, x, hx, hne⟩ := Finset.mem_filter.mp hk
  refine ⟨evT ρ (canW k) x, evT_mem_fixU ρ _ hx, hne, fun s => ?_⟩
  rcases Th_evT ρ s k hx with ⟨ha, he⟩ | ⟨_, he⟩
  · left
    rw [he]
    by_contra h
    have hm := hmax (mulTab s k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, h⟩)
    unfold IsAsc at ha
    omega
  · right
    exact he

theorem hW_eigen {y : V} (hy : ∀ s : Fin 3, Th ρ s y = 0 ∨ Th ρ s y = y) (l : List (Fin 3)) :
    hW ρ l y = 0 ∨ hW ρ l y = y := by
  induction l with
  | nil => exact Or.inr rfl
  | cons s l ih =>
    rw [hW_cons]
    rcases ih with h | h
    · left
      rw [h, map_zero, add_zero]
    · rw [h]
      rcases hy s with h' | h'
      · right
        rw [h', add_zero]
      · left
        rw [h', add_self_zmod2]

theorem fixU_eq {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V] {y : V}
    (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) (heig : ∀ s : Fin 3, Th ρ s y = 0 ∨ Th ρ s y = y) {x : V}
    (hx : x ∈ fixU ρ) : x = 0 ∨ x = y := by
  have h := fixU_le_span hρ hy hy0 hx
  have hle : Submodule.span (ZMod 2) (Set.range fun j => hW ρ (canW j) y) ≤
      Submodule.span (ZMod 2) {y} := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show hW ρ (canW j) y ∈ _
    rcases hW_eigen ρ heig (canW j) with h' | h'
    · rw [h']
      exact zero_mem _
    · rw [h']
      exact Submodule.subset_span rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle h)
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · left
    rw [← hc, zero_smul]
  · right
    rw [← hc, one_smul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
