module

public import CFSG.Quasithin.Background.JonesParshallCurtisInj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

@[expose] def applyMove (l : List (Fin 4)) : ℕ × Bool → Option (List (Fin 4))
  | (p, false) =>
    match l.drop p with
    | a :: b :: r =>
      if a.val + 2 ≤ b.val ∨ b.val + 2 ≤ a.val then some (l.take p ++ b :: a :: r) else none
    | _ => none
  | (p, true) =>
    match l.drop p with
    | a :: b :: c :: r =>
      if a = c ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val) then some (l.take p ++ b :: a :: b :: r)
      else none
    | _ => none

@[expose] def applyMoves : List (Fin 4) → List (ℕ × Bool) → Option (List (Fin 4))
  | l, [] => some l
  | l, m :: ms =>
    match applyMove l m with
    | some l' => applyMoves l' ms
    | none => none

@[expose] def cert0 : Fin 120 → List (ℕ × Bool) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], []]

@[expose] def cert1 : Fin 120 → List (ℕ × Bool) :=
  ![[], [], [], [], [], [(0, true)], [], [], [], [], [], [], [], [], [(0, true)], [(0, true)],
    [(0, true)], [], [], [], [], [], [], [], [], [], [], [], [], [(0, true)], [(0, true)],
    [(0, true)], [(0, true)], [(0, true)], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [(0, true)], [(0, true)], [(0, true)], [(0, true)], [(0, true)], [(0, true)],
    [(0, true)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [(0, true)],
    [(0, true)], [(0, true)], [(0, true)], [(0, true)], [(0, true)], [(0, true)], [(0, true)],
    [], [], [], [], [], [], [], [], [], [], [], [], [(0, true)], [(0, true)], [(0, true)],
    [(0, true)], [(0, true)], [(0, true)], [(0, true)], [], [], [], [], [], [], [], [],
    [(0, true)], [(0, true)], [(0, true)], [(0, true)], [(0, true)], [], [], [], [],
    [(0, true)], [(0, true)], [(0, true)], [], [(0, true)]]

@[expose] def cert2 : Fin 120 → List (ℕ × Bool) :=
  ![[], [(0, false)], [], [], [], [(0, false)], [(0, false)], [(0, false)], [], [(0, true)],
    [], [], [], [], [(0, false)], [(0, false), (1, true)], [(0, false)], [(0, false)],
    [(0, false)], [(0, false)], [(2, false), (0, true)], [], [(0, true)], [(0, true)], [], [],
    [], [], [], [(0, false), (3, false), (1, true)], [(0, false)], [(1, true), (0, false)],
    [(0, false), (1, true)], [(0, false)], [(0, false)], [(0, false)], [(0, false)],
    [(0, false)], [(2, false), (0, true), (2, true), (1, false)], [(2, false), (0, true)], [],
    [(0, true), (2, false)], [(0, true)], [(0, true)], [], [], [], [], [],
    [(0, false), (3, false), (1, true), (3, true), (2, false)],
    [(0, false), (3, false), (1, true)], [(0, false)], [(1, true), (0, false), (3, false)],
    [(1, true), (0, false)], [(0, false), (1, true)], [(0, false)], [(0, false)], [(0, false)],
    [(0, false)], [(0, false)], [(1, false), (2, true), (0, true), (2, false)],
    [(2, false), (0, true), (2, true), (1, false)], [(2, false), (0, true)], [],
    [(0, true), (2, false)], [(0, true)], [(0, true)], [], [], [], [],
    [(2, false), (3, true), (1, true), (0, false), (3, false)],
    [(0, false), (3, false), (1, true), (3, true), (2, false)],
    [(0, false), (3, false), (1, true)], [(0, false)], [(1, true), (0, false), (3, false)],
    [(1, true), (0, false)], [(0, false), (1, true)], [(0, false)], [(0, false)], [(0, false)],
    [(0, false)], [(1, false), (2, true), (0, true), (2, false)],
    [(2, false), (0, true), (2, true), (1, false)], [(2, false), (0, true)], [],
    [(0, true), (2, false)], [(0, true)], [(0, true)], [], [],
    [(2, false), (3, true), (1, true), (0, false), (3, false)],
    [(0, false), (3, false), (1, true), (3, true), (2, false)],
    [(0, false), (3, false), (1, true)], [(0, false)], [(1, true), (0, false), (3, false)],
    [(1, true), (0, false)], [(0, false), (1, true)], [(0, false)], [(0, false)],
    [(1, false), (2, true), (0, true), (2, false)],
    [(2, false), (0, true), (2, true), (1, false)], [(2, false), (0, true)],
    [(0, true), (2, false)], [(0, true)], [],
    [(2, false), (3, true), (1, true), (0, false), (3, false)],
    [(0, false), (3, false), (1, true), (3, true), (2, false)],
    [(0, false), (3, false), (1, true)], [(1, true), (0, false), (3, false)],
    [(1, true), (0, false)], [(0, false)], [(1, false), (2, true), (0, true), (2, false)],
    [(2, false), (0, true), (2, true), (1, false)], [(0, true), (2, false)],
    [(2, false), (3, true), (1, true), (0, false), (3, false)],
    [(0, false), (3, false), (1, true), (3, true), (2, false)],
    [(1, true), (0, false), (3, false)], [(1, false), (2, true), (0, true), (2, false)],
    [(2, false), (3, true), (1, true), (0, false), (3, false)]]

@[expose] def cert3 : Fin 120 → List (ℕ × Bool) :=
  ![[], [(0, false)], [(0, false)], [], [], [(0, false), (1, false)], [(0, false)],
    [(0, false)], [(0, false), (1, false)], [(0, false)], [(0, false)], [], [(0, true)], [],
    [(0, false), (1, false), (2, false)], [(0, false), (1, false)], [(1, false), (0, false)],
    [(0, false)], [(0, false), (1, true)], [(0, false)], [(0, false), (1, false)],
    [(1, false), (0, false)], [(0, false)], [(0, false), (1, true)], [(0, false)], [],
    [(2, false), (0, true)], [(0, true)], [], [(0, false), (1, false), (2, false)],
    [(2, false), (1, false), (0, false)], [(0, false), (1, false)],
    [(0, false), (1, false), (2, true)], [(1, false), (0, false)], [(0, false)],
    [(0, false), (3, false), (1, true)], [(1, true), (0, false)], [(0, false)],
    [(0, false), (1, false)], [(0, false), (1, false), (2, true)], [(1, false), (0, false)],
    [(0, false)], [(0, false), (3, false), (1, true)], [(1, true), (0, false)], [(0, false)],
    [(3, false), (2, false), (0, true)], [(2, false), (0, true), (2, true), (1, false)],
    [(0, true), (2, false)], [], [(0, false), (1, false), (2, false)],
    [(0, false), (1, false), (2, false), (3, true)], [(2, false), (1, false), (0, false)],
    [(0, false), (1, false)], [(0, false), (1, false), (4, false), (2, true)],
    [(2, true), (1, false), (0, false)], [(1, false), (0, false)],
    [(0, false), (4, false), (3, false), (1, true)],
    [(0, false), (3, false), (1, true), (3, true), (2, false)],
    [(1, true), (0, false), (3, false)], [(0, false)], [(0, false), (1, false)],
    [(0, false), (1, false), (4, false), (2, true)], [(2, true), (1, false), (0, false)],
    [(1, false), (0, false)], [(0, false), (4, false), (3, false), (1, true)],
    [(0, false), (3, false), (1, true), (3, true), (2, false)],
    [(1, true), (0, false), (3, false)], [(0, false)],
    [(3, false), (2, false), (4, false), (0, true), (2, true), (1, false)],
    [(1, false), (2, true), (0, true), (2, false)], [(0, true), (2, false), (3, false)],
    [(0, false), (1, false), (2, false)],
    [(0, false), (1, false), (2, false), (5, false), (3, true)],
    [(3, true), (2, false), (1, false), (0, false)], [(2, false), (1, false), (0, false)],
    [(0, false), (1, false), (5, false), (4, false), (2, true)],
    [(0, false), (1, false), (4, false), (2, true), (4, true), (3, false)],
    [(2, true), (1, false), (0, false), (4, false)], [(1, false), (0, false)],
    [(0, false), (4, false), (3, false), (5, false), (1, true), (3, true), (2, false)],
    [(2, false), (3, true), (1, true), (0, false), (3, false)],
    [(1, true), (0, false), (3, false), (4, false)],
    [(0, false), (1, false), (5, false), (4, false), (2, true)],
    [(0, false), (1, false), (4, false), (2, true), (4, true), (3, false)],
    [(2, true), (1, false), (0, false), (4, false)], [(1, false), (0, false)],
    [(0, false), (4, false), (3, false), (5, false), (1, true), (3, true), (2, false)],
    [(2, false), (3, true), (1, true), (0, false), (3, false)],
    [(1, true), (0, false), (3, false), (4, false)],
    [(3, false), (2, false), (4, false), (0, true), (2, true), (1, false), (4, true),
      (3, false), (2, false)],
    [(1, false), (2, true), (4, false), (0, true), (2, false), (3, false)],
    [(0, false), (1, false), (2, false), (6, false), (5, false), (3, true)],
    [(0, false), (1, false), (2, false), (5, false), (3, true), (5, true), (4, false)],
    [(3, true), (2, false), (1, false), (0, false), (5, false)],
    [(2, false), (1, false), (0, false)],
    [(0, false), (1, false), (5, false), (4, false), (6, false), (2, true), (4, true),
      (3, false)],
    [(3, false), (4, true), (2, true), (1, false), (0, false), (4, false)],
    [(2, true), (1, false), (0, false), (4, false), (5, false)],
    [(0, false), (4, false), (3, false), (5, false), (1, true), (3, true), (2, false),
      (5, true), (4, false), (3, false)],
    [(2, false), (3, true), (5, false), (1, true), (0, false), (3, false), (4, false)],
    [(0, false), (1, false), (5, false), (4, false), (6, false), (2, true), (4, true),
      (3, false)],
    [(3, false), (4, true), (2, true), (1, false), (0, false), (4, false)],
    [(2, true), (1, false), (0, false), (4, false), (5, false)],
    [(0, false), (4, false), (3, false), (5, false), (1, true), (3, true), (2, false),
      (5, true), (4, false), (3, false)],
    [(2, false), (3, true), (5, false), (1, true), (0, false), (3, false), (4, false)],
    [(2, false), (1, false), (3, false), (4, true), (2, true), (4, false), (0, true),
      (2, false), (3, false)],
    [(0, false), (1, false), (2, false), (6, false), (5, false), (7, false), (3, true),
      (5, true), (4, false)],
    [(4, false), (5, true), (3, true), (2, false), (1, false), (0, false), (5, false)],
    [(3, true), (2, false), (1, false), (0, false), (5, false), (6, false)],
    [(0, false), (1, false), (5, false), (4, false), (6, false), (2, true), (4, true),
      (3, false), (6, true), (5, false), (4, false)],
    [(3, false), (4, true), (6, false), (2, true), (1, false), (0, false), (4, false),
      (5, false)],
    [(3, false), (2, false), (4, false), (5, true), (3, true), (5, false), (1, true),
      (0, false), (3, false), (4, false)],
    [(0, false), (1, false), (5, false), (4, false), (6, false), (2, true), (4, true),
      (3, false), (6, true), (5, false), (4, false)],
    [(3, false), (4, true), (6, false), (2, true), (1, false), (0, false), (4, false),
      (5, false)],
    [(3, false), (2, false), (4, false), (5, true), (3, true), (5, false), (1, true),
      (0, false), (3, false), (4, false)],
    [(0, false), (1, false), (2, false), (6, false), (5, false), (7, false), (3, true),
      (5, true), (4, false), (7, true), (6, false), (5, false)],
    [(4, false), (5, true), (7, false), (3, true), (2, false), (1, false), (0, false),
      (5, false), (6, false)],
    [(4, false), (3, false), (5, false), (6, true), (4, true), (6, false), (2, true),
      (1, false), (0, false), (4, false), (5, false)],
    [(4, false), (3, false), (5, false), (6, true), (4, true), (6, false), (2, true),
      (1, false), (0, false), (4, false), (5, false)],
    [(5, false), (4, false), (6, false), (7, true), (5, true), (7, false), (3, true),
      (2, false), (1, false), (0, false), (5, false), (6, false)]]

@[expose] def certT (s : Fin 4) : Fin 120 → List (ℕ × Bool) := ![cert0, cert1, cert2, cert3] s

@[expose] def IsAsc (s : Fin 4) (k : Fin 120) : Prop :=
  (canW (mulTab s k)).length = (canW k).length + 1

instance (s : Fin 4) (k : Fin 120) : Decidable (IsAsc s k) := by
  unfold IsAsc
  infer_instance

theorem cert_spec : ∀ (s : Fin 4) (k : Fin 120),
    (IsAsc s k ∧ applyMoves (s :: canW k) (certT s k) = some (canW (mulTab s k))) ∨
      (¬IsAsc s k ∧ (canW k).length = (canW (mulTab s k)).length + 1 ∧
        applyMoves (canW k) (certT s k) = some (s :: canW (mulTab s k))) := by
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G5 V)

@[expose] def evT (l : List (Fin 4)) : V →ₗ[ZMod 2] V :=
  l.foldr (fun s f => Th ρ s ∘ₗ f) LinearMap.id

theorem evT_nil (x : V) : evT ρ [] x = x := rfl

theorem evT_cons (s : Fin 4) (l : List (Fin 4)) (x : V) :
    evT ρ (s :: l) x = Th ρ s (evT ρ l x) := rfl

theorem evT_append (l l' : List (Fin 4)) (x : V) : evT ρ (l ++ l') x = evT ρ l (evT ρ l' x) := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [List.cons_append, evT_cons, evT_cons, ih]

theorem evT_mem_fixU
    (l : List (Fin 4)) {x : V} (hx : x ∈ fixU ρ) : evT ρ l x ∈ fixU ρ := by
  induction l with
  | nil => exact hx
  | cons s l ih => rw [evT_cons]; exact Th_mem_fixU ρ s ih

theorem Th_braid'
    {a b : Fin 4} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) {x : V}
    (hx : x ∈ fixU ρ) : Th ρ a (Th ρ b (Th ρ a x)) = Th ρ b (Th ρ a (Th ρ b x)) := by
  rcases hab with h | h <;> fin_cases a <;> fin_cases b <;> simp at h <;>
    first
      | exact Th_braid ρ 0 hx | exact Th_braid ρ 1 hx | exact Th_braid ρ 2 hx
      | exact (Th_braid ρ 0 hx).symm | exact (Th_braid ρ 1 hx).symm
      | exact (Th_braid ρ 2 hx).symm

theorem evT_applyMove
    {l l' : List (Fin 4)} {m : ℕ × Bool} (h : applyMove l m = some l')
    {x : V} (hx : x ∈ fixU ρ) : evT ρ l x = evT ρ l' x := by
  obtain ⟨p, c⟩ := m
  have hl : evT ρ l x = evT ρ (l.take p ++ l.drop p) x := by rw [List.take_append_drop]
  cases c with
  | false =>
    simp only [applyMove] at h
    split at h
    · rename_i a b r hd
      split_ifs at h with hab
      cases h
      rw [hl, hd, evT_append, evT_append, evT_cons, evT_cons, evT_cons, evT_cons,
        Th_comm ρ hab]
    · exact absurd h (by simp)
  | true =>
    simp only [applyMove] at h
    split at h
    · rename_i a b c r hd
      split_ifs at h with habc
      cases h
      obtain ⟨rfl, hab⟩ := habc
      rw [hl, hd, evT_append, evT_append, evT_cons, evT_cons, evT_cons, evT_cons, evT_cons,
        evT_cons, Th_braid' ρ hab (evT_mem_fixU ρ r hx)]
    · exact absurd h (by simp)

theorem evT_applyMoves
    {l l' : List (Fin 4)} {ms : List (ℕ × Bool)}
    (h : applyMoves l ms = some l') {x : V} (hx : x ∈ fixU ρ) : evT ρ l x = evT ρ l' x := by
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

theorem Th_evT
    (s : Fin 4) (k : Fin 120) {x : V} (hx : x ∈ fixU ρ) :
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

theorem exists_eigen
    [Finite V] [Nontrivial V] :
    ∃ y ∈ fixU ρ, y ≠ 0 ∧ ∀ s : Fin 4, Th ρ s y = 0 ∨ Th ρ s y = y := by
  classical
  obtain ⟨x₀, hx₀, hx₀0⟩ := exists_fixU_ne ρ
  let S : Finset (Fin 120) := Finset.univ.filter fun k => ∃ x ∈ fixU ρ, evT ρ (canW k) x ≠ 0
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

theorem hW_eigen {y : V} (hy : ∀ s : Fin 4, Th ρ s y = 0 ∨ Th ρ s y = y) (l : List (Fin 4)) :
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

theorem fixU_eq
    {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) [Finite V] {y : V}
    (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) (heig : ∀ s : Fin 4, Th ρ s y = 0 ∨ Th ρ s y = y) {x : V}
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

end CFSG.Quasithin.JonesParshall.Curtis
