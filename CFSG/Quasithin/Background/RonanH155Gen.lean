module

public import CFSG.Quasithin.Background.RonanH155PG2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.RonanH143

@[expose] def specials155 : List (List PG2) :=
  [[⟨10, 5, 0⟩, ⟨6, 2, 0⟩, ⟨1, 2, 0⟩, ⟨0, 0, 1⟩],
    [⟨1, 5, 1⟩, ⟨1, 0, 1⟩, ⟨0, 5, 0⟩, ⟨0, 2, 0⟩],
    [⟨10, 0, 0⟩, ⟨6, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 2, 1⟩],
    [⟨4, 0, 0⟩, ⟨2, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 4, 1⟩],
    [⟨8, 0, 0⟩, ⟨6, 0, 0⟩, ⟨1, 0, 0⟩, ⟨0, 6, 1⟩],
    [⟨10, 0, 0⟩, ⟨1, 7, 1⟩, ⟨1, 2, 1⟩, ⟨0, 5, 0⟩],
    [⟨10, 2, 1⟩, ⟨1, 5, 1⟩, ⟨1, 2, 1⟩, ⟨0, 7, 0⟩]]

@[expose] def posTab155 : List ℕ :=
  [71, 0, 71, 71, 1, 2, 71, 71, 3, 4, 5, 71, 6, 7, 8, 71, 9, 10, 71, 71, 11, 12, 71, 71, 13, 14, 71, 15, 16, 17, 71, 18, 19, 71, 71, 71, 71, 71, 71, 71, 71, 20, 71, 71, 71, 71, 71, 71, 21, 71, 71, 71, 71, 71, 71, 71, 71, 22, 71, 71, 71, 71, 71, 71, 23, 71, 71, 71, 71, 71, 71, 71, 71, 24, 71, 71, 71, 71, 71, 71, 25, 71, 71, 71, 71, 71, 71, 71, 71, 26, 71, 71, 71, 71, 71, 71, 27, 28, 71, 71, 29, 30, 71, 71, 31, 32, 71, 33, 34, 35, 71, 36, 37, 38, 71, 71, 39, 40, 71, 71, 41, 42, 43, 71, 44, 45, 46, 71, 47, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 48, 71, 71, 49, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 50, 71, 71, 51, 71, 71, 71, 71, 52, 71, 71, 71, 71, 53, 54, 71, 71, 71, 71, 55, 71, 71, 71, 71, 56, 71, 71, 71, 71, 71, 71, 71, 71, 57, 58, 59, 71, 71, 71, 71, 60, 71, 71, 71, 71, 71, 71, 71, 71, 61, 62, 63, 71, 71, 71, 71, 64, 71, 71, 71, 71, 65, 66, 71, 71, 71, 71, 67, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 68, 71, 71, 69, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 70, 71, 71]

@[expose] def pg2Idx (x : PG2) : ℕ := (x.t.val * 8 + x.j.val) * 2 + x.ε.val

@[expose] def posF155 (x : PG2) : ℕ := posTab155.getD (pg2Idx x) 71

theorem posF155_eq : ∀ x : PG2, posF155 x = pos PG2.invs x := by decide +kernel

@[expose] def koL155 : List PG2 := (List.finRange 16).map fun t => ⟨t, 0, 0⟩

@[expose] def nq2L155 : List PG2 :=
  (List.finRange 32).map fun u =>
    ⟨nqKF ⟨u.val % 16, by omega⟩, nqJF ⟨u.val % 16, by omega⟩, ⟨u.val / 16, by omega⟩⟩

@[expose] def pred155 (l : List PG2) : Bool :=
  (subprods l).all (fun x => koL155.contains x) || (subprods l).all (fun x => nq2L155.contains x) ||
    specials155.contains l

theorem greedy155 : forallGreedyP posF155 PG2.invs pred155 4 [] = true := by decide +kernel

theorem toPerm_koL155 {s : PG2} (hs : s ∈ koL155) : PG2.toPerm s ∈ fixO := by
  simp only [koL155, List.mem_map, List.mem_finRange, true_and] at hs
  obtain ⟨t, rfl⟩ := hs
  refine (mem_fixO_iff _).2 ⟨t, ?_⟩
  show koPerm t * dPerm 0 * (if (0 : Fin 2) = 1 then ePerm else 1) = koPerm t
  rw [dPerm_zero]
  simp

theorem toPerm_nq2L : ∀ u : Fin 32, PG2.toPerm
    (⟨nqKF ⟨u.val % 16, by omega⟩, nqJF ⟨u.val % 16, by omega⟩, ⟨u.val / 16, by omega⟩⟩ : PG2) =
      nq2Perm u := by
  decide +kernel

theorem toPerm_nq2L155 {s : PG2} (hs : s ∈ nq2L155) : PG2.toPerm s ∈ NQ2 := by
  simp only [nq2L155, List.mem_map, List.mem_finRange, true_and] at hs
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u, toPerm_nq2L u⟩

theorem E16_P2_cases (A : Subgroup P24) (hA : A ≤ P2) (hE : IsE2k 4 A) :
    (∀ x : P24, x ∈ A → x ∈ fixO) ∨ (∀ x : P24, x ∈ A → x ∈ NQ2) ∨
      ∃ l ∈ specials155, ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s := by
  have hg : forallGreedy PG2.invs pred155 4 [] = true :=
    (forallGreedyP_eq posF155_eq pred155 4 []).symm.trans greedy155
  let A' : Subgroup PG2 := A.comap PG2.toPermHom
  have hmem : ∀ x : PG2, x ∈ A' ↔ PG2.toPerm x ∈ A := fun x => Iff.rfl
  have hcomm0 : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := hE.1.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hsq0 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact hE.1.2 a ha
  have hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
    PG2.toPerm_injective (by
      rw [PG2.toPerm_mul, PG2.toPerm_mul]
      exact hcomm0 _ ((hmem x).1 hx) _ ((hmem y).1 hy))
  have hsq : ∀ x ∈ A', x * x = 1 := fun x hx =>
    PG2.toPerm_injective (by
      rw [PG2.toPerm_mul, PG2.toPerm_one]
      exact hsq0 _ ((hmem x).1 hx))
  have hR : ∀ x ∈ A', x ≠ 1 → x ∈ PG2.invs := fun x hx hne => PG2.mem_invs hne (hsq x hx)
  have hcard : Nat.card A' = 2 ^ 4 := by
    have h1 : A'.map PG2.toPermHom = A := by
      apply Subgroup.map_comap_eq_self
      rw [PG2.range_toPermHom]
      exact hA
    have h2 : Nat.card ↥(A'.map PG2.toPermHom) = Nat.card ↥A' :=
      (Nat.card_congr (A'.equivMapOfInjective PG2.toPermHom PG2.toPerm_injective).toEquiv).symm
    rw [h1] at h2
    rw [← h2]
    exact hE.2
  obtain ⟨l, hlen, hind, hspan, hp⟩ := forallGreedy_sound hg A' hcomm hsq hR hcard
  have hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s := by
    intro x
    constructor
    · intro hx
      have hxr : x ∈ PG2.toPermHom.range := by
        rw [PG2.range_toPermHom]
        exact hA hx
      obtain ⟨s, hs⟩ := hxr
      refine ⟨s, (hspan s).1 ?_, hs.symm⟩
      rw [hmem]
      show PG2.toPerm s ∈ A
      have : PG2.toPerm s = x := hs
      rw [this]
      exact hx
    · rintro ⟨s, hs, rfl⟩
      exact (hmem s).1 ((hspan s).2 hs)
  simp only [pred155, Bool.or_eq_true, List.all_eq_true, List.contains_iff_mem] at hp
  rcases hp with (hp | hp) | hp
  · left
    intro x hx
    obtain ⟨s, hs, rfl⟩ := (hAeq x).1 hx
    exact toPerm_koL155 (hp s hs)
  · right
    left
    intro x hx
    obtain ⟨s, hs, rfl⟩ := (hAeq x).1 hx
    exact toPerm_nq2L155 (hp s hs)
  · right
    right
    exact ⟨l, hp, hAeq⟩

end CFSG.Quasithin.RonanH155
