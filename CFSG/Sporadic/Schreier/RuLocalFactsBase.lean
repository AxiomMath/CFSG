
module

public import CFSG.Sporadic.Schreier.RuDefs

@[expose] public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem permOfArr_eq_of_eqA {n : ℕ} {a t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ha : isInvA n a (invCand n a) = true) (ht : Rep n t g) (h : eqA n a t = true) :
    permOfArr n a = g :=
  eq_of_eqA (rep_permOfArr ha).1 ht h

theorem closure_hom_mem {G M : Type*} [Group G] [Group M] {H : Subgroup G}
    (f : H →* M) {X : Set G} (hX : X ⊆ H) :
    ∀ g ∈ Subgroup.closure X, ∀ hgH : g ∈ H,
      f ⟨g, hgH⟩ ∈ Subgroup.closure (Set.range fun x : X => f ⟨x.1, hX x.2⟩) := by
  have hXH : Subgroup.closure X ≤ H := (Subgroup.closure_le H).2 hX
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact fun _ => Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩
  | one =>
    intro h1
    have e : (⟨1, h1⟩ : H) = 1 := rfl
    rw [e, map_one]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    intro hxy
    have e : (⟨x * y, hxy⟩ : H) = ⟨x, hXH hx⟩ * ⟨y, hXH hy⟩ := rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (ihx (hXH hx)) (ihy (hXH hy))
  | inv x hx ihx =>
    intro hxi
    have e : (⟨x⁻¹, hxi⟩ : H) = (⟨x, hXH hx⟩ : H)⁻¹ := rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ (ihx (hXH hx))

theorem map_subgroupOf_closure {G M : Type*} [Group G] [Group M] {H : Subgroup G}
    (f : H →* M) {X : Set G} (hX : X ⊆ H) :
    ((Subgroup.closure X).subgroupOf H).map f =
      Subgroup.closure (Set.range fun x : X => f ⟨x.1, hX x.2⟩) := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hgH⟩, hg, rfl⟩
    exact closure_hom_mem f hX g (Subgroup.mem_subgroupOf.1 hg) hgH
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x.1, hX x.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure x.2), rfl⟩

theorem range_closure {G M : Type*} [Group G] [Group M] {X : Set G}
    (f : Subgroup.closure X →* M) :
    f.range = Subgroup.closure (Set.range fun x : X => f ⟨x.1, Subgroup.subset_closure x.2⟩) := by
  have h := map_subgroupOf_closure f (X := X) (fun x hx => Subgroup.subset_closure hx)
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  exact h

theorem card_ker_mul_card_range {G M : Type*} [Group G] [Group M] (f : G →* M) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem injective_of_card_range {G M : Type*} [Group G] [Group M] [Finite G] (f : G →* M)
    (h : Nat.card f.range = Nat.card G) : Function.Injective f := by
  have hk := card_ker_mul_card_range f
  rw [h] at hk
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h1 : Nat.card f.ker = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (hk.trans (one_mul _).symm)
    exact this
  exact (MonoidHom.ker_eq_bot_iff f).1 (Subgroup.card_eq_one.1 h1)

theorem closure_list_eq {G : Type*} [Group G] (l : List G) :
    Subgroup.closure {g | g ∈ l} = Subgroup.closure {g | g ∈ l} := rfl

theorem setOf_mem_pair {G : Type*} (a b : G) : {g | g ∈ [a, b]} = ({a, b} : Set G) := by
  ext g
  simp

theorem getElem!_ofFn' {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem ruField4060_get {f j : ℕ} (hj : j < (ruLines4060.getD f (0, 0)).2) :
    (ruField4060 f)[j]! = ruArr4060 ((ruLines4060.getD f (0, 0)).1 + j) := by
  rw [ruField4060, getElem!_ofFn' _ hj]

end CFSG.Sporadic.RuSchreier
