module

public import CFSG.Certificates.PresentationLetters
public import CFSG.Certificates.OrbitChain
public import TauCeti.GroupTheory.Presentation.GroupPresentation

public section

namespace CFSG.Sporadic.Bridge

open CFSG.Certificates CFSG.Certificates.CosetEnumeration TauCeti

@[expose] def wordProd {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) : G :=
  (w.map fun l => if l.2 then x l.1 else (x l.1)⁻¹).prod

theorem wordProd_mem {G : Type*} [Group G] {K : Subgroup G} {x : ℕ → G} (hx : ∀ i, x i ∈ K)
    (w : List (ℕ × Bool)) : wordProd x w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    refine K.mul_mem ?_ ih
    split
    · exact hx _
    · exact K.inv_mem (hx _)

theorem map_wordProd {G H : Type*} [Group G] [Group H] (φ : G →* H) (x : ℕ → G)
    (w : List (ℕ × Bool)) : φ (wordProd x w) = wordProd (fun i => φ (x i)) w := by
  induction w with
  | nil => simp [wordProd]
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, ih]
    split <;> simp

theorem coe_wordProd {G : Type*} [Group G] {K : Subgroup G} (x : ℕ → K) (w : List (ℕ × Bool)) :
    ((wordProd x w : K) : G) = wordProd (fun i => (x i : G)) w :=
  map_wordProd K.subtype x w

theorem codes_relators (P : GroupPresentation) :
    codes P.relators =
      P.relatorLetters.map (List.map fun x => 2 * x.1 + if x.2 then 0 else 1) := by
  rw [GroupPresentation.relatorLetters_def, List.map_map]
  unfold codes
  apply List.map_congr_left
  intro w _
  rw [Function.comp_apply, List.map_map]
  rfl

theorem relators_mem (P : GroupPresentation) :
    ∀ w ∈ P.relators, FreeGroup.mk w ∈ P.relatorSet := by
  intro w hw
  rw [GroupPresentation.mem_relatorSet_iff]
  rw [GroupPresentation.relators_def, List.mem_map] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨t, ht, (Relator.toWord_toFreeGroup t).symm⟩

theorem lift_mk {G : Type*} [Group G] (P : GroupPresentation) (img : ℕ → G)
    (w : List (Fin P.generatorCount × Bool)) :
    FreeGroup.lift (fun i : Fin P.generatorCount => img i.val) (FreeGroup.mk w) =
      wordProd img (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [show FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, b⟩ := x
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte]
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]

theorem lift_relator {G : Type*} [Group G] (P : GroupPresentation) (img : ℕ → G)
    (h : ∀ v ∈ P.relatorLetters, wordProd img v = 1) :
    ∀ r ∈ P.relatorSet, FreeGroup.lift (fun i : Fin P.generatorCount => img i.val) r = 1 := by
  intro r hr
  rw [GroupPresentation.mem_relatorSet_iff] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  rw [← Relator.toWord_toFreeGroup, lift_mk]
  apply h
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def, List.map_map]
  exact List.mem_map_of_mem ht

noncomputable def presHom {G : Type*} [Group G] (P : GroupPresentation) (img : ℕ → G)
    (h : ∀ v ∈ P.relatorLetters, wordProd img v = 1) : P.Group →* G :=
  PresentedGroup.toGroup (lift_relator P img h)

noncomputable def presGen (P : GroupPresentation) (i : ℕ) : P.Group :=
  if h : i < P.generatorCount then PresentedGroup.of ⟨i, h⟩ else 1

theorem presHom_presGen {G : Type*} [Group G] (P : GroupPresentation) (img : ℕ → G)
    (h : ∀ v ∈ P.relatorLetters, wordProd img v = 1) {i : ℕ} (hi : i < P.generatorCount) :
    presHom P img h (presGen P i) = img i := by
  rw [presGen, dite_eq_left hi, presHom, PresentedGroup.toGroup.of]

theorem presHom_wordProd {G : Type*} [Group G] (P : GroupPresentation) (img : ℕ → G)
    (h : ∀ v ∈ P.relatorLetters, wordProd img v = 1) (w : List (ℕ × Bool))
    (hw : ∀ l ∈ w, l.1 < P.generatorCount) :
    presHom P img h (wordProd (presGen P) w) = wordProd img w := by
  rw [map_wordProd]
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih (fun l' hl' => hw l' (by simp [hl'])), presHom_presGen P img h (hw l (by simp))]

theorem nonempty_mulEquiv_of_surjective {P N : Type*} [Group P] [Group N] [Finite P]
    (φ : P →* N) (hφ : Function.Surjective φ) {k : ℕ} (hP : Nat.card P ≤ k)
    (hN : k ≤ Nat.card N) : Nonempty (N ≃* P) :=
  ⟨(MulEquiv.ofBijective φ (hφ.bijective_of_nat_card_le (le_trans hP hN))).symm⟩

theorem finite_card_le_of_zpowers {G : Type*} [Group G] (g : G) {k n : ℕ} (hk : 0 < k)
    (hg : g ^ k = 1) (hfin : (Subgroup.zpowers g).FiniteIndex)
    (hn : (Subgroup.zpowers g).index ≤ n) : Finite G ∧ Nat.card G ≤ n * k := by
  have hord : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hg
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hord hk
  have hfinz : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hcard : Nat.card (Subgroup.zpowers g) ≤ k := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd hk hord
  have hG : Finite G := by
    have : Finite (G ⧸ Subgroup.zpowers g) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (Subgroup.zpowers g)
  refine ⟨hG, ?_⟩
  rw [← (Subgroup.zpowers g).index_mul_card]
  exact Nat.mul_le_mul hn hcard

theorem le_card_of_witnesses {n : ℕ} {K : Subgroup (Equiv.Perm (Fin n))}
    (gen : ℕ → Equiv.Perm (Fin n)) (b : Fin n) (W : List (Fin n × List (ℕ × Bool)))
    (hmem : ∀ x ∈ W, wordProd gen x.2 ∈ K) (hmap : ∀ x ∈ W, wordProd gen x.2 b = x.1)
    (hnodup : (W.map Prod.fst).Nodup) :
    W.length * Nat.card ↥(K ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) b) ≤ Nat.card K := by
  have h := card_mul_card_inf_stabilizer_le K b (W.map Prod.fst).toFinset (by
    intro p hp
    rw [List.mem_toFinset, List.mem_map] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact ⟨wordProd gen x.2, hmem x hx, hmap x hx⟩)
  rwa [List.toFinset_card_of_nodup hnodup, List.length_map] at h

theorem mem_stabilizer_iff_apply {n : ℕ} {g : Equiv.Perm (Fin n)} {b : Fin n} :
    g ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) b ↔ g b = b := by
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

end CFSG.Sporadic.Bridge
