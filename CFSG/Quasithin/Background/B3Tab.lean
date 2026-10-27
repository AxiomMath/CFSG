module

public import CFSG.Quasithin.Background.B3Sec
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.B3

abbrev Gp (n : ℕ) : Type := Equiv.Perm (Fin n)

abbrev Tab : Type := List ℕ

@[expose] def tab {n : ℕ} (σ : Gp n) : Tab := List.ofFn (fun i : Fin n => (σ i : ℕ))

@[expose] def idT (n : ℕ) : Tab := List.range n

@[expose] def mulT (a b : Tab) : Tab := b.map (fun j => a.getD j 0)

@[expose] def invT (a : Tab) : Tab := (List.range a.length).map (fun j => a.idxOf j)

@[expose] def cjT (g x : Tab) : Tab := mulT (mulT g x) (invT g)

@[expose] def isTab (n : ℕ) (t : Tab) : Bool :=
  t.length == n && t.all (fun x => decide (x < n)) && decide t.Nodup

section tabLemmas

variable {n : ℕ}

theorem length_tab (σ : Gp n) : (tab σ).length = n := by simp [tab]

theorem getElem_tab (σ : Gp n) (i : ℕ) (h : i < (tab σ).length) :
    (tab σ)[i] = (σ ⟨i, by simpa [length_tab] using h⟩ : ℕ) := by
  simp [tab]

theorem getD_tab (σ : Gp n) (i : Fin n) : (tab σ).getD i 0 = (σ i : ℕ) := by
  rw [List.getD_eq_getElem _ _ (by simp [length_tab])]
  simp [tab]

theorem tab_mul (σ τ : Gp n) : tab (σ * τ) = mulT (tab σ) (tab τ) := by
  simp only [mulT, tab, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, Equiv.Perm.coe_mul]
  have := getD_tab σ (τ i)
  simp

theorem tab_one : tab (1 : Gp n) = idT n := by
  simp [tab, idT, List.ofFn_eq_map]

theorem nodup_tab (σ : Gp n) : (tab σ).Nodup := by
  unfold tab
  rw [List.nodup_ofFn]
  intro i j h
  exact σ.injective (Fin.ext h)

theorem tab_inv (σ : Gp n) : tab σ⁻¹ = invT (tab σ) := by
  apply List.ext_getElem
  · simp [invT, length_tab]
  · intro j h1 h2
    have hj : j < n := by simpa [length_tab] using h1
    rw [getElem_tab]
    simp only [invT, List.getElem_map, List.getElem_range]
    have h3 := (nodup_tab σ).idxOf_getElem (σ⁻¹ ⟨j, hj⟩ : ℕ) (by simp [length_tab])
    rw [getElem_tab] at h3
    simpa using h3.symm

theorem tab_injective : Function.Injective (tab : Gp n → Tab) := by
  intro σ τ h
  ext i
  have := congrArg (fun l => l.getD i 0) h
  simp only [getD_tab] at this
  exact this

theorem isTab_tab (σ : Gp n) : isTab n (tab σ) = true := by
  simp only [isTab, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    length_tab, true_and]
  refine ⟨?_, nodup_tab σ⟩
  intro x hx
  simp only [tab, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (σ i).isLt

theorem exists_tab_eq {t : Tab} (h : isTab n t = true) : ∃ σ : Gp n, tab σ = t := by
  simp only [isTab, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hlt⟩, hnd⟩ := h
  let f : Fin n → Fin n := fun i => ⟨t[i.val]'(by omega), hlt _ (List.getElem_mem _)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : t[i.val]'(by omega) = t[j.val]'(by omega) := congrArg Fin.val hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h1)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), ?_⟩
  apply List.ext_getElem
  · simp [tab, hlen]
  · intro i h1 h2
    simp [tab, f]

theorem tab_getElem_lt (σ : Gp n) (i : ℕ) (h : i < (tab σ).length) : (tab σ)[i] < n := by
  rw [getElem_tab]
  exact (σ _).isLt

end tabLemmas

@[expose] def subOK (n : ℕ) (S : List Tab) : Bool :=
  S.all (isTab n) && S.contains (idT n) &&
    S.all (fun a => S.all (fun b => S.contains (mulT a b))) &&
    S.all (fun a => S.contains (invT a)) && decide S.Nodup

theorem subOK_spec {n : ℕ} {S : List Tab} (h : subOK n S = true) :
    (∀ t ∈ S, isTab n t = true) ∧ idT n ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, mulT a b ∈ S) ∧
      (∀ a ∈ S, invT a ∈ S) ∧ S.Nodup := by
  simp only [subOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

noncomputable def subOf (n : ℕ) (S : List Tab) : Subgroup (Gp n) :=
  if h : subOK n S = true then
    { carrier := {σ | tab σ ∈ S}
      one_mem' := by
        show tab 1 ∈ S
        rw [tab_one]
        exact (subOK_spec h).2.1
      mul_mem' := fun {a b} ha hb => by
        show tab (a * b) ∈ S
        rw [tab_mul]
        exact (subOK_spec h).2.2.1 _ ha _ hb
      inv_mem' := fun {a} ha => by
        show tab a⁻¹ ∈ S
        rw [tab_inv]
        exact (subOK_spec h).2.2.2.1 _ ha }
  else ⊥

theorem mem_subOf {n : ℕ} {S : List Tab} (h : subOK n S = true) {σ : Gp n} :
    σ ∈ subOf n S ↔ tab σ ∈ S := by
  unfold subOf
  simp only [h, ↓reduceDIte]
  exact Iff.rfl

theorem card_subOf {n : ℕ} {S : List Tab} (h : subOK n S = true) :
    Nat.card (subOf n S) = S.length := by
  classical
  obtain ⟨hT, -, -, -, hnd⟩ := subOK_spec h
  have h1 : Nat.card (subOf n S) = (Finset.univ.filter (fun σ : Gp n => tab σ ∈ S)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext σ
    simp [mem_subOf h]
  rw [h1, ← Finset.card_image_of_injective _ (tab_injective (n := n))]
  have h2 : (Finset.univ.filter (fun σ : Gp n => tab σ ∈ S)).image tab = S.toFinset := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact hσ
    · intro ht
      obtain ⟨σ, rfl⟩ := exists_tab_eq (hT t ht)
      exact ⟨σ, ht, rfl⟩
  rw [h2, List.toFinset_card_of_nodup hnd]

@[expose] def chainOK (gens : List Tab) (idt : Tab) : List Tab → List Tab → Bool
  | _, [] => true
  | done, x :: rest =>
      (x == idt || gens.any (fun g => done.any (fun y => mulT g y == x))) &&
        chainOK gens idt (x :: done) rest

theorem chain_sound {n : ℕ} (gensP : List (Gp n)) :
    ∀ (S done : List Tab), chainOK (gensP.map tab) (idT n) done S = true →
      (∀ y ∈ done, ∃ σ ∈ Subgroup.closure {g | g ∈ gensP}, tab σ = y) →
      ∀ x ∈ S, ∃ σ ∈ Subgroup.closure {g | g ∈ gensP}, tab σ = x := by
  intro S
  induction S with
  | nil => intro done _ _ x hx; simp at hx
  | cons a rest ih =>
    intro done hch hdone x hx
    simp only [chainOK, Bool.and_eq_true] at hch
    obtain ⟨ha, hrest⟩ := hch
    have hA : ∃ σ ∈ Subgroup.closure {g | g ∈ gensP}, tab σ = a := by
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at ha
      rcases ha with ha | ⟨g, hg, y, hy, hgy⟩
      · exact ⟨1, Subgroup.one_mem _, by rw [tab_one, ha]⟩
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        obtain ⟨τ, hτ, rfl⟩ := hdone y hy
        refine ⟨g0 * τ, Subgroup.mul_mem _ (Subgroup.subset_closure hg0) hτ, ?_⟩
        rw [tab_mul]
        simpa using hgy
    have hdone' : ∀ y ∈ a :: done, ∃ σ ∈ Subgroup.closure {g | g ∈ gensP}, tab σ = y := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hA
      · exact hdone y hy
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hA
    · exact ih (a :: done) hrest hdone' x hx

theorem closure_eq_subOf {n : ℕ} (gensP : List (Gp n)) (S : List Tab) (hS : subOK n S = true)
    (hg : gensP.all (fun g => S.contains (tab g)) = true)
    (hc : chainOK (gensP.map tab) (idT n) [] S = true) :
    Subgroup.closure {g | g ∈ gensP} = subOf n S := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg'
    rw [SetLike.mem_coe, mem_subOf hS]
    simp only [List.all_eq_true, List.contains_iff_mem] at hg
    exact hg g hg'
  · intro x hx
    rw [mem_subOf hS] at hx
    obtain ⟨σ, hσ, hσx⟩ := chain_sound gensP S [] hc (by simp) _ hx
    rwa [← tab_injective hσx]


end CFSG.Quasithin.B3
