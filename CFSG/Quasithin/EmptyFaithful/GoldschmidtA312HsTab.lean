module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open scoped Pointwise

section Tab

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_mul_toArray (x y : Γ) :
    (tab n (x * y)).toArray = compArr (tab n x).toArray (tab n y).toArray := by
  apply Array.ext'
  rw [compArr_toList, List.toList_toArray, List.toList_toArray, List.toList_toArray, tab_mul]

theorem eq_of_tab_eq {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {x y : Γ}
    (h : (tab n x).toArray = (tab n y).toArray) : x = y := by
  have h' : tab n x = tab n y := by simpa using congrArg Array.toList h
  have hxy : ∀ b, act n x b = act n y b := fun b => by
    unfold act
    rw [h']
  have h1 : x⁻¹ * y = 1 := by
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb), ← hxy b, ← act_mul _ _ (hB b hb), inv_mul_cancel, act_one (hB b hb)]
  calc x = x * (x⁻¹ * y) := by rw [h1, mul_one]
    _ = y := by group

end Tab

section Sound

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem explOK_sound (C : LatCtx Γ n Lab) {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {j : ℕ} (hj : j < C.J) {N : ℕ}
    {word : ℕ → List ℕ} {mulf : ℕ → ℕ → ℕ} {conj : List (List ℕ)}
    (h : ExplOK n (C.D.sTabs ++ C.D.mt[j]!) N word mulf conj) :
    ∃ x : ℕ → Γ, (∀ i < N, x i ∈ C.Y j) ∧ x 0 = 1 ∧ (∀ i < N, ∀ k < N, x i = x k → i = k) ∧
      (∀ i < N, ∀ k < N, mulf i k < N ∧ x i * x k = x (mulf i k)) ∧
      ∀ g ∈ C.sg ++ C.gens j, ∀ i < N, ∃ k < N, g * x i * g⁻¹ = x k := by
  have hL : C.D.sTabs ++ C.D.mt[j]! = genTabs n (C.sg ++ C.gens j) := (C.Y_letters hj).symm
  unfold ExplOK at h
  generalize hLL : C.D.sTabs ++ C.D.mt[j]! = L at hL h
  generalize hEE : C.sg ++ C.gens j = E at hL
  have hLlen : L.length = E.length := by rw [hL, genTabs_length]
  have hel : ∀ l < E.toArray.size, L.toArray.getD l #[] = (tab n (E.toArray.getD l 1)).toArray := by
    rw [hL]
    exact genTabs_hel E
  obtain ⟨hw0, hwl, hdist, hmul, hclen, hconj⟩ := h
  have hwE : ∀ i < N, ∀ l ∈ word i, l < E.toArray.size := fun i hi l hl => by
    have := hwl i hi l hl
    simpa [hLlen] using this
  let x : ℕ → Γ := fun i => evalElt E.toArray (word i)
  have hT : ∀ i < N, (explTabs n L N word)[i]! = (tab n (x i)).toArray := by
    intro i hi
    rw [← wordTabA_eq E.toArray L.toArray hel (word i) (hwE i hi)]
    simp [explTabs, hi]
  have hYE : ∀ g ∈ E, g ∈ C.Y j := fun g hg => by
    rw [← hEE] at hg
    exact Subgroup.subset_closure hg
  refine ⟨x, fun i hi => ?_, ?_, fun i hi k hk hik => ?_, fun i hi k hk => ?_, ?_⟩
  · refine evalElt_mem E.toArray (fun l hl => ?_) (word i) (hwE i hi)
    have hl' : l < E.length := by simpa using hl
    have : E.toArray.getD l 1 ∈ E := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hl)]
      simp
    exact hYE _ this
  · simp [x, hw0, evalElt_nil]
  · by_contra hne
    apply hdist i hi k hk hne
    rw [hT i hi, hT k hk, hik]
  · obtain ⟨hlt, heq⟩ := hmul i hi k hk
    refine ⟨hlt, eq_of_tab_eq hB hbase ?_⟩
    rw [tab_mul_toArray, ← hT i hi, ← hT k hk, heq, hT _ hlt]
  · intro g hg i hi
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨hclen', hc⟩ := hconj l (by omega)
    obtain ⟨hk, hceq⟩ := hc i hi
    refine ⟨(conj[l]!)[i]!, hk, ?_⟩
    have hLl : L[l]! = (tab n E[l]).toArray := by
      have h1 := hel l (by simpa using hl)
      have h2 : L.toArray.getD l #[] = L[l]! := by
        simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem!_eq_getElem?_getD]
        rfl
      have h3 : E.toArray.getD l 1 = E[l] := by
        simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hl]
      rw [← h2, h1, h3]
    have h1 : E[l] * x i = x ((conj[l]!)[i]!) * E[l] := by
      refine eq_of_tab_eq hB hbase ?_
      rw [tab_mul_toArray, tab_mul_toArray, ← hLl, ← hT i hi, ← hT _ hk, hceq]
    calc E[l] * x i * (E[l])⁻¹ = x ((conj[l]!)[i]!) * E[l] * (E[l])⁻¹ := by rw [h1]
      _ = x ((conj[l]!)[i]!) := by group

end Sound

section Group

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem tab_group {N : ℕ} {mulf : ℕ → ℕ → ℕ} {x : ℕ → Γ} (hN : 0 < N) (h0 : x 0 = 1)
    (hinj : ∀ i < N, ∀ k < N, x i = x k → i = k)
    (hmul : ∀ i < N, ∀ k < N, mulf i k < N ∧ x i * x k = x (mulf i k)) :
    ∃ (V : Subgroup Γ) (idx : Fin N ≃ V), (∀ i, ((idx i : V) : Γ) = x i) ∧
      ∀ (i k : Fin N) (hik : mulf i k < N), idx ⟨mulf i k, hik⟩ = idx i * idx k := by
  let S : Set Γ := {g | ∃ i < N, x i = g}
  have hS2 : S * S = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, ⟨i, hi, rfl⟩, b, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨mulf i k, (hmul i hi k hk).1, ((hmul i hi k hk).2).symm⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ⟨x i, ⟨i, hi, rfl⟩, x 0, ⟨0, hN, rfl⟩, by simp [h0]⟩
  let V : Subgroup Γ := subgroupOfIdempotent S ⟨x 0, 0, hN, rfl⟩ hS2
  have hV : ∀ g, g ∈ V ↔ ∃ i < N, x i = g := fun g => Iff.rfl
  let f : Fin N → V := fun i => ⟨x i, (hV _).mpr ⟨i, i.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i k hik
      exact Fin.ext (hinj i i.2 k k.2 (congrArg Subtype.val hik))
    · rintro ⟨g, hg⟩
      obtain ⟨i, hi, rfl⟩ := (hV g).mp hg
      exact ⟨⟨i, hi⟩, rfl⟩
  refine ⟨V, Equiv.ofBijective f hf, fun i => rfl, fun i k hik => ?_⟩
  exact Subtype.ext ((hmul i i.2 k k.2).2).symm

end Group

end CFSG.Quasithin.A312Hs
