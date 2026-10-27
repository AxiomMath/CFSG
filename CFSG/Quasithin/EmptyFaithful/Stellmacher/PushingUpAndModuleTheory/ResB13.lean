module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB2

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem OoOf_smul (g : ↥(H ⊔ M)) (v : Geo H M) : OoOf (g • v) = conjSub (g : G) (OoOf v) := by
  unfold OoOf
  rw [Qv_smul, stab_smul, pResidualOf_eq_oTwoRes, pResidualOf_eq_oTwoRes, ← conjSub_oTwoRes,
    conjSub_commutator]

@[expose] noncomputable def aZ (i j : Geo H M) : ℕ := (Zv i ⊓ Qv j).relIndex (Zv i)

omit [Finite G] in
theorem aZ_smul (g : ↥(H ⊔ M)) (i j : Geo H M) : aZ (g • i) (g • j) = aZ i j := by
  unfold aZ
  rw [Zv_smul, Qv_smul, ← conjSub_inf, relIndex_conjSub]

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem aZ_unif (hA : F53Amalgam H M S) (h : ConfR δ μ U) {i j i' j' : Geo H M}
    (hi : i ∈ nbrs μ) (hj : j ∈ nbrs μ) (hi' : i' ∈ nbrs μ) (hj' : j' ∈ nbrs μ)
    (hij : i ≠ j) (hij' : i' ≠ j') : aZ i j = aZ i' j' := by
  obtain ⟨g, -, hgi, hgj⟩ := h.two_transitive hA hi hj hi' hj' hij hij'
  rw [← hgi, ← hgj, aZ_smul]

theorem swap_of_not_Qv (hA : F53Amalgam H M S) (h : ConfR δ μ U) {n n' : Geo H M}
    (hn : n ∈ nbrs μ) (hn' : n' ∈ nbrs μ) (hnδ : n ≠ δ) (hn'δ : n' ≠ δ) (hnn' : n ≠ n')
    (hall : ∀ x ∈ nbrs μ, x = δ ∨ x = n ∨ x = n') {s : ↥(H ⊔ M)} (hsδ : (s : G) ∈ stab δ)
    (hsμ : (s : G) ∈ stab μ) (hsP : (s : G) ∉ Qv μ) : s • n = n' := by
  have hsδ' : s • δ = δ := smul_eq_of_mem_stab (g := s) hsδ
  have hne : ∀ x, x ≠ δ → s • x ≠ δ := fun x hx e => hx (smul_left_cancel s (e.trans hsδ'.symm))
  have hn1 : s • n = n ∨ s • n = n' := by
    rcases hall _ (smul_mem_nbrs hsμ hn) with e | e | e
    · exact absurd e (hne n hnδ)
    · exact Or.inl e
    · exact Or.inr e
  rcases hn1 with e | e
  · exfalso
    have e' : s • n' = n' := by
      rcases hall _ (smul_mem_nbrs hsμ hn') with e2 | e2 | e2
      · exact absurd e2 (hne n' hn'δ)
      · exact absurd (smul_left_cancel s (e2.trans e.symm)) (Ne.symm hnn')
      · exact e2
    exact hsP (mem_Qv_of_fix hA hsμ fun x hx => by
      rcases hall x hx with rfl | rfl | rfl
      exacts [hsδ', e, e'])
  · exact e

end ConfR

theorem commute_of_index_two {A B X X' Y Y' : Subgroup G}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hX : X ≤ A) (hX' : X' ≤ A) (hY : Y ≤ B) (hY' : Y' ≤ B)
    (hXi : X.relIndex A = 2) (hX'i : X'.relIndex A = 2) (hYi : Y.relIndex B = 2)
    (hY'i : Y'.relIndex B = 2) (hXX : X ≠ X') (hYY : Y ≠ Y')
    (hX'B : ∀ x ∈ X', ∀ b ∈ B, x * b = b * x) (hY'A : ∀ y ∈ Y', ∀ a ∈ A, y * a = a * y)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have key : ∀ {A X X' : Subgroup G}, X ≤ A → X' ≤ A → X.relIndex A = 2 → X'.relIndex A = 2 →
      X ≠ X' → A ≤ X ⊔ X' := by
    intro A X X' hX hX' hXi hX'i hne
    have hXs : X ⊔ X' ≤ A := sup_le hX hX'
    have hmul := Subgroup.relIndex_mul_relIndex X (X ⊔ X') A le_sup_left hXs
    rw [hXi] at hmul
    have hd : X.relIndex (X ⊔ X') ∣ 2 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exfalso
      have h2 : X' ≤ X := le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)
      have h3 := Subgroup.relIndex_mul_relIndex X' X A h2 hX
      rw [hX'i, hXi] at h3
      have h4 : X'.relIndex X = 1 := by omega
      exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h4) h2)
    · rw [h1] at hmul
      have : (X ⊔ X').relIndex A = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp this
  have hAs := key hX hX' hXi hX'i hXX
  have hBs := key hY hY' hYi hY'i hYY
  intro a ha b hb
  obtain ⟨x, hx, x', hx', rfl⟩ := mem_sup_of_commute (fun u hu v hv => hA u (hX hu) v (hX' hv)) (hAs ha)
  obtain ⟨y, hy, y', hy', rfl⟩ := mem_sup_of_commute (fun u hu v hv => hB u (hY hu) v (hY' hv)) (hBs hb)
  have hxA := hX hx
  have hx'A := hX' hx'
  have hyB := hY hy
  have hy'B := hY' hy'
  calc x * x' * (y * y') = x * (x' * y) * y' := by group
    _ = x * (y * x') * y' := by rw [hX'B x' hx' y hyB]
    _ = (x * y) * (x' * y') := by group
    _ = (y * x) * (x' * y') := by rw [hXY x hx y hy]
    _ = y * (x * x') * y' := by group
    _ = y * ((x * x') * y') := by group
    _ = y * (y' * (x * x')) := by rw [← hY'A y' hy' (x * x') (A.mul_mem hxA hx'A)]
    _ = y * y' * (x * x') := by group

end CFSG.Quasithin.F53
