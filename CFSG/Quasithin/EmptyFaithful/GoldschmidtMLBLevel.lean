module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA
open CFSG.QuasithinUnique.Setup.X6

variable {G : Type} [Group G]

structure LieLevel (L S₀ : Subgroup G) (P : Fin 2 → Subgroup G) : Prop where
  le_L : ∀ j, P j ≤ L
  S_le : ∀ j, S₀ ≤ P j
  ne : P 0 ≠ P 1
  ne_L : ∀ j, P j ≠ L
  cover : ∀ A : Subgroup G, S₀ ≤ A → A ≤ L → A ≠ L → A ≤ P 0 ∨ A ≤ P 1
  maxl : ∀ (j : Fin 2) (A : Subgroup G), P j ≤ A → A ≤ L → A = P j ∨ A = L
  solv01 : Group.IsSolvable ↥(P 0 ⊓ P 1)
  nonsolv : ∀ A : Subgroup G, S₀ ≤ A → A ≤ L → A ≠ L → ¬ Group.IsSolvable ↥A →
    ∃ j, (∀ k, A ≤ P k ↔ k = j) ∧ perfectCore (P j) ≤ A
  norm_le : ∀ j, L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P j
  solv : ∀ A : Subgroup G, S₀ ≤ A → A ≤ L → Group.IsSolvable ↥A →
    A ≤ Subgroup.normalizer (S₀ : Set G)
  charTwo : ∀ j, CharTwo (P j)
  split : ∀ j, ∀ g ∈ P j, ∃ a ∈ perfectCore (P j), ∃ c ∈ leviCent (P j), g = a * c
  hall : ∀ j, ∀ x ∈ leviCent (P j), ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ pCoreOf 2 (P j)

section Frattini

variable [Finite G]

theorem isSylowTwoOf_of_le_of_le {S M L : Subgroup G} (hS : IsSylowTwoOf S L) (hSM : S ≤ M)
    (hML : M ≤ L) : IsSylowTwoOf S M := by
  have h := CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hS
  exact CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mpr
    ⟨hSM, h.2.1, fun R hRM hR hSR => h.2.2 R (hRM.trans hML) hR hSR⟩

theorem frattini {X MZ L S₀ : Subgroup G} (hMZX : MZ ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hS₀ : IsSylowTwoOf S₀ L) (hS₀M : S₀ ≤ MZ)
    {m : G} (hm : m ∈ MZ) :
    ∃ l ∈ MZ ⊓ L, ∃ n ∈ MZ ⊓ Subgroup.normalizer (S₀ : Set G), m = l * n := by
  have hmL : m ∈ Subgroup.normalizer (L : Set G) := hXL (hMZX hm)
  have hmM : m ∈ Subgroup.normalizer ((MZ ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hm) hmL
  have hS₀M' : IsSylowTwoOf S₀ (MZ ⊓ L) :=
    isSylowTwoOf_of_le_of_le hS₀ (le_inf hS₀M hS₀.1) inf_le_right
  have hS₁ : IsSylowTwoOf (conjByElt m S₀) (MZ ⊓ L) := by
    have h := isSylowOf_map_injective (p := 2) (MulAut.conj m).toMonoidHom
      (MulAut.conj m).injective (isSylowTwoOf_iff_isSylowOf.1 hS₀M')
    rw [show (MZ ⊓ L).map (MulAut.conj m).toMonoidHom = MZ ⊓ L from
      conjByElt_eq_of_mem_normalizer hmM] at h
    exact isSylowTwoOf_iff_isSylowOf.2 h
  obtain ⟨k, hkM, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hS₀M') (isSylowTwoOf_iff_isSylowOf.1 hS₁)
  refine ⟨k, hkM, k⁻¹ * m, ⟨MZ.mul_mem (MZ.inv_mem hkM.1) hm, ?_⟩, by group⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  have h1 := hk (m * x * m⁻¹)
  rw [mem_conjByElt, show m⁻¹ * (m * x * m⁻¹) * m = x by group] at h1
  rw [h1]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

end Frattini

section Swap

theorem conj_maximal {L S₀ P : Subgroup G} {n : G} (hnL : n ∈ Subgroup.normalizer (L : Set G))
    (hnS : n ∈ Subgroup.normalizer (S₀ : Set G)) (hPL : P ≤ L) (hSP : S₀ ≤ P)
    (hmax : ∀ A : Subgroup G, P ≤ A → A ≤ L → A = P ∨ A = L) :
    conjByElt n P ≤ L ∧ S₀ ≤ conjByElt n P ∧
      ∀ A : Subgroup G, conjByElt n P ≤ A → A ≤ L → A = conjByElt n P ∨ A = L := by
  have hn' : n⁻¹ ∈ Subgroup.normalizer (L : Set G) := (Subgroup.normalizer _).inv_mem hnL
  have hnS' : n⁻¹ ∈ Subgroup.normalizer (S₀ : Set G) := (Subgroup.normalizer _).inv_mem hnS
  have hconjL : conjByElt n L = L := conjByElt_eq_of_mem_normalizer hnL
  have hback : ∀ K : Subgroup G, conjByElt n⁻¹ (conjByElt n K) = K := fun K => by
    rw [← conjByElt_mul', inv_mul_cancel, conjByElt_one']
  refine ⟨?_, ?_, fun A hPA hAL => ?_⟩
  · rw [← hconjL]
    exact Subgroup.map_mono hPL
  · intro x hx
    rw [mem_conjByElt]
    have h := (Subgroup.mem_normalizer_iff.mp hnS' x).mp hx
    rw [inv_inv] at h
    exact hSP h
  · have hback' : ∀ K : Subgroup G, conjByElt n (conjByElt n⁻¹ K) = K := fun K => by
      rw [← conjByElt_mul', mul_inv_cancel, conjByElt_one']
    have h1 : P ≤ conjByElt n⁻¹ A := by
      intro x hx
      rw [mem_conjByElt]
      have hx' : n⁻¹⁻¹ * x * n⁻¹ ∈ conjByElt n P := by
        rw [mem_conjByElt, show n⁻¹ * (n⁻¹⁻¹ * x * n⁻¹) * n = x by group]
        exact hx
      exact hPA hx'
    have h2 : conjByElt n⁻¹ A ≤ L := by
      rw [← conjByElt_eq_of_mem_normalizer hn']
      exact Subgroup.map_mono hAL
    rcases hmax _ h1 h2 with h | h
    · left
      calc A = conjByElt n (conjByElt n⁻¹ A) := (hback' A).symm
        _ = conjByElt n P := by rw [h]
    · right
      calc A = conjByElt n (conjByElt n⁻¹ A) := (hback' A).symm
        _ = conjByElt n L := by rw [h]
        _ = L := hconjL

theorem inf_eq_of_ne (P : Fin 2 → Subgroup G) {j k : Fin 2} (h : k ≠ j) :
    P j ⊓ P k = P 0 ⊓ P 1 := by
  fin_cases j <;> fin_cases k <;> first | exact absurd rfl h | rfl | exact inf_comm _ _

theorem mem_normalizer_of_nonsolvable {X MZ L S₀ : Subgroup G} {P : Fin 2 → Subgroup G}
    (hlie : LieLevel L S₀ P) (hMZX : MZ ≤ X) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    {j : Fin 2} (hMj : MZ ⊓ L ≤ P j) (hns : ¬ Group.IsSolvable ↥(MZ ⊓ L)) {n : G}
    (hn : n ∈ MZ ⊓ Subgroup.normalizer (S₀ : Set G)) :
    n ∈ Subgroup.normalizer (P j : Set G) := by
  have hnL : n ∈ Subgroup.normalizer (L : Set G) := hXL (hMZX hn.1)
  have hnM : n ∈ Subgroup.normalizer ((MZ ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hn.1) hnL
  obtain ⟨hP'L, hSP', hmax'⟩ := conj_maximal hnL hn.2 (hlie.le_L j) (hlie.S_le j) (hlie.maxl j)
  have hback : ∀ K : Subgroup G, conjByElt n⁻¹ (conjByElt n K) = K := fun K => by
    rw [← conjByElt_mul', inv_mul_cancel, conjByElt_one']
  have hP'ne : conjByElt n (P j) ≠ L := by
    intro h
    apply hlie.ne_L j
    calc P j = conjByElt n⁻¹ (conjByElt n (P j)) := (hback _).symm
      _ = conjByElt n⁻¹ L := by rw [h]
      _ = L := conjByElt_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hnL)
  obtain ⟨k, hk⟩ : ∃ k, conjByElt n (P j) ≤ P k := by
    rcases hlie.cover _ hSP' hP'L hP'ne with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hPk : conjByElt n (P j) = P k := by
    rcases hmax' (P k) hk (hlie.le_L k) with h | h
    · exact h.symm
    · exact absurd h (hlie.ne_L k)
  by_cases hkj : k = j
  · subst hkj
    exact mem_normalizer_of_conjByElt_eq hPk
  · exfalso
    apply hns
    have hMk : MZ ⊓ L ≤ P k := by
      intro x hx
      rw [← hPk, mem_conjByElt]
      have h1 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer _).inv_mem hnM) x).mp hx
      rw [inv_inv] at h1
      exact hMj h1
    have hle : MZ ⊓ L ≤ P 0 ⊓ P 1 := by
      rw [← inf_eq_of_ne P hkj]
      exact le_inf hMj hMk
    have := hlie.solv01
    exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.inclusion hle))
      (Subgroup.inclusion_injective hle)

end Swap

end CFSG.Quasithin.GoldMLB
