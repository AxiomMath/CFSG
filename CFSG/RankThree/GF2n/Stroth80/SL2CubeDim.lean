module

public import CFSG.RankThree.GF2n.Stroth80.SL2KDescent

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Descent

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Dim

variable {K F : Type*} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [CharP F 2]

theorem irr_dim_cases {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk1 : 1 ≤ k)
    (hF : Fintype.card F = 2 ^ (k * 3)) (κ : K →+* F) {X : Type*} [AddCommGroup X]
    [Module K X] [Finite X] (ρ : Representation K SL(2, F) X) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) :
    6 ≤ Module.finrank K X ∧
      (Module.finrank K X ≤ 8 → Module.finrank K X = 6 ∨ Module.finrank K X = 8) := by
  obtain ⟨f, J, hf1, -, hfn, hJne, hJn, hshift, hdim⟩ :=
    kDescent (ρ := ρ) hk (n := k * 3) (by omega) hF κ hnt
  have hf3 : f ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by omega) hfn
  have hcard : 1 ≤ J.card := Finset.card_pos.mpr hJne
  rcases (Nat.dvd_prime Nat.prime_three).mp hf3 with h1 | h3
  · subst h1
    have h3d : 3 ∣ J.card :=
      dvd_card_of_shift (k := k) (e := 3) (by omega) hJn (by simpa using hshift)
    rw [one_mul] at hdim
    obtain ⟨a, ha⟩ := h3d
    by_cases h : a = 1
    · subst h
      refine ⟨by rw [hdim, ha]; norm_num, fun _ => Or.inr (by rw [hdim, ha]; norm_num)⟩
    · have ha2 : 2 ≤ a := by omega
      have h8 : 2 ^ 6 ≤ 2 ^ J.card := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨by omega, fun h => by omega⟩
  · subst h3
    by_cases h : J.card = 1
    · refine ⟨by rw [hdim, h]; norm_num, fun _ => Or.inl (by rw [hdim, h]; norm_num)⟩
    · have h4 : 2 ^ 2 ≤ 2 ^ J.card := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨by omega, fun h => by omega⟩


end Dim

section Minimal

variable {G K X : Type*} [Monoid G] [Field K] [AddCommGroup X] [Module K X]

theorem exists_minimal_invariant [Module.Finite K X] (ρ : Representation K G X)
    (Y : Submodule K X) (hY : Y ≠ ⊥) (hYρ : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) :
    ∃ N ≤ Y, N ≠ ⊥ ∧ (∀ g, ∀ n ∈ N, ρ g n ∈ N) ∧
      ∀ N' ≤ N, (∀ g, ∀ n ∈ N', ρ g n ∈ N') → N' = ⊥ ∨ N' = N := by
  obtain ⟨Z, ⟨hZY, hZ0, hZρ⟩, hmin⟩ :=
    (InvImage.wf (fun Z : Submodule K X => Module.finrank K Z) wellFounded_lt).has_min
      {Z | Z ≤ Y ∧ Z ≠ ⊥ ∧ ∀ g, ∀ z ∈ Z, ρ g z ∈ Z} ⟨Y, le_rfl, hY, hYρ⟩
  refine ⟨Z, hZY, hZ0, hZρ, fun Z' hZ'Z hZ'ρ => ?_⟩
  by_cases h0 : Z' = ⊥
  · exact Or.inl h0
  · exact Or.inr (Submodule.eq_of_le_of_finrank_le hZ'Z
      (not_lt.mp (hmin Z' ⟨hZ'Z.trans hZY, h0, hZ'ρ⟩)))

@[expose] def subRep (ρ : Representation K G X) (N : Submodule K X) (hN : ∀ g, ∀ n ∈ N, ρ g n ∈ N) :
    Representation K G N :=
  ρ.subrepresentation N fun g n hn => hN g n hn

theorem subRep_apply (ρ : Representation K G X) (N : Submodule K X)
    (hN : ∀ g, ∀ n ∈ N, ρ g n ∈ N) (g : G) (n : N) : (subRep ρ N hN g n : X) = ρ g n := rfl

theorem subRep_irreducible (ρ : Representation K G X) (N : Submodule K X) (hN0 : N ≠ ⊥)
    (hN : ∀ g, ∀ n ∈ N, ρ g n ∈ N)
    (hmin : ∀ N' ≤ N, (∀ g, ∀ n ∈ N', ρ g n ∈ N') → N' = ⊥ ∨ N' = N) :
    (subRep ρ N hN).IsIrreducible := by
  refine (isIrreducible_iff _).mpr ⟨Submodule.nontrivial_iff_ne_bot.mpr hN0, fun U hU => ?_⟩
  have hinv : ∀ g, ∀ n ∈ U.map N.subtype, ρ g n ∈ U.map N.subtype := by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨subRep ρ N hN g u, hU g u hu, rfl⟩
  rcases hmin _ (Submodule.map_subtype_le N U) hinv with h | h
  · left
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [h, Submodule.map_bot]
  · right
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [h, Submodule.map_subtype_top]

end Minimal

section Dichotomy

variable {K F : Type*} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [CharP F 2]
  {X : Type*} [AddCommGroup X] [Module K X] [Finite X]

theorem minimal_dichotomy {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk1 : 1 ≤ k)
    (hF : Fintype.card F = 2 ^ (k * 3)) (κ : K →+* F) (ρ : Representation K SL(2, F) X)
    (N : Submodule K X) (hN0 : N ≠ ⊥) (hN : ∀ g, ∀ n ∈ N, ρ g n ∈ N)
    (hmin : ∀ N' ≤ N, (∀ g, ∀ n ∈ N', ρ g n ∈ N') → N' = ⊥ ∨ N' = N) :
    (∀ g, ∀ n ∈ N, ρ g n = n) ∨ (6 ≤ Module.finrank K N ∧
      (Module.finrank K N ≤ 8 → Module.finrank K N = 6 ∨ Module.finrank K N = 8)) := by
  by_cases htriv : ∀ g, ∀ n ∈ N, ρ g n = n
  · exact Or.inl htriv
  · right
    haveI : Fact (subRep ρ N hN).IsIrreducible := ⟨subRep_irreducible ρ N hN0 hN hmin⟩
    push Not at htriv
    obtain ⟨g, n, hn, hne⟩ := htriv
    have hnt : ∃ g, subRep ρ N hN g ≠ 1 := by
      refine ⟨g, fun h => hne ?_⟩
      have h1 := congrArg (fun r : Module.End K N => (r ⟨n, hn⟩ : X)) h
      simpa [subRep_apply] using h1
    exact irr_dim_cases hk hk1 hF κ (subRep ρ N hN) hnt

end Dichotomy

section Extension

open scoped commutatorElement

theorem trivial_of_extension {G K X : Type*} [Group G] [Field K] [AddCommGroup X] [Module K X]
    (hG : commutator G = ⊤) (ρ : Representation K G X) (X' : Submodule K X)
    (h1 : ∀ g, ∀ x ∈ X', ρ g x = x) (h2 : ∀ g x, ρ g x - x ∈ X') :
    ∀ g x, ρ g x = x := by
  obtain ⟨D, hD⟩ : ∃ D : G → Module.End K X, ∀ g, D g = ρ g - 1 :=
    ⟨fun g => ρ g - 1, fun _ => rfl⟩
  have hDapp : ∀ g x, D g x = ρ g x - x := by
    intro g x
    rw [hD, LinearMap.sub_apply, Module.End.one_apply]
  have hkill : ∀ g, ∀ x ∈ X', D g x = 0 := by
    intro g x hx
    rw [hDapp, h1 g x hx, sub_self]
  have hprod : ∀ g h : G, D g * D h = 0 := by
    intro g h
    ext x
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    exact hkill g (D h x) (by rw [hDapp]; exact h2 h x)
  have hDmul : ∀ x y : G, D (x * y) = D x + D y := by
    intro x y
    have hp : (ρ x - 1) * (ρ y - 1) = 0 := by
      rw [← hD, ← hD]
      exact hprod x y
    have e : ρ (x * y) - 1 = (ρ x - 1) * (ρ y - 1) + (ρ x - 1) + (ρ y - 1) := by
      rw [map_mul]
      noncomm_ring
    simp only [hD]
    rw [e, hp, zero_add]
  have hDone : D 1 = 0 := by
    rw [hD, map_one, sub_self]
  have hDinv : ∀ x : G, D x⁻¹ = -D x := by
    intro x
    have h := hDmul x⁻¹ x
    rw [inv_mul_cancel, hDone] at h
    exact add_eq_zero_iff_eq_neg.mp h.symm
  have hcomm_val : ∀ a b : G, D ⁅a, b⁆ = 0 := by
    intro a b
    rw [commutatorElement_def, hDmul, hDmul, hDmul, hDinv, hDinv]
    abel
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, ∀ g, g ∈ S ↔ D g = 0 :=
    ⟨{ carrier := {g | D g = 0}
       mul_mem' := fun {a b} ha hb => by
         show D (a * b) = 0
         rw [hDmul, show D a = 0 from ha, show D b = 0 from hb, add_zero]
       one_mem' := hDone
       inv_mem' := fun {a} ha => by
         show D a⁻¹ = 0
         rw [hDinv, show D a = 0 from ha, neg_zero] }, fun _ => Iff.rfl⟩
  have hcomm_le : commutator G ≤ S := by
    show ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ S
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [hS]
    exact hcomm_val a b
  rw [hG] at hcomm_le
  intro g x
  have hg : g ∈ S := hcomm_le (Subgroup.mem_top g)
  rw [hS, hD, sub_eq_zero] at hg
  rw [hg, Module.End.one_apply]

end Extension

section Small

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [CharP F 2]

theorem trivial_of_finrank_le {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk1 : 1 ≤ k)
    (hF : Fintype.card F = 2 ^ (k * 3)) (κ : K →+* F) (hG : commutator SL(2, F) = ⊤) :
    ∀ (d : ℕ), d ≤ 5 → ∀ (X : Type) [AddCommGroup X] [Module K X] [Module.Finite K X]
      (ρ : Representation K SL(2, F) X), Module.finrank K X ≤ d → ∀ g, ρ g = 1 := by
  intro d
  induction d with
  | zero =>
    intro _ X _ _ _ ρ hX g
    have : Subsingleton X := (Module.finrank_zero_iff (R := K) (M := X)).mp (by omega)
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  | succ d ih =>
    intro hd X _ _ _ ρ hX g
    by_cases hlt : Module.finrank K X ≤ d
    · exact ih (by omega) X ρ hlt g
    · haveI : Finite X := Module.finite_of_finite K
      have hX0 : (⊤ : Submodule K X) ≠ ⊥ := by
        intro h
        have h1 : Module.finrank K (⊤ : Submodule K X) = 0 := by rw [h, finrank_bot]
        rw [finrank_top] at h1
        omega
      obtain ⟨N, -, hN0, hN, hmin⟩ :=
        exists_minimal_invariant ρ ⊤ hX0 (fun _ _ _ => Submodule.mem_top)
      have hNtriv : ∀ g, ∀ n ∈ N, ρ g n = n := by
        rcases minimal_dichotomy hk hk1 hF κ ρ N hN0 hN hmin with h | ⟨h6, -⟩
        · exact h
        · exfalso
          have := Submodule.finrank_le N
          omega
      haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
      have hNpos : 0 < Module.finrank K N := Module.finrank_pos
      have hQ : Module.finrank K (X ⧸ N) ≤ d := by
        have := Submodule.finrank_quotient_add_finrank N
        omega
      let ρQ := ρ.quotient N (fun g n hn => hN g n hn)
      have hQtriv := ih (by omega) (X ⧸ N) ρQ hQ
      refine LinearMap.ext (trivial_of_extension hG ρ N hNtriv (fun g' x => ?_) g)
      have h1 := LinearMap.congr_fun (hQtriv g') (Submodule.Quotient.mk x)
      have h2 : Submodule.Quotient.mk (ρ g' x) = (Submodule.Quotient.mk x : X ⧸ N) := h1
      exact (Submodule.Quotient.eq N).mp h2

end Small

end CFSG.RankThree.GF2n.Stroth80.SL2Descent
