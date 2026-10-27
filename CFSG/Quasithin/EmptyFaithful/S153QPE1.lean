module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.QP

open CFSG.QuasithinUnique

section FixedPoint

variable {K : Type*} [Group K]

theorem exists_centralizing_mem_sdiff [Finite K] {N M E : Subgroup K} (hMN : M ≤ N)
    (hcard : Nat.card N = 5 * Nat.card M) (hM2 : IsPGroup 2 M) (hE3 : IsPGroup 3 E)
    (hEN : ∀ e ∈ E, ∀ n ∈ N, e * n * e⁻¹ ∈ N) (hEM : ∀ e ∈ E, ∀ m ∈ M, e * m * e⁻¹ ∈ M) :
    ∃ n ∈ N, n ∉ M ∧ ∀ e ∈ E, e * n * e⁻¹ = n := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Type _ := ↥((N : Set K) \ (M : Set K))
  have hEM' : ∀ e ∈ E, ∀ m, e * m * e⁻¹ ∈ M ↔ m ∈ M := by
    intro e he m
    refine ⟨fun h => ?_, fun h => hEM e he m h⟩
    have h1 := hEM e⁻¹ (E.inv_mem he) _ h
    have e1 : e⁻¹ * (e * m * e⁻¹) * e⁻¹⁻¹ = m := by group
    rwa [e1] at h1
  let act : ↥E → X → X := fun e x =>
    ⟨e * (x : K) * (e : K)⁻¹, ⟨hEN e e.2 x x.2.1, fun h => x.2.2 ((hEM' e e.2 x).1 h)⟩⟩
  let _ : MulAction ↥E X :=
    { smul := act
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥E) : K) * (x : K) * ((1 : ↥E) : K)⁻¹ = x
        simp)
      mul_smul := fun e e' x => Subtype.ext (by
        show ((e * e' : ↥E) : K) * (x : K) * ((e * e' : ↥E) : K)⁻¹ =
          (e : K) * ((e' : K) * (x : K) * (e' : K)⁻¹) * (e : K)⁻¹
        simp [mul_assoc]) }
  have hmod := hE3.card_modEq_card_fixedPoints X
  have hX : Nat.card X = 4 * Nat.card M := by
    have h1 : Nat.card X = Set.ncard ((N : Set K) \ (M : Set K)) := Nat.card_coe_set_eq _
    have h2 : Set.ncard ((N : Set K) \ (M : Set K)) = Set.ncard (N : Set K) - Set.ncard (M : Set K) :=
      Set.ncard_sdiff (by exact_mod_cast hMN)
    have h3 : Set.ncard (N : Set K) = Nat.card N := (Nat.card_coe_set_eq _).symm
    have h4 : Set.ncard (M : Set K) = Nat.card M := (Nat.card_coe_set_eq _).symm
    rw [h1, h2, h3, h4, hcard]
    omega
  have h3 : ¬ 3 ∣ Nat.card X := by
    rw [hX]
    intro h
    obtain ⟨k, hk⟩ := hM2.exists_card_eq
    rw [hk] at h
    have : 3 ∣ 4 * 2 ^ k := h
    have h4 : 3 ∣ 2 ^ (k + 2) := by
      have e2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
      rw [e2]
      exact this
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h4) (by norm_num)
  have hfix : Nat.card (MulAction.fixedPoints ↥E X) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact h3 ((Nat.modEq_zero_iff_dvd).1 hmod)
  have hne : Nonempty (MulAction.fixedPoints ↥E X) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    exact hfix (Nat.card_of_isEmpty)
  obtain ⟨⟨x, hxX⟩, hxfix⟩ := hne
  refine ⟨x, hxX.1, hxX.2, fun e he => ?_⟩
  have := hxfix ⟨e, he⟩
  exact congrArg (fun y : X => (y : K)) this

end FixedPoint

section Conj

variable {X : Type*} [Group X] [Finite X]

theorem exists_conj_isSylowTwoOf {S₁ S₂ : Subgroup X} (h₁ : IsSylowTwoOf S₁ ⊤)
    (h₂ : IsSylowTwoOf S₂ ⊤) : ∃ g : X, S₂ = S₁.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h.symm

end Conj

end CFSG.Quasithin.QP
