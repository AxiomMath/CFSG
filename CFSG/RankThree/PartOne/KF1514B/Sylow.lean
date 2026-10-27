module

public import Mathlib.GroupTheory.Sylow
public import CFSG.RankThree.PartOne.KF1514B.Card

public section

namespace CFSG.RankThree.PartOne.KF1514B

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conj_le_of_not_dvd_index {T A : Subgroup G} (hT : ¬ p ∣ T.index)
    (hA : IsPGroup p A) : ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ T := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p T))
  set S : Subgroup G := (P : Subgroup T).map T.subtype with hS
  have hSp : IsPGroup p S := P.isPGroup'.map T.subtype
  have hPi : ¬ p ∣ (P : Subgroup T).index := P.not_dvd_index
  have hSi : ¬ p ∣ S.index := by
    rw [hS, Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).1 h with h | h
    · exact hPi h
    · exact hT h
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hSp.toSylow hSi) Q
  have hmap : (Q : Subgroup G) = S.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, IsPGroup.toSylow_coe]
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hyQ : y ∈ (Q : Subgroup G) := hAQ hy
  rw [hmap] at hyQ
  obtain ⟨z, hz, rfl⟩ := hyQ
  have : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom z) = z := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  obtain ⟨t, ht, rfl⟩ := hz
  exact t.2

end Sylow

section Cyclic

variable {C : Type*} [Group C] [Finite C] [IsCyclic C]

theorem card_le_of_pow_eq_one {H : Subgroup C} {n : ℕ} (hn : 0 < n) (hH : ∀ x ∈ H, x ^ n = 1) :
    Nat.card H ≤ n := by
  classical
  have := Fintype.ofFinite C
  calc Nat.card H ≤ Nat.card {a : C // a ^ n = 1} := by
        refine Nat.card_le_card_of_injective (fun x => ⟨(x : C), hH x x.2⟩) ?_
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : {a : C // a ^ n = 1} => (z : C)) h
    _ = (Finset.univ.filter fun a : C => a ^ n = 1).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ n := IsCyclic.card_pow_eq_one_le hn

end Cyclic

section Torus

variable {G Tor C : Type*} [Group G] [Group Tor] [Finite Tor] [Group C] [Finite C] [IsCyclic C]

theorem exists_torus_subgroup {p : ℕ} (hp : 0 < p) (τ : Tor →* G) (hτ : Function.Injective τ)
    (ψ : Tor →* C) {A : Subgroup G} (hA : ∀ a ∈ A, a ^ p = 1) {h : G}
    (hAh : A.map (MulAut.conj h).toMonoidHom ≤ τ.range) :
    ∃ B : Subgroup G, B ≤ A ∧ Nat.card A ≤ p * Nat.card B ∧
      ∀ b ∈ B, ∃ t : Tor, ψ t = 1 ∧ h * b * h⁻¹ = τ t := by
  set A₀ : Subgroup Tor := (A.map (MulAut.conj h).toMonoidHom).comap τ with hA₀def
  have hA₀ : A₀.map τ = A.map (MulAut.conj h).toMonoidHom := by
    rw [hA₀def, Subgroup.map_comap_eq, inf_eq_right.2 hAh]
  have hexp : ∀ t ∈ A₀, t ^ p = 1 := by
    intro t ht
    have ht' : τ t ∈ A.map (MulAut.conj h).toMonoidHom := ht
    obtain ⟨a, ha, hat⟩ := ht'
    apply hτ
    rw [map_pow, map_one, ← hat]
    have : (MulAut.conj h).toMonoidHom a ^ p = (MulAut.conj h).toMonoidHom (a ^ p) :=
      (map_pow _ _ _).symm
    rw [this, hA a ha, map_one]
  have hcardA₀ : Nat.card A₀ = Nat.card A := by
    rw [← Subgroup.card_map_of_injective hτ (K := A₀), hA₀,
      Subgroup.card_map_of_injective (MulAut.conj h).injective]
  have h1 := card_le_ker_mul_map ψ A₀
  have h2 : Nat.card ↥(A₀.map ψ) ≤ p := by
    refine card_le_of_pow_eq_one hp ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, hexp t ht, map_one]
  set B₀ : Subgroup Tor := A₀ ⊓ ψ.ker with hB₀
  refine ⟨(B₀.map τ).map (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have : τ t ∈ A.map (MulAut.conj h).toMonoidHom := by
      rw [← hA₀]
      exact ⟨t, ht.1, rfl⟩
    obtain ⟨a, ha, hat⟩ := this
    have e : (MulAut.conj h⁻¹).toMonoidHom (τ t) = a := by
      rw [← hat]
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact ha
  · have hcardB : Nat.card ↥((B₀.map τ).map (MulAut.conj h⁻¹).toMonoidHom) = Nat.card B₀ := by
      rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective,
        Subgroup.card_map_of_injective hτ]
    rw [hcardB, ← hcardA₀]
    calc Nat.card A₀ ≤ Nat.card B₀ * Nat.card ↥(A₀.map ψ) := h1
      _ ≤ Nat.card B₀ * p := Nat.mul_le_mul_left _ h2
      _ = p * Nat.card B₀ := mul_comm _ _
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, MonoidHom.mem_ker.1 ht.2, ?_⟩
    simp [mul_assoc]

end Torus

end CFSG.RankThree.PartOne.KF1514B
