module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Helpers

variable {G : Type*} [Group G]

private theorem exists_mem_normalizer_of_lt_pGroup {p : ℕ} [Fact p.Prime] [Finite G]
    {H P : Subgroup G} (hP : IsPGroup p P) (hHP : H < P) :
    ∃ x ∈ P, x ∉ H ∧ x ∈ normalizer (H : Set G) := by
  set IP : Subgroup P := H.subgroupOf P with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hHP.ne (le_antisymm hHP.le fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ IP := by rw [htop]; trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : IP < normalizer (IP : Set P) := Group.normalizerCondition_of_isNilpotent IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (normalizer (H : Set G)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hHP.le]
    exact hxN
  exact mem_subgroupOf.mp hxsub

@[instance_reducible]
private def conjAction (Q : Subgroup G) (Ω : Set (Subgroup G))
    (h : ∀ g ∈ Q, ∀ B ∈ Ω, B.map (MulAut.conj g).toMonoidHom ∈ Ω) : MulAction Q Ω where
  smul g B := ⟨B.1.map (MulAut.conj (g : G)).toMonoidHom, h g g.2 B.1 B.2⟩
  one_smul B := Subtype.ext (by
    show B.1.map (MulAut.conj ((1 : Q) : G)).toMonoidHom = B.1
    ext x
    simp [Subgroup.mem_map])
  mul_smul g g' B := Subtype.ext (by
    show B.1.map (MulAut.conj ((g * g' : Q) : G)).toMonoidHom =
      (B.1.map (MulAut.conj (g' : G)).toMonoidHom).map (MulAut.conj (g : G)).toMonoidHom
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(g' : G) * y * (g' : G)⁻¹, ⟨y, hy, rfl⟩, by simp [mul_assoc]⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [mul_assoc]⟩)

private theorem exists_le_normalizer_of_not_dvd_ncard {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQ : IsPGroup p Q) {Ω : Set (Subgroup G)} (hΩ : ¬ p ∣ Ω.ncard)
    (h : ∀ g ∈ Q, ∀ B ∈ Ω, B.map (MulAut.conj g).toMonoidHom ∈ Ω) :
    ∃ B ∈ Ω, Q ≤ normalizer (B : Set G) := by
  let _ := conjAction Q Ω h
  obtain ⟨B, hB⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card Ω hΩ
  refine ⟨B.1, B.2, fun g hg => ?_⟩
  have h1 : (⟨g, hg⟩ : Q) • B = B := MulAction.mem_fixedPoints.mp hB ⟨g, hg⟩
  have h2 : B.1.map (MulAut.conj g).toMonoidHom = B.1 := congrArg Subtype.val h1
  exact mem_normalizer_iff_map_conj_eq.mpr h2

end Helpers

theorem card_eq_pow_factorization_of_fixed_point {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {T : Subgroup G} (hT : IsPGroup p T) (Ω : Set (Subgroup G))
    (hΩ : ¬ p ∣ Ω.ncard)
    (hΩn : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ B ∈ Ω,
      B.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hbound : ∀ B ∈ Ω, ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ Subgroup.normalizer (B : Set G) →
      Nat.card Q ≤ Nat.card T) :
    Nat.card T = p ^ (Nat.card G).factorization p := by
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  suffices hTeq : T = (P : Subgroup G) by
    rw [hTeq]
    exact Sylow.card_eq_multiplicity P
  by_contra hne
  have hlt : T < (P : Subgroup G) := lt_of_le_of_ne hTP hne
  obtain ⟨x, hxP, hxT, hxN⟩ := exists_mem_normalizer_of_lt_pGroup P.isPGroup' hlt
  have hxQ : x ∈ (P : Subgroup G) ⊓ normalizer (T : Set G) := ⟨hxP, hxN⟩
  have hTQ : T < (P : Subgroup G) ⊓ normalizer (T : Set G) :=
    lt_of_le_of_ne (le_inf hTP le_normalizer) fun heq => hxT (heq ▸ hxQ)
  have hQ : IsPGroup p ↥((P : Subgroup G) ⊓ normalizer (T : Set G)) :=
    P.isPGroup'.to_inf_left
  obtain ⟨B, hB, hQB⟩ := exists_le_normalizer_of_not_dvd_ncard hQ hΩ
    (fun g hg => hΩn g (mem_inf.mp hg).2)
  exact absurd (Subgroup.card_lt_of_lt hTQ) (not_lt_of_ge (hbound B hB _ hQ hQB))

end CFSG.Sporadic.Recognition.LyonsSims
