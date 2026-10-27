module

public import CFSG.RankThree.GF2n.Smith81.OrthE1B7bCard

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

section Abstract

variable {G : Type*} [Group G]

theorem b6s_exists_sq_mem (H : Subgroup G) :
    ∀ (m : ℕ) (s : G), s ∉ H → s ^ (2 ^ m) ∈ H →
      ∃ k : ℕ, s ^ k ∉ H ∧ s ^ k * s ^ k ∈ H := by
  intro m
  induction m with
  | zero =>
    intro s hs h
    exact absurd (by simpa using h) hs
  | succ m ih =>
    intro s hs h
    by_cases h2 : s * s ∈ H
    · exact ⟨1, by simpa using hs, by simpa using h2⟩
    · obtain ⟨k, hk1, hk2⟩ := ih (s * s) h2 (by
        have e : (s * s) ^ (2 ^ m) = s ^ (2 ^ (m + 1)) := by
          rw [← sq, ← pow_mul]
          congr 1
          ring
        rwa [e])
      refine ⟨2 * k, ?_, ?_⟩
      · have e : s ^ (2 * k) = (s * s) ^ k := by rw [pow_mul, sq]
        rwa [e]
      · have e : s ^ (2 * k) * s ^ (2 * k) = (s * s) ^ k * (s * s) ^ k := by
          rw [pow_mul, sq]
        rwa [e]

theorem b6s_exists_normalizing [Finite G] {P S : Subgroup G} (hP : IsPGroup 2 P) (hSP : S ≤ P)
    (hne : S ≠ P) : ∃ x ∈ P, x ∉ S ∧ ∀ y ∈ S, x * y * x⁻¹ ∈ S := by
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : S.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    exact le_antisymm hSP (Subgroup.subgroupOf_eq_top.mp h)
  have hN := Group.normalizerCondition_of_isNilpotent (S.subgroupOf P) hlt
  obtain ⟨-, x, hx, hxn⟩ := SetLike.lt_iff_le_and_exists.mp hN
  refine ⟨x.1, x.2, fun h => hxn (Subgroup.mem_subgroupOf.mpr h), fun y hy => ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp hx ⟨y, hSP hy⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
  exact Subgroup.mem_subgroupOf.mp this

theorem b6s_unique_abelian [Finite G] {U S V : Subgroup G} (hUS : U ≤ S)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hidx : U.relIndex S ≤ 2)
    (hcent : ∀ s ∈ S, s ∉ U →
      2 * Nat.card ↥(U ⊓ Subgroup.centralizer ({s} : Set G)) < Nat.card U)
    (hVS : V ≤ S) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hcard : Nat.card V = Nat.card U) : V = U := by
  by_contra hne
  have hVU : ¬ V ≤ U := fun h => hne (Subgroup.eq_of_le_of_card_ge h hcard.ge)
  obtain ⟨v, hvV, hvU⟩ := SetLike.not_le_iff_exists.mp hVU
  have hprod := b7b_card_sup_mul_card_inf (hVS.trans hSN)
  have hSU : Nat.card S ≤ 2 * Nat.card U := by
    have h := Subgroup.relIndex_mul_card U S
    rw [inf_eq_left.2 hUS] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hidx
  have h1 : Nat.card ↥(V ⊔ U) ≤ Nat.card S := Subgroup.card_le_of_le (sup_le hVS hUS)
  have h2 : Nat.card ↥(V ⊓ U) ≤ Nat.card ↥(U ⊓ Subgroup.centralizer ({v} : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hVab x (Subgroup.mem_inf.mp hx).1 v hvV).symm
  have h3 := hcent v (hVS hvV) hvU
  have hUpos : 0 < Nat.card U := Nat.card_pos
  rw [hcard] at hprod
  have h4 : Nat.card U * Nat.card U ≤
      2 * Nat.card U * Nat.card ↥(U ⊓ Subgroup.centralizer ({v} : Set G)) := by
    calc Nat.card U * Nat.card U = Nat.card ↥(V ⊔ U) * Nat.card ↥(V ⊓ U) := hprod.symm
      _ ≤ (2 * Nat.card U) * Nat.card ↥(U ⊓ Subgroup.centralizer ({v} : Set G)) :=
          Nat.mul_le_mul (h1.trans hSU) h2
  have h5 : Nat.card U ≤ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer ({v} : Set G)) := by
    refine Nat.le_of_mul_le_mul_left ?_ hUpos
    calc Nat.card U * Nat.card U ≤
        2 * Nat.card U * Nat.card ↥(U ⊓ Subgroup.centralizer ({v} : Set G)) := h4
      _ = Nat.card U * (2 * Nat.card ↥(U ⊓ Subgroup.centralizer ({v} : Set G))) := by ring
  omega

theorem b6s_S_eq_P [Finite G] {P U : Subgroup G} (hP : IsPGroup 2 P) (hUP : U ≤ P)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hkey : ∀ V : Subgroup G, V ≤ P ⊓ Subgroup.normalizer (U : Set G) →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → Nat.card V = Nat.card U → V = U) :
    P ⊓ Subgroup.normalizer (U : Set G) = P := by
  by_contra hne
  have hUS : U ≤ P ⊓ Subgroup.normalizer (U : Set G) := le_inf hUP Subgroup.le_normalizer
  obtain ⟨x, hxP, hxS, hxn⟩ := b6s_exists_normalizing hP inf_le_left hne
  set V : Subgroup G := U.map (MulAut.conj x).toMonoidHom with hV
  have hmem : ∀ y, y ∈ V ↔ x⁻¹ * y * x ∈ U := fun y => by
    rw [hV, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hVS : V ≤ P ⊓ Subgroup.normalizer (U : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    exact hxn u (hUS hu)
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩
    show x * u * x⁻¹ * (x * w * x⁻¹) = x * w * x⁻¹ * (x * u * x⁻¹)
    have e1 : x * u * x⁻¹ * (x * w * x⁻¹) = x * (u * w) * x⁻¹ := by group
    have e2 : x * w * x⁻¹ * (x * u * x⁻¹) = x * (w * u) * x⁻¹ := by group
    rw [e1, e2, hUab u hu w hw]
  have hcard : Nat.card V = Nat.card U := Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hVU := hkey V hVS hVab hcard
  have key : ∀ h, h ∈ U ↔ x * h * x⁻¹ ∈ U := by
    intro h
    have h1 := hmem (x * h * x⁻¹)
    rw [hVU] at h1
    have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    rw [e] at h1
    exact h1.symm
  exact hxS ⟨hxP, Subgroup.mem_normalizer_iff.mpr fun h => key h⟩

end Abstract

end CFSG.RankThree.GF2n.Smith81.Smith23E1.B6

end
