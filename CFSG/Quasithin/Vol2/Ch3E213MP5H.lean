module

public import CFSG.Quasithin.Vol2.Ch3E213MP5G
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A] {K : Subgroup A} [K.Normal]

theorem mem_normalizer_of_map_conjNormal {X : Subgroup K} {t : A}
    (h : X.map (MulAut.conjNormal t).toMonoidHom = X) :
    t ∈ Subgroup.normalizer (X.map K.subtype : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨MulAut.conjNormal t x, h ▸ ⟨x, hx, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]
  · rintro ⟨x, hx, hxy⟩
    rw [← h] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨z, hz, ?_⟩
    have h1 : (MulAut.conjNormal t z : A) = t * y * t⁻¹ := hxy
    rw [MulAut.conjNormal_apply] at h1
    have h2 : (z : A) = y := by
      have := congrArg (fun a => t⁻¹ * a * t) h1
      simpa [mul_assoc] using this
    exact h2

variable {k : Type} [Field k]

theorem map_conjModel_ne (θ : ↥K ≃* projectiveSL 3 k) {P : Subgroup (projectiveSL 3 k)} {t : A}
    (ht : t ∉ Subgroup.normalizer (((P.map θ.symm.toMonoidHom).map K.subtype : Subgroup A) :
      Set A)) :
    P.map (conjModel θ t).toMonoidHom ≠ P := by
  intro h
  apply ht
  apply mem_normalizer_of_map_conjNormal
  apply Subgroup.map_injective (f := θ.toMonoidHom) θ.injective
  have h1 := map_conjModel θ t (P.map θ.symm.toMonoidHom)
  rw [map_map_symm] at h1
  rw [← h1, h, map_map_symm]

omit [K.Normal] in
theorem subgroupOf_eq_normalizer {S B : Subgroup A}
    (h : B ⊓ K = K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A)) :
    (B ⊓ K).subgroupOf K =
      Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K) := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right, map_subtype_normalizer inf_le_right, h]

omit [K.Normal] in
theorem isMaxParabolic2_of_isCoatom {S : Subgroup A} (hS : IsSylowTwoOf (S ⊓ K) K)
    {P : Subgroup K} (hP : P ⋖ ⊤)
    (hNP : Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K) ≤ P) :
    IsMaxParabolic2 K (P.map K.subtype) ∧
      K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) ≤ P.map K.subtype := by
  have hN : K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) ≤ P.map K.subtype := by
    rw [← map_subtype_normalizer inf_le_right]
    exact Subgroup.map_mono hNP
  have hKtop : (⊤ : Subgroup K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨⟨⟨Subgroup.map_subtype_le P, S ⊓ K, hS, hN⟩, fun h => hP.1.ne ?_, ?_⟩, hN⟩
  · apply Subgroup.map_injective K.subtype_injective
    rw [h, hKtop]
  · intro Q hQ hQne hPQ
    have hQK : Q ≤ K := hQ.1
    have hQ' : Q.subgroupOf K ≠ ⊤ := by
      intro h
      apply hQne
      rw [← Subgroup.map_subgroupOf_eq_of_le hQK, h, hKtop]
    have hPQ' : P ≤ Q.subgroupOf K := fun x hx => hPQ ⟨x, hx, rfl⟩
    rcases hP.eq_or_eq hPQ' le_top with h | h
    · rw [← Subgroup.map_subgroupOf_eq_of_le hQK, h]
    · exact absurd h hQ'

end CFSG.Quasithin.Ch3E213M.P5
