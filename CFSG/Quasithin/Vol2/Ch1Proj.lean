module

public import CFSG.Quasithin.Vol2.Ch1Index2
public import CFSG.Quasithin.Vol2.Ch1Quotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Radical

variable {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]

omit [Finite Y] in
theorem map_solvRad_le_solvRad_map (θ : X →* Y) (Λ : Subgroup X) :
    (solvRad Λ).map θ ≤ solvRad (Λ.map θ) := by
  have hNH : (solvRad Λ).map θ ≤ Λ.map θ := Subgroup.map_mono (solvRad_le Λ)
  refine le_solvRad hNH ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff hNH]
    rintro _ _ ⟨s, hs, rfl⟩ ⟨l, hl, rfl⟩
    refine ⟨l * s * l⁻¹, conj_mem_solvRad (Subgroup.le_normalizer hl) hs, by simp⟩
  · have := solvRad_isSolvable Λ
    exact Group.isSolvable_of_surjective (f := θ.subgroupMap (solvRad Λ))
      (θ.subgroupMap_surjective (solvRad Λ))

end Radical

variable {X : Type} [Group X] [Finite X]

theorem le_of_projection {K K' Λ S₁ R₁ Z : Subgroup X} (hK : K.Normal) (hK' : K'.Normal)
    (hKK' : K ⊔ K' = ⊤) (hΛ : Λ ∈ cComp Λ) (hΛK' : ¬ Λ ≤ K')
    (hS₁ : IsSylowTwoOf S₁ ⊤) (hR₁ : R₁ ≤ S₁) (h2 : TwoCosets R₁ S₁)
    (hD : IsSylowTwoOf (R₁ ⊓ Λ) Λ) (hZ : IsPGroup 2 Z)
    (hKL : ∀ r ∈ R₁, Λ.map (MulAut.conj r).toMonoidHom = Λ ∨
      ⁅Λ, Λ.map (MulAut.conj r).toMonoidHom⁆ ≤ Z) : Λ ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ : X →* X ⧸ K' := QuotientGroup.mk' K'
  have hΛperf : ⁅Λ, Λ⁆ = Λ := perfect_of_mem_cComp hΛ
  have hΛtop : (⊤ : Subgroup ↥Λ) ∈ cComp (⊤ : Subgroup ↥Λ) := by
    have h := subgroupOf_mem_cComp hΛ
    rwa [Subgroup.subgroupOf_self] at h
  let f : ↥Λ →* X ⧸ K' := θ.comp Λ.subtype
  have hfk : f.ker = K'.subgroupOf Λ := by
    ext x
    simp [f, θ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hkerf : Group.IsSolvable f.ker := by
    have hn : (K'.subgroupOf Λ).Normal := hK'.comap Λ.subtype
    rcases normal_eq_top_or_map_le_solvRad hΛ (K'.subgroupOf Λ) with h | h
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h) hΛK'
    · rw [hfk]
      have hs : Group.IsSolvable ↥(solvRad Λ) := solvRad_isSolvable Λ
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion h).comp
          ((K'.subgroupOf Λ).equivMapOfInjective Λ.subtype Λ.subtype_injective).toMonoidHom)
        ((Subgroup.inclusion_injective h).comp
          ((K'.subgroupOf Λ).equivMapOfInjective _ _).injective)
  have hrange : (⊤ : Subgroup ↥Λ).map f = Λ.map θ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype]
  have hPh : Λ.map θ ∈ cComp (Λ.map θ) := by
    have h := map_mem_cComp_of_le f hkerf (le_top : f.ker ≤ ⊤) hΛtop
    rwa [hrange] at h
  let KP : Subgroup X := K ⊓ (Λ.map θ).comap θ
  have hSK : IsSylowTwoOf (S₁ ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hS₁ le_top (Subgroup.normalizer_eq_top_iff.mpr hK).ge
  have hKN : K ≤ Subgroup.normalizer (K' : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hK']; exact le_top
  have hSKN : S₁ ⊓ K ≤ Subgroup.normalizer (K' : Set X) := inf_le_right.trans hKN
  have hdec' : ∀ t ∈ S₁, ∃ k ∈ S₁ ⊓ K, ∃ k' ∈ K', k * k' = t := by
    intro t ht
    have h := A312.inf_sup_le_of_sylow hSK hS₁.2.1 hKN
    rw [hKK', inf_top_eq] at h
    have h1 := h ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSKN] at h1
    obtain ⟨k, hk, k', hk', rfl⟩ := h1
    exact ⟨k, hk, k', hk', rfl⟩
  have hmaxD := (A4.isSylowTwoOf_iff_maximal.mp hD).2.2
  have hSΛ : S₁ ⊓ Λ ≤ R₁ ⊓ Λ :=
    hmaxD (S₁ ⊓ Λ) inf_le_right hS₁.2.1.to_inf_left (inf_le_inf_right Λ hR₁)
  have hΛS : (S₁ ⊓ Λ).map θ ≤ (S₁ ⊓ KP).map θ := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨k, hk, k', hk', rfl⟩ := hdec' t ht.1
    have hθ1 : θ k' = 1 := (QuotientGroup.eq_one_iff k').mpr hk'
    have hθ : θ (k * k') = θ k := by
      rw [map_mul, hθ1, mul_one]
    have hθk : θ k ∈ Λ.map θ := hθ ▸ Subgroup.mem_map_of_mem θ ht.2
    exact ⟨k, ⟨hk.1, hk.2, hθk⟩, hθ.symm⟩
  have hDsyl : IsSylowTwoOf ((R₁ ⊓ Λ).map θ) (Λ.map θ) := isSylowTwoOf_map_hom θ hD
  have hDS : (R₁ ⊓ Λ).map θ ≤ (S₁ ⊓ KP).map θ :=
    (Subgroup.map_mono (inf_le_inf_right Λ hR₁)).trans hΛS
  have hShle : (S₁ ⊓ KP).map θ ≤ Λ.map θ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2.2
  have hSh2 : IsPGroup 2 ((S₁ ⊓ KP).map θ) := (hS₁.2.1.to_inf_left).map θ
  have hShSyl : IsSylowTwoOf ((S₁ ⊓ KP).map θ) (Λ.map θ) := by
    rw [A4.isSylowTwoOf_iff_maximal]
    refine ⟨hShle, hSh2, fun Q hQ hQ2 hSQ => ?_⟩
    have hmaxP := (A4.isSylowTwoOf_iff_maximal.mp hDsyl).2.2 Q hQ hQ2 (hDS.trans hSQ)
    exact hmaxP.trans hDS
  have h2Sh : TwoCosets ((R₁ ⊓ KP).map θ) ((S₁ ⊓ KP).map θ) := (h2.inf KP).map θ
  have hAL := not_commutator_le_solvRad hPh hShSyl h2Sh
  have hex : ∃ x ∈ Λ.map θ, ∃ y ∈ (R₁ ⊓ KP).map θ, ⁅x, y⁆ ∉ solvRad (Λ.map θ) := by
    by_contra hcon
    push Not at hcon
    exact hAL (Subgroup.commutator_le.mpr hcon)
  obtain ⟨x, hx, y, hy, hxy⟩ := hex
  obtain ⟨l, hl, rfl⟩ := hx
  obtain ⟨r, hr, rfl⟩ := hy
  have hrR : r ∈ R₁ := hr.1
  have hrK : r ∈ K := hr.2.1
  have hθrP : θ r ∈ Λ.map θ := hr.2.2
  have hnorm : Λ.map (MulAut.conj r).toMonoidHom = Λ := by
    rcases hKL r hrR with h | h
    · exact h
    · exfalso
      have himg : (Λ.map (MulAut.conj r).toMonoidHom).map θ = Λ.map θ := by
        rw [Subgroup.map_map]
        have hc : θ.comp (MulAut.conj r).toMonoidHom =
            (MulAut.conj (θ r)).toMonoidHom.comp θ := by
          ext y
          simp [MulAut.conj_apply]
        rw [hc, ← Subgroup.map_map]
        exact A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hθrP)
      have hperf' : ⁅Λ.map θ, Λ.map θ⁆ = Λ.map θ := by
        rw [← Subgroup.map_commutator, hΛperf]
      have h1 : (⁅Λ, Λ.map (MulAut.conj r).toMonoidHom⁆).map θ = Λ.map θ := by
        rw [Subgroup.map_commutator, himg, hperf']
      have hPh2 : IsPGroup 2 (Λ.map θ) := (hZ.map θ).to_le (h1 ▸ Subgroup.map_mono h)
      have : Group.IsNilpotent ↥(Λ.map θ) := hPh2.isNilpotent
      exact not_isSolvable_of_mem_cComp hPh inferInstance
  have hrN : r ∈ Subgroup.normalizer (Λ : Set X) := A38.map_conj_eq_iff.mp hnorm
  have hzr : Subgroup.zpowers r ≤ Subgroup.normalizer (Λ : Set X) := Subgroup.zpowers_le.mpr hrN
  have hΔΛ : ⁅Λ, Subgroup.zpowers r⁆ ≤ Λ := Subgroup.le_normalizer_iff_commutator_le_left.mp hzr
  have hΛΔ : Λ ≤ Subgroup.normalizer ((⁅Λ, Subgroup.zpowers r⁆ : Subgroup X) : Set X) :=
    Subgroup.normalizer_commutator_ge_left Λ _
  have hΔn : (⁅Λ, Subgroup.zpowers r⁆.subgroupOf Λ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΔΛ).mpr hΛΔ
  have hΔeq : ⁅Λ, Subgroup.zpowers r⁆ = Λ := by
    rcases normal_eq_top_or_map_le_solvRad hΛ (⁅Λ, Subgroup.zpowers r⁆.subgroupOf Λ) with h | h
    · exact le_antisymm hΔΛ (Subgroup.subgroupOf_eq_top.mp h)
    · exfalso
      have hΔs : ⁅Λ, Subgroup.zpowers r⁆ ≤ solvRad Λ := by
        rwa [Subgroup.map_subgroupOf_eq_of_le hΔΛ] at h
      have hcl : ⁅l, r⁆ ∈ ⁅Λ, Subgroup.zpowers r⁆ :=
        Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers r)
      have h1 : θ ⁅l, r⁆ ∈ solvRad (Λ.map θ) :=
        map_solvRad_le_solvRad_map θ Λ (Subgroup.mem_map_of_mem θ (hΔs hcl))
      rw [map_commutatorElement] at h1
      exact hxy h1
  rw [← hΔeq]
  exact A312.commutator_le_of_le_normalizer
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hK]; exact le_top) (Subgroup.zpowers_le.mpr hrK)

end CFSG.Quasithin
