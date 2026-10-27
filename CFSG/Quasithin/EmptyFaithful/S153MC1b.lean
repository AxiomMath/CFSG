module

public import CFSG.Quasithin.EmptyFaithful.S153MDiag
public import CFSG.Quasithin.EmptyFaithful.S153MSig
public import CFSG.Quasithin.EmptyFaithful.SzN15Out
public import CFSG.Quasithin.EmptyFaithful.S1565A

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Quasithin.S1565

namespace S153M

section Diag

variable {G : Type} [Group G] [Finite G]

theorem not_isDiagramNontrivial_of_natOutcome {H K T : Subgroup G} (M' : Subgroup G)
    (hKH : K ≤ H) (hsub : IsSubnormal K H) (hT : IsSylowTwoOf T H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {E : Type} [CommGroup E] [Finite E]
    (φ : ↥H →* MulAut E) {L' : Subgroup (MulAut E)} (ρK : ↥K →* ↥L')
    (hρK : Function.Surjective ρK)
    (hρKφ : ∀ k : ↥K, ((ρK k : ↥L') : MulAut E) = φ (Subgroup.inclusion hKH k))
    (σ : ↥L' →* ↥(E2.star M' H K)) (hσ : Function.Surjective σ)
    (hz : σ.ker ≤ Subgroup.center ↥L')
    (hσρ : ∀ k : ↥K, σ (ρK k) = S153M.starMapK M' H K hKH k)
    (hNat : SzN15.NatOutcome L') :
    ¬ E2.IsDiagramNontrivial (E2.star M' H T) (E2.star M' H K) (E2.star M' H (T ⊓ K)) := by
  have hSylK : IsSylowTwoOf (T ⊓ K) K := A312.isSylowTwoOf_inf_of_subnormal hsub hT
  have hSylK₁ : IsSylowTwoOf ((T ⊓ K).subgroupOf K) ⊤ := isSylowTwoOf_subgroupOf_top' hSylK
  set S₁ : Subgroup ↥L' := ((T ⊓ K).subgroupOf K).map ρK with hS₁def
  have hS₁ : IsSylowTwoOf S₁ ⊤ := isSylowTwoOf_map_top_surj ρK hρK hSylK₁
  set S₀ : Subgroup (MulAut E) := S₁.map L'.subtype with hS₀def
  have hS₀L : S₀ ≤ L' := Subgroup.map_subtype_le _
  have hS₀sub : S₀.subgroupOf L' = S₁ :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective L') S₁
  have hS₀ : IsSylowTwoOf S₀ L' := by
    refine isSylowTwoOf_of_subgroupOf_top hS₀L ?_
    rw [hS₀sub]
    exact hS₁
  have hmemS₀ : ∀ m : MulAut E, m ∈ S₀ ↔
      ∃ k : ↥K, (k : G) ∈ T ∧ φ (Subgroup.inclusion hKH k) = m := by
    intro m
    constructor
    · rintro ⟨s, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, (Subgroup.mem_subgroupOf.mp hk).1, (hρKφ k).symm⟩
    · rintro ⟨k, hkT, rfl⟩
      exact ⟨ρK k, ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hkT, k.2⟩, rfl⟩, hρKφ k⟩
  have hmemL : ∀ m : MulAut E, m ∈ L' ↔ ∃ k : ↥K, φ (Subgroup.inclusion hKH k) = m := by
    intro m
    constructor
    · intro hm
      obtain ⟨k, hk⟩ := hρK ⟨m, hm⟩
      exact ⟨k, by rw [← hρKφ k, hk]⟩
    · rintro ⟨k, rfl⟩
      rw [← hρKφ k]
      exact (ρK k).2
  obtain ⟨Q, hQ, hQN, hQa⟩ := SzN15.goodCoatom_of_natOutcome hNat hS₀
  have hSσ : S₁.map σ = (E2.star M' H (T ⊓ K)).subgroupOf (E2.star M' H K) := by
    ext y
    constructor
    · rintro ⟨s, ⟨k, hk, rfl⟩, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      refine ⟨Subgroup.inclusion hKH k, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hk)
      · rw [hσρ k]
        rfl
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.mp hy
      have hxTK : (x : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hx
      refine ⟨ρK ⟨x, hxTK.2⟩, ⟨⟨x, hxTK.2⟩, Subgroup.mem_subgroupOf.mpr hxTK, rfl⟩, ?_⟩
      rw [hσρ]
      apply Subtype.ext
      exact hxy
  have hSstar : IsSylowTwoOf (E2.star M' H (T ⊓ K)) (E2.star M' H K) := by
    have hle : E2.star M' H (T ⊓ K) ≤ E2.star M' H K := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx |>.2), rfl⟩
    refine isSylowTwoOf_of_subgroupOf_top hle ?_
    rw [← hSσ]
    exact isSylowTwoOf_map_top_surj σ hσ hS₁
  have hfwdL : ∀ τ : ↥H, (τ : G) ∈ T → ∀ y ∈ L', φ τ * y * (φ τ)⁻¹ ∈ L' := by
    intro τ hτ y hy
    obtain ⟨k, rfl⟩ := (hmemL y).1 hy
    refine (hmemL _).2 ⟨⟨(τ : G) * k * (τ : G)⁻¹, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hTK hτ) (k : G)).1 k.2
    · rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hfwdS : ∀ τ : ↥H, (τ : G) ∈ T → ∀ y ∈ S₀, φ τ * y * (φ τ)⁻¹ ∈ S₀ := by
    intro τ hτ y hy
    obtain ⟨k, hkT, rfl⟩ := (hmemS₀ y).1 hy
    refine (hmemS₀ _).2 ⟨⟨(τ : G) * k * (τ : G)⁻¹, ?_⟩, T.mul_mem (T.mul_mem hτ hkT) (T.inv_mem hτ), ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hTK hτ) (k : G)).1 k.2
    · rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hnormL : ∀ τ : ↥H, (τ : G) ∈ T → φ τ ∈ Subgroup.normalizer (L' : Set (MulAut E)) := by
    intro τ hτ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwdL τ hτ y, fun hy => ?_⟩
    have hτ' : ((τ⁻¹ : ↥H) : G) ∈ T := by
      rw [Subgroup.coe_inv]
      exact T.inv_mem hτ
    have := hfwdL τ⁻¹ hτ' _ hy
    simpa [map_inv, mul_assoc] using this
  have hnormS : ∀ τ : ↥H, (τ : G) ∈ T → φ τ ∈ Subgroup.normalizer (S₀ : Set (MulAut E)) := by
    intro τ hτ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwdS τ hτ y, fun hy => ?_⟩
    have hτ' : ((τ⁻¹ : ↥H) : G) ∈ T := by
      rw [Subgroup.coe_inv]
      exact T.inv_mem hτ
    have := hfwdS τ⁻¹ hτ' _ hy
    simpa [map_inv, mul_assoc] using this
  refine not_isDiagramNontrivial_of_coatom hSstar σ hσ hz hS₁ hSσ hQ ?_ ?_
  ·
    intro x hx
    refine hQN x ?_
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      obtain ⟨s, hs, rfl⟩ := hm
      have := (Subgroup.mem_normalizer_iff.mp hx s).mp hs
      exact ⟨x * s * x⁻¹, this, rfl⟩
    · intro hm
      obtain ⟨s, hs, hsm⟩ := hm
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (S₁ : Set ↥L') := Subgroup.inv_mem _ hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hxinv s).mp hs
      refine ⟨x⁻¹ * s * x, ?_, ?_⟩
      · simpa using h1
      · have h2 : (s : MulAut E) = (x : MulAut E) * m * (x : MulAut E)⁻¹ := hsm
        change ((x⁻¹ * s * x : ↥L') : MulAut E) = m
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2]
        group
  ·
    rintro t ⟨τ, hτ, rfl⟩
    have hτT : (τ : G) ∈ T := Subgroup.mem_subgroupOf.mp hτ
    have hτK : ∀ g : G, (τ : G) * g * (τ : G)⁻¹ ∈ K ↔ g ∈ K := fun g => by
      simpa using (Subgroup.mem_normalizer_iff.mp (hTK hτT) g).symm
    let cK : ↥K → ↥K := fun k => ⟨(τ : G) * k * (τ : G)⁻¹, (hτK k).2 k.2⟩
    have hcK : ∀ k : ↥K, φ (Subgroup.inclusion hKH (cK k)) =
        φ τ * φ (Subgroup.inclusion hKH k) * (φ τ)⁻¹ := by
      intro k
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    have hfL : ∀ y : ↥L', φ τ * (y : MulAut E) * (φ τ)⁻¹ ∈ L' := fun y =>
      hfwdL τ hτT y y.2
    have hfL' : ∀ y : ↥L', (φ τ)⁻¹ * (y : MulAut E) * (φ τ)⁻¹⁻¹ ∈ L' := by
      intro y
      have hτ' : ((τ⁻¹ : ↥H) : G) ∈ T := by
        rw [Subgroup.coe_inv]
        exact T.inv_mem hτT
      have := hfwdL τ⁻¹ hτ' y y.2
      simpa [map_inv] using this
    let α : ↥L' ≃* ↥L' :=
      { toFun := fun y => ⟨φ τ * y * (φ τ)⁻¹, hfL y⟩
        invFun := fun y => ⟨(φ τ)⁻¹ * y * (φ τ)⁻¹⁻¹, hfL' y⟩
        left_inv := fun y => Subtype.ext (by simp [mul_assoc])
        right_inv := fun y => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hαρ : ∀ k : ↥K, α (ρK k) = ρK (cK k) := by
      intro k
      apply Subtype.ext
      show φ τ * ((ρK k : ↥L') : MulAut E) * (φ τ)⁻¹ = ((ρK (cK k) : ↥L') : MulAut E)
      rw [hρKφ, hρKφ, hcK]
    refine ⟨α, fun x => ?_, fun x hx => hQa (φ τ) (hnormL τ hτT) (hnormS τ hτT) x (α x) rfl hx⟩
    obtain ⟨k, rfl⟩ := hρK x
    rw [hαρ, hσρ, hσρ]
    show (QuotientGroup.mk' ((kerIn M' H).subgroupOf H)) (Subgroup.inclusion hKH (cK k)) =
      (QuotientGroup.mk' ((kerIn M' H).subgroupOf H)) τ *
        (QuotientGroup.mk' ((kerIn M' H).subgroupOf H)) (Subgroup.inclusion hKH k) *
          ((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)) τ)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

end Diag

end S153M

end CFSG.Quasithin
