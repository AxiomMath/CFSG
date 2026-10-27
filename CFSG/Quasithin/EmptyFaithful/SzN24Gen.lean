module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.SzN22Rig

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace SzN24

section Glue

variable {Ω : Type} [Group Ω]

theorem krig_of_autRigid {K : Subgroup Ω} {M : Type} [Group M] [Finite M] (Φ : ↥K ≃* M)
    (R : ∀ (Ŝ : Subgroup M) (α : M ≃* M), IsSylowTwoOf Ŝ ⊤ → (∀ g ∈ Ŝ, α g ∈ Ŝ) →
      (∀ b ∈ Subgroup.normalizer (Ŝ : Set M), α b * b⁻¹ ∈ Ŝ) → (∀ m, α (α (α m)) = m) →
      (∀ b ∈ Subgroup.normalizer (Ŝ : Set M), orderOf b ≠ 3) →
      ∃ x : M, ∀ m, α m = x * m * x⁻¹) :
    SzN22.KRig K := by
  intro S z hS hzK hzS hz3 hno hcomm
  let σ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨z, hzK⟩
  have hσ : ∀ k : ↥K, ((σ k : ↥K) : Ω) = z * (k : Ω) * z⁻¹ := fun k => rfl
  have hσ3 : ∀ k, σ (σ (σ k)) = k := by
    have hz3' : (⟨z, hzK⟩ : ↥(Subgroup.normalizer (K : Set Ω))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hz3)
    have h' : σ ^ 3 = 1 := by
      show (Subgroup.normalizerMonoidHom K ⟨z, hzK⟩) ^ 3 = 1
      rw [← map_pow, hz3', map_one]
    intro k
    have := congrArg (fun φ : MulAut ↥K => φ k) h'
    simpa [pow_succ, MulAut.mul_apply] using this
  let α : M ≃* M := Φ.symm.trans (σ.trans Φ)
  have hα : ∀ k : ↥K, α (Φ k) = Φ (σ k) := fun k => by
    show Φ (σ (Φ.symm (Φ k))) = Φ (σ k)
    rw [MulEquiv.symm_apply_apply]
  have hSt : IsSylowTwoOf (S.subgroupOf K) ⊤ := (SBd8.isSylowTwoOf_iff_subgroupOf hS.1).mp hS
  have hŜ : IsSylowTwoOf ((S.subgroupOf K).map Φ.toMonoidHom) ⊤ :=
    GoldS146R.isSylowTwoOf_top_map_equiv Φ hSt
  have hnorm : ∀ b ∈ Subgroup.normalizer (((S.subgroupOf K).map Φ.toMonoidHom : Subgroup M) : Set M),
      ((Φ.symm b : ↥K) : Ω) ∈ Subgroup.normalizer (S : Set Ω) := by
    intro b hb
    rw [← Subgroup.map_equiv_normalizer_eq] at hb
    obtain ⟨k, hk, hkb⟩ := hb
    have : Φ.symm b = k := by rw [← hkb]; simp
    rw [this]
    exact (SBd8.mem_normalizer_subgroupOf_iff hS.1 k).mp hk
  have h1 : ∀ g ∈ (S.subgroupOf K).map Φ.toMonoidHom, α g ∈ (S.subgroupOf K).map Φ.toMonoidHom := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨σ k, ?_, (hα k).symm⟩
    show σ k ∈ S.subgroupOf K
    rw [Subgroup.mem_subgroupOf, hσ]
    exact (Subgroup.mem_normalizer_iff.mp hzS _).mp (Subgroup.mem_subgroupOf.mp hk)
  have h2 : ∀ b ∈ Subgroup.normalizer (((S.subgroupOf K).map Φ.toMonoidHom : Subgroup M) : Set M),
      α b * b⁻¹ ∈ (S.subgroupOf K).map Φ.toMonoidHom := by
    intro b hb
    obtain ⟨k, rfl⟩ := Φ.surjective b
    have hk := hnorm _ hb
    rw [MulEquiv.symm_apply_apply] at hk
    refine ⟨σ k * k⁻¹, ?_, ?_⟩
    · show σ k * k⁻¹ ∈ S.subgroupOf K
      rw [Subgroup.mem_subgroupOf]
      have := hcomm (k : Ω) ⟨hk, k.2⟩
      simpa [hσ] using this
    · simp [hα]
  have h3 : ∀ m, α (α (α m)) = m := by
    intro m
    obtain ⟨k, rfl⟩ := Φ.surjective m
    rw [hα, hα, hα, hσ3]
  have h4 : ∀ b ∈ Subgroup.normalizer (((S.subgroupOf K).map Φ.toMonoidHom : Subgroup M) : Set M),
      orderOf b ≠ 3 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Φ.surjective b
    have hk := hnorm _ hb
    rw [MulEquiv.symm_apply_apply] at hk
    have := hno (k : Ω) ⟨hk, k.2⟩
    rwa [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq Φ k] at this
  obtain ⟨x, hx⟩ := R _ α hŜ h1 h2 h3 h4
  refine ⟨((Φ.symm x : ↥K) : Ω), (Φ.symm x).2, fun n hn => ?_⟩
  have h5 := hx (Φ ⟨n, hn⟩)
  rw [hα] at h5
  have h6 : σ ⟨n, hn⟩ = Φ.symm x * ⟨n, hn⟩ * (Φ.symm x)⁻¹ := by
    apply Φ.injective
    rw [h5]
    simp
  have h7 := congrArg (fun k : ↥K => (k : Ω)) h6
  simpa [hσ] using h7

end Glue

section Field

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_of_trace_eq {σ : F ≃+* F} (h3 : ∀ a, σ (σ (σ a)) = a)
    (htr : ∀ a : F, a ≠ 0 → σ a + (σ a)⁻¹ = a + a⁻¹) : σ = 1 := by
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have key : ∀ a : F, σ a = a := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]
    by_contra hne
    have hσa : σ a ≠ 0 := by
      intro h0
      exact ha (σ.injective (by rw [h0, map_zero]))
    have hprod : (σ a - a) * (a * σ a - 1) = 0 := by
      have := htr a ha
      field_simp at this
      linear_combination this
    have hinv : a * σ a = 1 := by
      have := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
      exact sub_eq_zero.mp this
    have hσinv : σ a = a⁻¹ := by
      field_simp
      linear_combination hinv
    have h22 : σ (σ a) = a := by
      rw [hσinv, map_inv₀, hσinv, inv_inv]
    have : σ a = a := by
      have := h3 a
      rw [h22] at this
      exact this
    exact hne this
  ext a
  exact key a

end Field

end SzN24

end CFSG.Quasithin
