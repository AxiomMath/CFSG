module

public import CFSG.Quasithin.H13.A6Producer4

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem s1347_A6_frame {H₀ K₀ T I : Subgroup G} (hKH : K₀ ≤ H₀)
    (hN : H₀ ≤ normalizer (K₀ : Set G)) (hH₀I : H₀ ≤ normalizer (I : Set G)) (hTH : T ≤ H₀)
    (hT2 : IsPGroup 2 T) (hsylK : IsSylowTwoOf (T ⊓ K₀) K₀) [IsMulCommutative ↥I]
    (hAN : AlternatingNatural (V := ↥I) (autOn K₀ I) ⊤ ⊥ 6) :
    ∃ (ρ : ↥H₀ →* Perm (Fin 6)) (ψ : ↥I ≃* ↥W4),
      (∀ (h : ↥H₀) (v : ↥I), ψ (conjAct I ⟨h, hH₀I h.2⟩ v) = act4 (ρ h) (ψ v)) ∧
      (∀ t (ht : t ∈ T), InD6 (ρ ⟨t, hTH ht⟩)) ∧
      (∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
        ∃ t, ∃ ht : t ∈ T, ρ ⟨t, hTH ht⟩ = σ) ∧
      ∀ σ : Perm (Fin 6), (∃ k, ∃ hk : k ∈ K₀, ρ ⟨k, hKH hk⟩ = σ) ↔
        σ ∈ alternatingGroup (Fin 6) := by
  obtain ⟨R⟩ := exists_rawData4 (hKH.trans hH₀I) hAN
  have hex : ∀ h : ↥H₀, ∃ π : Perm (Fin 6), alpha4 R ⟨h, hH₀I h.2⟩ = act4 π :=
    fun h => exists_perm_alpha4 R ⟨h, hH₀I h.2⟩ (hN h.2)
  choose f hf using hex
  let ρ₀ : ↥H₀ →* Perm (Fin 6) :=
    { toFun := f
      map_one' := by
        apply act4_injective
        rw [← hf, map_one]
        refine MulEquiv.ext fun x => ?_
        show alpha4 R 1 x = x
        rw [alpha4_apply, map_one, MulAut.one_apply, MulEquiv.apply_symm_apply]
      map_mul' := fun a b => by
        apply act4_injective
        rw [map_mul, ← hf, ← hf, ← hf]
        exact alpha4_mul R ⟨a, hH₀I a.2⟩ ⟨b, hH₀I b.2⟩ }
  have hρ₀ : ∀ h : ↥H₀, act4 (ρ₀ h) = alpha4 R ⟨h, hH₀I h.2⟩ := fun h => (hf h).symm
  have hρ₀K : ∀ k : ↥K₀, ρ₀ ⟨k, hKH k.2⟩ = (R.θ k : Perm (Fin 6)) := by
    intro k
    apply act4_injective
    rw [hρ₀, ← alpha4_L]
  set V' : Subgroup ↥H₀ := I.subgroupOf H₀ with hV'
  have hnormtop : ∀ g : ↥H₀, g ∈ normalizer (V' : Set ↥H₀) := by
    intro g
    rw [mem_normalizer_iff]
    intro v
    simp only [hV', mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 (hH₀I g.2) v
  let ρ0' : ↥(normalizer (V' : Set ↥H₀)) →* Perm (Fin 6) := ρ₀.comp (normalizer _).subtype
  let θ' : ↥(K₀.subgroupOf H₀) →* ↥(alternatingGroup (Fin 6)) :=
    R.θ.comp (subgroupOfEquivOfLe hKH).toMonoidHom
  have hsurj' : Function.Surjective θ' :=
    R.surj.comp (subgroupOfEquivOfLe hKH).surjective
  have hnorm' : K₀.subgroupOf H₀ ≤ normalizer (V' : Set ↥H₀) := fun g _ => hnormtop g
  have hρ0L' : ∀ l : ↥(K₀.subgroupOf H₀), ρ0' ⟨l, hnorm' l.2⟩ = (θ' l : Perm (Fin 6)) := by
    intro l
    have := hρ₀K (subgroupOfEquivOfLe hKH l)
    exact this
  have hT' : IsPGroup 2 ↥(T.subgroupOf H₀) := hT2.of_equiv (subgroupOfEquivOfLe hTH).symm
  have hTV' : T.subgroupOf H₀ ≤ normalizer (V' : Set ↥H₀) := fun g _ => hnormtop g
  have hsyl' : IsSylowTwoOf (T.subgroupOf H₀ ⊓ K₀.subgroupOf H₀) (K₀.subgroupOf H₀) := by
    have e : T.subgroupOf H₀ ⊓ K₀.subgroupOf H₀ = (T ⊓ K₀).subgroupOf H₀ := by
      rw [subgroupOf, subgroupOf, subgroupOf, comap_inf]
    refine ⟨inf_le_right, hT'.to_le inf_le_left, ?_⟩
    show ¬ 2 ∣ (T.subgroupOf H₀ ⊓ K₀.subgroupOf H₀).relIndex (K₀.subgroupOf H₀)
    rw [e, relIndex_subgroupOf hKH]
    exact hsylK.2.2
  obtain ⟨π, hπT, hπD, hπL⟩ := exists_conj_frame ρ0' θ' hsurj' hnorm' hρ0L' hT' hTV' hsyl'
  refine ⟨(MulAut.conj π).toMonoidHom.comp ρ₀, R.ψ.trans (act4 π), fun h v => ?_,
    fun t ht => ?_, fun σ hσD hσA => ?_, fun σ => ?_⟩
  · show act4 π (R.ψ (conjAct I ⟨h, hH₀I h.2⟩ v)) =
      act4 (π * ρ₀ h * π⁻¹) (act4 π (R.ψ v))
    have e1 : R.ψ (conjAct I ⟨h, hH₀I h.2⟩ v) = alpha4 R ⟨h, hH₀I h.2⟩ (R.ψ v) := by
      rw [alpha4_apply, MulEquiv.symm_apply_apply]
    rw [e1, ← hρ₀, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul,
      inv_mul_cancel_right]
  · exact hπT ⟨⟨t, hTH ht⟩, hnormtop _⟩ (mem_subgroupOf.2 ht)
  · obtain ⟨g, hg, hgσ⟩ := hπD σ hσD hσA
    exact ⟨((g : ↥H₀) : G), mem_subgroupOf.1 hg, hgσ⟩
  · constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hπL _).1 ⟨⟨⟨k, hKH hk⟩, hnormtop _⟩, mem_subgroupOf.2 hk, rfl⟩
    · intro hσ
      obtain ⟨g, hg, hgσ⟩ := (hπL σ).2 hσ
      exact ⟨((g : ↥H₀) : G), mem_subgroupOf.1 hg, hgσ⟩

end CFSG.Quasithin.H13.U3
