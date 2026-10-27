module

public import CFSG.Quasithin.H13.L32NLem14332e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14332

variable {G : Type} [Group G] {T V : Subgroup G} (D : HatModelU (fsuU T V))

@[expose] noncomputable def imgHom : ↥(l32nH T V) →* ↥(D.img (l32nH T V)) :=
  (D.ρ.comp (Subgroup.inclusion (l32nH_le_normalizer_fsuU T V))).codRestrict (D.img (l32nH T V))
    fun h => L128A.HatU.rho_mem_img D h.2 (l32nH_le_normalizer_fsuU T V h.2)

theorem imgHom_apply (h : ↥(l32nH T V)) :
    ((imgHom D h : ↥(D.img (l32nH T V))) : D.V ≃ₗ[ZMod 2] D.V) =
      D.ρ ⟨h, l32nH_le_normalizer_fsuU T V h.2⟩ := rfl

theorem imgHom_surjective : Function.Surjective (imgHom D) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

theorem imgHom_ker : (imgHom D).ker = (l32nCHat T V).subgroupOf (l32nH T V) := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← rho_eq_one_iff_mem h.2
    (l32nH_le_normalizer_fsuU T V h.2)]
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    rwa [imgHom_apply] at this
  · intro h1
    exact Subtype.ext (by rw [imgHom_apply]; exact h1)

theorem sym_of_iso (e : ↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 5)) :
    ∃ φ : ↥(l32nH T V) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
      φ.ker = (l32nCHat T V).subgroupOf (l32nH T V) := by
  refine ⟨(e : ↥(D.img (l32nH T V)) →* Equiv.Perm (Fin 5)).comp (imgHom D),
    e.surjective.comp (imgHom_surjective D), ?_⟩
  rw [← imgHom_ker D]
  ext h
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
  exact e.map_eq_one_iff

theorem natural_of_case_ii
    (hnat : ∃ (φ : ↥(D.img (l32nH T V)) ≃* RuType.SigmaL2F4) (ψ : D.V ≃+ (Fin 2 → RuType.F4)),
      ∀ (h : ↥(D.img (l32nH T V))) (v : D.V),
        ψ ((h : D.V ≃ₗ[ZMod 2] D.V) v) = RuType.sigmaAct (φ h) (ψ v)) :
    ∃ (φ : ↥(l32nH T V) →* RuType.SigmaL2F4)
      (ψ : ↥(fsuU T V) →* Multiplicative (Fin 2 → RuType.F4)),
      Function.Surjective φ ∧ φ.ker = (l32nCHat T V).subgroupOf (l32nH T V) ∧
      Function.Surjective ψ ∧ ψ.ker = (centerOf (fsuU T V)).subgroupOf (fsuU T V) ∧
      ∀ (h : ↥(l32nH T V)) (u u' : ↥(fsuU T V)), (u' : G) = h * u * (h : G)⁻¹ →
        ψ u' = Multiplicative.ofAdd (RuType.sigmaAct (φ h) (Multiplicative.toAdd (ψ u))) := by
  obtain ⟨e, ψ', hψ'⟩ := hnat
  let ψ : ↥(fsuU T V) →* Multiplicative (Fin 2 → RuType.F4) :=
    { toFun := fun u => Multiplicative.ofAdd (ψ' (D.π u))
      map_one' := by
        show Multiplicative.ofAdd (ψ' (D.π 1)) = Multiplicative.ofAdd 0
        rw [L128A.HatU.π_one D, map_zero]
      map_mul' := fun u w => by
        show Multiplicative.ofAdd (ψ' (D.π ((u : G) * w))) =
          Multiplicative.ofAdd (ψ' (D.π u)) * Multiplicative.ofAdd (ψ' (D.π w))
        rw [D.π_mul u u.2 w w.2, map_add]
        rfl }
  refine ⟨(e : ↥(D.img (l32nH T V)) →* RuType.SigmaL2F4).comp (imgHom D), ψ,
    e.surjective.comp (imgHom_surjective D), ?_, ?_, ?_, ?_⟩
  · rw [← imgHom_ker D]
    ext h
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
    exact e.map_eq_one_iff
  · intro w
    obtain ⟨v, rfl⟩ := ψ'.surjective (Multiplicative.toAdd w)
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    exact ⟨⟨u, hu⟩, rfl⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (ψ' (D.π u)) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, map_eq_zero_iff _ ψ'.injective,
      L128A.HatU.π_eq_zero_iff D u.2]
  · intro h u u' hu'
    show Multiplicative.ofAdd (ψ' (D.π u')) = Multiplicative.ofAdd
      (RuType.sigmaAct (e (imgHom D h)) (ψ' (D.π u)))
    rw [hu', ← D.ρ_π ⟨h, l32nH_le_normalizer_fsuU T V h.2⟩ u u.2, ← imgHom_apply, hψ']

end L14332

end CFSG.Quasithin.H13
