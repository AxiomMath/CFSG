module

public import CFSG.Quasithin.Vol2.KGFactC31E16
public import CFSG.Quasithin.Vol2.KGFactC31Concl

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique

variable {A : Type} [Group A] {n : ℕ} {v : Fin n → A} (hv : EBasis v)

theorem sum_natural_of_surj [Finite A] {M₀ R : Subgroup A} (hM₀N : M₀ ≤ eNorm hv)
    (hRC : R ≤ Subgroup.centralizer (eSub hv : Set A))
    (hsurj₀ : Function.Surjective (E16.eNHom hv hM₀N))
    (hXC : (M₀ ⊔ R) ⊓ Subgroup.centralizer (eSub hv : Set A) = R) :
    IsSumOfNaturalModules (M₀ ⊔ R) (eSub hv) ⊥ (R.subgroupOf (M₀ ⊔ R))
      (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) false 1 := by
  have hRN' : R ≤ eNorm hv := fun r hr => mem_eNorm_of_cent hv (hRC hr)
  have hXN : M₀ ⊔ R ≤ eNorm hv := sup_le hM₀N hRN'
  let α := E16.eNHom hv hXN
  have hker : α.ker = R.subgroupOf (M₀ ⊔ R) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E16.eNHom_eq_one_iff]
    constructor
    · intro h
      have h3 : (x : A) ∈ (M₀ ⊔ R) ⊓ Subgroup.centralizer (eSub hv : Set A) := ⟨x.2, h⟩
      rw [hXC] at h3
      exact h3
    · intro hx
      exact hRC hx
  have hsurj : Function.Surjective α := by
    intro σ
    obtain ⟨m, hm⟩ := hsurj₀ σ
    exact ⟨⟨m, le_sup_left (a := M₀) m.2⟩, Subtype.ext (Units.ext (by rw [← hm]; rfl))⟩
  let β : ↥(eSub hv) →* Multiplicative (Fin n → ZMod 2) := (ecoords hv).toMonoidHom
  have hsec : IsNaturalSection (M₀ ⊔ R) (eSub hv) ⊥ (R.subgroupOf (M₀ ⊔ R))
      (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) := by
    refine ⟨hXN, α, hsurj, hker, β, (ecoords hv).surjective, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr (ecoords hv).injective
    · intro a u w hw
      exact ecoords_conj hv ⟨a, hXN a.2⟩ u w hw
  exact (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec

theorem ker_eNHom {M₀ : Subgroup A} (hM₀N : M₀ ≤ eNorm hv) {O : Subgroup A}
    (hO : M₀ ⊓ Subgroup.centralizer (eSub hv : Set A) = O) :
    (E16.eNHom hv hM₀N).ker = O.subgroupOf M₀ := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E16.eNHom_eq_one_iff, ← hO]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end CFSG.Quasithin.KGC31

end
