module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLAligned
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHolds

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.StandardType.E6ThreeModel
open scoped commutatorElement

theorem zlProp_transport {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (I : Set (MulAut R)) (I' : Set (MulAut R'))
    (hI : ∀ φ : MulAut R', φ ∈ I' ↔ (MulAut.congr e).symm φ ∈ I) :
    GGE6DepZLProp R I → GGE6DepZLProp R' I' := by
  intro h L' _ _ ψ' A hTB hcard
  obtain ⟨hψ', hker', hperf, hA, hAI, h5, h3, hsc⟩ := hTB
  have hψ : Function.Surjective (e.symm.toMonoidHom.comp ψ') := e.symm.surjective.comp hψ'
  have hkerEq : (e.symm.toMonoidHom.comp ψ').ker = ψ'.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  have hTB : GGTorusTBGroup 3 5 R I L' (e.symm.toMonoidHom.comp ψ') A := by
    refine ⟨hψ, hkerEq ▸ hker', hperf, hA, ?_, h5, h3, hsc⟩
    intro a ha
    obtain ⟨φ', hφ', hφ'a⟩ := hAI a ha
    refine ⟨(MulAut.congr e).symm φ', (hI φ').1 hφ', fun l => ?_⟩
    simp [MulAut.congr_symm_apply, hφ'a]
  obtain ⟨Φ, T, w, hmodel, hcob⟩ := h L' (e.symm.toMonoidHom.comp ψ') A hTB hcard
  rw [hkerEq] at hmodel hcob
  exact ⟨Φ, T, w, hmodel, hcob⟩

theorem commutator_mem_cobdry {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {w : Fin 6 → L'}
    (i : Fin 6) {t : L'} (ht : MulAut.conj t ∈ A) :
    ⁅w i, t⁆ ∈ ggE6WeylCobdry A w := by
  refine Subgroup.subset_closure ⟨i, MulAut.conj t, ht, ?_⟩
  simp only [MulAut.conj_apply, commutatorElement_def]
  group

variable {R : Type} [Group R]

theorem zlProp_of_good (hAL : GGAbelianLift) (D : FrameData R) (hD : D.Good)
    (I : Set (MulAut R)) (hI : (D.H : Set (MulAut R)) = I)
    (hcard : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Nat.card ψ.ker ∣ 3)
    (hrow : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ w : Fin 6 → L', (∀ i, ψ (w i) = D.nb i) →
        ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ D.V0) ∧
          ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆)) :
    GGE6DepZLProp R I := by
  intro L' _ _ ψ A hTB _
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  haveI : Finite R := Finite.of_surjective ψ hψ
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hD.center
  let ρ : MulAut L' →* MulAut R := BstarDesc.descAut hψ hZ
  have hρ : ∀ a l, ρ a (ψ l) = ψ (a l) := fun a l => BstarDesc.descAut_apply hψ hZ a l
  have hρinj : Function.Injective ρ := BstarDesc.descAut_injective hψ hZ hperf
  have hAH : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hρφ : ρ a = φ := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hρ, hφ]
    have hφH : φ ∈ (D.H : Set (MulAut R)) := by rw [hI]; exact hφI
    rw [hρφ]
    exact hφH
  obtain ⟨γ, -, hγ⟩ := exists_align D hD.shape hρinj hA h5 hAH
  let ψ' : L' →* R := γ.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ
  have hkerEq : ψ'.ker = ψ.ker := by
    ext l
    simp [ψ', MonoidHom.mem_ker]
  have hker' : ψ'.ker ≤ Subgroup.center L' := hkerEq ▸ hker
  have hZ' : ψ'.ker = Subgroup.center L' := hkerEq ▸ hZ
  let ρ' : MulAut L' →* MulAut R := BstarDesc.descAut hψ' hZ'
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := fun a l => BstarDesc.descAut_apply hψ' hZ' a l
  have hρ'inj : Function.Injective ρ' := BstarDesc.descAut_injective hψ' hZ' hperf
  have hρ'eq : ∀ a, ρ' a = γ * ρ a * γ⁻¹ := by
    intro a
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ := hψ' r
    rw [hρ']
    simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply,
      MulAut.inv_apply_self, hρ, map_mul]
  have hal : ∀ a ∈ A, ρ' a ∈ D.diag.range := fun a ha => by
    rw [hρ'eq]
    exact hγ a ha
  have hc3 : Nat.card ψ'.ker = 1 ∨ Nat.card ψ'.ker = 3 := by
    have h3 : Nat.card ψ'.ker ∣ 3 := hcard L' ψ' hψ' hker' hperf
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  obtain ⟨Φ, w, hmodel, hw, hAV⟩ := zl_model_odd D hAL hD hψ' hker' hc3 hρ' hρ'inj hA hsc hal
  rw [hkerEq] at hmodel
  refine ⟨Φ, D.Tor.comap ψ', w, hmodel, ?_⟩
  intro z hz _
  obtain ⟨t, ht, hsub⟩ := hrow L' ψ' hψ' hker' hperf w hw
  have hle : Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) ≤ ggE6WeylCobdry A w := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact commutator_mem_cobdry i (hAV (t i) (ht i))
  exact hle (hsub (hkerEq ▸ hz))

end CFSG.StandardType.E6Dep.ZL

end
