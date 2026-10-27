module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Comm
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLAligned
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLRowE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsE
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.StandardType.E6Dep.ZL
open scoped commutatorElement

theorem coverCommSCr_of_good_row {R : Type} [Group R]
    (hAL : GGAbelianLift) (D : FrameData R) (hD : D.Good)
    (I : Set (MulAut R)) (hI : (D.H : Set (MulAut R)) = I)
    (hcard : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Nat.card ψ.ker ∣ 3)
    (hrow : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ w : Fin 6 → L', (∀ i, ψ (w i) = D.nb i) →
        ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ D.V0) ∧
          ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆)) :
    GGE6ThreeCoverCommSCr R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h5 hsc z hz _
  have : Finite R := Finite.of_surjective ψ hψ
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
      MulAut.inv_apply_self, hρ]
  have hal : ∀ a ∈ A, ρ' a ∈ D.diag.range := fun a ha => by
    rw [hρ'eq]
    exact hγ a ha
  have hc3 : Nat.card ψ'.ker = 1 ∨ Nat.card ψ'.ker = 3 := by
    have h3 : Nat.card ψ'.ker ∣ 3 := hcard L' ψ' hψ' hker' hperf
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  obtain ⟨Φ, w, hmodel, hw, hAV⟩ := zl_model_odd D hAL hD hψ' hker' hc3 hρ' hρ'inj hA hsc hal
  obtain ⟨-, -, -, -, hfix, -, -, hact, -⟩ := hmodel
  obtain ⟨t, ht, hsub⟩ := hrow L' ψ' hψ' hker' hperf w hw
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a.1 a.2)⟩
  have hcube := (abelianLift_apply D hAL hD hψ' hker' hc3 hρ' hAp hal hw).2.2
  have hle : Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) ≤
      Subgroup.closure {x : L' | ∃ m t : L',
        (∀ a ∈ A, MulAut.conj m * a * (MulAut.conj m)⁻¹ ∈ A) ∧
        (∀ a ∈ A, a t = t) ∧ t ^ 3 = 1 ∧ x = m * t * m⁻¹ * t⁻¹} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have htT : t i ∈ D.Tor.comap ψ' := ((FrameData.mem_V0 D).1 (ht i)).1
    refine Subgroup.subset_closure ⟨w i, t i, ?_, ?_, hcube (t i) (ht i), ?_⟩
    · intro a ha
      obtain ⟨b, hb, -⟩ := hact i ⟨a, ha⟩
      rw [hb]
      exact b.2
    · intro a ha
      exact hfix a ha (t i) htT
    · exact commutatorElement_def _ _
  exact hle (hsub (hkerEq ▸ hz))


theorem coverCommSCr_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGE6ThreeCoverCommSCr (adjointGroup .E6 K) ((hatAut .E6 K).range : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := Fintype.ofFinite K
  obtain ⟨n, -, hKcard⟩ := FiniteField.card K 2
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKcard]
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hcard : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* adjointGroup .E6 K),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Nat.card ψ.ker ∣ 3 := by
    intro L' _ _ ψ hψ hker hperf
    let ψ' : L' →* TableBExc.RecipeGroup .E6 K :=
      (TableBExc.recipeEquiv .E6 K).symm.toMonoidHom.comp ψ
    have hkerEq : ψ'.ker = ψ.ker := by
      ext l
      simp [ψ', MonoidHom.mem_ker]
    have h := card_ker_dvd_three_e6 hn hK
      ((TableBExc.recipeEquiv .E6 K).symm.surjective.comp hψ) (hkerEq ▸ hker) hperf
    rwa [hkerEq] at h
  exact coverCommSCr_of_good_row ggAbelianLift (eFrame K ζ hζ) (eFrame_good hζo hζ)
    _ rfl hcard fun L' _ _ ψ hψ hker hperf w hw =>
      eFrame_zl_row hK h3 ζ hζ hζo L' ψ hψ hker hperf w hw

end CFSG.StandardType.E6ThreeModel
