module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Defs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGE6ThreeCoverCommSCr (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), CFSG.Open.IsElemAbelian 3 A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      3 ^ 5 ≤ Nat.card A → GGTorusSelfCent 3 A →
      ∀ z ∈ ψ.ker, (∃ k : ℕ, z ^ 3 ^ k = 1) →
        z ∈ Subgroup.closure {x : L' | ∃ m t : L',
          (∀ a ∈ A, MulAut.conj m * a * (MulAut.conj m)⁻¹ ∈ A) ∧
          (∀ a ∈ A, a t = t) ∧ t ^ 3 = 1 ∧ x = m * t * m⁻¹ * t⁻¹}

theorem coverCommSCr_of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (I : Set (MulAut R)) (I' : Set (MulAut R'))
    (hI : ∀ φ : MulAut R, φ ∈ I ↔ MulAut.congr e φ ∈ I') :
    GGE6ThreeCoverCommSCr R' I' → GGE6ThreeCoverCommSCr R I := by
  intro h L' _ _ ψ hψ hker hperf A hA hAI h5 hsc z hz hodd
  have hψ' : Function.Surjective (e.toMonoidHom.comp ψ) := e.surjective.comp hψ
  have hkerEq : (e.toMonoidHom.comp ψ).ker = ψ.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  have hker' : (e.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
    rw [hkerEq]
    exact hker
  have hz' : z ∈ (e.toMonoidHom.comp ψ).ker := by
    rw [hkerEq]
    exact hz
  have hAI' : ∀ a ∈ A, ∃ φ ∈ I', ∀ l : L',
      φ ((e.toMonoidHom.comp ψ) l) = (e.toMonoidHom.comp ψ) (a l) := by
    intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact ⟨MulAut.congr e φ, (hI φ).1 hφ, fun l => by
      simp [MonoidHom.comp_apply, MulAut.congr_apply, hφa]⟩
  exact h L' (e.toMonoidHom.comp ψ) hψ' hker' hperf A hA hAI' h5 hsc z hz' hodd

namespace E6ThreeModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

@[expose] def GGE6ThreeRGen {R : Type} [Group R] (D : FrameData R) : Prop :=
  ∀ x : Fin Tag.E6.rank → ZMod 3, x ≠ 0 → ∀ J : Subgroup R, IsComponentOf J (ggFix (D.ad x)) →
    ∀ c ∈ D.Tor, (∃ k : ℕ, c ^ 3 ^ k = 1) →
      c ∈ Subgroup.closure (⋃ n ∈ (Subgroup.closure (Set.range D.nb) : Set R),
        (fun s => n * s * n⁻¹) '' {s : R | s ∈ J ∧ s ∈ D.Tor ∧ ∃ k : ℕ, s ^ 3 ^ k = 1})

end E6ThreeModel

end CFSG.StandardType
