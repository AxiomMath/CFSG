module

import CFSG.Quasithin.MS93.S33Semi
public import CFSG.Quasithin.MS93.S34Ext
public import CFSG.Quasithin.MS93.S4ASL3
import CFSG.Quasithin.MS93.S33Lin

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Semi

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F] [Finite F]
  {ψ : ↥K →* ↥(StatedSL 3 F)}

omit [Finite F] in
theorem exists_semilinear_natVec (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia K V ⊥ ψ false 1) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxK : x ∈ Subgroup.normalizer (K : Set G)) :
    ∃ (f : (Fin 3 → F) → (Fin 3 → F)) (σ : F →+* F),
      (∀ v v' : ↥V, (v' : G) = x * v * x⁻¹ → natVec hψ v' = f (natVec hψ v)) ∧
      ∀ (c : F) (y : Fin 3 → F), f (c • y) = σ c • f y := by
  have hspec := Classical.choose_spec hψ.2.2
  set β := Classical.choose hψ.2.2 with hβdef
  have hβs : Function.Surjective β := hspec.1
  have hβker : β.ker = (⊥ : Subgroup G).subgroupOf V := hspec.2.1
  have hβψ : ∀ a : ↥K, IsCoordAct β a ((ψ a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec :=
    fun a u v huv => by simpa [moduleAct] using hspec.2.2 a u v huv 0
  have hnat : ∀ v : ↥V, natVec hψ v = Multiplicative.toAdd (β v) 0 := fun v => rfl
  obtain ⟨f, hf⟩ := S33.exists_isCoordAct' hβs hβker hxV
  obtain ⟨f', hf'⟩ := S33.exists_isCoordAct' hβs hβker (inv_mem hxV)
  obtain ⟨σ, hσ⟩ := S33.exists_semilinear hψs hψ.1 hβs hβψ hxV hxK hf hf'
  refine ⟨f, σ, fun v v' hvv' => ?_, hσ⟩
  rw [hnat, hnat]
  exact hf v v' hvv'

end Semi

end CFSG.Quasithin.MS93.S34F
