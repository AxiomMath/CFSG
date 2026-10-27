module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Pi
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210SecAbs
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210SecComp

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open CFSG.Quasithin CFSG.Open Subgroup

theorem exists_pi_quotient {Q : Type} [Group Q] [Finite Q] {H K L : Subgroup Q}
    (hL : IsComponentModN K H L) (h3 : 3 ∣ K.relIndex L) (t : Fin 4 → Q) (ht : ∀ i, t i ∈ H)
    (hinj : Function.Injective fun i => conjSubgroup L (t i)) :
    ∃ (B : Fin 4 → Type) (_ : ∀ i, Group (B i)) (_ : ∀ i, Finite (B i)) (M : Subgroup ↥H)
      (θ : ↥M →* ∀ i, B i), Function.Surjective θ ∧ SimpleFactors B := by
  have : (K.subgroupOf H).Normal := hL.1
  obtain ⟨A, hq, hcomm, h3'⟩ := exists_four_components hL h3 t ht hinj
  obtain ⟨W, B, hG, hF, θ, hθ, hB⟩ := exists_pi_of_commuting_quasisimple A hq hcomm h3'
  refine ⟨B, hG, hF, W.comap (QuotientGroup.mk' (K.subgroupOf H)),
    θ.comp ((QuotientGroup.mk' (K.subgroupOf H)).subgroupComap W), ?_, hB⟩
  exact hθ.comp (MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective _))

end CFSG.LocalAnalysis.WeakClosure81.Asch210
