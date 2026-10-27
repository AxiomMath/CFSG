module

public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.B69Mod
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.FixedLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Quasithin
open scoped Matrix

theorem card_fixedPointSubgroup_sylow_of_realizes {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥)
    (hline : ∃ (U : Subgroup ↥Γ) (e : ι → K), IsPGroup p ↥U ∧
      ∀ v : ι → K, (∀ u ∈ U, ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) →
        v ∈ Submodule.span K {e})
    (S : Sylow p ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = Nat.card K := by
  obtain ⟨π, hRV⟩ := hR
  obtain ⟨U, e, hU, hfix⟩ := hline
  have hinj : Function.Injective π := CFSG.Quasithin.B69.natRealizes_injective hRV
  have hle : (S : Subgroup ↥H) ≤ π.range := fun s _ => MonoidHom.mem_range.mpr (hRV.1 s)
  let S' : Sylow p ↥Γ := S.comapOfInjective π hinj hle
  have hS' : (S' : Subgroup ↥Γ) = (S : Subgroup ↥H).comap π :=
    S.coe_comapOfInjective π hinj hle
  have h1 := card_fixedPointSubgroup_eq_of_realizesVia hRV (S : Subgroup ↥H)
  have h2 := card_fixed_sylow_eq_card p U hU e hfix S'
  rw [hS'] at h2
  exact h1.trans h2

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
