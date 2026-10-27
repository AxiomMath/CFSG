module

public import CFSG.LocalAnalysis.StandardType.GGTDModelBasic
public import CFSG.LocalAnalysis.StandardType.GGTDModelWeyl
public import CFSG.LocalAnalysis.StandardType.GGTDModelInner
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {K : Type} [Field K] {N m : ℕ} {L' : Type} [Group L']

theorem ggTDwit_holds_of_model (M : GGTDModel K N m L') {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (hm : 0 < m) (hN2 : 2 ≤ N) {A : Subgroup (MulAut L')}
    (hsc : GGTorusSelfCent p A) (hAT : ∀ a ∈ A, ∃ t, M.Act a t)
    (hN : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (ρ : Equiv.Perm (Fin (N + 1)) →* MulAut ↥A) (hρ : Function.Injective ρ)
    (hrange : ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hsw : ∀ k : Fin N, ρ (Equiv.swap k.castSucc k.succ) =
      ggConjAut A (hN (Equiv.swap k.castSucc k.succ))) :
    (ggTDwit M A hN).Holds (CartanMatrix.A N) (CoxeterMatrix.A N) :=
  ggTDHolds_of_parts (ggTDholdsOne M hN hAT hN2)
    (ggTDholdsTwo M hp hp2 hpm hm hN hAT hsc) (ggTDholdsThree M hp hp2 hpm hm hN hAT hsc)
    (ggTorusAutomizerClauses_of_permAut (ggTDn M) (fun _ => hN _) ρ hρ hrange hsw)

theorem ggTDtorData_of_model (M : GGTDModel K N m L') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (hm : 0 < m) (hN2 : 2 ≤ N) {A : Subgroup (MulAut L')}
    (hsc : GGTorusSelfCent p A) (hAT : ∀ a ∈ A, ∃ t, M.Act a t)
    (hN : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (ρ : Equiv.Perm (Fin (N + 1)) →* MulAut ↥A) (hρ : Function.Injective ρ)
    (hrange : ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hsw : ∀ k : Fin N, ρ (Equiv.swap k.castSucc k.succ) =
      ggConjAut A (hN (Equiv.swap k.castSucc k.succ))) :
    GGTorusTorData m N (CartanMatrix.A N) (CoxeterMatrix.A N) L' A :=
  ⟨ggTDwit M A hN, ggTDwit_holds_of_model M hp hp2 hpm hm hN2 hsc hAT hN ρ hρ hrange hsw⟩

end CFSG.StandardType
