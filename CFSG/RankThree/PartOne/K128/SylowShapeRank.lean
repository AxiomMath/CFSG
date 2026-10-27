module

public import CFSG.RankThree.PartOne.K128.TorusShape

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG.RankThree.PartOne.K128

theorem two_le_pRank_of_sylowShape_sq {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {X : Type*} [Group X]
    [Finite X] (h : SylowShape p 2 e X) : 2 ≤ CFSG.pRank p X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
  obtain ⟨ε⟩ := h P.1 P.isPGroup' P.not_dvd_index
  have hdvd : p ∣ p ^ e := dvd_pow_self p (by omega)
  have hm : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  let Ψ₀ : (Fin 2 → Multiplicative (ZMod p)) →* (Fin 2 → Multiplicative (ZMod (p ^ e))) :=
    MonoidHom.pi fun i => (zmodIncl p (p ^ e) hdvd).comp (Pi.evalMonoidHom _ i)
  have hΨ₀ : Function.Injective Ψ₀ := by
    intro a b hab
    funext i
    exact zmodIncl_injective hdvd hm (congrFun hab i)
  let Ψ : (Fin 2 → Multiplicative (ZMod p)) →* X :=
    P.1.subtype.comp (ε.symm.toMonoidHom.comp Ψ₀)
  have hΨ : Function.Injective Ψ :=
    P.1.subtype_injective.comp (ε.symm.injective.comp hΨ₀)
  have hcard : Nat.card (Fin 2 → Multiplicative (ZMod p)) = p ^ 2 := by
    rw [Nat.card_pi]
    simp
  have hpow : ∀ z : Fin 2 → Multiplicative (ZMod p), z ^ p = 1 := fun z => by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← ofAdd_toAdd (z i), ← ofAdd_nsmul, ← ofAdd_zero]
    congr 1
    simp
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b) hpow hcard Ψ
    hΨ (H := ⊤) le_top

end CFSG.RankThree.PartOne.K1214
