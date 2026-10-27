module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.FFC2Core
public import CFSG.Quasithin.Background.F918XAL2Basic

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin

theorem case7Twist_holds : Case7Twist := by
  intro V _ _ _ G L A hHyp hcase
  obtain ⟨-, -, hq, -⟩ := hHyp
  obtain ⟨-, -, ⟨α, π, hπ⟩, -⟩ := hcase
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hbij : Function.Bijective (π : ↥(alternatingGroup (Fin 7)) →* ↥L) :=
    AL2.bijective_of_surjective_of_quasisimple (A := ↥(alternatingGroup (Fin 7))) hq π hπ.1
  let e : ↥(alternatingGroup (Fin 7)) ≃* ↥L := MulEquiv.ofBijective π hbij
  have hZ : Subgroup.center ↥L = ⊥ :=
    AL2.center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp))
  refine ⟨twoClassMod_of_inner hZ ?_, Or.inl hZ⟩
  have hcard := FFC.card_mulAut_alternating_le (n := 7) (Or.inr le_rfl)
  rwa [← Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr e.toEquiv]

end CFSG.Quasithin.F918X
