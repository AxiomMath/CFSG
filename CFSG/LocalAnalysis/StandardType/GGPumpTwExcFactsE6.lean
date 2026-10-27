module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwExcE6
public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGL45E67Center
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

private theorem l04fHE4a_autOrderAt_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : KGA.GGF4AutOrderAt p R') : KGA.GGF4AutOrderAt p R := by
  intro E hE hr
  let E' := E.map e.toMonoidHom
  have hE' : IsElemAbelian p E' := TableB.isElemAbelian_map hE e.toMonoidHom
  have hcardE : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective e.injective
  have hr' : p ^ 4 ≤ Nat.card E' := hr.trans hcardE.ge
  obtain ⟨hcard', h1152'⟩ := h E' hE' hr'
  refine ⟨hcardE.symm.trans hcard', ?_⟩
  have hmap := F4AutWeyl.ggAutomizer_map_eq e.injective ⊤ E
    (show E.map e.toMonoidHom = E' from rfl)
  rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  have hcardAut : Nat.card (ggAutomizer ⊤ E') = Nat.card (ggAutomizer ⊤ E) := by
    rw [hmap]
    exact Subgroup.card_map_of_injective (MulAut.congr _).injective
  exact hcardAut.symm.trans h1152'

theorem ggPumpTwExc_facts_E6
    {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.E6, 0, f⟩ fun R _ I _ =>
      Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        KGA.GGF4AutOrderAt 3 R := by
  intro Q hQ
  obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := charP_two_of_card hK
  have hpow : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h3' : ¬ 3 ∣ 2 ^ f - 1 := by
    intro hd
    have hsub : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h3 hd
    have heq : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [heq] at hsub
    norm_num at hsub
  have h3K : 3 ∣ Nat.card K + 1 := by rw [hK]; exact h3
  have h3K' : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3'
  have hcop : Nat.Coprime 3 (Nat.gcd 3 (Nat.card K - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (Nat.card K - 1))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3K')
  refine ⟨K, hField, hFinite, hK, hQ', ?_⟩
  refine ⟨TableBExc.center_recipeGroup_eq_bot .E6 K,
    ggCenterPrime_recipe_E6_of_coprime (K := K) Nat.prime_three (by norm_num) hcop, ?_, ?_⟩
  · exact fun φ hφ hφp =>
      mem_inn_of_mem_recipeID_E6 (K := K) hK Nat.prime_three (Or.inr h3') hφ hφp
  · exact l04fHE4a_autOrderAt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggPumpTwExc_autOrderAt_E6 (K := K) h3K)

end CFSG.StandardType

end
