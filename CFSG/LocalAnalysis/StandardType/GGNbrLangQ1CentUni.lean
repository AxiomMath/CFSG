module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentUniLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniMark
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Transfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.SemisimpleCentralizers
open CFSG.StandardType.S2MathAs51642Interfaces


theorem q1CentUni_recipe {d m p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 1 ≤ m) (hd : 3 ≤ d) (hdq : (d, 2 ^ m) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hcop : ¬ p ∣ Nat.gcd d (2 ^ m + 1))
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))))
    (hAab : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
      (LargeEvenGUSet (Fin d) K (2 ^ m)))
    (u : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))) (huA : u ∈ A)
    (huord : orderOf u = p) (J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))))
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u)) :
    CFSG.StandardType.LargeEvenMarking J (fun _ _ _ IJ _ θJ =>
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θJ IJ) := by
  have hF := unitaryFieldData_of_card hm hK
  haveI : CharP K 2 := hF.charP
  obtain ⟨τ, hτ, hτQ⟩ := exists_unitaryInvolution hm hK
  obtain ⟨s, hsN, hs, rfl⟩ := q1CentUni_exists_lift hK hm τ hτ hτQ (hAI u huA)
  have hsp : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ ^ p = 1 := by
    rw [← huord]
    exact pow_orderOf_eq_one _
  have hodd : Odd (orderOf s) :=
    q1CentUni_odd_orderOf hK hm (hp.odd_of_ne_two hp2)
      (q1CentUni_pow_mem_scalars hK hm hd hdq hsN hsp)
  obtain ⟨C, hC, hCSU, hJeq⟩ := q1TorUni_component_lift τ hτ hτQ s hs hsN J hJ
  have hmark := q1TorUni_marking hK τ hτ hτQ s hs hodd C hC hCSU J hJeq
  have hlift : ∀ a ∈ A, ∃ (t : GL (Fin d) K) (htN : t ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K))),
      t ∈ Held.heldGU d K τ hτ ∧ t * s = s * t ∧
        a = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨t, htN⟩ := by
    intro a ha
    obtain ⟨t, htN, ht, rfl⟩ := q1CentUni_exists_lift hK hm τ hτ hτQ (hAI a ha)
    refine ⟨t, htN, ht, ?_, rfl⟩
    haveI : IsMulCommutative ↥A := hAab.1
    have hcomm := congrArg Subtype.val
      (mul_comm' (⟨_, huA⟩ : ↥A) (⟨_, ha⟩ : ↥A))
    exact q1CentUni_commute_of_projConj hK hm hd hdq τ hτ hτQ hp hcop hs ht hsN htN hsp
      hcomm
  refine largeEvenMarking_mono (fun _ _ _ _ _ _ hprop => ⟨?_, ?_⟩) hmark
  · intro a ha j hj
    obtain ⟨t, htN, ht, hts, rfl⟩ := hlift a ha
    exact (hprop t htN ht hts).1 j hj
  · intro a ha
    obtain ⟨t, htN, ht, hts, rfl⟩ := hlift a ha
    exact (hprop t htN ht hts).2

theorem q1RToral_centUni :
    Q1RToralTransfer (fun _ _ _ => True) (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twA)
      (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨-, hcop⟩, ht⟩ := hS
  dsimp only at ht
  subst ht
  obtain ⟨hn, hl2, hl2n⟩ := hlab
  change 1 ≤ n at hn
  change 2 ≤ l at hl2
  change l = 2 → 2 ≤ n at hl2n
  change ¬ p ∣ Nat.gcd (l + 1) (2 ^ n + 1) at hcop
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hn2 : 2 ≤ n := hl2n (by omega)
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_and (fun K _ _ hK A hAab hAI _ u huA huord J hJ =>
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩)
      (q1CentUni_recipe hK hn (by omega) hdq hp hp2 hcop A hAab hAI u huA huord J hJ)) hQ

theorem q1CenterPrimeToTwA_holds :
    GGBstarInnerDiagJInputOn (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twA) :=
  q1On_of_selectedTransfer
    (q1SelectedTransfer_of_toral (q1ToralActionTransfer_of_rToral q1RToral_centUni)
      (by
        intro G _ _ p B Bs x L D J hcfg P hP
        exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h, fun _ _ _ => trivial⟩) hP))

end CFSG.StandardType
