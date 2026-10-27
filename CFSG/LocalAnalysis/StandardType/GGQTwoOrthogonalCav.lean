module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalMarking
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalFixedAutomizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalMovingAutomizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthNonFull
public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap

public noncomputable section

namespace CFSG.StandardType.QTwoOrthogonalCav

open Module Multiplicative Polynomial CFSG.Assembly
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal

theorem four_dvd_component_of_full_three_card
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) (hn : 4 ≤ n)
    {E : Subgroup ↥(orthDerived Q)} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ n) {t : ↥(orthDerived Q)} (htE : t ∈ E)
    (ht3 : orderOf t = 3) {J : Subgroup ↥(orthDerived Q)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({t} : Set ↥(orthDerived Q)))) :
    4 ∣ Nat.card (ggAutomizer J E) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A := E.map (orthDerived Q).subtype
  have hAΩ : A ≤ orthDerived Q := Subgroup.map_subtype_le E
  have hAE : CFSG.Open.IsElemAbelian 3 A := hE.map (orthDerived Q).subtype
  have hcardA : Nat.card A = 3 ^ n := by
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective, hcard]
  obtain ⟨Δ⟩ := exists_full_torus_data hK hQ hdim hn hAΩ hAE hcardA
  have htA : (t : V ≃ₗ[K] V) ∈ A := Subgroup.mem_map_of_mem _ htE
  obtain ⟨f₀, hτ⟩ : ∃ f₀, Δ.τ f₀ = (t : V ≃ₗ[K] V) := by
    rw [← Δ.τ_range] at htA
    exact htA
  have ht1 : Δ.τ f₀ ≠ 1 := by
    intro h
    have h1 : t = 1 := Subtype.ext (hτ.symm.trans h)
    rw [h1, orderOf_one] at ht3
    omega
  have hx := Δ.oddOrderIsometry (by decide) hQ hAΩ f₀
  have hh : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (Δ.τ f₀).toLinearMap :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_mem hx (by norm_num [hK]) ht1
  letI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  letI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  letI : Nontrivial ↥J := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  have hJns : ¬ Group.IsSolvable ↥J := Group.IsPerfect.not_isSolvable (G := ↥J)
  have hcases := ggQ2OrthNonFull_comp_cases hK hQ hdim ht3 hJ
  rw [← hτ] at hcases
  have hfour : 4 ∣ Nat.card (ggAutomizer (J.map (orthDerived Q).subtype) A) := by
    rcases hcases with hmov | ⟨hfix, hcond⟩
    · have hns : ¬ Group.IsSolvable
          ↥((specialBlock Q (Δ.τ f₀) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)) := by
        rw [← hmov]
        exact hJns
      have h4 := four_dvd_moving_of_data hK hQ hAΩ Δ f₀ hh hns
      rw [hmov, Subgroup.subgroupOf_map_subtype]
      exact h4
    · rcases hcond with h6 | ⟨h4, hminus⟩
      · rw [hfix, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hx.supportedFixedDerived_le_orthDerived]
        exact four_dvd_fixed_of_full_data hQ hdim hAΩ Δ f₀ h6
      · exact False.elim (hminus (full_data_fixed_four_plus hK hQ hdim hAΩ Δ f₀ h4))
  have hcardAut : Nat.card (ggAutomizer (J.map (orthDerived Q).subtype) A) =
      Nat.card (ggAutomizer J E) := by
    rw [F4AutWeyl.ggAutomizer_map_eq (orthDerived Q).subtype_injective J E rfl,
      Subgroup.card_map_of_injective (MulAut.congr _).injective]
  rwa [hcardAut] at hfour

theorem four_dvd_image_of_full_orthogonal
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .D ∨ lab.tag = .twD) (hr : 4 ≤ lab.rank)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    4 ∣ Nat.card (ggAutomizer
      ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L)) (ggGamma L hN).range) := by
  obtain ⟨K, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, Q, hK, hQ, hdim,
    θ, E, t, hZ, hE, hcardE, hmap, htE, _, _, horder, hJ⟩ :=
    exists_orthogonal_full_component hS hq2 htag hr hmark hidx hN
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module K V := hMod
  letI : FiniteDimensional K V := hFinDim
  have hfour := four_dvd_component_of_full_three_card hK hQ hdim hr hE hcardE htE horder hJ
  rwa [card_automizer_eq_original_image hS.2.1.1 hN θ hZ hmap] at hfour

end CFSG.StandardType.QTwoOrthogonalCav

end
