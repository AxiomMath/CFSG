module

public import CFSG.Quasithin.EmptyFaithful.S153D33
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.S153Nine

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem commutator_V₂_Yplus (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    ⁅V₂, oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))⁆ = V₂ := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, y, hy, hyY, hyL, hyord⟩ := h.exists_mem_Yplus_acts h113 D
  set Yp : Subgroup G := oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) with hYp
  set x' := convI hV ⟨y, hy⟩ with hx'
  have hx'odd : Odd (orderOf x') := by rw [hyord]; decide
  have hx'1 : x' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyord
    exact absurd hyord (by norm_num)
  have hfpf : ∀ u ∈ commV L₂, u ≠ 1 → x' u ≠ u := fun u hu hu1 hxu =>
    hx'1 (eq_one_of_odd_of_fixed hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hyL hx'odd hu hu1
      hxu)
  have hfpfG : ∀ u ∈ V₂, u ≠ 1 → y * u * y⁻¹ ≠ u := by
    intro u hu hu1 hyu
    rw [hV₂] at hu
    obtain ⟨w, hw, rfl⟩ := (mem_map_inclMod_iff hV).1 hu
    refine hfpf w hw (fun hw1 => hu1 (by rw [hw1]; rfl)) (IntMod.val_injective ?_)
    rw [hx', convI_apply_val]
    exact hyu
  have hYpM : Yp ≤ M ⊓ Subgroup.centralizer (V₁ : Set G) :=
    (oTwoUpper_le _).trans (inf_le_inf_right _ (Y153_le Mc M))
  have hMN : M ⊓ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (V₂ : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right (VZ T M) (M ⊓ Subgroup.centralizer (V₁ : Set G))
    rwa [D.comm₂] at this
  have hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G) := hYpM.trans hMN
  have hN2 : ⁅V₂, Yp⁆ ≤ V₂ := Subgroup.le_normalizer_iff_commutator_le_left.mp hYN
  have hyN : y ∈ Subgroup.normalizer ((⁅V₂, Yp⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right V₂ Yp hyY
  have hV₂ne : V₂ ≠ ⊥ := by
    intro hb
    have := D.card₂
    rw [hb, Subgroup.card_bot] at this
    omega
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₂, u ≠ 1 := by
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₂ne
    exact ⟨u, hu, fun h1 => hu1 (Subtype.ext h1)⟩
  set u₀ : G := ⁅u, y⁆ with hu₀
  have hu₀N : u₀ ∈ ⁅V₂, Yp⁆ := Subgroup.commutator_mem_commutator hu hyY
  have hu₀V : u₀ ∈ V₂ := hN2 hu₀N
  have hu₀1 : u₀ ≠ 1 := by
    intro h1
    apply hfpfG u hu hu1
    have h2 : u * y = y * u := commutatorElement_eq_one_iff_mul_comm.mp h1
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  set u₁ : G := y * u₀ * y⁻¹ with hu₁
  have hu₁N : u₁ ∈ ⁅V₂, Yp⁆ := (Subgroup.mem_normalizer_iff.mp hyN u₀).mp hu₀N
  have hu₁1 : u₁ ≠ 1 := by
    intro h1
    apply hu₀1
    calc u₀ = y⁻¹ * (y * u₀ * y⁻¹) * y := by group
      _ = 1 := by rw [show y * u₀ * y⁻¹ = 1 from h1]; group
  have hu₁u₀ : u₁ ≠ u₀ := hfpfG u₀ hu₀V hu₀1
  have hsub : ({1, u₀, u₁} : Set G) ⊆ ((⁅V₂, Yp⁆ : Subgroup G) : Set G) := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hu₀N
    · exact hu₁N
  have h3 : ({1, u₀, u₁} : Set G).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, u₀, u₁, hu₀1.symm, hu₁1.symm, hu₁u₀.symm, rfl⟩
  have hcard3 : 3 ≤ Nat.card (⁅V₂, Yp⁆ : Subgroup G) := by
    calc 3 = ({1, u₀, u₁} : Set G).ncard := h3.symm
      _ ≤ (((⁅V₂, Yp⁆ : Subgroup G) : Set G)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (⁅V₂, Yp⁆ : Subgroup G) := (Nat.card_coe_set_eq _).symm
  have hdvd : Nat.card (⁅V₂, Yp⁆ : Subgroup G) ∣ 4 := D.card₂ ▸ Subgroup.card_dvd_of_le hN2
  have h4 : Nat.card (⁅V₂, Yp⁆ : Subgroup G) = 4 := by
    have hle4 : Nat.card (⁅V₂, Yp⁆ : Subgroup G) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    rcases (by omega : Nat.card (⁅V₂, Yp⁆ : Subgroup G) = 3 ∨ Nat.card (⁅V₂, Yp⁆ : Subgroup G) = 4) with h3' | h4'
    · rw [h3'] at hdvd
      norm_num at hdvd
    · exact h4'
  exact Subgroup.eq_of_le_of_card_ge hN2 (by rw [D.card₂, h4])

end Hyp153

namespace S153D

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_mono_152 {p : ℕ} {V W : Subgroup G} (h : IsElemAbelian p W) (hle : V ≤ W) :
    IsElemAbelian p V := CFSG.Open.IsElemAbelian.mono h hle

omit [Finite G] in
theorem opResidual_two_oTwoUpper_152 (X : Subgroup G) :
    opResidual 2 (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (opResidual_le 2 _) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_opResidual_of_coprime (Subgroup.subset_closure hx) (Nat.coprime_two_right.mpr hx.2)

theorem input15311Eight_of_stages (h113 : StageLemma14113) : Input15311Eight := by
  intro G _ _ T Mc M V₁ V₂ Yp t h I hI
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYp : oTwoUpper Yp = Yp := h.oTwoUpper_eq
  have hX : opResidual 2 Yp = Yp := by
    have := opResidual_two_oTwoUpper_152 Yp
    rwa [hYp] at this
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p I) ≤ 2 := fun p hp hp2 =>
    (CFSG.SectionRank.pRank_mono hp.one_lt (pCoreOf_le p I)).trans
      (pRank_le_two_of_pCoreOf_ne_bot h.hyp.qtfe.qtke hI.1.2 hp hp2)
  obtain ⟨V₀, hV₀, hcomm, hV₀I, hV₀M⟩ : ∃ V₀ : Subgroup G, IsElemAbelian 2 V₀ ∧ ⁅V₀, Yp⁆ = V₀ ∧
      V₀ ≤ I ∧ Subgroup.centralizer (V₀ : Set G) ≤ M := by
    rcases h.cases with hY | h2
    · have hHv : IsHv T M := h.hyp.isHv_of_inM' h.hyp.inM
      refine ⟨VZ T M, h.hyp.elemAbelian, ?_, ?_, ?_⟩
      · rw [hY]
        exact h.hyp.commutator_VZ_Y153 h113
      · refine (h.hyp.VZ_le_Y153 h113).trans ?_
        rw [← hY]
        exact hYI
      · intro x hx
        have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.centralizer_le_normalizer _ hx
        rwa [← hHv] at hxN
    · have h3 := h.lemma_15_3_11_three h113 h2 hI
      have hcomm : ⁅V₂, Yp⁆ = V₂ := by
        rw [h2.2]
        exact h.hyp.commutator_V₂_Yplus h113 h.decomp
      have hV₂C : V₂ ≤ Subgroup.centralizer (V₁ : Set G) := by
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have := h.hyp.elemAbelian.1
        exact setLike_mul_comm (h.decomp.le₁ hw) (h.decomp.le₂ hv)
      have hV₂N : V₂ ≤ Subgroup.normalizer (Yp : Set G) := by
        intro v hv
        have hvM : v ∈ M := h.hyp.T_le (h.hyp.VZ_le_T (h.decomp.le₂ hv))
        have hvY : v ∈ Subgroup.normalizer (Y153 Mc M : Set G) := le_normalizer_Y153 Mc M hvM
        have hvC : v ∈ Subgroup.normalizer
            ((Subgroup.centralizer (V₁ : Set G) : Subgroup G) : Set G) :=
          Subgroup.le_normalizer (hV₂C hv)
        have hv' : v ∈ Subgroup.normalizer
            ((Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) : Subgroup G) : Set G) :=
          Subgroup.inf_normalizer_le_normalizer_inf ⟨hvY, hvC⟩
        rw [h2.2]
        exact normalizer_le_normalizer_oTwoUpper _ hv'
      refine ⟨V₂, isElemAbelian_mono_152 h.hyp.elemAbelian h.decomp.le₂, hcomm, ?_, ?_⟩
      · refine le_trans ?_ hYI
        rw [← hcomm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp hV₂N
      · intro x hx
        exact h3.2.2.1 (Subgroup.centralizer_le_normalizer _ hx)
  have hcent : V₀ ≤ Subgroup.centralizer (fusionOddCoreOf I : Set G) :=
    a126_one hYI hX hV₀I (B2F.isPGroup_of_isElemAbelian hV₀) hcomm hrank
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hV₀)
  have hOM : oddCoreIn I ≤ M ⊓ I := by
    intro x hx
    refine ⟨hV₀M ?_, oddCoreIn_le I hx⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hcent hv)) x hx).symm
  exact CharTwo.eq_bot_of_odd_card (h.hyp.charTwo_inf h.decomp (le_sup_right.trans hI.1.1)) hOM
    (inf_le_right.trans (le_normalizer_oddCoreIn I)) (odd_card_oddCoreIn I)

end S153D

end CFSG.Quasithin
