module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Chief
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm34AuxFitting
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm34AuxSmear

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34

variable {Γ : Type*} [Group Γ]

theorem isNormalIn_bot (H : Subgroup Γ) : IsNormalIn (⊥ : Subgroup Γ) H :=
  ⟨bot_le, (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup Γ).Normal)) ▸
    le_top⟩

theorem le_fittingSubgroupOf_of_chief {D M : Subgroup Γ} [Finite Γ] (hD : Group.IsSolvable D)
    (hM : IsChiefFactorOf D M ⊥) : M ≤ CFSG.fittingSubgroupOf D := by
  have hMD : M ≤ D := hM.2.1.1
  have hMs : Group.IsSolvable M := Thm211.isSolvable_of_le hMD hD
  have hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
    by_contra hnc
    push Not at hnc
    exact Thm32.not_isSolvable_of_chief_bot hM hnc hMs
  have : IsMulCommutative M := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  exact Thm210.le_fittingSubgroupOf_of_nilpotent hMD hM.2.1.2 inferInstance

variable [Finite Γ] {p : ℕ} {A G K D : Subgroup Γ}

theorem core34
    (H : Thm32.ChiefSetting p A G K D) (hD : cenIn G (A : Set Γ) = D) :
    CFSG.fittingSubgroupOf D = CFSG.fittingSubgroupOf (D ⊓ K) ∧
      IsChiefFactorOf D (CFSG.fittingSubgroupOf D) ⊥ ∧
      ∀ M : Subgroup Γ, IsChiefFactorOf D M ⊥ → M = CFSG.fittingSubgroupOf D := by
  have hmin : IsChiefFactorOf (G ⊔ A) (layerIn G) ⊥ := by
    rw [H.layerIn_eq]
    exact H.chief
  have hL : Lemma212.Hyp p A G := ⟨H.near, H.sol_eq_bot, hmin, H.prod_eq⟩
  have hKk : kOf G = K := hL.layerIn_eq.symm.trans H.layerIn_eq
  have hG1 : G ≠ ⊥ := fun h0 => H.K_ne_bot (le_bot_iff.mp (h0 ▸ H.K_le))
  have hs : SemisimpleAction p A (kOf G) := hL.semisimpleAction
  have hDsol : Group.IsSolvable ↥D := hD ▸ H.near.solvable_cen
  have hDG : D ≤ G := H.D_le
  have hDK : D ⊓ K = cenIn (kOf G) (A : Set Γ) := by
    rw [hKk, ← hD, inf_comm]
    exact Thm211.inf_cenIn_eq H.K_le
  have hFle : CFSG.fittingSubgroupOf D ≤ D := Subgroup.map_subtype_le _
  have hFK : CFSG.fittingSubgroupOf D ≤ K := by
    have := fittingSubgroupOf_cenIn_le_kOf H.near H.sol_eq_bot hG1
    rw [hD, hKk] at this
    exact this
  have hDnorK : D ≤ Subgroup.normalizer (K : Set Γ) := hDG.trans H.G_le_nor_K
  have hFeq : CFSG.fittingSubgroupOf D = CFSG.fittingSubgroupOf (D ⊓ K) := by
    refine le_antisymm ?_ ?_
    · exact Thm210.le_fittingSubgroupOf_of_nilpotent (le_inf hFle hFK)
        (inf_le_left.trans (Thm210.le_normalizer_fittingSubgroupOf D))
        (Thm210.isNilpotent_fittingSubgroupOf D)
    · refine Thm210.le_fittingSubgroupOf_of_nilpotent
        ((Subgroup.map_subtype_le _).trans inf_le_left) ?_
        (Thm210.isNilpotent_fittingSubgroupOf _)
      exact fun d hd => mem_normalizer_fittingSubgroupOf
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hd, hDnorK hd⟩)
  have htrans : ∀ J₁ ∈ lcal (kOf G), ∀ J₂ ∈ lcal (kOf G), ∃ d ∈ D,
      smear J₂ A = (smear J₁ A).map (MulAut.conj d).toMonoidHom := by
    intro J₁ h₁ J₂ h₂
    obtain ⟨d, hd, h⟩ := exists_smear_conj hL (hL.lcal_kOf ▸ h₁) (hL.lcal_kOf ▸ h₂)
    exact ⟨d, hD ▸ hd, h⟩
  have hnormal : ∀ N : Subgroup Γ, N ≤ D ⊓ K → D ≤ Subgroup.normalizer (N : Set Γ) →
      N ≠ ⊥ → CFSG.fittingSubgroupOf D ≤ N := by
    intro N hN hND hN1
    rw [hFeq, hDK]
    rw [hDK] at hN
    exact fittingSubgroupOf_cenIn_le_of_normal hs (D := D)
      (hDK ▸ inf_le_left) htrans hN hND hN1
  obtain ⟨J₀, hJ₀⟩ : ∃ J, J ∈ lcal (kOf G) := hL.lcal_kOf ▸ hL.exists_lcal
  have hne : CFSG.fittingSubgroupOf D ≠ ⊥ := by
    rw [hFeq, hDK]
    exact fittingSubgroupOf_cenIn_ne_bot hs hJ₀
  refine ⟨hFeq, ⟨isNormalIn_bot D, ⟨hFle, Thm210.le_normalizer_fittingSubgroupOf D⟩,
    bot_lt_iff_ne_bot.mpr hne, fun K' hK' _ hK'F => ?_⟩, fun M hM => ?_⟩
  · by_cases h0 : K' = ⊥
    · exact Or.inl h0
    · exact Or.inr (le_antisymm hK'F
        (hnormal K' (hK'F.trans (le_inf hFle hFK)) hK'.2 h0))
  · have hMF : M ≤ CFSG.fittingSubgroupOf D := le_fittingSubgroupOf_of_chief hDsol hM
    have hM1 : M ≠ ⊥ := hM.2.2.1.ne'
    exact le_antisymm hMF (hnormal M (hMF.trans (le_inf hFle hFK)) hM.2.1.2 hM1)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34
