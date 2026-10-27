module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveOrbitC
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveRedGrp
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveRedIso
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveRedBack
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveReduced

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.E2.E22N CFSG.LocalAnalysis.UniquenessCase.UC22
  Subgroup

theorem fourFive_component_dichotomy {Q : Type} [Group Q] [Finite Q] {j : ℕ} (hj : 1 ≤ j)
    {T N J : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hN : FourFiveNMN N) (hJ : IsComponentOf J N)
    (hF : fourFiveFAS j (↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)))
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) :
    J ≤ E1.eGen j ⊤ T Ω ⊔ T ∨ J ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set Q) := by
  obtain ⟨X, hX⟩ : ∃ X : Subgroup Q, X = ⨆ t ∈ T, CFSG.Quasithin.A1b.conjSub t J := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Subgroup Q, U = X ⊔ T := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Subgroup Q, C = U ⊓ Subgroup.centralizer (X : Set Q) := ⟨_, rfl⟩
  have hJX : J ≤ X := fourFive_le_orbit hX
  have hXcomp : E111R.IsComp X J := fourFive_orbit_isComp hN hJ hX
  have hXnc : ¬ IsMulCommutative X := fourFive_orbit_nonabelian hN hJ hX
  have hXZ : X ⊓ Subgroup.centralizer (X : Set Q) = ⊥ := fourFive_orbit_inf_centralizer hN hJ hX
  have hTU : T ≤ U := hU ▸ le_sup_right
  have hXU : X ≤ U := hU ▸ le_sup_left
  have hJU : J ≤ U := hJX.trans hXU
  have hUnorm : U ≤ Subgroup.normalizer (X : Set Q) :=
    hU ▸ sup_le Subgroup.le_normalizer (fourFive_le_normalizer_orbit hX)
  haveI hXn : (X.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXU).mpr hUnorm
  haveI hCn : (C.subgroupOf U).Normal := hC ▸ fourFive_normal_inf_centralizer hUnorm
  have hCT : C ≤ T := fourFive_orbit_centralizer_le hT hN hJ hX hU hC
  have hXC : X ⊓ C = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ X ⊓ Subgroup.centralizer (X : Set Q) := ⟨hx.1, (hC ▸ hx.2).2⟩
    rwa [hXZ] at this
  have hTUS : IsSylowIn 2 T U := fourFive_isSylowIn_of_le hT hTU
  have hmin : ∀ K : Subgroup Q, K ≤ X → (K.subgroupOf U).Normal → K = ⊥ ∨ K = X :=
    fun K hKX hK => fourFive_orbit_minimal hN hJ hX hU hKX hK
  have hRed := fourFive_reduced_quotient hTUS hU hmin hXnc hXZ hC
  have hJbar := fourFive_isComp_quotient hXU hXC hXcomp
  obtain ⟨e⟩ := fourFive_autQuot_equiv_quotient hTU hJX hXU hXC
  have hFbar := fourFive_fas_mulEquiv e hF
  exact fourFive_dichotomy_of_quotient hT hTU hCT hJU
    (fun Ωq hΩq => fourFive_reduced_dichotomy hj hRed hJbar hFbar hΩq) hΩ

end CFSG.LocalAnalysis.WeakClosure81
