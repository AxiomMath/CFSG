module

public import CFSG.Quasithin.EmptyFaithful.Gap6R0G
public import CFSG.Quasithin.EmptyFaithful.Gap6R0Stmt
public import CFSG.Quasithin.EmptyFaithful.S151cGlue

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6

variable {V : Type*} [CommGroup V] [Finite V] {X Tb : Subgroup (MulAut V)}

theorem central_of_residual (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) (hsqtk : IsQuotientOfSQTKTC ↥X) (hsyl : Tb ∈ sylow2Of X)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    (hres : ∀ A ∈ QhatStar X, ¬ ExcShape X A) :
    ∀ c ∈ fixV (fittingOf (Jhat X)), ∀ j ∈ Jhat X, j c = c := by
  intro c hc j hj
  have hle : Jhat X ≤ centSub (fixV (fittingOf (Jhat X))) := by
    refine iSup₂_le fun A hA => ?_
    rcases central_or_exc hV hsolv hO2 hsqtk hsyl hgen hA with h | h
    · intro a ha u hu
      exact h hu a ha
    · exact absurd h (hres A hA)
  exact hle hj c hc

end Gap6

section Ambient

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem commutator_eq_bot_of_central_autI (hVe : IsElemAbelian 2 (VZ T M))
    (hcen : ∀ c ∈ fixV (fittingOf (Jhat (autI hVe M))), ∀ j ∈ Jhat (autI hVe M), j c = c) :
    ⁅VZ T M ⊓ Subgroup.centralizer
        (preOn M (VZ T M) (fittingIn (JhatOn M (VZ T M))) : Set G), mJ154 T M⁆ = ⊥ := by
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  rw [JhatOn_eq_Jhat_autI M hVe] at hx
  set J := Jhat (autI hVe M) with hJ
  have hJX : J ≤ autOn M (VZ T M) := Jhat_le _
  have hFJ : fittingOf J ≤ autOn M (VZ T M) := (fittingOf_le J).trans hJX
  have hA : preOn M (VZ T M) (fittingIn J) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (preOn_le _ _ _).trans hMN
  have hAut : autI hVe (preOn M (VZ T M) (fittingIn J)) = fittingOf J := autOn_preOn hFJ
  set c : IntMod (VZ T M) hVe := IntMod.mk hVe ⟨x, hx.1⟩ with hcdef
  have hcval : c.val = x := rfl
  have hcf : c ∈ fixV (fittingOf J) := by
    rw [← hAut]
    exact (mem_fixV_autI hVe hA c).2 (by rw [hcval]; exact hx.2)
  have hmJ : m ∈ preOn M (VZ T M) J := by
    unfold mJ154 at hm
    rwa [JhatOn_eq_Jhat_autI M hVe] at hm
  have hmM : m ∈ M := (preOn_le _ _ _) hmJ
  have hjJ : convI hVe ⟨m, hMN hmM⟩ ∈ J := by
    have h1 := convI_mem_autI hVe (K := preOn M (VZ T M) J) hmJ (hMN hmM)
    have h2 : autI hVe (preOn M (VZ T M) J) = J := autOn_preOn hJX
    rwa [h2] at h1
  have h3 := hcen c hcf _ hjJ
  have h4 := congrArg IntMod.val h3
  rw [convI_apply_val] at h4
  have h5 : m * x * m⁻¹ = x := h4
  calc m * x = (m * x * m⁻¹) * m := by group
    _ = x * m := by rw [h5]

theorem centralOnComplement1512_of_residual (h1416 : StageLemma1416) (hres : Row24Residual) :
    CentralOnComplement1512 := by
  intro G _ _ T Mc M h hM
  have hVe : IsElemAbelian 2 (VZ T M) := isElemAbelian_VZ h hM.1.1
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have := h.simple
  refine commutator_eq_bot_of_central_autI hVe ?_
  exact Gap6.central_of_residual (IntMod.sq_eq_one) (isSolvable_autI_VZ h1416 h hM hVe)
    (pCoreOf_autI_VZ h hM hVe) (isQuotientOfSQTK_autI h.qtke h.nonabelian hM.1.1.1 hVe hMN)
    (autI_mem_sylow2Of h hM.1.1 hVe hMN) (gen_autI_VZ h hM.1.1 hVe)
    (hres G T Mc M h hM hVe)

end Ambient

end CFSG.Quasithin
