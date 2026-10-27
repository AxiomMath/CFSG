module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeS5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18S5

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F7 CFSG.Quasithin.F53Push CFSG.Quasithin.F53Mod
  CosetGeom Equiv
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace SitSigma

variable {δ μ : Geo H M} {U : Subgroup G}

theorem sitSigma_false_of_O2Ubar_trivial (hBau3 : BaumannS3 G) (hBau5 : BaumannA5 G)
    (hA : F53Amalgam H M S) (hb : 1 < bMin H M) (h : SitSigma δ μ U) (hQ : Qv μ ≤ U)
    (hR : pCoreOf 2 U ≤ Qv δ) :
    False ∨ (Nonempty (OTwoQuot U ≃* Equiv.Perm (Fin 5)) ∧
      IsOrthSec U (zZero U (conjJoinOf U (quasithinOmegaOneCenter (Qv μ))))
        (conjJoinOf U (quasithinOmegaOneCenter (Qv μ)))) := by
  have hPn := stab_le_normalizer_of_le hQ
  have hPR := h.not_le_pCore hA hPn
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  have hP0 : Qv μ ⊓ U ≠ ⊥ := fun hb => by
    have : Zv μ ≤ Qv μ ⊓ U := fun z hz => h.R_le_P (h.zle hz)
    rw [hb] at this
    exact Zv_ne_bot hA μ (le_bot_iff.mp this)
  have hJ := not_le_core_of_noCharNormal hPH hP0 hnc
  obtain ⟨n, ψ, hn, -, hker⟩ := exists_quotHom hA δ
  have hφ := redHom_eq_one_iff ψ hker h hR
  rcases hn with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · obtain ⟨-, he5⟩ := h.shape_five hBau3 hBau5 hA hPn hR _ hφ
    rcases hss18S5_holds G _ _ _ hPH he5 hJ with hnat | horth
    · exact Or.inl (h.false_of_s5_natural hBau3 hBau5 hA hb hQ hR he5 hnat)
    · refine Or.inr ⟨he5, ?_⟩
      have hZ : conjJoinOf U (quasithinOmegaOneCenter (Qv μ)) =
          CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U := by
        rw [inf_eq_left.mpr hQ, conjClosure_eq_conjJoin]
        rfl
      rw [hZ]
      exact horth
  · exact Or.inl (h.false_of_S3 hBau3 hA hPn hR (shape_of_hom_three h.sylow _ hφ hPR))

end SitSigma

end CFSG.Quasithin.F53
