module

public import CFSG.Quasithin.Background.SmithC27B51
public import CFSG.Quasithin.Background.C126NatDSL2

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem three_of_lin2 (h : Hyp27 H R M K) (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    (hchi : IsChiBlock2 H K) {n : ℕ} (hn : 1 < n) (hL : IsLin2Type K n) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hVdef
  have hs : StarHyp R K V := h.starHyp
  have hK : IsShort2 K := hchi.1.1
  have hJ : IsSylowTwoOf (autOn (thompsonJ R) V) (autOn K V) :=
    sylow_thompsonJ_of_lin2 h hs hA21 hB51 hK hn hL
  have hZ := center_eq_bot_of_lin2 hL
  obtain ⟨eq⟩ := hs.quotEquiv hZ
  obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := id hL
  let eK : ↥(autOn K V) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    eq.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hstar := normalizer_J_star_le h hs
  have hJM : autOn (thompsonJ R) V ≤ autOn (M ⊓ K) V := fun x hx =>
    hstar ⟨hJ.1 hx, Subgroup.le_normalizer hx⟩
  have hMK : autOn (M ⊓ K) V ≤ autOn K V := autOn_mono' inf_le_right
  rcases C126.Nat.sylow_dichotomy_of_equiv_sl2 (by omega) hFc eK hJ hMK hJM with h1 | h1
  · exact absurd h1 (autOn_MK_ne h hs)
  · have hB : IsBorelIn (autOn K V) (autOn (M ⊓ K) V) :=
      ⟨autOn (thompsonJ R) V, hJ, le_antisymm (le_inf hMK h1) hstar⟩
    exact Or.inl ⟨hchi, Or.inl ⟨⟨n, hn, hL⟩, hJ, hB⟩⟩

end CFSG.Quasithin.SmithC27
