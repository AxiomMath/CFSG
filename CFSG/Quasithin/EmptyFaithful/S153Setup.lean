module

public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.EmptyFaithful.S14112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Hyp153 (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G) : Prop where
  qtfe : quasithinQTFE14Cat G T Mc
  mf : IsMf T Mc M
  ofour : IsOFourPlusAction M (VZ T M)

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem inM (h : Hyp153 G T Mc M) : InM T M := h.mf.1.1

theorem T_le (h : Hyp153 G T Mc M) : T ≤ M := h.inM.2

theorem ne_mc (h : Hyp153 G T Mc M) : M ≠ Mc := h.mf.2.1

theorem card_VZ (h : Hyp153 G T Mc M) : Nat.card (VZ T M) = 16 := h.ofour.1

theorem isHv_of_inM' (h : Hyp153 G T Mc M) {K : Subgroup G} (hK : InM T K) : IsHv T K := by
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have := isHv_of_inM h.qtfe.qtke.2.1 S (hS ▸ hK)
  rwa [hS] at this

theorem twoReduced (h : Hyp153 G T Mc M) : IsTwoReducedIn M (VZ T M) ∧ VZ T M ≤ T := by
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.T_le
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S, hSM⟩
  have hVred : IsTwoReducedIn M (VZ T M) := by
    have := isTwoReducedIn_conjClosure M S hSM hF le_rfl
    rwa [hS] at this
  refine ⟨hVred, ?_⟩
  have := le_sylow_of_isTwoReducedIn S hSM hVred
  rwa [hS] at this

theorem elemAbelian (h : Hyp153 G T Mc M) : IsElemAbelian 2 (VZ T M) := h.twoReduced.1.2.2.1

theorem VZ_le_T (h : Hyp153 G T Mc M) : VZ T M ≤ T := h.twoReduced.2

theorem le_normalizer (h : Hyp153 G T Mc M) : M ≤ Subgroup.normalizer (VZ T M : Set G) :=
  h.twoReduced.1.2.1

theorem isSylowTwoOf (h : Hyp153 G T Mc M) : IsSylowTwoOf T M := by
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have := isSylowTwoOf_of_sylow S (H := M) (hS ▸ h.T_le)
  rwa [hS] at this

theorem Z_le_VZ (_h : Hyp153 G T Mc M) : quasithinOmegaOneCenter T ≤ VZ T M :=
  le_conjClosure _ _

theorem exists_C₂ (h11 : StageLemma14111) (h : Hyp153 G T Mc M) :
    ∃ C₂ : Subgroup G, Lemma14111Concl T Mc C₂ ∧ Subgroup.normalizer (C₂ : Set G) ≤ M := by
  obtain ⟨C₂, hC⟩ := h11 G T Mc h.qtfe
  have hC₂p : IsPGroup 2 C₂ := h.qtfe.sylow.1.to_le (hC.2.1.trans inf_le_left)
  obtain ⟨Mf, hMf, hNMf⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (C₂ : Set G)) ⟨C₂, hC.1, hC₂p, rfl⟩
  have hMfIs : IsMf T Mc Mf := isMf_of_lemma14111Concl h.qtfe hC hMf hNMf
  have hMfeq : Mf = M := h.mf.1.2 Mf hMfIs.1.1 (hMfIs.2.2 M h.inM h.ne_mc)
  exact ⟨C₂, hC, hMfeq ▸ hNMf⟩

end Hyp153

end CFSG.Quasithin
