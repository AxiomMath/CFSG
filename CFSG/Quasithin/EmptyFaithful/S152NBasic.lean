module

public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S152NQuot
public import CFSG.Quasithin.EmptyFaithful.S152NTrans
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

namespace S152N

theorem isElemAbelian_V154 {T Mc M : Subgroup G} (hs : Setting152 T Mc M) :
    IsElemAbelian 2 (V154 T Mc M) :=
  isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ hs.qtfe hs.mf.1.1)

theorem V154_le_T {T Mc M : Subgroup G} (hs : Setting152 T Mc M) : V154 T Mc M ≤ T :=
  (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ hs.qtfe hs.mf.1.1).2

theorem normalizer_V154_eq {T Mc M : Subgroup G} (hs : Setting152 T Mc M) :
    Subgroup.normalizer (V154 T Mc M : Set G) = M :=
  hs.mf.1.1.1.2 _ ⟨V154 T Mc M, V154_ne_bot hs.qtfe,
    B2F.isPGroup_of_isElemAbelian (isElemAbelian_V154 hs), rfl⟩ (le_normalizer_V154 T Mc M)

theorem isSylowTwoOf_hStar {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) : IsSylowTwoOf T H :=
  isSylowTwoOf_of_le151 hs.qtfe.sylow hH.1.1

theorem inf_eq_of_W3 {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (φ : OTwoQuot H ≃* W3) : M ⊓ H = T := by
  have hTM : T ≤ M := hs.mf.1.1.2
  rcases eq_or_eq_of_le (isSylowTwoOf_hStar hs hH) φ (le_inf hTM hH.1.1) inf_le_right with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left : H ≤ M) hH.2.1

theorem inf_normalizer_eq_of_W3 {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (φ : OTwoQuot H ≃* W3) :
    H ⊓ Subgroup.normalizer (V154 T Mc M : Set G) = T := by
  rw [normalizer_V154_eq hs, inf_comm]
  exact inf_eq_of_W3 hs hH φ

theorem relIndex_inf_eq_nine {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (φ : OTwoQuot H ≃* W3) :
    (H ⊓ Subgroup.normalizer (V154 T Mc M : Set G)).relIndex H = 9 := by
  rw [inf_normalizer_eq_of_W3 hs hH φ]
  exact relIndex_eq_nine (isSylowTwoOf_hStar hs hH) φ

theorem delta_commutator_ne_bot {T Mc M H A : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (φ : OTwoQuot H ≃* W3)
    (hc : Concl319 T M (V154 T Mc M) H True) (hA : A ∈ deltaSet H (V154 T Mc M))
    (hord : (A ⊓ pCoreOf 2 H).relIndex A = 2) (hAT : ¬ A ≤ T) :
    ⁅V154 T Mc M, A ⊓ pCoreOf 2 H⁆ ≠ ⊥ := by
  intro hbot
  have hVU : V154 T Mc M ≤ conjClosure (V154 T Mc M) H := le_conjClosure _ _
  have h1 : V154 T Mc M ≤ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
    le_centralizer_of_commutator_eq_bot (by rwa [Subgroup.commutator_comm] at hbot)
  have h2 := delta_fixed_eq (isSylowTwoOf_hStar hs hH) hA hord hc
  have h3 : V154 T Mc M ≤ Subgroup.centralizer (A : Set G) := by
    have : V154 T Mc M ≤ conjClosure (V154 T Mc M) H ⊓
        Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G) := le_inf hVU h1
    rw [← h2] at this
    exact this.trans inf_le_right
  have h4 : A ≤ Subgroup.centralizer (V154 T Mc M : Set G) := Subgroup.le_centralizer_iff.mp h3
  have h5 : A ≤ M := by
    rw [← normalizer_V154_eq hs]
    exact h4.trans (Subgroup.centralizer_le_normalizer _)
  exact hAT (by
    have : A ≤ M ⊓ H := le_inf h5 hA.1.1
    rwa [inf_eq_of_W3 hs hH φ] at this)

end S152N

end CFSG.Quasithin
