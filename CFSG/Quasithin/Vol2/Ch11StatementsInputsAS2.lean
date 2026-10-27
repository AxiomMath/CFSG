module

public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Nlow
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique

@[expose] def AS_E_3_38_perH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V M H : Subgroup G) (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    E3.HypE322 T V → quasithinIsQTKECat G →
    IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M →
    IsHStar T M H → 1 < E1.nParam H → H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) →
    H ⊓ M ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (H ⊓ M) →
      E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞)

section Consequences

variable {G : Type} [Group G] [Finite G] {T V M H : Subgroup G}

theorem nParam_le_nPrime_of_perH (h : AS_E_3_38_perH) (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hyp : E3.HypE336 T V M) (hH : IsHStar T M H) :
    E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) := by
  by_cases hn : 1 < E1.nParam H
  · obtain ⟨h1, h2⟩ := hyp.local_structure H hH hn
    exact h G T V M H hV hV1 hs hnab hyp.hyp322 hyp.qtke hyp.unique hH hn h1 h2
  · exact (not_lt.1 hn).trans (by exact_mod_cast E3.one_le_nPrime (autI hV ⊤))

omit [Finite G] in
theorem isSylowIn_of_le_top (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) : IsSylowIn 2 T H := by
  refine ⟨hTH, hT.isPGroup, fun hd => hT.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top]
  exact Dvd.dvd.mul_right hd _

theorem min_le_nParam_of_le (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hyp : E3.HypE336 T V M)
    (hH : IsHStar T M H) (hCH : H ⊓ Subgroup.centralizer (V : Set G) ≤ M) :
    min (E3.wParam T V) (E3.rParam V) ≤ E1.nParam H := by
  refine not_lt.1 fun hlt => hH.2.1 ?_
  exact E3.e3_35_one hV hV1 hyp.hyp322 hyp.unique
    (isSylowIn_of_le_top hyp.hyp322.sylow hH.1.1) hCH inf_le_left hlt

theorem min_le_nParam_of_hypE336 (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hyp : E3.HypE336 T V M) (hH : IsHStar T M H) (hn : 1 < E1.nParam H) :
    min (E3.wParam T V) (E3.rParam V) ≤ E1.nParam H := by
  refine min_le_nParam_of_le hV hV1 hyp hH ?_
  have h1 := (hyp.local_structure H hH hn).1
  intro x hx
  have hx' : x ∈ H ⊓ Subgroup.normalizer (V : Set G) :=
    ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  rw [← h1] at hx'
  exact hx'.2

theorem as_e_3_38_of_perH (h : AS_E_3_38_perH) (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hyp : E3.HypE336 T V M) (hH : IsHStar T M H)
    (hCH : H ⊓ Subgroup.centralizer (V : Set G) ≤ M) :
    min (E3.wParam T V) (E3.rParam V) ≤ E1.nParam H ∧
      E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) :=
  ⟨min_le_nParam_of_le hV hV1 hyp hH hCH, nParam_le_nPrime_of_perH h hV hV1 hs hnab hyp hH⟩

end Consequences

end CFSG.Quasithin.ASInputs
