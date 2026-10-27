module

public import CFSG.Quasithin.EmptyFaithful.Gap6R2Base
public import CFSG.Quasithin.EmptyFaithful.S1519

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6R2

variable {G : Type} [Group G] [Finite G]

theorem vE_le_omegaOneCenter_J1 {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hMf : IsMf T Mc M) (h157 : Lemma1517Concl T Mc M) (h15 : Lemma1515Concl T Mc M)
    (h159 : Lemma1519Concl T Mc M) : vE T Mc M ≤ omegaOneCenterOf (thompsonJi T 1) := by
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hTM : (S : Subgroup G) ≤ M := hMf.1.1.2
  have hred : IsTwoReducedIn M (V154 (S : Subgroup G) Mc M) := h15.reduced
  have hVelem : IsElemAbelian 2 (V154 (S : Subgroup G) Mc M) := hred.2.2.1
  have hrank : 1 < CFSG.Open.pRank 2 (S : Subgroup G) := one_lt_pRank_T h hMf h157
  have hJT : thompsonJ (S : Subgroup G) ≤ thompsonJi (S : Subgroup G) 1 := by
    rw [thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_mono (Nat.zero_le 1) hrank
  have hJcent : thompsonJ (S : Subgroup G) ≤
      Subgroup.centralizer (V154 (S : Subgroup G) Mc M : Set G) :=
    le_centralizer_of_commutator_eq_bot h159.one_commute
  have hJV : thompsonJ (S : Subgroup G) ≤
      M ⊓ Subgroup.centralizer (V154 (S : Subgroup G) Mc M : Set G) :=
    le_inf ((thompsonJ_le_self151 _).trans hTM) hJcent
  have hVE : V154 (S : Subgroup G) Mc M ≤ omegaOneCenterOf (thompsonJ (S : Subgroup G)) :=
    (lemma_14_1_2_one S hTM hred hJV).1
  intro x hx
  exact Subgroup.subset_closure
    ⟨⟨hJT (omegaOneCenterOf_le_self _ (hVE hx.1)), hx.2⟩, hVelem.2 x hx.1⟩

end Gap6R2

end CFSG.Quasithin
