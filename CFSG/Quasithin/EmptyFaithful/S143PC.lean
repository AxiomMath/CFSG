module

public import CFSG.Quasithin.EmptyFaithful.S143PB
public import CFSG.Quasithin.EmptyFaithful.S143NA2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

@[expose] def Lemma14322Tail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
      Subgroup.centralizer (A : Set G) = A → Concl14321 T M →
        ∀ d : G, dOf T M = Subgroup.zpowers d → orderOf d = 4 → False

theorem lemma_14_3_22_of_tail
    (h : Lemma14322Tail) : Lemma14322 := by
  intro G _ _ T M g A t c c18 c19 hΓ c21
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  obtain ⟨x, z, a, r1, hS⟩ := c.exists_setup hrW hrV hr2 c18.a
  have htT := c18.b.t_mem
  have htRQ := c18.b.t_nmem
  obtain ⟨y, cm, Vl, Vr, s, hM, hP, hVl, hVr⟩ := hS.exists_KModel3 htT htRQ
  by_cases hDZ : dOf T M = quasithinOmegaOneCenter T
  · refine ⟨hDZ, ?_⟩
    have hZU : quasithinOmegaOneCenter T ≤ uOfL22 T M :=
      (Hyp1281Two.omegaOneCenter_le_VZ T M).trans (Hyp1281Two.VZ_le_uOfL22 T M)
    apply le_antisymm
    · exact uOfL22_le_qOf c
    · rw [c19.a.q_eq, hDZ]
      exact sup_le le_rfl hZU
  · exfalso
    obtain ⟨d, -, -, hDd, hd4⟩ := exists_cyclic_of_dOf_ne hS htT htRQ hM hP hVr c18.b.r_eq_AAt hΓ hDZ
    exact h G T M g _ t c c18 c19 hΓ c21 d hDd hd4

end S143

end CFSG.Quasithin
