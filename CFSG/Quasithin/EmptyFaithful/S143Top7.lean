module

public import CFSG.Quasithin.EmptyFaithful.S143Top6
public import CFSG.Quasithin.EmptyFaithful.S143LE
public import CFSG.Quasithin.EmptyFaithful.S143LC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

theorem lemma_14_3_19_six : Lemma14319SixDihedral := by
  intro G _ _ T M g A t c c18 c19a hK
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  obtain ⟨x, z, a, r1, hS⟩ := c.exists_setup hrW hrV hr2 c18.a
  obtain ⟨y, cm, Vl, s, hM, hconf, hVl⟩ := hS.exists_KModel2 c18.b.t_mem c18.b.t_nmem
  have hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1 := by
    intro γ hγ
    have h : γ ∈ Subgroup.centralizer (kOf T M (c.Ac hrW hrV hr2) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr hγ
    rw [c.centralizer_kOf_eq_bot c18.b] at h
    exact Subgroup.mem_bot.mp h
  exact dihedral_main hS c18.b.t_mem c18.b.t_nmem hM hconf hVl hC1
    (c.normalizer_kOf_eq c18.b c19a hK)

structure Inputs14316Seven : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h20 : Lemma14320
  h22 : Lemma14322

theorem Inputs14316Seven.toInputsSix (h : Inputs14316Seven) : Inputs14316Six :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h19six := lemma_14_3_19_six
    h20 := h.h20
    h22 := h.h22 }

end S143

theorem stageTheorem14316_of_inputs7 (h : S143.Inputs14316Seven) : StageTheorem14316 :=
  stageTheorem14316_of_inputs6 h.toInputsSix

end CFSG.Quasithin
