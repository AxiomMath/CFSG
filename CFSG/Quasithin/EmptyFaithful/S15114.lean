module

public import CFSG.Quasithin.EmptyFaithful.S1519
public import CFSG.Quasithin.EmptyFaithful.S1414Group

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_14 (hStep : Step1514Gen) {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hCE : IsCE1513 T M) (h157 : Lemma1517Concl T Mc M)
    (h15 : Lemma1515Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (h16 : oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (V154 T Mc M : Set G))
    (h1512 : ∀ H : Subgroup G, IsHStar T M H →
      ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥) :
    Lemma15114Concl T Mc M := by
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hMT : InM (S : Subgroup G) M := hM.1.1
  have hTM : (S : Subgroup G) ≤ M := hMT.2
  have hred : IsTwoReducedIn M (V154 (S : Subgroup G) Mc M) := h15.reduced
  have hVT : V154 (S : Subgroup G) Mc M ≤ S :=
    (V154_le_VZ _ Mc M).trans (isTwoReducedIn_VZ h hMT).2
  have hVelem : IsElemAbelian 2 (V154 (S : Subgroup G) Mc M) := hred.2.2.1
  have hrank : 1 < CFSG.Open.pRank 2 (S : Subgroup G) := one_lt_pRank_T h hM h157
  have hJT : thompsonJ (S : Subgroup G) ≤ thompsonJi (S : Subgroup G) 1 := by
    rw [thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_mono (Nat.zero_le 1) hrank
  have hJ1T : thompsonJi (S : Subgroup G) 1 ≤ S := iSup₂_le fun _ hA => hA.1
  have hJcent : thompsonJ (S : Subgroup G) ≤
      Subgroup.centralizer (V154 (S : Subgroup G) Mc M : Set G) :=
    le_centralizer_of_commutator_eq_bot h159.one_commute
  have hJV : thompsonJ (S : Subgroup G) ≤
      M ⊓ Subgroup.centralizer (V154 (S : Subgroup G) Mc M : Set G) :=
    le_inf ((thompsonJ_le_self151 _).trans hTM) hJcent
  have hVE : V154 (S : Subgroup G) Mc M ≤ omegaOneCenterOf (thompsonJ (S : Subgroup G)) :=
    (lemma_14_1_2_one S hTM hred hJV).1
  have hVE_le : (V154 (S : Subgroup G) Mc M ⊓
      Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G)) ≤
      omegaOneCenterOf (thompsonJi (S : Subgroup G) 1) := by
    intro x hx
    exact Subgroup.subset_closure
      ⟨⟨hJT (omegaOneCenterOf_le_self _ (hVE hx.1)), hx.2⟩, hVelem.2 x hx.1⟩
  have hNJ1 : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (thompsonJi (S : Subgroup G) 1 : Set G) :=
    normalizer_le_normalizer_thompsonJi151 _ 1
  have hVEne : (V154 (S : Subgroup G) Mc M ⊓
      Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G)) ≠ ⊥ := by
    obtain ⟨z, hzV, hz1, hzZ⟩ := exists_ne_one_mem_omegaOneCenter_of_normalized h.sylow.1 hVT
      (V154_ne_bot h) (hTM.trans (le_normalizer_V154 _ Mc M))
    have hz' := quasithinOmegaOneCenter_le_center (S : Subgroup G) hzZ
    intro hb
    have hzmem : z ∈ V154 (S : Subgroup G) Mc M ⊓
        Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) :=
      ⟨hzV, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hz'.2 y (hJ1T hy)⟩
    rw [hb, Subgroup.mem_bot] at hzmem
    exact hz1 hzmem
  have h1 : ¬ Case3bOf (S : Subgroup G) Mc M →
      oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G)) ≤
      Subgroup.centralizer ((V154 (S : Subgroup G) Mc M ⊓
        Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G) := by
    intro hnb
    by_contra hn
    have h16' : oTwoUpper (M ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter (S : Subgroup G) : Set G)) ≤
        Subgroup.centralizer ((V154 (S : Subgroup G) Mc M ⊓
          Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G) :=
      h16.trans (Subgroup.centralizer_le inf_le_left)
    obtain ⟨H, hH, -, hHn⟩ := hStep G S Mc M h hM hCE h16' hn hnb
    have hle : oTwoUpper H ≤ Subgroup.centralizer ((V154 (S : Subgroup G) Mc M ⊓
        Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G) :=
      (le_centralizer_of_commutator_eq_bot (h1512 H hH)).trans (Subgroup.centralizer_le hVE_le)
    refine hHn ((Subgroup.closure_le _).mpr fun x hx => ?_)
    exact mem_oTwoUpper_of_odd (hle (mem_oTwoUpper_of_odd hx.1 hx.2)) hx.2
  have hCsyl : IsSylowTwoOf (S : Subgroup G)
      (Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G)) := by
    refine ⟨fun t ht => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center _ hz).2 t ht).symm,
      h.sylow.1, ?_⟩
    intro h2
    apply h.sylow.2
    exact h2.trans (Subgroup.relIndex_dvd_index_of_le (fun t ht =>
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center _ hz).2 t ht).symm))
  have hCeq := eq_oTwoUpper_sup_of_isSylowTwoOf hCsyl
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((V154 (S : Subgroup G) Mc M ⊓
      Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer' (hTM.trans hred.2.1)
      (Subgroup.le_normalizer.trans hNJ1)
  have hCN : ¬ Case3bOf (S : Subgroup G) Mc M →
      Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((V154 (S : Subgroup G) Mc M ⊓
        Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G) := by
    intro hnb
    rw [hCeq]
    exact sup_le ((h1 hnb).trans (Subgroup.centralizer_le_normalizer _)) hSN
  have hNMc : ¬ Case3bOf (S : Subgroup G) Mc M →
      Subgroup.normalizer ((V154 (S : Subgroup G) Mc M ⊓
      Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G) ≤ Mc := by
    intro hnb
    have hp : IsPGroup 2 (V154 (S : Subgroup G) Mc M ⊓
        Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) :=
      h.sylow.1.to_le (inf_le_left.trans hVT)
    obtain ⟨K, hK, hNK⟩ := exists_maxTwoLocal_ge
      (L := Subgroup.normalizer ((V154 (S : Subgroup G) Mc M ⊓
        Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G))
      ⟨_, hVEne, hp, rfl⟩
    exact (hNK.trans (h.mc_unique K hK ((hCN hnb).trans hNK)).le)
  have h2 : M ⊓ Subgroup.normalizer (thompsonJi (S : Subgroup G) 1 : Set G) ≤
      Subgroup.normalizer ((V154 (S : Subgroup G) Mc M ⊓
        Subgroup.centralizer (thompsonJi (S : Subgroup G) 1 : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer' (inf_le_left.trans hred.2.1) inf_le_right
  have hJeq : thompsonJ (thompsonJi (S : Subgroup G) 1) = thompsonJ (S : Subgroup G) := by
    have := thompsonJi_eq_of_le (S := (S : Subgroup G)) (R := thompsonJi (S : Subgroup G) 1)
      (i := 0) (by omega) (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJT) hJ1T
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero, ← this]
  have hNM : Subgroup.normalizer (thompsonJi (S : Subgroup G) 1 : Set G) ≤ M := by
    refine (normalizer_le_normalizer_thompsonJ (thompsonJi (S : Subgroup G) 1)).trans ?_
    rw [hJeq]
    exact (S1414.normalizer_thompsonJ_le_CGS h.sylow.1 h.ne_bot).trans h159.one_cgs
  exact
    { one := h1
      two := fun hnb => ⟨h2, hNMc hnb⟩
      three := fun hnb x hx => ⟨hNM hx, hNMc hnb (h2 ⟨hNM hx, hx⟩)⟩ }

theorem stageLemma15114_of (hStep : Step1514Gen) (h157 : StageLemma1517)
    (h15 : StageLemma1515) (h159 : StageLemma1519) (h16 : StageLemma1516)
    (h1512 : StageLemma15112) : StageLemma15114 := by
  intro G _ _ T Mc M h hM hCE
  exact lemma_15_1_14 hStep h hM hCE (h157 G T Mc M h hM hCE) (h15 G T Mc M h hM)
    (h159 G T Mc M h hM hCE) (h16 G T Mc M h hM)
    (fun H hH => (h1512 G T Mc M h hM hCE H hH).2)

end CFSG.Quasithin
