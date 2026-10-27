module

public import CFSG.Quasithin.Vol2.Ch3E213MP5I
public import CFSG.Quasithin.Vol2.Ch3E213MP5J
public import CFSG.Quasithin.Vol2.Ch3E213MSL2Pair
public import CFSG.Quasithin.Vol2.Ch3E213MShare

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.GorensteinWalter
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

theorem P5.isSylowTwoOf_top_sylow {W : Type} [Group W] [Finite W] (S : Sylow 2 W) :
    IsSylowTwoOf (S : Subgroup W) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, S.isPGroup', ?_⟩
  rw [show ((S : Subgroup W).subgroupOf ⊤).index = (S : Subgroup W).index from
    Subgroup.relIndex_top_right _]
  exact S.not_dvd_index

theorem P5.isPSL_of_mulEquiv {X X' : Type} [Group X] [Group X'] {d p m : ℕ} (e : X ≃* X')
    (h : IsPSL d p m X') : IsPSL d p m X := by
  obtain ⟨hadm, F, hF, hFin, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, F, hF, hFin, hcard, ⟨e.trans e'⟩⟩

theorem pair_of_l3
    {G : Type} [Group G] [Finite G]
    {H T M V K : Subgroup G} (hS : Setting H T M V K) (h2 : Case2 H T M K) {n : ℕ} (_hn : 1 ≤ n)
    (hPSL : IsPSL 3 2 n ↥(E2.star M H K))
    (hD : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    ∃ T' : Sylow 2 ↥H, (T' : Subgroup H) = T.subgroupOf H ∧
      SL2Pair.Pair T' (M.subgroupOf H) (V.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hKnH : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH, hS.eq_sup]
    exact sup_le Subgroup.le_normalizer h2.1
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  obtain ⟨-, -, -, hKn, hCK, -, ⟨hSB, -, -⟩, -, -, -⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  have hK₀ := map_oddResidualPreimage_eq_of_case2 hS h2
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  have hKe : ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))).map
      (starEquiv hMH).toMonoidHom = E2.star M H K := by
    rw [hK₀]
    exact map_barIn_starEquiv hMH K
  have hSe : ((T' : Subgroup H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))).map
      (starEquiv hMH).toMonoidHom = E2.star M H T := by
    rw [hT']
    exact map_barIn_starEquiv hMH T
  have hBe := map_barIn_starEquiv hMH M
  have hPSL' : IsPSL 3 2 n
      ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))) :=
    P5.isPSL_of_mulEquiv ((MulEquiv.subgroupCongr hK₀).trans φ) hPSL
  have hTKs := E2P.star_inf_T (M := M) hmp.isSylow
    (CFSG.Open.IsSubnormal.step hKH hKnH (CFSG.Open.IsSubnormal.refl H)) hKH
  have hMKs := E2P.star_inf_M (H := H) (M := M) K
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hDdef
  set π := QuotientGroup.mk' D with hπdef
  set e := starEquiv hMH with he
  set Kb := (oddResidualPreimage H).map π with hKbdef
  set Sb := (T' : Subgroup H).map π with hSbdef
  set Bb := (M.subgroupOf H).map π with hBbdef
  set Eb := (V.subgroupOf H).map π with hEbdef
  have := hKn
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hSsyl : IsSylowTwoOf Sb ⊤ := by
    have h := P5.isSylowTwoOf_top_sylow (T'.mapSurjective hπs)
    rwa [Sylow.coe_mapSurjective] at h
  have hdiag : ∀ P : Subgroup (↥H ⧸ D), IsMaxParabolic2 Kb P →
      Kb ⊓ Subgroup.normalizer ((Sb ⊓ Kb : Subgroup (↥H ⧸ D)) : Set (↥H ⧸ D)) ≤ P →
        ¬ Sb ≤ Subgroup.normalizer (P : Set (↥H ⧸ D)) := by
    intro P hP hle hSP
    refine hD (P.map e.toMonoidHom) ?_ ?_ ?_
    · rw [← hKe]
      exact P5.isMaxParabolic2_map_equiv e hP
    · rw [← hKe, hTKs, ← hSe, ← hKe, ← Subgroup.map_inf _ _ _ e.injective,
        ← P5.map_inf_normalizer]
      exact Subgroup.map_mono hle
    · rw [← hSe]
      exact P5.map_le_normalizer e hSP
  have hBorel : ∃ S₀ : Subgroup (↥H ⧸ D), IsSylowTwoOf S₀ Kb ∧
      Bb ⊓ Kb = Kb ⊓ Subgroup.normalizer (S₀ : Set (↥H ⧸ D)) := by
    obtain ⟨S₀, hS₀, hS₀eq⟩ := hB
    refine ⟨S₀.map e.symm.toMonoidHom, ?_, ?_⟩
    · have h := P5.isSylowTwoOf_map_equiv e.symm hS₀
      rwa [← hKe, P5.map_symm_map] at h
    · have h := congrArg (Subgroup.map e.symm.toMonoidHom) hS₀eq
      rw [hMKs, ← hBe, ← hKe, ← Subgroup.map_inf _ _ _ e.injective, P5.map_symm_map,
        P5.map_inf_normalizer, P5.map_symm_map] at h
      exact h
  have hES : Eb ≤ Sb := Subgroup.map_mono hVT'
  have hSE : Sb ≤ Subgroup.normalizer (Eb : Set (↥H ⧸ D)) :=
    (Subgroup.map_mono hTV').trans (Subgroup.le_normalizer_map π)
  have hEel : IsElementaryAbelian 2 Eb := IsElementaryAbelian.map π
  have hE2 : ∀ x ∈ Eb, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  obtain ⟨k, _, _, _, θ, hk, hθS, hθB, hEZ⟩ :=
    P5.model_of_setting hSsyl hCK hPSL' hdiag hBorel hSB hES hSE hE2
  have hφS : ∀ g, P5.cornerA θ g ∈ Sb ↔ g ∈ sl2UpperUnipotentSubgroup k := by
    intro g
    have h := P5.inf_range_cornerA_S θ hθS
    constructor
    · intro hg
      have h1 : P5.cornerA θ g ∈ Sb ⊓ (P5.cornerA θ).range := ⟨hg, g, rfl⟩
      rw [h] at h1
      exact (Subgroup.mem_map_iff_mem (P5.cornerA_injective θ)).1 h1
    · intro hg
      have h1 : P5.cornerA θ g ∈ (sl2UpperUnipotentSubgroup k).map (P5.cornerA θ) :=
        ⟨g, hg, rfl⟩
      rw [← h] at h1
      exact h1.1
  have hφB : ∀ g ∈ sl2Borel k, P5.cornerA θ g ∈ Bb := by
    intro g hg
    have h1 : P5.cornerA θ g ∈ (sl2Borel k).map (P5.cornerA θ) := ⟨g, hg, rfl⟩
    rw [← P5.inf_range_cornerA_B θ hθB] at h1
    exact h1.1
  have hEφ : Eb ≤ (sl2UpperUnipotentSubgroup k).map (P5.cornerA θ) := by
    rw [P5.map_cornerA, P5.map_sl2UpperUnipotent]
    exact hEZ
  exact ⟨T', hT', SL2Pair.qrc_pair_of_sl2 hS.not_solvable hcharH T' hTn hTM' hMH' hmax' hVT'
    hTV' hVM' hVQ' hk (P5.cornerA θ) (P5.cornerA_injective θ)
    (fun g => P5.range_cornerA_le θ ⟨g, rfl⟩) hφS hφB hEφ⟩

end CFSG.Quasithin.Ch3E213M
