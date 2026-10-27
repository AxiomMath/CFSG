module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin

variable {G Y : Type} [Group G] [Group Y]

private theorem opp_le_of_isSylowIn_le_normalizer [Finite G] {P J S : Subgroup G}
    (hJ : P ≤ normalizer (J : Set G)) (hS : IsSylowIn 2 S P) (hSJ : S ≤ J) :
    Opp 2 P ≤ J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup]
  refine (Subgroup.closure_le J).mpr ?_
  rintro x ⟨hxP, k, hk⟩
  let Y : Subgroup ↥P := (Subgroup.zpowers x).subgroupOf P
  have hzP : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.mpr hxP
  have hYcard : Nat.card Y = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzP).toEquiv, Nat.card_zpowers, hk]
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card hYcard
  obtain ⟨T, hYT⟩ := hY2.exists_le_sylow
  have hsub : (T.map P.subtype).subgroupOf P = T := by
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  have hT : IsSylowIn 2 (T.map P.subtype) P := by
    refine ⟨Subgroup.map_subtype_le (H := P) T, T.isPGroup'.map P.subtype, ?_⟩
    rw [Subgroup.relIndex, hsub]
    exact Sylow.not_dvd_index T
  obtain ⟨c, hcP, hconj⟩ :=
    CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hS hT
  have hxY : (⟨x, hxP⟩ : ↥P) ∈ Y :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x)
  have hxT : x ∈ T.map P.subtype := ⟨⟨x, hxP⟩, hYT hxY, rfl⟩
  have hcxS : c⁻¹ * x * c⁻¹⁻¹ ∈ S := by simpa using (hconj x).1 hxT
  have hcN : c⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normalizer (J : Set G)).inv_mem (hJ hcP)
  exact (Subgroup.mem_normalizer_iff.mp hcN x).2 (hSJ hcxS)

theorem opp_eq_of_isSimpleGroup_bar2 [Finite G] {P J S : Subgroup G} (hJP : J ≤ P)
    (hJ : P ≤ normalizer (J : Set G)) (hS : IsSylowIn 2 S P) (hSJ : S ≤ J)
    (hsimp : IsSimpleGroup (Bar2 J)) (heven : 2 ∣ Nat.card (Bar2 J)) :
    Opp 2 P = J := by
  have hEJ : Opp 2 P ≤ J := opp_le_of_isSylowIn_le_normalizer hJ hS hSJ
  have hEnormP : P ≤ Subgroup.normalizer (Opp 2 P : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy 2 p P
    have hPP : CFSG.RankThree.PartOne.conjBy p P = P := by
      unfold CFSG.RankThree.PartOne.conjBy
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hp)
    rw [hPP] at h1
    simpa [Opp, CFSG.RankThree.PartOne.conjBy] using h1.symm
  have hEnormJ : ((Opp 2 P).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEJ).2 (hJP.trans hEnormP)
  have hSE : S ≤ Opp 2 P :=
    CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two hS.isPGroup hS.le
  have hOleE : CFSG.Open.pCoreOf 2 J ≤ Opp 2 P :=
    CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥J)).map J.subtype)
      ((CFSG.openPCoreOf_le 2 J).trans hJP)
  let O : Subgroup ↥J := CFSG.pCore 2 ↥J
  let π : ↥J →* Bar2 J := QuotientGroup.mk' O
  have hker : π.ker ≤ (Opp 2 P).subgroupOf J := by
    change (QuotientGroup.mk' O).ker ≤ (Opp 2 P).subgroupOf J
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hx' : (x : G) ∈ CFSG.Open.pCoreOf 2 J :=
      (CFSG.mem_openPCoreOf_iff (p := 2) (H := J) x).2 (by simpa [O] using hx)
    exact Subgroup.mem_subgroupOf.mpr (hOleE hx')
  have hNnorm : (((Opp 2 P).subgroupOf J).map π).Normal :=
    Subgroup.Normal.map hEnormJ π (QuotientGroup.mk'_surjective O)
  haveI : (((Opp 2 P).subgroupOf J).map π).Normal := hNnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((Opp 2 P).subgroupOf J).map π) with hbot | htop
  · have hEsub_le : (Opp 2 P).subgroupOf J ≤ CFSG.pCore 2 ↥J := by
      intro x hx
      have hxmap : π x ∈ ((Opp 2 P).subgroupOf J).map π := Subgroup.mem_map_of_mem π hx
      rw [hbot, Subgroup.mem_bot] at hxmap
      exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥J) x).1 hxmap
    have hEO : Opp 2 P ≤ CFSG.Open.pCoreOf 2 J := by
      intro e he
      have heJ : e ∈ J := hEJ he
      have hmem : (⟨e, heJ⟩ : ↥J) ∈ CFSG.pCore 2 ↥J :=
        hEsub_le (Subgroup.mem_subgroupOf.mpr he)
      exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := J) ⟨e, heJ⟩).2 hmem
    have hSO : S ≤ CFSG.Open.pCoreOf 2 J := hSE.trans hEO
    have hOJ : CFSG.Open.pCoreOf 2 J ≤ J := CFSG.openPCoreOf_le 2 J
    have hOrel : (CFSG.Open.pCoreOf 2 J).relIndex J = Nat.card (Bar2 J) := by
      rw [Subgroup.relIndex, CFSG.openPCoreOf_subgroupOf, Subgroup.index_eq_card]
    have hdvd : (CFSG.Open.pCoreOf 2 J).relIndex J ∣ S.relIndex P := by
      have h1 := Subgroup.relIndex_mul_relIndex (H := S)
        (K := CFSG.Open.pCoreOf 2 J) (L := J) hSO hOJ
      have h2 := Subgroup.relIndex_mul_relIndex (H := S) (K := J) (L := P)
        (hSO.trans hOJ) hJP
      refine ⟨S.relIndex (CFSG.Open.pCoreOf 2 J) * J.relIndex P, ?_⟩
      rw [← h2, ← h1]
      ring
    exfalso
    exact hS.not_dvd_relIndex ((hOrel ▸ heven).trans hdvd)
  · have hEsub_top : (Opp 2 P).subgroupOf J = ⊤ := by
      rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
    exact le_antisymm hEJ (Subgroup.subgroupOf_eq_top.mp hEsub_top)

theorem isMaxParabolicOver_top_map (φ : G ≃* Y) {U P : Subgroup G}
    (hP : IsMaxParabolicOver (⊤ : Subgroup G) U P) :
    IsMaxParabolicOver (⊤ : Subgroup Y) (U.map φ.toMonoidHom) (P.map φ.toMonoidHom) := by
  have hN : Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (U : Set G)).map φ.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq U φ).symm
  have hPne : P.map φ.toMonoidHom ≠ ⊤ := by
    intro hmap
    refine hP.2.2.1 ?_
    have h := congrArg (Subgroup.comap φ.toMonoidHom) hmap
    rw [Subgroup.comap_map_eq_self_of_injective (f := φ.toMonoidHom) φ.injective,
      Subgroup.comap_top] at h
    exact h
  refine ⟨le_top, ?_, hPne, ?_⟩
  · calc
      (⊤ : Subgroup Y) ⊓ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup Y) : Set Y)
          ≤ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup Y) : Set Y) := inf_le_right
      _ = (Subgroup.normalizer (U : Set G)).map φ.toMonoidHom := hN
      _ ≤ (⊤ ⊓ Subgroup.normalizer (U : Set G)).map φ.toMonoidHom :=
        Subgroup.map_mono (le_inf le_top le_rfl)
      _ ≤ P.map φ.toMonoidHom := Subgroup.map_mono hP.2.1
  · intro Q hPQ _
    have hmapQ : (Q.comap φ.toMonoidHom).map φ.toMonoidHom = Q :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective Q
    have hPle : P ≤ Q.comap φ.toMonoidHom := by
      have hle : P.map φ.toMonoidHom ≤ (Q.comap φ.toMonoidHom).map φ.toMonoidHom := by
        rwa [hmapQ]
      exact (Subgroup.map_le_map_iff_of_injective φ.injective).1 hle
    rcases hP.2.2.2 (Q.comap φ.toMonoidHom) hPle le_top with h | h
    · left
      rw [← hmapQ, h]
    · right
      rw [← hmapQ, h,
        Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective]

theorem opp_map (φ : G ≃* Y) (p : ℕ) (X : Subgroup G) :
    Opp p (X.map φ.toMonoidHom) = (Opp p X).map φ.toMonoidHom := by
  rw [Opp, Opp, CFSG.RankThree.PartOne.pElementSubgroup,
    CFSG.RankThree.PartOne.pElementSubgroup, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hyX, k, hk⟩
    obtain ⟨x, hxX, rfl⟩ := hyX
    exact ⟨x, ⟨hxX, k, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨hxX, k, hk⟩ := hx
    exact ⟨⟨x, hxX, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]⟩

theorem nonempty_bar2_map (φ : G ≃* Y) (X : Subgroup G) :
    Nonempty (Bar2 (X.map φ.toMonoidHom) ≃* Bar2 X) := by
  let e : ↥X ≃* ↥(X.map φ.toMonoidHom) :=
    X.equivMapOfInjective φ.toMonoidHom φ.injective
  exact ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).symm⟩

theorem exists_mulEquiv_map_eq_of_isSylowIn {p : ℕ} [Fact p.Prime] [Finite G] (e : G ≃* Y)
    {U : Subgroup G} {S : Subgroup Y} (hU : IsSylowIn p U ⊤) (hS : IsSylowIn p S ⊤) :
    ∃ φ : G ≃* Y, U.map φ.toMonoidHom = S := by
  haveI : Finite Y := Finite.of_injective e.symm.toMonoidHom e.symm.injective
  have hU' : IsSylowIn p (U.map e.toMonoidHom) ⊤ := by
    have h := (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv e).mpr hU
    simpa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using h
  obtain ⟨y, -, hy⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hU' hS
  refine ⟨e.trans (MulAut.conj y), ?_⟩
  ext s
  constructor
  · rintro ⟨u, hu, hue⟩
    rw [← hue]
    refine (hy ((MulAut.conj y) (e u))).2 ?_
    simpa [MulAut.conj_apply, mul_assoc] using Subgroup.mem_map_of_mem e.toMonoidHom hu
  · intro hs
    have hmem : y⁻¹ * s * y ∈ U.map e.toMonoidHom := (hy s).1 hs
    obtain ⟨u, hu, hue⟩ := hmem
    refine ⟨u, hu, ?_⟩
    change y * e.toMonoidHom u * y⁻¹ = s
    rw [hue]
    group

theorem map_map_trans_symm (φ : G ≃* Y) (r : MulAut Y) (X : Subgroup G) :
    (X.map φ.toMonoidHom).map r.toMonoidHom =
      (X.map ((φ.trans r).trans φ.symm).toMonoidHom).map φ.toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1
  ext x
  simp [MulEquiv.trans_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
