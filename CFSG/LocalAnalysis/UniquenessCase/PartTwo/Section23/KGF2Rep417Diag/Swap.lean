module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.GraphL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.GraphSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.GraphBar
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.GF2Rep417Diag

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem swap_of_residual {Y : Type} [Group Y] [Finite Y] {U : Subgroup Y}
    {P : Fin 2 → Subgroup Y}
    (hR : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt Y U P) (θ : MulAut Y)
    (hθU : U.map θ.toMonoidHom = U)
    (hdich : ∀ H : Subgroup Y, U ≤ H → H.map θ.toMonoidHom = H →
      H ≤ normalizer (U : Set Y) ∨ H = ⊤)
    (hN : normalizer (U : Set Y) ≠ ⊤) :
    (P 0).map θ.toMonoidHom ≠ P 0 ∧ normalizer (U : Set Y) ≤ P 0 := by
  classical
  obtain ⟨hne, hUP, hmax, -, -, -⟩ := hR
  have hcov : ∀ j, P j ⋖ ⊤ := fun j => (hmax (P j) (hUP j)).2 ⟨j, rfl⟩
  have key : ∀ x y : Subgroup Y, x.map θ.toMonoidHom ⋖ y.map θ.toMonoidHom ↔ x ⋖ y :=
    fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup θ)
  have hcovmap : ∀ j, (P j).map θ.toMonoidHom ⋖ ⊤ := by
    intro j
    rw [← Subgroup.map_top_of_surjective θ.toMonoidHom θ.surjective]
    exact (key (P j) ⊤).2 (hcov j)
  have hex : ∀ j : Fin 2, ∃ k, (P j).map θ.toMonoidHom = P k := fun j =>
    (hmax _ (hθU ▸ Subgroup.map_mono (hUP j))).1 (hcovmap j)
  obtain ⟨k0, hk0⟩ := hex 0
  obtain ⟨k1, hk1⟩ := hex 1
  have hfixN : (normalizer (U : Set Y)).map θ.toMonoidHom = normalizer (U : Set Y) := by
    rw [Subgroup.map_equiv_normalizer_eq, hθU]
  fin_cases k0
  ·
    fin_cases k1
    · exfalso
      exact absurd (Subgroup.map_injective θ.injective (by rw [hk0, hk1])) hne
    ·
      exfalso
      have hfix0 : (P 0).map θ.toMonoidHom = P 0 := hk0
      have hfix1 : (P 1).map θ.toMonoidHom = P 1 := hk1
      have h0 : P 0 ≤ normalizer (U : Set Y) := by
        rcases hdich (P 0) (hUP 0) hfix0 with h | h
        · exact h
        · exact absurd h (hcov 0).ne
      have h1 : P 1 ≤ normalizer (U : Set Y) := by
        rcases hdich (P 1) (hUP 1) hfix1 with h | h
        · exact h
        · exact absurd h (hcov 1).ne
      have hN0 : normalizer (U : Set Y) = P 0 := by
        refine le_antisymm ?_ h0
        by_contra hlt'
        have hne' : P 0 ≠ normalizer (U : Set Y) := fun hEq => hlt' (hEq ▸ le_rfl)
        have hlt : P 0 < normalizer (U : Set Y) := lt_of_le_of_ne h0 hne'
        exact hN (by
          by_contra hnt
          exact (hcov 0).2 hlt (lt_of_le_of_ne le_top hnt))
      have hle : P 1 ≤ P 0 := h1.trans hN0.le
      have hlt : P 1 < P 0 := lt_of_le_of_ne hle hne.symm
      refine (hcov 0).ne (by
        by_contra hpt
        exact (hcov 1).2 hlt (lt_of_le_of_ne le_top hpt))
  ·
    have hk0' : (P 0).map θ.toMonoidHom = P 1 := hk0
    have hk1' : (P 1).map θ.toMonoidHom = P 0 := by
      fin_cases k1
      · exact hk1
      · exfalso
        exact absurd (Subgroup.map_injective θ.injective (by rw [hk0, hk1])) hne
    have hNle0 : normalizer (U : Set Y) ≤ P 0 := by
      obtain ⟨M, hNM, hMcov⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.mpr hN)
      obtain ⟨k, hkP⟩ := (hmax M (Subgroup.le_normalizer.trans hNM)).1 hMcov
      have hNMk : normalizer (U : Set Y) ≤ P k := hkP ▸ hNM
      fin_cases k
      · exact hNMk
      · have h := Subgroup.map_mono hNMk (f := θ.toMonoidHom)
        change (normalizer (U : Set Y)).map θ.toMonoidHom ≤
          (P 1).map θ.toMonoidHom at h
        rw [hfixN, hk1'] at h
        exact h
    exact ⟨by rw [hk0']; exact hne.symm, hNle0⟩

theorem isSylowIn_inf_of_isComponentOf {G : Type} [Group G] [Finite G] {T L X : Subgroup G}
    (hT : IsSylowIn 2 T X) (hL : IsComponentOf L X) : IsSylowIn 2 (T ⊓ L) L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Quasithin.F6.isSylowIn_inf_of_isSubnormal hL.2.1 hT

private theorem map_centerQuot_sylow_fixed {G : Type} [Group G] [Finite G]
    {T L : Subgroup G} {t : G}
    (S : Sylow 2 ↥L) (hS : (S : Subgroup ↥L) = (T ⊓ L).subgroupOf L)
    (htT : t ∈ T) (htL : t ∈ normalizer (L : Set G))
    {θ : MulAut (↥L ⧸ Subgroup.center ↥L)}
    (hθ : ∀ a a' : ↥L, (a' : G) = t * (a : G) * t⁻¹ →
      θ (QuotientGroup.mk a) = QuotientGroup.mk a') :
    ((S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) :
        Sylow 2 (↥L ⧸ Subgroup.center ↥L)) : Subgroup (↥L ⧸ Subgroup.center ↥L)).map
        θ.toMonoidHom =
      ((S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) :
        Sylow 2 (↥L ⧸ Subgroup.center ↥L)) : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := Subgroup.center ↥L
  let q : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  let Sb : Sylow 2 (↥L ⧸ Z) := S.mapSurjective (QuotientGroup.mk'_surjective Z)
  have hSbcoe : (Sb : Subgroup (↥L ⧸ Z)) = (S : Subgroup ↥L).map q :=
    Sylow.coe_mapSurjective (f := q) (QuotientGroup.mk'_surjective Z) S
  change (Sb : Subgroup (↥L ⧸ Z)).map θ.toMonoidHom = (Sb : Subgroup (↥L ⧸ Z))
  have hle : (Sb : Subgroup (↥L ⧸ Z)).map θ.toMonoidHom ≤ Sb := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hSbcoe] at hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have haT : (a : G) ∈ T ⊓ L := by
      rw [hS] at ha
      exact Subgroup.mem_subgroupOf.mp ha
    let a' : ↥L := ⟨t * (a : G) * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htL (a : G)).mp a.2⟩
    have ha'S : a' ∈ (S : Subgroup ↥L) := by
      rw [hS]
      exact Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem (T.mul_mem htT haT.1) (T.inv_mem htT), a'.2⟩
    change θ (QuotientGroup.mk a) ∈ (Sb : Subgroup (↥L ⧸ Z))
    rw [hθ a a' rfl]
    exact Subgroup.mem_map.2 ⟨a', ha'S, rfl⟩
  have hcard : Nat.card ((Sb : Subgroup (↥L ⧸ Z)).map θ.toMonoidHom) =
      Nat.card (Sb : Subgroup (↥L ⧸ Z)) :=
    Subgroup.card_map_of_injective θ.injective
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

private theorem exists_maxParabolic_moved {G : Type} [Group G] [Finite G]
    {T L : Subgroup G} {t : G} (htT : t ∈ T) (htL : t ∈ normalizer (L : Set G))
    (S : Sylow 2 ↥L) (hS : (S : Subgroup ↥L) = (T ⊓ L).subgroupOf L)
    {θ : MulAut (↥L ⧸ Subgroup.center ↥L)}
    (hθ : ∀ a a' : ↥L, (a' : G) = t * (a : G) * t⁻¹ →
      θ (QuotientGroup.mk a) = QuotientGroup.mk a')
    {P0 : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hP0cov : P0 ⋖ ⊤)
    (hNle : normalizer ((S.map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)) ≤ P0)
    (hθP0 : P0.map θ.toMonoidHom ≠ P0) :
    ∃ Q : Subgroup G, S17.IsMaxParabolicOver L (T ⊓ L) Q ∧
      Q.map (MulAut.conj t).toMonoidHom ≠ Q := by
  classical
  let Z := Subgroup.center ↥L
  let q : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  let Pt : Subgroup ↥L := P0.comap q
  let Q : Subgroup G := Pt.map L.subtype
  have hQle : Q ≤ L := Subgroup.map_subtype_le _
  have hPt_cov : Pt ⋖ ⊤ :=
    (Subgroup.isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective Z)
      hP0cov.isCoatom).covBy_top
  have hNclause : L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ Q := by
    intro x hx
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
    let x' : ↥L := ⟨x, hxL⟩
    have hxN' : x' ∈ normalizer ((S : Subgroup ↥L) : Set ↥L) := by
      rw [hS, ← Subgroup.subgroupOf_normalizer_eq (inf_le_right : T ⊓ L ≤ L)]
      exact Subgroup.mem_subgroupOf.mpr hxN
    have hqx : QuotientGroup.mk' (Subgroup.center ↥L) x' ∈
        normalizer ((S.map (QuotientGroup.mk' (Subgroup.center ↥L)) :
          Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)) :=
      Subgroup.le_normalizer_map (QuotientGroup.mk' (Subgroup.center ↥L))
        (Subgroup.mem_map_of_mem _ hxN')
    have hNle' := hNle hqx
    have hxPt : x' ∈ Pt := by
      change QuotientGroup.mk' (Subgroup.center ↥L) x' ∈ P0
      exact hNle'
    exact Subgroup.mem_map.mpr ⟨x', hxPt, rfl⟩
  have hQne : Q ≠ L := by
    intro hQL
    have hPt_top : Pt = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      calc Pt.map L.subtype = Q := rfl
        _ = L := hQL
        _ = (⊤ : Subgroup ↥L).map L.subtype := by
            simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := L)).symm
    have hP0top : P0 = ⊤ := by
      calc P0 = Pt.map q := by
              rw [show Pt = P0.comap q from rfl]
              exact (Subgroup.map_comap_eq_self_of_surjective
                (QuotientGroup.mk'_surjective Z) P0).symm
        _ = (⊤ : Subgroup ↥L).map q := by rw [hPt_top]
        _ = ⊤ := Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective Z)
    exact hP0cov.ne hP0top
  have hmax : ∀ R : Subgroup G, Q ≤ R → R ≤ L → R = Q ∨ R = L := by
    intro R hQR hRL
    by_cases hRQ : R = Q
    · exact Or.inl hRQ
    · right
      let Rt : Subgroup ↥L := R.subgroupOf L
      have hRt_ge : Pt ≤ Rt := by
        intro x hx
        exact Subgroup.mem_subgroupOf.mpr (hQR (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
      have hRt_ne : Rt ≠ Pt := by
        intro hEq
        exact hRQ (by
          calc R = Rt.map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hRL).symm
            _ = Pt.map L.subtype := by rw [hEq]
            _ = Q := rfl)
      have hlt : Pt < Rt := lt_of_le_of_ne hRt_ge hRt_ne.symm
      have hRt_top : Rt = ⊤ := by
        by_contra hnt
        exact hPt_cov.2 hlt (lt_of_le_of_ne le_top hnt)
      calc R = Rt.map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hRL).symm
        _ = (⊤ : Subgroup ↥L).map L.subtype := by rw [hRt_top]
        _ = L := by
            simpa [MonoidHom.range_eq_map] using Subgroup.range_subtype (H := L)
  refine ⟨Q, ⟨hQle, hNclause, hQne, hmax⟩, ?_⟩
  intro hQfix
  have hleθ : P0.map θ.toMonoidHom ≤ P0 := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective Z a
    have hbP0 : q b ∈ P0 := hb ▸ ha
    have hbPt : b ∈ Pt := Subgroup.mem_comap.mpr hbP0
    have hbQ : (b : G) ∈ Q := Subgroup.mem_map.mpr ⟨b, hbPt, rfl⟩
    have hbtQ : (MulAut.conj t) (b : G) ∈ Q := by
      rw [← hQfix]
      exact Subgroup.mem_map.mpr ⟨b, hbQ, rfl⟩
    let bt : ↥L := ⟨t * (b : G) * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htL (b : G)).mp b.2⟩
    have hbtQ' : (bt : G) ∈ Q := by
      simpa [bt, MulAut.conj_apply] using hbtQ
    have hbtPt : bt ∈ Pt := by
      obtain ⟨c, hc, hcG⟩ := Subgroup.mem_map.1 hbtQ'
      have hcbt : c = bt := Subtype.ext hcG
      rwa [hcbt] at hc
    have hqbt : q bt ∈ P0 := Subgroup.mem_comap.mp hbtPt
    have hθb : θ (q b) = q bt := hθ b bt rfl
    rw [← hb]
    simpa [q] using hθb.symm ▸ hqbt
  have hcard : Nat.card (P0.map θ.toMonoidHom) = Nat.card P0 :=
    Subgroup.card_map_of_injective θ.injective
  exact hθP0 (Subgroup.eq_of_le_of_card_ge hleθ hcard.ge)

private theorem isPerfect_of_isSp4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSp4 X n) : Group.IsPerfect X := by
  have hmodel : CFSG.Open.StatedClassicalModel X .PSp 2 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hmodel
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hn1 : n ≠ 1 := by
    intro hn
    apply hadm.2.2.2
    rw [hn]
    norm_num
  have hn0 : 1 ≤ n := hadm.2.1
  have hn2 : 2 ≤ n := by omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  haveI : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 K
      (Or.inl (CFSG.LinearGroups.exists_finset_card_eq_four h4))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem ne_top_normalizer_of_two_dvd {Y : Type} [Group Y] [Finite Y]
    {U : Subgroup Y} {P : Fin 2 → Subgroup Y} (hsimple : IsSimpleGroup Y)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (h2 : 2 ∣ Nat.card Y)
    (hR : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt Y U P) :
    normalizer (U : Set Y) ≠ ⊤ := by
  intro htop
  haveI : U.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  obtain ⟨-, hUP, hmax, -, -, -⟩ := hR
  have hcov : P 0 ⋖ ⊤ := (hmax (P 0) (hUP 0)).2 ⟨0, rfl⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal U with hbot | htopU
  · exact CFSG.QuasithinUnique.B113Lie.ne_bot_of_two_dvd hU h2 hbot
  · exact hcov.ne (top_le_iff.mp (htopU ▸ hUP 0))

theorem swapsParabolics_of_actsNontrivOnDiagramIn {G : Type} [Group G] [Finite G]
    {T L : Subgroup G} {n : ℕ} (hshape : IsSL3 ↥L n ∨ IsSp4 ↥L n)
    (hTL : IsSylowIn 2 (T ⊓ L) L) {t : G} (htT : t ∈ T) (ht : ActsNontrivOnDiagramIn L t) :
    S17.SwapsParabolics (T ⊓ Subgroup.normalizer (L : Set G)) L := by
  classical
  obtain ⟨htL, θ, hθ, hnd⟩ := ht
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := Subgroup.center ↥L
  let Lb := ↥L ⧸ Z
  let q : ↥L →* Lb := QuotientGroup.mk' Z
  let S : Sylow 2 ↥L := hTL.toSylow
  let Sb : Sylow 2 Lb := S.mapSurjective (QuotientGroup.mk'_surjective Z)
  let U : Subgroup Lb := Sb
  have hScoe : (S : Subgroup ↥L) = (T ⊓ L).subgroupOf L := by
    simpa [S] using CFSG.Quasithin.IsSylowIn.coe_toSylow hTL
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    simpa [U, Sb] using CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Sb
  have hθSb : U.map θ.toMonoidHom = U := by
    simpa [U, Sb, S, Z, Lb] using map_centerQuot_sylow_fixed S hScoe htT htL hθ
  have finish : ∀ P : Fin 2 → Subgroup Lb,
      CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt Lb U P →
      (∀ H : Subgroup Lb, U ≤ H → H.map θ.toMonoidHom = H →
        H ≤ normalizer (U : Set Lb) ∨ H = ⊤) →
      normalizer (U : Set Lb) ≠ ⊤ →
      S17.SwapsParabolics (T ⊓ Subgroup.normalizer (L : Set G)) L := by
    intro P hR hdich hN
    obtain ⟨hθP0, hNle⟩ := swap_of_residual hR θ hθSb hdich hN
    obtain ⟨hne, hUP, hmax, -, -, -⟩ := hR
    have hP0cov : P 0 ⋖ ⊤ := (hmax (P 0) (hUP 0)).2 ⟨0, rfl⟩
    have hNle' : normalizer ((S.map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) :
        Set (↥L ⧸ Subgroup.center ↥L)) ≤ P 0 := by
      simpa [U, Sb, S, Z, Lb, q] using hNle
    obtain ⟨Q, hQmax, hQmove⟩ :=
      exists_maxParabolic_moved htT htL S hScoe hθ hP0cov hNle' hθP0
    have hTeq : (T ⊓ Subgroup.normalizer (L : Set G)) ⊓ L = T ⊓ L := by
      rw [inf_assoc, inf_eq_right.mpr (Subgroup.le_normalizer)]
    exact ⟨t, ⟨htT, htL⟩, Q, hTeq ▸ hQmax, hQmove⟩
  rcases hshape with hlin | hsp
  ·
    have h3 : CFSG.Blueprint.LieModel Lb .PSL 3 2 n := hlin.2
    have hmodel : CFSG.Open.StatedClassicalModel Lb .PSL 3 2 n :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h3
    obtain ⟨K, hKfield, hKfin, hKchar, φ, -, -, hR, -⟩ :=
      CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hmodel hU
    letI : Field K := hKfield
    letI : Finite K := hKfin
    letI : CharP K 2 := hKchar
    have h2 : 2 ∣ Nat.card Lb := by
      rw [Nat.card_congr φ.toEquiv]
      exact CFSG.QuasithinUnique.B113Lie.Lin.two_dvd_card_projectiveSL
        (n := 3) (K := K) (by norm_num)
    haveI hsimple : IsSimpleGroup Lb :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
    have hdich : ∀ H : Subgroup Lb, U ≤ H → H.map θ.toMonoidHom = H →
        H ≤ normalizer (U : Set Lb) ∨ H = ⊤ :=
      fun H hUH hθH =>
        CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel.graphL3_dich
          h3 θ hnd Sb hθSb H hUH hθH
    have hN : normalizer (U : Set Lb) ≠ ⊤ :=
      ne_top_normalizer_of_two_dvd hsimple hU h2 hR
    exact finish _ hR hdich hN
  ·
    haveI : Group.IsPerfect ↥L := isPerfect_of_isSp4 hsp
    have hperf : _root_.commutator ↥L = ⊤ := Group.IsPerfect.commutator_eq_top
    have hspLie : CFSG.Blueprint.LieModel Lb .PSp 2 2 n :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel.lieModel_quot_center_of_isSp4
        hsp hperf
    have hmodel : CFSG.Open.StatedClassicalModel Lb .PSp 2 2 n :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hspLie
    obtain ⟨K, hKfield, hKfin, hKchar, φ, -, -, hR, -⟩ :=
      CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_symplectic hmodel hU
    letI : Field K := hKfield
    letI : Finite K := hKfin
    letI : CharP K 2 := hKchar
    have h2 : 2 ∣ Nat.card Lb := by
      rw [Nat.card_congr φ.toEquiv]
      exact CFSG.QuasithinUnique.B113Lie.Sp.two_dvd_card_statedProj (K := K) (r := 2)
        (CFSG.QuasithinUnique.B113Lie.Sp.single_inl_ne_zero (r := 2) ⟨0, by norm_num⟩)
    haveI hsimple : IsSimpleGroup Lb :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hspLie
    have hdich : ∀ H : Subgroup Lb, U ≤ H → H.map θ.toMonoidHom = H →
        H ≤ normalizer (U : Set Lb) ∨ H = ⊤ :=
      fun H hUH hθH =>
        CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel.graphSp4_dich
          hspLie θ hnd Sb hθSb H hUH hθH
    have hN : normalizer (U : Set Lb) ≠ ⊤ :=
      ne_top_normalizer_of_two_dvd hsimple hU h2 hR
    exact finish _ hR hdich hN

end CFSG.LocalAnalysis.UniquenessCase.UC22.GF2Rep417Diag
