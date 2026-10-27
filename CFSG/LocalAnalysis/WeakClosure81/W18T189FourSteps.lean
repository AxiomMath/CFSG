module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2b
public import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentral
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineShape
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourFacts
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem pgls_isPerfect_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : Group.IsPerfect X := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ ∈ commutator X :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
  · exact h

private theorem pgls_center_eq_bot_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

private theorem pgls_isQuasisimple_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  refine ⟨(pgls_isPerfect_of_isSimpleGroup hnab).commutator_eq_top, ?_⟩
  have hcenter := pgls_center_eq_bot_of_isSimpleGroup hnab
  exact MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)

private theorem pgls_genFittingFStar_map {Q Y : Type*} [Group Q] [Group Y] (e : Q ≃* Y) :
    (genFittingFStar Q).map e.toMonoidHom = genFittingFStar Y := by
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, CFSG.Adapters.genFittingFStar_eq_foundations]
  exact CFSG.WholeGroup.generalizedFitting_map_mulEquiv e

private theorem pgls_genFittingFStar_equivMap {Q Y : Type*} [Group Q] [Group Y] (e : Q ≃* Y) :
    Nonempty (↥(genFittingFStar Q) ≃* ↥(genFittingFStar Y)) :=
  ⟨(Subgroup.equivMapOfInjective (genFittingFStar Q) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (pgls_genFittingFStar_map e))⟩

section Shape

theorem exists_mulEquiv_img_quot {H E K : Subgroup G} (M : ModDataE H E)
    (hK : H ⊓ Subgroup.centralizer (E : Set G) = K) :
    Nonempty ((↥H ⧸ (K.subgroupOf H).normalCore) ≃* ↥(M.img H)) := by
  have hker : M.ρ.ker = K.subgroupOf H := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, M.ρ_eq_one_iff j]
    constructor
    · intro hc
      rw [← hK]
      exact ⟨j.2, hc⟩
    · intro h
      rw [← hK] at h
      exact h.2
  have hKn : (K.subgroupOf H).Normal := hker ▸ MonoidHom.normal_ker M.ρ
  have hcore : (K.subgroupOf H).normalCore = M.ρ.ker := by
    rw [Subgroup.normalCore_eq_self, hker]
  have himg : M.ρ.range = M.img H := by
    unfold ModDataE.img
    rw [Subgroup.subgroupOf_self, MonoidHom.range_eq_map]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans
    ((QuotientGroup.quotientKerEquivRange M.ρ).trans (MulEquiv.subgroupCongr himg))⟩

theorem hyp66Shape_of_quotEquiv {H : Subgroup G} (hH : Shape185 H) {Y : Type} [Group Y]
    [Finite Y] (e : (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore) ≃* Y) :
    Hyp66Shape Y (genFittingFStar Y) := by
  obtain ⟨h512, hnot⟩ := hH
  have hNn : ((relPPrimeCore 3 H).subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      (p := 3) (by norm_num) H
  haveI := hNn
  rcases h512 with ⟨p, e', hp, hp5, he, HQ⟩ |
    ⟨p, f, hp, hp5, hcase⟩ | ⟨-, HPGL⟩ | hfour
  · obtain ⟨X, instX, hPX, ⟨eF⟩⟩ :=
      exists_mulEquiv_genFittingFStar_of_hasQuotShape hNn HQ
    haveI : Finite X := Finite.of_injective eF.symm eF.symm.injective
    obtain ⟨eF'⟩ := pgls_genFittingFStar_equivMap e
    have hY : F6.IsL2 p e' ↥(genFittingFStar Y) :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (eF.symm.trans eF') hPX
    exact Or.inl ⟨p, e', hp, by omega, he, hY⟩
  · rcases hcase with ⟨h3, h4, HQ⟩ | ⟨h3, h4, HQ⟩
    · obtain ⟨X, instX, hPX, ⟨eF⟩⟩ :=
        exists_mulEquiv_genFittingFStar_of_hasQuotShape hNn HQ
      haveI : Finite X := Finite.of_injective eF.symm eF.symm.injective
      obtain ⟨eF'⟩ := pgls_genFittingFStar_equivMap e
      have hSocle : Socle185Shape X :=
        Or.inr (Or.inl ⟨p, f, hp, hp5, Or.inl ⟨h3, h4, hPX⟩⟩)
      haveI : IsSimpleGroup X := hSocle.isSimpleGroup
      have hnab : ∃ a b : X, a * b ≠ b * a := hSocle.exists_not_commute
      have hq : CFSG.Open.IsQuasisimple X := pgls_isQuasisimple_of_isSimpleGroup hnab
      have hqY : CFSG.Open.IsQuasisimple ↥(genFittingFStar Y) :=
        CFSG.Open.IsQuasisimple.of_mulEquiv (eF'.symm.trans eF) hq
      haveI : IsSimpleGroup ↥(genFittingFStar Y) :=
        MulEquiv.isSimpleGroup (eF'.symm.trans eF)
      have hnabY : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnab
        refine ⟨(eF'.symm.trans eF).symm a, (eF'.symm.trans eF).symm b, fun h => hab ?_⟩
        have := congrArg (eF'.symm.trans eF) h
        simpa using this
      have hcenterY : Subgroup.center ↥(genFittingFStar Y) = ⊥ :=
        pgls_center_eq_bot_of_isSimpleGroup hnabY
      have h3lt : 3 < p ^ f := by
        have hf1 : 1 ≤ f := hPX.admissible.2.1
        have hpf : 5 ≤ p ^ f :=
          le_trans hp5 (Nat.le_self_pow (by omega : f ≠ 0) p)
        omega
      have hfodd : Odd f := by
        by_contra hf
        rw [Nat.not_odd_iff_even] at hf
        have h1 : p ^ f % 4 = 1 :=
          CFSG.ComponentClassification.AutL2Facts.pow_mod_four_of_even hp (by omega) hf
        omega
      refine Or.inr (Or.inl ⟨p, f, X, instX, hp, by omega, h3lt, Or.inl ⟨hfodd, hPX⟩,
        hqY, ?_⟩)
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenterY).trans
        (QuotientGroup.quotientBot.trans (eF'.symm.trans eF))⟩
    · obtain ⟨X, instX, hPX, ⟨eF⟩⟩ :=
        exists_mulEquiv_genFittingFStar_of_hasQuotShape hNn HQ
      haveI : Finite X := Finite.of_injective eF.symm eF.symm.injective
      obtain ⟨eF'⟩ := pgls_genFittingFStar_equivMap e
      have hSocle : Socle185Shape X :=
        Or.inr (Or.inl ⟨p, f, hp, hp5, Or.inr ⟨h3, h4, hPX⟩⟩)
      haveI : IsSimpleGroup X := hSocle.isSimpleGroup
      have hnab : ∃ a b : X, a * b ≠ b * a := hSocle.exists_not_commute
      have hq : CFSG.Open.IsQuasisimple X := pgls_isQuasisimple_of_isSimpleGroup hnab
      have hqY : CFSG.Open.IsQuasisimple ↥(genFittingFStar Y) :=
        CFSG.Open.IsQuasisimple.of_mulEquiv (eF'.symm.trans eF) hq
      haveI : IsSimpleGroup ↥(genFittingFStar Y) :=
        MulEquiv.isSimpleGroup (eF'.symm.trans eF)
      have hnabY : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnab
        refine ⟨(eF'.symm.trans eF).symm a, (eF'.symm.trans eF).symm b, fun h => hab ?_⟩
        have := congrArg (eF'.symm.trans eF) h
        simpa using this
      have hcenterY : Subgroup.center ↥(genFittingFStar Y) = ⊥ :=
        pgls_center_eq_bot_of_isSimpleGroup hnabY
      have h3lt : 3 < p ^ f := by
        have hf1 : 1 ≤ f := hPX.admissible.2.1
        have hpf : 5 ≤ p ^ f :=
          le_trans hp5 (Nat.le_self_pow (by omega : f ≠ 0) p)
        omega
      refine Or.inr (Or.inl ⟨p, f, X, instX, hp, by omega, h3lt, Or.inr hPX, hqY, ?_⟩)
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenterY).trans
        (QuotientGroup.quotientBot.trans (eF'.symm.trans eF))⟩
  · obtain ⟨X, instX, φ, hφs, hφk, hPGLX⟩ := HPGL
    haveI : Finite X := Finite.of_surjective φ hφs
    have hker : φ.ker = (relPPrimeCore 3 H).subgroupOf H := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hφk k
    have hcore : (relPPrimeCore 3 H).subgroupOf H =
        ((relPPrimeCore 3 H).subgroupOf H).normalCore :=
      (Subgroup.normalCore_eq_self ((relPPrimeCore 3 H).subgroupOf H)).symm
    have eQX : X ≃* (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore) :=
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientMulEquivOfEq hcore))
    have hPGLY : F6.IsPGL2 7 Y := by
      obtain ⟨K, hKf, hKfin, hcard, ⟨ePGL⟩⟩ := hPGLX
      exact ⟨K, hKf, hKfin, hcard, ⟨(eQX.trans e).symm.trans ePGL⟩⟩
    exact Or.inr (Or.inr hPGLY)
  · exact absurd hfour hnot

theorem exists_hyp66Shape {H E : Subgroup G} (hH : Shape185 H) (M : ModDataE H E)
    (hK : H ⊓ Subgroup.centralizer (E : Set G) = relPPrimeCore 3 H) :
    Hyp66Shape ↥(M.img H) (genFittingFStar ↥(M.img H)) := by
  obtain ⟨e⟩ := exists_mulEquiv_img_quot M hK
  exact hyp66Shape_of_quotEquiv hH e

end Shape

section Images

variable {H E : Subgroup G}

theorem img_inf_centralizer_eq (M : ModDataE H E) {w : G} (hw : w ∈ E) :
    M.img (H ⊓ Subgroup.centralizer ({w} : Set G)) =
      centralizerOn (M.img H) (Submodule.span (ZMod 2) {M.ι w}) := by
  ext r
  rw [mem_centralizerOn_span_singleton]
  constructor
  · intro hr
    obtain ⟨j, hj, rfl⟩ := M.mem_img.1 hr
    refine ⟨M.mem_img.2 ⟨j, hj.1, rfl⟩, ?_⟩
    have hc : ((j : ↥H) : G) * w = w * ((j : ↥H) : G) :=
      ((Subgroup.mem_centralizer_iff.1 hj.2) w (Set.mem_singleton w)).symm
    rw [M.ρ_ι j w hw, hc]
    congr 1
    group
  · rintro ⟨hr, hfix⟩
    obtain ⟨j, hj, rfl⟩ := M.mem_img.1 hr
    refine M.mem_img.2 ⟨j, ⟨hj, ?_⟩, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have h1 : M.ι (((j : ↥H) : G) * w * ((j : ↥H) : G)⁻¹) = M.ι w := by
      rw [← M.ρ_ι j w hw, hfix]
    have hmem : ((j : ↥H) : G) * w * ((j : ↥H) : G)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (M.le_normalizer j.2) w).1 hw
    have heq := M.ι_injOn hmem hw h1
    have h2 : ((j : ↥H) : G) * w = w * ((j : ↥H) : G) := by
      calc ((j : ↥H) : G) * w = (((j : ↥H) : G) * w * ((j : ↥H) : G)⁻¹) *
            ((j : ↥H) : G) := by group
        _ = w * ((j : ↥H) : G) := by rw [heq]
    exact h2.symm

theorem exists_order_three (M : ModDataE H E) {S : Subgroup G} (hSH : S ≤ H)
    (hK : Nat.Coprime 3 (Nat.card ↥(H ⊓ Subgroup.centralizer (E : Set G))))
    (h3 : 3 ∣ Nat.card ↥(M.img S)) :
    ∃ P : Subgroup G, P ≤ S ∧ Nat.card ↥P = 3 ∧ Nat.card ↥(M.img P) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardS : 3 ∣ Nat.card ↥S := by
    rw [M.card_img hSH] at h3
    exact h3.trans (Subgroup.relIndex_dvd_card (H := Subgroup.centralizer (E : Set G)) (K := S))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 3 hcardS
  let P : Subgroup G := (Subgroup.zpowers x).map S.subtype
  have hPS : P ≤ S := Subgroup.map_subtype_le _
  have hPcard : Nat.card ↥P = 3 := by
    show Nat.card ↥((Subgroup.zpowers x).map S.subtype) = 3
    rw [Subgroup.card_map_of_injective S.subtype_injective, Nat.card_zpowers, hx]
  refine ⟨P, hPS, hPcard, ?_⟩
  have hcardinf : Nat.card ↥(Subgroup.centralizer (E : Set G) ⊓ P) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes hK ?_ ?_
    · rw [← hPcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    · exact Subgroup.card_dvd_of_le fun y hy => ⟨(hPS.trans hSH) hy.2, hy.1⟩
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (E : Set G)) (K := P)
  rw [hcardinf, mul_one, hPcard] at hmul
  rw [M.card_img (hPS.trans hSH)]
  exact hmul

theorem img_normalizer_eq (M : ModDataE H E) {P : Subgroup G} (hPH : P ≤ H)
    (hP : Nat.card ↥P = 3)
    (hK : Nat.Coprime 3 (Nat.card ↥(H ⊓ Subgroup.centralizer (E : Set G)))) :
    M.img (H ⊓ Subgroup.normalizer (P : Set G)) =
      M.img H ⊓ Subgroup.normalizer ((M.img P : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · intro r hr
    exact ⟨M.img_mono inf_le_left hr,
      M.img_le_normalizer inf_le_left hPH inf_le_right hr⟩
  · rintro r ⟨hrH, hrN⟩
    obtain ⟨j, -, rfl⟩ := M.mem_img.1 hrH
    let C : Subgroup G := H ⊓ Subgroup.centralizer (E : Set G)
    let X : Subgroup G := P ⊔ C
    have hCH : C ≤ H := inf_le_left
    have hXH : X ≤ H := sup_le hPH hCH
    have hHnormC : H ≤ Subgroup.normalizer (C : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro h hh c hc
      refine ⟨H.mul_mem (H.mul_mem hh hc.1) (H.inv_mem hh), ?_⟩
      have hcE : c ∈ Subgroup.centralizer (E : Set G) := hc.2
      rw [Subgroup.mem_centralizer_iff] at hcE
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro e he
      have hhe : h⁻¹ * e * h ∈ E := by
        simpa using (Subgroup.mem_normalizer_iff.1 (M.le_normalizer (H.inv_mem hh)) e).1 he
      have h1 := hcE _ hhe
      exact (calc (h * c * h⁻¹) * e = h * c * (h⁻¹ * e * h) * h⁻¹ := by group
        _ = h * ((h⁻¹ * e * h) * c) * h⁻¹ := by rw [h1]; group
        _ = e * (h * c * h⁻¹) := by group).symm
    have hPnormC : P.subgroupOf X ≤ Subgroup.normalizer (C.subgroupOf X) := by
      rw [← Subgroup.subgroupOf_normalizer_eq (show C ≤ X from le_sup_right)]
      intro p hp
      exact hHnormC (hPH hp)
    have hCP : IsComplement' (C.subgroupOf X) (P.subgroupOf X) := by
      refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · refine Subgroup.disjoint_of_coprime_natCard ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ X from le_sup_right)).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show P ≤ X from le_sup_left)).toEquiv, hP]
        exact hK.symm
      · have hsup : (C.subgroupOf X) ⊔ (P.subgroupOf X) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup (show C ≤ X from le_sup_right)
              (show P ≤ X from le_sup_left)]
          rw [show C ⊔ P = P ⊔ C from sup_comm C P]
          exact Subgroup.subgroupOf_self X
        calc (↑(C.subgroupOf X) : Set ↥X) * (↑(P.subgroupOf X) : Set ↥X)
            = ↑((C.subgroupOf X) ⊔ (P.subgroupOf X)) :=
              (Subgroup.coe_mul_of_right_le_normalizer_left (C.subgroupOf X)
                (P.subgroupOf X) hPnormC).symm
          _ = (Set.univ : Set ↥X) := by rw [hsup]; rfl
    have hPsub : Nat.card ↥(P.subgroupOf X) = 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show P ≤ X from le_sup_left)).toEquiv).trans hP
    have hPgrp : IsPGroup 3 (P.subgroupOf X) := IsPGroup.of_card (n := 1) (by simpa using hPsub)
    have hPidxC : (P.subgroupOf X).index = Nat.card ↥C := by
      rw [← hCP.card_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ X from le_sup_right)).toEquiv
    have hPidx : ¬ 3 ∣ (P.subgroupOf X).index := by
      rw [hPidxC]
      exact (Nat.prime_three.coprime_iff_not_dvd).mp hK
    let Q : Subgroup G := P.map (MulAut.conj ((j : ↥H) : G)).toMonoidHom
    have hQcard : Nat.card ↥Q = 3 := by
      show Nat.card ↥(P.map (MulAut.conj ((j : ↥H) : G)).toMonoidHom) = 3
      rw [Subgroup.card_map_of_injective (MulAut.conj ((j : ↥H) : G)).injective, hP]
    have hQX : Q ≤ X := by
      intro q hq
      change q ∈ P.map (MulAut.conj ((j : ↥H) : G)).toMonoidHom at hq
      obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.1 hq
      let jx : ↥H := ⟨((j : ↥H) : G) * x * ((j : ↥H) : G)⁻¹,
        H.mul_mem (H.mul_mem j.2 (hPH hxP)) (H.inv_mem j.2)⟩
      have hconj : M.ρ j * M.ρ ⟨x, hPH hxP⟩ * (M.ρ j)⁻¹ ∈ M.img P :=
        (Subgroup.mem_normalizer_iff.1 hrN (M.ρ ⟨x, hPH hxP⟩)).1
          (M.mem_img.2 ⟨⟨x, hPH hxP⟩, hxP, rfl⟩)
      have heq : M.ρ jx = M.ρ j * M.ρ ⟨x, hPH hxP⟩ * (M.ρ j)⁻¹ := by
        have h1 : jx = j * ⟨x, hPH hxP⟩ * j⁻¹ := by
          apply Subtype.ext
          show ((j : ↥H) : G) * x * ((j : ↥H) : G)⁻¹ =
            ((j : ↥H) : G) * x * ((j : ↥H) : G)⁻¹
          rfl
        rw [h1, map_mul, map_mul, map_inv]
      have hmem_img : M.ρ jx ∈ M.img P := by rwa [heq]
      obtain ⟨p, hpP, hpρ⟩ := M.mem_img.1 hmem_img
      have hker : M.ρ (jx * p⁻¹) = 1 := by
        rw [map_mul, map_inv, hpρ]
        simp
      have hmemC : ((jx * p⁻¹ : ↥H) : G) ∈ C :=
        ⟨(jx * p⁻¹).2, (M.ρ_eq_one_iff _).1 hker⟩
      have hqc : (MulAut.conj ((j : ↥H) : G)) x = ((jx * p⁻¹ : ↥H) : G) * (p : G) := by
        have h2 : ((jx * p⁻¹ : ↥H) : G) * (p : G) = ((jx : ↥H) : G) := by
          rw [← Subgroup.coe_mul]
          congr 1
          group
        rw [h2]
        rfl
      change (MulAut.conj ((j : ↥H) : G)) x ∈ X
      rw [hqc]
      exact X.mul_mem (Subgroup.mem_sup_right hmemC) (Subgroup.mem_sup_left hpP)
    have hQsub : Nat.card ↥(Q.subgroupOf X) = 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv).trans hQcard
    have hQgrp : IsPGroup 3 (Q.subgroupOf X) := IsPGroup.of_card (n := 1) (by simpa using hQsub)
    have hcardX : Nat.card ↥X = 3 * Nat.card ↥C := by
      rw [← Subgroup.card_mul_index (H := P.subgroupOf X), hPsub, hPidxC]
    have hQidx : ¬ 3 ∣ (Q.subgroupOf X).index := by
      have hidx : (Q.subgroupOf X).index = Nat.card ↥C := by
        have := Subgroup.card_mul_index (H := Q.subgroupOf X)
        rw [hQsub, hcardX] at this
        omega
      rw [hidx]
      exact (Nat.prime_three.coprime_iff_not_dvd).mp hK
    let P1 : Sylow 3 ↥X := hPgrp.toSylow hPidx
    let Q1 : Sylow 3 ↥X := hQgrp.toSylow hQidx
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥X) P1 Q1
    have hg' : MulAut.conj g • (P.subgroupOf X) = Q.subgroupOf X :=
      congrArg (fun S : Sylow 3 ↥X => (S : Subgroup ↥X)) hg
    have hkq : ∀ q ∈ Q, ((g : ↥X) : G)⁻¹ * q * ((g : ↥X) : G) ∈ P := by
      intro q hq
      have hqX : q ∈ X := hQX hq
      have h1 : (⟨q, hqX⟩ : ↥X) ∈ MulAut.conj g • (P.subgroupOf X) := by
        rw [hg']
        exact hq
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa [MulAut.conj_inv_apply] using h2
    have hkH : ((g : ↥X) : G) ∈ H := hXH g.2
    let n : ↥H := ⟨((g : ↥X) : G)⁻¹ * ((j : ↥H) : G),
      H.mul_mem (H.inv_mem hkH) j.2⟩
    have hnNorm : ((n : ↥H) : G) ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply Subgroup.eq_of_le_of_card_ge
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
        have hxj : ((j : ↥H) : G) * x * ((j : ↥H) : G)⁻¹ ∈ Q := by
          change ((j : ↥H) : G) * x * ((j : ↥H) : G)⁻¹ ∈
            P.map (MulAut.conj ((j : ↥H) : G)).toMonoidHom
          exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
        have := hkq _ hxj
        simpa [MulAut.conj_apply, n, mul_assoc] using this
      · rw [Subgroup.card_map_of_injective (MulAut.conj ((n : ↥H) : G)).injective]
    have hkImg : M.ρ ⟨((g : ↥X) : G), hkH⟩ ∈ M.img (H ⊓ Subgroup.normalizer (P : Set G)) := by
      refine M.img_mono (le_inf hPH Subgroup.le_normalizer) ?_
      have himgX : M.img X = M.img P := by
        show M.img (P ⊔ C) = M.img P
        rw [M.img_sup hPH hCH]
        have hCker : M.img C = ⊥ := by
          rw [Subgroup.eq_bot_iff_forall]
          intro r hr
          obtain ⟨c, hc, rfl⟩ := M.mem_img.1 hr
          exact (M.ρ_eq_one_iff c).2 hc.2
        rw [hCker, sup_bot_eq]
      rw [← himgX]
      exact M.mem_img.2 ⟨⟨((g : ↥X) : G), hkH⟩, g.2, rfl⟩
    have hnImg : M.ρ n ∈ M.img (H ⊓ Subgroup.normalizer (P : Set G)) :=
      M.mem_img.2 ⟨n, ⟨n.2, hnNorm⟩, rfl⟩
    have hprod : M.ρ j = M.ρ ⟨((g : ↥X) : G), hkH⟩ * M.ρ n := by
      have h1 : (⟨((g : ↥X) : G), hkH⟩ : ↥H) * n = j := by
        apply Subtype.ext
        show ((g : ↥X) : G) * (((g : ↥X) : G)⁻¹ * ((j : ↥H) : G)) = ((j : ↥H) : G)
        group
      rw [← h1, map_mul]
    rw [hprod]
    exact (M.img (H ⊓ Subgroup.normalizer (P : Set G))).mul_mem hkImg hnImg

end Images

theorem normalizer_le_conj_of_stronglyEmbedded {M : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M) (g : G) {P : Subgroup G}
    (hP : P ≠ ⊥) (hP3 : IsPGroup 3 P) (hPM : P ≤ conjSubgroup M g) :
    Subgroup.normalizer (P : Set G) ≤ conjSubgroup M g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (CFSG.RankThree.PartOne.IsStronglyPEmbedded.conj hM g⁻¹).normalizer_le hP hP3 hPM

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem img_elemAbelian_quadratic (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g) :
    IsElemAbelian 2 (M.img (vInH V H g)) ∧
      CFSG.Quasithin.G11.commSpace (M.img (vInH V H g)) (commSub (M.img (vInH V H g))) = ⊥ :=
  ⟨M.isElemAbelian_img
      ((E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left),
    M.commSpace_commSub_img_eq_bot (A := vInH V H g) inf_le_right
      (x.hyp.quadratic_of_ne_bot (x.inf_ne_bot_of_gam183 hg))⟩

theorem exists_vector_conj (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {K : Subgroup (LGL 2 M.W)}
    {U₁ U₂ : Submodule (ZMod 2) M.W} (cfg : PGLConfig (M.img H) K U₁ U₂)
    (hAK : M.img (vInH V H g) ≤ K) (hA4 : Nat.card ↥(M.img (vInH V H g)) = 4) :
    ∃ w ∈ conjSubgroup V₀ g ⊓ eOmegaZ H D.T, w ≠ 1 ∧ (M.ι w ∈ U₁ ∨ M.ι w ∈ U₂) := by
  classical
  obtain ⟨hAe, -⟩ := x.img_elemAbelian_quadratic M hg
  obtain ⟨B, c, hBA, hmB, hc0, hcU, hcmem⟩ := cfg.exists_vector hAK hA4 hAe
  have hmB' : mOf (M.img (vInH V H g)) B ≤ x.iStar := by
    rw [hmB]
    exact x.iStar_pos
  have hsp := x.packU_cond2 M (M.img (vInH V H g)) ⟨g, hg, rfl⟩ B hBA hmB' hcmem
  rw [x.packSpaceU_eq_apply M hg] at hsp
  obtain ⟨w, hw, hwc⟩ := M.mem_sp.1 hsp
  refine ⟨w, hw, fun h1 => hc0 ?_, hwc ▸ hcU⟩
  rw [← hwc, h1]
  exact M.ι_one

theorem false_of_le_conj (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) (hH : H ≤ conjSubgroup D.M g) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMg : conjSubgroup D.M g = Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [← x.hyp.setting.normalizer_eq, E3.conjSubgroup_normalizer]
  have hnorm : H ≤ Subgroup.normalizer (vInH V H g : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have h1 : h ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := hMg ▸ hH hh
    have h2 := (Subgroup.mem_normalizer_iff.1 h1) a
    constructor
    · rintro ⟨ha1, ha2⟩
      exact ⟨h2.1 ha1, H.mul_mem (H.mul_mem hh ha2) (H.inv_mem hh)⟩
    · rintro ⟨ha1, ha2⟩
      refine ⟨h2.2 ha1, ?_⟩
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) ha2) hh
      simpa [mul_assoc] using this
  have hab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  have hle : M.img (vInH V H g) ≤ pCoreOf 2 (M.img H) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (M.img_mono inf_le_right)
      (M.img_le_normalizer le_rfl inf_le_right hnorm) (M.isPGroup_img hab.isPGroup)
  have hmem : M.img (vInH V H g) ∈ packFamilyU D V H i M := ⟨g, hg, rfl⟩
  have h0 := x.packU_inf_pCore M _ hmem
  rw [inf_eq_left.2 hle] at h0
  exact packU_ne_bot M _ hmem h0

end Ctx188

theorem le_conj_M_of_pglConfig {D : Data G} {V₀ V H E : Subgroup G}
    (hset : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (M : ModDataE H E)
    (hK : Nat.Coprime 3 (Nat.card ↥(H ⊓ Subgroup.centralizer (E : Set G)))) {g w : G}
    (hw : w ∈ conjSubgroup V₀ g) (hwE : w ∈ E) (hw1 : w ≠ 1)
    {K : Subgroup (LGL 2 M.W)} {U₁ U₂ : Submodule (ZMod 2) M.W}
    (cfg : PGLConfig (M.img H) K U₁ U₂) (hc : M.ι w ∈ U₁ ∨ M.ι w ∈ U₂) :
    H ≤ conjSubgroup D.M g := by
  classical
  have hc0 : M.ι w ≠ 0 := fun h => hw1 (M.ι_eq_zero w hwE h)
  have hCw : Subgroup.centralizer ({w} : Set G) ≤ conjSubgroup D.M g :=
    centralizer_le_conj_M hset hV₀ g hw hw1
  have hSimg := img_inf_centralizer_eq M hwE
  obtain ⟨-, hcard24⟩ := cfg.stab_le_and_card hc hc0
  have h3 : 3 ∣ Nat.card ↥(M.img (H ⊓ Subgroup.centralizer ({w} : Set G))) := by
    rw [hSimg, hcard24]
    norm_num
  obtain ⟨P, hPS, hP3, hP3'⟩ := exists_order_three M inf_le_left hK h3
  have hPH : P ≤ H := hPS.trans inf_le_left
  have hPM : P ≤ conjSubgroup D.M g := hPS.trans (inf_le_right.trans hCw)
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP3
    omega
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by simpa using hP3)
  have hN : Subgroup.normalizer (P : Set G) ≤ conjSubgroup D.M g :=
    normalizer_le_conj_of_stronglyEmbedded hsp g hPbot hPp hPM
  have hNimg := img_normalizer_eq M hPH hP3 hK
  have hPimg : M.img P ≤ centralizerOn (M.img H) (Submodule.span (ZMod 2) {M.ι w}) :=
    hSimg ▸ M.img_mono hPS
  have hsup := cfg.sup_eq hc hc0 hPimg hP3'
  have hSX : H ⊓ Subgroup.centralizer ({w} : Set G) ≤ H ⊓ conjSubgroup D.M g :=
    inf_le_inf_left _ hCw
  have hNX : H ⊓ Subgroup.normalizer (P : Set G) ≤ H ⊓ conjSubgroup D.M g :=
    inf_le_inf_left _ hN
  have hYle : M.img H ≤ M.img (H ⊓ conjSubgroup D.M g) := by
    rw [← hsup, ← hSimg, ← hNimg]
    exact sup_le (M.img_mono hSX) (M.img_mono hNX)
  intro h hh
  obtain ⟨j, hjX, hj⟩ := M.mem_img.1 (hYle (M.mem_img.2 ⟨⟨h, hh⟩, hh, rfl⟩))
  have hker : M.ρ (j⁻¹ * ⟨h, hh⟩) = 1 := by
    rw [map_mul, map_inv, hj]
    simp
  have hcen := (M.ρ_eq_one_iff _).1 hker
  have hcw : ((j⁻¹ * ⟨h, hh⟩ : ↥H) : G) ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwE) hcen
  have h1 : (j : G)⁻¹ * h ∈ conjSubgroup D.M g := hCw hcw
  have h2 : (j : G) ∈ conjSubgroup D.M g := hjX.2
  have h3 : h = (j : G) * ((j : G)⁻¹ * h) := by group
  rw [h3]
  exact Subgroup.mul_mem _ h2 h1

end CFSG.LocalAnalysis.WeakClosure81

end
