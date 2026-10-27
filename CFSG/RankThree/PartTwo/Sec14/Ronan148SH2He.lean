module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeKFact
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor
public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SComp
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S

@[expose] def GoodA6 {S : Type} [Group S] (C : Subgroup S) : Prop :=
  ∀ K : Subgroup S, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal →
    ¬ IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))

section TransportA6

variable {S G' : Type} [Group S] [Group G']

theorem GoodA6.of_map [Finite S] (f : S →* G') (hf : Function.Injective f) {C : Subgroup S}
    (h : GoodA6 (C.map f)) : GoodA6 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  have eK : K ≃* K.map f := K.equivMapOfInjective f hf
  have hKq' : IsQuasisimple (K.map f) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq
  refine h (K.map f) (Subgroup.map_mono hKC) hKq' ?_
    (Sec13.isTripleCover_of_mulEquiv (thetaQuotCongr eK) hT)
  let eC : C ≃* C.map f := C.equivMapOfInjective f hf
  have heC : ∀ x : C, ((eC x : C.map f) : G') = f x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply C f hf x
  have hsurj : Function.Surjective (eC : C →* C.map f) := eC.surjective
  have hmap := hKs.map hsurj
  have heq : (K.subgroupOf C).map (eC : C →* C.map f) = (K.map f).subgroupOf (C.map f) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      rw [← heC x, hxy]
    · rintro ⟨x, hxK, rfl⟩
      refine ⟨⟨x, hKC hxK⟩, hxK, Subtype.ext ?_⟩
      rw [heC]
  rwa [heq] at hmap

theorem goodA6_centralizer_of_mulEquiv [Finite S] [Finite G'] (e : S ≃* G') {s : S}
    (h : GoodA6 (Subgroup.centralizer ({e s} : Set G'))) :
    GoodA6 (Subgroup.centralizer ({s} : Set S)) := by
  refine GoodA6.of_map (e : S →* G') e.injective ?_
  rwa [map_centralizer_singleton_equiv e s]

theorem GoodA6.of_isConj [Finite S] {a b : S} (hab : IsConj a b)
    (h : GoodA6 (Subgroup.centralizer ({a} : Set S))) :
    GoodA6 (Subgroup.centralizer ({b} : Set S)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hab
  have := goodA6_centralizer_of_mulEquiv (MulAut.conj c)⁻¹ (s := c * a * c⁻¹)
  apply this
  have h' : (MulAut.conj c)⁻¹ (c * a * c⁻¹) = a := by
    rw [MulAut.inv_apply, MulAut.conj_symm_apply]
    group
  rw [h']
  exact h

end TransportA6

section Inner

theorem rowH2_of_goodA6 {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    (hcube : CubeInner S)
    (h : ∀ s : S, orderOf s = 3 → GoodA6 (Subgroup.centralizer ({s} : Set S))) : RowH2 S := by
  intro Γ _ _ C hC4 hCθ _ A L K d hA hLA hdA hd1 _ hLq hCL hLd hKM hKsn hKq _ hA6 ⟨e⟩ hZL
  exfalso
  have hLC : L ≤ C := hLA ▸ le_sup_left
  have hAC : A ≤ C := hLA ▸ le_sup_right
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hKd : K ≤ Subgroup.centralizer {d} := hKM.trans inf_le_right
  have hZ3 := isPGroup_center_of_normal hCθ hLC hCL hLq
  obtain ⟨z, hzK, hKz, hz3, hZ⟩ := exists_pCore_center_eq_zpowers hKq hA6.1
  have hLz : ¬ L ≤ Subgroup.centralizer {z} := by
    intro hLz
    apply hZL
    rw [hZ, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLz hl)
  obtain ⟨-, hinf, -, -, -⟩ := exists_cq_bar hZ3 hKL hKq hzK hKz hz3 hZ hLz
  have hdN : d ∈ Subgroup.normalizer (L : Set Γ) := hCL (hAC hdA)
  set τ := descAut L ⟨d, hdN⟩ with hτ
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set Γ)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  obtain ⟨y, hy⟩ := cubeInner_of_mulEquiv e hcube τ hτ3
  have hZS : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hex : e x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g']
    rw [hcen, Subgroup.mem_bot] at hex
    exact (map_eq_one_iff e e.injective).mp hex
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hLd
    have hτ1 : τ = 1 := by rw [← hy, map_one]
    have hdC := (descAut_eq_one_iff hLq.1 ⟨d, hdN⟩).mp hτ1
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdC l hl
  have hy3 : y ^ 3 = 1 := by
    have hc : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, hy, hτ3]
    have hmem : y ^ 3 ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) => φ g) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [hg]
        _ = y ^ 3 * g := by group
    rw [hZS, Subgroup.mem_bot] at hmem
    exact hmem
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hfix : autFix τ = Subgroup.centralizer ({y} : Set (↥L ⧸ Subgroup.center ↥L)) := by
    rw [← hy]
    exact RonanK429H.autFix_conj y
  let eB := equivBar hKL hinf
  have hle : (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
      Subgroup.centralizer ({y} : Set (↥L ⧸ Subgroup.center ↥L)) := by
    rw [← hfix]
    exact map_le_autFix hdN hKd
  have hsn := isSubnormal_bar hdN hKM hKsn
  rw [← hτ, hfix] at hsn
  have hgood : GoodA6 (Subgroup.centralizer ({y} : Set (↥L ⧸ Subgroup.center ↥L))) :=
    goodA6_centralizer_of_mulEquiv e (h (e y) (by rw [MulEquiv.orderOf_eq]; exact hyo))
  exact hgood _ hle (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hKq) hsn
    (Sec13.isTripleCover_of_mulEquiv (thetaQuotCongr eB) hA6)

theorem rowOfH2_of_goodA6 {X : Type} [Group X] (hcube : CubeInner X)
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → ∀ s : S, orderOf s = 3 →
        GoodA6 (Subgroup.centralizer ({s} : Set S))) :
    RowOfH2 X := by
  intro S _ _ hs hna ⟨eX⟩
  exact rowH2_of_goodA6 (RonanK429H.center_eq_bot_of_simple_nonab hna) (cubeInner_of_mulEquiv eX hcube)
    (h S hs hna ⟨eX⟩)

end Inner

section He

open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
  CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.Sporadic.HeldB

theorem goodA6_heY : GoodA6 (Subgroup.centralizer ({heY} : Set heP)) := by
  obtain ⟨-, ⟨e''⟩, hQ⟩ := he_layer
  have hCq : IsQuasisimple ↥(Subgroup.centralizer ({heY} : Set heP)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e''.symm heTc_spec.2.1
  have hZ3 : Nat.card (Subgroup.center ↥(Subgroup.centralizer ({heY} : Set heP))) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e'').toEquiv]
    exact hQ.1
  have hcard : Nat.card ↥(Subgroup.centralizer ({heY} : Set heP)) = 7560 := by
    rw [Nat.card_congr e''.toEquiv]
    obtain ⟨hz, ⟨eq⟩⟩ := hQ
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥heTcQ)
    rw [Nat.card_congr eq.toEquiv, hz, KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at h1
    rw [h1]
    decide
  intro K hKC hKq hKs hT
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hKeq : K = Subgroup.centralizer ({heY} : Set heP) :=
    Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hKC hCq hKq.1 hnt hKs
  have h1080 := Sec13.card_eq_of_isTripleCover_six hT
  have hZ : IsPGroup 3 (Subgroup.center K) := by
    rw [hKeq]
    exact IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hθ := theta_eq_bot_of_center_three hKq hZ
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 K)
  have h3 : Nat.card (aschbacherSolvableCore 3 K) = 1 := by rw [hθ, Subgroup.card_bot]
  rw [h1080, h3, mul_one] at h2
  rw [hKeq, hcard] at h2
  exact absurd h2 (by norm_num)

theorem goodA6_heB {y : heP} (hy : (y : Equiv.Perm (Fin 8330)) = bOf heThreeWordsB) :
    GoodA6 (Subgroup.centralizer ({y} : Set heP)) := by
  have hcard : Nat.card ↥(Subgroup.centralizer ({y} : Set heP)) = 504 := by
    rw [card_centralizer_heP, hy]
    exact card_cent_B
  intro K hKC hKq hKs hT
  have h1080 := Sec13.card_eq_of_isTripleCover_six hT
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ 504 :=
    (card_theta_quot_dvd K).trans (hcard ▸ Subgroup.card_dvd_of_le hKC)
  rw [h1080] at hdvd
  exact absurd hdvd (by norm_num)

theorem goodA6_heP (y : heP) (hy : orderOf y = 3) :
    GoodA6 (Subgroup.centralizer ({y} : Set heP)) := by
  have hord : orderOf (y : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hy
  rcases three_conj_cases y.2 hord with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
  · refine GoodA6.of_isConj (a := heY) (isConj_iff.mpr ⟨⟨c, hc⟩, Subtype.ext ?_⟩) goodA6_heY
    simpa [heY] using hcx.symm
  · have hB : bOf heThreeWordsB ∈ heP := by
      have h := heP.mul_mem (heP.mul_mem (heP.inv_mem hc) y.2) hc
      have heq : c⁻¹ * (y : Equiv.Perm (Fin 8330)) * c = bOf heThreeWordsB := by
        have hcx' : c * bOf heThreeWordsB * c⁻¹ = (y : Equiv.Perm (Fin 8330)) := hcx.symm
        rw [← hcx']
        group
      rwa [heq] at h
    refine GoodA6.of_isConj (a := ⟨bOf heThreeWordsB, hB⟩)
      (isConj_iff.mpr ⟨⟨c, hc⟩, Subtype.ext ?_⟩) (goodA6_heB rfl)
    simpa using hcx.symm

theorem rowOfH2_he : RowOfH2 (Spor .He) := by
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .He ≃* Spor .He) :=
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  refine rowOfH2_of_goodA6 (cubeInner_of_not_three_dvd_card_outer spor_he.1) ?_
  intro S _ _ _ _ ⟨e⟩ s hs
  exact goodA6_centralizer_of_mulEquiv (e.trans (b.symm.trans heEquivP))
    (goodA6_heP _ (by rw [MulEquiv.orderOf_eq]; exact hs))

end He

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
