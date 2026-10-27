module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNLift
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

open Subgroup

variable {G : Type} [Group G] [Finite G]

variable {N T A : Subgroup G} {r : ℕ}

omit [Finite G] in
theorem barIn_commutator {H X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    barIn H ⁅X, Y⁆ = ⁅barIn H X, barIn H Y⁆ := by
  rw [barIn, barIn, barIn, ← CFSG.GroupTheory.commutator_subgroupOf_eq hX hY,
    Subgroup.map_commutator]

theorem Hyp146N.exists_lift (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) {q : ℕ} (hq : q.Prime) (hqr : q ≠ r)
    {P : Subgroup (UC22.BarInf (UC22.conjClosure N A))} (hP : IsPGroup q P)
    (hAP : barIn (UC22.conjClosure N A) A ≤
      normalizer (P : Set (UC22.BarInf (UC22.conjClosure N A)))) :
    ∃ S : Subgroup G, S ≤ UC22.conjClosure N A ∧ IsPGroup q S ∧ A ≤ normalizer (S : Set G) ∧
      barIn (UC22.conjClosure N A) S = P := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  let H : Subgroup G := UC22.conjClosure N A
  let R : Subgroup ↥H := CFSG.solvableRadical ↥H
  let π : ↥H →* UC22.BarInf H := QuotientGroup.mk' R
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hker : π.ker = R := QuotientGroup.ker_mk' R
  have hRleK : R ≤ P.comap π := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxker : x ∈ π.ker := by rw [hker]; exact hx
    rw [MonoidHom.mem_ker.mp hxker]
    exact P.one_mem
  have hAcard : Nat.card (A.subgroupOf H) = r := by
    rw [← h.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hAp : IsPGroup r (A.subgroupOf H) :=
    IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hAK : A.subgroupOf H ≤ normalizer ((P.comap π : Subgroup ↥H) : Set ↥H) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hAP (Subgroup.mem_map_of_mem π ha)) (π x)).1 hx
    · intro hx
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv] at hx
      exact (Subgroup.mem_normalizer_iff.mp (hAP (Subgroup.mem_map_of_mem π ha)) (π x)).2 hx
  have hRcard : Nat.card R = Nat.card (UC22.OInf H) := by
    rw [UC22.OInf]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hPnotdvd : ¬ r ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    intro hdvd
    have hdvd' : r ∣ q := h.prime.dvd_of_dvd_pow hdvd
    exact hqr ((Nat.Prime.dvd_iff_eq hq h.prime.ne_one).mp hdvd')
  have hKcard : Nat.card (P.comap π : Subgroup ↥H) = Nat.card R * Nat.card P := by
    have hc := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card π hπsurj P
    rwa [hker] at hc
  have hcop : ¬ r ∣ Nat.card (P.comap π : Subgroup ↥H) := by
    rw [hKcard]
    intro hdvd
    rcases h.prime.dvd_mul.mp hdvd with h1 | h1
    · rw [hRcard] at h1
      exact h.not_dvd_card_OInf hns h1
    · exact hPnotdvd h1
  obtain ⟨S', hS'syl, hAS'⟩ :=
    CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime
      (p := r) (r := q) h.prime hq hAp hAK hcop
  have hS'K : S' ≤ P.comap π := hS'syl.le
  have hPmap : (P.comap π : Subgroup ↥H).map π = P :=
    Subgroup.map_comap_eq_self_of_surjective hπsurj P
  have hrel : (S'.map π).relIndex P = (S' ⊔ R).relIndex (P.comap π : Subgroup ↥H) := by
    conv_lhs => rw [← hPmap]
    rw [Subgroup.relIndex_map_map, hker, sup_eq_left.mpr hRleK]
  have hrel_dvd : (S' ⊔ R).relIndex (P.comap π : Subgroup ↥H) ∣ S'.relIndex (P.comap π) := by
    exact Subgroup.relIndex_dvd_of_le_left (H := S') (K := S' ⊔ R)
      (L := (P.comap π : Subgroup ↥H)) le_sup_left
  have hnotdvd : ¬ q ∣ S'.relIndex (P.comap π : Subgroup ↥H) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hS'syl).2.2
  have hmapP : S'.map π = P := by
    have hle : S'.map π ≤ P := by
      calc S'.map π ≤ (P.comap π : Subgroup ↥H).map π := Subgroup.map_mono hS'K
        _ = P := Subgroup.map_comap_eq_self_of_surjective hπsurj P
    have hSylImg : CFSG.ABGLocalTools.IsSylowOf q (S'.map π) P := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨hle, hS'syl.isPGroup.map π, ?_⟩
      rw [hrel]
      exact fun hdvd => hnotdvd (hdvd.trans hrel_dvd)
    exact (CFSG.ABGLocalTools.IsSylowOf.eq_of_le hSylImg hle le_rfl hP).symm
  let S : Subgroup G := S'.map H.subtype
  have hSH : S ≤ H := Subgroup.map_subtype_le S'
  have hSsub : S.subgroupOf H = S' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective S'
  have hbarS : barIn H S = P := by
    rw [barIn, hSsub]
    exact hmapP
  have hnorm : (normalizer (S : Set G)).subgroupOf H = normalizer (S' : Set ↥H) := by
    rw [Subgroup.subgroupOf_normalizer_eq hSH, hSsub]
  have hAS : A ≤ normalizer (S : Set G) := by
    intro a ha
    have haH : a ∈ H := hAH ha
    have ha' : (⟨a, haH⟩ : ↥H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr ha
    have hmem : (⟨a, haH⟩ : ↥H) ∈ (normalizer (S : Set G)).subgroupOf H := by
      rw [hnorm]
      exact hAS' ha'
    exact Subgroup.mem_subgroupOf.mp hmem
  exact ⟨S, hSH, hS'syl.isPGroup.map H.subtype, hAS, hbarS⟩

theorem Hyp146N.starCentralizes_barIn (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) :
    StarCentralizes (barIn (UC22.conjClosure N A) A) r := by
  classical
  let H : Subgroup G := UC22.conjClosure N A
  let R : Subgroup ↥H := CFSG.solvableRadical ↥H
  let π : ↥H →* UC22.BarInf H := QuotientGroup.mk' R
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  intro s hs hs2 hsr hrs P hP hAP
  obtain ⟨S, hSH, hSq, hAS, hbarS⟩ := h.exists_lift hns hs hsr hP hAP
  have hSrank : CFSG.Open.pRank s S ≤ 2 :=
    pRank_le_two_of_le hs hs2 (hSH.trans h.conjClosure_le) h.rank_three h.rank_two
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by simpa using h.card)
  have : Fact s.Prime := ⟨hs⟩
  have hAC : A ≤ centralizer (S : Set G) :=
    le_centralizer_of_not_dvd (G := G) hs2 h.prime hsr hrs hSq hSrank hAp hAS
  rw [← hbarS]
  intro x hx
  rw [barIn] at hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [barIn] at hy
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have hcomm : (b : G) * (a : G) = (a : G) * (b : G) :=
    Subgroup.mem_centralizer_iff.mp (hAC (Subgroup.mem_subgroupOf.mp ha))
      (b : G) (Subgroup.mem_subgroupOf.mp hb)
  have hcomm' : b * a = a * b := Subtype.ext hcomm
  calc π b * π a = π (b * a) := by rw [map_mul]
    _ = π (a * b) := by rw [hcomm']
    _ = π a * π b := by rw [map_mul]

theorem Hyp146N.bar_cases (h : Hyp146N N T A r) (hbar : K_UC146N_Bar)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) :
    BarOne (barIn (UC22.conjClosure N A) A) (barIn (UC22.conjClosure N A) T) ∨
      BarTwo (barIn (UC22.conjClosure N A) A) ∨
      BarThree (barIn (UC22.conjClosure N A) A) (barIn (UC22.conjClosure N A) T) r :=
  hbar (UC22.BarInf (UC22.conjClosure N A)) _ _ r h.isKGroup_barInf
    CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient h.prime h.three_lt
    h.two_pow (h.card_barIn hns) h.isSylowOf_barIn h.permutes_barIn h.normalClosure_barIn
    (h.pRank_barInf_le_one Nat.prime_three (by norm_num) h.rank_three)
    (h.pRank_barInf_le_one h.prime (by have := h.three_lt; omega) h.rank_r)
    (h.starCentralizes_barIn hns)

theorem Hyp146N.normalizer_barIn_le (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) :
    normalizer (barIn (UC22.conjClosure N A) A : Set (UC22.BarInf (UC22.conjClosure N A))) ≤
      barIn (UC22.conjClosure N A) (N ⊓ normalizer (A : Set G)) := by
  classical
  let H : Subgroup G := UC22.conjClosure N A
  let R : Subgroup ↥H := CFSG.solvableRadical ↥H
  let π : ↥H →* UC22.BarInf H := QuotientGroup.mk' R
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hRcard : Nat.card R = Nat.card (UC22.OInf H) := by
    rw [UC22.OInf]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hcop : Nat.Coprime r (Nat.card R) := by
    rw [Nat.Prime.coprime_iff_not_dvd h.prime, hRcard]
    exact h.not_dvd_card_OInf hns
  have : Fact r.Prime := ⟨h.prime⟩
  have hAcard : Nat.card (A.subgroupOf H) = r := by
    rw [← h.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hAp : IsPGroup r (A.subgroupOf H) :=
    IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have : Fact (IsPGroup r ↥(A.subgroupOf H)) := ⟨hAp⟩
  have hbarA : barIn H A = (A.subgroupOf H).map π := rfl
  have hnorm : normalizer ((A.subgroupOf H).map π : Set (UC22.BarInf H)) =
      ((normalizer (A.subgroupOf H) : Subgroup ↥H)).map π :=
    CFSG.normalizer_map_quotient_eq_map_normalizer r (A.subgroupOf H) R inferInstance hcop
  have htarget : barIn H (N ⊓ normalizer (A : Set G)) =
      ((N ⊓ normalizer (A : Set G)).subgroupOf H).map π := rfl
  rw [hbarA, htarget, hnorm]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map_of_mem π ?_
  rw [Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact h.conjClosure_le y.2
  · have hsubnorm : (normalizer (A : Set G)).subgroupOf H = normalizer (A.subgroupOf H) :=
      Subgroup.subgroupOf_normalizer_eq hAH
    have hyN : y ∈ (normalizer (A : Set G)).subgroupOf H := by
      rw [hsubnorm]
      exact hy
    exact Subgroup.mem_subgroupOf.mp hyN

theorem Hyp146N.centralizer_barIn_le (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A))
    (L : Subgroup (UC22.BarInf (UC22.conjClosure N A))) :
    centralizer (barIn (UC22.conjClosure N A) A : Set (UC22.BarInf (UC22.conjClosure N A))) ⊓ L ≤
      barIn (UC22.conjClosure N A)
        (centralizer (A : Set G) ⊓ liftIn (UC22.conjClosure N A) L) := by
  classical
  let H : Subgroup G := UC22.conjClosure N A
  let R : Subgroup ↥H := CFSG.solvableRadical ↥H
  let π : ↥H →* UC22.BarInf H := QuotientGroup.mk' R
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hRcard : Nat.card R = Nat.card (UC22.OInf H) := by
    rw [UC22.OInf]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hcop : Nat.Coprime r (Nat.card R) := by
    rw [Nat.Prime.coprime_iff_not_dvd h.prime, hRcard]
    exact h.not_dvd_card_OInf hns
  have : Fact r.Prime := ⟨h.prime⟩
  have hAcard : Nat.card (A.subgroupOf H) = r := by
    rw [← h.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hAp : IsPGroup r (A.subgroupOf H) :=
    IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have : Fact (IsPGroup r ↥(A.subgroupOf H)) := ⟨hAp⟩
  have hbarA : barIn H A = (A.subgroupOf H).map π := rfl
  have hcent : centralizer ((A.subgroupOf H).map π : Set (UC22.BarInf H)) =
      ((centralizer (A.subgroupOf H) : Subgroup ↥H)).map π :=
    CFSG.centralizer_map_quotient_eq_map_centralizer r (A.subgroupOf H) R inferInstance hcop
  have htarget : barIn H (centralizer (A : Set G) ⊓ liftIn H L) =
      ((centralizer (A : Set G) ⊓ liftIn H L).subgroupOf H).map π := rfl
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxC, hxL⟩ := hx
  have hxC' : x ∈ ((centralizer (A.subgroupOf H) : Subgroup ↥H)).map π := by
    rw [← hcent, ← hbarA]
    exact hxC
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hxC'
  rw [htarget]
  refine Subgroup.mem_map_of_mem π ?_
  rw [Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr ha
    exact congrArg Subtype.val (hc ⟨a, hAH ha⟩ ha')
  · have hcL : c ∈ L.comap π := by
      rw [Subgroup.mem_comap]
      exact hxL
    rw [liftIn]
    exact Subgroup.mem_map_of_mem H.subtype hcL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN
