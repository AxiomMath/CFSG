module

public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenExtra
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SL3FourRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.RankThree.PartTwo.KFacts.L34

theorem center_qSub_card {k : Type*} [Field k] (hk : Nat.card k = 4) :
    Nat.card (Subgroup.center (qSub (k := k))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 3) k) := inferInstance
  have hcard : Nat.card (qSub (k := k)) = 3 ^ 3 := by
    rw [card_qSub hk]
    norm_num
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hnc : ∃ a ∈ qSub (k := k), ∃ b ∈ qSub (k := k), a * b ≠ b * a := by
    refine ⟨hSL u, hSL_mem_qSub, rSL, rSL_mem_qSub, ?_⟩
    intro h
    have h1 : hSL u * rSL * (hSL u)⁻¹ * rSL⁻¹ = 1 := by rw [h]; group
    rw [hSL_commutator hk, inv_eq_one] at h1
    have h0 := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
      (g : Matrix (Fin 3) (Fin 3) k)) h1) 0) 0
    simp only [zSL, coe_dHom, Matrix.SpecialLinearGroup.coe_one] at h0
    simp at h0
    exact hu h0
  obtain ⟨n, hn0, hn⟩ := IsPGroup.card_center_eq_prime_pow (G := qSub (k := k)) (p := 3)
    (n := 3) hcard (by norm_num)
  have hdvd : Nat.card (Subgroup.center (qSub (k := k))) ∣ 3 ^ 3 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd ⊢
  have hnle : n ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 hdvd
  interval_cases n
  · norm_num
  · exfalso
    have hq : Nat.card (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) = 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (qSub (k := k)))
      rw [card_qSub hk, hn] at h
      norm_num at h
      have h9 : 3 * 9 = Nat.card (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) * 9 := by
        rw [h.symm]
      exact (Nat.mul_right_cancel (by norm_num : 0 < 9) h9).symm
    haveI : IsCyclic (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) :=
      isCyclic_of_prime_card (p := 3) hq
    have hcomm : IsMulCommutative (qSub (k := k)) :=
      isMulCommutative_of_isCyclic_quotient_center_self _
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · exfalso
    have htop : Subgroup.center (qSub (k := k)) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hn, card_qSub hk]
      norm_num
    have hcomm : IsMulCommutative (qSub (k := k)) := Subgroup.center_eq_top_iff.mp htop
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem isElementaryAbelian_quotient_qSub {k : Type*} [Field k] (hk : Nat.card k = 4) :
    CFSG.IsElementaryAbelian 3
      (↥(qSub (k := k)) ⧸ Subgroup.center (qSub (k := k))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 3) k) := inferInstance
  have hZ := center_qSub_card hk
  have hquot : Nat.card (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (qSub (k := k)))
    rw [card_qSub hk, hZ] at h
    have h9 : 9 * 3 = Nat.card (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) * 3 := by
      rw [h.symm]
    exact (Nat.mul_right_cancel (by norm_num : 0 < 3) h9).symm
  refine CFSG.IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv ?_
  refine isElementaryAbelian_three_of_card (H := ⊤) ?_ ?_
  · rw [Subgroup.card_top]
    exact hquot
  · intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (qSub (k := k))) x
    obtain ⟨g, hg⟩ := y
    rw [← SetLike.mem_coe, coe_qSub] at hg
    obtain ⟨z, rfl⟩ := hg
    have hy3 : (⟨qElt z, hg⟩ : qSub (k := k)) ^ 3 = 1 :=
      Subtype.ext (qElt_pow_three hk z)
    rw [← map_pow, hy3, map_one]

theorem isExtraspecial_qSub {k : Type*} [Field k] (hk : Nat.card k = 4) :
    CFSG.IsExtraspecial 3 (qSub (k := k)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 3) k) := inferInstance
  refine ⟨center_qSub_card hk, isElementaryAbelian_quotient_qSub hk, ?_⟩
  have hquot : Nat.card (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (qSub (k := k)))
    rw [card_qSub hk, center_qSub_card hk] at h
    have h9 : 9 * 3 = Nat.card (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) * 3 := by
      rw [h.symm]
    exact (Nat.mul_right_cancel (by norm_num : 0 < 3) h9).symm
  haveI : Finite (qSub (k := k) ⧸ Subgroup.center (qSub (k := k))) := inferInstance
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hquot]; norm_num)

theorem isExtraspecial_statedSL_sylow {k : Type} [Field k] (hk : Nat.card k = 4)
    {P : Subgroup (↥(StatedSL 3 k))} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) :
    CFSG.IsExtraspecial 3 P ∧ Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 3) k) := inferInstance
  let e : Matrix.SpecialLinearGroup (Fin 3) k ≃* ↥(StatedSL 3 k) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 k
  have hfactSL : (Nat.card (Matrix.SpecialLinearGroup (Fin 3) k)).factorization 3 = 3 := by
    rw [card_specialLinearGroup hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 60480 = 3 ^ 3 * 2240 by norm_num) (by norm_num)
  have hfactStated : (Nat.card (↥(StatedSL 3 k))).factorization 3 = 3 := by
    rw [CFSG.Open.StatedAPI.card_statedSL, hfactSL]
  have hPcard : Nat.card P = 27 := by
    have h := hP.card_eq (p := 3) (K := ⊤)
    rw [Subgroup.card_top, hfactStated] at h
    simpa using h
  let Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) := P.map (e.symm : _ →* _)
  have hQcard : Nat.card Q = 27 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective e.symm.injective, hPcard]
  have hQfact : Nat.card Q = 3 ^ (Nat.card (Matrix.SpecialLinearGroup (Fin 3) k)).factorization 3 := by
    rw [hQcard, hfactSL]
    norm_num
  have hqfact : Nat.card (qSub (k := k)) =
      3 ^ (Nat.card (Matrix.SpecialLinearGroup (Fin 3) k)).factorization 3 := by
    rw [card_qSub hk, hfactSL]
    norm_num
  let SQ : Sylow 3 (Matrix.SpecialLinearGroup (Fin 3) k) := Sylow.ofCard Q hQfact
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map (P := qSub (k := k))
    (L := Matrix.SpecialLinearGroup (Fin 3) k) hqfact SQ
  have hQeq : Q = (qSub (k := k)).map (MulAut.conj g).toMonoidHom := by
    simpa [SQ] using hg
  let heQ : qSub (k := k) ≃* Q :=
    ((MulAut.conj g).subgroupMap (qSub (k := k))).trans
      (MulEquiv.subgroupCongr hQeq.symm)
  have hQext : CFSG.IsExtraspecial 3 Q := by
    haveI : CFSG.IsExtraspecial 3 (qSub (k := k)) := isExtraspecial_qSub hk
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv heQ.symm
  have hQmap : Q.map (e : Matrix.SpecialLinearGroup (Fin 3) k →* ↥(StatedSL 3 k)) = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rw [← hzy]
      simpa using hz
    · intro hx
      exact ⟨e.symm x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩
  let heQP : Q ≃* P :=
    (e.subgroupMap Q).trans (MulEquiv.subgroupCongr hQmap)
  have hPext : CFSG.IsExtraspecial 3 P := by
    haveI : CFSG.IsExtraspecial 3 Q := hQext
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv heQP.symm
  exact ⟨hPext, hPcard⟩


theorem isExtraspecial_sylow_three_of_isSL3Four_of_certificates
    {X : Type} [Group X] [Finite X]
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four X)
    {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) :
    CFSG.IsExtraspecial 3 P ∧ Nat.card P = 27 := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.nonempty_mulEquiv_statedSL_of_isSL3Four h
  letI := hKfield
  letI := hKfin
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcardX : Nat.card P = 3 ^ (Nat.card X).factorization 3 := by
    have h := hP.card_eq (p := 3) (K := ⊤)
    rwa [Subgroup.card_top] at h
  let P' : Subgroup (↥(StatedSL 3 K)) := P.map (e : X →* ↥(StatedSL 3 K))
  have hP'card : Nat.card P' =
      3 ^ (Nat.card (↥(StatedSL 3 K))).factorization 3 := by
    dsimp [P']
    rw [Subgroup.card_map_of_injective e.injective, hPcardX,
      Nat.card_congr e.toEquiv]
  have hP'cardTop : Nat.card P' =
      3 ^ (Nat.card (⊤ : Subgroup (↥(StatedSL 3 K)))).factorization 3 := by
    rwa [Subgroup.card_top]
  have hP'sylow : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top hP'cardTop
  obtain ⟨hP'ext, hP'card27⟩ := isExtraspecial_statedSL_sylow hKcard hP'sylow
  haveI : CFSG.IsExtraspecial 3 P' := hP'ext
  let he : P ≃* P' := e.subgroupMap P
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv he
  · rw [Nat.card_congr he.toEquiv, hP'card27]


theorem pow_three_qSub {k : Type*} [Field k] (hk : Nat.card k = 4)
    (x : qSub (k := k)) : x ^ 3 = 1 := by
  have hx : (x : Matrix.SpecialLinearGroup (Fin 3) k) ∈ (qSub (k := k) : Set _) := x.2
  rw [coe_qSub] at hx
  obtain ⟨z, hz⟩ := hx
  have hmem : qElt z ∈ qSub (k := k) := by rw [hz]; exact x.2
  have hxeq : (⟨qElt z, hmem⟩ : qSub (k := k)) = x := Subtype.ext hz
  rw [← hxeq]
  exact Subtype.ext (qElt_pow_three hk z)

theorem pow_three_statedSL_sylow {k : Type} [Field k] (hk : Nat.card k = 4)
    {P : Subgroup (↥(StatedSL 3 k))} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) :
    ∀ x : P, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 3) k) := inferInstance
  let e : Matrix.SpecialLinearGroup (Fin 3) k ≃* ↥(StatedSL 3 k) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 k
  have hfactSL : (Nat.card (Matrix.SpecialLinearGroup (Fin 3) k)).factorization 3 = 3 := by
    rw [card_specialLinearGroup hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 60480 = 3 ^ 3 * 2240 by norm_num) (by norm_num)
  have hfactStated : (Nat.card (↥(StatedSL 3 k))).factorization 3 = 3 := by
    rw [CFSG.Open.StatedAPI.card_statedSL, hfactSL]
  have hPcard : Nat.card P = 27 := by
    have h := hP.card_eq (p := 3) (K := ⊤)
    rw [Subgroup.card_top, hfactStated] at h
    simpa using h
  let Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) := P.map (e.symm : _ →* _)
  have hQcard : Nat.card Q = 27 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective e.symm.injective, hPcard]
  have hQfact : Nat.card Q =
      3 ^ (Nat.card (Matrix.SpecialLinearGroup (Fin 3) k)).factorization 3 := by
    rw [hQcard, hfactSL]
    norm_num
  have hqfact : Nat.card (qSub (k := k)) =
      3 ^ (Nat.card (Matrix.SpecialLinearGroup (Fin 3) k)).factorization 3 := by
    rw [card_qSub hk, hfactSL]
    norm_num
  let SQ : Sylow 3 (Matrix.SpecialLinearGroup (Fin 3) k) := Sylow.ofCard Q hQfact
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map (P := qSub (k := k))
    (L := Matrix.SpecialLinearGroup (Fin 3) k) hqfact SQ
  have hQeq : Q = (qSub (k := k)).map (MulAut.conj g).toMonoidHom := by
    simpa [SQ] using hg
  let heQ : qSub (k := k) ≃* Q :=
    ((MulAut.conj g).subgroupMap (qSub (k := k))).trans
      (MulEquiv.subgroupCongr hQeq.symm)
  have hQmap : Q.map (e : Matrix.SpecialLinearGroup (Fin 3) k →* ↥(StatedSL 3 k)) = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rw [← hzy]
      simpa using hz
    · intro hx
      exact ⟨e.symm x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩
  let heQP : Q ≃* P :=
    (e.subgroupMap Q).trans (MulEquiv.subgroupCongr hQmap)
  intro x
  have h := pow_three_qSub hk (heQ.symm (heQP.symm x))
  have h' := congrArg heQP (congrArg heQ h)
  simpa [map_pow] using h'

theorem pow_three_of_isSL3Four_sylow
    {X : Type} [Group X] [Finite X]
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four X)
    {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) :
    ∀ x : P, x ^ 3 = 1 := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.nonempty_mulEquiv_statedSL_of_isSL3Four h
  letI := hKfield
  letI := hKfin
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcardX : Nat.card P = 3 ^ (Nat.card X).factorization 3 := by
    have h := hP.card_eq (p := 3) (K := ⊤)
    rwa [Subgroup.card_top] at h
  let P' : Subgroup (↥(StatedSL 3 K)) := P.map (e : X →* ↥(StatedSL 3 K))
  have hP'card : Nat.card P' =
      3 ^ (Nat.card (↥(StatedSL 3 K))).factorization 3 := by
    dsimp [P']
    rw [Subgroup.card_map_of_injective e.injective, hPcardX,
      Nat.card_congr e.toEquiv]
  have hP'cardTop : Nat.card P' =
      3 ^ (Nat.card (⊤ : Subgroup (↥(StatedSL 3 K)))).factorization 3 := by
    rwa [Subgroup.card_top]
  have hP'sylow : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top hP'cardTop
  have hexp' : ∀ y : P', y ^ 3 = 1 := pow_three_statedSL_sylow hKcard hP'sylow
  let he : P ≃* P' := e.subgroupMap P
  intro x
  have h := hexp' (he x)
  simpa [map_pow] using he.injective (by simpa [map_pow] using h : he (x ^ 3) = he 1)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
