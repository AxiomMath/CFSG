module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuterPGL
public import CFSG.Quasithin.EmptyFaithful.Insp9QS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s1715six_conj_trichotomy (D : Data G) (h82 : F08.R82 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL7 : IsL2Over17 (Bar2 L) 7) (hk2 : D.k = 2)
    {x y : G} (hx : x ∈ D.M) (hy : y ∈ D.M) :
    L.map (MulAut.conj x).toMonoidHom = L ∨ L.map (MulAut.conj y).toMonoidHom = L ∨
      L.map (MulAut.conj y).toMonoidHom = L.map (MulAut.conj x).toMonoidHom := by
  by_contra h
  push Not at h
  have hk := k_eq_one_of_three_conj D h82 hL hL7 hx hy h.1 h.2.1 h.2.2
  omega

theorem s1715six_conj_mem_normalizer (D : Data G) (h82 : F08.R82 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL7 : IsL2Over17 (Bar2 L) 7) (hk2 : D.k = 2)
    {m n : G} (hm : m ∈ D.M) (hn : n ∈ D.M) (hnL : n ∈ normalizer (L : Set G)) :
    m * n * m⁻¹ ∈ normalizer (L : Set G) := by
  by_contra hconj
  have hm1 : m⁻¹ ∈ D.M := D.M.inv_mem hm
  have hnm : n * m⁻¹ ∈ D.M := D.M.mul_mem hn (D.M.inv_mem hm)
  have h1 : L.map (MulAut.conj m⁻¹).toMonoidHom ≠ L := by
    intro h
    have hm1N : m⁻¹ ∈ normalizer (L : Set G) :=
      (UC6S846.mem_normalizer_iff_map_conj).2 h
    have hmN : m ∈ normalizer (L : Set G) := by
      simpa using (Subgroup.normalizer (L : Set G)).inv_mem hm1N
    exact hconj ((Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).mul_mem hmN hnL)
      ((Subgroup.normalizer (L : Set G)).inv_mem hmN))
  have h2 : L.map (MulAut.conj (n * m⁻¹)).toMonoidHom ≠ L := by
    intro h
    have hnmN : n * m⁻¹ ∈ normalizer (L : Set G) :=
      (UC6S846.mem_normalizer_iff_map_conj).2 h
    have hm1N : m⁻¹ ∈ normalizer (L : Set G) := by
      simpa [mul_assoc] using
        (Subgroup.normalizer (L : Set G)).mul_mem
          ((Subgroup.normalizer (L : Set G)).inv_mem hnL) hnmN
    have hmN : m ∈ normalizer (L : Set G) := by
      simpa using (Subgroup.normalizer (L : Set G)).inv_mem hm1N
    exact hconj ((Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).mul_mem hmN hnL)
      ((Subgroup.normalizer (L : Set G)).inv_mem hmN))
  have h3 : L.map (MulAut.conj (n * m⁻¹)).toMonoidHom ≠ L.map (MulAut.conj m⁻¹).toMonoidHom := by
    intro h
    apply hconj
    have h' := congrArg (fun S : Subgroup G => S.map (MulAut.conj m).toMonoidHom) h
    simp only [Subgroup.map_map] at h'
    have e1 : (MulAut.conj m).toMonoidHom.comp (MulAut.conj (n * m⁻¹)).toMonoidHom =
        (MulAut.conj (m * n * m⁻¹)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e2 : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [e1, e2, Subgroup.map_id] at h'
    exact (UC6S846.mem_normalizer_iff_map_conj).2 h'
  rcases s1715six_conj_trichotomy D h82 hL hL7 hk2 hm1 hnm with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

theorem s1715six_normalizer_normal (D : Data G) (h82 : F08.R82 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL7 : IsL2Over17 (Bar2 L) 7) (hk2 : D.k = 2) :
    ((D.M ⊓ normalizer (L : Set G)).subgroupOf D.M).Normal := by
  refine (Subgroup.normal_subgroupOf_iff inf_le_left).2 ?_
  intro y n hy hn
  exact ⟨D.M.mul_mem (D.M.mul_mem hn hy.1) (D.M.inv_mem hn),
    s1715six_conj_mem_normalizer D h82 hL hL7 hk2 hn hy.1 hy.2⟩

theorem s1715six_conj_eq_or_eq (D : Data G) (h82 : F08.R82 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL7 : IsL2Over17 (Bar2 L) 7) (hk2 : D.k = 2)
    {x₀ m : G} (hx₀ : x₀ ∈ D.M) (hx₀N : x₀ ∉ normalizer (L : Set G)) (hm : m ∈ D.M) :
    conjSubgroup L m = L ∨ conjSubgroup L m = conjSubgroup L x₀ := by
  have h := s1715six_conj_trichotomy D h82 hL hL7 hk2 (D.M.inv_mem hx₀) (D.M.inv_mem hm)
  rcases h with h1 | h2 | h3
  · exact absurd (conjSubgroup_eq_iff_mem_normalizer.1 (show conjSubgroup L x₀ = L from h1)) hx₀N
  · exact Or.inl h2
  · exact Or.inr h3

theorem s1715six_conj_eq_of_barSub_eq {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKb : barSub V₀ V h.isElemAbelian K ≠ ⊥)
    {m : G} (hm : m ∈ D.M)
    (heq : barSub V₀ V h.isElemAbelian (conjSubgroup K m) = barSub V₀ V h.isElemAbelian K) :
    conjSubgroup K m = K := by
  have hV := h.isElemAbelian
  by_contra hne
  have hKmcal : conjSubgroup K m ∈ calC D.M :=
    uc22p22u_calC_conj (X := D.M) (M := D.M) (K := K) Subgroup.le_normalizer hK (m := m) hm
  have hcommG' : ⁅barSub V₀ V hV K, barSub V₀ V hV (conjSubgroup K m)⁆ = ⊥ := by
    have hle : ⁅K, conjSubgroup K m⁆ ≤ pCoreOf 2 K :=
      (calC_commutator_le_of_ne hK hKmcal (fun h => hne h.symm)).trans inf_le_left
    have hbot : barSub V₀ V hV (pCoreOf 2 K) = ⊥ :=
      TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hK.1
        (barSub_pCoreOf_eq_bot_of_hyp125 h)
    have hmap : barSub V₀ V hV ⁅K, conjSubgroup K m⁆ = ⊥ :=
      le_bot_iff.1 (hbot ▸ barSub_mono V₀ V hV hle)
    have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
    have hKstab : K ≤ stabTil V₀ V := hK.1.le.trans hMs
    have hKmM : conjSubgroup K m ≤ D.M := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have hy' : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [hy']
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hm) (hK.1.le hy)) hm
    have hlebar := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.commutator_barSub_le
      (V₀ := V₀) (V := V) hV hKstab (hKmM.trans hMs)
    exact le_bot_iff.1 (hmap ▸ hlebar)
  have hcommG : ⁅barSub V₀ V hV K, barSub V₀ V hV K⁆ = ⊥ := by
    rwa [heq] at hcommG'
  have hcent : barSub V₀ V hV K ≤
      Subgroup.centralizer (barSub V₀ V hV K : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommG
  have hcomm : ∀ a b : ↥(barSub V₀ V hV K), a * b = b * a := by
    intro a b
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent a.2) b b.2).symm
  have hcomp := barSub_mem_compBar_of_ne_bot h hK hKb
  have hqC : CFSG.IsQuasisimple ↥(barSub V₀ V hV K) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2
  exact CFSG.Quasithin.Insp9.qs_not_commutative hqC hcomm

theorem s1715six_not_pgl (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D)
    (h111 : W3Thm111 G) (h127 : R127 D) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h117 : C117 D V₀ V) (h1771 : R17_7_1At D V₀ V L r q hC)
    (hB : B17_15BoundK2 D V₀ V L r q hC) (h7 : IsL2Over17 (Bar2 L) 7) (hV0 : V₀ = ⊥)
    (hk2 : D.k = 2) (hm4 : mBar D.M V₀ V hC.hyp125.isElemAbelian = 4)
    (hfix : fixV (barSub V₀ V hC.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥) :
    ¬ CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)) := by
  subst hV0
  intro hP
  have hL1 : barSub ⊥ V hC.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 hC.hyp125 h117 hC.memL h1771
  have hb : bBar (UC22.conjClosure D.M L) D.M ⊥ V hC.hyp125.isElemAbelian ≤ 1 :=
    hB hL1 h7 hP hk2 hfix
  have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
      (TwelveTwentyThree.conjClosure_le hC.memL.1.le) h1771
  have hm3 := twelve_twentyThree_one D hx h61 h126 h111 hC.hyp125 rfl
    hC.memL.1 hC.memL.2.2 hL1 hUc
  omega

theorem s1715six_exists_inner (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (h7 : IsL2Over17 (Bar2 L) 7)
    (hnot : ¬ CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)))
    (hnorm : ((D.M ⊓ normalizer (L : Set G)).subgroupOf D.M).Normal)
    {n : G} (hn : n ∈ D.M ⊓ normalizer (L : Set G)) :
    ∃ l ∈ L, l⁻¹ * n ∈ centSection D.M L (CFSG.Open.pCoreOf 2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := D.M ⊓ normalizer (L : Set G)
  let S : Subgroup G := NTL17 D L
  let LS : Subgroup G := L ⊔ S
  have hLM : L ≤ D.M := hL.1.le
  have hSNL : S ≤ normalizer (L : Set G) := inf_le_right
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLSN : LS ≤ N := by
    refine sup_le (le_inf hLM Subgroup.le_normalizer) (le_inf ?_ hSNL)
    exact inf_le_left.trans hTM
  have hdataLS := bar2_sup_data (L := L) (R := S) hS2 hSNL h7
  have hLS7 : IsL2Over17 (Bar2 LS) 7 := by
    rcases hdataLS.2 with h | h
    · exact h
    · exact absurd h hnot
  have hLScard : Nat.card (Bar2 LS) = 168 :=
    card_of_isL2Odd_seven (isL2Odd_seven_of_isL2Over17_seven hLS7)
  have hLcard : Nat.card (Bar2 L) = 168 :=
    card_of_isL2Odd_seven (isL2Odd_seven_of_isL2Over17_seven h7)
  have hZ : Subgroup.center (Bar2 L) = ⊥ := by
    have hsc : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 2 7 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num)
        (isL2Odd_seven_of_isL2Over17_seven h7)
    obtain ⟨-, F, _, _, -, ⟨eF⟩⟩ := hsc
    let e' : Bar2 L ≃* CFSG.GorensteinWalter.PSL2 F :=
      eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e'
      (CFSG.GorensteinWalter.psl2_center_eq_bot F)
  let I : Subgroup (MulAut (Bar2 L)) := (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range
  have hIcard : Nat.card ↥I = 168 := by
    rw [← hLcard]
    exact (Nat.card_congr (CFSG.Quasithin.Vol2.Ch11.SecB.rangeConjEquiv hZ).toEquiv).symm
  let φN : ↥N →* MulAut (Bar2 L) := autBar2 (L := L) (N := D.M)
  let φLS : ↥LS →* MulAut (Bar2 L) := φN.comp (Subgroup.inclusion hLSN)
  have hLSnorm : (L.subgroupOf LS).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSNL)
  have hcentK : Subgroup.centralizer ((L.subgroupOf LS).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥LS)) : Set (Bar2 LS)) = ⊥ := by
    simpa [LS, S] using hdataLS.1
  have hcentLS : CFSG.Open.pCoreOf 2 LS = centSection LS L (oTwoThreeIn L) :=
    pCoreOf_eq_centSection le_sup_left hLSnorm h7 hcentK
  have hker : φLS.ker = (CFSG.Open.pCoreOf 2 LS).subgroupOf LS := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxφ : φN (Subgroup.inclusion hLSN x) = 1 := by simpa [φLS] using hx
      have hx' : (Subgroup.inclusion hLSN x : G) ∈ centSection D.M L (pCoreOf 2 L) :=
        (autBar2_eq_one_iff (Subgroup.inclusion hLSN x)).mp hxφ
      have hxLS' : (x : G) ∈ centSection LS L (oTwoThreeIn L) := by
        rw [oTwoThreeIn_eq_pCoreOf h7]
        exact ⟨x.2, hx'.2.1, hx'.2.2.1, hx'.2.2.2⟩
      rw [← hcentLS] at hxLS'
      exact hxLS'
    · intro hx
      have hx' : (x : G) ∈ centSection LS L (oTwoThreeIn L) := by
        rw [← hcentLS]
        exact hx
      obtain ⟨-, hxNL, hxNB, hxcomm⟩ := hx'
      rw [oTwoThreeIn_eq_pCoreOf h7] at hxNB hxcomm
      have hmem : (Subgroup.inclusion hLSN x : G) ∈ centSection D.M L (pCoreOf 2 L) :=
        ⟨(hLSN x.2).1, hxNL, hxNB, hxcomm⟩
      have h1 : φN (Subgroup.inclusion hLSN x) = 1 :=
        (autBar2_eq_one_iff (Subgroup.inclusion hLSN x)).mpr hmem
      simpa [φLS] using h1
  have hrangeCard : Nat.card ↥φLS.range = 168 := by
    have h1 : Nat.card ↥φLS.ker * Nat.card ↥φLS.range = Nat.card ↥LS := by
      rw [← Subgroup.index_ker φLS, Subgroup.card_mul_index]
    have h2 : Nat.card ↥(CFSG.pCore 2 ↥LS) * Nat.card (Bar2 LS) = Nat.card ↥LS := by
      have h := Subgroup.card_mul_index (H := CFSG.pCore 2 ↥LS) (G := ↥LS)
      rwa [Subgroup.index_eq_card] at h
    rw [hker, CFSG.openPCoreOf_subgroupOf, ← h2] at h1
    have := Nat.mul_left_cancel (Nat.card_pos (α := ↥(CFSG.pCore 2 ↥LS))) h1
    simpa [hLScard] using this
  have hinnerL : ∀ v : ↥L,
      φN (Subgroup.inclusion hLSN ⟨(v : G), Subgroup.mem_sup_left v.2⟩) =
        MulAut.conj (QuotientGroup.mk v) := by
    intro v
    ext y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    rw [autBar2_apply_mk_coe, MulAut.conj_apply]
    have hnorm : (Subgroup.normalizerMonoidHom L
        (Subgroup.inclusion inf_le_right
          (Subgroup.inclusion hLSN ⟨(v : G), Subgroup.mem_sup_left v.2⟩)) w : ↥L) =
        (v : ↥L) * w * (v : ↥L)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [hnorm]
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (v * w * v⁻¹ : ↥L) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) v *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) w *
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)) v)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hIle : I ≤ φLS.range := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨(v : G), Subgroup.mem_sup_left v.2⟩, hinnerL v⟩
  have hRangeEq : φLS.range = I := by
    exact (Subgroup.eq_of_le_of_card_ge hIle (by rw [hIcard, hrangeCard])).symm
  have hInorm : I.Normal := CFSG.Quasithin.Vol2.Ch11.SecB.normal_range_conj (Bar2 L)
  let π : MulAut (Bar2 L) →* MulAut (Bar2 L) ⧸ I := QuotientGroup.mk' I
  let θ : ↥N →* MulAut (Bar2 L) ⧸ I := π.comp φN
  let P' : Subgroup ↥N := θ.ker
  let S' : Subgroup ↥N := S.subgroupOf N
  have hSyleq : S' ≤ P' := by
    intro x hx
    have hxS : (x : G) ∈ S := hx
    have hxLS : (x : G) ∈ LS := Subgroup.mem_sup_right hxS
    have hxe : (Subgroup.inclusion hLSN ⟨(x : G), hxLS⟩ : ↥N) = x := Subtype.ext rfl
    have hxI : φN x ∈ I := by
      rw [← hxe, ← hRangeEq]
      exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hxLS⟩, rfl⟩
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (φN x)).mpr hxI
  have hSylow : IsSylowIn 2 S N := by
    have hST : D.T ⊓ N = S := by
      ext x
      simp only [N, S, NTL17, Subgroup.mem_inf]
      constructor
      · rintro ⟨hxT, -, hxN⟩
        exact ⟨hxT, hxN⟩
      · rintro ⟨hxT, hxN⟩
        exact ⟨hxT, hTM hxT, hxN⟩
    rw [← hST]
    exact CFSG.Quasithin.IsSylowIn.inf_normal (TwelveShort.isSylowIn_of_le D D.sylowM.le)
      inf_le_left hnorm
  have hSodd : Odd S'.index := by
    have h := hSylow.not_dvd_relIndex
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact h
  have hPodd : Odd P'.index :=
    Odd.of_dvd_nat hSodd (Subgroup.index_dvd_of_le hSyleq)
  have hIindex : I.index = 2 := by
    have h := Subgroup.card_mul_index (H := I) (G := MulAut (Bar2 L))
    rw [hIcard, card_mulAut_of_isL2Over17_seven h7] at h
    omega
  have hquotcard : Nat.card (MulAut (Bar2 L) ⧸ I) = 2 := by
    rw [← Subgroup.index_eq_card, hIindex]
  have hPcard : P'.index = Nat.card ↥θ.range := Subgroup.index_ker θ
  have hPdvd2 : P'.index ∣ 2 := by
    rw [hPcard]
    exact (Subgroup.card_subgroup_dvd_card θ.range).trans (by rw [hquotcard])
  have hPone : P'.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hPdvd2 with h | h
    · exact h
    · rw [h] at hPodd
      exact absurd even_two (Nat.not_even_iff_odd.mpr hPodd)
  have hPtop : P' = ⊤ := Subgroup.index_eq_one.mp hPone
  have hkerall : ∀ x : ↥N, x ∈ θ.ker := by
    intro x
    change x ∈ P'
    rw [hPtop]
    exact Subgroup.mem_top x
  have hmemI : φN ⟨n, hn⟩ ∈ I := by
    have h1 : θ ⟨n, hn⟩ = 1 := hkerall ⟨n, hn⟩
    exact (QuotientGroup.eq_one_iff (φN ⟨n, hn⟩)).mp h1
  obtain ⟨q, hq⟩ := hmemI
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  let vN : ↥N := Subgroup.inclusion hLSN ⟨(v : G), Subgroup.mem_sup_left v.2⟩
  have hvN : (v : G) ∈ N := vN.2
  have hvn : (v : G)⁻¹ * n ∈ N := by
    refine ⟨D.M.mul_mem (D.M.inv_mem (hLM v.2)) hn.1, ?_⟩
    exact (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).inv_mem (Subgroup.le_normalizer v.2)) hn.2
  refine ⟨(v : G), v.2, ?_⟩
  have heq : (⟨(v : G)⁻¹ * n, hvn⟩ : ↥N) = vN⁻¹ * ⟨n, hn⟩ := by
    ext
    rfl
  have hφ1 : φN ⟨(v : G)⁻¹ * n, hvn⟩ = 1 := by
    rw [heq, map_mul, map_inv, hinnerL v, hq]
    group
  exact (autBar2_eq_one_iff ⟨(v : G)⁻¹ * n, hvn⟩).mp hφ1

theorem s1715six_normIn_eq (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hLb : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hinner : ∀ n ∈ D.M ⊓ normalizer (L : Set G), ∃ l ∈ L,
      l⁻¹ * n ∈ centSection D.M L (CFSG.Open.pCoreOf 2 L)) :
    normIn (Mbar D.M V₀ V h.isElemAbelian) (barSub V₀ V h.isElemAbelian L) =
      barSub V₀ V h.isElemAbelian L ⊔
        centGroupIn (Mbar D.M V₀ V h.isElemAbelian) (barSub V₀ V h.isElemAbelian L) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hbotL : barSub V₀ V hV (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)
  apply le_antisymm
  · intro φ hφ
    obtain ⟨hφM, hφN⟩ := hφ
    obtain ⟨n, hnM, hφeq⟩ := (mem_barSub V₀ V hV D.M φ).1 hφM
    have hφmap : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom = barSub V₀ V hV L :=
      UC6S846.mem_normalizer_iff_map_conj.1 hφN
    have hφmap' : (barSub V₀ V hV L).map (MulAut.conj φ⁻¹).toMonoidHom = barSub V₀ V hV L :=
      UC6S846.mem_normalizer_iff_map_conj.1
        ((Subgroup.normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).inv_mem hφN)
    have hconj : barSub V₀ V hV (conjSubgroup L (n : G)) =
        (barSub V₀ V hV L).map (MulAut.conj (actTil V₀ V hV n)⁻¹).toMonoidHom :=
      s15_Infra_barSub_conjSubgroup V₀ V hV n.2 L
    rw [hφeq, hφmap'] at hconj
    have hnN : (n : G) ∈ normalizer (L : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.1
        (s1715six_conj_eq_of_barSub_eq h hL hLb hnM hconj)
    obtain ⟨l, hlL, hc⟩ := hinner (n : G) ⟨hnM, hnN⟩
    let c : G := l⁻¹ * (n : G)
    have hcM : c ∈ D.M := centSection_le D.M L (CFSG.Open.pCoreOf 2 L) hc
    have hlstab : l ∈ stabTil V₀ V := hMs (hL.1.le hlL)
    have hcstab : c ∈ stabTil V₀ V := hMs hcM
    let ls : stabTil V₀ V := ⟨l, hlstab⟩
    let cs : stabTil V₀ V := ⟨c, hcstab⟩
    have hc_center : actTil V₀ V hV cs ∈
        Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro ψ hψ
      obtain ⟨a, haL, rfl⟩ := (mem_barSub V₀ V hV L ψ).1 hψ
      have hstabcomm : c * (a : G) * c⁻¹ * (a : G)⁻¹ ∈ stabTil V₀ V :=
        (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem hcstab a.2)
          ((stabTil V₀ V).inv_mem hcstab)) ((stabTil V₀ V).inv_mem a.2)
      let ds : stabTil V₀ V := ⟨c * (a : G) * c⁻¹ * (a : G)⁻¹, hstabcomm⟩
      have hds : ds = ⁅cs, a⁆ := by
        ext
        simp [ds, cs, commutatorElement_def, mul_assoc]
      have hcomm1 : ⁅actTil V₀ V hV cs, actTil V₀ V hV a⁆ = 1 := by
        rw [← map_commutatorElement, ← hds]
        have hmem : actTil V₀ V hV ds ∈ barSub V₀ V hV (pCoreOf 2 L) :=
          actTil_mem_barSub V₀ V hV (hc.2.2.2 (a : G) haL) hstabcomm
        rw [hbotL] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm
    have hlc : ls * cs = n := by
      ext
      show l * (l⁻¹ * (n : G)) = (n : G)
      group
    have hmemL : actTil V₀ V hV ls ∈ barSub V₀ V hV L :=
      actTil_mem_barSub V₀ V hV hlL hlstab
    have hmemC : actTil V₀ V hV cs ∈
        centGroupIn (Mbar D.M V₀ V hV) (barSub V₀ V hV L) :=
      ⟨actTil_mem_barSub V₀ V hV hcM hcstab, hc_center⟩
    have hprod : actTil V₀ V hV ls * actTil V₀ V hV cs = φ := by
      calc actTil V₀ V hV ls * actTil V₀ V hV cs
          = actTil V₀ V hV (ls * cs) := (map_mul _ _ _).symm
        _ = actTil V₀ V hV n := by rw [hlc]
        _ = φ := hφeq
    rw [← hprod]
    exact Subgroup.mul_mem_sup hmemL hmemC
  · refine sup_le ?_ ?_
    · intro a ha
      exact ⟨barSub_mono V₀ V hV hL.1.le ha, Subgroup.le_normalizer ha⟩
    · intro b hb
      refine ⟨hb.1, ?_⟩
      exact Subgroup.centralizer_le_normalizer
        (G := MulAut (Vtil V₀ V hV)) (barSub V₀ V hV L : Set _) hb.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
