module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreStatement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

theorem eq_one_of_pow_two_pow_of_odd {A : Type*} [Group A] {a : A} {m n : ℕ}
    (ha : a ^ (2 ^ n) = 1) (hm : Odd m) (ham : a ^ m = 1) : a = 1 := by
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha)
    (orderOf_dvd_of_pow_eq_one ham))

theorem oddCore_quotient_eq_bot_of_central {A : Type*} [Group A] [Finite A] (N : Subgroup A)
    [N.Normal] (hNc : N ≤ Subgroup.center A) (hN2 : IsPGroup 2 N)
    (hA : CFSG.oddCore A = ⊥) : CFSG.oddCore (A ⧸ N) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore (A ⧸ N) with hOdef
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card _
  set R := O.comap (QuotientGroup.mk' N) with hRdef
  have hNR : N ≤ R := fun n hn => by
    change QuotientGroup.mk' N n ∈ O
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact O.one_mem
  have hRcard : Nat.card R = Nat.card N * Nat.card O := by
    have h1 : R.index = O.index :=
      Subgroup.index_comap_of_surjective O (QuotientGroup.mk'_surjective N)
    have h2 := R.card_mul_index
    have h3 := O.card_mul_index
    have h4 := N.card_mul_index
    have hpos : 0 < R.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card R * R.index = Nat.card A := h2
      _ = Nat.card N * N.index := h4.symm
      _ = Nat.card N * (Nat.card O * O.index) := by rw [h3]; rfl
      _ = Nat.card N * Nat.card O * R.index := by rw [h1]; ring
  set N' := N.subgroupOf R with hN'def
  have : N'.Normal := Subgroup.normal_subgroupOf
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
  have hN'index : N'.index = Nat.card O := by
    have h1 := N'.card_mul_index
    rw [hN'card, hRcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  obtain ⟨m, hm⟩ := hN2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hN'card, hm, hN'index]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hOodd)
  obtain ⟨D', hD'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hD'card : Nat.card D' = Nat.card O := by
    have h1 := hD'.card_mul_card
    rw [hN'card, hRcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hoddmem : ∀ x : R, Odd (orderOf x) → x ∈ D' := by
    intro x hx
    obtain ⟨⟨n, d⟩, hnd⟩ := hD'.2 x
    change (n : R) * (d : R) = x at hnd
    have hnc : Commute (n : R) (d : R) := by
      have hnA : ((n : R) : A) ∈ Subgroup.center A := hNc n.2
      exact Subtype.ext (Subgroup.mem_center_iff.mp hnA _).symm
    have hk : ((n : R) ^ orderOf x) * ((d : R) ^ orderOf x) = 1 := by
      rw [← hnc.mul_pow, hnd, pow_orderOf_eq_one]
    have hnk1 : (n : R) ^ orderOf x = 1 := by
      have hdisj := hD'.disjoint
      rw [Subgroup.disjoint_def] at hdisj
      exact hdisj (N'.pow_mem n.2 _) (by
        rw [eq_inv_of_mul_eq_one_left hk]
        exact D'.inv_mem (D'.pow_mem d.2 _))
    obtain ⟨a, ha⟩ := hN2 ⟨((n : R) : A), n.2⟩
    have hna : (n : R) ^ (2 ^ a) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val ha
      simpa using this
    have hn1 : (n : R) = 1 := eq_one_of_pow_two_pow_of_odd hna hx hnk1
    rw [← hnd, hn1, one_mul]
    exact d.2
  set D := D'.map R.subtype with hDdef
  have hDcard : Nat.card D = Nat.card O := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hD'card]
  have hDnormal : D.Normal := by
    constructor
    rintro _ ⟨d, hd, rfl⟩ g
    have hdR : g * (d : A) * g⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem _ d.2 g
    refine ⟨⟨g * (d : A) * g⁻¹, hdR⟩, hoddmem _ ?_, rfl⟩
    have hord : orderOf (⟨g * (d : A) * g⁻¹, hdR⟩ : R) = orderOf d := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe d]
      show orderOf (g * (d : A) * g⁻¹) = orderOf (d : A)
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hord]
    exact (hD'card ▸ hOodd).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hd)
  have hDO : D ≤ CFSG.oddCore A :=
    CFSG.ComponentClassification.OddCore.maximal A D hDnormal (hDcard ▸ hOodd)
  rw [hA, le_bot_iff] at hDO
  have hO1 : Nat.card O = 1 := by rw [← hDcard, hDO, Subgroup.card_bot]
  exact Subgroup.card_eq_one.mp hO1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem point_sup_eq_top_of_two_transitive {H L : Subgroup G}
    (htwo : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    {x : G} (hxL : x ∈ L) (hxH : x ∉ H) : H ⊔ L = ⊤ := by
  rw [eq_top_iff]
  intro g _
  by_cases hgH : g ∈ H
  · exact Subgroup.mem_sup_left hgH
  have hne : ∀ y : G, y ∉ H → rightCosetMk H y ≠ rightCosetMk H 1 := fun y hy hy1 =>
    hy ((PairInvolutionFixedField.translate_base_iff H y).mp
      ((PairInvolutionFixedField.translate_base_mk H y).trans hy1))
  obtain ⟨h, hhα, hhx⟩ := htwo (rightCosetMk H 1) (rightCosetMk H x) (rightCosetMk H 1)
    (rightCosetMk H g) (hne x hxH).symm (hne g hgH).symm
  have hhH : h ∈ H := (PairInvolutionFixedField.translate_base_iff H h).mp hhα
  rw [rightCosetTranslate_mk] at hhx
  have hmem : g * (x * h)⁻¹ ∈ H := (PairInvolutionFixedField.rightCosetMk_eq_iff H _ _).mp hhx
  have hg : g = g * (x * h)⁻¹ * x * h := by group
  rw [hg]
  exact (H ⊔ L).mul_mem ((H ⊔ L).mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hxL))
    (Subgroup.mem_sup_left hhH)

theorem oddCore_root_centralizer_eq_bot
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
      (minimalLocalFailurePairActionPointHull H z : Set G)) = ⊥ := by
  obtain ⟨-, htwo, -, -, -, hJeq, -, hQJ, hJQ, hidx, -⟩ :=
    minimalLocalFailure_linear_point_kernel_and_odd_centralizers_of_conclusions h hcomm
      hsmallerR1 hbeta ht hproper hlin hexcl
  obtain ⟨hQH, -, hQnormal, hQab, -, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨-, ⟨e, hQe⟩, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set J := Subgroup.centralizer (K : Set G) with hJdef
  set C := H ⊓ Subgroup.centralizer (Q : Set G) with hCdef
  have hCnormal : (C.subgroupOf H).Normal :=
    (TwoCoreGrowth.point_two_core_of_normal_root_centralizer H Q hQH hQnormal
      (TwoCoreGrowth.original_point_hull_centralizes_two_core h.local_datum h.central_sylow)).1
  have hCn := (Subgroup.normal_subgroupOf_iff (inf_le_left : C ≤ H)).mp hCnormal
  have hJB : J ≤ pairPointStabilizer H beta := by
    rw [hJeq]
    exact inf_le_left
  have hJC : J ≤ C := le_inf (hJB.trans (pairPointStabilizer_le_point H beta)) hJQ
  have hQQ : Q ≤ Subgroup.centralizer (Q : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hQab.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hQJC : Q ⊔ J ≤ C := sup_le (le_inf hQH hQQ) hJC
  set D := (CFSG.oddCore C).map C.subtype with hDdef
  have hDodd : Odd (Nat.card D) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card _
  have hDC : D ≤ C := Subgroup.map_subtype_le _
  have hDnC : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    rintro c hc _ ⟨d, hd, rfl⟩
    exact ⟨⟨c, hc⟩ * d * ⟨c, hc⟩⁻¹, (CFSG.oddCore_normal (G := C)).conj_mem d hd _, rfl⟩
  have hDH : ∀ g ∈ H, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    set D' := D.map (MulAut.conj g).toMonoidHom with hD'def
    have hD'C : D' ≤ C := by
      rintro _ ⟨d, hd, rfl⟩
      exact hCn d g (hDC hd) hg
    have hD'n : (D'.subgroupOf C).Normal := by
      refine (Subgroup.normal_subgroupOf_iff hD'C).mpr ?_
      rintro _ c ⟨d, hd, rfl⟩ hc
      have hc' : g⁻¹ * c * g ∈ C := by
        simpa only [inv_inv] using hCn c g⁻¹ hc (H.inv_mem hg)
      refine ⟨(g⁻¹ * c * g) * d * (g⁻¹ * c * g)⁻¹, hDnC _ hc' d hd, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hD'odd : Odd (Nat.card (D'.subgroupOf C)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD'C).toEquiv,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hDodd
    have hle := CFSG.ComponentClassification.OddCore.maximal C _ hD'n hD'odd
    have hmem : (⟨g * d * g⁻¹, hD'C ⟨d, hd, rfl⟩⟩ : C) ∈ D'.subgroupOf C := ⟨d, hd, rfl⟩
    exact ⟨_, hle hmem, rfl⟩
  have hDQJ : D ≤ Q ⊔ J := by
    have hBN : Q ⊔ J ≤ Subgroup.normalizer (D : Set G) := fun c hc =>
      Subgroup.mem_normalizer_iff.mpr fun d => ⟨fun hd => hDnC c (hQJC hc) d hd, fun hd => by
        have := hDnC c⁻¹ (C.inv_mem (hQJC hc)) _ hd
        rwa [show c⁻¹ * (c * d * c⁻¹) * c⁻¹⁻¹ = d by group] at this⟩
    have hprod := card_sup_mul_card_inf_of_le_normalizer hBN
    have hsupC : D ⊔ (Q ⊔ J) ≤ C := sup_le hDC hQJC
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hsupC
    have hrel := Subgroup.relIndex_mul_card (Q ⊔ J) C
    rw [inf_eq_left.mpr hQJC] at hrel
    have hrelD := Subgroup.relIndex_mul_card (D ⊓ (Q ⊔ J)) D
    rw [inf_eq_left.mpr inf_le_left] at hrelD
    set s := (D ⊓ (Q ⊔ J)).relIndex D with hsdef
    have hpos1 : 0 < Nat.card (D ⊓ (Q ⊔ J) : Subgroup G) := Nat.card_pos
    have hpos2 : 0 < Nat.card (Q ⊔ J : Subgroup G) := Nat.card_pos
    have hsup : Nat.card (D ⊔ (Q ⊔ J) : Subgroup G) = s * Nat.card (Q ⊔ J : Subgroup G) := by
      apply Nat.eq_of_mul_eq_mul_right hpos1
      rw [hprod, ← hrelD]
      ring
    have hsr : s ∣ (Q ⊔ J).relIndex C := by
      refine ⟨m, Nat.eq_of_mul_eq_mul_right hpos2 ?_⟩
      rw [hrel, hm, hsup]
      ring
    have hs2 : s ∣ 2 ^ (2 * e) := by
      rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
      have h1 := hsr.trans hidx
      rw [hQe, ← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num] at h1
      exact h1
    have hsodd : s ∣ Nat.card D := ⟨Nat.card (D ⊓ (Q ⊔ J) : Subgroup G), hrelD.symm⟩
    have hcop : Nat.Coprime (2 ^ (2 * e)) (Nat.card D) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hDodd)
    have hs1 : s = 1 := Nat.eq_one_of_dvd_coprimes hcop hs2 hsodd
    exact Subgroup.relIndex_eq_one.mp hs1 |>.trans inf_le_right
  have hJN : J ≤ Subgroup.normalizer (Q : Set G) :=
    hJQ.trans (Subgroup.centralizer_le_normalizer (s := (Q : Set G)))
  have hDJ : D ≤ J := by
    intro d hd
    have hd' : d ∈ (Q : Set G) * (J : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q J hJN]
      exact hDQJ hd
    obtain ⟨a, ha, b, hb, rfl⟩ := hd'
    have hab : Commute a b := (Subgroup.mem_centralizer_iff.mp (hJQ hb) a ha)
    have hodd : Odd (orderOf (a * b)) := hDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hd)
    have hk : a ^ orderOf (a * b) * b ^ orderOf (a * b) = 1 := by
      rw [← hab.mul_pow, pow_orderOf_eq_one]
    have hak : a ^ orderOf (a * b) = 1 := by
      have hmem : a ^ orderOf (a * b) ∈ Q ⊓ J := by
        refine ⟨Q.pow_mem ha _, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hk]
        exact J.inv_mem (J.pow_mem hb _)
      rwa [hQJ, Subgroup.mem_bot] at hmem
    have ha2 : a ^ (2 ^ 1) = 1 := by rw [pow_one]; exact hQab.2 a ha
    show a * b ∈ J
    rw [eq_one_of_pow_two_pow_of_odd ha2 hodd hak, one_mul]
    exact hb
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  have htH : t ∉ H := pair_flip_not_mem_point hbeta ht
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := fun k hk =>
    CyclicSemiregular.mem_normalizer_of_forall_inv_conj_mem fun v hv => by
      have hkv : k * v = v * k := Subgroup.mem_centralizer_iff.mp (hDJ hv) k hk
      rw [mul_assoc, ← hkv, inv_mul_cancel_left]
      exact hv
  have hHD : H ≤ Subgroup.normalizer (D : Set G) := fun g hg =>
    CyclicSemiregular.mem_normalizer_of_forall_inv_conj_mem fun v hv => by
      simpa only [inv_inv] using hDH g⁻¹ (H.inv_mem hg) v hv
  have htop : H ⊔ K = ⊤ := point_sup_eq_top_of_two_transitive htwo htK htH
  have hDnormal : D.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_unique (htop ▸ sup_le hHD hKD))
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (self := hsimple) D) with hbot | htopD
  · exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hbot
  · exfalso
    have hGodd : Odd (Nat.card G) := by
      rw [← Subgroup.card_top (G := G), ← htopD]
      exact hDodd
    have hz2 : 2 ∣ Nat.card G := by
      rw [← h.local_datum.distinguished_order]
      exact orderOf_dvd_natCard z
    exact (Nat.not_even_iff_odd.mpr hGodd) (even_iff_two_dvd.mpr hz2)

theorem minimalLocalFailure_linear_point_kernel_odd_core_free_quotient_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    RootCentralizerOddCoreFreeConclusion H z := by
  unfold RootCentralizerOddCoreFreeConclusion
  intro Q C
  obtain ⟨hQH, -, hQnormal, hQab, hQp, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  have hQQ : Q ≤ Subgroup.centralizer (Q : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hQab.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hQC : Q ≤ C := le_inf hQH hQQ
  have hQCn : (Q.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (inf_le_left.trans hHQ)
  have hcentral : Q.subgroupOf C ≤ Subgroup.center C := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2.2 q hq).symm
  have h2 : IsPGroup 2 (Q.subgroupOf C) := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  exact ⟨hQCn, oddCore_quotient_eq_bot_of_central (Q.subgroupOf C) hcentral h2
    (oddCore_root_centralizer_eq_bot h hcomm hsmallerR1 hbeta ht hproper hlin hexcl)⟩

end CFSG.ShultStronglyClosedTI.LinearChain
