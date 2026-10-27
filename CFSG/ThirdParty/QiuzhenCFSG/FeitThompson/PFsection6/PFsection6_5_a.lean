module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_2_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_3

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe v
universe u

@[expose] public def theorem_6_5_a_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 : Subgroup L)
    (S SM : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_6_4_statement K M H1 S T →
    inducedKernelFamily K M SM →
      ¬ coherentFamily SM T →
        chiefFactorQuotient H1 K ∧
          H1.relIndex K ≤ 4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1

/-- Peterfalvi `(6.5)(b)`. -/


public theorem theorem_6_5_a_coherent_H1
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K M H1 : Subgroup L}
    {S SH1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h61 : hypothesis_6_1_statement K S T)
    (hH1norm : H1.Normal)
    (hcomm : commutatorQuotientHypothesis M H1 K)
    (hfrob : frobeniusQuotientWithKernel K H1)
    (hSH1 : inducedKernelFamily K H1 SH1) :
    coherentFamily SH1 T := by
  classical
  have : K.Normal := h61.2.1
  have hSbot : inducedKernelFamily K ⊥ S := hypothesis_6_1_inducedKernelFamily_bot h61
  have hsub : SH1 ⊆ S := inducedKernelFamily_subset_base hSbot hSH1
  have hH1ltK : H1 < K := frobeniusQuotientWithKernel_left_lt hfrob
  have hnonempty : SH1.Nonempty := by
    rcases inducedKernelFamily_nonempty_of_solvable_proper
        h61.2.2.1 hH1norm hH1ltK hSH1 with ⟨χ, hχ⟩
    exact ⟨χ, hχ⟩
  have hclosed : ∀ χ : Section1.ClassFunction L, χ ∈ SH1 →
      Section1.conjugateCharacter χ ∈ SH1 := by
    intro χ hχ
    exact inducedKernelFamily_conjugate_mem hSH1 hχ
  have h52SH1 : Section5.hypothesis_5_2_statement SH1 T :=
    Section5.hypothesis_5_2_statement_subset hsub hnonempty hclosed
      (hypothesis_6_1_hypothesis_5_2 h61)
  rcases h52SH1 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hKmodH1comm : IsMulCommutative (K ⧸ H1.subgroupOf K) :=
    commutatorQuotientHypothesis_quotient_commutative hH1norm hcomm
  have hdeg : ∀ X Y : SH1,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L) := by
    intro X Y
    have hX := inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
      hSH1 hH1norm hKmodH1comm X.2
    have hY := inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
      hSH1 hH1norm hKmodH1comm Y.2
    exact hX.trans hY.symm
  simpa [coherentFamily] using
    (Section5.theorem_5_7 SH1 T R hsetup h52a h52b h52c h52d h52e hdeg)

public theorem theorem_6_5_a_index_bound
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K M H1 : Subgroup L}
    {S SM SH1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h64 : hypothesis_6_4_statement K M H1 S T)
    (hSM : inducedKernelFamily K M SM)
    (hnotSM : ¬ coherentFamily SM T)
    (hSH1 : inducedKernelFamily K H1 SH1)
    (hcohSH1 : coherentFamily SH1 T) :
    H1.relIndex K ≤ 4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1 := by
  classical
  rcases h64 with ⟨h61, _hodd, hMH1, _hMK, hnil, hcomm, _hfrob⟩
  rcases hcomm with
    ⟨_hMKc, hH1K, _hMH1c, _hMnormK, hMnorm, hH1norm, hKnorm, _hcommEq⟩
  by_contra hle
  have hgt : H1.relIndex K > 4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1 := by
    omega
  exact hnotSM
    (theorem_6_3 K M H1 K S SM SH1 T
      h61 hMnorm hH1norm hKnorm hSM hMH1 hH1K le_rfl hnil hSH1 hcohSH1 hgt)

public theorem natCard_actor_dvd_group_card_sub_one
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [MulDistribMulAction A G]
    (hfree : ∀ a : A, a ≠ 1 → ∀ g : G, a • g = g → g = 1) :
    Nat.card A ∣ Nat.card G - 1 := by
  classical
  let α := {g : G // g ≠ 1}
  let : MulAction A α :=
    { smul := fun a x => ⟨a • (x : G), by
        intro h
        apply x.2
        have h' := congrArg (fun y : G => a⁻¹ • y) h
        simpa using h'⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change (1 : A) • (x : G) = (x : G)
        simp
      mul_smul := by
        intro a b x
        apply Subtype.ext
        change (a * b) • (x : G) = a • (b • (x : G))
        rw [mul_smul] }
  have hstab : ∀ x : α, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (x : G) = (x : G) := congrArg Subtype.val hax
    exact x.2 (hfree a ha_ne (x : G) hfix)
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardα : Nat.card α = Nat.card G - 1 := by
    let : Fintype G := Fintype.ofFinite G
    let : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {g : G // g ≠ 1} = Fintype.card G - 1
    simp
  rw [hcardα, Nat.card_prod] at hcard_equiv
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A α)), by
    rw [mul_comm]
    exact hcard_equiv⟩

public theorem frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
    {Q : Type*} [Group Q] [Finite Q]
    {K R N : Subgroup Q} [N.Normal]
    (hNK : N ≤ K)
    (hcent : ∀ r : R, r ≠ 1 → Section2.centralizerIn K (r : Q) = ⊥) :
    Nat.card R ∣ Nat.card N - 1 := by
  classical
  have : Subgroup.Normalizes R N := inferInstance
  exact natCard_actor_dvd_group_card_sub_one
    (A := R) (G := N) (by
      intro r hr x hfix
      have hconj : (r : Q) * (x : Q) * (r : Q)⁻¹ = (x : Q) := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val hfix
      have hcomm : (r : Q) * (x : Q) = (x : Q) * (r : Q) := by
        have h := congrArg (fun t : Q => t * (r : Q)) hconj
        simpa [mul_assoc] using h
      have hxcent : (x : Q) ∈ Section2.centralizerIn K (r : Q) := by
        exact ⟨hNK x.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
      have hxbot : (x : Q) ∈ (⊥ : Subgroup Q) := by
        simpa [hcent r hr] using hxcent
      exact Subtype.ext (by simpa using hxbot))

public theorem theorem_6_5_a_map_card_eq_relIndex
    {L : Type u} [Group L] [Finite L]
    {H1 N : Subgroup L} (hH1norm : H1.Normal) :
    Nat.card (N.map (QuotientGroup.mk' H1)) = H1.relIndex N := by
  classical
  let : H1.Normal := hH1norm
  rw [natCard_map_mk'_eq N H1]
  rw [← Subgroup.index_eq_card (H1.subgroupOf N)]
  rfl

public theorem theorem_6_5_a_complement_card_eq_relIndex_top
    {L : Type u} [Group L] [Finite L]
    {K H1 : Subgroup L} (hH1norm : H1.Normal) (hH1K : H1 ≤ K)
    {R : Subgroup (L ⧸ H1)}
    (hcomp : (K.map (QuotientGroup.mk' H1)).IsComplement' R) :
    Nat.card R = K.relIndex (⊤ : Subgroup L) := by
  classical
  let : H1.Normal := hH1norm
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Kbar : Subgroup (L ⧸ H1) := K.map q
  have hcardQ : Nat.card (L ⧸ H1) = H1.relIndex (⊤ : Subgroup L) := by
    rw [Subgroup.relIndex_top_right]
    rw [← Subgroup.index_eq_card H1]
  have hcardKbar : Nat.card Kbar = H1.relIndex K := by
    simpa [Kbar, q] using theorem_6_5_a_map_card_eq_relIndex (N := K) hH1norm
  have hmul_comp : Nat.card Kbar * Nat.card R = Nat.card (L ⧸ H1) := hcomp.card_mul_card
  have hrel_mul : H1.relIndex K * K.relIndex (⊤ : Subgroup L) =
      H1.relIndex (⊤ : Subgroup L) :=
    Subgroup.relIndex_mul_relIndex H1 K ⊤ hH1K le_top
  have hpos : 0 < H1.relIndex K := by
    rw [← hcardKbar]
    exact Nat.card_pos
  rw [hcardKbar, hcardQ, ← hrel_mul] at hmul_comp
  exact Nat.mul_left_cancel hpos hmul_comp

theorem theorem_6_5_a_quotient_card_eq_relIndex
    {L : Type u} [Group L] [Finite L]
    {H1 N K : Subgroup L} (hH1norm : H1.Normal)
    (hH1N : H1 ≤ N) (hNK : N ≤ K) :
    let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
    let Kbar : Subgroup (L ⧸ H1) := K.map q
    let Nbar : Subgroup (L ⧸ H1) := N.map q
    Nat.card (Kbar ⧸ Nbar.subgroupOf Kbar) = N.relIndex K := by
  classical
  let : H1.Normal := hH1norm
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Kbar : Subgroup (L ⧸ H1) := K.map q
  let Nbar : Subgroup (L ⧸ H1) := N.map q
  have hNbarKbar : Nbar ≤ Kbar := Subgroup.map_mono hNK
  have hcardKbar : Nat.card Kbar = H1.relIndex K := by
    simpa [Kbar, q] using theorem_6_5_a_map_card_eq_relIndex (N := K) hH1norm
  have hcardNbar : Nat.card Nbar = H1.relIndex N := by
    simpa [Nbar, q] using theorem_6_5_a_map_card_eq_relIndex (N := N) hH1norm
  have hcardNsub : Nat.card (Nbar.subgroupOf Kbar) = Nat.card Nbar :=
    natCard_subgroupOf_eq Nbar Kbar hNbarKbar
  have hquot_mul : Nat.card (Kbar ⧸ Nbar.subgroupOf Kbar) *
        Nat.card (Nbar.subgroupOf Kbar) = Nat.card Kbar := by
    simpa [mul_comm] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup
        (α := Kbar) (s := Nbar.subgroupOf Kbar)).symm
  have hrel_mul : H1.relIndex N * N.relIndex K = H1.relIndex K :=
    Subgroup.relIndex_mul_relIndex H1 N K hH1N hNK
  have hposRel : 0 < H1.relIndex N := by
    rw [← hcardNbar]
    exact Nat.card_pos
  rw [hcardKbar, hcardNsub, hcardNbar, ← hrel_mul] at hquot_mul
  exact Nat.mul_right_cancel hposRel
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hquot_mul)

theorem theorem_6_5_a_isSolvable_map_mk
    {L : Type u} [Group L] [Finite L]
    {H1 K : Subgroup L} (hH1norm : H1.Normal) (hsolvK : Group.IsSolvable K) :
    Group.IsSolvable (K.map (QuotientGroup.mk' H1)) := by
  classical
  let : H1.Normal := hH1norm
  let : Group.IsSolvable K := hsolvK
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Kbar : Subgroup (L ⧸ H1) := K.map q
  let φ : K →* Kbar :=
    { toFun := fun k => ⟨q (k : L), ⟨(k : L), k.property, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp [q]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp [q] }
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨k, hkK, rfl⟩
    exact ⟨⟨k, hkK⟩, rfl⟩
  exact Group.isSolvable_of_surjective hφsurj

public theorem odd_divisor_sub_one_lower_bound
    {d n : ℕ} (hdodd : Odd d) (hnodd : Odd n)
    (hngt : 1 < n) (hdvd : d ∣ n - 1) :
    2 * d + 1 ≤ n := by
  rcases hdvd with ⟨c, hc⟩
  have hn_eq : n = d * c + 1 := by
    have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    omega
  have hc_ne_zero : c ≠ 0 := by
    intro hc0
    have : n = 1 := by simpa [hc0] using hn_eq
    omega
  have hc_ne_one : c ≠ 1 := by
    intro hc1
    have hn_even : Even n := by
      rw [hn_eq, hc1]
      simpa [mul_one] using hdodd.add_one
    exact (Nat.not_odd_iff_even.mpr hn_even) hnodd
  have hcge : 2 ≤ c := by omega
  have hmul : d * 2 ≤ d * c := Nat.mul_le_mul_left d hcge
  omega

public theorem frobeniusQuotientWithKernel_intermediate_lower_bounds
    {L : Type u} [Group L] [Finite L]
    {K H1 N : Subgroup L}
    (hoddL : Odd (Nat.card L))
    (hsolvK : Group.IsSolvable K)
    (hfrob : frobeniusQuotientWithKernel K H1)
    (hNnorm : N.Normal)
    (hH1N : H1 ≤ N) (hNK : N ≤ K)
    (hH1ltN : H1 < N) (hNltK : N < K) :
    2 * K.relIndex (⊤ : Subgroup L) + 1 ≤ H1.relIndex N ∧
      2 * K.relIndex (⊤ : Subgroup L) + 1 ≤ N.relIndex K := by
  classical
  rcases hfrob with
    ⟨hH1norm, hH1K, hKnorm, R, hcomp, hKbar_ne_bot, hR_ne_bot, hcent⟩
  let : H1.Normal := hH1norm
  let : K.Normal := hKnorm
  let : N.Normal := hNnorm
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Kbar : Subgroup (L ⧸ H1) := K.map q
  let Nbar : Subgroup (L ⧸ H1) := N.map q
  have : Kbar.Normal := by
    dsimp [Kbar, q]
    infer_instance
  have : Nbar.Normal := by
    dsimp [Nbar, q]
    infer_instance
  have hNbarKbar : Nbar ≤ Kbar := Subgroup.map_mono hNK
  have hcardR : Nat.card R = K.relIndex (⊤ : Subgroup L) :=
    theorem_6_5_a_complement_card_eq_relIndex_top hH1norm hH1K hcomp
  have hcardNbar : Nat.card Nbar = H1.relIndex N := by
    simpa [Nbar, q] using theorem_6_5_a_map_card_eq_relIndex (N := N) hH1norm
  have hdivA_card : Nat.card R ∣ Nat.card Nbar - 1 :=
    frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := Kbar) (R := R) (N := Nbar) hNbarKbar
      (by simpa [Kbar, q] using hcent)
  have hdivA : K.relIndex (⊤ : Subgroup L) ∣ H1.relIndex N - 1 := by
    rw [hcardR, hcardNbar] at hdivA_card
    simpa [Subgroup.relIndex_top_right] using hdivA_card
  have hfrobKbarR : IsFrobeniusGroupWithKernelComplement Kbar R := by
    refine
      (lemma_3_1 (G := L ⧸ H1) (K := Kbar) (R := R)
        (by simpa [Kbar, q] using hKbar_ne_bot) hR_ne_bot
        (by infer_instance) (by simpa [Kbar, q] using hcomp)).2 ?_
    intro r hr
    simpa [Kbar, q, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcent r hr
  have hsolvKbar : Group.IsSolvable Kbar := by
    simpa [Kbar, q] using
      theorem_6_5_a_isSolvable_map_mk hH1norm hsolvK
  have hKbar_not_le_Nbar : ¬ Kbar ≤ Nbar := by
    intro hKbar_le_Nbar
    have hKN : K ≤ N := by
      intro k hkK
      have hkq_mem : q k ∈ Nbar := hKbar_le_Nbar ⟨k, hkK, rfl⟩
      rcases hkq_mem with ⟨n, hnN, hnq⟩
      have hnkH1 : n / k ∈ H1 := (QuotientGroup.eq_iff_div_mem).mp hnq
      have hnkN : n / k ∈ N := hH1N hnkH1
      have hkinv : (n / k)⁻¹ ∈ N := N.inv_mem hnkN
      have hk_eq : k = (n / k)⁻¹ * n := by
        simp [div_eq_mul_inv, mul_assoc]
      rw [hk_eq]
      exact N.mul_mem hkinv hnN
    exact hNltK.not_ge hKN
  let qN : (L ⧸ H1) →* (L ⧸ H1) ⧸ Nbar := QuotientGroup.mk' Nbar
  have hfrobQuot :
      IsFrobeniusGroupWithKernelComplement (Kbar.map qN) (R.map qN) :=
    lemma_3_2_b (K := Kbar) (R := R) (N := Nbar)
      hfrobKbarR hsolvKbar hKbar_not_le_Nbar
  have hcardKquot : Nat.card (Kbar.map qN) = N.relIndex K := by
    rw [natCard_map_mk'_eq Kbar Nbar]
    simpa [Kbar, Nbar, q] using
      theorem_6_5_a_quotient_card_eq_relIndex hH1norm hH1N hNK
  have hcardRmap : Nat.card (R.map qN) = Nat.card R :=
    natCard_map_mk'_eq_of_le_isComplement' Kbar R Nbar hNbarKbar
      (by simpa [Kbar, q] using hcomp)
  have hcentQuot :
      ∀ r : R.map qN, r ≠ 1 →
        Section2.centralizerIn (Kbar.map qN)
          (r : (L ⧸ H1) ⧸ Nbar) = ⊥ := by
    have hcentElem :
        ∀ r : R.map qN, r ≠ 1 →
          elementCentralizerIn (Kbar.map qN) (r : (L ⧸ H1) ⧸ Nbar) = ⊥ :=
      (lemma_3_1 (G := (L ⧸ H1) ⧸ Nbar)
        (K := Kbar.map qN) (R := R.map qN)
        hfrobQuot.kernel_ne_bot hfrobQuot.complement_ne_bot
        hfrobQuot.normal hfrobQuot.isComplement').1 hfrobQuot
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentElem r hr
  have : (Kbar.map qN).Normal := hfrobQuot.normal
  have hdivB_card : Nat.card (R.map qN) ∣ Nat.card (Kbar.map qN) - 1 :=
    frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := Kbar.map qN) (R := R.map qN) (N := Kbar.map qN) le_rfl hcentQuot
  have hdivB : K.relIndex (⊤ : Subgroup L) ∣ N.relIndex K - 1 := by
    rw [hcardRmap, hcardR, hcardKquot] at hdivB_card
    simpa [Subgroup.relIndex_top_right] using hdivB_card
  have hAgt : 1 < H1.relIndex N := by
    have hpos : 0 < H1.relIndex N := by
      rw [← hcardNbar]
      exact Nat.card_pos
    have hne : H1.relIndex N ≠ 1 := by
      intro hrel
      have hNH1 : N ≤ H1 := (Subgroup.relIndex_eq_one).1 hrel
      exact hH1ltN.not_ge hNH1
    omega
  have hBgt : 1 < N.relIndex K := by
    have hpos : 0 < N.relIndex K := by
      rw [← hcardKquot]
      exact Nat.card_pos
    have hne : N.relIndex K ≠ 1 := by
      intro hrel
      have hKN : K ≤ N := (Subgroup.relIndex_eq_one).1 hrel
      exact hNltK.not_ge hKN
    omega
  have hAodd : Odd (H1.relIndex N) :=
    hoddL.of_dvd_nat
      (dvd_trans (Subgroup.relIndex_dvd_index_of_le hH1N) (Subgroup.index_dvd_card H1))
  have hBodd : Odd (N.relIndex K) :=
    hoddL.of_dvd_nat
      (dvd_trans (Subgroup.relIndex_dvd_index_of_le hNK) (Subgroup.index_dvd_card N))
  have hDodd : Odd (K.relIndex (⊤ : Subgroup L)) :=
    hoddL.of_dvd_nat
      (dvd_trans (Subgroup.relIndex_dvd_index_of_le (le_top : K ≤ (⊤ : Subgroup L)))
        (Subgroup.index_dvd_card K))
  exact
    ⟨odd_divisor_sub_one_lower_bound hDodd hAodd hAgt hdivA,
      odd_divisor_sub_one_lower_bound hDodd hBodd hBgt hdivB⟩

theorem theorem_6_5_a_product_bound
    {a b d : ℕ} (hdpos : 0 < d)
    (ha : 2 * d + 1 ≤ a) (hb : 2 * d + 1 ≤ b) :
    4 * d ^ 2 + 1 < a * b := by
  nlinarith [Nat.mul_le_mul ha hb]

theorem theorem_6_5_a_chiefFactor
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K M H1 : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h64 : hypothesis_6_4_statement K M H1 S T)
    (hbound : H1.relIndex K ≤ 4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1) :
    chiefFactorQuotient H1 K := by
  classical
  rcases h64 with ⟨h61, hoddL, _hMH1, _hMK, _hnil, _hcomm, hfrob⟩
  have hfrobHyp := hfrob
  rcases hfrob with
    ⟨hH1norm, hH1K, hKnorm, R, hcomp, hKbar_ne_bot, hR_ne_bot, hcent⟩
  let : H1.Normal := hH1norm
  let : K.Normal := hKnorm
  change IsChiefFactor H1 K
  refine
    { normal_K := hH1norm
      normal_H := hKnorm
      lt := frobeniusQuotientWithKernel_left_lt hfrobHyp
      is_maximal := ?_ }
  intro N hNnorm hH1N hNK
  by_cases hN_eq_H1 : N = H1
  · exact Or.inl hN_eq_H1
  by_cases hN_eq_K : N = K
  · exact Or.inr hN_eq_K
  exfalso
  let : N.Normal := hNnorm
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Kbar : Subgroup (L ⧸ H1) := K.map q
  let Nbar : Subgroup (L ⧸ H1) := N.map q
  have : Kbar.Normal := by
    dsimp [Kbar, q]
    infer_instance
  have : Nbar.Normal := by
    dsimp [Nbar, q]
    infer_instance
  have hNbarKbar : Nbar ≤ Kbar := Subgroup.map_mono hNK
  have hcardR : Nat.card R = K.relIndex (⊤ : Subgroup L) :=
    theorem_6_5_a_complement_card_eq_relIndex_top hH1norm hH1K hcomp
  have hcardNbar : Nat.card Nbar = H1.relIndex N := by
    simpa [Nbar, q] using theorem_6_5_a_map_card_eq_relIndex (N := N) hH1norm
  have hdivA_card : Nat.card R ∣ Nat.card Nbar - 1 :=
    frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := Kbar) (R := R) (N := Nbar) hNbarKbar
      (by simpa [Kbar, q] using hcent)
  have hdivA : K.relIndex (⊤ : Subgroup L) ∣ H1.relIndex N - 1 := by
    rw [hcardR, hcardNbar] at hdivA_card
    simpa [Subgroup.relIndex_top_right] using hdivA_card
  have hfrobKbarR : IsFrobeniusGroupWithKernelComplement Kbar R := by
    refine
      (lemma_3_1 (G := L ⧸ H1) (K := Kbar) (R := R)
        (by simpa [Kbar, q] using hKbar_ne_bot) hR_ne_bot
        (by infer_instance) (by simpa [Kbar, q] using hcomp)).2 ?_
    intro r hr
    simpa [Kbar, q, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcent r hr
  have hsolvKbar : Group.IsSolvable Kbar := by
    simpa [Kbar, q] using
      theorem_6_5_a_isSolvable_map_mk hH1norm h61.2.2.1
  have hKbar_not_le_Nbar : ¬ Kbar ≤ Nbar := by
    intro hKbar_le_Nbar
    apply hN_eq_K
    apply le_antisymm hNK
    intro k hkK
    have hkq_mem : q k ∈ Nbar := hKbar_le_Nbar ⟨k, hkK, rfl⟩
    rcases hkq_mem with ⟨n, hnN, hnq⟩
    have hnkH1 : n / k ∈ H1 := (QuotientGroup.eq_iff_div_mem).mp hnq
    have hnkN : n / k ∈ N := hH1N hnkH1
    have hkinv : (n / k)⁻¹ ∈ N := N.inv_mem hnkN
    have hk_eq : k = (n / k)⁻¹ * n := by
      simp [div_eq_mul_inv, mul_assoc]
    rw [hk_eq]
    exact N.mul_mem hkinv hnN
  let qN : (L ⧸ H1) →* (L ⧸ H1) ⧸ Nbar := QuotientGroup.mk' Nbar
  have hfrobQuot :
      IsFrobeniusGroupWithKernelComplement (Kbar.map qN) (R.map qN) :=
    lemma_3_2_b (K := Kbar) (R := R) (N := Nbar)
      hfrobKbarR hsolvKbar hKbar_not_le_Nbar
  have hcardKquot : Nat.card (Kbar.map qN) = N.relIndex K := by
    rw [natCard_map_mk'_eq Kbar Nbar]
    simpa [Kbar, Nbar, q] using
      theorem_6_5_a_quotient_card_eq_relIndex hH1norm hH1N hNK
  have hcardRmap : Nat.card (R.map qN) = Nat.card R :=
    natCard_map_mk'_eq_of_le_isComplement' Kbar R Nbar hNbarKbar
      (by simpa [Kbar, q] using hcomp)
  have hcentQuot :
      ∀ r : R.map qN, r ≠ 1 →
        Section2.centralizerIn (Kbar.map qN)
          (r : (L ⧸ H1) ⧸ Nbar) = ⊥ := by
    have hcentElem :
        ∀ r : R.map qN, r ≠ 1 →
          elementCentralizerIn (Kbar.map qN) (r : (L ⧸ H1) ⧸ Nbar) = ⊥ :=
      (lemma_3_1 (G := (L ⧸ H1) ⧸ Nbar)
        (K := Kbar.map qN) (R := R.map qN)
        hfrobQuot.kernel_ne_bot hfrobQuot.complement_ne_bot
        hfrobQuot.normal hfrobQuot.isComplement').1 hfrobQuot
    intro r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentElem r hr
  have : (Kbar.map qN).Normal := hfrobQuot.normal
  have hdivB_card : Nat.card (R.map qN) ∣ Nat.card (Kbar.map qN) - 1 :=
    frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := Kbar.map qN) (R := R.map qN) (N := Kbar.map qN) le_rfl hcentQuot
  have hdivB : K.relIndex (⊤ : Subgroup L) ∣ N.relIndex K - 1 := by
    rw [hcardRmap, hcardR, hcardKquot] at hdivB_card
    simpa [Subgroup.relIndex_top_right] using hdivB_card
  have hH1_lt_N : H1 < N := by
    refine lt_of_le_of_ne hH1N ?_
    intro hEq
    exact hN_eq_H1 hEq.symm
  have hN_lt_K : N < K := by
    exact lt_of_le_of_ne hNK hN_eq_K
  have hAgt : 1 < H1.relIndex N := by
    have hpos : 0 < H1.relIndex N := by
      rw [← hcardNbar]
      exact Nat.card_pos
    have hne : H1.relIndex N ≠ 1 := by
      intro hrel
      have hNH1 : N ≤ H1 := (Subgroup.relIndex_eq_one).1 hrel
      exact hH1_lt_N.not_ge hNH1
    omega
  have hBgt : 1 < N.relIndex K := by
    have hpos : 0 < N.relIndex K := by
      rw [← hcardKquot]
      exact Nat.card_pos
    have hne : N.relIndex K ≠ 1 := by
      intro hrel
      have hKN : K ≤ N := (Subgroup.relIndex_eq_one).1 hrel
      exact hN_lt_K.not_ge hKN
    omega
  have hAodd : Odd (H1.relIndex N) :=
    hoddL.of_dvd_nat
      (dvd_trans (Subgroup.relIndex_dvd_index_of_le hH1N) (Subgroup.index_dvd_card H1))
  have hBodd : Odd (N.relIndex K) :=
    hoddL.of_dvd_nat
      (dvd_trans (Subgroup.relIndex_dvd_index_of_le hNK) (Subgroup.index_dvd_card N))
  have hDodd : Odd (K.relIndex (⊤ : Subgroup L)) :=
    hoddL.of_dvd_nat
      (dvd_trans (Subgroup.relIndex_dvd_index_of_le (le_top : K ≤ (⊤ : Subgroup L)))
        (Subgroup.index_dvd_card K))
  have hAlower : 2 * K.relIndex (⊤ : Subgroup L) + 1 ≤ H1.relIndex N :=
    odd_divisor_sub_one_lower_bound hDodd hAodd hAgt hdivA
  have hBlower : 2 * K.relIndex (⊤ : Subgroup L) + 1 ≤ N.relIndex K :=
    odd_divisor_sub_one_lower_bound hDodd hBodd hBgt hdivB
  have hDpos : 0 < K.relIndex (⊤ : Subgroup L) := by
    rw [← hcardR]
    exact Nat.card_pos
  have hrel_mul : H1.relIndex N * N.relIndex K = H1.relIndex K :=
    Subgroup.relIndex_mul_relIndex H1 N K hH1N hNK
  have hcontr :
      4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1 < H1.relIndex K := by
    rw [← hrel_mul]
    exact theorem_6_5_a_product_bound hDpos hAlower hBlower
  exact (not_lt_of_ge hbound) hcontr

public theorem theorem_6_5_a
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 : Subgroup L)
    (S SM : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_6_5_a_statement K M H1 S SM T := by
  classical
  intro h64 hSM hnotSM
  have h64Hyp := h64
  rcases h64 with ⟨h61, _hodd, _hMH1, _hMK, _hnil, hcomm, hfrob⟩
  have hcommHyp := hcomm
  rcases hcomm with
    ⟨_hMKc, hH1K, _hMH1c, _hMnormK, _hMnorm, hH1norm, _hKnorm, _hcommEq⟩
  let SH1 : Finset (Section1.ClassFunction L) := inducedKernelFamilyOf K H1 S
  have hSH1 : inducedKernelFamily K H1 SH1 :=
    inducedKernelFamilyOf_isFamily (hypothesis_6_1_inducedKernelFamily_bot h61) hH1K
  have hcohSH1 : coherentFamily SH1 T :=
    theorem_6_5_a_coherent_H1 h61 hH1norm hcommHyp hfrob hSH1
  have hbound : H1.relIndex K ≤ 4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1 :=
    theorem_6_5_a_index_bound h64Hyp hSM hnotSM hSH1 hcohSH1
  exact ⟨theorem_6_5_a_chiefFactor h64Hyp hbound, hbound⟩

end CFSG.Section6
