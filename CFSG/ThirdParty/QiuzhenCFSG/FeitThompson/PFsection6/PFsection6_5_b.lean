module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.BaerCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe v
universe u

@[expose] public def theorem_6_5_b_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 : Subgroup L)
    (S SM : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_6_4_statement K M H1 S T →
    inducedKernelFamily K M SM →
      ¬ coherentFamily SM T →
        ∃ p : ℕ, nonabelianPQuotient M K p

/-- Peterfalvi `(6.5)(c)`. -/


theorem card_eq_one_of_isPGroup_of_coprime
    {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) (hcop : Nat.Coprime p (Nat.card A)) :
    Nat.card A = 1 := by
  rcases hA.exists_card_eq with ⟨n, hn⟩
  cases n with
  | zero =>
      simpa [Nat.card_eq_fintype_card] using hn
  | succ n =>
      have hpdvd : p ∣ Nat.card A := by
        rw [hn]
        refine ⟨p ^ n, ?_⟩
        rw [pow_succ, mul_comm]
      have hnot : ¬ p ∣ Nat.card A :=
        (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hcop
      exact False.elim (hnot hpdvd)

theorem pPrimeCore_le_commutator_of_quotient_isPGroup
    {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQab : IsPGroup p (Q ⧸ commutator Q)) :
    pPrimeCore p Q ≤ commutator Q := by
  classical
  let D : Subgroup Q := commutator Q
  have : D.Normal := by
    dsimp [D]
    infer_instance
  let q : Q →* Q ⧸ D := QuotientGroup.mk' D
  have hmap_p : IsPGroup p ((pPrimeCore p Q).map q) := by
    exact hQab.to_subgroup ((pPrimeCore p Q).map q)
  have hmap_cop : Nat.Coprime p (Nat.card ((pPrimeCore p Q).map q)) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_map_dvd (H := pPrimeCore p Q) q)
      (pPrimeCore_coprime_card (G := Q) (p := p))
  have hmap_card_one : Nat.card ((pPrimeCore p Q).map q) = 1 :=
    card_eq_one_of_isPGroup_of_coprime hmap_p hmap_cop
  have hmap_bot : (pPrimeCore p Q).map q = ⊥ :=
    (Subgroup.card_eq_one (H := (pPrimeCore p Q).map q)).1 hmap_card_one
  have hle_ker : pPrimeCore p Q ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := pPrimeCore p Q)).1 hmap_bot
  simpa [q, D, QuotientGroup.ker_mk'] using hle_ker

theorem nilpotent_top_le_pCore_sup_pPrimeCore
    {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQnil : Group.IsNilpotent Q) :
    (⊤ : Subgroup Q) ≤ pCore p Q ⊔ pPrimeCore p Q := by
  classical
  have : Group.IsNilpotent Q := hQnil
  have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup Q)) := by
    exact Group.nilpotent_of_mulEquiv
      (G := Q) (G' := ↥(⊤ : Subgroup Q))
      (Subgroup.topEquiv.symm : Q ≃* ↥(⊤ : Subgroup Q))
  have hTop_le_iSup :
      (⊤ : Subgroup Q) ≤ ⨆ q : (Nat.card Q).primeFactors.attach, pCore q.1 Q :=
    normal_nilpotent_le_sup_pCore
      (G := Q) (N := (⊤ : Subgroup Q)) (hN := inferInstance) hnilTop
  refine hTop_le_iSup.trans ?_
  refine iSup_le ?_
  intro q
  by_cases hqp : q.1 = p
  · subst hqp
    exact le_sup_left
  · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
    let : Fact (Nat.Prime q.1) := ⟨hqprime⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := Q) (p := q.1)).exists_card_eq
    have hcop : Nat.Coprime p (Nat.card (pCore q.1 Q)) := by
      rw [hn]
      have hpq : p ≠ q.1 := by
        intro hpq'
        exact hqp hpq'.symm
      exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
    exact
      (le_sSup (show pCore q.1 Q ∈
        {K : Subgroup Q | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
          ⟨inferInstance, hcop⟩)).trans le_sup_right

set_option maxHeartbeats 160000000 in
public theorem isPGroup_of_nilpotent_quotient_commutator_isPGroup
    {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQnil : Group.IsNilpotent Q)
    (hQab : IsPGroup p (Q ⧸ commutator Q)) :
    IsPGroup p Q := by
  classical
  let C : Subgroup Q := pCore p Q
  let P' : Subgroup Q := pPrimeCore p Q
  let D : Subgroup Q := commutator Q
  have : C.Normal := by
    dsimp [C]
    infer_instance
  have hP_le_D : P' ≤ D := by
    simpa [P', D] using
      pPrimeCore_le_commutator_of_quotient_isPGroup (Q := Q) (p := p) hQab
  have htop_le : (⊤ : Subgroup Q) ≤ C ⊔ P' := by
    simpa [C, P'] using
      nilpotent_top_le_pCore_sup_pPrimeCore (Q := Q) (p := p) hQnil
  have hsup_top : C ⊔ P' = (⊤ : Subgroup Q) := top_unique htop_le
  let q : Q →* Q ⧸ C := QuotientGroup.mk' C
  have hP_map_top : P'.map q = (⊤ : Subgroup (Q ⧸ C)) := by
    have hmap_sup : (C ⊔ P').map q = C.map q ⊔ P'.map q := by
      exact Subgroup.map_sup C P' q
    have hC_map : C.map q = ⊥ := by
      exact QuotientGroup.map_mk'_self (N := C)
    have htop_map : (⊤ : Subgroup Q).map q = (⊤ : Subgroup (Q ⧸ C)) := by
      exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective C)
    have : (⊥ : Subgroup (Q ⧸ C)) ⊔ P'.map q = (⊤ : Subgroup (Q ⧸ C)) := by
      simpa [hmap_sup, hC_map, htop_map] using
        congrArg (fun H : Subgroup Q => H.map q) hsup_top
    simpa using this
  have hD_map_top : D.map q = (⊤ : Subgroup (Q ⧸ C)) := by
    have hle : P'.map q ≤ D.map q := Subgroup.map_mono (f := q) hP_le_D
    exact top_unique (by simpa [hP_map_top] using hle)
  have hD_map_comm : D.map q = commutator (Q ⧸ C) := by
    dsimp [D]
    rw [show commutator Q = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ from rfl]
    rw [Subgroup.map_commutator]
    have hqtop : (⊤ : Subgroup Q).map q = (⊤ : Subgroup (Q ⧸ C)) := by
      exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective C)
    rw [hqtop]
    rfl
  have hcomm_top : commutator (Q ⧸ C) = (⊤ : Subgroup (Q ⧸ C)) := by
    simpa [hD_map_comm] using hD_map_top
  have hquot_top_bot : (⊤ : Subgroup (Q ⧸ C)) = ⊥ := by
    by_contra hne
    have : Group.IsNilpotent Q := hQnil
    have : Group.IsSolvable (Q ⧸ C) := by infer_instance
    have hlt :
        ⁅(⊤ : Subgroup (Q ⧸ C)), (⊤ : Subgroup (Q ⧸ C))⁆ <
          (⊤ : Subgroup (Q ⧸ C)) :=
      Group.IsSolvable.commutator_lt_of_ne_bot (G := Q ⧸ C) hne
    exact (ne_of_lt hlt) (by simpa [hcomm_top])
  have hC_top : C = (⊤ : Subgroup Q) := by
    apply top_unique
    intro x _hx
    have hxbot : q x ∈ (⊥ : Subgroup (Q ⧸ C)) := by
      simp [← hquot_top_bot]
    have hxq : q x = 1 := by simpa using hxbot
    exact (QuotientGroup.eq_one_iff (N := C) (x := x)).1 hxq
  have hC_p : IsPGroup p C := by
    simpa [C] using (pCore_isPGroup (G := Q) (p := p))
  exact hC_p.of_equiv
    ((MulEquiv.subgroupCongr hC_top).trans (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q))

theorem theorem_6_5_b_chief_quotient_isPGroup
    {L : Type u} [Group L] [Finite L]
    {K H1 : Subgroup L} [H1.Normal] [K.Normal]
    (hKsolv : Group.IsSolvable K)
    (hchief : IsChiefFactor H1 K) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p (K ⧸ H1.subgroupOf K) := by
  classical
  let cf : ChiefFactor L := { V := H1, U := K, isChief := hchief }
  let π : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Uq : Subgroup (L ⧸ H1) := K.map π
  have : Uq.Normal := by
    dsimp [Uq, π]
    infer_instance
  have : IsMinimalNormal Uq := by
    simpa [cf, π, Uq] using chiefFactor_quotient_isMinimalNormal (G := L) cf
  have : Group.IsSolvable Uq := by
    let φ : K →* L ⧸ H1 := π.comp K.subtype
    have hφrange : φ.range = Uq := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact ⟨y, y.property, rfl⟩
      · rintro ⟨y, hyK, rfl⟩
        exact ⟨⟨y, hyK⟩, rfl⟩
    have : Group.IsSolvable K := hKsolv
    have : Group.IsSolvable φ.range :=
      Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    exact hφrange ▸ inferInstance
  rcases minimalNormal_solvable_exists_isElementaryAbelian (G := L ⧸ H1) Uq with
    ⟨p, hp, hpElem⟩
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p Uq := hpElem
  have hUq_p : IsPGroup p Uq := IsElementaryAbelian.isPGroup p Uq
  refine ⟨p, hp, ?_⟩
  exact hUq_p.of_equiv (quotientSubgroupRangeEquiv K H1).symm

theorem theorem_6_5_b_quotient_commutator_isPGroup
    {L : Type u} [Group L] [Finite L]
    {K M H1 : Subgroup L}
    {p : ℕ} [Fact p.Prime]
    (hMH1 : M ≤ H1)
    (hMnormK : (M.subgroupOf K).Normal)
    (hH1normK : (H1.subgroupOf K).Normal)
    (hcommEq : (H1.subgroupOf K).map (QuotientGroup.mk' (M.subgroupOf K)) =
          commutator (K ⧸ M.subgroupOf K))
    (hKH1p : IsPGroup p (K ⧸ H1.subgroupOf K)) :
    IsPGroup p ((K ⧸ M.subgroupOf K) ⧸ commutator (K ⧸ M.subgroupOf K)) := by
  classical
  let Msub : Subgroup K := M.subgroupOf K
  let Hsub : Subgroup K := H1.subgroupOf K
  have : Msub.Normal := hMnormK
  have : Hsub.Normal := hH1normK
  have hMsubHsub : Msub ≤ Hsub := by
    intro x hx
    exact hMH1 hx
  let Q : Type u := K ⧸ Msub
  let Hbar : Subgroup Q := Hsub.map (QuotientGroup.mk' Msub)
  have : Hbar.Normal := by
    dsimp [Hbar]
    infer_instance
  let e₁ : Q ⧸ commutator Q ≃* Q ⧸ Hbar :=
    QuotientGroup.quotientMulEquivOfEq (by
      dsimp [Hbar, Q, Msub, Hsub]
      exact hcommEq.symm)
  let e₂ : Q ⧸ Hbar ≃* K ⧸ Hsub :=
    QuotientGroup.quotientQuotientEquivQuotient Msub Hsub hMsubHsub
  exact hKH1p.of_equiv (e₁.trans e₂).symm

theorem theorem_6_5_b_quotient_noncomm
    {L : Type u} [Group L] [Finite L]
    {K M H1 : Subgroup L}
    (hMH1 : M ≤ H1) (hH1K : H1 ≤ K)
    (hMnormK : (M.subgroupOf K).Normal)
    (hcommEq : (H1.subgroupOf K).map (QuotientGroup.mk' (M.subgroupOf K)) =
          commutator (K ⧸ M.subgroupOf K))
    (hMneH1 : M ≠ H1) :
    ¬ IsMulCommutative (K ⧸ M.subgroupOf K) := by
  classical
  intro hQcomm
  let q : K →* K ⧸ M.subgroupOf K := QuotientGroup.mk' (M.subgroupOf K)
  have hcomm_bot : commutator (K ⧸ M.subgroupOf K) = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top]
    rw [eq_top_iff]
    intro x _hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact hQcomm.is_comm.comm y x
  have hH1map_bot : (H1.subgroupOf K).map q = ⊥ := by
    simpa [q, hcomm_bot] using hcommEq
  have hH1sub_le_ker : H1.subgroupOf K ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := H1.subgroupOf K)).1 hH1map_bot
  have hH1sub_le_Msub : H1.subgroupOf K ≤ M.subgroupOf K := by
    change H1.subgroupOf K ≤ (QuotientGroup.mk' (M.subgroupOf K)).ker at hH1sub_le_ker
    simpa [QuotientGroup.ker_mk'] using hH1sub_le_ker
  have hH1_le_M : H1 ≤ M := by
    intro x hxH1
    have hxK : x ∈ K := hH1K hxH1
    exact hH1sub_le_Msub (show (⟨x, hxK⟩ : K) ∈ H1.subgroupOf K from hxH1)
  exact hMneH1 (le_antisymm hMH1 hH1_le_M)

public theorem theorem_6_5_b
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 : Subgroup L)
    (S SM : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_6_5_b_statement K M H1 S SM T := by
  classical
  intro h64 hSM hnotSM
  rcases h64 with ⟨h61, _hoddL, hMH1, _hMK, hnil, hcomm, hfrob⟩
  have h64' : hypothesis_6_4_statement K M H1 S T :=
    ⟨h61, _hoddL, hMH1, _hMK, hnil, hcomm, hfrob⟩
  have hcommHyp : commutatorQuotientHypothesis M H1 K := hcomm
  rcases hcomm with
    ⟨hMKc, hH1K, hMH1c, hMnormK, hMnorm, hH1norm, hKnorm, hcommEq⟩
  rcases hnil with ⟨_hMKn, _hMnormKn, _hMnormn, _hKnormn, hQnil⟩
  rcases theorem_6_5_a K M H1 S SM T h64' hSM hnotSM with ⟨hchief, _hbound⟩
  have hMneH1 : M ≠ H1 := by
    intro hMeqH1
    have hSH1 : inducedKernelFamily K H1 SM := by
      simpa [hMeqH1] using hSM
    exact hnotSM
      (theorem_6_5_a_coherent_H1 h61 hH1norm hcommHyp hfrob hSH1)
  have hnoncomm : ¬ IsMulCommutative (K ⧸ M.subgroupOf K) :=
    theorem_6_5_b_quotient_noncomm hMH1c hH1K hMnormK hcommEq hMneH1
  have : H1.Normal := hH1norm
  have : K.Normal := hKnorm
  have hH1normK : (H1.subgroupOf K).Normal := hH1norm.subgroupOf K
  rcases theorem_6_5_b_chief_quotient_isPGroup
      (L := L) (K := K) (H1 := H1) h61.2.2.1 hchief with
    ⟨p, hp, hKH1p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hQabp : IsPGroup p
      ((K ⧸ M.subgroupOf K) ⧸ commutator (K ⧸ M.subgroupOf K)) :=
    theorem_6_5_b_quotient_commutator_isPGroup
      (K := K) (M := M) (H1 := H1) hMH1c hMnormK hH1normK hcommEq hKH1p
  have hQp : IsPGroup p (K ⧸ M.subgroupOf K) :=
    isPGroup_of_nilpotent_quotient_commutator_isPGroup hQnil hQabp
  exact ⟨p, hMKc, hMnormK, hMnorm, hKnorm, hp, hQp, hnoncomm⟩

end CFSG.Section6
