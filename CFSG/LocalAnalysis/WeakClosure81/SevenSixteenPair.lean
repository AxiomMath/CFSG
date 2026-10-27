module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenSetup
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenARank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup CFSG.ASVolI.ChIJK
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G} {A : Subgroup G}

structure PairHyp (V A : Subgroup G) : Prop where
  elemAbelian_left : IsElemAbelian 2 V
  elemAbelian_right : IsElemAbelian 2 A
  pRank_eq : CFSG.pRank 2 ↥V = CFSG.pRank 2 ↥A
  ti_left : CFSG.ASVolI.ChIJK.IsTISubgroup V
  ti_right : CFSG.ASVolI.ChIJK.IsTISubgroup A
  ne : V ≠ A
  cross : ∀ g : G, CFSG.conjugate A g ≠ V → CFSG.conjugate A g ⊓ V = ⊥
  nIn_ne_bot : NIn V A ≠ ⊥
  nIn_lt : NIn V A < V


theorem s716P_card_eq_two_pow_pRank {W : Subgroup G} (hW : IsElemAbelian 2 W) :
    Nat.card ↥W = 2 ^ CFSG.pRank 2 ↥W := by
  haveI : CFSG.IsElementaryAbelian 2 W := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hW
  obtain ⟨m, hm⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two hm]
  exact hm

theorem pairHyp_conj (h : Hyp716 V H E) {a : G} (ha : a ∈ kSub V H E)
    (hne : ⁅V, conjSubgroup V a⁆ ≠ ⊥) :
    PairHyp V (conjSubgroup V a) ∧ PairHyp (conjSubgroup V a) V := by
  have hA : IsElemAbelian 2 (conjSubgroup V a) := isElemAbelian_conjSubgroup' h.elemAbelian a
  have hTIV : CFSG.ASVolI.ChIJK.IsTISubgroup V := isTISubgroup_of_isTI h.ti
  have hTIA : CFSG.ASVolI.ChIJK.IsTISubgroup (conjSubgroup V a) :=
    isTISubgroup_of_isTI (isTI_conj h.ti a)
  have hrank : CFSG.pRank 2 ↥V = CFSG.pRank 2 ↥(conjSubgroup V a) := by
    apply Nat.pow_right_injective (by norm_num : 1 < 2)
    change 2 ^ CFSG.pRank 2 ↥V = 2 ^ CFSG.pRank 2 ↥(conjSubgroup V a)
    rw [← s716P_card_eq_two_pow_pRank h.elemAbelian, ← s716P_card_eq_two_pow_pRank hA]
    exact (card_conjSubgroup' a V).symm
  have hne' : V ≠ conjSubgroup V a := by
    intro heq
    apply hne
    rw [← heq]
    exact Subgroup.commutator_self_eq_bot_iff.mpr h.elemAbelian.1
  have hAΩ : conjSubgroup V a ∈ omegaSet V H E := conjSubgroup_mem_omegaSet_of_mem_kSub h ha
  have hcross : ∀ g : G, CFSG.conjugate (conjSubgroup V a) g ≠ V →
      CFSG.conjugate (conjSubgroup V a) g ⊓ V = ⊥ := by
    intro g hg
    have hconj : CFSG.conjugate (conjSubgroup V a) g = conjSubgroup V (a * g) := by
      change conjSubgroup (conjSubgroup V a) g = conjSubgroup V (a * g)
      rw [Quasithin.conjSubgroup_conjSubgroup]
    rw [hconj, inf_comm]
    rcases inf_conjSubgroup_eq_bot_or_eq h.ti 1 (a * g) with hbot | heq
    · rw [Quasithin.conjSubgroup_one] at hbot
      exact hbot
    · rw [Quasithin.conjSubgroup_one] at heq
      exact (hg (hconj.trans heq.symm)).elim
  have hNIn : NIn V (conjSubgroup V a) ≠ ⊥ := by
    obtain ⟨a', b', hVa, hVb, hNab⟩ :=
      nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian h.mem hAΩ
    show V ⊓ Subgroup.normalizer (conjSubgroup V a : Set G) ≠ ⊥
    have hEq : V ⊓ Subgroup.normalizer (conjSubgroup V a : Set G) =
        conjSubgroup V a' ⊓ Subgroup.normalizer (conjSubgroup V b' : Set G) := by
      rw [hVb]
      nth_rewrite 1 [hVa]
      rfl
    rw [hEq]
    exact hNab
  have hnotle := not_le_normalizer_conjSubgroup_of_commutator_ne_bot h.elemAbelian h.ti hne
  have hNIn_lt : NIn V (conjSubgroup V a) < V := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    apply hnotle
    have hle : NIn V (conjSubgroup V a) ≤ Subgroup.normalizer (conjSubgroup V a : Set G) :=
      inf_le_right
    rwa [hEq] at hle
  refine ⟨⟨h.elemAbelian, hA, hrank, hTIV, hTIA, hne', hcross, hNIn, hNIn_lt⟩, ?_⟩
  have hcross' : ∀ g : G, CFSG.conjugate V g ≠ conjSubgroup V a →
      CFSG.conjugate V g ⊓ conjSubgroup V a = ⊥ := by
    intro g hg
    have hconj : CFSG.conjugate V g = conjSubgroup V g := rfl
    rw [hconj]
    rcases inf_conjSubgroup_eq_bot_or_eq h.ti g a with hbot | heq
    · exact hbot
    · exact (hg (hconj.trans heq)).elim
  have hNIn' : NIn (conjSubgroup V a) V ≠ ⊥ := by
    obtain ⟨a', b', hVa, hVb, hNab⟩ :=
      nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian hAΩ h.mem
    show conjSubgroup V a ⊓ Subgroup.normalizer (V : Set G) ≠ ⊥
    have hEq : conjSubgroup V a ⊓ Subgroup.normalizer (V : Set G) =
        conjSubgroup V a' ⊓ Subgroup.normalizer (conjSubgroup V b' : Set G) := by
      rw [← hVa, ← hVb]
    rw [hEq]
    exact hNab
  have hne2 : ⁅conjSubgroup V a, conjSubgroup (conjSubgroup V a) a⁻¹⁆ ≠ ⊥ := by
    rw [Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel, Quasithin.conjSubgroup_one,
      Subgroup.commutator_comm]
    exact hne
  have hnotle' :=
    not_le_normalizer_conjSubgroup_of_commutator_ne_bot hA (isTI_conj h.ti a) hne2
  rw [Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel, Quasithin.conjSubgroup_one]
    at hnotle'
  have hNIn_lt' : NIn (conjSubgroup V a) V < conjSubgroup V a := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    apply hnotle'
    have hle : NIn (conjSubgroup V a) V ≤ Subgroup.normalizer (V : Set G) := inf_le_right
    rwa [hEq] at hle
  exact ⟨hA, h.elemAbelian, hrank.symm, hTIA, hTIV, hne'.symm, hcross', hNIn', hNIn_lt'⟩

theorem pairHyp_part_a (hP : PairHyp V A) :
    IsDirectProductOf (NIn V A) (NIn A V) (pairY V A) ∧
      CFSG.ASVolI.ChIJK.IsNormalIn (pairY V A) (V ⊔ A) ∧
      ∀ v ∈ V, v ∉ NIn V A →
        NIn V A = pairY V A ⊓ Subgroup.centralizer ({v} : Set G) ∧
          NIn V A = ⁅pairY V A, Subgroup.zpowers v⁆ :=
  ((CFSG.ASVolI.as_I_6_2 (G := G) V A hP.elemAbelian_left hP.elemAbelian_right hP.pRank_eq
    hP.ti_left hP.ti_right hP.ne hP.cross hP.nIn_ne_bot).2 hP.nIn_lt).1

theorem pairY_normal (hP : PairHyp V A) : ((pairY V A).subgroupOf (V ⊔ A)).Normal :=
  (pairHyp_part_a hP).2.1.2

theorem pairHyp_quotient (hP : PairHyp V A) [((pairY V A).subgroupOf (V ⊔ A)).Normal] :
    QuotientIsDihedralL2OrSz (V ⊔ A) (pairY V A) :=
  (((CFSG.ASVolI.as_I_6_2 (G := G) V A hP.elemAbelian_left hP.elemAbelian_right hP.pRank_eq
    hP.ti_left hP.ti_right hP.ne hP.cross hP.nIn_ne_bot).2 hP.nIn_lt).2).1.1

theorem pairHyp_chief_natural (hP : PairHyp V A)
    [((pairY V A).subgroupOf (V ⊔ A)).Normal] :
    ∀ P Q : Subgroup G, IsChiefSection (V ⊔ A) (pairY V A) P Q →
      IsNaturalSection (V ⊔ A) (pairY V A) P Q :=
  (((CFSG.ASVolI.as_I_6_2 (G := G) V A hP.elemAbelian_left hP.elemAbelian_right hP.pRank_eq
    hP.ti_left hP.ti_right hP.ne hP.cross hP.nIn_ne_bot).2 hP.nIn_lt).2).2.1

theorem nIn_le_normalizer_nIn (hP : PairHyp V A) :
    NIn V A ≤ Subgroup.normalizer (NIn A V : Set G) := by
  obtain ⟨hcomm, -, -⟩ := (pairHyp_part_a hP).1
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcomm x hx y hy).symm

theorem pairY_isPGroup (hP : PairHyp V A) : IsPGroup 2 ↥(pairY V A) :=
  IsPGroup.to_sup_of_normal_right'
    ((isPGroup_two_of_isElemAbelian hP.elemAbelian_left).to_le inf_le_left)
    ((isPGroup_two_of_isElemAbelian hP.elemAbelian_right).to_le inf_le_left)
    (nIn_le_normalizer_nIn hP)

theorem card_pairY (hP : PairHyp V A) :
    Nat.card ↥(pairY V A) = Nat.card ↥(NIn V A) * Nat.card ↥(NIn A V) := by
  obtain ⟨hcomm, hinf, -⟩ := (pairHyp_part_a hP).1
  let f : ↥(NIn V A) →* G := (NIn V A).subtype
  let g : ↥(NIn A V) →* G := (NIn A V).subtype
  have hfg : ∀ (m : ↥(NIn V A)) (n : ↥(NIn A V)), Commute (f m) (g n) :=
    fun m n => hcomm m m.2 n n.2
  have hinj : Function.Injective (f.noncommCoprod g hfg) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    simp only [f, g, Subgroup.range_subtype]
    exact disjoint_iff.mpr hinf
  have hrange : (f.noncommCoprod g hfg).range = pairY V A := by
    rw [MonoidHom.noncommCoprod_range]
    simp only [f, g, Subgroup.range_subtype]
    rfl
  have h1 : Nat.card (↥(NIn V A) × ↥(NIn A V)) = Nat.card ↥(f.noncommCoprod g hfg).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [Nat.card_prod] at h1
  rw [← hrange]
  exact h1.symm

theorem pair_nIn_le (hP : PairHyp A V) {W : Subgroup G} (hVW : NIn V A ≤ W)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) : NIn A V ≤ W := by
  obtain ⟨hdp, -, hv⟩ := pairHyp_part_a hP
  obtain ⟨hcomm, -, -⟩ := hdp
  obtain ⟨v, hvA, hvN⟩ := SetLike.exists_of_lt hP.nIn_lt
  rw [(hv v hvA hvN).2, Subgroup.commutator_le]
  intro y hy u hu
  have hy' : y ∈ ((NIn A V ⊔ NIn V A : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (nIn_le_normalizer_nIn hP)] at hy'
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := Set.mem_mul.mp hy'
  have huA : u ∈ A := Subgroup.zpowers_le.mpr hvA hu
  haveI := hP.elemAbelian_left.1
  have hn₁A : n₁ ∈ A := (inf_le_left : NIn A V ≤ A) hn₁
  have h1 : n₁ * u = u * n₁ := setLike_mul_comm hn₁A huA
  have h2 : n₁ * n₂ = n₂ * n₁ := hcomm n₁ hn₁ n₂ hn₂
  have hc : Commute n₁ (n₂ * u * n₂⁻¹) :=
    (Commute.mul_right h2 h1).mul_right (Commute.inv_right h2)
  have hcomm_eq : ⁅n₁ * n₂, u⁆ = n₂ * (u * n₂⁻¹ * u⁻¹) := by
    have hc' := hc.eq
    simp only [commutatorElement_def, mul_inv_rev]
    calc n₁ * n₂ * u * (n₂⁻¹ * n₁⁻¹) * u⁻¹
        = (n₁ * (n₂ * u * n₂⁻¹)) * n₁⁻¹ * u⁻¹ := by group
      _ = ((n₂ * u * n₂⁻¹) * n₁) * n₁⁻¹ * u⁻¹ := by rw [hc']
      _ = n₂ * (u * n₂⁻¹ * u⁻¹) := by group
  rw [hcomm_eq]
  have hn₂W : n₂ ∈ W := hVW hn₂
  have hu' : u ∈ Subgroup.normalizer (W : Set G) := hAW huA
  exact mul_mem hn₂W ((Subgroup.mem_normalizer_iff.mp hu' _).mp (inv_mem hn₂W))

end CFSG.LocalAnalysis.WeakClosure81
