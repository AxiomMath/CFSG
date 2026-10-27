module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

set_option linter.unusedSectionVars false

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec11
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

namespace G2

theorem eq_of_isPerfect_of_isSubnormal_of_isQuasisimple {X : Type*} [Group X] [Finite X]
    {C L : Subgroup X} (hC : IsQuasisimple C) (hLC : L ≤ C) (hLp : Group.IsPerfect L)
    (hLs : (L.subgroupOf C).IsSubnormal) (hL1 : L ≠ ⊥) : L = C := by
  haveI := hLp
  have hP : Group.IsPerfect (L.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hcomp : IsComponent (⊤ : Subgroup C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hC,
      Subgroup.IsSubnormal.top⟩
  have htop : L.subgroupOf C = ⊤ := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hLs with h | h
    · exact top_le_iff.mp h
    · exfalso
      apply hL1
      have hle : (⊤ : Subgroup C) ≤ Subgroup.centralizer ((L.subgroupOf C : Subgroup C) : Set C) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hcen : L.subgroupOf C ≤ Subgroup.center C := by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro g
        exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) x hx).symm
      have hab : ∀ a b : L.subgroupOf C, a * b = b * a := fun a b =>
        Subtype.ext ((Subgroup.mem_center_iff.mp (hcen a.2)) b).symm
      have htop' : commutator (L.subgroupOf C) = ⊤ := hP.commutator_eq_top
      have hbot : commutator (L.subgroupOf C) = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        exact hab b a
      have hLbot : L.subgroupOf C = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hx⟩ : L.subgroupOf C) ∈ commutator (L.subgroupOf C) :=
          htop' ▸ Subgroup.mem_top _
        rw [hbot, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hLC hx⟩ : C) ∈ L.subgroupOf C := hx
      rw [hLbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  exact le_antisymm hLC (Subgroup.subgroupOf_eq_top.mp htop)

theorem exists_card_eq_two_pow {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card K = 2 ^ n := by
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := by
    have := ringChar.charP K
    rwa [hK2] at this
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem not_pow_nine_dvd_ordG2 {m : ℕ} (hm : 1 ≤ m) :
    ¬ (2 ^ m) ^ 9 ∣ CFSG.Open.ordG2 (2 ^ m) := by
  intro h
  unfold CFSG.Open.ordG2 at h
  have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h2m' : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have h6 : 2 ∣ (2 ^ m) ^ 6 := dvd_pow h2m (by norm_num)
  have h2 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow h2m (by norm_num)
  have h6pos : 1 ≤ (2 ^ m) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2pos : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hu : ¬ 2 ∣ (2 ^ m) ^ 6 - 1 := by omega
  have hw : ¬ 2 ∣ (2 ^ m) ^ 2 - 1 := by omega
  have hcop2 : Nat.Coprime 2 (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hu)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hw)
  have hcop : Nat.Coprime ((2 ^ m) ^ 9) (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) :=
    Nat.Coprime.pow_left 9 (Nat.Coprime.pow_left m hcop2)
  rw [mul_assoc] at h
  have h' : (2 ^ m) ^ 9 ∣ (2 ^ m) ^ 6 := hcop.dvd_of_dvd_mul_right h
  have := (Nat.pow_dvd_pow_iff_le_right h2m').mp h'
  omega

end G2

section Certificates


variable {K : Type} [Field K] [Finite K]

namespace G2

theorem centralizer_threeA (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    IsQuasisimple (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) ∧
      Nat.card K ^ 3 ∣ Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  rcases KS11Lie4Proof.three_dvd_card_sub_one_or_add_one hK3 with h31 | h31
  · obtain ⟨e⟩ := Sec4.E27.nonempty_centralizer_mulEquiv_SL3 h31 hzS hz3 hz1
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)), ?_⟩
    rw [Nat.card_congr e.toEquiv,
      LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
      show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    exact dvd_mul_right _ _
  · refine ⟨KS11Lie7Proof.isQuasisimple_centralizer_threeA h31 hK4 hzS hz3 hz1, ?_⟩
    obtain ⟨n, hn1, hn⟩ := exists_card_eq_two_pow hK2
    rw [Sec4.E27.card_centralizer_short_unitary hn1 hn h31 hzS hz3 hz1, ← hn]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem eq_one_of_mem_long_of_mem_short (hK2 : ringChar K = 2) {x : adjointGroup .G2 K}
    (hM : x ∈ KS11Lie4Proof.g2LongSL2 K) (hS : x ∈ KS11Lie4Proof.g2ShortSL2 K) : x = 1 := by
  obtain ⟨A, hA⟩ := KS11Lie4Proof.mem_g2ShortSL2_iff.mp hS
  have hM' : (x : ModGL .G2 K) ∈ rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) := hM
  have hcomm : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, A * B = B * A := fun B => by
    apply KS11Lie4Proof.rhoV_injective
    rw [map_mul, map_mul, hA]
    have hB : KS11Lie4Proof.rhoV K B ∈
        rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) := by
      rw [← KS11Lie4Proof.range_rhoV]
      exact ⟨B, rfl⟩
    exact (KS11Lie2Proof.g2_commute' hM' hB).eq
  have hcenter : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Subgroup.mem_center_iff.mpr fun B => (hcomm B).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  have hchar : CharP K 2 := by
    have := ringChar.charP K
    rwa [hK2] at this
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  apply Subtype.ext
  rw [← hA, hA1, map_one]
  rfl

end G2

theorem g2_perfect_subnormal_centralizer (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K)
    {c : adjointGroup .G2 K} (hc : orderOf c = 3)
    {L : Subgroup (adjointGroup .G2 K)}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set _))
    (hLsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set _))).IsSubnormal)
    (hLp : Group.IsPerfect L) (hcL : c ∈ L)
    (hE : ∃ B : Subgroup _, B ≤ L ∧ CFSG.Open.IsElemAbelian 3 B ∧ Nat.card B = 9) :
    IsQuasisimple L ∧ Nat.card K ^ 3 ∣ Nat.card L := by
  clear hE
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    omega
  haveI : Finite (ModGL .G2 K) := CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (adjointGroup .G2 K) := Subtype.finite
  obtain ⟨g, hg⟩ := KS11Lie4Proof.g2ThreeConjSL2_of_minus
    KS11Lie7Proof.g2ThreeConjSL2Minus_holds K hK3 hK4 c hc3 hc1
  have hc'3 : (g * c * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3, mul_one, mul_inv_cancel]
  have hc'1 : g * c * g⁻¹ ≠ 1 := fun h => hc1 (conj_eq_one_iff.mp h)
  rcases hg with hS | hM
  ·
    obtain ⟨hq', hdvd'⟩ := G2.centralizer_threeA hK2 hK4 hS hc'3 hc'1
    set e := Sec4.E27.centralizerConjEquiv g c
    have hq : IsQuasisimple (Subgroup.centralizer ({c} : Set (adjointGroup .G2 K))) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq'
    have hdvd : Nat.card K ^ 3 ∣
        Nat.card (Subgroup.centralizer ({c} : Set (adjointGroup .G2 K))) := by
      rw [Nat.card_congr e.toEquiv]
      exact hdvd'
    have hL1 : L ≠ ⊥ := fun h => hc1 (by simpa [h] using hcL)
    have hLeq := G2.eq_of_isPerfect_of_isSubnormal_of_isQuasisimple hq hLc hLp hLsn hL1
    subst hLeq
    exact ⟨hq, hdvd⟩
  ·
    exfalso
    have hcomm := (KS11Lie4Proof.g2ThreeBCent_holds K hK3 hK4 (g * c * g⁻¹) hM hc'3 hc'1).1
    have hLS : L ≤ (KS11Lie4Proof.g2ShortSL2 K).comap (MulAut.conj g).toMonoidHom := by
      refine le_of_eq_of_le (Subgroup.isPerfect_iff.mp hLp).symm
        (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
      rw [commutatorElement_def]
      change g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K
      have e1 : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
      rw [e1]
      exact hcomm _ (KS11Lie4Proof.conj_mem_centralizer (hLc hx)) _
        (KS11Lie4Proof.conj_mem_centralizer (hLc hy))
    exact hc'1 (G2.eq_one_of_mem_long_of_mem_short hK2 hM (hLS hcL))

end Certificates

section FieldAut


variable {K : Type} [Field K] [Finite K]

theorem g2_not_dvd_of_outer (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K)
    (α : MulAut (adjointGroup .G2 K)) (hα : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : _ →* MulAut (adjointGroup .G2 K)).range)
    (L : Subgroup (adjointGroup .G2 K)) (hL : ∀ l ∈ L, α l = l) :
    ¬ Nat.card K ^ 3 ∣ Nat.card L := by
  intro hdvd
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  obtain ⟨σ, hσ3, k, hαk⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hα hout
  have hfix : ∀ l ∈ L, k⁻¹ * l * k ∈ (KFacts.g2Incl σ).range := by
    intro l hl
    rw [KFacts.mem_range_g2Incl_iff hK2]
    have h1 := hL l hl
    rw [hαk] at h1
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
      MulAut.conj_apply] at h1
    have h2 := congrArg (fun x => k⁻¹ * x * k) h1
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h2
    simpa [mul_assoc] using h2
  have hLR : Nat.card L ∣ Nat.card (KFacts.g2Incl σ).range := by
    have hle : L.map (MulAut.conj k⁻¹).toMonoidHom ≤ (KFacts.g2Incl σ).range := by
      rintro _ ⟨l, hl, rfl⟩
      simpa using hfix l hl
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
      (MulAut.conj k⁻¹).injective]
    exact Subgroup.card_dvd_of_le hle
  have hR : Nat.card (KFacts.g2Incl σ).range =
      CFSG.Open.ordG2 (Nat.card (fixSubfield σ)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (KFacts.g2Incl_injective σ)).toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  have hq0 : Nat.card (fixSubfield σ) ^ 3 = Nat.card K := by
    have := KFacts.card_fixSubfield_pow σ
    rwa [hσ3] at this
  obtain ⟨f, -, hf⟩ := G2.exists_card_eq_two_pow hK2
  have hdq : Nat.card (fixSubfield σ) ∣ 2 ^ f := by
    rw [← hf, ← hq0]
    exact dvd_pow_self _ (by norm_num)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdq
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hm
    rw [hm] at hq0
    omega
  have hqK : Nat.card K ^ 3 = (2 ^ m) ^ 9 := by
    rw [← hq0, hm]
    ring
  rw [hqK] at hdvd
  refine G2.not_pow_nine_dvd_ordG2 hm1 (hdvd.trans (hLR.trans ?_))
  rw [hR, hm]

end FieldAut

end CFSG.RankThree.PartTwo.Sec19.SimsC198
