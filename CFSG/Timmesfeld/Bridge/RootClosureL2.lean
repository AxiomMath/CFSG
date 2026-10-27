module

public import CFSG.Timmesfeld.Bridge.RootClosureL2Chief
public import CFSG.Timmesfeld.Bridge.RootClosureThree

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.BenderSuzuki
open scoped commutatorElement

theorem rootThreeL2Stmt_of (h1 : PSL2SylowCoordStmt) (h2 : L2TorusIrredStmt)
    (h3 : NaturalComplementStmt) : RootThreeL2Stmt := by
  intro K _ _ D hD hDn x hx a ha b hb hab hax hconjb hconjab hgen N _ hN2 n hn he
  by_contra hNne
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconjx : IsConj a x := by
    obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one ha)
      (hD.mul_self_eq_one hx) (by rw [hax]; decide)
    exact isConj_iff.2 ⟨g, hg⟩
  have haN : a ∉ N := by
    intro haN
    have hconjN : ∀ g, IsConj a g → g ∈ N := fun g hg => by
      obtain ⟨k, rfl⟩ := isConj_iff.1 hg
      exact (inferInstance : N.Normal).conj_mem a haN k
    have htop : N = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      rintro g (rfl | rfl | rfl)
      · exact hconjN _ hconjx
      · exact haN
      · exact hconjN _ hconjb
    obtain ⟨u, w, huw⟩ := Asc72.IsBenderGroup.exists_not_commute
      (IsBenderGroup.isPSL2 n hn e : IsBenderGroup (K ⧸ N))
    apply huw
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    rw [(QuotientGroup.eq_one_iff u).2 (htop ▸ Subgroup.mem_top u)]
    exact Commute.one_left _
  have hnotN : ∀ g, IsConj a g → g ∉ N := by
    intro g hg hgN
    obtain ⟨k, rfl⟩ := isConj_iff.1 hg
    apply haN
    have h' := (inferInstance : N.Normal).conj_mem _ hgN k⁻¹
    convert h' using 1
    group
  have hax' : ¬ Commute a x := by
    intro hc
    have h' := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one ha)
      (hD.mul_self_eq_one hx)).1 hc)
    rw [hax] at h'
    exact absurd h' (by decide)
  have hTN : ∀ t ∈ rootSet D a, t ∉ N := by
    intro t ht
    have hodd : Odd (orderOf (t * x)) :=
      (odd_orderOf_mul_iff_of_mem_rootSet hD ha ht hx hax').2 (by rw [hax]; decide)
    obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one ht.1)
      (hD.mul_self_eq_one hx) hodd
    exact hnotN t (hconjx.trans (isConj_iff.2 ⟨g, hg⟩).symm)
  have : Finite (Subgroup K) := Finite.of_injective (fun M : Subgroup K => (M : Set K))
    SetLike.coe_injective
  obtain ⟨M, -, hMax⟩ := Finite.exists_le_maximal (α := Subgroup K)
    (p := fun M => M.Normal ∧ M < N) (a := ⊥) ⟨inferInstance, bot_lt_iff_ne_bot.2 hNne⟩
  have hMn : M.Normal := hMax.prop.1
  have hMN : M < N := hMax.prop.2
  have hM2 : IsPGroup 2 M := hN2.to_le hMN.le
  set ι := QuotientGroup.mk' M with hι
  set V : Subgroup (K ⧸ M) := N.map ι with hV
  have hVn : V.Normal := (inferInstance : N.Normal).map ι (QuotientGroup.mk'_surjective M)
  have hcomap : V.comap ι = N := by
    rw [hV, Subgroup.comap_map_eq, hι, QuotientGroup.ker_mk', sup_eq_left.2 hMN.le]
  have hnotM : ∀ g, g ∉ N → g ∉ M := fun g hg hgM => hg (hMN.le hgM)
  have hmemQ : ∀ g ∈ D, g ∉ N → (g : K ⧸ M) ∈ quotSetN D M := fun g hg hgN =>
    ⟨g, ⟨hg, hnotM g hgN⟩, rfl⟩
  obtain ⟨h, hh⟩ := isConj_iff.1 hconjb
  have hcomm2 : ∀ t ∈ rootSet D a, ∀ t' ∈ rootSet D a, ∀ c ∈ D, c ∈ N →
      Commute ⁅t, c⁆ t' := by
    intro t ht t' ht' c hc hcN
    have htD := ht.1
    have ht2 := hD.mul_self_eq_one htD
    have hc2 := hD.mul_self_eq_one hc
    have hsq : t * c * (t * c) ∈ N := by
      rw [show t * c * (t * c) = t * c * t⁻¹ * c by rw [hD.inv_eq htD]; group]
      exact N.mul_mem ((inferInstance : N.Normal).conj_mem c hcN t) hcN
    obtain ⟨k, hk⟩ := hN2 ⟨_, hsq⟩
    have hpow : (t * c) ^ 2 ^ (k + 1) = 1 := by
      have h' := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h'
      rw [pow_succ', pow_mul, sq]
      exact h'
    rcases hD.2.1 t htD c hc with h2 | h4 | ho
    · have htc : Commute t c := (commute_iff_mul_sq_eq_one ht2 hc2).2 (by
        rw [← h2]
        exact pow_orderOf_eq_one _)
      rw [commutatorElement_eq_one_iff_commute.2 htc]
      exact Commute.one_left _
    ·
      have hcomm_eq : ⁅t, c⁆ = (t * c) ^ 2 := by
        rw [commutatorElement_def, hD.inv_eq htD, hD.inv_eq hc, sq]
        group
      have hsqD : (t * c) ^ 2 ∈ D := hD.2.2 t htD c hc h4
      have hpow4 : (t * c) ^ 4 = 1 := by
        rw [← h4]
        exact pow_orderOf_eq_one _
      have htsq : Commute t ((t * c) ^ 2) := by
        have e4 : t * c * t * c * t * c * t * c = 1 := by
          calc t * c * t * c * t * c * t * c = (t * c) ^ 4 := by
                simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := hpow4
        have e5 : t * c * t * c * t * (c * t * c) = 1 := by
          rw [← e4]
          group
        have e6 : t * c * t * c * t = c * t * c := by
          rw [eq_inv_of_mul_eq_one_left e5, mul_inv_rev, mul_inv_rev, hD.inv_eq htD,
            hD.inv_eq hc]
          group
        show t * (t * c) ^ 2 = (t * c) ^ 2 * t
        rw [sq]
        calc t * (t * c * (t * c)) = c * t * c := by
              rw [show t * (t * c * (t * c)) = t * t * c * t * c by group, ht2, one_mul]
          _ = t * c * t * c * t := e6.symm
          _ = t * c * (t * c) * t := by group
      rw [hcomm_eq]
      exact ((ht'.2 _ hsqD).2 ((ht.2 _ hsqD).1 htsq)).symm
    · have h1' : orderOf (t * c) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho))
          (orderOf_dvd_of_pow_eq_one hpow)
      rw [orderOf_eq_one_iff] at h1'
      have htc : c = t⁻¹ := eq_inv_of_mul_eq_one_right h1'
      rw [htc, commutatorElement_eq_one_iff_commute.2 (Commute.refl t).inv_right]
      exact Commute.one_left _
  have hc : L2Chief (quotSetN D M) V (x : K ⧸ M) (a : K ⧸ M) (b : K ⧸ M) (h : K ⧸ M)
      ((fun t : K => (t : K ⧸ M)) '' rootSet D a) n := by
    have hab' : a * b ∉ N := hnotN _ hconjab
    refine
      { root := isRootInvolutionSet_quotSetN hD M
        normal := fun g f hf => conj_mem_quotSetN hDn M g hf
        x_mem := hmemQ x hx (hnotN x hconjx)
        a_mem := hmemQ a ha haN
        b_mem := hmemQ b hb.1 (hnotN b hconjb)
        ab_mem := by
          rw [← QuotientGroup.mk_mul]
          exact hmemQ _ hab hab'
        order := by
          rw [← QuotientGroup.mk_mul]
          have h' := orderOf_mk_eq_of_odd hM2 (g := a * x) (by rw [hax]; decide)
          rw [QuotientGroup.mk'_apply] at h'
          rw [h', hax]
        conj_b := (QuotientGroup.mk' M).map_isConj hconjb
        conj_ab := by
          rw [← QuotientGroup.mk_mul]
          exact (QuotientGroup.mk' M).map_isConj hconjab
        gen := ?_
        two := hN2.map ι
        ne_bot := ?_
        min := ?_
        two_le := hn
        iso := ⟨(QuotientGroup.quotientQuotientEquivQuotient M N hMN.le).trans e⟩
        sub := ?_
        a_E := ⟨a, mem_rootSet_self ha, rfl⟩
        b_E := ⟨b, hb, rfl⟩
        comm := ?_
        conj_h := by
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hh]
        h_E := ?_
        weak := ?_ }
    · have h' := congrArg (Subgroup.map ι) hgen
      rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective M)] at h'
      rw [← h']
      simp only [Set.image_insert_eq, Set.image_singleton, hι, QuotientGroup.mk'_apply]
    · intro h0
      rw [hV, Subgroup.map_eq_bot_iff, hι, QuotientGroup.ker_mk'] at h0
      exact lt_irrefl _ (lt_of_lt_of_le hMN h0)
    · intro W hWn hWV
      have hW' : (W.comap ι).Normal := hWn.comap ι
      have hMW : M ≤ W.comap ι := by
        intro m hm
        show ι m ∈ W
        rw [show ι m = 1 from (QuotientGroup.eq_one_iff m).2 hm]
        exact W.one_mem
      have hWN : W.comap ι ≤ N := by
        rw [← hcomap]
        exact Subgroup.comap_mono hWV
      by_cases hWeq : W.comap ι = N
      · right
        rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) W, hWeq]
      · left
        have hle := hMax.le_of_ge ⟨hW', lt_of_le_of_ne hWN hWeq⟩ hMW
        rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) W,
          eq_bot_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [Subgroup.mem_bot]
        exact (QuotientGroup.eq_one_iff g).2 (hle hg)
    · rintro _ ⟨t, ht, rfl⟩
      exact hmemQ t ht.1 (hTN t ht)
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
      exact (commute_of_mem_rootSet ha ht ht').map (QuotientGroup.mk' M)
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨h * t * h⁻¹, ?_, by simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
      have h' := conj_mem_rootSet_of_normal hDn h ht
      rwa [hh, rootSet_eq_of_mem hb] at h'
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ _ ⟨c, ⟨hcD, -⟩, rfl⟩ hcV
      have hcN : c ∈ N := by
        rw [← hcomap]
        exact hcV
      show Commute ⁅QuotientGroup.mk' M t, QuotientGroup.mk' M c⁆ (QuotientGroup.mk' M t')
      rw [← map_commutatorElement]
      exact (hcomm2 t ht t' ht' c hcD hcN).map (QuotientGroup.mk' M)
  exact hc.false h1 h2 h3

end CFSG.Timmesfeld.Bridge.RootClosure
