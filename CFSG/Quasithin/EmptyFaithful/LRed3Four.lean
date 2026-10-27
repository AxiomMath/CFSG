module

public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.EmptyFaithful.LRed3FourB
public import CFSG.Quasithin.Background.F918C12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
  CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

@[expose] def FactG2Cayley : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    IsG2 2 n (↥(CFSG.Open.quasithinG2 K) ⧸ Subgroup.center ↥(CFSG.Open.quasithinG2 K))

private theorem lred3_one_le_of_card' {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  by_contra h
  have h0 : n = 0 := by omega
  have := Finite.one_lt_card (α := K)
  rw [hK, h0] at this
  norm_num at this

section Types

variable {Y : Type} [Group Y]

theorem lred3_false_of_su3_one (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (π : ↥(StatedSU 3 (2 ^ 1) K) →* Y)
    (hπ : Function.Surjective π) : False := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, hK.trans (by norm_num)⟩
  have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have := Fintype.ofFinite ↥(StatedSU 3 (2 ^ 1) K)
  have hsolv : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) K) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  have hsolvY : Group.IsSolvable Y := Group.isSolvable_of_surjective (f := π) hπ
  have : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have : Group.IsPerfect Y := hY.1
  exact Group.IsPerfect.not_isSolvable Y hsolvY

theorem lred3_four_of_b42Types
    (hG2 : FactG2Cayley) (hY : CFSG.IsQuasisimple Y)
    (h : B42Types Y) : FourList (Y ⧸ Subgroup.center Y) := by
  rcases h with ⟨K, _, _, n, hn, hK, ⟨e⟩⟩ | ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, n, hn, hK, ⟨e⟩⟩ |
    ⟨K, _, _, n, hn, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, N, hN, ⟨e⟩⟩ | ⟨m, hm, hAlt⟩ | hhat |
    ⟨K, _, _, n, hK, hn, ⟨e⟩⟩
  · exact lred3_four_of_sl2 hY hn hK e.symm.toMonoidHom e.symm.surjective
  · exact lred3_four_of_sl3 hY hn hK e.symm.toMonoidHom e.symm.surjective
  · exact lred3_four_of_sp4 hY hn hK e.symm.toMonoidHom e.symm.surjective
  ·
    have eq := QuotientGroup.congr (Subgroup.center Y)
      (Subgroup.center ↥(CFSG.Open.quasithinG2 K)) e (Subgroup.map_center_eq e)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, hn, IsG2.of_mulEquiv eq.symm (hG2 K n hn hK)⟩))))
  ·
    have hs : IsSimpleGroup ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK
    have hD : (commutator ↥(CFSG.Open.quasithinG2 K)).map (CFSG.Open.quasithinG2 K).subtype =
        ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    let eD : ↥(commutator ↥(CFSG.Open.quasithinG2 K)) ≃*
        ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      ((commutator ↥(CFSG.Open.quasithinG2 K)).equivMapOfInjective
        (CFSG.Open.quasithinG2 K).subtype (CFSG.Open.quasithinG2 K).subtype_injective).trans
        (MulEquiv.subgroupCongr hD)
    have hDs : IsSimpleGroup ↥(commutator ↥(CFSG.Open.quasithinG2 K)) := eD.isSimpleGroup
    have hYp : Group.IsPerfect Y := hY.1
    have : Group.IsPerfect ↥N := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hY1 : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY
    have hN0 : N ≠ ⊥ := by
      rintro rfl
      obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      apply hy
      have h1 : ((e y : ↥(⊥ : Subgroup ↥(CFSG.Open.quasithinG2 K))) :
          ↥(CFSG.Open.quasithinG2 K)) = 1 := Subgroup.mem_bot.1 (e y).2
      exact e.injective (Subtype.ext (by rw [h1]; simp))
    have heq : N = commutator ↥(CFSG.Open.quasithinG2 K) := eq_commutator_of_isPerfect N hN0 hDs
    let e' : Y ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      (e.trans (MulEquiv.subgroupCongr heq)).trans eD
    exact lred3_four_of_g2derived hY hK e'.symm.toMonoidHom e'.symm.surjective
  ·
    obtain ⟨e⟩ := hAlt
    exact lred3_four_of_alt hY hm e.symm.toMonoidHom e.symm.surjective
  ·
    obtain ⟨f⟩ := hhat.2.2
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f⟩)))
  · rcases hn with rfl | rfl
    · exact lred3_four_of_sl4 hY hK e.symm.toMonoidHom e.symm.surjective
    · exact lred3_four_of_sl5 hY hK e.symm.toMonoidHom e.symm.surjective

end Types

section Table

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem lred3_four_of_table
    (hq : CFSG.IsQuasisimple ↥L) (ht : AsB45Table G L)
    (hqq : qOf G ≤ ((2 : ℚ) : WithTop ℚ)) : FourList (↥L ⧸ Subgroup.center ↥L) := by
  rcases ht with ⟨⟨π, hR⟩, -⟩ | ⟨m, hm, horth, -⟩ | ⟨m, ⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨f, hsz, -⟩ | ⟨m, hm, ⟨K, _, _, _, hK, π, hR⟩, -⟩ | ⟨⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨⟨eY, heY, hw, π, hR⟩, hq2⟩ | ⟨⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩, -⟩ |
      ⟨⟨x, y, hxy, π, hR⟩, hq2⟩ | ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨h2324, hq2⟩
  ·
    exact lred3_four_of_alt hq (m := 7) (by omega) π hR.1
  ·
    obtain ⟨K, _, _, _, hK, π, hR⟩ := horth
    exact lred3_four_of_sl2 hq (n := 2 * m) (by omega) hK π hR.1
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hm1 : 1 ≤ m := by
        by_contra h
        have h0 : m = 0 := by omega
        have := Finite.one_lt_card (α := K)
        rw [hK, h0] at this
        norm_num at this
      have : m = 1 := by omega
      subst this
      exact (lred3_false_of_su3_one hq hK π hR.1).elim
    · exact lred3_four_of_su3 hq hm hK π hR.1
  ·
    obtain ⟨a, K, _, _, ha, hf, hK, ⟨e⟩⟩ := hsz.exists_equiv
    subst hf
    exact lred3_four_of_sz hq ha hK e.toMonoidHom e.surjective
  ·
    exact lred3_four_of_sl3 hq (n := 2 * m) (by omega) hK π hR.1
  ·
    exact lred3_four_of_g2derived hq (by rw [hK]; norm_num) π hR.1
  · exact absurd hq2 (not_lt.2 hqq)
  ·
    exact lred3_four_of_hatM22 hq hhat π hR.1
  · exact absurd hq2 (not_lt.2 hqq)
  ·
    exact lred3_four_of_m22 hq hxy π hR.1
  · exact absurd hq2 (not_lt.2 hqq)

end Table

section Second

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U C : Subgroup W}

theorem lred3_four_of_first (hq : CFSG.IsQuasisimple ↥L)
    (h : (∃ n, BinaryNaturalSL L U C 3 n) ∨ (∃ n, BinaryNaturalSp4 L U C n) ∨
      AlternatingNatural L U C 6 ∨ BinaryNaturalSL L U C 4 1 ∨ BinaryNaturalSL L U C 5 1 ∨
      A7Four L U C) : FourList (↥L ⧸ Subgroup.center ↥L) := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨π, hπ⟩ | h4 | h5 | ⟨α, π, hπ⟩
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := hn
    exact lred3_four_of_sl3 hq (lred3_one_le_of_card' hKc) hKc π hπ.1
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := hn
    by_cases h2 : 2 ≤ n
    · exact lred3_four_of_sp4 hq h2 hKc π hπ.1
    · exfalso
      have hn1 : n = 1 := by have := lred3_one_le_of_card' hKc; omega
      subst hn1
      have hinj : Function.Injective π :=
        realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
      let eπ : ↥(StatedSp 2 K) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
      have hK2 : Nat.card K = 2 := by simpa using hKc
      have : Fintype K := Fintype.ofFinite K
      have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
      let c : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hF
      have hLp : Group.IsPerfect ↥L := hq.1
      have hperf : Group.IsPerfect (Equiv.Perm (Fin 6)) :=
        Group.IsPerfect.ofSurjective (f := (((B5FinSp.theta c).trans eπ).symm).toMonoidHom)
          ((B5FinSp.theta c).trans eπ).symm.surjective
      exact B5.not_isPerfect_perm 6 (by norm_num) hperf
  · exact lred3_four_of_alt hq (m := 6) (by omega) π hπ.1
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := h4
    exact lred3_four_of_sl4 hq (by simpa using hKc) π hπ.1
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := h5
    exact lred3_four_of_sl5 hq (by simpa using hKc) π hπ.1
  · exact lred3_four_of_alt hq (m := 7) (by omega) π hπ.1

end Second

section Stab

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
theorem lred3_cq_autSec {L : Subgroup (MulAut W)} {V : Subgroup W} {C : Subgroup ↥V}
    (hLs : L ≤ stabSub V) (hq : CFSG.IsQuasisimple ↥L) (hne : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v)
    (hKC : autSub L V ≤ stabSub C) (hf : autSub L V ⊓ centSec ⊤ C = ⊥) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
      ↥(autSec (autSub L V) ⊤ C) ⧸ Subgroup.center ↥(autSec (autSub L V) ⊤ C)) := by
  have hKq := lred3_isQuasisimple_autSub hLs hq hne
  let eK : ↥(resHomOn V hLs).range ≃* ↥(autSub L V) :=
    MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs).symm
  let ρ : ↥L →* ↥(autSub L V) := eK.toMonoidHom.comp (resHomOn V hLs).rangeRestrict
  have hρ : Function.Surjective ρ :=
    eK.surjective.comp (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨e1⟩ := lred3_cq_of_quasisimple hq hKq ρ hρ
  let e2 : ↥(autSub L V) ≃* ↥(autSec (autSub L V) ⊤ C) :=
    B5.secEquiv (autSub L V) (InternalSec.le_stabSub_top _) hKC hf
  exact ⟨e1.trans (QuotientGroup.congr (Subgroup.center ↥(autSub L V))
    (Subgroup.center ↥(autSec (autSub L V) ⊤ C)) e2 (Subgroup.map_center_eq e2))⟩

theorem lred3_four_of_stab
    (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42)
    (h45 : AsB45) (hD : D3Std M Mp T L V) (hMp : Mp = L) (hT : T ≤ stabSub V)
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    FourList (↥L ⧸ Subgroup.center ↥L) := by
  subst hMp
  have hLs : Mp ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQ := lred3_qsec hD.hyp rfl hO2
  have hb4 := lred3_b4Hyp hA21 hD.hyp rfl hO2
  have hqhat := lred3_qhatOf_autSec hD rfl hT
  have hqs := lred3_qOf_autSec hD rfl hT hq
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
    sec_sq_eq_one hexp ⊤ _
  have hLt : CFSG.IsQuasisimple ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
    hb4.2.2.1
  obtain ⟨e⟩ := lred3_cq_autSec hLs hD.hyp.quasi (lred3_exists_ne hD.hyp rfl) hQ.stabKC hQ.faithful
  refine lred3_fourList_congr e.symm ?_
  rcases h45 _ hsv _ _ hb4 hqhat with ⟨-, ⟨A, hA'⟩, -⟩ | ⟨-, ht⟩ | h3
  · exact lred3_four_of_b42Types hG2 hLt
      (asB42Types_of_asB42With (KP := CFSG.SectionRank.IsKGroupCat) h42 _ hsv _ _ hb4 ⟨A, hA'⟩)
  · exact lred3_four_of_table hLt ht hqs
  · exact absurd h3.2.1 (not_lt.2 hqs)

end Stab

section Main

theorem insp4_of_inputs
    (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42)
    (h45 : AsB45) (hD310 : D310) : Insp4 := by
  intro W _ _ M Mp T L V hD hMp hqM hq
  rcases hD310 W M Mp T L V hD hMp hqM with hT | ⟨hfirst, -, -⟩
  · exact lred3_four_of_stab hA21 hG2 h42 h45 hD hMp (fun t ht => hT t ht) hq
  · exact lred3_four_of_first hD.hyp.quasi hfirst

end Main

end CFSG.Quasithin
