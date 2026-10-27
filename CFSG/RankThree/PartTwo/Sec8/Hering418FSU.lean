module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiInndiag
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCTri
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofSU3Kind
public import CFSG.RankThree.PartTwo.Sec8.Hering418FDich
public import CFSG.RankThree.PartTwo.Sec8.Hering418FSplit

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section SU


theorem dichotomy_suThreeSixOdd {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hX : IsSUThreeSixOdd (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), innBar L ≤ N ∧
      (∀ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsElemAbelian 3 F → F ≤ N →
        Nat.card F ≤ 9) ∧
      ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)), x ^ 3 = 1 →
        (rho L ⟨x, hx⟩ ∈ N ∧ ¬ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) ∨
          (rho L ⟨x, hx⟩ ∉ N ∧ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) := by
  obtain ⟨k, hk, ⟨m, rfl⟩, ho, F, hFf, hFfin, hF, ⟨φ⟩⟩ := hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : 1 ≤ m := by omega
  have hq : 2 ^ (3 * m) % 3 = 2 := two_pow_mod_three_of_odd' ho
  have hm3 : 3 ∣ 2 ^ (3 * m) + 1 := by omega
  have hn3 : 3 ≤ 3 * m := by omega
  have hSL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m)) :=
    ⟨F, hFf, hFfin, Or.inr ⟨hF, hq, ⟨φ⟩⟩⟩
  have hIso : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m)) :=
    ⟨F, hFf, hFfin, hF, ⟨φ⟩⟩
  have hperf : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2.1
  have hU : UnitaryFieldData 2 (3 * m) F := ⟨Nat.prime_two, by omega, by
    rw [hF, ← pow_mul, mul_comm]⟩
  have hq2 : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  have hfin := hU.finite
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card (p := 2) (f := 2 * (3 * m)) Nat.prime_two
    (by norm_num) (by rw [hF, ← pow_mul, mul_comm])
  have hii : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)),
      (KFacts.InducesStdKind L x .inner ∨ KFacts.InducesStdKind L x .diagonal) →
        rho L ⟨x, hx⟩ ∈ commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
    intro x hx hk
    obtain ⟨k', hk', hk''⟩ :
        ∃ k', KFacts.InducesStdKind L x k' ∧ (k' = .inner ∨ k' = .diagonal) := by
      rcases hk with hk | hk
      · exact ⟨_, hk, Or.inl rfl⟩
      · exact ⟨_, hk, Or.inr rfl⟩
    obtain ⟨K, _, h, hq', e₁, hxN, hkind⟩ :=
      KFacts.inducesKindSU3_of_inducesStdKind hn3 hm3 hIso hk'
    have : CharP K 2 := h.charP
    exact KFacts.mem_commutator_of_inducesKindSU3 h hq' e₁ hxN hkind hk''
  have hff : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)),
      (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) →
        rho L ⟨x, hx⟩ ∉ commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := by
    intro x hx hk
    obtain ⟨k', hk', hk1, hk2⟩ : ∃ k', KFacts.InducesStdKind L x k' ∧ k' ≠ .inner ∧
        k' ≠ .diagonal := by
      rcases hk with hk | hk
      · exact ⟨_, hk, by decide, by decide⟩
      · exact ⟨_, hk, by decide, by decide⟩
    obtain ⟨K, _, h, hq', e₁, hxN, hkind⟩ :=
      KFacts.inducesKindSU3_of_inducesStdKind hn3 hm3 hIso hk'
    exact KFacts.not_mem_commutator_of_inducesKindSU3 h hq' e₁ hxN hkind hk1 hk2
  let φ' : MulAut (L ⧸ aschbacherSolvableCore 3 L) →* MulAut (unitaryPSU hU 3) :=
    (MulAut.congr (KFacts.suCenterEquiv hU hq2)).toMonoidHom.comp
      ((KFacts.centerDescend (unitarySU 2 (3 * m) F 3)).comp (MulAut.congr φ).toMonoidHom)
  have hφ' : Function.Injective φ' :=
    (MulAut.congr (KFacts.suCenterEquiv hU hq2)).injective.comp
      ((Sec21.Item223CensusProof.centerDescend_injective_unitarySU hU hq2).comp
        (MulAut.congr φ).injective)
  refine ⟨commutator (MulAut (L ⧸ aschbacherSolvableCore 3 L)), ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact KFacts.conj_mem_commutator y
  · intro F' hF' hFN
    have hle : F'.map φ' ≤ (KFacts.psuConj hU).range := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact KFacts.commutator_le_psuConj_range hU hq2 (KFacts.map_mem_commutator φ' (hFN hσ))
    have := Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 (F'.map φ')
      (hF'.map φ') hle
    rwa [Subgroup.card_map_of_injective hφ'] at this
  · intro x hx hx3
    rcases KFacts.inducesStdKind_trichotomy_of_isSLThreePiAt hm1 hSL hx hx3 with h | h | h
    · exact Or.inl ⟨hii x hx (Or.inl h), fun hk => hff x hx hk (hii x hx (Or.inl h))⟩
    · exact Or.inl ⟨hii x hx (Or.inr h), fun hk => hff x hx hk (hii x hx (Or.inr h))⟩
    · exact Or.inr ⟨hff x hx (Or.inl h), Or.inl h⟩

theorem pow_apply_eq_of_apply_eq {X : Type*} [Group X] {α : MulAut X} {u : X} (h : α u = u)
    (j : ℕ) : (α ^ j) u = u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, MulAut.mul_apply, h, ih]

theorem kF418OuterOn_suThreeSixOdd : KF418OuterOn (fun X _ => IsSUThreeSixOdd X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨k, hk, ⟨m, rfl⟩, ho, F, hFf, hFfin, hF, ⟨φ⟩⟩ := hl
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hβ : Sec4.InducesOuterTheta b L := by
    rcases hbk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .field) L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .graphField) L h (by decide)
  have hm1 : 1 ≤ m := by omega
  have hq : 2 ^ (3 * m) % 3 = 2 := two_pow_mod_three_of_odd' ho
  have hm3 : 3 ∣ 2 ^ (3 * m) + 1 := by omega
  have hIso : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m)) :=
    ⟨F, hFf, hFfin, hF, ⟨φ⟩⟩
  have hSL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m)) :=
    ⟨F, hFf, hFfin, Or.inr ⟨hF, hq, ⟨φ⟩⟩⟩
  have hbF : KFacts.InducesStdKind L b .field :=
    hbk.resolve_right (KFacts.not_inducesStdKind_graphField_of_isoSUThree (by omega) hm3 hIso)
  have hC := KFacts.isSLThreePiAt_barCentralizer_of_field hm1 hSL hb3 (Or.inl hbF)
  by_cases hm1' : m = 1
  ·
    subst hm1'
    exfalso
    obtain ⟨K'', hK''f, hK''fin, h | h⟩ := hC
    · obtain ⟨hK'', hmod, -⟩ := h
      omega
    · obtain ⟨hK'', -, ⟨ι⟩⟩ := h
      have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) K'') :=
        CFSG.Quasithin.isSolvable_statedSU_one hK''
      haveI hsolvC : Group.IsSolvable ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) :=
        Group.isSolvable_of_isSolvable_injective (f := ι.toMonoidHom) ι.injective
      have hle := imageModTheta_le_barCentralizer_of_le c.hbL c.hb3 c.hKL c.hKb
      haveI : Group.IsSolvable ↥(Sec8.imageModTheta L K) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      haveI := isPerfect_imageModTheta hK
      haveI : Nontrivial ↥(Sec8.imageModTheta L K) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr (imageModTheta_ne_bot c.hKL hKq)
      have := IsSolvable.commutator_lt_top_of_nontrivial (Sec8.imageModTheta L K)
      rw [Group.IsPerfect.commutator_eq_top] at this
      exact lt_irrefl _ this
  have hm2 : 2 ≤ m := by omega
  have hmo : Odd m := (Nat.odd_mul.mp ho).2
  have hqC := KFacts.isQuasisimple_of_isSLThreePiAt_two_pow hm2 hC
  have hcardC := KFacts.card_center_of_isSLThreePiAt_two_pow hm1 hC
  have hZ : IsPGroup 3 (Subgroup.center ↥(Sec8.barCentralizer (Subgroup.zpowers b) L)) :=
    IsPGroup.of_card (n := 1) (by rw [hcardC, pow_one])
  obtain ⟨Ψ, hΨ⟩ := c.exists_mulEquiv_barCentralizer_of_isQuasisimple hK hqC hZ
  have hcardK : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3 := by
    rw [card_center_congr Ψ]
    exact hcardC
  have hZne : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardK
    omega
  rcases htype with hSU | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  rotate_left
  · exact hZne (Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inl rfl) hn) hKq ψ)
  · exact hZne (Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inr rfl) hn) hKq ψ)
  obtain ⟨F', hF'f, hF'fin, hF', ⟨ψ⟩⟩ := hSU
  have hcf := center_su3_facts (K := F') hn hF'
  have h3q : 3 ∣ 2 ^ (3 * n) + 1 := by
    apply hcf.2
    intro hbot
    apply hZne
    rw [← Subgroup.card_eq_one, card_center_congr ψ, Subgroup.card_eq_one.mpr hbot]
  have hodd : Odd n := odd_of_three_dvd_two_pow h3q
  have hSU' : Sec8.IsoSUThree (K ⧸ aschbacherSolvableCore 3 K) (2 ^ (3 * n)) :=
    ⟨F', hF'f, hF'fin, hF', ⟨ψ⟩⟩
  obtain ⟨F'', hF''f, hF''fin, hF'', ⟨ψ'⟩⟩ :=
    KFacts.isoSUThree_barCentralizer_of_inducesStdKind hodd hSU' c.ha3 hKa
  have hU'' : UnitaryFieldData 2 n F'' := ⟨Nat.prime_two, hn, by rw [hF'', ← pow_mul, mul_comm]⟩
  obtain ⟨u0, hu04, hu02⟩ := Item8KFacts2Proof.exists_unitarySU_pow_four hU'' hodd
  let ι : ↥(Sec8.barCentralizer (Subgroup.zpowers a) K) →* L ⧸ aschbacherSolvableCore 3 L :=
    ((Sec8.barCentralizer (Subgroup.zpowers b) L).subtype.comp Ψ.toMonoidHom).comp
      (Sec8.barCentralizer (Subgroup.zpowers a) K).subtype
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Ψ.injective.comp Subtype.val_injective)
  set ū : ↥(Sec8.barCentralizer (Subgroup.zpowers a) K) := ψ'.symm u0 with hū
  have hū4 : ū ^ 4 = 1 := by
    rw [hū, ← map_pow, hu04, map_one]
  have hū2 : ū ^ 2 ≠ 1 := by
    rw [hū, ← map_pow]
    intro h
    exact hu02 (ψ'.symm.injective (h.trans (map_one _).symm))
  set u : L ⧸ aschbacherSolvableCore 3 L := ι ū with hu
  have hu4 : u ^ 4 = 1 := by
    rw [hu, ← map_pow, hū4, map_one]
  have hu2 : u ^ 2 ≠ 1 := by
    rw [hu, ← map_pow]
    intro h
    exact hū2 (hι (h.trans (map_one ι).symm))
  have hfixK : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩)
      ((ū : ↥(Sec8.barCentralizer (Subgroup.zpowers a) K)) : K ⧸ aschbacherSolvableCore 3 K) =
      ((ū : ↥(Sec8.barCentralizer (Subgroup.zpowers a) K)) : K ⧸ aschbacherSolvableCore 3 K) :=
    (KFacts.mem_barCentralizer_zpowers_iff c.haK _).mp ū.2
  have hαu : c.alpha u = u := by
    have h1 := hΨ ((ū : ↥(Sec8.barCentralizer (Subgroup.zpowers a) K)) :
      K ⧸ aschbacherSolvableCore 3 K)
    rw [hfixK] at h1
    exact h1.symm
  have hβu : c.beta u = u :=
    (KFacts.mem_barCentralizer_zpowers_iff c.hbL _).mp
      (Ψ ((ū : ↥(Sec8.barCentralizer (Subgroup.zpowers a) K)) :
        K ⧸ aschbacherSolvableCore 3 K)).2
  have hOTC : KFacts.OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) :=
    KFacts.outThreeCyclic_of_statedSU hL.2.2 (by omega : 1 ≤ 3 * m) hF φ
  have hcomm : Commute c.beta c.alpha := c.alpha_mul_beta.symm
  obtain ⟨i, -, x, hx⟩ := hOTC c.beta c.alpha hcomm c.beta_pow_three c.alpha_pow_three hβ.2
  have hτu : (c.beta ^ i * c.alpha) u = u := by
    rw [MulAut.mul_apply, hαu]
    exact pow_apply_eq_of_apply_eq hβu i
  have hτ3 : (c.beta ^ i * c.alpha) ^ 3 = 1 := by
    rw [(hcomm.pow_left i).mul_pow, c.alpha_pow_three, mul_one, ← pow_mul, mul_comm, pow_mul,
      c.beta_pow_three, one_pow]
  have hU : UnitaryFieldData 2 (3 * m) F := ⟨Nat.prime_two, by omega, by
    rw [hF, ← pow_mul, mul_comm]⟩
  set A : KFacts.unitaryIsom3 hU := ⟨((φ x : StatedSU 3 (2 ^ (3 * m)) F) : GL (Fin 3) F),
    KFacts.unitarySU_le_unitaryIsom3 (φ x).2⟩ with hA
  have hcongr : MulAut.congr φ (MulAut.conj x) = KFacts.suConj hU A := by
    refine MulEquiv.ext fun g => ?_
    refine Subtype.ext ?_
    rw [KFacts.coe_suConj]
    change ((φ (x * φ.symm g * x⁻¹) : StatedSU 3 (2 ^ (3 * m)) F) : GL (Fin 3) F) = _
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hAfix : KFacts.suConj hU A (φ u) = φ u := by
    rw [← hcongr]
    change φ ((MulAut.conj x) (φ.symm (φ u))) = φ u
    rw [MulEquiv.symm_apply_apply, hx, hτu]
  have hA3 : KFacts.suConj hU A ^ 3 = 1 := by
    rw [← hcongr, ← map_pow, hx, hτ3, map_one]
  have hA1 := Item8KFacts2Proof.eq_one_of_suConj_of_fixed hU ho hA3 hAfix
    (by rw [← map_pow, hu4, map_one])
    (by rw [← map_pow]; intro h; exact hu2 (φ.injective (h.trans (map_one φ).symm)))
  have : c.beta ^ i * c.alpha = 1 := by
    have h2 : MulAut.congr φ (MulAut.conj x) = 1 := hcongr.trans hA1
    rw [← hx]
    exact (MulAut.congr φ).injective (h2.trans (map_one _).symm)
  apply c.hαβ (i : ℤ)
  rw [zpow_natCast, (hcomm.pow_left i).symm.eq]
  exact this

theorem kF418ModelOn_suThreeSixOdd : KF418ModelOn (fun X _ => IsSUThreeSixOdd X) :=
  kF418ModelOn_of_dichotomy (fun _ _ _ _ hL hl => dichotomy_suThreeSixOdd hL hl)
    kF418OuterOn_suThreeSixOdd

end SU

end CFSG.RankThree.PartTwo.Sec8.Hering418
