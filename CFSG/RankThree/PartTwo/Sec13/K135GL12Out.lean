module

public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12Defs
public import CFSG.RankThree.PartTwo.Sec13.K135GL12Census
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.RankThree.ThinCatalog.OuterThreeFree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPrime
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711c
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneAltSpor
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135GL12

open CFSG CFSG.RankThree.PartTwo.Sec13.K135SF TauCeti CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def OutFreeAt (d : ValidLieTypeIndex) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (CFSGIndex.lie d).Group) →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ f : MulAut S, orderOf f = p →
      f ∈ (MulAut.conj : S →* MulAut S).range

private theorem gl12kA_not_dvd_of_dvd_pow {m p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (h : m ∣ 30 ^ m) : ¬ p ∣ m := by
  intro hpm
  have h30 : p ∣ 30 := hp.dvd_of_dvd_pow (hpm.trans h)
  have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) h30
  interval_cases p <;> first | omega | norm_num at hp

private theorem gl12kA_survA_ge_one : ∀ x ∈ survA, 1 ≤ x.1 := by
  decide +kernel

private theorem gl12kA_survA_dvd : ∀ x ∈ survA,
    2 * x.2.2 * Nat.gcd (x.1 + 1) (x.2.1 ^ x.2.2 - 1) ∣
      30 ^ (2 * x.2.2 * Nat.gcd (x.1 + 1) (x.2.1 ^ x.2.2 - 1)) := by
  decide +kernel

private theorem gl12kA_survTA_ge_two : ∀ x ∈ survTA, 2 ≤ x.1 := by
  decide +kernel

private theorem gl12kA_survTA_dvd : ∀ x ∈ survTA,
    2 * x.2.2 * Nat.gcd (x.1 + 1) (x.2.1 ^ x.2.2 + 1) ∣
      30 ^ (2 * x.2.2 * Nat.gcd (x.1 + 1) (x.2.1 ^ x.2.2 + 1)) := by
  decide +kernel

private theorem gl12kA_outer_dvd_A {S : Type} [Group S] [Finite S] {n : ℕ} {q : PrimePower}
    (hn : 1 ≤ n) (hm : CFSG.Open.StatedClassicalModel S .PSL (n + 1) q.p q.exponent) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣
      2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact (CFSG.RankThree.ThinCatalog.outer_card_dvd_of_psl_two hm).trans
      (by rw [mul_assoc]; exact dvd_mul_left _ _)
  · exact (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (τ := .PSL) (Or.inl rfl) (by omega) q.prime_p q.exponent_pos hm).1

private theorem gl12kA_outer_dvd_twistedA {S : Type} [Group S] [Finite S] {n : ℕ} {q : PrimePower}
    (hn : 2 ≤ n) (hm : CFSG.Open.StatedClassicalModel S .PSU (n + 1) q.p q.exponent) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣
      2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent + 1) :=
  (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSU) (Or.inr rfl) (by omega) q.prime_p q.exponent_pos hm).1

theorem outFree_A {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A n q).Valid)
    (hs : GL12Surv (LieTypeIndex.A n q)) : OutFreeAt ⟨.A n q, hv⟩ := by
  intro S _ _ ⟨e⟩ p hp hp7 f hf
  have hs' : (n, q.p, q.exponent) ∈ survA := hs
  have hn : 1 ≤ n := gl12kA_survA_ge_one _ hs'
  have hL := CFSG.Models.lieModel_A n q hv e
  have hm : CFSG.Open.StatedClassicalModel S .PSL (n + 1) q.p q.exponent :=
    hL.2.resolve_right (fun h => absurd h.1 (by omega))
  have hdvd := gl12kA_outer_dvd_A hn hm
  have key : 2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent - 1) ∣
      30 ^ (2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent - 1)) :=
    gl12kA_survA_dvd _ hs'
  have hnd : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
    fun h => gl12kA_not_dvd_of_dvd_pow hp hp7 key (h.trans hdvd)
  have hpow : f ^ p = 1 := by
    rw [← hf]
    exact pow_orderOf_eq_one f
  exact CFSG.AGLEmbedding.LieOut.mem_innerAut_of_not_dvd_card_outer hp hnd hpow

theorem outFree_twistedA {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA n q).Valid)
    (hs : GL12Surv (LieTypeIndex.twistedA n q)) : OutFreeAt ⟨.twistedA n q, hv⟩ := by
  intro S _ _ ⟨e⟩ p hp hp7 f hf
  have hs' : (n, q.p, q.exponent) ∈ survTA := hs
  have hn : 2 ≤ n := gl12kA_survTA_ge_two _ hs'
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA n q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA n q
  have hf' : ValidLieTypeIndex.fieldExponent ⟨.twistedA n q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA n q
  have hL := CFSG.Models.lieModel_twistedA n q hv e
  rw [hc, hf'] at hL
  have hm : CFSG.Open.StatedClassicalModel S .PSU (n + 1) q.p q.exponent :=
    hL.2.resolve_right (fun h => absurd h.1 (by omega))
  have hdvd := gl12kA_outer_dvd_twistedA hn hm
  have key : 2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent + 1) ∣
      30 ^ (2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent + 1)) :=
    gl12kA_survTA_dvd _ hs'
  have hnd : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
    fun h => gl12kA_not_dvd_of_dvd_pow hp hp7 key (h.trans hdvd)
  have hpow : f ^ p = 1 := by
    rw [← hf]
    exact pow_orderOf_eq_one f
  exact CFSG.AGLEmbedding.LieOut.mem_innerAut_of_not_dvd_card_outer hp hnd hpow

private theorem gl12kB_not_dvd_of_dvd_pow {m p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (h : m ∣ 30 ^ m) : ¬ p ∣ m := by
  intro hpm
  have h30 : p ∣ 30 := hp.dvd_of_dvd_pow (hpm.trans h)
  have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) h30
  interval_cases p <;> first | omega | (norm_num at hp)

private theorem gl12kB_classical {G : Type} [Group G] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : CFSG.Models.LieModel G t n p f) :
    CFSG.Open.StatedClassicalModel G t n p f := by
  obtain ⟨-, hc | ⟨h0, -⟩⟩ := h
  · exact hc
  · exact absurd h0 hn

private theorem gl12kB_facts_B : ∀ x ∈ survB, x.1 ≠ 0 ∧ 0 < x.2.2 ∧ x.2.2 < 7 ∧
    2 * x.2.2 * Nat.gcd 2 (x.2.1 ^ x.2.2 - 1) ∣
      30 ^ (2 * x.2.2 * Nat.gcd 2 (x.2.1 ^ x.2.2 - 1)) := by
  decide +kernel

private theorem gl12kB_facts_C : ∀ x ∈ survC, x.1 ≠ 0 ∧
    2 * x.2.2 * Nat.gcd 2 (x.2.1 ^ x.2.2 - 1) ∣
      30 ^ (2 * x.2.2 * Nat.gcd 2 (x.2.1 ^ x.2.2 - 1)) := by
  decide +kernel

private theorem gl12kB_facts_D : ∀ x ∈ survD, x.1 ≠ 0 ∧ 0 < x.2.2 ∧ x.2.2 < 7 := by
  decide +kernel

private theorem gl12kB_facts_TD : ∀ x ∈ survTD, x.1 ≠ 0 ∧ 0 < x.2.2 ∧ x.2.2 < 7 := by
  decide +kernel

theorem outFree_B {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B n q).Valid)
    (hs : GL12Surv (LieTypeIndex.B n q)) : OutFreeAt ⟨.B n q, hv⟩ := by
  unfold OutFreeAt
  rintro S _ _ ⟨e⟩ p hp hp7 φ hφ
  have hφp : φ ^ p = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hsurv : (n, q.p, q.exponent) ∈ survB := hs
  have hn : n ≠ 0 := (gl12kB_facts_B _ hsurv).1
  have hfpos : 0 < q.exponent := (gl12kB_facts_B _ hsurv).2.1
  have hf7 : q.exponent < 7 := (gl12kB_facts_B _ hsurv).2.2.1
  have hm : 2 * q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) ∣
      30 ^ (2 * q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1)) :=
    (gl12kB_facts_B _ hsurv).2.2.2
  by_contra hnot
  rcases CFSG.Models.lieModel_B n q hv e with h | h
  · have hc := gl12kB_classical hn h
    have hdiv := (CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound
      S n q.p q.exponent hc).2.1
    have hnd : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
      fun hpd => gl12kB_not_dvd_of_dvd_pow hp hp7 hm (hpd.trans hdiv)
    exact hnot (CFSG.AGLEmbedding.LieOut.mem_innerAut_of_not_dvd_card_outer hp hnd hφp)
  · have hc := gl12kB_classical hn h
    have hdiv := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c.dvd_of_outer_omegaOdd
      hc hp (by omega) hφp hnot
    have := Nat.le_of_dvd hfpos hdiv
    omega

theorem outFree_C {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.C n q).Valid)
    (hs : GL12Surv (LieTypeIndex.C n q)) : OutFreeAt ⟨.C n q, hv⟩ := by
  unfold OutFreeAt
  rintro S _ _ ⟨e⟩ p hp hp7 φ hφ
  have hφp : φ ^ p = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hsurv : (n, q.p, q.exponent) ∈ survC := hs
  have hn : n ≠ 0 := (gl12kB_facts_C _ hsurv).1
  have hm : 2 * q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) ∣
      30 ^ (2 * q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1)) :=
    (gl12kB_facts_C _ hsurv).2
  have hc := gl12kB_classical hn (CFSG.Models.lieModel_C n q hv e)
  have hdiv := (CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound
    S n q.p q.exponent hc).2.1
  have hnd : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
    fun hpd => gl12kB_not_dvd_of_dvd_pow hp hp7 hm (hpd.trans hdiv)
  exact CFSG.AGLEmbedding.LieOut.mem_innerAut_of_not_dvd_card_outer hp hnd hφp

theorem outFree_D {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.D n q).Valid)
    (hs : GL12Surv (LieTypeIndex.D n q)) : OutFreeAt ⟨.D n q, hv⟩ := by
  unfold OutFreeAt
  rintro S _ _ ⟨e⟩ p hp hp7 φ hφ
  have hφp : φ ^ p = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hsurv : (n, q.p, q.exponent) ∈ survD := hs
  have hn : n ≠ 0 := (gl12kB_facts_D _ hsurv).1
  have hfpos : 0 < q.exponent := (gl12kB_facts_D _ hsurv).2.1
  have hf7 : q.exponent < 7 := (gl12kB_facts_D _ hsurv).2.2
  by_contra hnot
  have hc := gl12kB_classical hn (CFSG.Models.lieModel_D n q hv e)
  have hdiv := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c.dvd_of_outer_omegaPlus
    hc hp (by omega) (fun _ => by omega) hφp hnot
  have := Nat.le_of_dvd hfpos hdiv
  omega

theorem outFree_twistedD {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedD n q).Valid)
    (hs : GL12Surv (LieTypeIndex.twistedD n q)) : OutFreeAt ⟨.twistedD n q, hv⟩ := by
  unfold OutFreeAt
  rintro S _ _ ⟨e⟩ p hp hp7 φ hφ
  have hφp : φ ^ p = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hsurv : (n, q.p, q.exponent) ∈ survTD := hs
  have hn : n ≠ 0 := (gl12kB_facts_TD _ hsurv).1
  have hfpos : 0 < q.exponent := (gl12kB_facts_TD _ hsurv).2.1
  have hf7 : q.exponent < 7 := (gl12kB_facts_TD _ hsurv).2.2
  by_contra hnot
  have hc := gl12kB_classical hn (CFSG.Models.lieModel_twistedD n q hv e)
  have hdiv := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c.dvd_of_outer_omegaMinus
    hc hp (by omega) hφp hnot
  have := Nat.le_of_dvd hfpos hdiv
  omega


section Exc

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem gl12kE_card_outer_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) :
    Nat.card (Outer S) = Nat.card (Outer T) :=
  Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv

theorem gl12kE_card_outer_dvd {C Q : Type} [Group C] [Group Q] (Θ : MulAut C →* Q)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) :
    Nat.card (Outer C) ∣ Nat.card Q := by
  have e1 : (MulAut C ⧸ Θ.ker) ≃* Outer C := QuotientGroup.quotientMulEquivOfEq hker
  calc Nat.card (Outer C) = Nat.card (MulAut C ⧸ Θ.ker) := Nat.card_congr e1.symm.toEquiv
    _ = Nat.card Θ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv
    _ ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card _

theorem gl12kE_inner_of_not_dvd {S : Type} [Group S] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer S)) (f : MulAut S) (hf : orderOf f = p) :
    f ∈ (MulAut.conj : S →* MulAut S).range := by
  have h1 : orderOf (QuotientGroup.mk f : Outer S) ∣ p := by
    rw [← hf]
    exact orderOf_map_dvd (QuotientGroup.mk' (inner S)) f
  have h2 : orderOf (QuotientGroup.mk f : Outer S) ∣ Nat.card (Outer S) :=
    orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk f : Outer S) = 1 := by
    rcases (Nat.dvd_prime hp).1 h1 with h4 | h4
    · exact h4
    · exfalso
      apply h
      rw [← h4]
      exact h2
  exact (QuotientGroup.eq_one_iff (N := inner S) f).1 (orderOf_eq_one_iff.1 h3)


theorem gl12kE_outFree_of_card_dvd {d : ValidLieTypeIndex} {m : ℕ}
    (hcard : Nat.card (Outer (CFSGIndex.lie d).Group) ∣ m) (hm : 0 < m) (hm7 : m < 7) :
    OutFreeAt d := by
  intro S _ _ ⟨e⟩ p hp hp7 f hf
  have h1 : Nat.card (Outer S) ∣ m := by
    rw [gl12kE_card_outer_congr e]
    exact hcard
  refine gl12kE_inner_of_not_dvd hp (fun h => ?_) f hf
  have := Nat.le_of_dvd hm (h.trans h1)
  omega

section Fam42


theorem gl12kE_G2_card_outer (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq : 3 ≤ q.card) :
    Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) ∣ 2 * q.exponent := by
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  haveI : CharP K q.p := hKc
  obtain ⟨Q, _, _, Θ, hQ, hker⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_cyclic_G2 q hq K hK
  calc Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)
      = Nat.card (Outer _) := gl12kE_card_outer_congr e
    _ ∣ Nat.card Q := gl12kE_card_outer_dvd Θ hker
    _ ∣ 2 * q.exponent := hQ

theorem gl12kE_F4_card_outer (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) :
    Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) ∣ 2 * q.exponent := by
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  haveI : CharP K q.p := hKc
  obtain ⟨Q, _, _, Θ, hQ, hker⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_cyclic_F4 q K hK
  calc Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group)
      = Nat.card (Outer _) := gl12kE_card_outer_congr e
    _ ∣ Nat.card Q := gl12kE_card_outer_dvd Θ hker
    _ ∣ 2 * q.exponent := hQ

theorem gl12kE_E6_card_outer (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) ∣ 3 * 2 * q.exponent := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hdvd := (CFSG.LieType.Chevalley.ordinary_E_outer_order_Cartan_divisor
    CFSG.Blueprint.Chevalley.Tag.E6 (Or.inl rfl) q.prime_p q.exponent_pos K hK' 3 2
    (Or.inl ⟨rfl, rfl, rfl⟩)).1
  calc Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group)
      = Nat.card (Outer _) := gl12kE_card_outer_congr e
    _ ∣ 3 * 2 * q.exponent := hdvd

theorem gl12kE_3D4_card_outer (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) ∣ 3 * q.exponent := by
  obtain ⟨K, _, _, σ, hK, -, ⟨Θ, hker⟩, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hK' : Nat.card K = q.p ^ (3 * q.exponent) := by
    rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      q.prime_p (by have := q.exponent_pos; omega) hK'
  have hdvd := gl12kE_card_outer_dvd Θ hker
  rw [hcard] at hdvd
  calc Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)
      = Nat.card (Outer _) := gl12kE_card_outer_congr e
    _ ∣ 3 * q.exponent := hdvd

theorem gl12kE_Sz8_card_outer (hv : (TauCeti.LieTypeIndex.suzuki 1).Valid) :
    Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hv⟩).Group) ∣ 2 * 1 + 1 := by
  have hM := CFSG.StandardType.ChevTwo.suzukiModel_of_valid 1 hv
    (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.suzuki 1, hv⟩))
  exact (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 (2 * 1 + 1)
    hM).1.2.1


theorem outFree_G2 {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid)
    (hs : GL12Surv (LieTypeIndex.G2 q)) : OutFreeAt ⟨.G2 q, hv⟩ := by
  have hs' : (q.p, q.exponent) ∈ survG2 := hs
  have hf2 : q.exponent ≤ 2 := by
    have key : ∀ x ∈ survG2, x.2 ≤ 2 := by decide
    exact key _ hs'
  have hq3 : 3 ≤ q.card := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hpos := q.exponent_pos
  exact gl12kE_outFree_of_card_dvd (gl12kE_G2_card_outer q hv hq3) (by omega) (by omega)

theorem outFree_F4 {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid)
    (hs : GL12Surv (LieTypeIndex.F4 q)) : OutFreeAt ⟨.F4 q, hv⟩ := by
  have hs' : (q.p, q.exponent) = (3, 1) := hs
  have hf1 : q.exponent = 1 := (Prod.mk.inj hs').2
  exact gl12kE_outFree_of_card_dvd (gl12kE_F4_card_outer q hv) (by omega) (by omega)

theorem outFree_E6 {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid)
    (hs : GL12Surv (LieTypeIndex.E6 q)) : OutFreeAt ⟨.E6 q, hv⟩ := by
  have hs' : (q.p, q.exponent) = (3, 1) := hs
  have hf1 : q.exponent = 1 := (Prod.mk.inj hs').2
  exact gl12kE_outFree_of_card_dvd (gl12kE_E6_card_outer q hv) (by omega) (by omega)

theorem outFree_trialityD4 {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hs : GL12Surv (LieTypeIndex.trialityD4 q)) : OutFreeAt ⟨.trialityD4 q, hv⟩ := by
  have hs' : (q.p, q.exponent) ∈ survD4t := hs
  have hf1 : q.exponent = 1 := by
    have key : ∀ x ∈ survD4t, x.2 = 1 := by decide
    exact key _ hs'
  exact gl12kE_outFree_of_card_dvd (gl12kE_3D4_card_outer q hv) (by omega) (by omega)

theorem outFree_suzuki {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid)
    (hs : GL12Surv (LieTypeIndex.suzuki m)) : OutFreeAt ⟨.suzuki m, hv⟩ := by
  have hm1 : m = 1 := hs
  subst hm1
  exact gl12kE_outFree_of_card_dvd (gl12kE_Sz8_card_outer hv) (by omega) (by omega)

end Fam42

section Tits


theorem gl12kE_Tits_card_outer (hv : (TauCeti.LieTypeIndex.tits).Valid) :
    Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) = 2 := by
  have hM := CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv
    (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.tits, hv⟩))
  exact (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound _ 2 1 hM).2.2.1

theorem outFree_tits (hv : LieTypeIndex.tits.Valid) : OutFreeAt ⟨.tits, hv⟩ := by
  refine gl12kE_outFree_of_card_dvd (m := 2) ?_ (by omega) (by omega)
  rw [gl12kE_Tits_card_outer hv]

end Tits

end Exc

theorem kFactOutGL12_holds :
    KFactOutGL12 := by
  have hB : LieOrderBridge := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hSpor : ∀ {K : Type} [Group K] [Finite K] {p : ℕ}, p.Prime → p ≠ 2 → ∀ {s : SporadicName},
      (K ≃* (CFSGIndex.sporadic s).Group) →
        ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
    fun {K} [Group K] [Finite K] {p} hp hp2 {s} e => CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne.not_dvd_card_outer_spor hp hp2 e
  intro S _ _ hK hS hna hGL p hp hp7 f hf
  have hfp : f ^ p = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  haveI := hS
  obtain ⟨i, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.isCatalogGroup_of_isKGroup_simple hK
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact CFSG.AGLEmbedding.LieOut.mem_innerAut_of_not_dvd_card_outer hp
      (CFSG.AGLEmbedding.not_dvd_card_outer_of_mulEquiv_alternatingGroup e hn hp (by omega)) hfp
  | sporadic s =>
    exact CFSG.AGLEmbedding.LieOut.mem_innerAut_of_not_dvd_card_outer hp
      (hSpor hp (by omega) e) hfp
  | lie d =>
    have hord : Nat.card S = I1420.lieOrderFormula d.1 := hB d S ⟨e⟩
    have hdiv : I1420.lieOrderFormula d.1 ∣ gl12Order := hord ▸ gl12Data_card_dvd hGL
    have hs := lie_census d.2 hdiv
    obtain ⟨d, hv⟩ := d
    cases d with
    | A n q => exact outFree_A hv hs S ⟨e⟩ p hp hp7 f hf
    | twistedA n q => exact outFree_twistedA hv hs S ⟨e⟩ p hp hp7 f hf
    | B n q => exact outFree_B hv hs S ⟨e⟩ p hp hp7 f hf
    | C n q => exact outFree_C hv hs S ⟨e⟩ p hp hp7 f hf
    | D n q => exact outFree_D hv hs S ⟨e⟩ p hp hp7 f hf
    | twistedD n q => exact outFree_twistedD hv hs S ⟨e⟩ p hp hp7 f hf
    | E6 q => exact outFree_E6 hv hs S ⟨e⟩ p hp hp7 f hf
    | E7 q => exact False.elim hs
    | E8 q => exact False.elim hs
    | F4 q => exact outFree_F4 hv hs S ⟨e⟩ p hp hp7 f hf
    | G2 q => exact outFree_G2 hv hs S ⟨e⟩ p hp hp7 f hf
    | twistedE6 q => exact False.elim hs
    | trialityD4 q => exact outFree_trialityD4 hv hs S ⟨e⟩ p hp hp7 f hf
    | suzuki m => exact outFree_suzuki hv hs S ⟨e⟩ p hp hp7 f hf
    | reeG2 m => exact False.elim hs
    | reeF4 m => exact False.elim hs
    | tits => exact outFree_tits hv S ⟨e⟩ p hp hp7 f hf

end CFSG.RankThree.PartTwo.Sec13.K135GL12
