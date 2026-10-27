module

public import CFSG.Quasithin.Recognition.Stroth.LieExtInner
public import CFSG.GroupTheory.OddOrderClosurePResidual
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.Quasithin.H13

private theorem exists_pow_pow_eq_one_of_mk'_pow_pow_eq_one {X : Type} [Group X]
    {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup 2 Q) {x : X} {k : ℕ}
    (h : (QuotientGroup.mk' Q x) ^ 2 ^ k = 1) : ∃ j : ℕ, x ^ 2 ^ j = 1 := by
  have hxQ : x ^ 2 ^ k ∈ Q := by
    have h1 : (QuotientGroup.mk' Q) (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact h
    exact (QuotientGroup.eq_one_iff (N := Q) (x ^ 2 ^ k)).mp h1
  obtain ⟨m, hm⟩ := hQ.exists_pow_pow_eq_one ⟨x ^ 2 ^ k, hxQ⟩
  have hval : (x ^ 2 ^ k) ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  exact ⟨k + m, by rw [pow_add, pow_mul]; exact hval⟩

private theorem isPGroup_zpowers_of_pow_pow_eq_one {X : Type} [Group X] [Finite X] {x : X}
    (h : ∃ j : ℕ, x ^ 2 ^ j = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hj)
  exact IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := m) (by
    rw [Nat.card_zpowers, hm])

theorem eq_top_of_normal_odd_index_of_two_generated_quotient {X : Type} [Group X] [Finite X]
    {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup 2 Q)
    (hgen : Subgroup.closure {x : X ⧸ Q | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    {N : Subgroup X} (hN : N.Normal) (hodd : Odd N.index) : N = ⊤ := by
  have hQN : Q ≤ N := CFSG.GH74.Uniqueness.SU.K.KI8.le_of_isPGroup_of_odd_index hodd hQ
  have hNtop : N.map (QuotientGroup.mk' Q) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro y ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q y
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    exact CFSG.GH74.Uniqueness.SU.K.KI8.le_of_isPGroup_of_odd_index hodd
      (isPGroup_zpowers_of_pow_pow_eq_one
        (exists_pow_pow_eq_one_of_mk'_pow_pow_eq_one hQ hk))
      (Subgroup.mem_zpowers x)
  calc N = (N.map (QuotientGroup.mk' Q)).comap (QuotientGroup.mk' Q) :=
        (Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])).symm
    _ = ⊤ := by rw [hNtop, Subgroup.comap_top]

private theorem closure_twoElements_normal (Y : Type) [Group Y] :
    (Subgroup.closure {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1}).Normal := by
  have hconj : ∀ g x : Y, x ∈ {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1} →
      g * x * g⁻¹ ∈ {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    rintro g x ⟨k, hk⟩
    exact ⟨k, by rw [conj_pow, hk]; simp⟩
  rw [show Subgroup.closure {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1} =
      Subgroup.normalClosure {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1} from
    (CFSG.GroupTheory.normalClosure_eq_closure_of_conj_invariant hconj).symm]
  exact Subgroup.normalClosure_normal

private theorem exists_orderOf_eq_two_of_even_card {Y : Type} [Group Y] [Finite Y]
    (heven : Even (Nat.card Y)) : ∃ x : Y, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)

private theorem closure_twoElements_eq_top_of_isSimpleGroup_even {Y : Type} [Group Y] [Finite Y]
    (hsimple : IsSimpleGroup Y) (heven : Even (Nat.card Y)) :
    Subgroup.closure {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤ := by
  let K : Subgroup Y := Subgroup.closure {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1}
  have hKnormal : K.Normal := closure_twoElements_normal Y
  haveI : K.Normal := hKnormal
  have hKne : K ≠ ⊥ := by
    obtain ⟨x, hx2⟩ := exists_orderOf_eq_two_of_even_card heven
    have hxK : x ∈ K :=
      Subgroup.subset_closure ⟨1, by simpa [hx2] using pow_orderOf_eq_one x⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hxK
    rw [hxK, orderOf_one] at hx2
    omega
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exact absurd h hKne
  · exact h

theorem closure_twoElements_eq_top_of_perfect_odd_center {Y : Type} [Group Y] [Finite Y]
    (hperf : Group.IsPerfect Y) (hZodd : Odd (Nat.card (Subgroup.center Y)))
    (hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y)) (heven : Even (Nat.card Y)) :
    Subgroup.closure {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤ := by
  let K : Subgroup Y := Subgroup.closure {x : Y | ∃ k : ℕ, x ^ 2 ^ k = 1}
  have hKnormal : K.Normal := closure_twoElements_normal Y
  haveI : K.Normal := hKnormal
  obtain ⟨x, hx2⟩ := exists_orderOf_eq_two_of_even_card heven
  have hxK : x ∈ K :=
    Subgroup.subset_closure ⟨1, by simpa [hx2] using pow_orderOf_eq_one x⟩
  have hKnotcentral : ¬ K ≤ Subgroup.center Y := by
    intro hle
    have hzp : Subgroup.zpowers x ≤ Subgroup.center Y :=
      Subgroup.zpowers_le.mpr (hle hxK)
    have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥(Subgroup.center Y) :=
      Subgroup.card_dvd_of_le hzp
    rw [Nat.card_zpowers, hx2] at hdvd
    exact hZodd.not_two_dvd_nat hdvd
  haveI : (Subgroup.center Y).Normal := inferInstance
  haveI : (K ⊔ Subgroup.center Y).Normal := inferInstance
  have himage_ne : (K ⊔ Subgroup.center Y).map (QuotientGroup.mk' (Subgroup.center Y)) ≠ ⊥ := by
    intro hbot
    have hle : K ⊔ Subgroup.center Y ≤ Subgroup.center Y := by
      have h := (Subgroup.map_eq_bot_iff (K ⊔ Subgroup.center Y)).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    exact hKnotcentral (le_trans le_sup_left hle)
  have himage_top : (K ⊔ Subgroup.center Y).map (QuotientGroup.mk' (Subgroup.center Y)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((K ⊔ Subgroup.center Y).map (QuotientGroup.mk' (Subgroup.center Y))) with h | h
    · exact absurd h himage_ne
    · exact h
  have hKZtop : K ⊔ Subgroup.center Y = ⊤ := by
    have hker : (QuotientGroup.mk' (Subgroup.center Y)).ker ≤ K ⊔ Subgroup.center Y := by
      rw [QuotientGroup.ker_mk']
      exact le_sup_right
    calc K ⊔ Subgroup.center Y =
          ((K ⊔ Subgroup.center Y).map (QuotientGroup.mk' (Subgroup.center Y))).comap
            (QuotientGroup.mk' (Subgroup.center Y)) := (Subgroup.comap_map_eq_self hker).symm
      _ = ⊤ := by rw [himage_top, Subgroup.comap_top]
  have hcommle : commutator Y ≤ K :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hKZtop
      (inferInstance : IsMulCommutative ↥(Subgroup.center Y))
  have htop : (⊤ : Subgroup Y) ≤ K :=
    (Group.isPerfect_def (G := Y)).1 hperf ▸ hcommle
  exact eq_top_iff.mpr htop

private theorem closure_twoElements_eq_top_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤) :
    Subgroup.closure {y : Y | ∃ k : ℕ, y ^ 2 ^ k = 1} = ⊤ := by
  have hmap : (Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1}).map e.toMonoidHom = ⊤ := by
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← hmap, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e.symm y, ⟨k, by rw [← map_pow, hk, map_one]⟩, e.apply_symm_apply y⟩
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩

private theorem ne_three_two_of_two_le {k : ℕ} (hk : 2 ≤ k) : ((3 : ℕ), 2 ^ k) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ k = 2 := (Prod.mk.inj h).2
  have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

private theorem even_card_statedProj_statedSU_three {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2) :
    Even (Nat.card (StatedProj (StatedSU 3 (2 ^ k) F))) := by
  have hk1 : 1 ≤ k := by omega
  have hnq := ne_three_two_of_two_le hk
  have hadm : StatedLieAdmissible .PSU 3 2 k := ⟨Nat.prime_two, hk1, by norm_num, hnq⟩
  have hSCM : StatedClassicalModel (StatedProj (StatedSU 3 (2 ^ k) F)) .PSU 3 2 k :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have hord : Nat.card (StatedProj (StatedSU 3 (2 ^ k) F)) = ordTwistedA 2 (2 ^ k) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hSCM).2.1 rfl
  obtain ⟨r, -, hfac⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := k) (by norm_num) hk1).two
  rw [hord, hfac, show 2 * (2 + 1) / 2 = 3 by norm_num]
  exact (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega)).mul_right r

private theorem even_card_statedSU_three {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ k) ^ 2) : Even (Nat.card (StatedSU 3 (2 ^ k) F)) := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ k) F))
  rw [hcard]
  exact (even_card_statedProj_statedSU_three hk hF).mul_right _

private theorem closure_twoElements_eq_top_statedSU_three {k : ℕ} (hk : 2 ≤ k) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2) :
    Subgroup.closure {x : StatedSU 3 (2 ^ k) F | ∃ j : ℕ, x ^ 2 ^ j = 1} = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk1 : 1 ≤ k := by omega
  have hnq := ne_three_two_of_two_le hk
  obtain ⟨hq, hZ⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := k) (n := 3)
      hF le_rfl hnq
  haveI : Finite (StatedSU 3 (2 ^ k) F) := inferInstance
  have hZodd : Odd (Nat.card (Subgroup.center (StatedSU 3 (2 ^ k) F))) := by
    rw [hZ, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 3)
      (by norm_num)).2.2]
    exact Odd.of_dvd_nat (by norm_num : Odd 3) (Nat.gcd_dvd_left _ _)
  exact closure_twoElements_eq_top_of_perfect_odd_center hq.1 hZodd hq.2.1
    (even_card_statedSU_three hk hF)

private theorem closure_twoElements_eq_top_statedProj_three {k : ℕ} (hk : 2 ≤ k) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2) :
    Subgroup.closure {x : StatedProj (StatedSU 3 (2 ^ k) F) | ∃ j : ℕ, x ^ 2 ^ j = 1} = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq := ne_three_two_of_two_le hk
  haveI : Finite (StatedProj (StatedSU 3 (2 ^ k) F)) := inferInstance
  exact closure_twoElements_eq_top_of_isSimpleGroup_even
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 k hF 3
      le_rfl hnq)
    (even_card_statedProj_statedSU_three hk hF)

theorem eq_top_of_normal_odd_index_of_u3 {L : Type} [Group L] [Finite L] {k : ℕ} (hk : 2 ≤ k)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (h : Nonempty (oTwoQuot L ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot L ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    ∀ N : Subgroup L, N.Normal → Odd N.index → N = ⊤ := by
  intro N hN hodd
  have hgen : Subgroup.closure {x : oTwoQuot L | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤ := by
    rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact closure_twoElements_eq_top_of_mulEquiv e.symm
        (closure_twoElements_eq_top_statedSU_three hk hF)
    · exact closure_twoElements_eq_top_of_mulEquiv e.symm
        (closure_twoElements_eq_top_statedProj_three hk hF)
  exact eq_top_of_normal_odd_index_of_two_generated_quotient
    (pCore_isPGroup (G := L) (p := 2)) hgen hN hodd

theorem psu5_model_facts {D : Type} [Group D] {k : ℕ} (hk : 2 ≤ k)
    (hD : IsLieOverTwo .PSU 5 k D) :
    Finite D ∧ Subgroup.center D = ⊥ ∧
      ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card T = (2 ^ k) ^ 10 := by
  have hk1 : 1 ≤ k := by omega
  have hD' : StatedClassicalModel D .PSU 5 2 k :=
    CFSG.Blueprint.LieModel.statedClassicalModel (G := D) (t := .PSU) (n := 5) (p := 2) (f := k)
      hD (by decide)
  have hsimple : IsSimpleGroup D :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity D 5 2 k hD').2
  have hord : Nat.card D = ordTwistedA 4 (2 ^ k) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hD').2.1 rfl
  obtain ⟨r, hr, hfac⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 4) (g := k) (by norm_num) hk1).two
  have hfac' : Nat.card D = 2 ^ (k * 10) * r := by
    rw [hord, hfac, show 4 * (4 + 1) / 2 = 10 by norm_num]
  have hnotprime : ¬ (Nat.card D).Prime := by
    intro hp
    have h2dvd : 2 ∣ Nat.card D := by
      rw [hfac']
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) r
    have hne2 : Nat.card D ≠ 2 := by
      rw [hfac']
      have h1 : 2 ^ 20 ≤ 2 ^ (k * 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ 20 ≤ 2 ^ (k * 10) * r :=
        h1.trans (Nat.le_mul_of_pos_right _ hr.pos)
      omega
    rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h | h
    · omega
    · exact hne2 h.symm
  obtain ⟨-, K, hKfield, hKfinite, -, ⟨e⟩⟩ := hD'
  letI : Field K := hKfield
  haveI : Finite K := hKfinite
  have hZ : Subgroup.center D = ⊥ :=
    CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_card_not_prime hnotprime
  have hfinD : Finite D := Finite.of_equiv _ e.symm.toEquiv
  haveI : Finite D := hfinD
  have hTcard : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card T = (2 ^ k) ^ 10 := by
    intro T hT
    have h := CFSG.Quasithin.H13.FiveNorm.card_eq_of_isSylowTwoOf_top (W := D) hT hfac'
      hr.not_two_dvd_nat
    rwa [show (2 : ℕ) ^ (k * 10) = (2 ^ k) ^ 10 by rw [pow_mul]] at h
  exact ⟨hfinD, hZ, hTcard⟩

theorem isAmalgamOfGroup_psu5_of_ext {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} {k : ℕ} (hF : F112Hyp L1 L2 S) (hk : 2 ≤ k)
    {F : Type} [Field F] [Finite F] (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2))
    (hS : Nat.card S = (2 ^ k) ^ 10)
    {D : Type} [Group D] (hD : IsLieOverTwo .PSU 5 k D)
    (hE : IsExtensionOfLieAmalgam D (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 5 k) := by
  classical
  obtain ⟨hfinD, hZ, hTcard⟩ := psu5_model_facts hk hD
  haveI : Finite D := hfinD
  have hL1' := eq_top_of_normal_odd_index_of_u3 hk hFc hU3
  have hL2' := eq_top_of_normal_odd_index_of_isL2Quot (by omega : 2 ≤ 2 * k) hL2
  have hS' : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card S = Nat.card T :=
    fun T hT => hS.trans (hTcard T hT).symm
  obtain ⟨T, hT⟩ := isYAmalgam_of_isExtensionOfLieAmalgam hF.toW hL1' hL2' hZ hS' hE
  exact ⟨D, inferInstance, hD, T, hT⟩

end CFSG.Quasithin.Stroth
