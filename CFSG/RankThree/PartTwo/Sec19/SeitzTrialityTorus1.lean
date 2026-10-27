module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.RankThree.PartOne.D4RC.Phi3
public import CFSG.RankThree.PartOne.D4RC.Phi6
import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTL3
import CFSG.RankThree.PartOne.D4RC.Lines
import CFSG.RankThree.PartOne.D4RC.Regular
import CFSG.RankThree.PartOne.D4RC.SylowSplit
import CFSG.RankThree.PartOne.D4RC.Gamma
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.RankThree.PartOne.SEITZ7.D4Final
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartOne.D4RC
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19

theorem exists_prime_dvd_cyclotomic_three (n : ℕ) (hn : 2 ≤ n) :
    ∃ (ε : ℤ) (p : ℕ), (ε = 1 ∨ ε = -1) ∧ p.Prime ∧ 5 ≤ p ∧
      (p : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1 ∧
      (3 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) - ε := by
  obtain ⟨ε, hε, hcong⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((2 ^ n : ℕ) : ℤ) ≡ ε [ZMOD 3] := by
    rcases Nat.even_or_odd n with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      have h1 : (2 : ℤ) ≡ -1 [ZMOD 3] := by decide
      have := h1.pow n
      rw [h.neg_one_pow] at this
      simpa using this
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have h1 : (2 : ℤ) ≡ -1 [ZMOD 3] := by decide
      have := h1.pow n
      rw [h.neg_one_pow] at this
      simpa using this
  have hpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1 := by
    have h4 : (4 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := by
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      exact_mod_cast (by omega : 4 ≤ 2 ^ n)
    rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1 :=
    ⟨_, Int.toNat_of_nonneg hpos⟩
  obtain ⟨-, ⟨p, hp, hp5, hpN⟩, -⟩ := TrialityArith.torus_arith (2 ^ n) n N ε hn rfl hε hcong hN
  exact ⟨ε, p, hε, hp, hp5, hN ▸ Int.natCast_dvd_natCast.mpr hpN, hcong.symm.dvd⟩

open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ7

section Generic

variable {G : Type*} [Group G]

theorem eq_top_of_two_factors (P : Fin 4 → Subgroup G) (hgen : (⨆ j, P j) = ⊤)
    (hrot : ∀ k, ∃ g ∈ P k, ∃ π : Equiv.Perm (Fin 4), π k = k ∧ (∀ j, j ≠ k → π j ≠ j) ∧
      ∀ j, (P j).map (MulAut.conj g).toMonoidHom = P (π j))
    {H : Subgroup G} {i j : Fin 4} (hij : i ≠ j) (hi : P i ≤ H) (hj : P j ≤ H) : H = ⊤ := by
  have hall : ∀ a : Fin 4, P a ≤ H := by
    intro a
    by_cases hai : a = i
    · rw [hai]; exact hi
    by_cases haj : a = j
    · rw [haj]; exact hj
    obtain ⟨g, hgP, π, hπi, hπmove, hconj⟩ := hrot i
    have hgH : g ∈ H := hi hgP
    have key : ∀ b, P b ≤ H → P (π b) ≤ H := by
      intro b hb
      rw [← hconj b]
      rintro _ ⟨y, hy, rfl⟩
      exact H.mul_mem (H.mul_mem hgH (hb hy)) (H.inv_mem hgH)
    have h3 : ∀ (π : Equiv.Perm (Fin 4)) (i j a : Fin 4), π i = i → (∀ v, v ≠ i → π v ≠ v) →
        j ≠ i → a ≠ i → a ≠ j → a = π j ∨ a = π (π j) := by decide
    rcases h3 π i j a hπi hπmove hij.symm hai haj with h | h
    · rw [h]; exact key j hj
    · rw [h]; exact key _ (key j hj)
  rw [eq_top_iff, ← hgen]
  exact iSup_le hall

theorem plane_of_two_commuting_prime_elements {p : ℕ} (hp : p.Prime) {y₁ y₂ : G}
    (h1 : y₁ ^ p = 1) (h1' : y₁ ≠ 1) (h2 : y₂ ^ p = 1) (h2' : y₂ ≠ 1) (hc : y₁ * y₂ = y₂ * y₁)
    (hne : Subgroup.zpowers y₁ ≠ Subgroup.zpowers y₂) :
    (∀ x ∈ Subgroup.closure ({y₁, y₂} : Set G), x ^ p = 1) ∧
      Nat.card (Subgroup.closure ({y₁, y₂} : Set G)) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := Subgroup.zpowers y₁ with hP
  set Q : Subgroup G := Subgroup.zpowers y₂ with hQ
  have hPc : Nat.card P = p := by rw [hP, Nat.card_zpowers, orderOf_eq_prime h1 h1']
  have hQc : Nat.card Q = p := by rw [hQ, Nat.card_zpowers, orderOf_eq_prime h2 h2']
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hPc]; exact hp.ne_zero)
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQc]; exact hp.ne_zero)
  have hdisj : Disjoint P Q := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(P ⊓ Q) ∣ p := by
      rw [← hPc]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hne
      have e1 : P ⊓ Q = P := Subgroup.eq_of_le_of_card_ge (inf_le_left) (by rw [h, hPc])
      have e2 : P ⊓ Q = Q := Subgroup.eq_of_le_of_card_ge (inf_le_right) (by rw [h, hQc])
      rw [← e1, e2]
  have hcomm : ∀ (m : P) (n : Q), Commute (P.subtype m) (Q.subtype n) := by
    intro m n
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp m.2
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp n.2
    show Commute (m : G) (n : G)
    rw [← ha, ← hb]
    exact (Commute.zpow_zpow (show Commute y₁ y₂ from hc) a b)
  set φ : P × Q →* G := MonoidHom.noncommCoprod P.subtype Q.subtype hcomm with hφ
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective P, Subgroup.subtype_injective Q, ?_⟩
    simpa [Subgroup.range_subtype] using hdisj
  have hrange : φ.range = Subgroup.closure ({y₁, y₂} : Set G) := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype,
      Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  constructor
  · intro x hx
    rw [← hrange] at hx
    obtain ⟨⟨u, v⟩, rfl⟩ := hx
    have hu : ((u : P) : G) ^ p = 1 := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp u.2
      rw [← ha, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
    have hv : ((v : Q) : G) ^ p = 1 := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp v.2
      rw [← ha, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
    rw [hφ, MonoidHom.noncommCoprod_apply]
    show ((u : G) * (v : G)) ^ p = 1
    rw [(show Commute (u : G) (v : G) from hcomm u v).mul_pow, hu, hv, mul_one]
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hPc, hQc]
    ring

end Generic

section RC

variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem exists_twistedEquiv_C0 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) :
    ∃ e : C0 σ ≃* twistedGroup σ.toRingHom,
      (∀ k : C0 σ, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 X) : ModGL d4 X) =
        ((k : C0 σ) : ModGL d4 X)) ∧
      Nat.card (twistedGroup σ.toRingHom) = CFSG.Open.ordTrialityD4 (2 ^ n) := by
  classical
  have : CharP X 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := n * 3) (by omega) (by rw [hX, pow_mul])
  set σ' : X →+* X := σ.toRingHom with hσ'def
  have hσq : ∀ c, σ' c = c ^ (2 ^ n) := hσ
  have hq2' : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hXD : Nat.card X = (2 ^ n) ^ TwistTag.D4.order := hX
  have hC0 : graphFixedRootGroup TwistTag.D4 X σ' =
      (twistedGroup σ').map (adjointGroup d4 X).subtype :=
    (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hn X hXD σ'
      hσq).2.2.1.symm.trans (commutator_twistedFixedGroup_eq_map σ' hq2' hX hσq)
  let eΓ : C0 σ ≃* twistedGroup σ' := (MulEquiv.subgroupCongr hC0).trans
    (Subgroup.equivMapOfInjective _ (adjointGroup d4 X).subtype
      (adjointGroup d4 X).subtype_injective).symm
  refine ⟨eΓ, ?_, ?_⟩
  · intro k
    let φ := Subgroup.equivMapOfInjective (twistedGroup σ') (adjointGroup d4 X).subtype
      (adjointGroup d4 X).subtype_injective
    set y := MulEquiv.subgroupCongr hC0 k with hy
    have h1 : φ (φ.symm y) = y := φ.apply_symm_apply y
    have h3 : ((φ (φ.symm y) : (twistedGroup σ').map (adjointGroup d4 X).subtype) : ModGL d4 X) =
        (((φ.symm y : twistedGroup σ') : adjointGroup d4 X) : ModGL d4 X) :=
      Subgroup.coe_equivMapOfInjective_apply _ _ _ _
    rw [h1] at h3
    exact h3.symm
  · rw [← Nat.card_congr eΓ.toEquiv]
    have := (triality_both_orientations_exact_finite_order 2 n Nat.prime_two hn X hX 1 (Or.inl rfl)
      σ' (fun c => by rw [pow_one]; exact hσq c)).1
    rw [this]
    unfold CFSG.Open.ordTrialityD4
    ring

theorem rce_conj_factor {ℓ f : ℕ} [Fact ℓ.Prime] {ε : ℤ} {p : ℕ} {L : Type} [Field L] [Algebra X L]
    [IsAlgClosure X L] [CharP L ℓ] {F : RclFrame ℓ f X σ ε p L} {S : Sylow p (C0 σ)} {c : C0 σ}
    {E : Subgroup (C0 σ)} (Ln : RceLines F S c E) [Fact p.Prime] {n : C0 σ}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup (C0 σ)) : Set (C0 σ))) (j : Fin 4) :
    (rclPx (Ln.sp j)).map (MulAut.conj n).toMonoidHom = rclPx (Ln.sp (rceIdx Ln n j)) := by
  have hmem := rceIdx_spec Ln hn j
  have h1 : n * Ln.x j * n⁻¹ ≠ 1 := fun h0 => (Ln.hx j).2 (by
    have : Ln.x j = n⁻¹ * (n * Ln.x j * n⁻¹) * n := by group
    rw [this, h0]
    group)
  have hC := rcr_centralizer_eq F.hp (Ln.hEp _ (Ln.hx (rceIdx Ln n j)).1)
    (Ln.hx (rceIdx Ln n j)).2 hmem h1
  rw [← rceR_eq_rclPx (Ln.sp j), ← rceR_eq_rclPx (Ln.sp (rceIdx Ln n j)), ← rceR_conj,
    rceR_congr hC]

theorem routeC_summary_perfect (n : ℕ) (hn : 2 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpd : (p : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1)
    (S : Sylow p (C0 σ)) (E : Subgroup (C0 σ)) (hES : E ≤ (S : Subgroup (C0 σ)))
    (hEp : ∀ y ∈ E, y ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ∃ (y : Fin 4 → C0 σ) (P : Fin 4 → Subgroup (C0 σ)),
      (∀ j, y j ∈ E ∧ y j ≠ 1) ∧
      (∀ j j', Subgroup.zpowers (y j) = Subgroup.zpowers (y j') → j = j') ∧
      (∀ j, P j ≤ Subgroup.centralizer {y j}) ∧
      (∀ e ∈ E, e ≠ 1 → Even (Nat.card (Subgroup.centralizer {e})) →
        ∃ j, e ∈ Subgroup.zpowers (y j)) ∧
      (⨆ j, P j) = ⊤ ∧
      (∀ k, ∃ g ∈ P k, ∃ π : Equiv.Perm (Fin 4), π k = k ∧ (∀ j, j ≠ k → π j ≠ j) ∧
        ∀ j, (P j).map (MulAut.conj g).toMonoidHom = P (π j)) ∧
      (∀ j, ⁅P j, P j⁆ = P j) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 ≤ n := by omega
  have hchar : CharP X 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := n * 3) (by omega) (by rw [hX, pow_mul])
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    have h := sigma_pow_three σ n hX hσ
    have := congrArg (fun τ : X ≃+* X => τ c) h
    simpa [pow_succ] using this
  let L := AlgebraicClosure X
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap X L).injective 2
  obtain ⟨F⟩ := rcl_exists_frame (ℓ := 2) (L := L) rfl hn1 hX hσ hε hp (by omega) hpd
  obtain ⟨e, hcompat, hT⟩ := exists_twistedEquiv_C0 σ n hn1 hX hσ
  haveI : Finite (twistedGroup σ.toRingHom) := Finite.of_equiv (C0 σ) e.toEquiv
  haveI := isSimpleGroup_C0 σ n hn1 hX hσ
  haveI : IsSimpleGroup (twistedGroup σ.toRingHom) := e.symm.isSimpleGroup
  have hgam : ∀ {S : Sylow p (C0 σ)} {c : C0 σ} {E : Subgroup (C0 σ)},
      ∀ (Ln : RceLines F S c E), rcgGamma Ln = ⊤ := by
    rcases hε with rfl | rfl
    · intro S c E Ln
      exact rc3_gamma_eq_top hσ3 hT e hcompat Ln
    · intro S c E Ln
      exact rc6_gamma_eq_top hσ3 hT e hcompat Ln
  obtain ⟨c, hc⟩ := F.hconj (S : Subgroup (C0 σ)) S.isPGroup'
  obtain ⟨Ln⟩ := rce_exists_lines F S hc hES hEp hEc
  refine ⟨fun j => Ln.x j, fun j => rclPx (Ln.sp j), fun j => Ln.hx j, ?_,
    fun j => rclPx_le_centralizer (Ln.sp j), ?_, hgam Ln, ?_,
    fun j => rcy_perfect_rclPx F (Ln.sp j)⟩
  · intro j j' h
    exact Ln.hinj j j' h
  · intro e' he' he1 hev
    rcases Ln.hcover e' he' he1 with h | ⟨b, hb, hker⟩
    · exact h
    · exfalso
      have hord : orderOf e' = p := orderOf_eq_prime (hEp e' he') he1
      exact (Nat.not_even_iff_odd.2 (rcr_odd_card_centralizer F hord hb hker)) hev
  · intro k
    obtain ⟨g, hgP, hgN, hk, hmove, -⟩ := rce_exists_rotation Ln k
    exact ⟨g, hgP, rcePerm Ln hgN, hk, hmove, fun j => rce_conj_factor σ Ln hgN j⟩

theorem exists_plane_in_sylow (n : ℕ) (hn : 2 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpd : (p : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) ^ 2 + ε * ((2 ^ n : ℕ) : ℤ) + 1)
    (S : Sylow p (C0 σ)) :
    ∃ E : Subgroup (C0 σ), E ≤ (S : Subgroup (C0 σ)) ∧ (∀ y ∈ E, y ^ p = 1) ∧
      Nat.card E = p ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hsh := CFSG.RankThree.PartOne.K128.sylowShape_D4_36 (ℓ := 2) (f := n) (by omega) X hX σ hσ
    hε hp (by omega) hpd
  have hd : p ∣ CFSG.RankThree.PartOne.KGD.d4T36d ε (2 ^ n) := by
    have h := CFSG.RankThree.PartOne.KGD.d4T36d_cast hε hq1
    have h2 : (p : ℤ) ∣ ((CFSG.RankThree.PartOne.KGD.d4T36d ε (2 ^ n) : ℕ) : ℤ) := by
      rw [h]; exact hpd
    exact_mod_cast h2
  have he : 1 ≤ (CFSG.RankThree.PartOne.KGD.d4T36d ε (2 ^ n)).factorization p :=
    hp.factorization_pos_of_dvd (CFSG.RankThree.PartOne.KGD.d4T36d_odd hε hq1).pos.ne' hd
  generalize (CFSG.RankThree.PartOne.KGD.d4T36d ε (2 ^ n)).factorization p = e at hsh he
  obtain ⟨φ⟩ := hsh (S : Subgroup (C0 σ)) S.isPGroup' S.not_dvd_index
  have hpe : p * p ^ (e - 1) = p ^ e := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨g, hg1, hgp⟩ : ∃ g : Multiplicative (ZMod (p ^ e)), g ≠ 1 ∧ g ^ p = 1 := by
    refine ⟨Multiplicative.ofAdd ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)), ?_, ?_⟩
    · intro h
      have h0 : ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa using this
      rw [ZMod.natCast_eq_zero_iff] at h0
      have h3 := Nat.le_of_dvd (pow_pos hp.pos _) h0
      have hlt : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
    · rw [← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, hpe, ZMod.natCast_self]
      rfl
  set w₁ : Fin 2 → Multiplicative (ZMod (p ^ e)) := Pi.mulSingle 0 g with hw₁d
  set w₂ : Fin 2 → Multiplicative (ZMod (p ^ e)) := Pi.mulSingle 1 g with hw₂d
  have hw₁ : w₁ ≠ 1 := fun h => hg1 (by simpa [hw₁d] using congrFun h 0)
  have hw₂ : w₂ ≠ 1 := fun h => hg1 (by simpa [hw₂d] using congrFun h 1)
  have hw₁p : w₁ ^ p = 1 := by rw [hw₁d, ← Pi.mulSingle_pow, hgp, Pi.mulSingle_one]
  have hw₂p : w₂ ^ p = 1 := by rw [hw₂d, ← Pi.mulSingle_pow, hgp, Pi.mulSingle_one]
  have hy₁T := (φ.symm w₁).2
  have hy₂T := (φ.symm w₂).2
  have hy₁p : ((φ.symm w₁ : (S : Subgroup (C0 σ))) : C0 σ) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hw₁p, map_one]; rfl
  have hy₂p : ((φ.symm w₂ : (S : Subgroup (C0 σ))) : C0 σ) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hw₂p, map_one]; rfl
  have hy₁1 : ((φ.symm w₁ : (S : Subgroup (C0 σ))) : C0 σ) ≠ 1 := fun h =>
    hw₁ (φ.symm.map_eq_one_iff.mp (Subtype.ext h))
  have hy₂1 : ((φ.symm w₂ : (S : Subgroup (C0 σ))) : C0 σ) ≠ 1 := fun h =>
    hw₂ (φ.symm.map_eq_one_iff.mp (Subtype.ext h))
  have hcomm : ((φ.symm w₁ : (S : Subgroup (C0 σ))) : C0 σ) * (φ.symm w₂ : C0 σ) =
      (φ.symm w₂ : C0 σ) * (φ.symm w₁ : C0 σ) := by
    have : φ.symm w₁ * φ.symm w₂ = φ.symm w₂ * φ.symm w₁ := by
      rw [← map_mul, ← map_mul, mul_comm]
    exact congrArg Subtype.val this
  have hne : Subgroup.zpowers ((φ.symm w₁ : (S : Subgroup (C0 σ))) : C0 σ) ≠
      Subgroup.zpowers ((φ.symm w₂ : (S : Subgroup (C0 σ))) : C0 σ) := by
    intro h
    have hmem : ((φ.symm w₂ : (S : Subgroup (C0 σ))) : C0 σ) ∈
        Subgroup.zpowers ((φ.symm w₁ : (S : Subgroup (C0 σ))) : C0 σ) := by
      rw [h]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 : (φ.symm w₁) ^ k = φ.symm w₂ := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
    rw [← map_zpow] at h2
    have h3 := φ.symm.injective h2
    have h4 : (w₁ ^ k) 1 = w₂ 1 := congrFun h3 1
    simp [hw₁d, hw₂d] at h4
    exact hg1 h4.symm
  obtain ⟨hpow, hcard⟩ := plane_of_two_commuting_prime_elements hp hy₁p hy₁1 hy₂p hy₂1 hcomm hne
  refine ⟨Subgroup.closure {((φ.symm w₁ : (S : Subgroup (C0 σ))) : C0 σ),
    ((φ.symm w₂ : (S : Subgroup (C0 σ))) : C0 σ)}, ?_, hpow, hcard⟩
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · exact hy₁T
  · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hy₂T

end RC

end CFSG.RankThree.PartTwo.Sec19
