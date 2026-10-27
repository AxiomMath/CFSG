module

public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.S1567ASymm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L3312.NQ

open CFSG.Open CFSG.QuasithinUnique
open CFSG.SectionRank.Ccomm (frattiniAction)

theorem pRank_le_two {q : ℕ} [hq : Fact q.Prime] {R : Type} [Group R] [Finite R]
    (h : ∀ E : Subgroup R, CFSG.Open.IsElemAbelian q E → Nat.card E ≤ q ^ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup R) ≤ 2 := by
  apply csSup_le'
  intro k hk
  obtain ⟨E, -, hrest⟩ := hk
  have hEk : Nat.card E = q ^ k := hrest.2
  have := h E hrest.1
  rw [hEk] at this
  exact (Nat.pow_le_pow_iff_right hq.out.one_lt).mp this

theorem card_le_of_isPOnePlusTwo {q : ℕ} [hq : Fact q.Prime] {R : Type} [Group R] [Finite R]
    (hR : IsPOnePlusTwo q R) (E : Subgroup R) (hE : CFSG.Open.IsElemAbelian q E) :
    Nat.card E ≤ q ^ 2 := by
  obtain ⟨hex, hcard, -⟩ := hR
  have hRp : IsPGroup q R := IsPGroup.of_card hcard
  obtain ⟨k, hk⟩ := (hRp.to_subgroup E).exists_card_eq
  have hk3 : k ≤ 3 := by
    have := Subgroup.card_le_card_group E
    rw [hk, hcard] at this
    exact (Nat.pow_le_pow_iff_right hq.out.one_lt).mp this
  rw [hk]
  by_contra hlt
  have hk3' : k = 3 := by
    have : 2 < k := by
      by_contra h2
      exact hlt (Nat.pow_le_pow_right hq.out.pos (by omega))
    omega
  have htop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [hk, hk3', hcard])
  have hcomm : ∀ a b : R, a * b = b * a := fun a b => by
    have hab := hE.1.is_comm.comm (⟨a, htop ▸ Subgroup.mem_top a⟩ : ↥E)
      ⟨b, htop ▸ Subgroup.mem_top b⟩
    exact congrArg Subtype.val hab
  have hcen : Subgroup.center R = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcomm g x
  have h1 := hex.center_order_p
  rw [hcen, Subgroup.card_top, hcard] at h1
  have : q ^ 3 = q ^ 1 := by rw [h1, pow_one]
  have := Nat.pow_right_injective hq.out.two_le this
  omega

theorem card_le_of_homocyclic {q : ℕ} [hq : Fact q.Prime] {R : Type} [Group R] [Finite R]
    (hR : IsHomocyclicRank2 q R) (E : Subgroup R) (hE : CFSG.Open.IsElemAbelian q E) :
    Nat.card E ≤ q ^ 2 := by
  classical
  obtain ⟨n, hn, ⟨e⟩⟩ := hR
  set C := Multiplicative (ZMod (q ^ n)) with hC
  have : NeZero (q ^ n) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  have hcyc : ∀ (S : Finset C), (∀ x ∈ S, x ^ q = 1) → S.card ≤ q := by
    intro S hS
    calc S.card ≤ (Finset.univ.filter fun x : C => x ^ q = 1).card :=
          Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hx⟩
      _ ≤ q := IsCyclic.card_pow_eq_one_le hq.out.pos
  let f : ↥E → {x : C // x ^ q = 1} × {x : C // x ^ q = 1} := fun x =>
    (⟨(e x).1, by
      have h1 := congrArg (fun y => (e y).1) (hE.2 x x.2)
      simpa using h1⟩, ⟨(e x).2, by
      have h1 := congrArg (fun y => (e y).2) (hE.2 x x.2)
      simpa using h1⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (congrArg (fun t => (t.1 : C)) hxy) (congrArg (fun t => (t.2 : C)) hxy)
  have hsub : Nat.card {x : C // x ^ q = 1} ≤ q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hq.out.pos
  calc Nat.card E ≤ Nat.card ({x : C // x ^ q = 1} × {x : C // x ^ q = 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card {x : C // x ^ q = 1} * Nat.card {x : C // x ^ q = 1} := Nat.card_prod _ _
    _ ≤ q * q := Nat.mul_le_mul hsub hsub
    _ = q ^ 2 := (sq q).symm

variable {Q : Type} [Group Q] [Finite Q]

theorem pRank_pCore_le_two (hcase : A36Case3 Q ∨ A36Case4 Q) {q : ℕ} [hq : Fact q.Prime]
    (hqF : q ∣ Nat.card (CFSG.fittingSubgroup Q)) :
    CFSG.Open.pRank q (⊤ : Subgroup ↥(CFSG.pCore q Q)) ≤ 2 := by
  rcases hcase with ⟨p, hp, -, -, ⟨e⟩, -⟩ | ⟨-, -, -, h4⟩
  · have hFc : Nat.card (CFSG.fittingSubgroup Q) = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      show Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hqp : q = p := by
      rw [hFc] at hqF
      exact (Nat.prime_dvd_prime_iff_eq hq.out hp).mp (hq.out.dvd_of_dvd_pow hqF)
    subst hqp
    refine pRank_le_two fun E _ => ?_
    calc Nat.card E ≤ Nat.card ↥(CFSG.pCore q Q) := Subgroup.card_le_card_group E
      _ ≤ Nat.card (CFSG.fittingSubgroup Q) := Subgroup.card_le_of_le (CFSG.pCore_le_fitting Q q)
      _ = q ^ 2 := hFc
  · rcases (h4 q hq.out hqF).2 with h | h
    · exact pRank_le_two fun E hE => card_le_of_isPOnePlusTwo h E hE
    · exact pRank_le_two fun E hE => card_le_of_homocyclic h E hE

theorem le_pCore_of_le_fitting {q : ℕ} [Fact q.Prime] {X : Subgroup Q}
    (hXF : X ≤ CFSG.fittingSubgroup Q) (hX : IsPGroup q X) : X ≤ CFSG.pCore q Q := by
  set F := CFSG.fittingSubgroup Q with hF
  have hX' : IsPGroup q ↥(X.subgroupOf F) := hX.comap_of_injective F.subtype F.subtype_injective
  obtain ⟨P, hP⟩ := hX'.exists_le_sylow
  rw [← Subgroup.map_subgroupOf_eq_of_le hXF]
  exact (Subgroup.map_mono hP).trans
    (Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent q P)

omit [Finite Q] in
theorem odd_card_oddCore [Finite Q] : Odd (Nat.card (CFSG.oddCore Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : CFSG.oddCore Q = CFSG.pPrimeCore 2 Q := by
    unfold CFSG.oddCore CFSG.pPrimeCore
    simp_rw [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem isPGroup_ker_frattiniAction {q : ℕ} [hq : Fact q.Prime] {R : Type} [Group R] [Finite R]
    {P : Subgroup R} [P.Characteristic]
    (hPfaith : ∀ α : MulAut R, (orderOf α).Coprime q → (∀ x ∈ P, x⁻¹ * α x ∈ frattiniIn P) →
      α = 1) : IsPGroup q (frattiniAction P).ker := by
  rintro ⟨α, hα⟩
  have hne : orderOf α ≠ 0 := (orderOf_pos α).ne'
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne q hq.out.ne_one
  have hβker : α ^ q ^ a ∈ (frattiniAction P).ker := Subgroup.pow_mem _ hα _
  have hβ : (orderOf (α ^ q ^ a)).Coprime q := by
    have hdvd : orderOf (α ^ q ^ a) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, ← hom, pow_orderOf_eq_one]
    exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd hq.out).mpr hm)))
  have h1 := hPfaith _ hβ ((mem_ker_frattiniAction_iff P _).mp hβker)
  exact ⟨a, Subtype.ext (by simpa using h1)⟩

theorem inv_frattini (hcomm : A36Common Q) (hcase : A36Case3 Q ∨ A36Case4 Q) {H : Subgroup Q}
    [Group.IsPerfect ↥H] {z : Q} (hzH : z ∈ H) (hz2 : z * z = 1)
    (hzF : z ∉ CFSG.fittingSubgroup Q) {q : ℕ} [hq : Fact q.Prime]
    (hqF : q ∣ Nat.card (CFSG.fittingSubgroup Q)) {P : Subgroup ↥(CFSG.pCore q Q)}
    (hPs : IsSupercritical q P)
    (hPfaith : ∀ α : MulAut ↥(CFSG.pCore q Q), (orderOf α).Coprime q →
      (∀ x ∈ P, x⁻¹ * α x ∈ frattiniIn P) → α = 1)
    (hPiff : ∀ x : Q, ActsTriviallyOnFrattiniQuotient (P.map (CFSG.pCore q Q).subtype) x ↔
      x ∈ CFSG.fittingSubgroup Q) :
    ∀ d ∈ P, d * (MulAut.conjNormal z : MulAut ↥(CFSG.pCore q Q)) d ∈ frattiniIn P := by
  have := hPs.characteristic
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hodd := odd_card_oddCore (Q := Q)
    rw [← hcomm.1] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqF)
  have hker := isPGroup_ker_frattiniAction (P := P) hPfaith
  set αH : ↥H →* MulAut ↥(CFSG.pCore q Q) :=
    (MulAut.conjNormal : Q →* MulAut ↥(CFSG.pCore q Q)).comp H.subtype with hαH
  have hρz : frattiniAction P (MulAut.conjNormal z : MulAut ↥(CFSG.pCore q Q)) ≠ 1 := by
    intro h1
    apply hzF
    rw [← hPiff, ← A36B.mem_ker_frattiniAction_conjNormal (CFSG.pCore q Q) P z, MonoidHom.mem_ker,
      MonoidHom.comp_apply]
    exact h1
  have hα : αH ≠ 1 := by
    intro h1
    apply hρz
    have : αH ⟨z, hzH⟩ = 1 := by rw [h1]; rfl
    rw [show αH ⟨z, hzH⟩ = MulAut.conjNormal z from rfl] at this
    rw [this, map_one]
  obtain ⟨-, -, hinv, -⟩ := A36B.action_frattini_quotient hq2 CFSG.pCore_isPGroup
    (pRank_pCore_le_two hcase hqF) P hPs.pow_eq_one hker αH hα ((frattiniAction P).comp αH) rfl
  have hzz : (⟨z, hzH⟩ : ↥H) * ⟨z, hzH⟩ = 1 := Subtype.ext hz2
  have hw := hinv ⟨z, hzH⟩ (by rw [← map_mul, hzz, map_one]) hρz
  intro d hd
  have h1 := hw ((⟨d, hd⟩ : ↥P) : ↥P ⧸ frattini ↥P)
  change frattiniAction P (MulAut.conjNormal z) ((⟨d, hd⟩ : ↥P) : ↥P ⧸ frattini ↥P) = _ at h1
  rw [CFSG.SectionRank.Ccomm.frattiniAction_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq] at h1
  refine ⟨_, (frattini ↥P).inv_mem h1, ?_⟩
  simp [mul_inv_rev]

omit [Finite Q] in
theorem mem_of_sq_mem_of_odd {X : Type} [Group X] [Finite X] {S : Subgroup X} {w : X}
    (hw : w * w ∈ S) (hodd : Odd (orderOf w)) : w ∈ S := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : w = (w * w) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    calc w = w ^ (2 * k + 1) * w := by rw [← hk, pow_orderOf_eq_one, one_mul]
      _ = w ^ (2 * (k + 1)) := by rw [← pow_succ]; ring_nf
  rw [h1]
  exact S.pow_mem hw _

omit [Finite Q] in
theorem mulAut_comm_of_isCyclic {X : Type} [Group X] [IsCyclic X] (σ τ : MulAut X) :
    σ * τ = τ * σ := by
  apply (IsCyclic.mulAutMulEquiv X).injective
  rw [map_mul, map_mul, mul_comm]

theorem le_centralizer_of_pCore (hcomm : A36Common Q) (hcase : A36Case3 Q ∨ A36Case4 Q)
    (hext : A36Extra Q) {H : Subgroup Q} [Group.IsPerfect ↥H] {z : Q} (hzH : z ∈ H)
    (hz2 : z * z = 1) (hzF : z ∉ CFSG.fittingSubgroup Q) {q : ℕ} [hq : Fact q.Prime] {y : Q}
    (hy : y ∈ CFSG.pCore q Q) (hyz : y * z = z * y) :
    y ∈ Subgroup.centralizer (H : Set Q) := by
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  have hRp : IsPGroup q ↥(CFSG.pCore q Q) := CFSG.pCore_isPGroup
  set yR : ↥(CFSG.pCore q Q) := ⟨y, hy⟩ with hyRdef
  have hyR1 : yR ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hqR : q ∣ Nat.card ↥(CFSG.pCore q Q) := by
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have : Subsingleton ↥(CFSG.pCore q Q) := (Nat.card_eq_one_iff_unique.mp hk).1
      exact hyR1 (Subsingleton.elim _ _)
    rw [hk]
    exact dvd_pow_self q hk0
  have hqF : q ∣ Nat.card (CFSG.fittingSubgroup Q) :=
    hqR.trans (Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting Q q))
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hodd := odd_card_oddCore (Q := Q)
    rw [← hcomm.1] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqF)
  obtain ⟨P, hPs, hPfaith, hPiso, hPiff⟩ := hext q hq.out hqF
  have hinv := inv_frattini hcomm hcase hzH hz2 hzF hqF hPs hPfaith hPiff
  have hconj : ∀ n : ℤ, (MulAut.conjNormal z : MulAut ↥(CFSG.pCore q Q)) (yR ^ n) = yR ^ n := by
    intro n
    rw [map_zpow]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show z * y * z⁻¹ = y
    rw [← hyz, mul_inv_cancel_right]
  have hodd : ∀ w : ↥(CFSG.pCore q Q), Odd (orderOf w) := fun w => by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hRp w
    rw [hk]
    exact Odd.pow (hq.out.odd_of_ne_two hq2)
  have hstruct : (∀ a b : ↥(CFSG.pCore q Q), a * b = b * a) ∨
      IsPOnePlusTwo q ↥(CFSG.pCore q Q) := by
    rcases hcase with ⟨p, -, -, -, ⟨e⟩, -⟩ | ⟨-, -, -, h4⟩
    · left
      intro a b
      have hle := CFSG.pCore_le_fitting Q q
      have hF : ∀ c d : ↥(CFSG.fittingSubgroup Q), c * d = d * c := fun c d =>
        e.injective (by rw [map_mul, map_mul, mul_comm])
      exact Subtype.ext (show (a : Q) * b = b * a from
        congrArg Subtype.val (hF ⟨a, hle a.2⟩ ⟨b, hle b.2⟩))
    · rcases (h4 q hq.out hqF).2 with h | ⟨n, -, ⟨e⟩⟩
      · exact Or.inr h
      · left
        intro a b
        exact e.injective (by rw [map_mul, map_mul, mul_comm])
  rcases hstruct with hab | hex
  ·
    exfalso
    have hq' : q ∣ Nat.card ↥(Subgroup.zpowers yR) := by
      rw [Nat.card_zpowers]
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hRp yR
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact hyR1 hk
      rw [hk]
      exact dvd_pow_self q hk0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hq'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    have hwq : orderOf (x : ↥(CFSG.pCore q Q)) = q := by rw [Subgroup.orderOf_coe, hx]
    have hwP : (x : ↥(CFSG.pCore q Q)) ∈ P := hPs.mem_of_orderOf_eq _
      (Subgroup.mem_centralizer_iff.mpr fun d _ => hab d _) hwq
    have hcw : (MulAut.conjNormal z : MulAut ↥(CFSG.pCore q Q)) (x : ↥(CFSG.pCore q Q)) =
        (x : ↥(CFSG.pCore q Q)) := by
      rw [← hn, hconj n]
    have h1 := hinv _ hwP
    rw [hcw] at h1
    have h2 := mem_of_sq_mem_of_odd h1 (hodd _)
    have : Fact (IsPGroup q ↥P) := ⟨hRp.to_subgroup P⟩
    have : IsElementaryAbelian q ↥P :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hab a b)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (hPs.pow_eq_one a a.2) }
    have hΦ : frattiniIn P = ⊥ := by
      rw [frattiniIn, frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
    rw [hΦ, Subgroup.mem_bot] at h2
    rw [h2, orderOf_one] at hwq
    exact hq.out.one_lt.ne hwq
  ·
    obtain ⟨hexs, hcardR, -⟩ := hex
    have hPtop : P = ⊤ := by
      rcases hPiso with hPel | ⟨-, hcardP, -⟩
      · exfalso
        obtain ⟨eP⟩ := hPel
        have hPab : ∀ a b : ↥P, a * b = b * a := fun a b =>
          eP.injective (by rw [map_mul, map_mul, mul_comm])
        have : Fact (IsPGroup q ↥P) := ⟨hRp.to_subgroup P⟩
        have : IsElementaryAbelian q ↥P :=
          { toIsMulCommutative := ⟨⟨hPab⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
              Subtype.ext (hPs.pow_eq_one a a.2) }
        have hΦ : frattiniIn P = ⊥ := by
          rw [frattiniIn, frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
        have hcen : P ≤ Subgroup.center ↥(CFSG.pCore q Q) := by
          intro d hd
          rw [Subgroup.mem_center_iff]
          intro r
          have hrF : (r : Q) ∈ CFSG.fittingSubgroup Q := CFSG.pCore_le_fitting Q q r.2
          have h1 := (hPiff r).mpr hrF (d : Q) ⟨d, hd, rfl⟩
          rw [A36B.frattiniIn_map_subtype, hΦ, Subgroup.map_bot, Subgroup.mem_bot,
            inv_mul_eq_one] at h1
          apply Subtype.ext
          show (r : Q) * d = d * r
          calc (r : Q) * d = (r : Q) * d * (r : Q)⁻¹ * r := by group
            _ = d * r := by rw [← h1]
        have hcard := Subgroup.card_le_of_le hcen
        rw [hexs.center_order_p, Nat.card_congr eP.toEquiv] at hcard
        have : Nat.card (Multiplicative (Fin 2 → ZMod q)) = q ^ 2 := by
          show Nat.card (Fin 2 → ZMod q) = q ^ 2
          rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
        rw [this] at hcard
        have h2 : q ^ 2 ≤ q ^ 1 := by rwa [pow_one]
        have := (Nat.pow_le_pow_iff_right hq.out.one_lt).mp h2
        omega
      · exact Subgroup.eq_top_of_card_eq P (by rw [hcardP, hcardR])
    have hyP : yR ∈ P := by
      rw [hPtop]
      exact Subgroup.mem_top _
    have h1 := hinv yR hyP
    have hc1 := hconj 1
    rw [zpow_one] at hc1
    rw [hc1] at h1
    have h2 := mem_of_sq_mem_of_odd (hPs.frattini_le h1) (hodd yR)
    have hyZ : yR ∈ Subgroup.center ↥(CFSG.pCore q Q) := by
      rw [Subgroup.mem_center_iff]
      intro r
      have hr : r ∈ P := by
        rw [hPtop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_centralizer_iff.mp h2.2 r hr)
    have hcyc : IsCyclic ↥(Subgroup.center ↥(CFSG.pCore q Q)) := by
      have : Fact (Nat.card ↥(Subgroup.center ↥(CFSG.pCore q Q))).Prime := by
        rw [hexs.center_order_p]
        exact hq
      exact isCyclic_of_prime_card rfl
    set φ : ↥H →* MulAut ↥(Subgroup.center ↥(CFSG.pCore q Q)) :=
      (MulAut.characteristic (Subgroup.center ↥(CFSG.pCore q Q))).comp
        ((MulAut.conjNormal : Q →* MulAut ↥(CFSG.pCore q Q)).comp H.subtype) with hφ
    have hφ1 : φ = 1 := CFSG.SectionRank.Ccomm.perfect_hom_eq_one_of_range_comm φ
      fun a _ b _ => mulAut_comm_of_isCyclic a b
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h3 := congrArg (fun ψ : MulAut ↥(Subgroup.center ↥(CFSG.pCore q Q)) =>
      ((ψ ⟨yR, hyZ⟩ : ↥(Subgroup.center ↥(CFSG.pCore q Q))) : Q)) (congrArg (· ⟨h, hh⟩) hφ1)
    simp only [hφ, MonoidHom.comp_apply, MonoidHom.one_apply, MulAut.one_apply] at h3
    have h4 : h * y * h⁻¹ = y := h3
    calc h * y = h * y * h⁻¹ * h := by group
      _ = y * h := by rw [h4]

theorem le_centralizer_of_fitting (hcomm : A36Common Q) (hcase : A36Case3 Q ∨ A36Case4 Q)
    (hext : A36Extra Q) {H : Subgroup Q} [Group.IsPerfect ↥H] {z : Q} (hzH : z ∈ H)
    (hz2 : z * z = 1) (hzF : z ∉ CFSG.fittingSubgroup Q) :
    CFSG.fittingSubgroup Q ⊓ Subgroup.centralizer ({z} : Set Q) ≤
      Subgroup.centralizer (H : Set Q) := by
  set E := CFSG.fittingSubgroup Q ⊓ Subgroup.centralizer ({z} : Set Q) with hE
  have htop : (Subgroup.centralizer (H : Set Q)).subgroupOf E = ⊤ := by
    apply CFSG.GroupTheory.WielandtProduct.eq_top_of_forall_sylow_le
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨P⟩ : Nonempty (Sylow q ↥E) := inferInstance
    refine ⟨P, fun x hx => ?_⟩
    have hPF : (P : Subgroup ↥E).map E.subtype ≤ CFSG.fittingSubgroup Q :=
      (Subgroup.map_subtype_le _).trans inf_le_left
    have hPq : IsPGroup q ↥((P : Subgroup ↥E).map E.subtype) := P.isPGroup'.map E.subtype
    have hxR : (x : Q) ∈ CFSG.pCore q Q := le_pCore_of_le_fitting hPF hPq ⟨x, hx, rfl⟩
    have hxz : (x : Q) * z = z * x :=
      Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    exact Subgroup.mem_subgroupOf.mpr (le_centralizer_of_pCore hcomm hcase hext hzH hz2 hzF hxR hxz)
  intro x hx
  have : (⟨x, hx⟩ : ↥E) ∈ (Subgroup.centralizer (H : Set Q)).subgroupOf E := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end CFSG.Quasithin.H13.L3312.NQ
