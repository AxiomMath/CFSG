module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Rank2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem mem_commutator_of_comm_ch615 {Q : Type*} [Group Q] [Finite Q] {P A N : Subgroup Q}
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hA : IsPGroup 2 A)
    (hAP : A ≤ Subgroup.normalizer (P : Set Q)) (hPA : P ≤ ⁅P, A⁆) (hNP : N ≤ P)
    {x : Q} (hx : x ∈ N) (hodd : Odd (orderOf x)) : x ∈ ⁅N, A⁆ := by
  classical
  have : Fintype A := Fintype.ofFinite _
  have hcomm : IsMulCommutative ↥P := ⟨⟨fun a b => Subtype.ext (hPc a a.2 b b.2)⟩⟩
  let _ : CommGroup ↥P := .mk hcomm.is_comm.comm
  let c : ↥A → ↥P →* ↥P := fun a =>
    { toFun := fun y => ⟨(a : Q) * y * (a : Q)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAP a.2) y).mp y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp [mul_assoc] }
  have hc : ∀ a y, ((c a y : ↥P) : Q) = (a : Q) * y * (a : Q)⁻¹ := fun _ _ => rfl
  have hcc : ∀ a b y, c a (c b y) = c (a * b) y := fun a b y => by
    ext
    simp only [hc, Subgroup.coe_mul, mul_inv_rev]
    group
  let ν : ↥P →* ↥P := ∏ a : ↥A, c a
  have hν : ∀ y, ν y = ∏ a : ↥A, c a y := fun y => MonoidHom.finsetProd_apply _ _ _
  have hνc : ∀ b y, ν (c b y) = ν y := fun b y => by
    rw [hν, hν]
    simp_rw [hcc]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ (fun _ => rfl)
  have hker : ⁅P, A⁆ ≤ (ν.ker).map P.subtype := by
    rw [Subgroup.commutator_le]
    intro p hp a ha
    refine ⟨⟨p, hp⟩ * (c ⟨a, ha⟩ ⟨p, hp⟩)⁻¹, ?_, ?_⟩
    · show ν (_ * _) = 1
      rw [map_mul, map_inv, hνc, mul_inv_cancel]
    · simp [hc, commutatorElement_def, mul_assoc]
  have hν1 : ∀ y : ↥P, ν y = 1 := fun y => by
    obtain ⟨z, hz, hzy⟩ := hker (hPA y.2)
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz
  set x' : ↥P := ⟨x, hNP hx⟩ with hx'
  have hpow : x' ^ Fintype.card ↥A = ∏ a : ↥A, x' * (c a x')⁻¹ := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hν, hν1, inv_one, mul_one,
      Finset.prod_const, Finset.card_univ]
  have hmem : x' ^ Fintype.card ↥A ∈ (⁅N, A⁆).comap P.subtype := by
    rw [hpow]
    refine Subgroup.prod_mem _ fun a _ => ?_
    show (x : Q) * ((a : Q) * x * (a : Q)⁻¹)⁻¹ ∈ ⁅N, A⁆
    have e : (x : Q) * ((a : Q) * x * (a : Q)⁻¹)⁻¹ = ⁅x, (a : Q)⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hx a.2
  have hmem' : x ^ Fintype.card ↥A ∈ ⁅N, A⁆ := by
    have h1 := Subgroup.mem_comap.mp hmem
    rw [map_pow] at h1
    exact h1
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rw [Fintype.card_eq_nat_card, hk] at hmem'
  exact B6.mem_of_pow_mem_of_coprime hmem'
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))

theorem closure_eq_top_of_frattini_ch615 {Q : Type*} [Group Q] [Finite Q] {P N : Subgroup Q}
    (hN : N ≤ (frattini P).map P.subtype) {S : Set P}
    (h : ∀ k ∈ P, ∃ w ∈ Subgroup.closure (P.subtype '' S), w⁻¹ * k ∈ N) :
    Subgroup.closure S = ⊤ := by
  refine frattini_nongenerating (eq_top_iff.mpr fun k _ => ?_)
  obtain ⟨w, hw, hwk⟩ := h k k.2
  rw [← MonoidHom.map_closure] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  obtain ⟨n', hn', hnk⟩ := hN hwk
  have e : k = w' * n' := Subtype.ext (by
    rw [Subgroup.coe_mul]
    change (k : Q) = (w' : Q) * P.subtype n'
    rw [hnk, Subgroup.coe_subtype]
    group)
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw') (Subgroup.mem_sup_right hn')

theorem comm_of_frattini_zpowers_ch615 {P : Type*} [Group P] [Finite P] {w : P}
    (h : ∀ g : P, ∃ i : ℤ, (w ^ i)⁻¹ * g ∈ frattini P) : ∀ a b : P, a * b = b * a := by
  have htop : Subgroup.zpowers w = ⊤ := by
    refine frattini_nongenerating (eq_top_iff.mpr fun g _ => ?_)
    obtain ⟨i, hi⟩ := h g
    have e : g = w ^ i * ((w ^ i)⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers w i))
      (Subgroup.mem_sup_right hi)
  intro a b
  have ha : a ∈ Subgroup.zpowers w := htop ▸ Subgroup.mem_top a
  have hb : b ∈ Subgroup.zpowers w := htop ▸ Subgroup.mem_top b
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

theorem commutatorElement_central_mul_left_ch615 {P : Type*} [Group P] {f u v : P}
    (hf : ∀ k : P, f * k = k * f) : ⁅f * u, v⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc f * u * v * (f * u)⁻¹ * v⁻¹ = f * (u * v * u⁻¹) * f⁻¹ * v⁻¹ := by group
    _ = u * v * u⁻¹ * v⁻¹ := by rw [hf (u * v * u⁻¹), mul_inv_cancel_right]

theorem commutatorElement_mul_central_right_ch615 {P : Type*} [Group P] {f u v : P}
    (hf : ∀ k : P, f * k = k * f) : ⁅u, v * f⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc u * (v * f) * u⁻¹ * (v * f)⁻¹ = u * v * (f * u⁻¹) * f⁻¹ * v⁻¹ := by group
    _ = u * v * u⁻¹ * v⁻¹ := by rw [hf u⁻¹]; group

theorem commutatorElement_inv_left_ch615 {P : Type*} [Group P] {x y : P}
    (hz : ∀ k : P, ⁅x, y⁆ * k = k * ⁅x, y⁆) : ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
    rw [commutatorElement_def, commutatorElement_def]; group
  have hz' : ⁅x, y⁆⁻¹ * x = x * ⁅x, y⁆⁻¹ := by
    have := hz x⁻¹
    have h2 : (⁅x, y⁆ * x⁻¹)⁻¹ = (x⁻¹ * ⁅x, y⁆)⁻¹ := by rw [this]
    simpa [mul_inv_rev] using h2.symm
  rw [e, mul_assoc, hz', ← mul_assoc, inv_mul_cancel, one_mul]

theorem index_frattini_eq_nine_ch615 {P : Type} [Group P] [Finite P] (hP : IsPGroup 3 P)
    {x y : P} (hcl : Subgroup.closure {x, y} = ⊤) (hnc : ∃ g h : P, g * h ≠ h * g) :
    (frattini P).index = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  set F := frattini P with hF
  have hFn : F.Normal := inferInstance
  set mk := QuotientGroup.mk' F with hmk
  have hcommQ : ∀ a b : P ⧸ F, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    have hab : ⁅a, b⁆ ∈ F := CFSG.commutator_le_frattini_of_isPGroup (p := 3)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
    have h1 : mk ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hab
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hu3 : (mk x) ^ 3 = 1 := by
    rw [← map_pow, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact CFSG.pth_power_mem_frattini_of_isPGroup x
  have hv3 : (mk y) ^ 3 = 1 := by
    rw [← map_pow, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact CFSG.pth_power_mem_frattini_of_isPGroup y
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective F
  have hclQ : Subgroup.closure {mk x, mk y} = ⊤ := by
    have := congrArg (Subgroup.map mk) hcl
    rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top_of_surjective _ hsurj] at this
    exact this
  have hsup : (⊤ : Subgroup (P ⧸ F)) ≤ Subgroup.zpowers (mk x) ⊔ Subgroup.zpowers (mk y) := by
    rw [← hclQ, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hcard : Nat.card (P ⧸ F) ≤ 9 := by
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers (mk x))
      (Subgroup.zpowers (mk y)) (fun a _ b _ => hcommQ a b)).1
    have h1 : Nat.card (P ⧸ F) ≤ Nat.card ↥(Subgroup.zpowers (mk x) ⊔ Subgroup.zpowers (mk y)) :=
      by rw [← Subgroup.card_top (G := P ⧸ F)]; exact Subgroup.card_le_of_le hsup
    have h2 : Nat.card ↥(Subgroup.zpowers (mk x) ⊔ Subgroup.zpowers (mk y)) ≤
        Nat.card ↥(Subgroup.zpowers (mk x)) * Nat.card ↥(Subgroup.zpowers (mk y)) := by
      rw [← hc]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    rw [Nat.card_zpowers, Nat.card_zpowers] at h2
    have hu := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hu3)
    have hv := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hv3)
    nlinarith
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hdvd : F.index ∣ 3 ^ m := hm ▸ Subgroup.index_dvd_card F
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hidx : F.index = Nat.card (P ⧸ F) := Subgroup.index_eq_card F
  have hcyc : ∀ w : P, Subgroup.zpowers (mk w) = ⊤ → False := by
    intro w hw
    obtain ⟨g, h, hgh⟩ := hnc
    refine hgh (comm_of_frattini_zpowers_ch615 (w := w) (fun g => ?_) g h)
    have hg : mk g ∈ Subgroup.zpowers (mk w) := hw ▸ Subgroup.mem_top _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨i, ?_⟩
    rw [← map_zpow, hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hi
    exact hi
  have hle : j ≤ 2 := by
    by_contra hj2
    have : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases j
  ·
    exfalso
    have htop : F = ⊤ := Subgroup.index_eq_one.mp (by simpa using hj)
    exact hcyc 1 (by
      rw [map_one, Subgroup.zpowers_one_eq_bot, eq_top_iff]
      intro q _
      induction q using QuotientGroup.induction_on with
      | H q =>
        rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, htop]
        exact Subgroup.mem_top q)
  ·
    exfalso
    have h3 : Nat.card (P ⧸ F) = 3 := by rw [← hidx, hj]; norm_num
    by_cases hu : mk x = 1
    · have hv : mk y ≠ 1 := by
        intro hv
        have : (⊤ : Subgroup (P ⧸ F)) = ⊥ := by
          rw [← hclQ, hu, hv, Set.pair_eq_singleton, Subgroup.closure_singleton_one]
        have h1 := Subgroup.card_top (G := P ⧸ F)
        rw [this, Subgroup.card_bot, h3] at h1
        omega
      refine hcyc y (Subgroup.eq_top_of_card_eq _ ?_)
      rw [Nat.card_zpowers, h3]
      exact orderOf_eq_prime hv3 hv
    · refine hcyc x (Subgroup.eq_top_of_card_eq _ ?_)
      rw [Nat.card_zpowers, h3]
      exact orderOf_eq_prime hu3 hu
  · simpa using hj

theorem le_commutator_of_rankTwo_ch615 (hR : RankTwoThreeClassTwo) {Q : Type} [Group Q]
    [Finite Q] {P N A : Subgroup Q} [P.Normal] {p : ℕ} (hp : p.Prime) (hPp : IsPGroup p P)
    (hNΦ : N ≤ (frattini P).map P.subtype)
    (hm3 : ∀ E : Subgroup Q, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hnc : ∃ g ∈ P, ∃ h ∈ P, g * h ≠ h * g)
    {x y a s : Q} (hx : x ∈ P) (hy : y ∈ P) (ha : a ∈ A)
    (hxN : x ∉ N) (hx3 : x ^ 3 ∈ N) (hax : a * x * a⁻¹ * x ∈ N)
    (hay : y⁻¹ * (a * y * a⁻¹) ∈ N) (hsx : y⁻¹ * (s * x * s⁻¹) ∈ N)
    (hsy : x⁻¹ * (s * y * s⁻¹) ∈ N)
    (hgen : ∀ k ∈ P, ∃ w ∈ Subgroup.closure {x, y}, w⁻¹ * k ∈ N) :
    N ≤ ⁅N, A⁆ := by
  classical
  have hp3 : p = 3 := by
    by_contra hp3
    apply hxN
    obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime (orderOf x) 3 :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk')
        (Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_three).mpr hp3))
    exact B6.mem_of_pow_mem_of_coprime hx3 hcop
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hPp⟩
  have hmemΦ : ∀ g (hg : g ∈ P), g ∈ N → (⟨g, hg⟩ : P) ∈ frattini P := by
    intro g hg hgN
    obtain ⟨g', hg', hgg⟩ := hNΦ hgN
    have : g' = ⟨g, hg⟩ := Subtype.ext hgg
    rw [← this]
    exact hg'
  have hS : ∀ k ∈ P, ∃ w ∈ Subgroup.closure (P.subtype '' {⟨x, hx⟩, ⟨y, hy⟩}), w⁻¹ * k ∈ N := by
    rw [Set.image_pair]
    exact hgen
  have hcl : Subgroup.closure {(⟨x, hx⟩ : P), ⟨y, hy⟩} = ⊤ :=
    closure_eq_top_of_frattini_ch615 hNΦ hS
  have hnc' : ∃ g h : P, g * h ≠ h * g := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hnc
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hgh (congrArg Subtype.val e)⟩
  have hidx := index_frattini_eq_nine_ch615 hPp hcl hnc'
  have hm3' : ∀ E : Subgroup P, IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    have hE' : IsElemAbelian 3 (E.map P.subtype) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
        obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
        have := hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
        exact Subtype.ext (by simpa using congrArg (fun u : E => ((u : P) : Q)) this)
      · rintro _ ⟨e, he, rfl⟩
        have := hE.2 e he
        simpa using congrArg Subtype.val this
    have := hm3 _ hE'
    rwa [Subgroup.card_map_of_injective P.subtype_injective] at this
  have hσ : ∀ g : Q, ∀ u : P, ((MulAut.conjNormal g u : P) : Q) = g * u * g⁻¹ :=
    fun g u => MulAut.conjNormal_apply g u
  have h1 : (MulAut.conjNormal a) (⟨x, hx⟩ : P) * ⟨x, hx⟩ ∈ frattini P := by
    have e : (MulAut.conjNormal a) (⟨x, hx⟩ : P) * ⟨x, hx⟩ =
        ⟨a * x * a⁻¹ * x, P.mul_mem (‹P.Normal›.conj_mem x hx a) hx⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, hσ])
    rw [e]
    exact hmemΦ _ _ hax
  have h2 : (⟨y, hy⟩ : P)⁻¹ * (MulAut.conjNormal a) (⟨y, hy⟩ : P) ∈ frattini P := by
    have e : (⟨y, hy⟩ : P)⁻¹ * (MulAut.conjNormal a) (⟨y, hy⟩ : P) =
        ⟨y⁻¹ * (a * y * a⁻¹), P.mul_mem (P.inv_mem hy)
          (‹P.Normal›.conj_mem y hy a)⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, hσ]; rfl)
    rw [e]
    exact hmemΦ _ _ hay
  have h3 : (⟨y, hy⟩ : P)⁻¹ * (MulAut.conjNormal s) (⟨x, hx⟩ : P) ∈ frattini P := by
    have e : (⟨y, hy⟩ : P)⁻¹ * (MulAut.conjNormal s) (⟨x, hx⟩ : P) =
        ⟨y⁻¹ * (s * x * s⁻¹), P.mul_mem (P.inv_mem hy)
          (‹P.Normal›.conj_mem x hx s)⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, hσ]; rfl)
    rw [e]
    exact hmemΦ _ _ hsx
  have h4 : (⟨x, hx⟩ : P)⁻¹ * (MulAut.conjNormal s) (⟨y, hy⟩ : P) ∈ frattini P := by
    have e : (⟨x, hx⟩ : P)⁻¹ * (MulAut.conjNormal s) (⟨y, hy⟩ : P) =
        ⟨x⁻¹ * (s * y * s⁻¹), P.mul_mem (P.inv_mem hx)
          (‹P.Normal›.conj_mem y hy s)⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, hσ]; rfl)
    rw [e]
    exact hmemΦ _ _ hsy
  obtain ⟨hclass, hsmall⟩ := hR P hPp hidx hm3' ⟨x, hx⟩ ⟨y, hy⟩ hcl (MulAut.conjNormal a)
    (MulAut.conjNormal s) h1 h2 h3 h4
  obtain ⟨hcard, hexp⟩ := hsmall hnc'
  set z : P := ⁅(⟨x, hx⟩ : P), ⟨y, hy⟩⁆ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    obtain ⟨g, h, hgh⟩ := hnc'
    have hpair : ({(⟨x, hx⟩ : P), ⟨y, hy⟩} : Set P).Pairwise Commute := by
      rw [Set.pairwise_pair]
      intro _
      have hxy : (⟨x, hx⟩ : P) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
        commutatorElement_eq_one_iff_mul_comm.mp hz1
      exact ⟨hxy, hxy.symm⟩
    have := Subgroup.isMulCommutative_closure hpair
    rw [hcl] at this
    have hgh' := this.is_comm.comm ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩
    exact hgh (by simpa using congrArg Subtype.val hgh')
  have hzΦ : z ∈ frattini P := CFSG.commutator_le_frattini_of_isPGroup (p := 3)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hFcard : Nat.card (frattini P) = 3 := by
    have h := Subgroup.index_mul_card (frattini P)
    rw [hidx, hcard] at h
    omega
  have hz3 : z ^ 3 = 1 := hexp z
  have hFz : frattini P = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzΦ) ?_).symm
    rw [hFcard, Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
  have hzc : ∀ k : P, z * k = k * z := fun k =>
    commutatorElement_eq_one_iff_mul_comm.mp (hclass _ _ k)
  have hFc : ∀ f ∈ frattini P, ∀ k : P, f * k = k * f := by
    intro f hf k
    rw [hFz] at hf
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    exact ((Commute.zpow_left (hzc k) i))
  have hσz : MulAut.conjNormal a z = z⁻¹ := by
    have ex : MulAut.conjNormal a (⟨x, hx⟩ : P) =
        ((MulAut.conjNormal a) ⟨x, hx⟩ * ⟨x, hx⟩) * (⟨x, hx⟩ : P)⁻¹ := by group
    have ey : MulAut.conjNormal a (⟨y, hy⟩ : P) =
        (⟨y, hy⟩ : P) * ((⟨y, hy⟩ : P)⁻¹ * (MulAut.conjNormal a) ⟨y, hy⟩) := by group
    rw [hz, map_commutatorElement, ex, ey,
      commutatorElement_central_mul_left_ch615 (hFc _ h1),
      commutatorElement_mul_central_right_ch615 (hFc _ h2),
      commutatorElement_inv_left_ch615 hzc]
  have hazQ : a * (z : Q) * a⁻¹ = (z : Q)⁻¹ := by
    rw [← hσ, hσz]
    rfl
  have hNz : ∀ n ∈ N, ∃ i : ℤ, n = (z : Q) ^ i := by
    intro n hn
    obtain ⟨n', hn', rfl⟩ := hNΦ hn
    rw [hFz] at hn'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn'
    exact ⟨i, by simp⟩
  intro n hn
  by_cases hzN : (z : Q) ∈ N
  · have hc : ⁅(z : Q), a⁆ ∈ ⁅N, A⁆ := Subgroup.commutator_mem_commutator hzN ha
    have e : ⁅(z : Q), a⁆ = (z : Q) ^ 2 := by
      rw [commutatorElement_def]
      have : (z : Q) * a * (z : Q)⁻¹ * a⁻¹ = (z : Q) * (a * (z : Q) * a⁻¹)⁻¹ := by group
      rw [this, hazQ, inv_inv, sq]
    rw [e] at hc
    have hz3Q : (z : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hz3
    have hzmem : (z : Q) ∈ ⁅N, A⁆ := by
      have := Subgroup.pow_mem _ hc 2
      rwa [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_succ, hz3Q, one_mul] at this
    obtain ⟨i, rfl⟩ := hNz n hn
    exact Subgroup.zpow_mem _ hzmem i
  · obtain ⟨i, rfl⟩ := hNz n hn
    by_cases h1' : (z : Q) ^ i = 1
    · rw [h1']; exact Subgroup.one_mem _
    · exfalso
      apply hzN
      have hle : Subgroup.zpowers ((z : Q) ^ i) ≤ Subgroup.zpowers (z : Q) :=
        Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers _ i)
      have hoz : orderOf (z : Q) = 3 := by
        rw [Subgroup.orderOf_coe]; exact orderOf_eq_prime hz3 hz1
      have hcardz : Nat.card (Subgroup.zpowers ((z : Q) ^ i)) = 3 := by
        rw [Nat.card_zpowers]
        have hd : orderOf ((z : Q) ^ i) ∣ 3 := by
          rw [← hoz]; exact orderOf_dvd_of_pow_eq_one (by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
              pow_orderOf_eq_one, one_zpow])
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) h1'
        · exact h
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardz, Nat.card_zpowers, hoz])
      have hzz : (z : Q) ∈ Subgroup.zpowers ((z : Q) ^ i) := heq ▸ Subgroup.mem_zpowers _
      exact Subgroup.zpowers_le.mpr hn hzz

end CFSG.Quasithin.H13
