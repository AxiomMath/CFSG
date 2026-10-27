module

public import CFSG.Quasithin.EmptyFaithful.E111L2OA
public import CFSG.Quasithin.EmptyFaithful.E22QTorus
public import CFSG.Quasithin.EmptyFaithful.E22PTor
public import CFSG.Quasithin.EmptyFaithful.E111L2D

public section

namespace CFSG.Quasithin.E2.E22N.E111L

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_commutator_of_inv {r : ℕ} (hr : Odd r) {P A : Subgroup G} (hP : IsPGroup r P)
    {w : G} (hw : w ∈ A) (hwinv : ∀ x ∈ P, w * x * w⁻¹ = x⁻¹) : P ≤ ⁅P, A⁆ := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := CFSG.Quasithin.E22L2.e22ptor_exists_sq hr hk'
  have hxj : x ^ j ∈ P := P.pow_mem hx j
  have h1 : ⁅x ^ j, w⁆ = x := by
    have h2 := hwinv (x ^ j) hxj
    have h3 : ⁅x ^ j, w⁆ = x ^ j * (w * x ^ j * w⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h3, h2, inv_inv, ← sq]
    exact hj
  rw [← h1]
  exact Subgroup.commutator_mem_commutator hxj hw

theorem conjSub_conjSub_comm {a k : G} (hak : a * k = k * a) (H : Subgroup G) :
    A1b.conjSub a (A1b.conjSub k H) = A1b.conjSub k (A1b.conjSub a H) := by
  rw [← A1b.conjSub_mul, ← A1b.conjSub_mul, hak]

section Outer

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem outer_member (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {X T A S : Subgroup G}
    (hR : E111Reduced G X T) (hQ : ∀ S' : Subgroup G, IsComp X S' → IsPSL 2 p 1 ↥S')
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hS : IsComp X S)
    (h4 : 4 ≤ (A ⊓ Subgroup.centralizer (S : Set G)).relIndex
      (A ⊓ Subgroup.normalizer (S : Set G)))
    (hout : ∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∀ s ∈ S,
      s⁻¹ * a ∉ Subgroup.centralizer (S : Set G))
    {z : G} (hz : z ∈ T ⊓ S) (hz2 : orderOf z = 2) (hzc : ∀ x ∈ T ⊓ S, z * x = x * z) :
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧
      ∃ g ∈ K, g ∈ Subgroup.normalizer (S : Set G) ∧ g * z ≠ z * g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := A ⊓ Subgroup.normalizer (S : Set G) with hVdef
  set V₀ := A ⊓ Subgroup.centralizer (S : Set G) with hV₀def
  have hV₀V : V₀ ≤ V :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_le hA inf_le_left
  obtain ⟨C, hCA, hCV, hCVA⟩ := exists_compl hA (inf_le_left : V ≤ A)
  have h : DiagSetting X T A S C := ⟨hR, hAT, hA, hS, hCA, hCV⟩
  let _ : Fintype ↥C := Fintype.ofFinite _
  set δ := diagHom S C h.diagComm with hδ
  have hinj : Function.Injective δ := diagHom_injective h.diagComm h.center_trivial
  set D := diagSub S C h.diagComm with hD
  have hDp : IsPSL 2 p 1 ↥D := isoInv_isPSL_two p _ _ h.diagEquiv.symm (hQ S hS)
  obtain ⟨A₁, hA₁V, hA₁V₀, hA₁V₀V⟩ := exists_compl hVe hV₀V
  have hA₁A : A₁ ≤ A := hA₁V.trans inf_le_left
  have hA₁e : IsElemAbelian 2 A₁ := isElemAbelian_of_le hA hA₁A
  have hA₁4 : 4 ≤ Nat.card A₁ := by
    have e1 := card_sup_of_comm hA hA₁A (hV₀V.trans inf_le_left) hA₁V₀
    rw [hA₁V₀V] at e1
    have e2 := card_mul_relIndex' hV₀V
    have hV₀p : 0 < Nat.card V₀ := Nat.card_pos
    have e3 : Nat.card V₀ * V₀.relIndex V = Nat.card V₀ * Nat.card A₁ := by
      rw [e2, e1, mul_comm]
    have e4 := Nat.eq_of_mul_eq_mul_left hV₀p e3
    omega
  have hAN : A ≤ Subgroup.normalizer (D : Set G) := h.le_normalizer_diag hCVA
  have hCD : C ≤ Subgroup.centralizer (D : Set G) := h.le_centralizer_diag
  have hV₀D : V₀ ≤ Subgroup.centralizer (D : Set G) := fun v hv =>
    h.le_centralizer_diag_of_le (hV₀V hv) hv.2
  set Q : Subgroup G := D ⊔ (T ⊓ Subgroup.normalizer (D : Set G)) with hQdef
  have hQN : Q ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer inf_le_right
  have hDQ : D ≤ Q := le_sup_left
  have hDn : (D.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr hQN
  have hT2 : IsPGroup 2 T := h.isPGroup_T
  have hTQ : IsSylowIn 2 (T ⊓ Q) Q :=
    isSylowIn_inf_sup hT2 inf_le_left inf_le_right h.isSylowIn_diag
  have hA₁Q : A₁ ≤ Q := fun a ha => Subgroup.mem_sup_right ⟨hAT (hA₁A ha), hAN (hA₁A ha)⟩
  have hAC : ∀ a ∈ A₁, a ∈ Subgroup.centralizer (D : Set G) → a = 1 := by
    intro a ha hac
    have haS := mem_centralizer_of_centralizer_diag h (hA₁V ha) hac
    have : a ∈ A₁ ⊓ V₀ := ⟨ha, hA₁A ha, haS⟩
    rw [hA₁V₀] at this
    exact this
  have hAD : ∃ a ∈ A₁, ∀ y ∈ D, ∀ y₀ ∈ Subgroup.centralizer (D : Set G), a ≠ y * y₀ := by
    obtain ⟨a₀, ha₀V, ha₀⟩ := hout
    have ha₀' : a₀ ∈ A₁ ⊔ V₀ := hA₁V₀V ▸ ha₀V
    have hV₀N : V₀ ≤ Subgroup.normalizer (A₁ : Set G) := le_normalizer_of_comm fun x hx y hy =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hA₁A hy⟩)
    obtain ⟨a₁, ha₁, v₀, hv₀, rfl⟩ := exists_mul_of_mem_sup hV₀N ha₀'
    refine ⟨a₁, ha₁, fun y hy y₀ hy₀ hay => ?_⟩
    obtain ⟨s, hs, hsc⟩ := inner_of_mem_diag_mul h (hA₁V ha₁) hy hy₀ hay
    apply ha₀ s hs
    have : s⁻¹ * (a₁ * v₀) = (s⁻¹ * a₁) * v₀ := by group
    rw [this]
    exact Subgroup.mul_mem _ hsc hv₀.2
  obtain ⟨hzD, hzDc⟩ := diag_central h hz hzc
  obtain ⟨m, hm, ⟨eP⟩⟩ := sub_dihedral hp7 hp8 hDp h.isSylowIn_diag
  have hzD2 : orderOf (δ ⟨z, hz.2⟩) = 2 := by
    rw [orderOf_injective δ hinj, Subgroup.orderOf_mk]
    exact hz2
  have hzQ : ∀ x ∈ T ⊓ Q, δ ⟨z, hz.2⟩ * x = x * δ ⟨z, hz.2⟩ := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer ((T ⊓ D : Subgroup G) : Set G) := by
      apply mem_normalizer_of_conjSub_eq
      rw [conjSub_inf, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hx.1),
        conjSub_eq_of_mem_normalizer (hQN hx.2)]
    have hfz := conj_eq_of_mem_normalizer hm eP hzD hzD2 hzDc hxN
    calc δ ⟨z, hz.2⟩ * x = (x * δ ⟨z, hz.2⟩ * x⁻¹) * x := by rw [hfz]
      _ = x * δ ⟨z, hz.2⟩ := by group
  obtain ⟨r, P₀, b, w, hr, hr2, hP₀D, hP₀ne, hP₀g, hA₁card, hbA, hb1, hwA, hwz, hAn, hbc, hzinv,
      htn⟩ := typeIIo_local (p := p) Fact.out hp8 hp7 (hA₁A.trans hAT) hA₁Q hA₁e hA₁4 hDQ hDn hDp
    h.diag_simple h.diag_nonabelian hTQ hAD hAC hzD.2 hzD2 hzQ
  have hr' : Odd r := hr.odd_of_ne_two hr2
  have hP₀odd : ∀ x ∈ P₀, x * x = 1 → x = 1 := by
    intro x hx hxx
    obtain ⟨k, hk⟩ := hP₀g ⟨x, hx⟩
    have hk' : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd1 : orderOf x ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hxx)
    have hco : Nat.Coprime (r ^ k) 2 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
    have := Nat.dvd_gcd hd1 hd2
    rw [hco.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ P₀, x ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hP₀ne ((Subgroup.eq_bot_iff_forall P₀).mpr hc)
  have hw₀ : ∀ x ∈ P₀, w * x * w⁻¹ = x⁻¹ := fun x hx => by
    rw [hwz x (hP₀D hx)]
    exact hzinv x hx
  have hw1 : w ≠ 1 := by
    intro hw
    apply hx₀1
    apply hP₀odd x₀ hx₀
    have h1 := hw₀ x₀ hx₀
    rw [hw, one_mul, inv_one, mul_one] at h1
    calc x₀ * x₀ = x₀ * x₀⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel x₀
  have hbw : b ≠ w := by
    intro hbw
    apply hx₀1
    apply hP₀odd x₀ hx₀
    have h1 := hw₀ x₀ hx₀
    rw [← hbw, hbc x₀ hx₀, mul_inv_cancel_right] at h1
    calc x₀ * x₀ = x₀ * x₀⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel x₀
  set R : Subgroup G := T ⊓ Subgroup.centralizer (A : Set G) with hRdef
  have hkA : ∀ k ∈ R, ∀ a ∈ A, a * k = k * a := fun k hk a ha =>
    Subgroup.mem_centralizer_iff.mp hk.2 a ha
  have hCP : C ⊔ V₀ ≤ Subgroup.centralizer (P₀ : Set G) :=
    (sup_le hCD hV₀D).trans (Subgroup.centralizer_le hP₀D)
  have hAeq : A = C ⊔ (A₁ ⊔ V₀) := by rw [hA₁V₀V, hCVA]
  have hAP₀ : A ≤ Subgroup.normalizer (P₀ : Set G) := by
    refine hAeq.le.trans (sup_le
      ((le_sup_left.trans hCP).trans (Subgroup.centralizer_le_normalizer _))
      (sup_le (fun a ha => hAn a ha)
        ((le_sup_right.trans hCP).trans (Subgroup.centralizer_le_normalizer _))))
  have hRP : ∀ u ∈ R, A1b.conjSub u D = D → A1b.conjSub u P₀ = P₀ := by
    intro u hu huD
    have huQ : u ∈ T ⊓ Q :=
      ⟨hu.1, Subgroup.mem_sup_right ⟨hu.1, mem_normalizer_of_conjSub_eq huD⟩⟩
    exact conjSub_eq_of_mem_normalizer
      (htn u huQ fun a ha => (hkA u hu a (hA₁A ha)).symm)
  let _ : Fintype ↥R := Fintype.ofFinite _
  set F : ↥R → Subgroup G := fun k => A1b.conjSub (k : G) P₀ with hF
  have hF2 : ∀ i j, F i = F j ∨ ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x := by
    intro i j
    set u : G := (i : G)⁻¹ * j with hu
    have huR : u ∈ R := R.mul_mem (R.inv_mem i.2) j.2
    have hj : (j : G) = i * u := by rw [hu]; group
    rcases h.eq_or_commute_conj huR.2 with hD' | hD'
    · left
      show A1b.conjSub (i : G) P₀ = A1b.conjSub (j : G) P₀
      rw [hj, A1b.conjSub_mul, hRP u huR hD']
    · right
      intro x hx y hy
      have hx' : (i : G)⁻¹ * x * i ∈ P₀ := A1b.mem_conjSub_iff.mp hx
      have hy' : (i : G)⁻¹ * y * i ∈ A1b.conjSub u D := by
        have hyj : y ∈ A1b.conjSub (i : G) (A1b.conjSub u P₀) := by
          rw [← A1b.conjSub_mul, ← hj]
          exact hy
        exact A1b.conjSub_mono u hP₀D (A1b.mem_conjSub_iff.mp hyj)
      have hc := hD' _ hy' _ (hP₀D hx')
      calc x * y = (i : G) * (((i : G)⁻¹ * x * i) * ((i : G)⁻¹ * y * i)) * (i : G)⁻¹ := by
            group
        _ = (i : G) * (((i : G)⁻¹ * y * i) * ((i : G)⁻¹ * x * i)) * (i : G)⁻¹ := by rw [← hc]
        _ = y * x := by group
  have hFg : ∀ i, IsPGroup r ↥(F i) := fun i => hP₀g.map (MulAut.conj (i : G)).toMonoidHom
  have hPg := isPGroup_iSup F hF2 hFg Finset.univ
  have hPeq : (⨆ i ∈ (Finset.univ : Finset ↥R), F i) = ⨆ i, F i := by simp
  rw [hPeq] at hPg
  set P : Subgroup G := ⨆ i, F i with hPdef
  have hP₀P : P₀ ≤ P := by
    have h1 : F 1 ≤ P := le_iSup F 1
    simpa [hF, A1b.conjSub_one] using h1
  have hPne : P ≠ ⊥ := fun hbot => hP₀ne (le_bot_iff.mp (hP₀P.trans hbot.le))
  have hRN : R ≤ Subgroup.normalizer (P : Set G) := by
    intro t ht
    apply mem_normalizer_of_conjSub_eq
    rw [hPdef, E111R.conjSub_iSup]
    have h1 : ∀ i : ↥R, A1b.conjSub t (F i) = F (⟨t, ht⟩ * i) := fun i => by
      simp only [hF, Subgroup.coe_mul]
      rw [A1b.conjSub_mul]
    simp only [h1]
    exact Equiv.iSup_comp (g := F) (Equiv.mulLeft ⟨t, ht⟩)
  have hτP : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (P : Set G) :=
    (E111R.tauOf_le (E111R.pCoreOf_two_eq_bot hR) T A).trans hRN
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    have := le_normalizer_iSup F Finset.univ (K := A) fun i _ a ha => by
      apply mem_normalizer_of_conjSub_eq
      show A1b.conjSub a (A1b.conjSub (i : G) P₀) = A1b.conjSub (i : G) P₀
      rw [conjSub_conjSub_comm (hkA i i.2 a ha), conjSub_eq_of_mem_normalizer (hAP₀ ha)]
    rwa [hPeq] at this
  have hconjcomm : ∀ (i : ↥R) {a : G}, a ∈ A → ∀ y : G,
      a * ((i : G) * y * (i : G)⁻¹) * a⁻¹ = (i : G) * (a * y * a⁻¹) * (i : G)⁻¹ := by
    intro i a ha y
    have hai : a * (i : G) = i * a := hkA i i.2 a ha
    calc a * ((i : G) * y * (i : G)⁻¹) * a⁻¹ = (a * i) * y * (a * i)⁻¹ := by group
      _ = (i * a) * y * (i * a)⁻¹ := by rw [hai]
      _ = (i : G) * (a * y * a⁻¹) * (i : G)⁻¹ := by group
  have hwF : ∀ i, ∀ x ∈ F i, w * x * w⁻¹ = x⁻¹ := by
    intro i x hx
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ P₀, x = (i : G) * x' * (i : G)⁻¹ :=
      ⟨(i : G)⁻¹ * x * i, A1b.mem_conjSub_iff.mp hx, by group⟩
    rw [hconjcomm i (hA₁A hwA), hw₀ x' hx']
    group
  have hcomm : ⁅P, A⁆ = P := by
    refine le_antisymm ?_ (iSup_le fun i =>
      (le_commutator_of_inv hr' (hFg i) (hA₁A hwA) (hwF i)).trans
        (Subgroup.commutator_mono (le_iSup F i) le_rfl))
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have h1 : a * x⁻¹ * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hAP ha) x⁻¹).mp (inv_mem hx)
    have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem hx h1
  set B : Subgroup G := Subgroup.zpowers b ⊔ (C ⊔ V₀) with hBdef
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr (hA₁A hbA)) (sup_le hCA inf_le_left)
  have hBP₀ : B ≤ Subgroup.centralizer (P₀ : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) hCP
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hbc x hx).symm
  have hBc : B ≤ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine iSup_le fun i => ?_
    intro x hx
    obtain ⟨x', hx', rfl⟩ : ∃ x' ∈ P₀, x = (i : G) * x' * (i : G)⁻¹ :=
      ⟨(i : G)⁻¹ * x * i, A1b.mem_conjSub_iff.mp hx, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyx : y * x' * y⁻¹ = x' := by
      rw [← Subgroup.mem_centralizer_iff.mp (hBP₀ hy) x' hx']
      group
    have h1 := hconjcomm i (hBA hy) x'
    rw [hyx] at h1
    calc y * ((i : G) * x' * (i : G)⁻¹) = y * ((i : G) * x' * (i : G)⁻¹) * y⁻¹ * y := by group
      _ = (i : G) * x' * (i : G)⁻¹ * y := by rw [h1]
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hA.2 b (hA₁A hbA)) hb1
  have hw2 : orderOf w = 2 := orderOf_eq_prime (hA.2 w (hA₁A hwA)) hw1
  have hzp : ∀ {y x : G}, orderOf y = 2 → x ∈ Subgroup.zpowers y → x = 1 ∨ x = y := by
    intro y x hy hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hsq : y ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ← hy, pow_orderOf_eq_one]
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left
      rw [zpow_mul, hsq, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]
  have hbwinf : Subgroup.zpowers b ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxb, hxw⟩
    rcases hzp hb2 hxb with h1 | h1
    · exact h1
    · rcases hzp hw2 hxw with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hbw
  have hbwA₁ : Subgroup.zpowers b ⊔ Subgroup.zpowers w = A₁ := by
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers w ≤ A₁ :=
      sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr hwA)
    have hcard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers w) = 4 := by
      rw [card_sup_of_comm hA ((Subgroup.zpowers_le.mpr hbA).trans hA₁A)
        ((Subgroup.zpowers_le.mpr hwA).trans hA₁A) hbwinf, Nat.card_zpowers, Nat.card_zpowers,
        hb2, hw2]
    exact Subgroup.eq_of_le_of_card_ge hle (hA₁card.trans hcard.symm).le
  have hA₁CV : A₁ ⊓ (C ⊔ V₀) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact hAC x hx1 ((sup_le hCD hV₀D) hx2)
  have hsupA : A₁ ⊔ (C ⊔ V₀) = A := by
    rw [hAeq]
    exact le_antisymm (sup_le (le_sup_left.trans le_sup_right) (sup_le le_sup_left
      (le_sup_right.trans le_sup_right))) (sup_le (le_sup_left.trans le_sup_right)
      (sup_le le_sup_left (le_sup_right.trans le_sup_right)))
  have hBidx : B.relIndex A = 2 :=
    relIndex_eq_two hA hA₁A hA₁CV (sup_le hCA inf_le_left) hwA hw1
      (Subgroup.zpowers_le.mpr hbA) hbwinf hbwA₁ hsupA
  have hE := (E1.isE_one_sup hr hr2 hR.2.2.2.2.2.1 hAT hA hPg hPne hτP hcomm hBA hBc
    hBidx.le).1
  refine ⟨P ⊔ E1.tauOf ⊤ T A, hE, x₀, Subgroup.mem_sup_left (hP₀P hx₀),
    hS.le_normalizer (h.diag_le (hP₀D hx₀)), fun hxz => hx₀1 ?_⟩
  obtain ⟨s, hs⟩ := hP₀D hx₀
  have hinvs : δ (⟨z, hz.2⟩ * s * (⟨z, hz.2⟩ : ↥S)⁻¹) = δ s⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, hs]
    exact hzinv x₀ hx₀
  have hzs : (z : G) * s * z⁻¹ = (s : G)⁻¹ :=
    congrArg Subtype.val (hinj hinvs)
  have hsc : (s : G)⁻¹ * x₀ ∈ Subgroup.centralizer (S : Set G) := by
    rw [← hs]
    exact inv_mul_diagHom_mem h.diagComm s
  have hsz : (s : G) * z = z * s := by
    have h1 := Subgroup.mem_centralizer_iff.mp hsc z hz.2
    calc (s : G) * z = (s : G) * z * ((s : G)⁻¹ * x₀) * ((s : G)⁻¹ * x₀)⁻¹ := by group
      _ = (s : G) * (((s : G)⁻¹ * x₀) * z) * ((s : G)⁻¹ * x₀)⁻¹ := by
          rw [mul_assoc (s : G) z, h1]
      _ = x₀ * z * x₀⁻¹ * s := by group
      _ = z * x₀ * x₀⁻¹ * s := by rw [hxz]
      _ = z * s := by group
  have hss : (s : G) * s = 1 := by
    have h2 : (z : G) * s * z⁻¹ = s := by rw [← hsz]; group
    rw [h2] at hzs
    calc (s : G) * s = (s : G) * (s : G)⁻¹ := by rw [← hzs]
      _ = 1 := mul_inv_cancel _
  apply hP₀odd x₀ hx₀
  rw [← hs, ← map_mul]
  have : s * s = 1 := Subtype.ext hss
  rw [this, map_one]

end Outer

theorem kleinMemberOuter_holds {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) :
    KleinMemberOuter p := by
  have : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    omega
  intro G _ _ X T A S hR hQ hAT hA hS h4 hout z hz hz2 hzc
  exact outer_member hp7 hp8 hR hQ hAT hA hS h4 hout hz hz2 hzc

end CFSG.Quasithin.E2.E22N.E111L
