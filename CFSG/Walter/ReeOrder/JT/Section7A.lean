module

public import CFSG.Walter.ReeOrder.JT.Section4H
public import CFSG.Walter.ReeOrder.JT.PSL2Unipotent
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem three_pow_mod_eight (n : ℕ) : 3 ^ n % 8 = 1 ∨ 3 ^ n % 8 = 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem p_ne_two_of_eq_three : h.p ≠ 2 := by rw [hp3]; norm_num

omit hp3 in
theorem f_ne_zero : h.f ≠ 0 := by
  intro hf0
  have := h.five_lt
  rw [hf0, pow_zero] at this
  omega

theorem q_mod_eight_of_eq_three :
    h.q % 8 = 3 := by
  rcases lemma_2_1 h (h.p_ne_two_of_eq_three hp3) |>.1 with h8 | h8
  · exact h8
  · rcases three_pow_mod_eight h.f with h1 | h1 <;> rw [JTHyp.q_eq, hp3, h1] at h8 <;> omega

theorem eps_eq_one_of_eq_three :
    h.eps = 1 := by
  have := h.q_mod_eight_of_eq_three hp3
  unfold JTHyp.eps
  rw [ite_eq_left_iff]
  omega

theorem three_dvd_q : 3 ∣ h.q := by
  rw [JTHyp.q_eq, hp3]
  exact dvd_pow_self 3 h.f_ne_zero

theorem unipotentFacts : PSL2UnipotentFacts h.F h.p h.f :=
  psl2UnipotentFacts h.F h.iso (h.p_ne_two_of_eq_three hp3) h.f_ne_zero

end JTHyp

namespace Setup

variable {h : JTHyp G} (s : Setup h) (hp3 : h.p = 3)
include hp3

theorem three_not_dvd_card_Q :
    ¬ 3 ∣ Nat.card s.Q := by
  intro h3
  have h4 := s.four_mul_card_Q (h.p_ne_two_of_eq_three hp3)
  rw [h.eps_eq_one_of_eq_three hp3] at h4
  obtain ⟨m, hm⟩ := h.three_dvd_q hp3
  obtain ⟨k, hk⟩ := h3
  rw [hk, hm] at h4
  push_cast at h4
  omega

end Setup

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem odd_orderOf_of_mem_normalizer
    {x : G} (hxF : x ∈ h.F) (hx : orderOf x = 3) {n : G}
    (hnF : n ∈ h.F) (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    Odd (orderOf n) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hU := h.unipotentFacts hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : IsPGroup h.p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, hp3, pow_one])
  obtain ⟨R, hxR, hRF, hRcard⟩ := hU.exists_le _ ((Subgroup.zpowers_le).mpr hxF) hX3
  have hx1 : x ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hx; omega
  have hnR : n ∈ h.F ⊓ Subgroup.normalizer (R : Set G) := by
    refine ⟨hnF, ?_⟩
    have hR' : R.map (MulAut.conj n).toMonoidHom = R := by
      refine (hU.ti R _ hRF ?_ hRcard ?_ (n * x * n⁻¹) ?_ ?_ ?_).symm
      · rintro _ ⟨y, hy, rfl⟩
        exact h.F.mul_mem (h.F.mul_mem hnF (hRF hy)) (h.F.inv_mem hnF)
      · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hRcard]
      · exact hxR ((Subgroup.mem_normalizer_iff.mp hn x).mp (Subgroup.mem_zpowers x))
      · exact ⟨x, hxR (Subgroup.mem_zpowers x), rfl⟩
      · intro h0
        apply hx1
        have := congrArg (fun y => n⁻¹ * y * n) h0
        simpa [mul_assoc] using this
    exact (conj_smul_eq_iff (K := R)).mp hR'
  have hodd : Odd (Nat.card (h.F ⊓ Subgroup.normalizer (R : Set G) : Subgroup G)) := by
    have hdvd := hU.normalizer R hRF hRcard
    rw [← JTHyp.q_eq] at hdvd
    refine Odd.of_dvd_nat ?_ hdvd
    refine Nat.odd_mul.mpr ⟨?_, ?_⟩
    · exact Nat.odd_iff.mpr (by omega)
    · exact Nat.odd_iff.mpr (by omega)
  exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hnR)

theorem not_four_dvd_card_normalizer_of_orderOf_three
    {y : G} (hyF : y ∈ h.F)
    (hy : orderOf y = 3) : ¬ 4 ∣ Nat.card (Subgroup.normalizer (Subgroup.zpowers y : Set G)) := by
  have hyt : y * h.t = h.t * y := h.commute_of_mem_F hyF
  set N := Subgroup.normalizer (Subgroup.zpowers y : Set G) with hNdef
  have htN : h.t ∈ N := mem_normalizer_zpowers_of_commute hyt.symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : IsPGroup 2 (Subgroup.zpowers (⟨h.t, htN⟩ : N)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_t, pow_one])
  obtain ⟨T, hT⟩ := ht2.exists_le_sylow
  set T₁ := (T : Subgroup N).map N.subtype with hT₁def
  have htT₁ : h.t ∈ T₁ := ⟨⟨h.t, htN⟩, hT (Subgroup.mem_zpowers _), rfl⟩
  have hT₁2 : IsPGroup 2 T₁ := T.isPGroup'.map _
  obtain ⟨S', hS'⟩ := hT₁2.exists_le_sylow
  have hab := h.abelian_sylow S'
  have hT₁C : ∀ z ∈ T₁, z * h.t = h.t * z := fun z hz =>
    congrArg Subtype.val (hab.is_comm.comm ⟨z, hS' hz⟩ ⟨h.t, hS' htT₁⟩)
  have hT₁card : Nat.card T₁ = 2 ^ (Nat.card T₁).factorization 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT₁2
    rw [hk, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hT₁t : ∀ z ∈ T₁, z = 1 ∨ z = h.t := by
    intro z hz
    have hzN : z ∈ N := Subgroup.map_subtype_le _ hz
    have hpow : ∀ w ∈ T₁, w ^ Nat.card T₁ = 1 := fun w hw =>
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard T₁ hw)
    have hkey : ∀ w : G, w ∈ h.F → w ∈ N → w ^ Nat.card T₁ = 1 → w = 1 := by
      intro w hwF hwN hw
      have hodd := h.odd_orderOf_of_mem_normalizer hp3 hyF hy hwF hwN
      have hdvd : orderOf w ∣ 2 ^ (Nat.card T₁).factorization 2 :=
        hT₁card ▸ orderOf_dvd_of_pow_eq_one hw
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rw [hj] at hodd
      have hj0 : j = 0 := by
        by_contra hj0
        exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hj0).mpr even_two)
      rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    rcases h.mem_centralizer_t.mp (Subgroup.mem_centralizer_singleton_iff.mpr
      (hT₁C z hz)) with hzF | hzF
    · exact Or.inl (hkey z hzF hzN (hpow z hz))
    · right
      have h1 : h.t * z = 1 := by
        refine hkey _ hzF (N.mul_mem htN hzN) ?_
        rw [(Commute.mul_pow (hT₁C z hz).symm _), hpow _ htT₁, hpow z hz, one_mul]
      rw [eq_inv_of_mul_eq_one_right h1, h.t_inv]
  have hT₁le : Nat.card T₁ ≤ 2 := by
    have hle : T₁ ≤ Subgroup.zpowers h.t := fun z hz => by
      rcases hT₁t z hz with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, h.orderOf_t] at this
  have hTcard : Nat.card (T : Subgroup N) = Nat.card T₁ :=
    (Subgroup.card_map_of_injective N.subtype_injective).symm
  have hN4 : ¬ 4 ∣ Nat.card N := by
    intro h4
    have := Sylow.pow_dvd_card_of_pow_dvd_card T (n := 2) (by norm_num; exact h4)
    rw [hTcard] at this
    have := Nat.le_of_dvd (Nat.card_pos) this
    omega
  exact hN4

theorem lemma_7_1_a
    {x u : G} (hx : orderOf x = 3) (hu : orderOf u = 2) (hxu : x * u = u * x)
    (g : G) : g * x * g⁻¹ ≠ x⁻¹ := by
  have hp := h.p_ne_two_of_eq_three hp3
  suffices H : ∀ {y : G}, orderOf y = 3 → y * h.t = h.t * y → ∀ g : G, g * y * g⁻¹ ≠ y⁻¹ by
    obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hu
    intro hg
    refine H (y := a * x * a⁻¹) (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]) ?_
      (a * g * a⁻¹) ?_
    · rw [← ha]
      calc a * x * a⁻¹ * (a * u * a⁻¹) = a * (x * u) * a⁻¹ := by group
        _ = a * (u * x) * a⁻¹ := by rw [hxu]
        _ = a * u * a⁻¹ * (a * x * a⁻¹) := by group
    · calc a * g * a⁻¹ * (a * x * a⁻¹) * (a * g * a⁻¹)⁻¹ = a * (g * x * g⁻¹) * a⁻¹ := by group
        _ = (a * x * a⁻¹)⁻¹ := by rw [hg]; group
  intro y hy hyt g hg
  have hyF : y ∈ h.F := h.mem_F_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hyt)
    (by rw [hy]; decide)
  set N := Subgroup.normalizer (Subgroup.zpowers y : Set G) with hNdef
  have hN4 : ¬ 4 ∣ Nat.card N := h.not_four_dvd_card_normalizer_of_orderOf_three hp3 hyF hy
  have hgN : g ∈ N := by
    refine (conj_smul_eq_iff (K := Subgroup.zpowers y)).mp ?_
    change (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers y
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers y
    rw [hg, Subgroup.zpowers_inv]
  have hy3 := pow_three_eq_one_of_orderOf hy
  have hyinv : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hy3])
  have hyy : y⁻¹ ≠ y := by
    intro h0
    have : y ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h0]; exact inv_mul_cancel y
    have := orderOf_dvd_of_pow_eq_one this
    rw [hy] at this
    omega
  have hCN : Subgroup.centralizer ({y} : Set G) ≤ N := fun b hb =>
    mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hb)
  have hcard := card_eq_two_mul_of_xor hCN hgN (fun b hb => by
    have hby : b * y * b⁻¹ = y ∨ b * y * b⁻¹ = y⁻¹ := by
      have hmem := (Subgroup.mem_normalizer_iff.mp hb y).mp (Subgroup.mem_zpowers y)
      rcases (mem_zpowers_iff_of_orderOf_three hy).mp hmem with h1 | h1 | h1
      · exfalso
        have : y = 1 := by
          have := congrArg (fun w => b⁻¹ * w * b) h1
          simpa [mul_assoc] using this
        rw [this, orderOf_one] at hy
        omega
      · exact Or.inl h1
      · exact Or.inr (h1.trans hyinv.symm)
    have hbg : b * g * y * (b * g)⁻¹ = (b * y * b⁻¹)⁻¹ := by
      rw [show b * g * y * (b * g)⁻¹ = b * (g * y * g⁻¹) * b⁻¹ by group, hg]
      group
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have hc : ∀ c : G, c * y = y * c ↔ c * y * c⁻¹ = y := fun c => by
      constructor
      · intro h1; rw [h1, mul_inv_cancel_right]
      · intro h1
        calc c * y = c * y * c⁻¹ * c := by group
          _ = y * c := by rw [h1]
    rw [hc, hc, hbg]
    rcases hby with h1 | h1 <;> rw [h1]
    · exact ⟨fun h2 => absurd h2 hyy, fun h2 => absurd rfl h2⟩
    · exact ⟨fun _ => hyy, fun _ => inv_inv y⟩)
  apply hN4
  rw [hcard]
  have ht : 2 ∣ Nat.card (Subgroup.centralizer ({y} : Set G)) :=
    h.orderOf_t ▸ Subgroup.orderOf_dvd_natCard _
      (Subgroup.mem_centralizer_singleton_iff.mpr hyt.symm)
  obtain ⟨k, hk⟩ := ht
  exact ⟨k, by omega⟩

end JTHyp

namespace Setup

variable {h : JTHyp G} (s : Setup h) (hp3 : h.p = 3)
include hp3

theorem lemma_7_1_b
    (hS : SuzukiFourGroupTheorem) :
    Subgroup.normalizer (s.Q : Set G) = Subgroup.normalizer (s.T : Set G) := by
  have hp := h.p_ne_two_of_eq_three hp3
  rcases s.lemma_4_4 hp hS with h1 | ⟨L, D, ⟨eL⟩, -, -, hD, hLD⟩
  · exact h1
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := L) 3
      (by rw [card_of_psl24 eL]; norm_num)
    obtain ⟨a, -, hal⟩ := exists_inv_of_orderOf_three_of_psl24 eL hl
    have hD2 : 2 ∣ Nat.card D := by
      have h4 := s.four_mul_card_Q hp
      have : (Nat.card D : ℤ) = 2 * Nat.card s.Q := by linarith
      exact ⟨Nat.card s.Q, by exact_mod_cast this⟩
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hD2
    refine h.lemma_7_1_a hp3 (x := (l : G)) (u := (d : G)) (by rw [Subgroup.orderOf_coe, hl])
      (by rw [Subgroup.orderOf_coe, hd]) (hLD.commute l.2 d.2) (a : G) ?_
    exact congrArg Subtype.val hal

end Setup

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem mul_self_of_isPGroup_two
    {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    x * x = 1 := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have := ((lemma_2_1 h (h.p_ne_two_of_eq_three hp3)).2.1 S).1
  rw [← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian x (hS hx)

theorem three_not_dvd_card_centralizer
    {V : Subgroup G} (hV : IsKleinFour V) :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (V : Set G)) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV.card_four]; norm_num)
  obtain ⟨⟨v, hvV⟩, hv1⟩ := exists_ne (1 : V)
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_isKleinFour' hV hvV)
      (fun h0 => hv1 (Subtype.ext h0))
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hv2
  set V' := V.map (MulAut.conj a).toMonoidHom with hV'def
  have eV : V' ≃* V := (V.equivMapOfInjective _ (MulAut.conj a).injective).symm
  have hV' : IsKleinFour V' :=
    ⟨by rw [Nat.card_congr eV.toEquiv, hV.card_four],
      by rw [Monoid.exponent_eq_of_mulEquiv eV, hV.exponent_two]⟩
  have htV' : h.t ∈ V' := ⟨v, hvV, ha⟩
  have hV'2 : IsPGroup 2 V' := IsPGroup.of_card (n := 2) (by rw [hV'.card_four]; norm_num)
  obtain ⟨S', hS'⟩ := hV'2.exists_le_sylow
  let s : Setup h := ⟨S', hS' htV', V', hS', hV', htV'⟩
  have hcard := s.card_centralizer_T hp
  have h3Q := s.three_not_dvd_card_Q hp3
  have hCC : Nat.card (Subgroup.centralizer (V : Set G)) =
      Nat.card (Subgroup.centralizer (V' : Set G)) := by
    have := map_centralizer_of_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective V
    rw [MonoidHom.range_eq_top.mpr (MulAut.conj a).surjective, top_inf_eq] at this
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
      (MulAut.conj a).injective, this]
  rw [hCC]
  change ¬ 3 ∣ Nat.card (Subgroup.centralizer (s.T : Set G))
  rw [hcard]
  intro h3
  exact h3Q ((Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 8)).mp h3)

theorem lemma_7_2 {H : Subgroup G}
    (hH : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3) (h4 : 4 ∣ Nat.card H) :
    (∃ P : Sylow 2 H, (P : Subgroup H).Normal) ∧ ¬ 9 ∣ Nat.card H := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hcardH : Nat.card H =
      2 ^ (Nat.card H).factorization 2 * 3 ^ (Nat.card H).factorization 3 := by
    have hsupp : (Nat.card H).factorization.support ⊆ {2, 3} := by
      intro r hr
      rw [Nat.support_factorization] at hr
      rcases hH r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr) with
        h2 | h2 <;> simp [h2]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hH0]
    rw [Finsupp.prod_of_support_subset _ hsupp _ (by simp), Finset.prod_pair (by norm_num)]
  have hsolv : Group.IsSolvable H := by
    let _ : Fintype H := Fintype.ofFinite H
    exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcardH)
  let T₀ : Sylow 2 H := default
  set T₀' := (T₀ : Subgroup H).map H.subtype with hT₀'def
  have hT₀'card : Nat.card T₀' = Nat.card (T₀ : Subgroup H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h4T : 4 ∣ Nat.card T₀' := by
    rw [hT₀'card]
    exact Sylow.pow_dvd_card_of_pow_dvd_card T₀ (n := 2) (by norm_num; exact h4)
  have hT₀'2 : IsPGroup 2 T₀' := T₀.isPGroup'.map _
  obtain ⟨S', hS'⟩ := hT₀'2.exists_le_sylow
  have hS'ab := h.abelian_sylow S'
  have hT₀'comm : ∀ x ∈ T₀', ∀ y ∈ T₀', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hS'ab.is_comm.comm ⟨x, hS' hx⟩ ⟨y, hS' hy⟩)
  have hT₀'sq : ∀ x ∈ T₀', x * x = 1 := fun x hx => h.mul_self_of_isPGroup_two hp3 hT₀'2 hx
  obtain ⟨a, haT, ha1⟩ : ∃ a ∈ T₀', a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : T₀' = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at h4T
    omega
  obtain ⟨b, hbT, hb1, hba⟩ : ∃ b ∈ T₀', b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (T₀' : Set G) ⊆ {1, a} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon x hx hx1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm ha1)] at h1
    have h2 : Nat.card T₀' = (T₀' : Set G).ncard := by rw [← Nat.card_coe_set_eq]; rfl
    have := Nat.le_of_dvd Nat.card_pos h4T
    omega
  have haa := hT₀'sq a haT
  have hbb := hT₀'sq b hbT
  have hab : Commute a b := hT₀'comm a haT b hbT
  have haH : a ∈ H := Subgroup.map_subtype_le _ haT
  have hbH : b ∈ H := Subgroup.map_subtype_le _ hbT
  set H₀ := (CFSG.pCore 3 H).map H.subtype with hH₀def
  have hH₀3 : IsPGroup 3 H₀ := (CFSG.pCore_isPGroup).map _
  have hH₀N : ∀ g ∈ H, g ∈ Subgroup.normalizer (H₀ : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (CFSG.pCore_normal).conj_mem y hy _, rfl⟩
  have hH₀odd : Odd (Nat.card H₀) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH₀3
    rw [hk]
    exact Odd.pow (by decide)
  have hfix : ∀ x : G, x ∈ H → x * x = 1 → x ≠ 1 → ∀ w : G, w ∈ H → w * w = 1 →
      w * x = x * w → ∀ z ∈ H₀, z * x = x * z → z * w = w * z := by
    intro x hxH hxx hx1 w hwH hww hwx z hz hzx
    by_contra hzw
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    set c := z⁻¹ * (w * z * w⁻¹) with hc
    have hcH : c ∈ H₀ := H₀.mul_mem (H₀.inv_mem hz)
      ((Subgroup.mem_normalizer_iff.mp (hH₀N w hwH) z).mp hz)
    have hc1 : c ≠ 1 := by
      intro h0
      apply hzw
      have : w * z * w⁻¹ = z := by
        have := congrArg (z * ·) h0
        simpa [hc] using this
      calc z * w = w * z * w⁻¹ * w := by rw [this]
        _ = w * z := by group
    have hcw : w * c * w⁻¹ = c⁻¹ := by
      have e1 : w * c * w⁻¹ = w * z⁻¹ * w * z * (w * w)⁻¹ := by rw [hc]; group
      have e2 : c⁻¹ = w * z⁻¹ * w⁻¹ * z := by rw [hc]; group
      rw [e1, e2, hww, inv_one, mul_one, hwinv]
    have hcx : c * x = x * c := by
      have h1 : Commute z x := hzx
      have h2 : Commute w x := hwx
      exact ((h1.inv_left).mul_left ((h2.mul_left h1).mul_left h2.inv_left)).eq
    have h3c : 3 ∣ orderOf c := by
      have hdvd : orderOf c ∣ 3 ^ (Nat.card H₀).factorization 3 := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH₀3
        have := Subgroup.orderOf_dvd_natCard H₀ hcH
        rw [hk] at this
        rw [hk, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
        exact this
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      have hj0 : j ≠ 0 := fun h0 => hc1 (orderOf_eq_one_iff.mp (by rw [hj, h0, pow_zero]))
      rw [hj]
      exact dvd_pow_self 3 hj0
    obtain ⟨⟨c', hc'⟩, hc'o⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers c) 3
      (by rw [Nat.card_zpowers]; exact h3c)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    have hc'o' : orderOf (c ^ n) = 3 := by rw [← hc'o, Subgroup.orderOf_mk]
    refine h.lemma_7_1_a hp3 (x := c ^ n) (u := x) hc'o' (orderOf_eq_prime (by
      rw [pow_two]; exact hxx) hx1) ((Commute.zpow_left hcx n).eq) w ?_
    rw [← conj_zpow, hcw, inv_zpow]
  have hab' : a * b * (a * b) = 1 := by
    rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab.eq,
      show a * (a * b) * b = (a * a) * (b * b) by group, haa, hbb, one_mul]
  have habH : a * b ∈ H := H.mul_mem haH hbH
  have hab1 : a * b ≠ 1 := fun h0 => hba (by
    have := eq_inv_of_mul_eq_one_right h0
    rw [this, inv_eq_of_mul_eq_one_right haa])
  have hba' : b * a = a * b := hab.eq.symm
  have hCa : ∀ z ∈ H₀, z * a = a * z → z * b = b * z := fun z hz hza =>
    hfix a haH haa ha1 b hbH hbb hba' z hz hza
  have hCb : ∀ z ∈ H₀, z * b = b * z → z * a = a * z := fun z hz hzb =>
    hfix b hbH hbb hb1 a haH haa hab.eq z hz hzb
  have hCab : ∀ z ∈ H₀, z * (a * b) = a * b * z → z * a = a * z ∧ z * b = b * z := by
    intro z hz hzab
    refine ⟨hfix (a * b) habH hab' hab1 a haH haa ?_ z hz hzab,
      hfix (a * b) habH hab' hab1 b hbH hbb ?_ z hz hzab⟩
    · rw [← mul_assoc, haa, one_mul, mul_assoc, ← hab.eq, ← mul_assoc, haa, one_mul]
    · rw [← mul_assoc, ← hab.eq]
  have hBW := card_mul_card_sq_eq_mul haa hbb ha1 hb1 (Ne.symm hba) hab H₀ (hH₀N a haH)
    (hH₀N b hbH) hH₀odd
  set C₀ := H₀ ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
    with hC₀def
  have hea : H₀ ⊓ Subgroup.centralizer ({a} : Set G) = C₀ := by
    refine le_antisymm (fun z hz => ⟨hz, ?_⟩) inf_le_left
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hCa z hz.1 (Subgroup.mem_centralizer_singleton_iff.mp hz.2))
  have heb : H₀ ⊓ Subgroup.centralizer ({b} : Set G) = C₀ := by
    refine le_antisymm (fun z hz => ⟨⟨hz.1, ?_⟩, hz.2⟩) (fun z hz => ⟨hz.1.1, hz.2⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hCb z hz.1 (Subgroup.mem_centralizer_singleton_iff.mp hz.2))
  have heab : H₀ ⊓ Subgroup.centralizer ({a * b} : Set G) = C₀ := by
    refine le_antisymm (fun z hz => ?_) (fun z hz => ⟨hz.1.1, ?_⟩)
    · obtain ⟨h1, h2⟩ := hCab z hz.1 (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
      exact ⟨⟨hz.1, Subgroup.mem_centralizer_singleton_iff.mpr h1⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr h2⟩
    · have h1 := Subgroup.mem_centralizer_singleton_iff.mp hz.1.2
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp hz.2
      show z ∈ Subgroup.centralizer ({a * b} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  rw [hea, heb, heab] at hBW
  have hC₀pos : 0 < Nat.card C₀ := Nat.card_pos
  have hH₀C₀ : Nat.card H₀ = Nat.card C₀ := by
    have : Nat.card H₀ * Nat.card C₀ ^ 2 = Nat.card C₀ * Nat.card C₀ ^ 2 := by
      rw [hBW]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this
  have hH₀le : H₀ ≤ C₀ := by
    have := Subgroup.eq_of_le_of_card_ge (show C₀ ≤ H₀ from fun z hz => hz.1.1) hH₀C₀.le
    rw [this]
  have hV := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b haa hbb ha1 hb1
    (Ne.symm hba) hab
  have hH₀V : H₀ ≤ Subgroup.centralizer
      (GorensteinWalter.kleinFourOfCommutingInvolutions a b haa hbb hab : Set G) := by
    intro z hz
    have hza := Subgroup.mem_centralizer_singleton_iff.mp (hH₀le hz).1.2
    have hzb := Subgroup.mem_centralizer_singleton_iff.mp (hH₀le hz).2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ ({a * b, a, b, 1} : Set G) at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · rw [mul_assoc, ← hzb, ← mul_assoc, ← hza, mul_assoc]
    · exact hza.symm
    · exact hzb.symm
    · rw [one_mul, mul_one]
  have hH₀1 : Nat.card H₀ = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH₀3
    rcases k with _ | k
    · rw [hk, pow_zero]
    · exfalso
      apply h.three_not_dvd_card_centralizer hp3 hV
      exact (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans (hk ▸ Subgroup.card_dvd_of_le hH₀V)
  have hcore3 : CFSG.pCore 3 H = ⊥ := by
    rw [← Subgroup.card_eq_one, ← Subgroup.card_map_of_injective H.subtype_injective]
    exact hH₀1
  have hcore2 : CFSG.pPrimeCore 2 H = ⊥ := by
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := H)
    have hdvd : Nat.card (CFSG.pPrimeCore 2 H) ∣ 3 ^ (Nat.card H).factorization 3 := by
      have := Subgroup.card_subgroup_dvd_card (CFSG.pPrimeCore 2 H)
      rw [hcardH] at this
      exact (Nat.Coprime.pow_left _ hcop).symm.dvd_of_dvd_mul_left this
    have h3 : IsPGroup 3 (CFSG.pPrimeCore 2 H) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      exact IsPGroup.of_card hj
    have hle : CFSG.pPrimeCore 2 H ≤ CFSG.pCore 3 H :=
      le_sSup ⟨CFSG.pPrimeCore_normal, h3⟩
    rw [hcore3] at hle
    exact le_bot_iff.mp hle
  have hFit := CFSG.Fitting_eq_pcore H 2 hcore2
  have hCF := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  rw [hFit] at hCF
  have hOT : CFSG.pCore 2 H ≤ (T₀ : Subgroup H) := CFSG.fitting_pCore_le_sylow T₀
  have hT₀ab : ∀ x ∈ (T₀ : Subgroup H), ∀ y ∈ (T₀ : Subgroup H), x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hT₀'comm _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
  have hT₀eq : (T₀ : Subgroup H) = CFSG.pCore 2 H := by
    refine le_antisymm (fun x hx => hCF ?_) hOT
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hT₀ab y (hOT hy) x hx
  refine ⟨⟨T₀, hT₀eq ▸ CFSG.pCore_normal⟩, ?_⟩
  intro h9
  obtain ⟨P₃, hP₃⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 2)
    (by norm_num; exact h9)
  set P₃' := P₃.map H.subtype with hP₃'def
  have hP₃'card : Nat.card P₃' = 9 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hP₃]
    norm_num
  have hT₀n : (T₀ : Subgroup H).Normal := hT₀eq ▸ CFSG.pCore_normal
  have hP₃N : P₃' ≤ Subgroup.normalizer (T₀' : Set G) := by
    rintro _ ⟨g, -, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨g * y * g⁻¹, hT₀n.conj_mem y hy g, rfl⟩
  have hdisj : Disjoint P₃' T₀' := by
    rw [Subgroup.disjoint_def]
    intro x hx3 hx2
    have h1 : orderOf x ∣ 9 := hP₃'card ▸ Subgroup.orderOf_dvd_natCard _ hx3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT₀'2
    have h2 : orderOf x ∣ 2 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard _ hx2
    have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hT₀'8 : Nat.card T₀' ∣ 8 := by
    rw [← (lemma_2_1 h hp).2.1 S' |>.2]
    exact Subgroup.card_dvd_of_le hS'
  have hcases : Nat.card T₀' = 4 ∨ Nat.card T₀' = 8 := by
    obtain ⟨k, hk⟩ := h4T
    have := Nat.le_of_dvd (by norm_num) hT₀'8
    have hpos := Nat.card_pos (α := T₀')
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card T₀' ∣ 2 ^ 3 by norm_num; exact hT₀'8)
      with ⟨j, hj, hj'⟩
    interval_cases j <;> omega
  rcases hcases with h4' | h8'
  ·
    have hV' : IsKleinFour T₀' := by
      refine ⟨h4', ?_⟩
      have : Nontrivial T₀' := Finite.one_lt_card_iff_nontrivial.mp (by rw [h4']; norm_num)
      refine (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun x hx1 => ?_
      refine orderOf_eq_prime (Subtype.ext ?_) hx1
      rw [SubgroupClass.coe_pow, pow_two]
      exact hT₀'sq x x.2
    have h6 := relIndex_inf_centralizer_dvd_six hV' P₃'
    rw [inf_eq_left.mpr hP₃N] at h6
    have hbot : P₃' ⊓ Subgroup.centralizer (T₀' : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx3 : x ∈ P₃' := hx.1
      have hxC : x ∈ Subgroup.centralizer (T₀' : Set G) := hx.2
      obtain ⟨y, -, rfl⟩ := hx3
      have hyC : y ∈ Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t' ht'
        have ht'T : (t' : G) ∈ T₀' := ⟨t', hOT ht', rfl⟩
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) _ ht'T)
      have hyT : y ∈ (T₀ : Subgroup H) := hT₀eq ▸ hCF hyC
      exact Subgroup.mem_bot.mpr ((Subgroup.disjoint_def.mp hdisj) hx.1 ⟨y, hyT, rfl⟩)
    rw [hbot, Subgroup.relIndex_bot_left, hP₃'card] at h6
    omega
  ·
    have hT₀S : T₀' = S' := Subgroup.eq_of_le_of_card_ge hS' (by
      rw [h8', ((lemma_2_1 h hp).2.1 S').2])
    have h21 := ((lemma_2_1 h hp).2.2.2.2.1 S').1
    have hNcard : Nat.card (Subgroup.normalizer ((S' : Subgroup G) : Set G)) = 168 := by
      have h1 := Subgroup.card_mul_index
        ((S' : Subgroup G).subgroupOf (Subgroup.normalizer ((S' : Subgroup G) : Set G)))
      rw [h21, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
        ((lemma_2_1 h hp).2.1 S').2] at h1
      omega
    have hsup := card_sup_eq_mul_of_disjoint (hT₀S ▸ hP₃N) (hT₀S ▸ hdisj)
    rw [hP₃'card, ((lemma_2_1 h hp).2.1 S').2] at hsup
    have hle : P₃' ⊔ (S' : Subgroup G) ≤ Subgroup.normalizer ((S' : Subgroup G) : Set G) :=
      sup_le (hT₀S ▸ hP₃N) Subgroup.le_normalizer
    have := Subgroup.card_dvd_of_le hle
    rw [hsup, hNcard] at this
    norm_num at this

end JTHyp

end CFSG.Walter.JT
