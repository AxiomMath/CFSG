module

public import CFSG.Walter.J1.Normalizer
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

theorem exists_conj_t_eq {x : G} (hx : orderOf x = 2) : ∃ g : G, (h.conj g).t = x := by
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hx
  refine ⟨g⁻¹, ?_⟩
  rw [conj_t, ← hg]
  group

include h in
theorem sq_eq_one_of_pow {x : G} {n : ℕ} (hx : x ^ 2 ^ n = 1) : x * x = 1 := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hx
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S, hS⟩ := hx2.exists_le_sylow
  have hxS : x ∈ S := hS (Subgroup.mem_zpowers x)
  have h8 : Nat.card (S : Subgroup G) = 8 := h.card_sylow' S
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (S : Subgroup G)) 2
    (by rw [h8]; norm_num)
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hy'
  exact (h.conj g).mul_self_of_mem_sylow S (by rw [hg]; exact y.2) hxS

include h in
theorem eq_one_of_commute_four {a b y : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a ≠ b) (hc : a * b = b * a) (hodd : Odd (orderOf y)) (hya : y * a = a * y)
    (hyb : y * b = b * y) : y = 1 := by
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq ha
  set h' := h.conj g
  have hyC : y ∈ Subgroup.centralizer ({h'.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hg]
    exact hya
  have hyF : y ∈ h'.F := h'.mem_F_of_odd hyC hodd
  have hbC : b ∈ Subgroup.centralizer ({h'.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hg]
    exact hc.symm
  obtain ⟨hb2, hb1⟩ := (orderOf_eq_two_iff).mp hb
  obtain ⟨ha2, ha1⟩ := (orderOf_eq_two_iff).mp ha
  obtain ⟨f, hfF, hf2, hf1, hfy⟩ : ∃ f ∈ h'.F, f ^ 2 = 1 ∧ f ≠ 1 ∧ f * y = y * f := by
    rcases h'.mem_centralizer_t.mp hbC with hbF | hbF
    · exact ⟨b, hbF, by rw [pow_two]; exact hb2, hb1, hyb.symm⟩
    · rw [hg] at hbF
      refine ⟨a * b, hbF, ?_, ?_, ?_⟩
      · rw [pow_two]
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hc]
          _ = 1 := by rw [← mul_assoc, ha2, one_mul, hb2]
      · intro h1
        apply hab
        have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this, inv_eq_of_mul_eq_one_right ha2]
      · calc a * b * y = a * (y * b) := by rw [mul_assoc, hyb]
          _ = y * (a * b) := by rw [← mul_assoc, ← hya, mul_assoc]
  have hy2 := A5Sub.sq_eq_one_of_commute h'.iso hfF hyF hf2 hf1 hfy
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

include h in
theorem exists_four_of_sylow (S : Sylow 2 G) :
    ∃ a ∈ (S : Subgroup G), ∃ b ∈ (S : Subgroup G), orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧
      a * b = b * a := by
  obtain ⟨T, hT⟩ := h.exists_sylow_mem_t
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T S
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_of_card_four (h.card_inf_F T hT)
  have hsq : ∀ x ∈ (T : Subgroup G), x * x = 1 := fun x hx => h.mul_self_of_mem_sylow T hT hx
  have habT := h.abelian_sylow T
  refine ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ ha.1
  · rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hb.1
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact (orderOf_eq_two_iff).mpr ⟨hsq a ha.1, ha1⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact (orderOf_eq_two_iff).mpr ⟨hsq b hb.1, hb1⟩
  · intro h1
    apply hab
    simpa using h1
  · have := congrArg Subtype.val (habT.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
    simp only [Subgroup.coe_mul] at this
    rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, this]
    group

include h in
theorem eq_bot_of_sylow_le_normalizer (S : Sylow 2 G) {K : Subgroup G}
    (hK : Odd (Nat.card K)) (hSK : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G)) :
    K = ⊥ := by
  obtain ⟨a, haS, b, hbS, ha, hb, hab, hc⟩ := h.exists_four_of_sylow S
  have hSab := h.abelian_sylow S
  obtain ⟨ha2, ha1⟩ := (orderOf_eq_two_iff).mp ha
  obtain ⟨hb2, hb1⟩ := (orderOf_eq_two_iff).mp hb
  have hC : ∀ x ∈ (S : Subgroup G), orderOf x = 2 →
      K ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
    intro x hxS hx
    obtain ⟨g, hg⟩ := h.exists_conj_t_eq hx
    set h' := h.conj g
    have htS : h'.t ∈ S := by rw [hg]; exact hxS
    set L := K ⊓ Subgroup.centralizer ({x} : Set G)
    have hLodd : Odd (Nat.card L) :=
      Odd.of_dvd_nat hK (Subgroup.card_dvd_of_le inf_le_left)
    have hLF : L ≤ h'.F := h'.le_F_of_odd (by rw [hg]; exact inf_le_right) hLodd
    obtain ⟨u, hu, v, hv, hu1, hv1, huv⟩ := exists_two_of_card_four (h'.card_inf_F S htS)
    have hsq : ∀ y ∈ (S : Subgroup G), y ^ 2 = 1 := fun y hy => by
      rw [pow_two]; exact h'.mul_self_of_mem_sylow S htS hy
    have hnorm : ∀ y ∈ (S : Subgroup G), y ∈ Subgroup.normalizer (L : Set G) := by
      intro y hy
      refine mem_normalizer_of_conj_mem fun z hz => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hSK hy) z).mp hz.1
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
        have hyx : y * x = x * y :=
          congrArg Subtype.val (hSab.is_comm.comm ⟨y, hy⟩ ⟨x, hxS⟩)
        calc y * z * y⁻¹ * x = y * z * (y⁻¹ * x) := by group
          _ = y * z * (x * y⁻¹) := by
            rw [show y⁻¹ * x = x * y⁻¹ by
              calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
                _ = y⁻¹ * (y * x) * y⁻¹ := by rw [hyx]
                _ = x * y⁻¹ := by group]
          _ = y * (z * x) * y⁻¹ := by group
          _ = y * (x * z) * y⁻¹ := by rw [hzx]
          _ = (y * x) * z * y⁻¹ := by group
          _ = x * (y * z * y⁻¹) := by rw [hyx]; group
    have huvc : u * v = v * u :=
      congrArg Subtype.val (hSab.is_comm.comm ⟨u, hu.1⟩ ⟨v, hv.1⟩)
    exact A5Sub.eq_bot_of_normalized h'.iso hLF hLodd hu.2 hv.2 (hsq u hu.1) (hsq v hv.1)
      hu1 hv1 huv huvc (hnorm u hu.1) (hnorm v hv.1)
  have habS : a * b ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem haS hbS
  have hab' : orderOf (a * b) = 2 := by
    refine (orderOf_eq_two_iff).mpr ⟨?_, ?_⟩
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hc]
        _ = 1 := by rw [← mul_assoc, ha2, one_mul, hb2]
    · intro h1
      apply hab
      have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, inv_eq_of_mul_eq_one_right ha2]
  have hBW := card_mul_card_sq_eq_mul ha2 hb2 ha1 hb1 hab hc K
    (Subgroup.mem_normalizer_iff.mpr fun z => (Subgroup.mem_normalizer_iff.mp (hSK haS) z))
    (Subgroup.mem_normalizer_iff.mpr fun z => (Subgroup.mem_normalizer_iff.mp (hSK hbS) z)) hK
  rw [hC a haS ha, hC b hbS hb, hC (a * b) habS hab', Subgroup.card_bot] at hBW
  have : Nat.card K = 1 := by simpa using hBW
  exact Subgroup.card_eq_one.mp this

include h in
theorem card_dvd_four_of_le_normalizer {X R : Subgroup G} (hX : Odd (Nat.card X))
    (hX1 : X ≠ ⊥) (hR : IsPGroup 2 R) (hRX : R ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card R ∣ 4 := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have hS8 : Nat.card (S : Subgroup G) = 8 := h.card_sylow' S
  have hdvd : Nat.card R ∣ 8 := hS8 ▸ Subgroup.card_dvd_of_le hRS
  rw [hn] at hdvd ⊢
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have : 2 ^ 4 ∣ 8 := (pow_dvd_pow 2 (by omega)).trans hdvd
    revert this
    decide
  by_cases hn3' : n = 3
  · exfalso
    subst hn3'
    have hRS' : R = (S : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hRS (by rw [hS8, hn]; norm_num)
    exact hX1 (h.eq_bot_of_sylow_le_normalizer S hX (hRS' ▸ hRX))
  · exact (pow_dvd_pow 2 (show n ≤ 2 by omega)).trans (by norm_num)

end JankoHyp

end CFSG.Walter.J1
