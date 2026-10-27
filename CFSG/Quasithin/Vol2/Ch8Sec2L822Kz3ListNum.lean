module

public import CFSG.Quasithin.EmptyFaithful.S146zXGOrder
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Adapters.StatedClassicalOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem dvd_prime_of_card_form_kz3 {N p : ℕ} (hN : ∃ a : ℕ, N = 2 ^ a * 360 ∨ N = 2 ^ a * 1080)
    (hp : p.Prime) (hpN : p ∣ N) : p = 2 ∨ p = 3 ∨ p = 5 := by
  have h2 : p ∣ 2 ^ 3 * 3 ^ 2 * 5 → p = 2 ∨ p = 3 ∨ p = 5 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
  have h3 : p ∣ 2 ^ 3 * 3 ^ 3 * 5 → p = 2 ∨ p = 3 ∨ p = 5 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
  obtain ⟨a, ha | ha⟩ := hN
  · rw [ha] at hpN
    rcases (Nat.Prime.dvd_mul hp).1 hpN with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact h2 (by norm_num; exact h)
  · rw [ha] at hpN
    rcases (Nat.Prime.dvd_mul hp).1 hpN with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact h3 (by norm_num; exact h)

theorem card_isHat_kz3 {X S : Type} [Group X] [Group S] (h : IsHat X S) :
    Nat.card X = 3 * Nat.card S := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hZ,
    Nat.card_congr e.toEquiv, mul_comm]

theorem card_isE2_kz3 {n : ℕ} {V : Type} [Group V] (h : IsE2 n V) : Nat.card V = 2 ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin n → ZMod 2) = 2 ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_isZ4Cubed_kz3 {V : Type} [Group V] (h : IsZ4Cubed V) : Nat.card V = 64 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → ZMod 4) = 64
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem two_pow_card_isZ4StarExtra2_kz3 {V : Type} [Group V] [Finite V] (h : IsZ4StarExtra2 V) :
    ∃ k : ℕ, Nat.card V = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ, -, hE, hZc, hZE, -⟩ := h
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hp : IsPGroup 2 ↥(Z ⊔ E) :=
    IsPGroup.to_sup_of_normal_left (IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num))
      (IsPGroup.of_card hE.2)
  rw [hZE] at hp
  exact IsPGroup.iff_card.mp (hp.of_equiv Subgroup.topEquiv)

theorem two_mul_card_alternatingGroup_kz3 (n : ℕ) (hn : 2 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [two_mul_nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

theorem card_alternatingGroup_five_kz3 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h : 2 * Nat.card (alternatingGroup (Fin 5)) = 120 := by
    rw [two_mul_card_alternatingGroup_kz3 5 (by norm_num)]
    rfl
  omega

theorem card_alternatingGroup_seven_kz3 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h : 2 * Nat.card (alternatingGroup (Fin 7)) = 5040 := by
    rw [two_mul_card_alternatingGroup_kz3 7 (by norm_num)]
    rfl
  omega

theorem card_isAlt_kz3 {n : ℕ} {X : Type} [Group X] (h : IsAlt n X) :
    Nat.card X = Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr e.toEquiv

theorem psl_two_two_ne_kz3 (m : ℕ)
    (h : 2 ^ m * ((2 ^ m) ^ 2 - 1) = 360 ∨ 2 ^ m * ((2 ^ m) ^ 2 - 1) = 1080) : False := by
  rcases Nat.lt_or_ge m 4 with hm | hm
  · interval_cases m <;> norm_num at h
  · have h16 : 16 ≤ 2 ^ m := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h256 : 256 ≤ (2 ^ m) ^ 2 := by nlinarith
    have h1 : 255 ≤ (2 ^ m) ^ 2 - 1 := by omega
    have h2 : 16 * 255 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul h16 h1
    rcases h with h | h <;> rw [h] at h2 <;> norm_num at h2

theorem card_ge_of_isSz_kz3 {f : ℕ} {X : Type} [Group X] (h : IsSz f X) :
    29120 ≤ Nat.card X := by
  obtain ⟨a, ha, hf, hc⟩ := CFSG.Quasithin.S146zX.card_isSz h
  rw [hc]
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h64 : 64 ≤ (2 ^ f) ^ 2 := by nlinarith
  have h7 : 7 ≤ 2 ^ f - 1 := by omega
  have h65 : 65 ≤ (2 ^ f) ^ 2 + 1 := by omega
  calc 29120 = 65 * 64 * 7 := by norm_num
    _ ≤ ((2 ^ f) ^ 2 + 1) * (2 ^ f) ^ 2 * (2 ^ f - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h65 h64) h7

theorem two_and_seventeen_dvd_card_psp_kz3 {E : Type} [Group E] {m : ℕ}
    (h : StatedClassicalModel E .PSp 2 2 m) (hm : Even m) :
    2 ∣ Nat.card E ∧ 17 ∣ Nat.card E := by
  have hm1 : 1 ≤ m := h.1.2.1
  have hc : Nat.card E = ordBC 2 (2 ^ m) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  obtain ⟨r, rfl⟩ := hm
  have hr : 1 ≤ r := by omega
  set q : ℕ := 2 ^ (r + r) with hq
  have hq2 : 2 ∣ q := dvd_pow_self 2 (by omega)
  have hgcd : Nat.gcd 2 (q - 1) = 1 := by
    have hodd : Odd (q - 1) := by
      obtain ⟨j, hj⟩ := hq2
      have hq2' : 2 ≤ q := by
        rw [hq]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (r + r) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨j - 1, by omega⟩
    exact Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)
  have hfor : ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    unfold ordBC
    rw [hgcd, Nat.div_one, Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 2), Finset.Icc_self,
      Finset.prod_singleton]
  have h17 : 17 ∣ q ^ 4 - 1 := by
    have hq4 : q ^ 4 = (2 ^ 8) ^ r := by
      rw [hq, ← pow_mul, ← pow_mul]
      ring_nf
    have hdvd : 2 ^ 8 - 1 ∣ (2 ^ 8) ^ r - 1 := Nat.sub_one_dvd_pow_sub_one (2 ^ 8) r
    rw [hq4]
    exact Nat.dvd_trans (by norm_num) hdvd
  refine ⟨?_, ?_⟩
  · rw [hc, hfor]
    exact Dvd.dvd.mul_right (Dvd.dvd.pow hq2 (by norm_num)) _
  · rw [hc, hfor]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h17 _) _

theorem card_statedSL_three_zmod_three_kz3 : Nat.card (StatedSL 3 (ZMod 3)) = 5616 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (by norm_num : 1 ≤ 3), Nat.card_zmod]
  norm_num [Finset.prod_Icc_succ_top]

theorem central_conj_kz3 {X : Type} [Group X] {z : X} (hz : z ∈ Subgroup.center X) (g : X) :
    z * g * z⁻¹ = g := by
  have := Subgroup.mem_center_iff.mp hz g
  rw [← this, mul_assoc, mul_inv_cancel, mul_one]

theorem commutatorElement_mul_central_left_kz3 {X : Type} [Group X] {y w z : X}
    (hz : z ∈ Subgroup.center X) : ⁅y * z, w⁆ = ⁅y, w⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc y * z * w * (y * z)⁻¹ * w⁻¹ = y * (z * w * z⁻¹) * y⁻¹ * w⁻¹ := by group
    _ = y * w * y⁻¹ * w⁻¹ := by rw [central_conj_kz3 hz]

theorem commutatorElement_mul_central_right_kz3 {X : Type} [Group X] {y w z : X}
    (hz : z ∈ Subgroup.center X) : ⁅y, w * z⁆ = ⁅y, w⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc y * (w * z) * y⁻¹ * (w * z)⁻¹ = y * w * (z * y⁻¹ * z⁻¹) * w⁻¹ := by group
    _ = y * w * y⁻¹ * w⁻¹ := by rw [central_conj_kz3 hz]

theorem oddCore_le_center_kz3 {X : Type} [Group X] [Finite X]
    (hc : commutator X = ⊤) (hs : IsSimpleGroup (X ⧸ Subgroup.center X))
    (hev : Even (Nat.card X)) : CFSG.oddCore X ≤ Subgroup.center X := by
  have hOodd : Odd (Nat.card (CFSG.oddCore X)) := CFSG.Quasithin.A312.odd_card_oddCore X
  have hN : (CFSG.oddCore X ⊔ Subgroup.center X).Normal := inferInstance
  have hM : ((CFSG.oddCore X ⊔ Subgroup.center X).map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal
      ((CFSG.oddCore X ⊔ Subgroup.center X).map (QuotientGroup.mk' (Subgroup.center X))) with
    hbot | htop
  · intro x hx
    have hxN : x ∈ CFSG.oddCore X ⊔ Subgroup.center X := Subgroup.mem_sup_left hx
    have hmem : QuotientGroup.mk' (Subgroup.center X) x ∈
        (CFSG.oddCore X ⊔ Subgroup.center X).map (QuotientGroup.mk' (Subgroup.center X)) :=
      Subgroup.mem_map_of_mem _ hxN
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · exfalso
    have hall : ∀ g : X, g ∈ CFSG.oddCore X ⊔ Subgroup.center X := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center X) g ∈
          (CFSG.oddCore X ⊔ Subgroup.center X).map (QuotientGroup.mk' (Subgroup.center X)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      have hrel : y⁻¹ * g ∈ Subgroup.center X := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyg
        exact hyg
      have hgeq : g = y * (y⁻¹ * g) := by group
      rw [hgeq]
      exact (CFSG.oddCore X ⊔ Subgroup.center X).mul_mem hy (Subgroup.mem_sup_right hrel)
    have hcomm : commutator X ≤ CFSG.oddCore X := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨y, hy, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_left).mp (hall a)
      obtain ⟨y', hy', z', hz', rfl⟩ := (Subgroup.mem_sup_of_normal_left).mp (hall b)
      rw [commutatorElement_mul_central_left_kz3 hz, commutatorElement_mul_central_right_kz3 hz']
      rw [commutatorElement_def]
      have h1 : y * y' * y⁻¹ ∈ CFSG.oddCore X :=
        Subgroup.Normal.conj_mem inferInstance y' hy' y
      exact (CFSG.oddCore X).mul_mem h1 ((CFSG.oddCore X).inv_mem hy')
    have hOtop : CFSG.oddCore X = ⊤ := by
      rw [eq_top_iff, ← hc]
      exact hcomm
    have hcardO : Nat.card (CFSG.oddCore X) = Nat.card X := by
      rw [hOtop]
      exact Subgroup.card_top
    rw [hcardO] at hOodd
    exact (Nat.not_even_iff_odd.mpr hOodd) hev

theorem commutator_map_kz3 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (commutator X).map (e.toMonoidHom) = commutator Y := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem isQuasisimple_of_mulEquiv_kz3 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple Y := by
  obtain ⟨hp, hs, a, b, hab⟩ := h
  have hcY : commutator Y = ⊤ := by
    rw [← commutator_map_kz3 e, hp.commutator_eq_top,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hZ : (Subgroup.center X).map (e.toMonoidHom) = Subgroup.center Y :=
    Subgroup.map_center_eq e
  let e' : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y := QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e hZ
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hs
  have hsY : IsSimpleGroup (Y ⧸ Subgroup.center Y) := MulEquiv.isSimpleGroup e'.symm
  exact ⟨⟨hcY⟩, hsY, e' a, e' b, fun h => hab (e'.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem nonquasi_false_kz3 {Gq : Type} [Group Gq] [Finite Gq] {B Q : Subgroup Gq}
    (hQ : CFSG.IsQuasisimple ↥Q) (hev : Even (Nat.card ↥Q)) (h : A312Nonquasi B Q) : False := by
  have hc : commutator ↥Q = ⊤ := hQ.1.commutator_eq_top
  have hs : IsSimpleGroup (↥Q ⧸ Subgroup.center ↥Q) := hQ.2.1
  have hOc := oddCore_le_center_kz3 hc hs hev
  have hOL : ⁅(CFSG.oddCore ↥Q).map Q.subtype, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hyc : y ∈ Subgroup.center ↥Q := hOc hy
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨g, hg⟩)
    simpa using this
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1 hOL
  · exact h1 hOL

end CFSG.Quasithin.H13
