module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.KG1468

open CFSG.Open CFSG.Quasithin

variable {X : Type} [Group X] [Finite X]

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_oTwoUpper_of_A5 {H : Subgroup X}
    (hA5 : Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* alternatingGroup (Fin 5))) :
    ∃ a : ℕ, Nat.card (oTwoUpper H) = 60 * 2 ^ a ∧
      Nat.card (pCoreOf 2 (oTwoUpper H)) = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA5
  have hR : IsPGroup 2 (CFSG.pCore 2 ↥(oTwoUpper H)) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR
  have hc := (CFSG.pCore 2 ↥(oTwoUpper H)).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, card_alt5, ha] at hc
  refine ⟨a, hc, ?_⟩
  have h1 : Nat.card (pCoreOf 2 (oTwoUpper H)) = Nat.card (Open.pCore 2 ↥(oTwoUpper H)) :=
    Subgroup.card_map_of_injective (oTwoUpper H).subtype_injective
  rw [h1, ha]

theorem dvd_fifteen_of_A5 {H : Subgroup X}
    (hA5 : Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* alternatingGroup (Fin 5)))
    {q e : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ^ e ∣ Nat.card H) : q ^ e ∣ 15 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha, -⟩ := card_oTwoUpper_of_A5 hA5
  obtain ⟨Qs, hQs⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
  have hle : Qs.map H.subtype ≤ oTwoUpper H := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.subset_closure ⟨y.2, ?_⟩
    have h1 : orderOf (H.subtype y) = orderOf y := Subgroup.orderOf_coe y
    rw [h1]
    have h2 : orderOf y ∣ q ^ e := by
      have := Subgroup.orderOf_dvd_natCard Qs hy
      rwa [hQs] at this
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hq).1 h2
    rw [hi]
    exact (hq.odd_of_ne_two hq2).pow
  have h1 : q ^ e ∣ Nat.card (oTwoUpper H) := by
    rw [← hQs, ← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  rw [ha] at h1
  have hcop : Nat.Coprime (q ^ e) (2 ^ a) :=
    Nat.Coprime.pow e a ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have h2 : q ^ e ∣ 60 := hcop.dvd_of_dvd_mul_right h1
  have hcop4 : Nat.Coprime (q ^ e) 4 :=
    Nat.Coprime.pow_left e (show Nat.Coprime q (2 ^ 2) from
      Nat.Coprime.pow_right 2 ((Nat.coprime_primes hq Nat.prime_two).mpr hq2))
  exact hcop4.dvd_of_dvd_mul_left (by simpa [show (60 : ℕ) = 4 * 15 by norm_num] using h2)

theorem five_dvd_of_A5 {H : Subgroup X}
    (hA5 : Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* alternatingGroup (Fin 5))) :
    5 ∣ Nat.card H := by
  obtain ⟨a, ha, -⟩ := card_oTwoUpper_of_A5 hA5
  have h1 : Nat.card (oTwoUpper H) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le (CFSG.Quasithin.oTwoUpper_le H)
  rw [ha] at h1
  exact dvd_trans (dvd_mul_of_dvd_left (by norm_num : 5 ∣ 60) _) h1

omit [Finite X] in
theorem card_inf_mul_relIndex (A C : Subgroup X) :
    Nat.card ↥(A ⊓ C) * (A ⊓ C).relIndex A = Nat.card A := by
  have h := Subgroup.card_mul_index ((A ⊓ C).subgroupOf A)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h

theorem exists_mem_center_of_normal {R A : Subgroup X} (hR : IsPGroup 2 R) (hAR : A ≤ R)
    (hAN : R ≤ Subgroup.normalizer (A : Set X)) (hA : A ≠ ⊥) :
    ∃ c ∈ A, c ≠ 1 ∧ ∀ r ∈ R, r * c = c * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  let A' : Subgroup R := A.subgroupOf R
  have hA'n : A'.Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hAN g.2) a).mp ha⟩
  have hA'ne : A' ≠ ⊥ := by
    intro h
    apply hA
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAR ha⟩ : R) ∈ A' := ha
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨⟨⟨c, hcR⟩, hc⟩, hc1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hA'ne)
  have hcA : (⟨c, hcR⟩ : R) ∈ A' := (Subgroup.mem_inf.mp hc).1
  have hcZ : (⟨c, hcR⟩ : R) ∈ Subgroup.center R := (Subgroup.mem_inf.mp hc).2
  refine ⟨c, hcA, fun h => hc1 (Subtype.ext (Subtype.ext h)), fun r hr => ?_⟩
  have := Subgroup.mem_center_iff.mp hcZ ⟨r, hr⟩
  exact (congrArg Subtype.val this)

theorem not_bigA_of_card_le {K₀ : Subgroup X} (hR : Nat.card (pCoreOf 2 K₀) ≤ 32) :
    ¬ ∃ A : Subgroup X, A ≤ pCoreOf 2 K₀ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      K₀ ≤ Subgroup.normalizer (A : Set X) ∧
      16 ≤ (A ⊓ Subgroup.centralizer (pCoreOf 2 K₀ : Set X)).relIndex A := by
  rintro ⟨A, hAR, hAab, hAN, h16⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (pCoreOf 2 K₀) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀
  have hRK : pCoreOf 2 K₀ ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hmul := card_inf_mul_relIndex A (Subgroup.centralizer (pCoreOf 2 K₀ : Set X))
  by_cases hA1 : A = ⊥
  · subst hA1
    rw [Subgroup.relIndex_bot_right] at h16
    omega
  obtain ⟨c, hcA, hc1, hcZ⟩ := exists_mem_center_of_normal hR2 hAR (hRK.trans hAN) hA1
  have hcC : c ∈ A ⊓ Subgroup.centralizer (pCoreOf 2 K₀ : Set X) :=
    Subgroup.mem_inf.mpr ⟨hcA, Subgroup.mem_centralizer_iff.mpr hcZ⟩
  have h2C : 2 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (pCoreOf 2 K₀ : Set X)) := by
    have hnt : Nontrivial ↥(A ⊓ Subgroup.centralizer (pCoreOf 2 K₀ : Set X)) :=
      ⟨⟨1, ⟨c, hcC⟩, fun h => hc1 (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card
  have hAcard : Nat.card A ≤ Nat.card (pCoreOf 2 K₀) := Subgroup.card_le_of_le hAR
  have h32 : 32 ≤ Nat.card A := by nlinarith
  have hAeq : A = pCoreOf 2 K₀ := Subgroup.eq_of_le_of_card_ge hAR (by omega)
  have hCA : A ⊓ Subgroup.centralizer (pCoreOf 2 K₀ : Set X) = A := by
    refine inf_eq_left.mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
    exact hAab r (hAeq ▸ hr) a ha
  rw [hCA, Subgroup.relIndex_self] at h16
  omega

omit [Finite X] in
theorem le_normalizer_oTwoUpper (H : Subgroup X) :
    H ≤ Subgroup.normalizer (oTwoUpper H : Set X) := by
  have key : ∀ g ∈ H, ∀ y ∈ oTwoUpper H, g * y * g⁻¹ ∈ oTwoUpper H := by
    intro g hg y hy
    have hle : oTwoUpper H ≤ (oTwoUpper H).comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact H.mul_mem (H.mul_mem hg hz.1) (H.inv_mem hg)
      · show Odd (orderOf (MulAut.conj g z))
        rw [MulEquiv.orderOf_eq]
        exact hz.2
    exact hle hy
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key h hh y
  · intro hy
    have := key h⁻¹ (H.inv_mem hh) _ hy
    simpa [mul_assoc] using this

theorem pCoreOf_oTwoUpper_le (H : Subgroup X) :
    pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Open.pCore 2 ↥(oTwoUpper H)).Characteristic :=
    CFSG.LieType.BorelTits.pCore_characteristic 2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (CFSG.Quasithin.oTwoUpper_le H))
    ((le_normalizer_oTwoUpper H).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem not_A5_of_card {H : Subgroup X}
    (h : ¬ 5 ∣ Nat.card H ∨ 9 ∣ Nat.card H ∨ 7 ∣ Nat.card H ∨ 11 ∣ Nat.card H) :
    ¬ Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  rcases h with h | h | h | h
  · exact h (five_dvd_of_A5 hA5)
  · have := dvd_fifteen_of_A5 hA5 (q := 3) (e := 2) Nat.prime_three (by norm_num) (by simpa using h)
    norm_num at this
  · have := dvd_fifteen_of_A5 hA5 (q := 7) (e := 1) (by norm_num) (by norm_num) (by simpa using h)
    norm_num at this
  · have := dvd_fifteen_of_A5 hA5 (q := 11) (e := 1) (by norm_num) (by norm_num)
      (by simpa using h)
    norm_num at this

theorem card_pCore_le_of_A5 {H : Subgroup X}
    (hA5 : Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* alternatingGroup (Fin 5)))
    (h8 : ¬ 2 ^ 8 ∣ Nat.card X) : Nat.card (pCoreOf 2 (oTwoUpper H)) ≤ 32 := by
  obtain ⟨a, ha, hR⟩ := card_oTwoUpper_of_A5 hA5
  have h1 : Nat.card (oTwoUpper H) ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
  rw [ha] at h1
  have h2 : 2 ^ (a + 2) ∣ Nat.card X := dvd_trans ⟨15, by ring⟩ h1
  have ha5 : a ≤ 5 := by
    by_contra h
    exact h8 (dvd_trans (pow_dvd_pow 2 (by omega)) h2)
  rw [hR]
  calc 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) ha5
    _ = 32 := by norm_num

omit [Finite X] in
theorem relIndex_lt_of_center {Q R A Z : Subgroup X} (hQ64 : Nat.card Q = 64) (hZQ : Z ≤ Q)
    (hZ4 : Nat.card Z = 4) (hZc : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hna : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) (hRQ : R ≤ Q) (hAR : A ≤ R)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    (A ⊓ Subgroup.centralizer (R : Set X)).relIndex A < 16 := by
  have hAQ : A ≤ Q := hAR.trans hRQ
  have hle : A ⊓ Z ≤ A ⊓ Subgroup.centralizer (R : Set X) := fun z hz =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1, Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (hZc z (Subgroup.mem_inf.mp hz).2 r (hRQ hr)).symm⟩
  have hdvd : (A ⊓ Subgroup.centralizer (R : Set X)).relIndex A ∣ (A ⊓ Z).relIndex A :=
    Subgroup.relIndex_dvd_of_le_left A hle
  have hc : (A ⊓ Z).relIndex A = Z.relIndex A := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right Z A
  have hd : Z.relIndex A = (Z.subgroupOf Q).relIndex (A.subgroupOf Q) :=
    (Subgroup.relIndex_subgroupOf hAQ).symm
  set Z' := Z.subgroupOf Q with hZ'
  set A' := A.subgroupOf Q with hA'
  have hZ'c : ∀ z ∈ Z', ∀ q : ↥Q, z * q = q * z := fun z hz q =>
    Subtype.ext (hZc z hz q q.2)
  have hZ'n : Z'.Normal := ⟨fun z hz g => by
    rw [← hZ'c z hz g, mul_inv_cancel_right]
    exact hz⟩
  have he : Z'.relIndex A' = Z'.relIndex (A' ⊔ Z') := (Subgroup.relIndex_sup_right A' Z').symm
  have hf := Subgroup.relIndex_mul_relIndex Z' (A' ⊔ Z') ⊤ le_sup_right le_top
  have hcardZ : Nat.card Z' = 4 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv, hZ4]
  have hZ'top : Z'.relIndex ⊤ = 16 := by
    rw [Subgroup.relIndex_top_right]
    have h1 := Subgroup.card_mul_index Z'
    rw [hcardZ, hQ64] at h1
    omega
  have hne : (A' ⊔ Z').relIndex ⊤ ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_top_right, Subgroup.index_eq_one] at h1
    have hmem : ∀ q : ↥Q, ∃ a ∈ A', ∃ z ∈ Z', a * z = q := by
      intro q
      have hq : q ∈ ((A' ⊔ Z' : Subgroup ↥Q) : Set ↥Q) := by rw [h1]; trivial
      rw [Subgroup.mul_normal] at hq
      obtain ⟨a, ha, z, hz, rfl⟩ := hq
      exact ⟨a, ha, z, hz, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    apply hab
    obtain ⟨a₁, ha₁, z₁, hz₁, he₁⟩ := hmem ⟨a, ha⟩
    obtain ⟨a₂, ha₂, z₂, hz₂, he₂⟩ := hmem ⟨b, hb⟩
    have haa : a₁ * a₂ = a₂ * a₁ := Subtype.ext (hAab _ ha₁ _ ha₂)
    have key : a₁ * z₁ * (a₂ * z₂) = a₂ * z₂ * (a₁ * z₁) := by
      calc a₁ * z₁ * (a₂ * z₂) = a₁ * (z₁ * a₂) * z₂ := by simp only [mul_assoc]
        _ = a₁ * (a₂ * z₁) * z₂ := by rw [hZ'c z₁ hz₁ a₂]
        _ = a₁ * a₂ * (z₁ * z₂) := by simp only [mul_assoc]
        _ = a₂ * a₁ * (z₂ * z₁) := by rw [haa, hZ'c z₁ hz₁ z₂]
        _ = a₂ * (a₁ * z₂) * z₁ := by simp only [mul_assoc]
        _ = a₂ * (z₂ * a₁) * z₁ := by rw [hZ'c z₂ hz₂ a₁]
        _ = a₂ * z₂ * (a₁ * z₁) := by simp only [mul_assoc]
    rw [he₁, he₂] at key
    exact congrArg Subtype.val key
  rw [hZ'top] at hf
  have hpos' : Z'.relIndex (A' ⊔ Z') ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hf
    omega
  have h8 : Z'.relIndex (A' ⊔ Z') ≤ 8 := by
    have h2 : 2 ≤ (A' ⊔ Z').relIndex ⊤ := by
      rcases Nat.lt_or_ge ((A' ⊔ Z').relIndex ⊤) 2 with h | h
      · interval_cases h3 : (A' ⊔ Z').relIndex ⊤
        · rw [mul_zero] at hf
          omega
        · exact absurd rfl hne
      · exact h
    nlinarith
  rw [hc, hd, he] at hdvd
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos') hdvd
  omega

omit [Finite X] in
theorem center_four_of_isZ4StarExtra2 {V : Subgroup X} (hV : IsZ4StarExtra2 ↥V) :
    (∃ Z : Subgroup X, Z ≤ V ∧ Nat.card Z = 4 ∧ ∀ z ∈ Z, ∀ q ∈ V, z * q = q * z) ∧
      ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a := by
  obtain ⟨Z, E, hZ4, -, hE, hZc, -, -⟩ := hV
  refine ⟨⟨Z.map V.subtype, Subgroup.map_subtype_le Z, by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hZ4], ?_⟩, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ q hq
    have := Subgroup.mem_center_iff.mp (hZc hz) ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  · by_contra hcon
    have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b => by
      by_contra h
      exact hcon ⟨a.1, a.1.2, b.1, b.1.2, fun h' =>
        h (Subtype.ext (Subtype.ext h'))⟩
    have hEc : Subgroup.center ↥E = ⊤ := eq_top_iff.mpr fun g _ =>
      Subgroup.mem_center_iff.mpr fun h => hcomm h g
    have hnt := hE.1.quotient_nontrivial
    rw [hEc] at hnt
    have : Subsingleton (↥E ⧸ (⊤ : Subgroup ↥E)) := QuotientGroup.subsingleton_quotient_top
    exact not_nontrivial_iff_subsingleton.mpr this hnt

abbrev Bad (x : X) : Prop :=
  Nonempty (↥(oTwoUpper (Subgroup.centralizer ({x} : Set X))) ⧸
      CFSG.pCore 2 ↥(oTwoUpper (Subgroup.centralizer ({x} : Set X))) ≃*
        alternatingGroup (Fin 5)) ∧
    ∃ A : Subgroup X, A ≤ pCoreOf 2 (oTwoUpper (Subgroup.centralizer ({x} : Set X))) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      oTwoUpper (Subgroup.centralizer ({x} : Set X)) ≤ Subgroup.normalizer (A : Set X) ∧
      16 ≤ (A ⊓ Subgroup.centralizer
        (pCoreOf 2 (oTwoUpper (Subgroup.centralizer ({x} : Set X))) : Set X)).relIndex A

theorem not_bad_of_two_part (h8 : ¬ 2 ^ 8 ∣ Nat.card X) (x : X) : ¬ Bad x := fun ⟨hA5, hA⟩ =>
  not_bigA_of_card_le (card_pCore_le_of_A5 hA5 h8) hA

theorem not_bad_of_card {x : X}
    (h : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) ∨
      9 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) ∨
      7 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) ∨
      11 ∣ Nat.card (Subgroup.centralizer ({x} : Set X))) : ¬ Bad x := fun hb =>
  not_A5_of_card h hb.1

end CFSG.Quasithin.H13.KG1468
