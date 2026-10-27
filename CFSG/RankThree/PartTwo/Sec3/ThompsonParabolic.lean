module

public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
public import CFSG.RankThree.PartTwo.Sec3.SectionModuleBound

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def pOne (T P : Subgroup G) : Subgroup G :=
  sSup {A₁ | A₁ ∈ famG T 1 ∧ A₁ ≤ P}

omit [Finite G] in
theorem pOne_le (T P : Subgroup G) : pOne T P ≤ P := sSup_le fun _ h => h.2

omit [Finite G] in
theorem pOne_le_jG (T P : Subgroup G) : pOne T P ≤ jG T 1 := sSup_le fun _ h => le_jG h.1

omit [Finite G] in
theorem le_pOne {T P A₁ : Subgroup G} (h : A₁ ∈ famG T 1) (hP : A₁ ≤ P) : A₁ ≤ pOne T P :=
  le_sSup ⟨h, hP⟩

omit [Finite G] in
theorem conj_mem_pOne {T P : Subgroup G} (hPT : P ≤ T) {g : G}
    (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) {x : G} (hx : x ∈ pOne T P) : g * x * g⁻¹ ∈ pOne T P := by
  have hle : (pOne T P).map (MulAut.conj g).toMonoidHom ≤ pOne T P := by
    rw [pOne, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    refine iSup₂_le fun A hA => le_sSup ⟨map_conj_mem_famG hA.1 g
      (fun a ha => hPT (hgP a (hA.2 ha))), ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hgP a (hA.2 ha)
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_mem_omegaG {J : Subgroup G} {g : G} (hg : ∀ x ∈ J, g * x * g⁻¹ ∈ J)
    (hg' : ∀ x ∈ J, g⁻¹ * x * g ∈ J) {z : G} (hz : z ∈ omegaG J) : g * z * g⁻¹ ∈ omegaG J := by
  obtain ⟨hzJ, hzc, hz2⟩ := hz
  refine ⟨hg z hzJ, fun x hx => ?_, ?_⟩
  · have h := hzc _ (hg' x hx)
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [h]
      _ = x * (g * z * g⁻¹) := by group
  · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]

theorem mem_omegaG_pOne {T P A₁ : Subgroup G} (hr : 2 ≤ CFSG.pRank 2 T)
    (hA₁ : A₁ ∈ famG T 1) (hA₁P : A₁ ≤ P) (hPT : P ≤ T) {e : G} (he : e ∈ omegaG (jG T 1))
    (heP : e ∈ P) : e ∈ omegaG (pOne T P) := by
  obtain ⟨heJ, hec, he2⟩ := he
  refine ⟨?_, fun x hx => hec x (pOne_le_jG T P hx), he2⟩
  by_cases heA : e ∈ A₁
  · exact le_pOne hA₁ hA₁P heA
  obtain ⟨hA₁T, hA₁2, hA₁card⟩ := hA₁
  have hpow : 2 ^ (CFSG.pRank 2 T - 2) ∣ Nat.card A₁ := by
    rw [hA₁card]
    exact Nat.pow_dvd_pow 2 (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hpow
  set K := K'.map A₁.subtype with hKdef
  have hKA : K ≤ A₁ := Subgroup.map_subtype_le K'
  have hKcard : Nat.card K = 2 ^ (CFSG.pRank 2 T - 2) := by
    rw [hKdef, Subgroup.card_map_of_injective A₁.subtype_injective, hK']
  have he1 : e ≠ 1 := fun h => heA (h ▸ A₁.one_mem)
  have hzp : Nat.card (Subgroup.zpowers e) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact he2) he1
  have hcomm : ∀ k ∈ K, ∀ l ∈ Subgroup.zpowers e, k * l = l * k := by
    intro k hk l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    exact ((Commute.zpow_left (hec k (le_jG ⟨hA₁T, hA₁2, hA₁card⟩ (hKA hk))) n).symm).eq
  have hinf : K ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxe⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [Subgroup.mem_bot]
    have he2' : e ^ 2 = 1 := by rw [pow_two]; exact he2
    have hmod : e ^ n = e ^ (n % (2 : ℕ)) := zpow_eq_zpow_emod' n he2'
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · exfalso
      apply heA
      have : e ^ n = e := by
        rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
      rw [← this]
      exact hKA hxK
  have hDcard : Nat.card ↥(K ⊔ Subgroup.zpowers e) = 2 ^ (CFSG.pRank 2 T - 1) := by
    have h := card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one, hKcard, hzp] at h
    rw [h, ← pow_succ]
    congr 1
    omega
  have hD : K ⊔ Subgroup.zpowers e ∈ famG T 1 := by
    refine ⟨sup_le (hKA.trans hA₁T) ((Subgroup.zpowers_le).mpr (hPT heP)), ?_, hDcard⟩
    refine isElemTwo_sup ⟨fun a ha b hb => hA₁2.1 a (hKA ha) b (hKA hb),
      fun a ha => hA₁2.2 a (hKA ha)⟩ ⟨fun a ha b hb => ?_, fun a ha => ?_⟩ hcomm
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_add, ← two_mul, zpow_mul, show e ^ (2 : ℤ) = 1 by
        rw [zpow_two]; exact he2, one_zpow]
  have hDP : K ⊔ Subgroup.zpowers e ≤ P :=
    sup_le (hKA.trans hA₁P) ((Subgroup.zpowers_le).mpr heP)
  exact le_pOne hD hDP (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))

theorem mem_of_stabilizes {H P W Q : Subgroup G} (hP2 : IsPGroup 2 P) (hWP : W ≤ P)
    (hQP : Q ≤ P) (hCQ : centralizer (Q : Set G) ≤ Q) (hQ2 : IsPGroup 2 Q)
    (hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) (hHW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K →
      K ≤ P)
    {k : G} (hkH : k ∈ H) (hkW : ∀ w ∈ W, k * w * k⁻¹ = w)
    (hkP : ∀ p ∈ P, k * p * k⁻¹ * p⁻¹ ∈ W) : k ∈ P := by
  let K : Subgroup G :=
    { carrier := {h | h ∈ H ∧ (∀ w ∈ W, h * w * h⁻¹ = w) ∧ ∀ p ∈ P, h * p * h⁻¹ * p⁻¹ ∈ W}
      one_mem' := ⟨H.one_mem, fun w _ => by group, fun p _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact W.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haH, haW, haP⟩ ⟨hbH, hbW, hbP⟩
        refine ⟨H.mul_mem haH hbH, fun w hw => ?_, fun p hp => ?_⟩
        · calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
            _ = w := by rw [hbW w hw, haW w hw]
        · have h1 := hbP p hp
          have h2 := haP p hp
          have h3 : a * (b * p * b⁻¹ * p⁻¹) * a⁻¹ = b * p * b⁻¹ * p⁻¹ := haW _ h1
          rw [show a * b * p * (a * b)⁻¹ * p⁻¹ =
              a * (b * p * b⁻¹ * p⁻¹) * a⁻¹ * (a * p * a⁻¹ * p⁻¹) by group, h3]
          exact W.mul_mem h1 h2
      inv_mem' := by
        rintro a ⟨haH, haW, haP⟩
        refine ⟨H.inv_mem haH, fun w hw => ?_, fun p hp => ?_⟩
        · have hw' : a⁻¹ * w * a ∈ W := by
            have := hHW a⁻¹ (H.inv_mem haH) w hw
            rwa [inv_inv] at this
          have := haW _ hw'
          calc a⁻¹ * w * a⁻¹⁻¹ = a⁻¹ * w * a := by group
            _ = a * (a⁻¹ * w * a) * a⁻¹ := this.symm
            _ = w := by group
        · have hp' : a⁻¹ * p * a ∈ P := by
            have := hHP a⁻¹ (H.inv_mem haH) p hp
            rwa [inv_inv] at this
          have h1 := haP _ hp'
          have : a⁻¹ * p * a⁻¹⁻¹ * p⁻¹ = (a * (a⁻¹ * p * a) * a⁻¹ * (a⁻¹ * p * a)⁻¹)⁻¹ := by
            group
          rw [this]
          exact W.inv_mem h1 }
  have hKH : K ≤ H := fun h hh => hh.1
  have hKn : ∀ h ∈ H, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    rintro g hg x ⟨hxH, hxW, hxP⟩
    refine ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), fun w hw => ?_, fun p hp => ?_⟩
    · have hw' : g⁻¹ * w * g ∈ W := by
        have := hHW g⁻¹ (H.inv_mem hg) w hw
        rwa [inv_inv] at this
      calc g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ := by group
        _ = w := by rw [hxW _ hw']; group
    · have hp' : g⁻¹ * p * g ∈ P := by
        have := hHP g⁻¹ (H.inv_mem hg) p hp
        rwa [inv_inv] at this
      have h1 := hHW g hg _ (hxP _ hp')
      have : g * x * g⁻¹ * p * (g * x * g⁻¹)⁻¹ * p⁻¹ =
          g * (x * (g⁻¹ * p * g) * x⁻¹ * (g⁻¹ * p * g)⁻¹) * g⁻¹ := by group
      rw [this]
      exact h1
  have hK2 : IsPGroup 2 K := by
    intro x
    have hne : orderOf (x : G) ≠ 0 := (orderOf_pos (x : G)).ne'
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hne
    set y : G := (x : G) ^ (2 ^ a) with hydef
    have hyK : y ∈ K := K.pow_mem x.2 _
    have hyord : orderOf y = m := by
      rw [hydef, orderOf_pow' _ (by positivity), hord, Nat.gcd_mul_right_left]
      rw [Nat.mul_div_cancel_left _ (by positivity)]
    have hycent : ∀ p ∈ P, y * p * y⁻¹ = p := fun p hp =>
      commute_of_odd_of_stabilizes hP2 hWP (by rw [hyord]; exact hm) hyK.2.2 hyK.2.1 hp
    have hyQ : y ∈ Q := by
      apply hCQ
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have := hycent q (hQP hq)
      calc q * y = y * q * y⁻¹ * y := by rw [this]
        _ = y * q := by group
    obtain ⟨j, hj⟩ := hQ2 ⟨y, hyQ⟩
    have hyj : y ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hdvd : m ∣ 2 ^ j := hyord ▸ orderOf_dvd_of_pow_eq_one hyj
    have hm1 : m = 1 := by
      have hcop : Nat.Coprime m (2 ^ j) :=
        Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm)
      exact Nat.Coprime.eq_one_of_dvd hcop hdvd
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hydef]
    rw [← orderOf_eq_one_iff, hyord, hm1]
  exact hO2 K hKH hKn hK2 ⟨hkH, hkW, hkP⟩

section Parabolic

variable {T Q H P X A₁ : Subgroup G}
  (hQT : Q ≤ T) (hQP : Q ≤ P) (hPT : P ≤ T) (hP2 : IsPGroup 2 P) (hQ2 : IsPGroup 2 Q)
  (hCQ : centralizer (Q : Set G) ≤ Q) (hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P)
  (hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K →
    K ≤ P)
  (hEH : omegaG (jG T 1) ≤ H)
  (hEn : ∀ t ∈ T, ∀ e ∈ omegaG (jG T 1), t * e * t⁻¹ ∈ omegaG (jG T 1))
  (hr : 2 ≤ CFSG.pRank 2 T) (hA₁ : A₁ ∈ famG T 1) (hA₁P : A₁ ≤ P)

omit [Finite G] in
include hPT in
theorem conj_mem_omegaG_pOne {g : G} (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (hg' : ∀ p ∈ P, g⁻¹ * p * g ∈ P) {w : G} (hw : w ∈ omegaG (pOne T P)) :
    g * w * g⁻¹ ∈ omegaG (pOne T P) :=
  conj_mem_omegaG (fun x hx => conj_mem_pOne hPT hg hx)
    (fun x hx => by
      have := conj_mem_pOne hPT (g := g⁻¹) (fun p hp => by rw [inv_inv]; exact hg' p hp) hx
      rwa [inv_inv] at this) hw

include hQP hPT hP2 hQ2 hCQ hHP hO2 hEH hEn hr hA₁ hA₁P in
theorem omegaG_jG_le : omegaG (jG T 1) ≤ P := by
  intro e he
  have hHW : ∀ h ∈ H, ∀ w ∈ omegaG (pOne T P), h * w * h⁻¹ ∈ omegaG (pOne T P) :=
    fun h hh w hw => conj_mem_omegaG_pOne hPT (hHP h hh)
      (fun p hp => by
        have := hHP h⁻¹ (H.inv_mem hh) p hp
        rwa [inv_inv] at this) hw
  refine mem_of_stabilizes hP2 ((omegaG_le _).trans (pOne_le T P)) hQP hCQ hQ2 hHP hHW hO2
    (hEH he) (fun w hw => ?_) (fun p hp => ?_)
  · have := he.2.1 w (pOne_le_jG T P (omegaG_le _ hw))
    rw [this, mul_inv_cancel_right]
  · have hcE : e * p * e⁻¹ * p⁻¹ ∈ omegaG (jG T 1) := by
      have h1 : p * e⁻¹ * p⁻¹ ∈ omegaG (jG T 1) :=
        hEn p (hPT hp) e⁻¹ ((omegaG (jG T 1)).inv_mem he)
      have : e * p * e⁻¹ * p⁻¹ = e * (p * e⁻¹ * p⁻¹) := by group
      rw [this]
      exact (omegaG (jG T 1)).mul_mem he h1
    have hcP : e * p * e⁻¹ * p⁻¹ ∈ P := P.mul_mem (hHP e (hEH he) p hp) (P.inv_mem hp)
    exact mem_omegaG_pOne hr hA₁ hA₁P hPT hcE hcP

include hQP hPT hP2 hQ2 hCQ hHP hO2 hEH hEn hr hA₁ hA₁P in
theorem not_centralizes_omegaG_pOne
    (hgen : ∀ N : Subgroup G, (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) →
      (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N.Normal)
    (hEnn : ¬ (omegaG (jG T 1)).Normal) :
    ¬ ∀ x ∈ X, ∀ w ∈ omegaG (pOne T P), x * w * x⁻¹ = w := by
  intro hX
  apply hEnn
  apply hgen _ hEn
  intro x hx e he
  have heW : e ∈ omegaG (pOne T P) :=
    mem_omegaG_pOne hr hA₁ hA₁P hPT he
      (omegaG_jG_le hQP hPT hP2 hQ2 hCQ hHP hO2 hEH hEn hr hA₁ hA₁P he)
  rw [hX x hx e heW]
  exact he

end Parabolic

theorem relIndex_centralizer_le_two {T P A : Subgroup G} (hPT : P ≤ T)
    (hA : A ∈ famG T 0) (hAP : A ⊓ P ∈ famG T 1) {t : G} (htA : t ∈ A) :
    (centralizer ({t} : Set G)).relIndex (omegaG (pOne T P)) ≤ 2 := by
  set W := omegaG (pOne T P) with hWdef
  have hAPle : A ⊓ P ≤ pOne T P := le_pOne hAP inf_le_right
  have hcomm : ∀ a ∈ A ⊓ P, ∀ w ∈ W, a * w = w * a := fun a ha w hw =>
    (hw.2.1 a (hAPle ha)).symm
  have hD := card_sup_mul_card_inf_of_commute hcomm
  have hDel : IsElemTwo ((A ⊓ P) ⊔ W) := isElemTwo_sup hAP.2.1 (isElemTwo_omegaG _) hcomm
  have hDT : (A ⊓ P) ⊔ W ≤ T :=
    sup_le (inf_le_left.trans hA.1) ((omegaG_le _).trans ((pOne_le T P).trans hPT))
  have hle := card_le_two_pow_pRank hDT hDel
  rw [hAP.2.2] at hD
  have h2 : 2 ^ CFSG.pRank 2 T ≤ 2 * 2 ^ (CFSG.pRank 2 T - 1) := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : Nat.card W ≤ 2 * Nat.card ↥((A ⊓ P) ⊓ W) := by
    have hpos : 0 < 2 ^ (CFSG.pRank 2 T - 1) := by positivity
    have : 2 ^ (CFSG.pRank 2 T - 1) * Nat.card W ≤
        2 ^ (CFSG.pRank 2 T - 1) * (2 * Nat.card ↥((A ⊓ P) ⊓ W)) := by
      rw [← hD]
      calc Nat.card ↥((A ⊓ P) ⊔ W) * Nat.card ↥((A ⊓ P) ⊓ W)
          ≤ 2 * 2 ^ (CFSG.pRank 2 T - 1) * Nat.card ↥((A ⊓ P) ⊓ W) :=
            Nat.mul_le_mul_right _ (hle.trans h2)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hpos
  have hrel : (A ⊓ P).relIndex W ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ P) (K := W)
    have hpos : 0 < Nat.card ↥((A ⊓ P) ⊓ W) := Nat.card_pos
    have : (A ⊓ P).relIndex W * Nat.card ↥((A ⊓ P) ⊓ W) ≤ 2 * Nat.card ↥((A ⊓ P) ⊓ W) := by
      rw [h]; exact hW
    exact Nat.le_of_mul_le_mul_right this hpos
  have hcent : A ⊓ P ≤ centralizer ({t} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hA.2.1.1 a ha.1 t htA
  exact (Subgroup.relIndex_le_of_le_left hcent (relIndex_ne_zero_of_finite _ _)).trans hrel

omit [Finite G] in
theorem centralizes_of_inv_mod {W Q X : Subgroup G} (hQ2 : IsPGroup 2 Q) {t : G}
    (htW : ∀ w ∈ W, t * w * t⁻¹ = w) (htX : ∀ x ∈ X, t * x * t⁻¹ * x ∈ Q)
    (hX3 : ∀ x ∈ X, x ^ 3 = 1) (hXW : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W) {x : G} (hx : x ∈ X) {w : G} (hw : w ∈ W) :
    x * w * x⁻¹ = w := by
  set q := t * x * t⁻¹ * x with hqdef
  have hq : q ∈ Q := htX x hx
  have htW' : ∀ w ∈ W, t⁻¹ * w * t = w := fun w hw => by
    have := htW w hw
    calc t⁻¹ * w * t = t⁻¹ * (t * w * t⁻¹) * t := by rw [this]
      _ = w := by group
  have hstep : ∀ w ∈ W, x * w * x⁻¹ = q⁻¹ * w * q := by
    intro w hw
    have hx2w : x * x * w * (x * x)⁻¹ ∈ W := by
      have := hXW x hx _ (hXW x hx w hw)
      rw [show x * x * w * (x * x)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ by group]
      exact this
    have hconj : ∀ v ∈ W, (t * x * t⁻¹) * v * (t * x * t⁻¹)⁻¹ = x * v * x⁻¹ := by
      intro v hv
      calc (t * x * t⁻¹) * v * (t * x * t⁻¹)⁻¹ = t * (x * (t⁻¹ * v * t) * x⁻¹) * t⁻¹ := by
            group
        _ = t * (x * v * x⁻¹) * t⁻¹ := by rw [htW' v hv]
        _ = x * v * x⁻¹ := htW _ (hXW x hx v hv)
    have h1 := hconj _ hx2w
    have htx : t * x * t⁻¹ = q * x⁻¹ := by rw [hqdef]; group
    rw [htx] at h1
    have hx3 : x * x * x = 1 := by rw [← pow_three']; exact hX3 x hx
    have e1 : q * x⁻¹ * (x * x * w * (x * x)⁻¹) * (q * x⁻¹)⁻¹ = q * (x * w * x⁻¹) * q⁻¹ := by
      group
    have e2 : x * (x * x * w * (x * x)⁻¹) * x⁻¹ = (x * x * x) * w * (x * x * x)⁻¹ := by group
    rw [e1, e2, hx3, one_mul, inv_one, mul_one] at h1
    calc x * w * x⁻¹ = q⁻¹ * (q * (x * w * x⁻¹) * q⁻¹) * q := by group
      _ = q⁻¹ * w * q := by rw [h1]
  have hiter : ∀ n : ℕ, ∀ w ∈ W, x ^ n * w * (x ^ n)⁻¹ = (q⁻¹) ^ n * w * ((q⁻¹) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      have hq'w : q⁻¹ * w * q⁻¹⁻¹ ∈ W := hQW q⁻¹ (Q.inv_mem hq) w hw
      calc x ^ (n + 1) * w * (x ^ (n + 1))⁻¹ = x ^ n * (x * w * x⁻¹) * (x ^ n)⁻¹ := by
            group
        _ = x ^ n * (q⁻¹ * w * q⁻¹⁻¹) * (x ^ n)⁻¹ := by rw [hstep w hw, inv_inv]
        _ = (q⁻¹) ^ n * (q⁻¹ * w * q⁻¹⁻¹) * ((q⁻¹) ^ n)⁻¹ := ih _ hq'w
        _ = (q⁻¹) ^ (n + 1) * w * ((q⁻¹) ^ (n + 1))⁻¹ := by group
  obtain ⟨k, hk⟩ := hQ2 ⟨q⁻¹, Q.inv_mem hq⟩
  have hqk : (q⁻¹) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have h4 : x ^ (4 ^ k) = x := by
    have hmod : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    rw [← Nat.div_add_mod (4 ^ k) 3, hmod, pow_add, pow_mul, hX3 x hx, one_pow, one_mul,
      pow_one]
  have hq4 : (q⁻¹) ^ (4 ^ k) = 1 := by
    rw [show 4 ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num, pow_mul, hqk, one_pow]
  have := hiter (4 ^ k) w hw
  rwa [h4, hq4, one_mul, inv_one, mul_one] at this

theorem sup_mem_famG {T Q P X A : Subgroup G} (hPT : P ≤ T) (hQ2 : IsPGroup 2 Q)
    (hA : A ∈ famG T 0) (hAP : A ⊓ P ∈ famG T 1) {t : G} (htA : t ∈ A)
    (htX : ∀ x ∈ X, t * x * t⁻¹ * x ∈ Q) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (hXW : ∀ x ∈ X, ∀ w ∈ omegaG (pOne T P), x * w * x⁻¹ ∈ omegaG (pOne T P))
    (hQW : ∀ q ∈ Q, ∀ w ∈ omegaG (pOne T P), q * w * q⁻¹ ∈ omegaG (pOne T P))
    (hXnc : ¬ ∀ x ∈ X, ∀ w ∈ omegaG (pOne T P), x * w * x⁻¹ = w) :
    (A ⊓ P) ⊔ omegaG (pOne T P) ∈ famG T 0 := by
  set W := omegaG (pOne T P) with hWdef
  have htW : ¬ ∀ w ∈ W, t * w * t⁻¹ = w := fun h =>
    hXnc (fun x hx w hw => centralizes_of_inv_mod hQ2 h htX hX3 hXW hQW hx hw)
  have hWnot : ¬ W ≤ A ⊓ P := fun h => htW (fun w hw => by
    rw [hA.2.1.1 t htA w (h hw).1, mul_inv_cancel_right])
  have hAPle : A ⊓ P ≤ pOne T P := le_pOne hAP inf_le_right
  have hcomm : ∀ a ∈ A ⊓ P, ∀ w ∈ W, a * w = w * a := fun a ha w hw =>
    (hw.2.1 a (hAPle ha)).symm
  have hD := card_sup_mul_card_inf_of_commute hcomm
  have hDel : IsElemTwo ((A ⊓ P) ⊔ W) := isElemTwo_sup hAP.2.1 (isElemTwo_omegaG _) hcomm
  have hDT : (A ⊓ P) ⊔ W ≤ T :=
    sup_le (inf_le_left.trans hA.1) ((omegaG_le _).trans ((pOne_le T P).trans hPT))
  have hle := card_le_two_pow_pRank hDT hDel
  rw [hAP.2.2] at hD
  have hlt : Nat.card ↥((A ⊓ P) ⊓ W) < Nat.card W := by
    apply Subgroup.card_lt_of_lt
    refine lt_of_le_of_ne inf_le_right fun h => hWnot ?_
    rw [← h]
    exact inf_le_left
  have hgt : 2 ^ (CFSG.pRank 2 T - 1) < Nat.card ↥((A ⊓ P) ⊔ W) := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card ↥((A ⊓ P) ⊔ W) * Nat.card ↥((A ⊓ P) ⊓ W) ≤
        2 ^ (CFSG.pRank 2 T - 1) * Nat.card ↥((A ⊓ P) ⊓ W) := Nat.mul_le_mul_right _ hcon
    have h2 : 2 ^ (CFSG.pRank 2 T - 1) * Nat.card ↥((A ⊓ P) ⊓ W) <
        2 ^ (CFSG.pRank 2 T - 1) * Nat.card W := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 2 ↥((A ⊓ P) ⊔ W) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]; exact hDel.2 x x.2)⟩
  obtain ⟨m, hm⟩ := hDp.exists_card_eq
  rw [hm] at hle hgt
  have h1 : CFSG.pRank 2 T - 1 < m := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hgt
  have h2 : m ≤ CFSG.pRank 2 T := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  refine ⟨hDT, hDel, ?_⟩
  rw [hm, Nat.sub_zero]
  congr 1
  omega

end CFSG.RankThree.PartTwo.Sec3
