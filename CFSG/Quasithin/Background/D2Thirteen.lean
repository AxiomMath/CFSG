module

public import CFSG.Quasithin.Background.F918Q0
public import CFSG.Quasithin.Background.D2Fitting
public import CFSG.Quasithin.Background.D2Offenders
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V]

theorem fixV_sup (A B : Subgroup (MulAut V)) :
    fixV (A ⊔ B) = fixV A ⊓ fixV B :=
  CFSG.Quasithin.fixV_sup_eq_inf_fixV A B

theorem le_fittingOf_of_normal [Finite V] {p : ℕ} [Fact p.Prime] {X P : Subgroup (MulAut V)}
    (hPX : P ≤ X) (hP : IsPGroup p P) (hn : ∀ x ∈ X, ∀ g ∈ P, x * g * x⁻¹ ∈ P) :
    P ≤ fittingOf X := by
  have hN : (P.subgroupOf X).Normal :=
    ⟨fun n hn' g => by
      rw [Subgroup.mem_subgroupOf] at hn' ⊢
      simpa using hn g g.2 n hn'⟩
  have hPN : IsPGroup p ↥(P.subgroupOf X) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  have hnil : Group.IsNilpotent ↥(P.subgroupOf X) := hPN.isNilpotent
  have hle : P.subgroupOf X ≤ CFSG.fittingSubgroup X := le_sSup ⟨hN, hnil⟩
  intro g hg
  exact ⟨⟨g, hPX hg⟩, hle (by rw [Subgroup.mem_subgroupOf]; exact hg), rfl⟩

theorem exists_orderOf_eq_pow {p : ℕ} [Fact p.Prime] {P : Subgroup (MulAut V)} (hP : IsPGroup p P)
    {d : MulAut V} (hd : d ∈ P) : ∃ a : ℕ, orderOf d = p ^ a := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf).mp hP ⟨d, hd⟩
  exact ⟨a, by rwa [Subgroup.orderOf_mk] at ha⟩


theorem inv_conj_of_involution {G : Type*} [Group G] {t : G} (y : G) (ht2 : t ^ 2 = 1) :
    t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹ = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have h1 : (y⁻¹ * (t * y * t⁻¹))⁻¹ = t * y⁻¹ * t⁻¹ * y := by group
  have h2 : t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹ = t * y⁻¹ * t * y * t⁻¹ * t⁻¹ := by group
  rw [h1, h2, htinv]
  rw [mul_assoc (t * y⁻¹ * t * y) t t, htt, mul_one]

theorem ne_one_of_not_commute {G : Type*} [Group G] {t y : G} (h : t * y ≠ y * t) :
    y⁻¹ * (t * y * t⁻¹) ≠ 1 := by
  intro h1
  apply h
  have h2 : y = t * y * t⁻¹ := inv_mul_eq_one.mp h1
  exact mul_inv_eq_iff_eq_mul.mp h2.symm

theorem false_of_inverted_commute {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {d t : G} (hord : orderOf d = p) (hinv : t * d * t⁻¹ = d⁻¹) (hcomm : t * d = d * t) :
    False := by
  have h1 : t * d * t⁻¹ = d := by rw [hcomm]; group
  rw [h1] at hinv
  have h2 : d ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hinv
  have h3 : p ∣ 2 := hord ▸ orderOf_dvd_of_pow_eq_one h2
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h3)

theorem zpow_involution {G : Type*} [Group G] {t : G} (ht2 : t ^ 2 = 1) (k : ℤ) :
    t ^ k = 1 ∨ t ^ k = t := by
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul]
    simp [ht2]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add, zpow_mul]
    simp [ht2]

section Core

variable [Finite V]

theorem one_le_rk_commV_zpowers (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} (ht1 : t ≠ 1) :
    1 ≤ rk (commV (Subgroup.zpowers t)) := by
  by_contra h
  have h0 : rk (commV (Subgroup.zpowers t)) = 0 := by omega
  have hbot := (rk_eq_zero_iff hV).mp h0
  apply ht1
  ext v
  have : t v * v⁻¹ ∈ commV (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, rfl⟩
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

theorem inverted_elem (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {t d : MulAut V}
    (ht : t ∈ TInv X) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup (MulAut V)}
    (hPX : P ≤ X) (hP : IsPGroup p P) (hd : d ∈ P) (hd1 : d ≠ 1)
    (hinv : t * d * t⁻¹ = d⁻¹) :
    orderOf d = p ∧ (p = 3 ∨ p = 5) ∧
      (rk (commV (Subgroup.zpowers t)) = 1 → p = 3) ∧
      (p = 2 * rk (commV (Subgroup.zpowers t)) + 1 →
        rk (commV (Subgroup.zpowers d)) = 2 * rk (commV (Subgroup.zpowers t))) := by
  obtain ⟨a, ha⟩ := exists_orderOf_eq_pow hP hd
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hodd : Odd (orderOf d) := by rw [ha]; exact hpodd.pow
  have hdX : d ∈ X := hPX hd
  have hr2 := ht.2.2.2
  have hr1 := one_le_rk_commV_zpowers hV ht.2.1
  rcases (by omega : rk (commV (Subgroup.zpowers t)) = 1 ∨
      rk (commV (Subgroup.zpowers t)) = 2) with h1 | h2
  · obtain ⟨hord3, hrk2⟩ := D2_11_1 hV ht h1 hdX hd1 hodd hinv
    rw [ha] at hord3
    obtain ⟨hp3, ha1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hord3
    subst hp3
    refine ⟨by rw [ha, ha1, pow_one], Or.inl rfl, fun _ => rfl, fun _ => by rw [hrk2, h1]⟩
  · obtain ⟨hord35, hrk4⟩ := D2_11_2 hV ht h2 hdX hd1 hodd hinv
    rw [ha] at hord35 hrk4
    rcases hord35 with h3 | h5
    · obtain ⟨hp3, ha1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp h3
      subst hp3
      refine ⟨by rw [ha, ha1, pow_one], Or.inl rfl, fun h => by omega, fun h => by omega⟩
    · obtain ⟨hp5, ha1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h5
      subst hp5
      refine ⟨by rw [ha, ha1, pow_one], Or.inr rfl, fun h => by omega, fun h => ?_⟩
      rw [h2]
      exact hrk4 h5

theorem core_involution (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {t : MulAut V}
    (ht : t ∈ TInv X) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup (MulAut V)}
    (hPX : P ≤ X) (hP : IsPGroup p P) (hn : ∀ x ∈ X, ∀ g ∈ P, x * g * x⁻¹ ∈ P)
    (hact : ∃ y ∈ P, t * y ≠ y * t) :
    (p = 3 ∨ p = 5) ∧ (rk (commV (Subgroup.zpowers t)) = 1 → p = 3) ∧
      (p = 2 * rk (commV (Subgroup.zpowers t)) + 1 →
        ∃ Y ∈ Xk X (rk (commV (Subgroup.zpowers t))), (∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) ∧
          (∀ d ∈ P, t * d * t⁻¹ = d⁻¹ → d ∈ Y) ∧
          commV Y ⊔ fixV (Y ⊔ Subgroup.zpowers t) = ⊤ ∧
          commV Y ⊓ fixV (Y ⊔ Subgroup.zpowers t) = ⊥) := by
  obtain ⟨y, hyP, hy⟩ := hact
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have hd₀P : y⁻¹ * (t * y * t⁻¹) ∈ P := P.mul_mem (P.inv_mem hyP) (hn t ht.1 y hyP)
  have hd₀1 : y⁻¹ * (t * y * t⁻¹) ≠ 1 := ne_one_of_not_commute hy
  have hd₀inv := inv_conj_of_involution (t := t) y ht2
  obtain ⟨-, hp35, hr1, -⟩ := inverted_elem hV ht hp hPX hP hd₀P hd₀1 hd₀inv
  refine ⟨hp35, hr1, fun hpr => ?_⟩
  have hk : rk (commV (Subgroup.zpowers t)) = 1 ∨ rk (commV (Subgroup.zpowers t)) = 2 := by
    have := ht.2.2.2
    have := one_le_rk_commV_zpowers hV ht.2.1
    omega
  have hfact := fact_prime_two_mul_add_one hk
  set r := rk (commV (Subgroup.zpowers t)) with hrdef
  have hmem : ∀ d ∈ P, d ≠ 1 → t * d * t⁻¹ = d⁻¹ → Subgroup.zpowers d ∈ Xk X r := by
    intro d hd hd1 hinv
    obtain ⟨hordd, -, -, hrkd⟩ := inverted_elem hV ht hp hPX hP hd hd1 hinv
    refine ⟨(Subgroup.zpowers_le).mpr (le_fittingOf_of_normal hPX hP hn hd), ?_, hrkd hpr⟩
    rw [Nat.card_zpowers, hordd, hpr]
  have hinvall : ∀ d : MulAut V, t * d * t⁻¹ = d⁻¹ →
      ∀ z ∈ Subgroup.zpowers d, t * z * t⁻¹ = z⁻¹ := by
    intro d hinv z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hinv, inv_zpow]
  have hd₀mem := hmem _ hd₀P hd₀1 hd₀inv
  rcases D2_12_3 hV hk ht rfl with ⟨hcomm, -⟩ | ⟨Y, hY, hinvY, huniq, -, -⟩
  · exfalso
    have hle : Subgroup.zpowers (y⁻¹ * (t * y * t⁻¹)) ≤ Gk X r :=
      le_iSup₂ (f := fun Y (_ : Y ∈ Xk X r) => Y) _ hd₀mem
    have hcm := hcomm _ (hle (Subgroup.mem_zpowers _))
    obtain ⟨hordd, -⟩ := inverted_elem hV ht hp hPX hP hd₀P hd₀1 hd₀inv
    exact false_of_inverted_commute hp hordd hd₀inv hcm.symm
  · have hY1 := hY.2.1
    refine ⟨Y, hY, hinvY, fun d hd hinv => ?_, ?_⟩
    · by_cases hd1 : d = 1
      · rw [hd1]; exact Y.one_mem
      · have := huniq _ (hmem d hd hd1 hinv) (hinvall d hinv)
        rw [← this]
        exact Subgroup.mem_zpowers d
    · obtain ⟨z, hzY, hz1, hzz, hzord⟩ := exists_generator_of_prime_card hY1
      have hzodd : Odd (orderOf z) := by rw [hzord]; exact ⟨r, rfl⟩
      have hzX : z ∈ X := fittingOf_le X (hY.1 hzY)
      have hrkz : rk (commV (Subgroup.zpowers z)) = 2 * rk (commV (Subgroup.zpowers t)) := by
        rw [hzz, hY.2.2]
      have h3 := D2_11_3 hV ht hzX hz1 hzodd (hinvY z hzY) hrkz
      rw [hzz] at h3
      have hfix : fixV Y ≤ fixV (Subgroup.zpowers t) := commSub_eq_bot_iff.mp h3.2.1
      have hfixY : fixV (Y ⊔ Subgroup.zpowers t) = fixV Y := by
        rw [fixV_sup]
        exact inf_eq_left.mpr hfix
      rw [hfixY]
      exact Xk_decomp hV hY

end Core

section Hyperplane

variable [Finite V]

theorem exists_hyperplane_commutator_ne_bot {A P : Subgroup (MulAut V)} {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥) (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set (MulAut V)))
    (hact : ∃ y ∈ P, ∃ a ∈ A, a * y ≠ y * a) :
    ∃ B : Subgroup (MulAut V), B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧
      ∃ y ∈ P ⊓ Subgroup.centralizer (B : Set (MulAut V)), ∃ a ∈ A, a * y ≠ y * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  have hAelem : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => Subtype.ext (hA.2 a a.2) }
  let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P (conjAut hAP)
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 this).symm
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := P) hodd
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hyP, a, haA, hne⟩ := hact
  have hsmul : ∀ (b : A) (x : P), (((b • x : P)) : MulAut V) =
      (b : MulAut V) * x * (b : MulAut V)⁻¹ := fun b x => rfl
  have hle : (⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B P) ≤
      CFSG.fixedPointSubgroup A P := by
    refine iSup₂_le fun B hB x hx => ?_
    have hB' : B.map A.subtype ≤ A := by
      rintro _ ⟨b, -, rfl⟩
      exact b.2
    have hcard : Nat.card A = 2 * Nat.card (B.map A.subtype) := by
      have := B.card_mul_index
      rw [hB] at this
      rw [Subgroup.card_map_of_injective A.subtype_injective]
      omega
    have hxc : (x : MulAut V) ∈ P ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup (MulAut V)) :
        Set (MulAut V)) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have h1 : b • x = x := hx ⟨b, hb⟩
      have h2 := congrArg (fun z : P => (z : MulAut V)) h1
      simp only [hsmul] at h2
      show (b : MulAut V) * x = x * b
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    intro a'
    apply Subtype.ext
    rw [hsmul]
    exact mul_inv_eq_iff_eq_mul.mpr (hcon _ hB' hcard x hxc a' a'.2)
  have hy : (⟨y, hyP⟩ : P) ∈ CFSG.fixedPointSubgroup A P := hle (hgen ▸ Subgroup.mem_top _)
  have h1 : (⟨a, haA⟩ : A) • (⟨y, hyP⟩ : P) = ⟨y, hyP⟩ := hy ⟨a, haA⟩
  have h2 := congrArg (fun z : P => (z : MulAut V)) h1
  simp only [hsmul] at h2
  exact hne (mul_inv_eq_iff_eq_mul.mp h2)

end Hyperplane


theorem commutator_ne_bot_iff {G : Type*} [Group G] {P A : Subgroup G} :
    ⁅P, A⁆ ≠ ⊥ ↔ ∃ y ∈ P, ∃ a ∈ A, a * y ≠ y * a := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    apply h
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcon y hy a ha
  · rintro ⟨y, hy, a, ha, hne⟩ h
    apply hne
    have h1 : ⁅y, a⁆ ∈ ⁅P, A⁆ := Subgroup.commutator_mem_commutator hy ha
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

@[expose] def IsDirectSum (W W₁ W₂ : Subgroup V) : Prop := W₁ ⊔ W₂ = W ∧ W₁ ⊓ W₂ = ⊥

section Cyclic

variable [Finite V]

theorem D2_13_cyclic (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) (hrk : rk A = 1)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {D : Subgroup (MulAut V)} (hD : D = ⁅pCoreOf p X, A⁆)
    (hAP : D ≠ ⊥) :
    ∃ m : ℕ, r = m ∧ (m = 1 ∨ m = 2) ∧ (p = 3 ∨ p = 5) ∧ (m = 1 → p = 3) ∧
      (p = 2 * m + 1 → Nat.card D = p ∧ IsCyclic D ∧ IsDirectSum ⊤ (commV D) (fixV (D ⊔ A)) ∧
        rk (commV D) = 2 * m) := by
  obtain ⟨r', hr', hr2, ⟨⟨hA2, hAr⟩, hAk⟩, -⟩ := QhatStar_spec hA
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  subst hrr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAcard : Nat.card A = 2 := by
    rw [card_eq_two_pow_of_isPGroup hA2.isElemAbelian2.isPGroup, hrk, pow_one]
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp hA2.ne_bot
  have ht1' : (t : MulAut V) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hAt : Subgroup.zpowers (t : MulAut V) = A := zpowers_eq_of_prime_card hAcard t.2 ht1'
  have hm : (rk (commV (Subgroup.zpowers (t : MulAut V))) : ℚ) = r' := by
    rw [← hAr, rAV, hAt, hrk, ← hAt, rkIdx_fixV_zpowers]
    simp
  set m := rk (commV (Subgroup.zpowers (t : MulAut V))) with hmdef
  have hm2 : m ≤ 2 := by
    have : (m : ℚ) ≤ 2 := hm ▸ hr2
    exact_mod_cast this
  have hm1 : 1 ≤ m := one_le_rk_commV_zpowers hV ht1'
  have ht2 : (t : MulAut V) ^ 2 = 1 := hA2.isElemAbelian2.2 t t.2
  have htT : (t : MulAut V) ∈ TInv X := ⟨hA2.le t.2, ht1', ht2, hm2⟩
  have hPnorm : ∀ x ∈ X, ∀ g ∈ pCoreOf p X, x * g * x⁻¹ ∈ pCoreOf p X := by
    intro x hx g hg
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p X hx) g).mp hg
  have hact : ∃ y ∈ pCoreOf p X, (t : MulAut V) * y ≠ y * t := by
    obtain ⟨y, hy, a, ha, hne⟩ := commutator_ne_bot_iff.mp (hD ▸ hAP)
    refine ⟨y, hy, fun hcomm => hne ?_⟩
    rw [← hAt] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (show Commute (t : MulAut V) y from hcomm) k).eq
  obtain ⟨h35, hm1p, hcore⟩ := core_involution hV htT hp (pCoreOf_le p X)
    (pCoreOf_isPGroup p X) hPnorm hact
  refine ⟨m, hm.symm, by omega, h35, hm1p, fun hpm => ?_⟩
  obtain ⟨Y, hY, hYinv, hYall, hdec1, hdec2⟩ := hcore hpm
  have hDY : D ≤ Y := by
    rw [hD, Subgroup.commutator_le]
    intro y hy a ha
    rw [← hAt] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rcases zpow_involution ht2 k with h | h
    · rw [h]
      simp only [commutatorElement_def, mul_one, mul_inv_cancel, inv_one]
      exact Y.one_mem
    · rw [h]
      have h1 : ⁅y, (t : MulAut V)⁆ =
          (y⁻¹)⁻¹ * ((t : MulAut V) * y⁻¹ * (t : MulAut V)⁻¹) := by
        rw [commutatorElement_def]; group
      rw [h1]
      refine hYall _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.inv_mem _ hy))
        (hPnorm _ (hA2.le t.2) _ (Subgroup.inv_mem _ hy))) ?_
      exact inv_conj_of_involution (t := (t : MulAut V)) y⁻¹ ht2
  have hYcard : Nat.card Y = p := by rw [hY.2.1, hpm]
  have hdvd : Nat.card D ∣ Nat.card Y := Subgroup.card_dvd_of_le hDY
  rw [hYcard] at hdvd
  have hD1 : Nat.card D ≠ 1 := fun h => hAP (Subgroup.card_eq_one.mp h)
  have hDp : Nat.card D = p := ((Nat.dvd_prime Fact.out).mp hdvd).resolve_left hD1
  have hDeq : D = Y := Subgroup.eq_of_le_of_card_ge hDY (by rw [hDp, hYcard])
  subst hDeq
  refine ⟨hDp, isCyclic_of_prime_card hDp, ?_, hY.2.2⟩
  rw [← hAt]
  exact ⟨hdec1, hdec2⟩

end Cyclic

section Restrict

theorem mem_stabSub_fixV_of_commute {B : Subgroup (MulAut V)} {g : MulAut V}
    (h : ∀ b ∈ B, b * g = g * b) : g ∈ stabSub (fixV B) := by
  intro u
  have key : ∀ b ∈ B, b (g u) = g (b u) := fun b hb => by
    have := congrArg (fun φ : MulAut V => φ u) (h b hb)
    simpa using this
  constructor
  · intro hu b hb
    have h1 : b (g u) = g u := hu b hb
    rw [key b hb] at h1
    exact g.injective h1
  · intro hu b hb
    rw [key b hb, hu b hb]

theorem isPGroup_autSub {p : ℕ} {Q : Subgroup (MulAut V)} {U : Subgroup V} (hQ : IsPGroup p Q) :
    IsPGroup p (autSub Q U) := by
  intro g
  obtain ⟨h, hhQ, hh⟩ := mem_autSub.mp g.2
  obtain ⟨k, hk⟩ := hQ ⟨h.1, hhQ⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (h ^ p ^ k : stabSub U) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h2 : resHom U (h ^ p ^ k) = 1 := by rw [h1, map_one]
  rw [map_pow, hh] at h2
  simpa using h2

theorem isPGroup_bot_of_two_primes {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hpq : p ≠ q) {C : Subgroup G} (hp : IsPGroup p C) (hq : IsPGroup q C) :
    C = ⊥ := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p)).mp hp
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := q)).mp hq
  rw [← Subgroup.card_eq_one]
  by_cases ha0 : a = 0
  · rw [ha, ha0, pow_zero]
  · exfalso
    have h1 : p ∣ q ^ b := by
      rw [← hb, ha]
      exact dvd_pow_self p ha0
    have h2 : p ∣ q := (Fact.out : p.Prime).dvd_of_dvd_pow h1
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)).mp h2)

variable [Finite V]

theorem pCoreOf_two_eq_bot {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {Q : Subgroup (MulAut V)}
    (hQ : IsPGroup p Q) : pCoreOf 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isPGroup_bot_of_two_primes (p := 2) (q := p) (Ne.symm hp)
    (pCoreOf_isPGroup 2 Q) (hQ.to_le (pCoreOf_le 2 Q))

theorem faithful_on_fixV (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {Q B : Subgroup (MulAut V)} (hQ : IsPGroup p Q) (hB : IsPGroup 2 B)
    (hcomm : ∀ q ∈ Q, ∀ b ∈ B, q * b = b * q) :
    ∀ q ∈ Q, (∀ u ∈ fixV B, q u = u) → q = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := thompson_AxB_two (p := 2) (isPGroup_two_of_sq_eq_one hV) (MonoidHom.id (MulAut V))
    (A := Q) (B := B) hcomm (by rw [Subgroup.map_id]; exact hB) (fun a _ ha => ha)
    (pCoreOf_two_eq_bot hp hQ)
  exact fun q hq hfix => h q hq fun x hx => hfix x hx

theorem inv_comm_involution {G : Type*} [Group G] {t : G} (ht2 : t ^ 2 = 1) (z : G) :
    t * ⁅z, t⁆ * t⁻¹ = ⁅z, t⁆⁻¹ := by
  have h1 : ⁅z, t⁆ = (z⁻¹)⁻¹ * (t * z⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
  rw [h1]
  exact inv_conj_of_involution z⁻¹ ht2

omit [Finite V] in
theorem commutator_fixes_of_res_comm {U : Subgroup V} {g h : MulAut V} (hg : g ∈ stabSub U)
    (hh : h ∈ stabSub U)
    (hcomm : resHom U ⟨g, hg⟩ * resHom U ⟨h, hh⟩ = resHom U ⟨h, hh⟩ * resHom U ⟨g, hg⟩) :
    ∀ u ∈ U, (g * h * g⁻¹ * h⁻¹) u = u := by
  intro u hu
  have e : ∀ u ∈ U, g (h u) = h (g u) := fun u hu =>
    congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : V)) hcomm
  have hinvg : g⁻¹ ∈ stabSub U := (stabSub U).inv_mem hg
  have hinvh : h⁻¹ ∈ stabSub U := (stabSub U).inv_mem hh
  have hw : g⁻¹ (h⁻¹ u) ∈ U := (hinvg _).mpr ((hinvh _).mpr hu)
  show g (h (g⁻¹ (h⁻¹ u))) = u
  rw [e _ hw]
  simp

end Restrict

section Hyperplane2

variable [Finite V]

theorem D2_13_hyperplane (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) (hrk : 1 < rk A)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {B : Subgroup (MulAut V)} (hBA : B ≤ A)
    (hBcard : Nat.card A = 2 * Nat.card B) {D : Subgroup (MulAut V)}
    (hD : D = ⁅pCoreOf p X ⊓ Subgroup.centralizer (B : Set (MulAut V)), A⁆) (hDne : D ≠ ⊥) :
    p = 3 ∧ 1 < r ∧ Nat.card D = 3 ∧ IsCyclic D ∧
      IsDirectSum (fixV B) (commSub (fixV B) D) (fixV (D ⊔ A)) ∧ rk (commSub (fixV B) D) = 2 := by
  classical
  obtain ⟨r', hr', hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  subst hrr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf p X with hPdef
  set Q := P ⊓ Subgroup.centralizer (B : Set (MulAut V)) with hQdef
  set U := fixV B with hUdef
  have hAel := hA2.isElemAbelian2
  have hAX : A ≤ X := hA2.le
  have hPp : IsPGroup p P := pCoreOf_isPGroup p X
  have hPn : ∀ x ∈ X, ∀ g ∈ P, x * g * x⁻¹ ∈ P := fun x hx g hg =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p X hx) g).mp hg
  have hQP : Q ≤ P := inf_le_left
  have hQp : IsPGroup p Q := hPp.to_le hQP
  have hQc : ∀ q ∈ Q, ∀ b ∈ B, q * b = b * q := fun q hq b hb =>
    ((Subgroup.mem_centralizer_iff.mp hq.2) b hb).symm
  have hB2 : IsPGroup 2 B := hAel.isPGroup.to_le hBA
  have hAcard : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hAel.isPGroup
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, hAcard] at hBcard
    have : 2 ^ 2 ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) hrk
    omega
  obtain ⟨y, hyQ, t, htA, hne⟩ := commutator_ne_bot_iff.mp (hD ▸ hDne)
  have hAQ : ∀ a ∈ A, ∀ z ∈ Q, a * z * a⁻¹ ∈ Q := by
    intro a ha z hz
    refine ⟨hPn a (hAX ha) z hz.1, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hab : Commute b a := hAel.1 b (hBA hb) a ha
    have hzb : b * z = z * b := (Subgroup.mem_centralizer_iff.mp hz.2) b hb
    calc b * (a * z * a⁻¹) = (b * a) * z * a⁻¹ := by group
      _ = a * b * z * a⁻¹ := by rw [hab.eq]
      _ = a * (b * z) * a⁻¹ := by group
      _ = a * (z * b) * a⁻¹ := by rw [hzb]
      _ = a * z * (b * a⁻¹) := by group
      _ = a * z * (a⁻¹ * b) := by rw [hab.inv_right.eq]
      _ = a * z * a⁻¹ * b := by group
  have hAn : A ≤ Subgroup.normalizer (Q : Set (MulAut V)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hAQ a ha z, fun hz => ?_⟩
    have := hAQ a⁻¹ (A.inv_mem ha) _ hz
    simpa [mul_assoc] using this
  have hQA : Q ⊔ A ≤ Subgroup.normalizer (Q : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hAn
  have hQs : Q ≤ stabSub U := fun q hq =>
    mem_stabSub_fixV_of_commute (fun b hb => (hQc q hq b hb).symm)
  have hAs : A ≤ stabSub U := fun a ha =>
    mem_stabSub_fixV_of_commute (fun b hb => hAel.1 b (hBA hb) a ha)
  have hfaith : ∀ q ∈ Q, (∀ u ∈ U, q u = u) → q = 1 := faithful_on_fixV hV hp hQp hB2 hQc
  have hQcent : Q ⊓ centSub U = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun q hq => hfaith q hq.1 hq.2
  have hUA : commSub U A ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    apply hne
    have hz := hAQ t htA y hyQ
    have hzy : ∀ u ∈ U, (t * y * t⁻¹) u = y u := by
      intro u hu
      have h1 : t⁻¹ u = u := hbot hu t⁻¹ (A.inv_mem htA)
      have h2 : y u ∈ U := ((hQs hyQ) u).mpr hu
      show t (y (t⁻¹ u)) = y u
      rw [h1]
      exact hbot h2 t htA
    have h1 : (t * y * t⁻¹)⁻¹ * y = 1 := by
      refine hfaith _ (Q.mul_mem (Q.inv_mem hz) hyQ) fun u hu => ?_
      show (t * y * t⁻¹)⁻¹ (y u) = u
      rw [← hzy u hu]
      simp
    have h2 : t * y * t⁻¹ = y := (inv_mul_eq_one.mp h1)
    exact mul_inv_eq_iff_eq_mul.mp h2
  obtain ⟨-, hD7⟩ := D2_7 hV hr hA hAs hUA
  rcases hD7 with ⟨ε, hε, hAUQ⟩ | ⟨hbot, -⟩
  swap
  · exfalso
    apply hBne
    have : B ≤ A ⊓ centSub U := le_inf hBA (fun b hb u hu => hu b hb)
    rw [hbot] at this
    exact le_bot_iff.mp this
  obtain ⟨⟨hA'2, hA'r⟩, hA'k⟩ := hAUQ
  have hBC : B ≤ A ⊓ centSub U := le_inf hBA (fun b hb u hu => hu b hb)
  have hCB : A ⊓ centSub U = B := by
    have hCA : A ⊓ centSub U ≤ A := inf_le_left
    have hnotA : ¬ A ≤ centSub U := fun h =>
      hUA ((commSub_eq_bot_iff).mpr fun u hu a ha => h ha u hu)
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBC
    have d2 : Nat.card ↥(A ⊓ centSub U) ∣ Nat.card A := Subgroup.card_dvd_of_le hCA
    rw [hk, hBcard, mul_comm 2] at d2
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hBpos d2
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h1 | h2
    · refine (Subgroup.eq_of_le_of_card_ge hBC ?_).symm
      rw [hk, h1, mul_one]
    · exfalso
      apply hnotA
      have : A ⊓ centSub U = A := by
        refine Subgroup.eq_of_le_of_card_ge hCA ?_
        rw [hk, h2, hBcard, mul_comm]
      rw [← this]
      exact inf_le_right
  have hcardAut := card_autSub_mul hAs
  rw [hCB, hBcard] at hcardAut
  have hA'card : Nat.card (autSub A U) = 2 := Nat.eq_of_mul_eq_mul_right hBpos
    (by rw [hcardAut, mul_comm])
  have ht2 : t ^ 2 = 1 := hAel.2 t htA
  have htB : t ∉ B := fun htB => hne (hQc y hyQ t htB).symm
  have htU : ∃ u ∈ U, t u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply htB
    rw [← hCB]
    exact ⟨htA, hcon⟩
  set t' : MulAut ↥U := resHom U ⟨t, hAs htA⟩ with ht'def
  have ht'1 : t' ≠ 1 := by
    obtain ⟨u, hu, htu⟩ := htU
    intro h
    exact htu (congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : U) : V)) h)
  have ht'2 : t' ^ 2 = 1 := by
    rw [ht'def, ← map_pow]
    have : (⟨t, hAs htA⟩ : stabSub U) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  have ht'A : t' ∈ autSub A U := mem_autSub.mpr ⟨⟨t, hAs htA⟩, htA, rfl⟩
  have hA'eq : autSub A U = Subgroup.zpowers t' :=
    (zpowers_eq_of_prime_card hA'card ht'A ht'1).symm
  have hVU : ∀ u : U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV u)
  set m := rk (commV (Subgroup.zpowers t')) with hmdef
  have hrkA' : rk (autSub A U) = 1 := by
    unfold rk
    rw [hA'card]
    simp
  have hmr : (m : ℚ) = rAV (autSub A U) := by
    rw [rAV, hrkA']
    have : rkIdx (fixV (autSub A U)) = m := by rw [hA'eq, rkIdx_fixV_zpowers]
    rw [this]
    simp
  have hm1 : 1 ≤ m := one_le_rk_commV_zpowers hVU ht'1
  have hmlt : (m : ℚ) < r' := by linarith
  have hm_eq : m = 1 := by
    have : (m : ℚ) < 2 := by linarith
    have : m < 2 := by exact_mod_cast this
    omega
  have h1r : 1 < r' := by
    have : (m : ℚ) = 1 := by exact_mod_cast hm_eq
    linarith
  set X' := autSub (Q ⊔ A) U with hX'
  set P' := autSub Q U with hP'
  have ht'X : t' ∈ X' := mem_autSub.mpr ⟨⟨t, hAs htA⟩, Subgroup.mem_sup_right htA, rfl⟩
  have ht'T : t' ∈ TInv X' := ⟨ht'X, ht'1, ht'2, by omega⟩
  have hP'X' : P' ≤ X' := autSub_mono le_sup_left U
  have hP'p : IsPGroup p P' := isPGroup_autSub hQp
  have hn' : ∀ x ∈ X', ∀ g ∈ P', x * g * x⁻¹ ∈ P' := by
    intro x hx g hg
    obtain ⟨h, hhX, rfl⟩ := mem_autSub.mp hx
    obtain ⟨q, hqQ, rfl⟩ := mem_autSub.mp hg
    have hconj : h.1 * q.1 * h.1⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQA hhX) q.1).mp hqQ
    refine mem_autSub.mpr ⟨h * q * h⁻¹, hconj, ?_⟩
    simp
  have hact' : ∃ y' ∈ P', t' * y' ≠ y' * t' := by
    refine ⟨resHom U ⟨y, hQs hyQ⟩, mem_autSub.mpr ⟨⟨y, hQs hyQ⟩, hyQ, rfl⟩, fun hcomm => hne ?_⟩
    have hc : t * y * t⁻¹ * y⁻¹ ∈ Q := Q.mul_mem (hAQ t htA y hyQ) (Q.inv_mem hyQ)
    have h1 : t * y * t⁻¹ * y⁻¹ = 1 :=
      hfaith _ hc (commutator_fixes_of_res_comm (hAs htA) (hQs hyQ) hcomm)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨-, hp3', hcore⟩ := core_involution hVU ht'T hp hP'X' hP'p hn' hact'
  have hp3 : p = 3 := hp3' hm_eq
  obtain ⟨Y, hY, hYinv, hYall, hdec1, hdec2⟩ := hcore (by omega)
  have hcommQ : ∀ z ∈ Q, ∀ a ∈ A, ⁅z, a⁆ ∈ Q := by
    intro z hz a ha
    have : ⁅z, a⁆ = z * (a * z⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact Q.mul_mem hz (hAQ a ha z⁻¹ (Q.inv_mem hz))
  have hDQ : D ≤ Q := by
    rw [hD, Subgroup.commutator_le]
    exact hcommQ
  have hDs : D ≤ stabSub U := hDQ.trans hQs
  have hD'Y : autSub D U ≤ Y := by
    let S : Subgroup (MulAut V) := (Y.comap (resHom U)).map (stabSub U).subtype
    have hDS : D ≤ S := by
      rw [hD, Subgroup.commutator_le]
      intro z hz a ha
      have hzs : z ∈ stabSub U := hQs hz
      have has : a ∈ stabSub U := hAs ha
      have hcQ : ⁅z, a⁆ ∈ Q := hcommQ z hz a ha
      have hcs : ⁅z, a⁆ ∈ stabSub U := hQs hcQ
      refine ⟨⟨⁅z, a⁆, hcs⟩, ?_, rfl⟩
      show resHom U ⟨⁅z, a⁆, hcs⟩ ∈ Y
      have hres : resHom U ⟨⁅z, a⁆, hcs⟩ = ⁅resHom U ⟨z, hzs⟩, resHom U ⟨a, has⟩⁆ :=
        map_commutatorElement (resHom U) ⟨z, hzs⟩ ⟨a, has⟩
      have haA' : resHom U ⟨a, has⟩ ∈ Subgroup.zpowers t' :=
        hA'eq ▸ mem_autSub.mpr ⟨⟨a, has⟩, ha, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haA'
      have hdP : resHom U ⟨⁅z, a⁆, hcs⟩ ∈ P' := mem_autSub.mpr ⟨⟨⁅z, a⁆, hcs⟩, hcQ, rfl⟩
      rcases zpow_involution ht'2 k with h | h
      · rw [hres, ← hk, h, commutatorElement_one_right]
        exact Y.one_mem
      · apply hYall _ hdP
        rw [hres, ← hk, h]
        exact inv_comm_involution ht'2 _
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨h, hh, hgh⟩ := hDS hg
    have : h = g := Subtype.ext hgh
    subst this
    exact hh
  have hD'ne : autSub D U ≠ ⊥ := by
    obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := D)).mp hDne
    intro hbot
    have hdQ : (d : MulAut V) ∈ Q := hDQ d.2
    have hmem : resHom U ⟨d, hDs d.2⟩ ∈ autSub D U :=
      mem_autSub.mpr ⟨⟨d, hDs d.2⟩, d.2, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hd1
    apply Subtype.ext
    refine hfaith _ hdQ fun u hu => ?_
    exact congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : U) : V)) hmem
  have hY3 : Nat.card Y = 3 := by have := hY.2.1; omega
  have hD'Yeq : autSub D U = Y := by
    have hdvd : Nat.card (autSub D U) ∣ Nat.card Y := Subgroup.card_dvd_of_le hD'Y
    rw [hY3] at hdvd
    have h1 : Nat.card (autSub D U) ≠ 1 := fun h => hD'ne (Subgroup.card_eq_one.mp h)
    have h3 : Nat.card (autSub D U) = 3 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd).resolve_left h1
    exact Subgroup.eq_of_le_of_card_ge hD'Y (by rw [h3, hY3])
  have hDcent : D ⊓ centSub U = ⊥ := le_bot_iff.mp (hQcent ▸ inf_le_inf_right _ hDQ)
  have hDcard : Nat.card D = 3 := by
    have := card_autSub_mul hDs
    rw [hDcent, Subgroup.card_bot, mul_one, hD'Yeq, hY3] at this
    exact this.symm
  have hU' : (⊤ : Subgroup ↥U).map U.subtype = U := by
    rw [← MonoidHom.range_eq_map]
    exact U.range_subtype
  have hmapcomm : (commV Y).map U.subtype = commSub U D := by
    rw [← hD'Yeq, commV_eq_commSub, map_commSub_autSub hDs ⊤, hU']
  have hmapfix : (fixV (Y ⊔ Subgroup.zpowers t')).map U.subtype = fixV (D ⊔ A) := by
    rw [← hD'Yeq, ← hA'eq, fixV_sup, Subgroup.map_inf _ _ U.subtype U.subtype_injective,
      map_subtype_fixV_autSub hDs, map_subtype_fixV_autSub hAs, fixV_sup]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, h1⟩, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fixV_anti hBA h2, h1⟩, fixV_anti hBA h2, h2⟩
  refine ⟨hp3, h1r, hDcard, isCyclic_of_prime_card (hDcard.trans hp3.symm), ⟨?_, ?_⟩, ?_⟩
  · have := congrArg (Subgroup.map U.subtype) hdec1
    rw [Subgroup.map_sup, hmapcomm, hmapfix, hU'] at this
    exact this
  · have := congrArg (Subgroup.map U.subtype) hdec2
    rw [Subgroup.map_inf _ _ U.subtype U.subtype_injective, hmapcomm, hmapfix, Subgroup.map_bot] at this
    exact this
  · have h1 : rk (commSub U D) = rk (commV Y) := by
      rw [← hmapcomm]
      unfold rk
      rw [Subgroup.card_map_of_injective U.subtype_injective]
    rw [h1, hY.2.2]
    omega

end Hyperplane2

section Main

variable [Finite V]

theorem D2_13 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {D : Subgroup (MulAut V)} (hD : D = ⁅pCoreOf p X, A⁆) (hAP : D ≠ ⊥) :
    (p = 3 ∨ p = 5) ∧
    (p = 5 → r = 2 ∧ rk A = 1 ∧ Nat.card D = 5 ∧ IsCyclic D ∧
      IsDirectSum ⊤ (commV D) (fixV (D ⊔ A)) ∧ rk (commV D) = 4) ∧
    (rk A = 1 → (r = 1 ∨ r = 2) ∧ (r = 1 → p = 3 ∧ Nat.card D = 3 ∧ IsCyclic D ∧
      IsDirectSum ⊤ (commV D) (fixV (D ⊔ A)) ∧ rk (commV D) = 2)) ∧
    (r ≤ 1 → r = 1 ∧ p = 3 ∧ rk A = 1) ∧
    (1 < rk A → p = 3 ∧ ∀ B : Subgroup (MulAut V), B ≤ A → Nat.card A = 2 * Nat.card B →
      ∀ D' : Subgroup (MulAut V),
        D' = ⁅pCoreOf p X ⊓ Subgroup.centralizer (B : Set (MulAut V)), A⁆ → D' ≠ ⊥ →
        Nat.card D' = 3 ∧ IsCyclic D' ∧
          IsDirectSum (fixV B) (commSub (fixV B) D') (fixV (D' ⊔ A)) ∧
          rk (commSub (fixV B) D') = 2) := by
  classical
  by_cases hcyc : rk A = 1
  · obtain ⟨m, hrm, hm12, h35, hm1p, hconc⟩ := D2_13_cyclic hV hr hA hcyc hp hD hAP
    refine ⟨h35, ?_, ?_, ?_, fun h => by omega⟩
    · intro hp5
      have hm2 : m = 2 := by
        rcases hm12 with h | h
        · exact absurd (hm1p h) (by omega)
        · exact h
      obtain ⟨hc1, hc2, hc3, hc4⟩ := hconc (by omega)
      exact ⟨by rw [hrm, hm2]; norm_num, hcyc, hc1.trans hp5, hc2, hc3, by omega⟩
    · intro _
      refine ⟨by rcases hm12 with h | h <;> simp [hrm, h], fun hr1 => ?_⟩
      have hm1 : m = 1 := by
        rw [hrm] at hr1
        exact_mod_cast hr1
      have hp3 := hm1p hm1
      obtain ⟨hc1, hc2, hc3, hc4⟩ := hconc (by omega)
      exact ⟨hp3, hc1.trans hp3, hc2, hc3, by omega⟩
    · intro hle
      have hm1 : m = 1 := by
        rcases hm12 with h | h
        · exact h
        · rw [hrm, h] at hle
          norm_num at hle
      exact ⟨by rw [hrm, hm1]; norm_num, hm1p hm1, hcyc⟩
  · obtain ⟨r', hr', hr2, ⟨⟨hA2, hAr⟩, hAk⟩, -⟩ := QhatStar_spec hA
    have hrk : 1 < rk A := by
      have := hA2.rk_pos
      omega
    have hAel := hA2.isElemAbelian2
    have hPp : IsPGroup p (pCoreOf p X) := pCoreOf_isPGroup p X
    have hAn : A ≤ Subgroup.normalizer ((pCoreOf p X : Subgroup (MulAut V)) : Set (MulAut V)) :=
      hA2.le.trans (le_normalizer_pCoreOf p X)
    obtain ⟨B₀, hB₀A, hB₀card, hB₀⟩ := exists_hyperplane_commutator_ne_bot hp hAel hA2.ne_bot
      hPp hAn (commutator_ne_bot_iff.mp (hD ▸ hAP))
    have hB₀ne := commutator_ne_bot_iff.mpr hB₀
    obtain ⟨hp3, h1r, -⟩ := D2_13_hyperplane hV hr hA hrk hp hB₀A hB₀card rfl hB₀ne
    refine ⟨Or.inl hp3, fun h => by omega, fun h => absurd h hcyc, fun h => by linarith,
      fun _ => ⟨hp3, fun B hBA hBcard D' hD' hD'ne => ?_⟩⟩
    obtain ⟨-, -, h⟩ := D2_13_hyperplane hV hr hA hrk hp hBA hBcard hD' hD'ne
    exact h

end Main

end CFSG.Quasithin
