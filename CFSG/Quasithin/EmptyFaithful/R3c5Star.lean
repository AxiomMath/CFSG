module

public import CFSG.Quasithin.EmptyFaithful.R3c2Excl
import CFSG.Quasithin.EmptyFaithful.R3c6Psl

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {H : Type} [Group H] [Finite H]

theorem coprime_orderOf_of_mem_pPrimeCore {x : H} (hx : x ∈ CFSG.pPrimeCore 3 H) :
    Nat.Coprime 3 (orderOf x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : orderOf (⟨x, hx⟩ : ↥(CFSG.pPrimeCore 3 H)) ∣ Nat.card (CFSG.pPrimeCore 3 H) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card

theorem mem_center_of_mem_pPrimeCore {L : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) (x : ↥L) (hx : (x : H) ∈ CFSG.pPrimeCore 3 H) :
    x ∈ Subgroup.center ↥L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥L := (CFSG.pPrimeCore 3 H).subgroupOf L with hN
  have hKn : (CFSG.pPrimeCore 3 H).Normal := CFSG.pPrimeCore_normal
  have hNn : N.Normal := hKn.subgroupOf L
  have hNt : N ≠ ⊤ := by
    intro htop
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3
    have hyN : y ∈ N := htop ▸ Subgroup.mem_top y
    have hyK : (y : H) ∈ CFSG.pPrimeCore 3 H := hyN
    have hcop := coprime_orderOf_of_mem_pPrimeCore hyK
    rw [Subgroup.orderOf_coe, hy] at hcop
    exact absurd hcop (by norm_num)
  exact CFSG.Quasithin.Vol2.Ch11.SecA.le_center_of_normal_ne_top hQ hNt hx


theorem commute_of_mem_pPrimeCore {L : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) {k : H} (hk : k ∈ CFSG.pPrimeCore 3 H) (x : ↥L) :
    (x : H) * k = k * (x : H) := by
  have hKn : (CFSG.pPrimeCore 3 H).Normal := CFSG.pPrimeCore_normal
  have hL : ∀ y : ↥L, (y : H) * k * (y : H)⁻¹ * k⁻¹ ∈ L := by
    intro y
    have h1 : k * (y : H)⁻¹ * k⁻¹ ∈ L := by
      have := (inferInstance : L.Normal).conj_mem ((y : H)⁻¹) (L.inv_mem y.2) k
      simpa [mul_assoc] using this
    have := L.mul_mem y.2 h1
    simpa [mul_assoc] using this
  have hK : ∀ y : ↥L, (y : H) * k * (y : H)⁻¹ * k⁻¹ ∈ CFSG.pPrimeCore 3 H := by
    intro y
    exact (CFSG.pPrimeCore 3 H).mul_mem (hKn.conj_mem k hk (y : H)) ((CFSG.pPrimeCore 3 H).inv_mem hk)
  set f : ↥L → ↥L := fun y => ⟨(y : H) * k * (y : H)⁻¹ * k⁻¹, hL y⟩ with hf
  have hfc : ∀ y, f y ∈ Subgroup.center ↥L := fun y =>
    mem_center_of_mem_pPrimeCore hQ h3 (f y) (hK y)
  have hmul : ∀ y z, f (y * z) = f z * f y := by
    intro y z
    have hz := Subgroup.mem_center_iff.mp (hfc z) y
    apply Subtype.ext
    have hz' : (y : H) * (f z : H) = (f z : H) * (y : H) := congrArg Subtype.val hz
    change ((y : H) * (z : H)) * k * ((y : H) * (z : H))⁻¹ * k⁻¹ =
      ((z : H) * k * (z : H)⁻¹ * k⁻¹) * ((y : H) * k * (y : H)⁻¹ * k⁻¹)
    have hz'' : (y : H) * ((z : H) * k * (z : H)⁻¹ * k⁻¹) =
        ((z : H) * k * (z : H)⁻¹ * k⁻¹) * (y : H) := hz'
    calc ((y : H) * (z : H)) * k * ((y : H) * (z : H))⁻¹ * k⁻¹
        = (y : H) * ((z : H) * k * (z : H)⁻¹ * k⁻¹) * k * (y : H)⁻¹ * k⁻¹ := by group
      _ = ((z : H) * k * (z : H)⁻¹ * k⁻¹) * (y : H) * k * (y : H)⁻¹ * k⁻¹ := by rw [hz'']
      _ = _ := by group
  let g : ↥L →* ↥(Subgroup.center ↥L) :=
    { toFun := fun y => ⟨f y, hfc y⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp [hf]
      map_mul' := by
        intro y z
        apply Subtype.ext
        show f (y * z) = f y * f z
        rw [hmul y z]
        exact Subgroup.mem_center_iff.mp (hfc y) (f z) }
  have hker : commutator ↥L ≤ g.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (g b).2 (g a)))
  have hx : x ∈ g.ker := hker (by rw [hQ.1.commutator_eq_top]; exact Subgroup.mem_top x)
  have hx1 : f x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hx2 : (x : H) * k * (x : H)⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hx1
  exact commutatorElement_eq_one_iff_mul_comm.mp hx2


theorem mem_of_mk_mem_starImage {L : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) {x : H} {k : ℕ} (hx : orderOf x = 3 ^ k)
    (hmem : (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) x ∈ starImage 3 L) : x ∈ L := by
  obtain ⟨l, hl, hlx⟩ := hmem
  have hlx' : l⁻¹ * x ∈ CFSG.pPrimeCore 3 H := by
    exact QuotientGroup.eq.mp hlx
  set o : H := l⁻¹ * x with ho
  have hxo : x = l * o := by simp [ho]
  have hcomm : Commute l o := by
    have := commute_of_mem_pPrimeCore hQ h3 hlx' ⟨l, hl⟩
    exact this
  have hx1 : x ^ 3 ^ k = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hpow : l ^ 3 ^ k * o ^ 3 ^ k = 1 := by
    rw [← hcomm.mul_pow, ← hxo]
    exact hx1
  have hopow : o ^ 3 ^ k ∈ L := by
    have : o ^ 3 ^ k = (l ^ 3 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hpow
    rw [this]
    exact L.inv_mem (L.pow_mem hl _)
  have hcop : Nat.Coprime (3 ^ k) (orderOf o) :=
    Nat.Coprime.pow_left k (coprime_orderOf_of_mem_pPrimeCore hlx')
  have hoz : o ∈ Subgroup.zpowers (o ^ 3 ^ k) := mem_zpowers_pow_iff.mpr hcop
  have hoL : o ∈ L := (Subgroup.zpowers_le.mpr hopow) hoz
  rw [hxo]
  exact L.mul_mem hl hoL


theorem isPGroup_two_center_starImage {L : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) :
    IsPGroup 2 ↥(Subgroup.center ↥(starImage 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKn : (CFSG.pPrimeCore 3 H).Normal := CFSG.pPrimeCore_normal
  have hperfL : Group.IsPerfect ↥L := hQ.1
  set π : ↥L →* ↥(starImage 3 L) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).subgroupMap L with hπ
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).subgroupMap_surjective L
  have hπv : ∀ y : ↥L, ((π y : ↥(starImage 3 L)) : H ⧸ CFSG.pPrimeCore 3 H) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (y : H) := fun y => rfl
  set N₁ : Subgroup ↥L := (Subgroup.center ↥(starImage 3 L)).comap π with hN₁
  have hN₁n : N₁.Normal := Subgroup.Normal.comap inferInstance π
  have hN₁t : N₁ ≠ ⊤ := by
    intro htop
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3
    have hperf : Group.IsPerfect ↥(starImage 3 L) := Group.IsPerfect.ofSurjective (f := π) hπs
    have hall : ∀ a : ↥(starImage 3 L), a ∈ Subgroup.center ↥(starImage 3 L) := by
      intro a
      obtain ⟨l, rfl⟩ := hπs a
      have hl : l ∈ N₁ := htop ▸ Subgroup.mem_top l
      exact hl
    have hcomm : commutator ↥(starImage 3 L) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _ b _
      exact (Subgroup.mem_center_iff.mp (hall b) a).symm
    have h1 : π y = 1 := by
      have : (⊤ : Subgroup ↥(starImage 3 L)) = ⊥ := by
        rw [← hperf.commutator_eq_top, hcomm]
      have hm : π y ∈ (⊥ : Subgroup ↥(starImage 3 L)) := this ▸ Subgroup.mem_top _
      exact Subgroup.mem_bot.mp hm
    have hyK : (y : H) ∈ CFSG.pPrimeCore 3 H := by
      have := congrArg (fun a : ↥(starImage 3 L) => (a : H ⧸ CFSG.pPrimeCore 3 H)) h1
      simp only [hπv, OneMemClass.coe_one] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have hcop := coprime_orderOf_of_mem_pPrimeCore hyK
    rw [Subgroup.orderOf_coe, hy] at hcop
    exact absurd hcop (by norm_num)
  have hN₁c : N₁ ≤ Subgroup.center ↥L :=
    CFSG.Quasithin.Vol2.Ch11.SecA.le_center_of_normal_ne_top hQ hN₁t
  rintro ⟨z, hz⟩
  obtain ⟨l, rfl⟩ := hπs z
  have hlc : l ∈ Subgroup.center ↥L := hN₁c hz
  obtain ⟨k, hk⟩ := hZ ⟨l, hlc⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  show (π l) ^ 2 ^ k = 1
  rw [← map_pow]
  have : l ^ 2 ^ k = 1 := congrArg (fun a : ↥(Subgroup.center ↥L) => (a : ↥L)) hk
  rw [this, map_one]


section Decomp

omit [Finite H] in
theorem mk_mem_oPrimeResidualOf {x : H} {k : ℕ} (hx : orderOf x = 3 ^ k) :
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) x ∈
      oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) := by
  have h1 : orderOf ((QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) x) ∣ 3 ^ k := by
    rw [← hx]
    exact orderOf_map_dvd _ _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  exact Subgroup.subset_closure ⟨Subgroup.mem_top _, i, hi⟩

omit [Finite H] in
theorem pow_three_mem_pCoreOf {Y : Subgroup H} (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) {y : H}
    (hy : y ∈ Y) : y ^ 3 ∈ pCoreOf 2 Y := by
  have h := hYe (QuotientGroup.mk (⟨y, hy⟩ : ↥Y))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  exact ⟨_, h, rfl⟩

theorem pow_three_eq_one_of_odd {Y : Subgroup H} (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) {x : H}
    (hx : x ∈ Y) (hodd : Odd (orderOf x)) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : x ^ 3 ∈ pCoreOf 2 Y := pow_three_mem_pCoreOf hYe hx
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) ⟨x ^ 3, h1⟩
  have h2 : (x ^ 3) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h3 : orderOf (x ^ 3) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
  have hodd' : Odd (orderOf (x ^ 3)) := hodd.of_dvd_nat (orderOf_pow_dvd 3)
  have hcop : Nat.Coprime (orderOf (x ^ 3)) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd')
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h3)


theorem decomposition_of_star {L Y : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) (hYo : oTwoUpper Y = Y) (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1)
    (hLP : starImage 3 L ≤ oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)))
    (hidx : Nat.card ↥(oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H))) =
      3 * Nat.card ↥(starImage 3 L)) :
    Y ≤ L ∨ ∃ y ∈ Y, orderOf y = 3 ∧ y ∉ L ∧
      Y = oTwoUpper (Y ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := CFSG.pPrimeCore 3 H with hK
  set φ := QuotientGroup.mk' K with hφ
  set P := oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) with hP
  set X := starImage 3 L with hX
  have hXn : X.Normal := Subgroup.Normal.map inferInstance φ (QuotientGroup.mk'_surjective _)
  have hodd3 : ∀ x ∈ Y, Odd (orderOf x) → orderOf x = 1 ∨ orderOf x = 3 := by
    intro x hx hodd
    have h1 : x ^ 3 = 1 := pow_three_eq_one_of_odd hYe hx hodd
    exact (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
  have hmemL : ∀ x ∈ Y, Odd (orderOf x) → φ x ∈ X → x ∈ L := by
    intro x hx hodd hxX
    rcases hodd3 x hx hodd with h | h
    · exact mem_of_mk_mem_starImage hQ h3 (k := 0) (by simpa using h) hxX
    · exact mem_of_mk_mem_starImage hQ h3 (k := 1) (by simpa using h) hxX
  have hYP : ∀ y ∈ Y, φ y ∈ P := by
    intro y hy
    rw [← hYo] at hy
    refine Subgroup.closure_induction (p := fun y _ => φ y ∈ P) ?_ ?_ ?_ ?_ hy
    · rintro x ⟨hx, hodd⟩
      rcases hodd3 x hx hodd with h | h
      · exact mk_mem_oPrimeResidualOf (k := 0) (by simpa using h)
      · exact mk_mem_oPrimeResidualOf (k := 1) (by simpa using h)
    · simp
    · intro x y _ _ hx hy
      rw [map_mul]
      exact P.mul_mem hx hy
    · intro x _ hx
      rw [map_inv]
      exact P.inv_mem hx
  have hXP : X ≤ P := hLP
  have hX'n : (X.subgroupOf P).Normal := hXn.subgroupOf P
  have hcardX' : Nat.card ↥(X.subgroupOf P) = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXP).toEquiv
  have hXpos : 0 < Nat.card ↥X := Nat.card_pos
  have hq3 : Nat.card (↥P ⧸ X.subgroupOf P) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (X.subgroupOf P)
    rw [hcardX', hidx] at h
    exact (Nat.eq_of_mul_eq_mul_right hXpos h).symm
  let ψ : ↥Y →* ↥P := (φ.comp Y.subtype).codRestrict P fun y => hYP y y.2
  let ρ : ↥Y →* ↥P ⧸ X.subgroupOf P := (QuotientGroup.mk' (X.subgroupOf P)).comp ψ
  have hρ1 : ∀ (x : H) (hx : x ∈ Y), ρ ⟨x, hx⟩ = 1 ↔ φ x ∈ X := by
    intro x hx
    show (QuotientGroup.mk' (X.subgroupOf P)) (ψ ⟨x, hx⟩) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  by_cases hall : ∀ x ∈ Y, Odd (orderOf x) → φ x ∈ X
  · left
    rw [← hYo]
    refine (Subgroup.closure_le L).mpr ?_
    rintro x ⟨hx, hodd⟩
    exact hmemL x hx hodd (hall x hx hodd)
  · right
    push Not at hall
    obtain ⟨y, hyY, hyodd, hyX⟩ := hall
    have hy3 : y ^ 3 = 1 := pow_three_eq_one_of_odd hYe hyY hyodd
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hyX (by rw [map_one]; exact X.one_mem)
    have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hyL : y ∉ L := fun h => hyX ⟨y, h, rfl⟩
    refine ⟨y, hyY, hyord, hyL, ?_⟩
    apply le_antisymm
    · refine le_trans hYo.symm.le ?_
      refine (Subgroup.closure_le _).mpr ?_
      rintro z ⟨hzY, hzodd⟩
      by_cases hzX : φ z ∈ X
      · have hzL := hmemL z hzY hzodd hzX
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (mem_oTwoUpper_of_odd ⟨hzY, hzL⟩ hzodd))
      · have hρy : ρ ⟨y, hyY⟩ ≠ 1 := fun h => hyX ((hρ1 y hyY).mp h)
        have hordρ : orderOf (ρ ⟨y, hyY⟩) = 3 := by
          apply orderOf_eq_prime _ hρy
          rw [← map_pow]
          have : (⟨y, hyY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
          rw [this, map_one]
        have hztop : Subgroup.zpowers (ρ ⟨y, hyY⟩) = ⊤ := by
          apply Subgroup.eq_top_of_card_eq
          rw [Nat.card_zpowers, hordρ, hq3]
        have hzmem : ρ ⟨z, hzY⟩ ∈ Subgroup.zpowers (ρ ⟨y, hyY⟩) := hztop ▸ Subgroup.mem_top _
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzmem
        have hykY : y ^ k ∈ Y := Y.zpow_mem hyY k
        set r : H := z * (y ^ k)⁻¹ with hr
        have hrY : r ∈ Y := Y.mul_mem hzY (Y.inv_mem hykY)
        have hρr : ρ ⟨r, hrY⟩ = 1 := by
          have : (⟨r, hrY⟩ : ↥Y) = ⟨z, hzY⟩ * (⟨y, hyY⟩ ^ k)⁻¹ := rfl
          rw [this, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
        have hφr : φ r ∈ X := (hρ1 r hrY).mp hρr
        have hr3 : r ^ 3 ∈ pCoreOf 2 Y := pow_three_mem_pCoreOf hYe hrY
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) ⟨r ^ 3, hr3⟩
        have ha' : (r ^ 3) ^ 2 ^ a = 1 := congrArg Subtype.val ha
        obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 ^ a = 3 * m + 1 := by
          have : 4 ^ a % 3 = 1 := by rw [Nat.pow_mod]; norm_num
          exact ⟨4 ^ a / 3, by omega⟩
        have h4 : (4 : ℕ) ^ a = 2 ^ a * 2 ^ a := by
          rw [← mul_pow]
          norm_num
        set r₃ : H := r ^ 4 ^ a with hr₃
        have hr₃Y : r₃ ∈ Y := Y.pow_mem hrY _
        have hr₃3 : r₃ ^ 3 = 1 := by
          rw [hr₃, ← pow_mul, mul_comm, pow_mul, h4, pow_mul, ha', one_pow]
        have hr₃odd : Odd (orderOf r₃) :=
          Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hr₃3)
        have hφr₃ : φ r₃ ∈ X := by
          rw [hr₃, map_pow]
          exact X.pow_mem hφr _
        have hr₃L : r₃ ∈ L := hmemL r₃ hr₃Y hr₃odd hφr₃
        have hr₃A : r₃ ∈ oTwoUpper (Y ⊓ L) := mem_oTwoUpper_of_odd ⟨hr₃Y, hr₃L⟩ hr₃odd
        have hr₂ : ((r ^ 3) ^ m)⁻¹ ∈ pCoreOf 2 Y :=
          (pCoreOf 2 Y).inv_mem ((pCoreOf 2 Y).pow_mem hr3 m)
        have hr₃eq : r₃ = (r ^ 3) ^ m * r := by
          rw [hr₃, hm, pow_succ, pow_mul]
        have hrr : r = ((r ^ 3) ^ m)⁻¹ * r₃ := by
          rw [hr₃eq]
          exact (inv_mul_cancel_left _ _).symm
        have hzr : z = r * y ^ k := by simp [hr]
        have hyk : y ^ k ∈ Subgroup.zpowers y := Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k
        rw [hzr, hrr, mul_assoc]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hr₂)
          (Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.mem_sup_left hr₃A)
            (Subgroup.mem_sup_right hyk)))
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact (oTwoUpper_le _).trans inf_le_left
      · exact (Subgroup.zpowers_le.mpr hyY)
      · exact CFSG.LieType.BorelTits.pCoreOf_le 2 Y

end Decomp

section Data

theorem psl3_data {X : Type} [Group X] {r e : ℕ} (h : IsPSL 3 r e X) :
    Finite X ∧ IsSimpleGroup X ∧ r.Prime ∧ 1 ≤ e ∧
      Nat.card X * Nat.gcd 3 (r ^ e - 1) =
        (r ^ e) ^ 3 * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 - 1)) :=
  CFSG.Quasithin.R3c6.psl3Data h

theorem psu3_data {X : Type} [Group X] {r e : ℕ} (h : IsPSU 3 r e X) :
    Finite X ∧ IsSimpleGroup X ∧ r.Prime ∧ 1 ≤ e ∧
      Nat.card X * Nat.gcd 3 (r ^ e + 1) =
        (r ^ e) ^ 3 * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 + 1)) :=
  CFSG.Quasithin.R3c6.psu3Data h

theorem isPSLEps3_finite_simple {s : Bool} {p e : ℕ} {X : Type} [Group X] (h : IsPSLEps3 s p e X) :
    Finite X ∧ IsSimpleGroup X := by
  cases s
  · exact ⟨(psu3_data h).1, (psu3_data h).2.1⟩
  · exact ⟨(psl3_data h).1, (psl3_data h).2.1⟩

theorem card_eq_of_isPSLEps3 {s : Bool} {p e : ℕ} {X Y : Type} [Group X] [Group Y]
    (hX : IsPSLEps3 s p e X) (hY : IsPSLEps3 s p e Y) : Nat.card X = Nat.card Y := by
  cases s
  · obtain ⟨-, -, -, -, hX'⟩ := psu3_data hX
    obtain ⟨-, -, -, -, hY'⟩ := psu3_data hY
    have hpos : 0 < Nat.gcd 3 (p ^ e + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    exact Nat.eq_of_mul_eq_mul_right hpos (hX'.trans hY'.symm)
  · obtain ⟨-, -, -, -, hX'⟩ := psl3_data hX
    obtain ⟨-, -, -, -, hY'⟩ := psl3_data hY
    have hpos : 0 < Nat.gcd 3 (p ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    exact Nat.eq_of_mul_eq_mul_right hpos (hX'.trans hY'.symm)

end Data

section Circ

theorem three_dvd_card_starImage {L : Subgroup H} (h3 : 3 ∣ Nat.card ↥L) :
    3 ∣ Nat.card ↥(starImage 3 L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3
  have hy3 : (y : H) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hyK : (y : H) ∉ CFSG.pPrimeCore 3 H := by
    intro hyK
    have hcop := coprime_orderOf_of_mem_pPrimeCore hyK
    rw [Subgroup.orderOf_coe, hy] at hcop
    exact absurd hcop (by norm_num)
  have hφy : QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (y : H) ≠ 1 := by
    intro h
    exact hyK ((QuotientGroup.eq_one_iff _).mp h)
  have hφ3 : (QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (y : H)) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have hord : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (y : H)) = 3 :=
    orderOf_eq_prime hφ3 hφy
  have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (y : H) ∈ starImage 3 L := ⟨y, y.2, rfl⟩
  have := Subgroup.orderOf_dvd_natCard (starImage 3 L) hmem
  rwa [hord] at this

theorem starImage_le_oPrimeResidualOf {L : Subgroup H} (hXs : IsSimpleGroup ↥(starImage 3 L))
    (h3X : 3 ∣ Nat.card ↥(starImage 3 L)) :
    starImage 3 L ≤ oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) := by
  have htop := R3c2.closure_orderOf_three_eq_top_of_simple (X := ↥(starImage 3 L)) h3X
  intro x hx
  have hz : (⟨x, hx⟩ : ↥(starImage 3 L)) ∈ Subgroup.closure {y : ↥(starImage 3 L) | orderOf y = 3} :=
    htop ▸ Subgroup.mem_top _
  have key := Subgroup.closure_induction
    (p := fun (z : ↥(starImage 3 L)) _ => (z : PStar 3 H) ∈ oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)))
    (fun z hz => Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by
      rw [pow_one, Subgroup.orderOf_coe]
      exact hz⟩)
    (by simp) (fun a b _ _ ha hb => by simpa using Subgroup.mul_mem _ ha hb)
    (fun a _ ha => by simpa using Subgroup.inv_mem _ ha) hz
  exact key

theorem mk_mem_oPrimeResidualOf_of_mem {Y : Subgroup H} (hYo : oTwoUpper Y = Y)
    (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) {y : H} (hy : y ∈ Y) :
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) y ∈ oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) := by
  have hodd3 : ∀ x ∈ Y, Odd (orderOf x) → orderOf x = 1 ∨ orderOf x = 3 := by
    intro x hx hodd
    have h1 : x ^ 3 = 1 := pow_three_eq_one_of_odd hYe hx hodd
    exact (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
  rw [← hYo] at hy
  refine Subgroup.closure_induction
    (p := fun y _ => (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) y ∈
      oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H))) ?_ ?_ ?_ ?_ hy
  · rintro x ⟨hx, hodd⟩
    rcases hodd3 x hx hodd with h | h
    · exact mk_mem_oPrimeResidualOf (k := 0) (by simpa using h)
    · exact mk_mem_oPrimeResidualOf (k := 1) (by simpa using h)
  · simp
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

end Circ

section CircCase

theorem mem_of_mk_mem_of_odd {L Y : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) {x : H} (hx : x ∈ Y)
    (hodd : Odd (orderOf x))
    (hxX : QuotientGroup.mk' (CFSG.pPrimeCore 3 H) x ∈ starImage 3 L) : x ∈ L := by
  have h1 : x ^ 3 = 1 := pow_three_eq_one_of_odd hYe hx hodd
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
  · exact mem_of_mk_mem_starImage hQ h3 (k := 0) (by simpa using h) hxX
  · exact mem_of_mk_mem_starImage hQ h3 (k := 1) (by simpa using h) hxX

theorem le_of_circ {L Y : Subgroup H} [L.Normal] (hQ : CFSG.IsQuasisimple ↥L)
    (h3 : 3 ∣ Nat.card ↥L) (hYo : oTwoUpper Y = Y) (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1)
    {s : Bool} {q : ℕ} (hSq : IsPSLEps3q s q ↥(starImage 3 L))
    (hcirc : ∃ m : ℕ, q = 2 ^ (3 * m) ∧
      IsL3CircAbstract s q ↥(oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)))) : Y ≤ L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) with hP
  set X := starImage 3 L with hX
  obtain ⟨m, hqm, e, L₀, hL₀n, hqe, hL₀, hidx3, hC, h3L₀⟩ := hcirc
  obtain ⟨p, e', hp, he', hqp, hX'⟩ := hSq
  have hpe : p = 2 ∧ e' = e := by
    have h1 : p ^ e' = 2 ^ e := hqp.symm.trans hqe
    have h2 : p ∣ 2 := by
      have : p ∣ 2 ^ e := h1 ▸ dvd_pow_self p (by omega)
      exact hp.dvd_of_dvd_pow this
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    subst hp2
    exact ⟨rfl, Nat.pow_right_injective le_rfl h1⟩
  obtain ⟨rfl, rfl⟩ := hpe
  obtain ⟨hXfin, hXs⟩ := isPSLEps3_finite_simple hX'
  have h3X : 3 ∣ Nat.card ↥X := three_dvd_card_starImage h3
  have hXP : X ≤ P := starImage_le_oPrimeResidualOf hXs h3X
  have hcard : Nat.card ↥X = Nat.card ↥L₀ := card_eq_of_isPSLEps3 hX' hL₀
  have hX'cardeq : Nat.card ↥(X.subgroupOf P) = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXP).toEquiv
  have hXsub : IsSimpleGroup ↥(X.subgroupOf P) := by
    have := hXs
    exact (Subgroup.subgroupOfEquivOfLe hXP).isSimpleGroup
  have := hXsub
  have h3X' : 3 ∣ Nat.card ↥(X.subgroupOf P) := by rw [hX'cardeq]; exact h3X
  have htop := R3c2.closure_orderOf_three_eq_top_of_simple (X := ↥(X.subgroupOf P)) h3X'
  have hle : X.subgroupOf P ≤ L₀ := by
    intro a ha
    have hz : (⟨a, ha⟩ : ↥(X.subgroupOf P)) ∈
        Subgroup.closure {y : ↥(X.subgroupOf P) | orderOf y = 3} := htop ▸ Subgroup.mem_top _
    exact Subgroup.closure_induction
      (p := fun (z : ↥(X.subgroupOf P)) _ => (z : ↥P) ∈ L₀)
      (fun z hz => h3L₀ _ (by rw [Subgroup.orderOf_coe]; exact hz))
      L₀.one_mem (fun a b _ _ ha hb => L₀.mul_mem ha hb) (fun a _ ha => L₀.inv_mem ha) hz
  have heq : X.subgroupOf P = L₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hX'cardeq, hcard])
  have hodd3 : ∀ x ∈ Y, Odd (orderOf x) → orderOf x = 1 ∨ orderOf x = 3 := by
    intro x hx hodd
    have h1 : x ^ 3 = 1 := pow_three_eq_one_of_odd hYe hx hodd
    exact (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
  rw [← hYo]
  refine (Subgroup.closure_le L).mpr ?_
  rintro x ⟨hx, hodd⟩
  have hxP := mk_mem_oPrimeResidualOf_of_mem hYo hYe hx
  have hxL₀ : (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 H) x, hxP⟩ : ↥P) ∈ L₀ := by
    rcases hodd3 x hx hodd with h | h
    · have : x = 1 := orderOf_eq_one_iff.mp h
      subst this
      have : (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 H) 1, hxP⟩ : ↥P) = 1 := Subtype.ext (map_one _)
      rw [this]
      exact L₀.one_mem
    · apply h3L₀
      rw [Subgroup.orderOf_mk]
      have h1 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 H) x) ∣ 3 := by
        rw [← h]
        exact orderOf_map_dvd _ _
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
      · exfalso
        have hx1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 H) x = 1 := orderOf_eq_one_iff.mp h2
        have hxK : x ∈ CFSG.pPrimeCore 3 H := (QuotientGroup.eq_one_iff _).mp hx1
        have hcop := coprime_orderOf_of_mem_pPrimeCore hxK
        rw [h] at hcop
        exact absurd hcop (by norm_num)
      · exact h2
  have hxX : QuotientGroup.mk' (CFSG.pPrimeCore 3 H) x ∈ X := by
    have : (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 H) x, hxP⟩ : ↥P) ∈ X.subgroupOf P := heq ▸ hxL₀
    exact this
  exact mem_of_mk_mem_of_odd hQ h3 hYe hx hodd hxX

end CircCase

section QuotPCore

theorem pCore_two_eq_center {L : Type} [Group L] [Finite L] (hQ : CFSG.IsQuasisimple L)
    (hZ : IsPGroup 2 ↥(Subgroup.center L)) (h3 : 3 ∣ Nat.card L) :
    CFSG.pCore 2 L = Subgroup.center L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hT : CFSG.pCore 2 L ≠ ⊤ := by
      intro hT
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 h3
      have hyP : y ∈ CFSG.pCore 2 L := hT ▸ Subgroup.mem_top y
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨y, hyP⟩
      have h1 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
      rw [hy] at h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
    exact CFSG.Quasithin.Vol2.Ch11.SecA.le_center_of_normal_ne_top hQ hT
  · exact le_sSup ⟨inferInstance, hZ⟩

theorem isQuasisimple_quot_pCore_two {L : Type} [Group L] [Finite L] (hQ : CFSG.IsQuasisimple L)
    (hZ : IsPGroup 2 ↥(Subgroup.center L)) (h3 : 3 ∣ Nat.card L) :
    CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) := by
  have hc := pCore_two_eq_center hQ hZ h3
  have e : (L ⧸ Subgroup.center L) ≃* (L ⧸ CFSG.pCore 2 L) :=
    QuotientGroup.quotientMulEquivOfEq hc.symm
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e ?_
  have hbot : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
    have hs := hQ.2.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (L ⧸ Subgroup.center L)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hQ.2.2
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a)) b).symm
  have e2 : (L ⧸ Subgroup.center L) ⧸ Subgroup.center (L ⧸ Subgroup.center L) ≃*
      (L ⧸ Subgroup.center L) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨?_, e2.isSimpleGroup_congr.mpr hQ.2.1, ?_⟩
  · have := hQ.1
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _)
  · obtain ⟨a, b, hab⟩ := hQ.2.2
    exact ⟨e2.symm a, e2.symm b, fun h =>
      hab (e2.symm.injective (by rw [map_mul, map_mul]; exact h))⟩

end QuotPCore

section RankTwo

@[expose] def PGLIndex : Prop :=
  ∀ (s : Bool) (q : ℕ) (A : Type) [Group A] [Finite A] (P X : Subgroup A), X ≤ P →
    IsPGLEps3 s q ↥P → IsPSLEps3q s q ↥X → Int.ModEq 3 (q : ℤ) (if s then 1 else -1) →
      Nat.card ↥P = 3 * Nat.card ↥X

theorem rankTwo_H (hF : A318Facts)
    (hE3 : ∀ (X : Type) [Group X] [Finite X], A318Case3Group X → Nat.card (Subgroup.center X) = 3)
    (hidx : PGLIndex) {H : Type} [Group H] [Finite H] (hH : SQTKGroup H)
    (h36 : A36Statement (H ⧸ CFSG.pCore 2 H)) (h38 : A38Part3 (H ⧸ CFSG.pCore 2 H))
    {L Y : Subgroup H} (hL : L ∈ cComp (⊤ : Subgroup H)) (hQ : CFSG.IsQuasisimple ↥L)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) (hr : 1 < CFSG.Open.pRank 3 L)
    (hYo : oTwoUpper Y = Y) (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) :
    Y ≤ L ∨
      ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
        IsPSLEps3q s q ↥(starImage 3 L) ∧
        IsPGLEps3 s q ↥(oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H))) ∧
        starImage 3 L ≤ oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) ∧
        Nat.card ↥(oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H))) = 3 * Nat.card ↥(starImage 3 L) ∧
        ∃ y ∈ Y, orderOf y = 3 ∧ y ∉ L ∧
          Y = oTwoUpper (Y ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLn : L.Normal := A318.normal_of_pRank_gt_one hH h38 hL Nat.prime_three (by norm_num) hr
  have h3 : 3 ∣ Nat.card ↥L := by
    refine R3c2.three_dvd_card_of_one_le_pRank L (by omega)
  have hQ' : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := isQuasisimple_quot_pCore_two hQ hZ h3
  rcases a318 hF hH h36 h38 hL hQ' Nat.prime_three (by norm_num) hr with h1 | ⟨-, h2⟩ | ⟨-, h3g, -⟩
  · left
    rw [← hYo]
    refine (Subgroup.closure_le L).mpr ?_
    rintro x ⟨hx, hodd⟩
    have h1' : x ^ 3 = 1 := pow_three_eq_one_of_odd hYe hx hodd
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1') with h | h
    · rw [h1]
      exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 0, by simpa using h⟩
    · rw [h1]
      exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by simpa using h⟩
  · obtain ⟨s, q, hqmod, hSq, hP⟩ := h2
    have hX3 : 3 ∣ Nat.card ↥(starImage 3 L) := three_dvd_card_starImage h3
    rcases hP with hPGL | ⟨m, hqm, hcirc⟩
    · obtain ⟨p, e, hp, he, hqp, hX'⟩ := hSq
      have hSq' : IsPSLEps3q s q ↥(starImage 3 L) := ⟨p, e, hp, he, hqp, hX'⟩
      have hXs : IsSimpleGroup ↥(starImage 3 L) := (isPSLEps3_finite_simple hX').2
      have hXP := starImage_le_oPrimeResidualOf hXs hX3
      have hcard := hidx s q (PStar 3 H) _ _ hXP hPGL hSq' hqmod
      rcases decomposition_of_star hQ h3 hYo hYe hXP hcard with hYL | ⟨y, hyY, hyord, hyL, hdec⟩
      · exact Or.inl hYL
      · exact Or.inr ⟨s, q, hqmod, hSq', hPGL, hXP, hcard, y, hyY, hyord, hyL, hdec⟩
    · exact Or.inl (le_of_circ hQ h3 hYo hYe hSq ⟨m, hqm, hcirc⟩)
  · exfalso
    have hc := hE3 _ h3g
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_two_center_starImage hQ h3 hZ)
    rw [hn] at hc
    have : 3 ∣ 2 ^ n := ⟨1, by omega⟩
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega

end RankTwo

end CFSG.Quasithin.R3c5
