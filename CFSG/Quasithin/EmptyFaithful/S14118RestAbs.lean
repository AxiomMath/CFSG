module

public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

section Group

variable {A : Type} [Group A] [Finite A]

theorem commutator_eq_of_not_le_centralizer {P T' : Subgroup A} (hPn : P.Normal)
    (hP3 : Nat.card P = 3) (hcomm : ¬ T' ≤ Subgroup.centralizer (P : Set A)) : ⁅P, T'⁆ = P := by
  have hle : ⁅P, T'⁆ ≤ P := Subgroup.commutator_le_left P T'
  have hdvd : Nat.card (⁅P, T'⁆ : Subgroup A) ∣ 3 := hP3 ▸ Subgroup.card_dvd_of_le hle
  have hcases : Nat.card (⁅P, T'⁆ : Subgroup A) = 1 ∨ Nat.card (⁅P, T'⁆ : Subgroup A) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hdvd
  rcases hcases with h1 | h3
  · exfalso
    apply hcomm
    have hbot : ⁅P, T'⁆ = ⊥ := Subgroup.card_eq_one.mp h1
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact hbot
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP3, h3])

omit [Finite A] in
theorem conjClosure_top_eq_top {P T' : Subgroup A} (hPT : P ⊔ T' = ⊤) (hPc : ⁅P, T'⁆ = P) :
    conjClosure T' ⊤ = ⊤ := by
  have hcomm_le : ⁅P, T'⁆ ≤ conjClosure T' ⊤ := by
    refine Subgroup.commutator_le.mpr fun p hp t ht => ?_
    have h1 : p * t * p⁻¹ ∈ conjClosure T' ⊤ := mem_conjClosure (Subgroup.mem_top p) ht
    have h2 : t⁻¹ ∈ conjClosure T' ⊤ := le_conjClosure T' ⊤ (T'.inv_mem ht)
    have := (conjClosure T' ⊤).mul_mem h1 h2
    simpa [commutatorElement_def, mul_assoc] using this
  have hP : P ≤ conjClosure T' ⊤ := hPc.ge.trans hcomm_le
  refine eq_top_iff.mpr ?_
  calc (⊤ : Subgroup A) = P ⊔ T' := hPT.symm
    _ ≤ conjClosure T' ⊤ := sup_le hP (le_conjClosure T' ⊤)

omit [Finite A] in
theorem oTwoUpper_top_eq {P : Subgroup A} (hPn : P.Normal) (hodd : Odd (Nat.card P))
    (hidx : P.index = 2) : oTwoUpper (⊤ : Subgroup A) = P := by
  have hP : P = oTwoUpper P := by
    refine le_antisymm (fun x hx => ?_) (oTwoUpper_le P)
    refine mem_oTwoUpper_of_odd hx ?_
    have hd : orderOf (⟨x, hx⟩ : P) ∣ Nat.card P := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact Odd.of_dvd_nat hodd hd
  refine (eq_oTwoUpper_of_pow_mem le_top (fun x _ => ⟨1, ?_⟩) hP).symm
  rw [pow_one, show (2 : ℕ) = P.index from hidx.symm]
  exact Subgroup.pow_index_mem P x

end Group

section Inversion

variable {Q : Type*} [Group Q]

theorem inv_of_le_commutator {Y : Subgroup Q} (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) {s : Q}
    (hs2 : s * s = 1) (hsY : s ∈ Subgroup.normalizer (Y : Set Q))
    (hYc : Y ≤ ⁅Y, Subgroup.zpowers s⁆) : ∀ y ∈ Y, s * y * s⁻¹ = y⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  let N₀ : Subgroup Q :=
    { carrier := {z | z ∈ Y ∧ s * z * s⁻¹ = z⁻¹}
      one_mem' := ⟨Y.one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨Y.mul_mem ha.1 hb.1, ?_⟩
        have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        rw [e, ha.2, hb.2]
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
          _ = (a * b)⁻¹ := by rw [hab b hb.1 a ha.1]
      inv_mem' := fun {a} ha => by
        refine ⟨Y.inv_mem ha.1, ?_⟩
        have e : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
        rw [e, ha.2] }
  have hle : ⁅Y, Subgroup.zpowers s⁆ ≤ N₀ := by
    refine Subgroup.commutator_le.mpr fun y hy g hg => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hsk : s ^ k = 1 ∨ s ^ k = s := by
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · left
        rw [zpow_mul, show s ^ (2 : ℤ) = 1 by rw [zpow_two, hs2], one_zpow]
      · right
        rw [zpow_add, zpow_mul, show s ^ (2 : ℤ) = 1 by rw [zpow_two, hs2], one_zpow, one_mul,
          zpow_one]
    rcases hsk with h1 | h1
    · rw [h1]
      exact ⟨by simp [commutatorElement_def], by simp [commutatorElement_def]⟩
    · rw [h1]
      have hsyi : s * y⁻¹ * s⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hsY y⁻¹).mp (Y.inv_mem hy)
      refine ⟨?_, ?_⟩
      · have : ⁅y, s⁆ = y * (s * y⁻¹ * s⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact Y.mul_mem hy hsyi
      · simp only [commutatorElement_def, hsi]
        have e1 : s * (y * s * y⁻¹ * s) * s = s * y * s * y⁻¹ * (s * s) := by group
        have e2 : (y * s * y⁻¹ * s)⁻¹ = s * y * s * y⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hsi]
          group
        rw [e1, hs2, mul_one, e2]
  exact fun y hy => (hle (hYc hy)).2

theorem eq_one_of_commute_of_le_commutator {Y : Subgroup Q} (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hodd : ∀ y ∈ Y, Odd (orderOf y)) {s : Q} (hs2 : s * s = 1)
    (hsY : s ∈ Subgroup.normalizer (Y : Set Q)) (hYc : Y ≤ ⁅Y, Subgroup.zpowers s⁆) {d : Q}
    (hd : d ∈ Y) (hds : s * d = d * s) : d = 1 := by
  have hinv := inv_of_le_commutator hab hs2 hsY hYc d hd
  have h1 : s * d * s⁻¹ = d := by rw [hds]; group
  rw [h1] at hinv
  have h2 : d * d = 1 := by
    calc d * d = d * d⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel d
  have hdvd : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hodd d hd) (by decide)

end Inversion

section Main

variable {Q A : Type} [Group Q] [Finite Q] [Group A] [Finite A]

theorem odd_card_of_forall_odd_orderOf {Y : Type*} [Group Y] [Finite Y]
    (h : ∀ y : Y, Odd (orderOf y)) : Odd (Nat.card Y) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card Y := by
    rcases Nat.even_or_odd (Nat.card Y) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 h2
  exact absurd (hx ▸ h x) (by decide)

theorem s3_extension (hQ : CFSG.pCore 2 Q = ⊥) (ρ : Q →* A) (hρ : Function.Surjective ρ)
    {P T' : Subgroup A} (hA6 : Nat.card A = 6) (hPn : P.Normal) (hP3 : Nat.card P = 3)
    (hT2 : Nat.card T' = 2) (hPT : P ⊔ T' = ⊤) (hcomm : ¬ T' ≤ Subgroup.centralizer (P : Set A))
    {S : Subgroup Q} (hSinj : ∀ x ∈ S, ρ x = 1 → x = 1) (hSimg : S.map ρ = T')
    (hker : ∀ w ∈ conjClosure S ⊤, ∀ c ∈ ρ.ker, c * w = w * c) :
    (oTwoUpper (conjClosure S ⊤)).map ρ = P ∧
      (∀ y ∈ oTwoUpper (conjClosure S ⊤), ρ y = 1 → y = 1) ∧
      Nat.card (oTwoUpper (conjClosure S ⊤)) = 3 ∧
      ∃ s ∈ S, S = Subgroup.zpowers s ∧ s * s = 1 ∧ s ≠ 1 ∧
        ∀ y ∈ oTwoUpper (conjClosure S ⊤), s * y * s⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPc : ⁅P, T'⁆ = P := commutator_eq_of_not_le_centralizer hPn hP3 hcomm
  set Wh : Subgroup Q := conjClosure S ⊤ with hWh
  set Yh : Subgroup Q := oTwoUpper Wh with hYh
  have hSW : S ≤ Wh := le_conjClosure S ⊤
  have hYW : Yh ≤ Wh := oTwoUpper_le Wh
  have hρW : Wh.map ρ = ⊤ := by
    rw [hWh, map_conjClosure_eq, hSimg, Subgroup.map_top_of_surjective ρ hρ]
    exact conjClosure_top_eq_top hPT hPc
  have hdecomp : ∀ g : Q, ∃ w ∈ Wh, w⁻¹ * g ∈ ρ.ker := by
    intro g
    have : ρ g ∈ Wh.map ρ := by rw [hρW]; trivial
    obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.mp this
    exact ⟨w, hw, by rw [MonoidHom.mem_ker, map_mul, map_inv, hwg, inv_mul_cancel]⟩
  have hcentral : ∀ d ∈ Wh, ρ d = 1 → ∀ g : Q, g * d = d * g := by
    intro d hd hρd g
    obtain ⟨w, hw, hk⟩ := hdecomp g
    have hg : g = w * (w⁻¹ * g) := by group
    have h1 : (w⁻¹ * g) * d = d * (w⁻¹ * g) := hker d hd _ hk
    have h2 : d * w = w * d := hker w hw d hρd
    rw [hg]
    calc w * (w⁻¹ * g) * d = w * ((w⁻¹ * g) * d) := by rw [mul_assoc]
      _ = w * (d * (w⁻¹ * g)) := by rw [h1]
      _ = (w * d) * (w⁻¹ * g) := by rw [mul_assoc]
      _ = (d * w) * (w⁻¹ * g) := by rw [h2]
      _ = d * (w * (w⁻¹ * g)) := by rw [mul_assoc]
  have hodd_ker : ∀ d ∈ Wh, ρ d = 1 → Odd (orderOf d) := fun d hd hρd =>
    odd_orderOf_of_central_of_normal hQ (C := ⊤) inferInstance (Subgroup.mem_top d)
      (fun c _ => hcentral d hd hρd c)
  have hρY : Yh.map ρ = P := by
    have h1 : oTwoUpper (Wh.map ρ) = Yh.map ρ := oTwoUpper_map ρ Wh
    rw [← h1, hρW]
    have hidx : P.index = 2 := by
      have := P.card_mul_index
      rw [hP3, hA6] at this
      omega
    exact oTwoUpper_top_eq hPn (by rw [hP3]; decide) hidx
  have hY_odd : ∀ y ∈ Yh, Odd (orderOf y) := by
    intro y hy
    have hρy : ρ y ∈ P := hρY ▸ Subgroup.mem_map_of_mem ρ hy
    have h3 : (ρ y) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := P) (x := ⟨ρ y, hρy⟩)
      rw [hP3] at this
      exact congrArg Subtype.val this
    have hy3W : y ^ 3 ∈ Wh := Subgroup.pow_mem _ (hYW hy) 3
    have hodd3 := hodd_ker (y ^ 3) hy3W (by rw [map_pow]; exact h3)
    have hd : orderOf y ∣ 3 * orderOf (y ^ 3) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat (Odd.mul (by decide) hodd3) hd
  have hab : ∀ a ∈ Yh, ∀ b ∈ Yh, a * b = b * a := by
    have : IsCyclic ↥P := isCyclic_of_prime_card hP3
    let f : ↥Yh →* ↥P := (ρ.comp Yh.subtype).codRestrict P
      (fun y => hρY ▸ Subgroup.mem_map_of_mem ρ y.2)
    have hf : f.ker ≤ Subgroup.center ↥Yh := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro z
      have hρy : ρ (y : Q) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
        simpa [f] using this
      exact Subtype.ext (hcentral (y : Q) (hYW y.2) hρy (z : Q))
    intro a ha b hb
    exact congrArg Subtype.val
      ((f.isMulCommutative_of_isCyclic_of_ker_le_center hf).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hScard : Nat.card S = 2 := by
    have hinj : Function.Injective (ρ.comp S.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hSinj x x.2 hx)
    have hrange : (ρ.comp S.subtype).range = T' := by
      rw [← hSimg]
      ext a
      simp [MonoidHom.mem_range, Subgroup.mem_map]
    calc Nat.card S = Nat.card (ρ.comp S.subtype).range :=
          Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      _ = Nat.card T' := by rw [hrange]
      _ = 2 := hT2
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 1) (by rw [hScard]; rfl)
  obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card S = 1 := Subgroup.card_eq_one.mpr
      (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
    omega
  have hs2' : s ^ 2 = 1 := by
    have hd : orderOf (⟨s, hsS⟩ : S) ∣ Nat.card S := orderOf_dvd_natCard _
    rw [hScard] at hd
    have hne : (⟨s, hsS⟩ : S) ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
    have h2 : orderOf (⟨s, hsS⟩ : S) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h2
    have := pow_orderOf_eq_one (⟨s, hsS⟩ : S)
    rw [h2] at this
    exact congrArg Subtype.val this
  have hs2 : s * s = 1 := by rw [← pow_two]; exact hs2'
  have hSz : S = Subgroup.zpowers s := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsS) ?_).symm
    rw [hScard, Nat.card_zpowers, orderOf_eq_prime hs2' hs1]
  have hSN : S ≤ Subgroup.normalizer (Yh : Set Q) := hSW.trans (le_normalizer_oTwoUpper Wh)
  have hYodd : Odd (Nat.card Yh) := odd_card_of_forall_odd_orderOf
    (fun y => by rw [← Subgroup.orderOf_coe]; exact hY_odd y y.2)
  have hgen : Wh = conjClosure S (Yh ⊔ S) := by
    apply le_antisymm
    · refine conjClosure_le fun g _ σ hσ => ?_
      have hρYS : (Yh ⊔ S).map ρ = ⊤ := by rw [Subgroup.map_sup, hρY, hSimg, hPT]
      have : ρ g ∈ (Yh ⊔ S).map ρ := by rw [hρYS]; trivial
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp this
      have hk : x⁻¹ * g ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
      have hkσ : (x⁻¹ * g) * σ = σ * (x⁻¹ * g) := hker σ (hSW hσ) _ hk
      have e : g * σ * g⁻¹ = x * σ * x⁻¹ := by
        have hg : g = x * (x⁻¹ * g) := by group
        calc g * σ * g⁻¹ = (x * (x⁻¹ * g)) * σ * (x * (x⁻¹ * g))⁻¹ := by rw [← hg]
          _ = x * (((x⁻¹ * g) * σ) * (x⁻¹ * g)⁻¹) * x⁻¹ := by group
          _ = x * σ * x⁻¹ := by rw [hkσ]; group
      rw [e]
      exact mem_conjClosure hx hσ
    · exact conjClosure_le fun g _ σ hσ => mem_conjClosure (Subgroup.mem_top g) hσ
  have hYeq : Yh = ⁅Yh, S⁆ := by
    have h1 : conjClosure S (Yh ⊔ S) = ⁅Yh, S⁆ ⊔ S :=
      conjClosure_sup_eq_commutator_sup hSN Subgroup.le_normalizer
    have h2 : oTwoUpper (⁅Yh, S⁆ ⊔ S) = ⁅Yh, S⁆ := oTwoUpper_commutator_sup hYodd hSp hSN
    calc Yh = oTwoUpper (conjClosure S (Yh ⊔ S)) := by rw [← hgen]
      _ = oTwoUpper (⁅Yh, S⁆ ⊔ S) := by rw [h1]
      _ = ⁅Yh, S⁆ := h2
  have hYc : Yh ≤ ⁅Yh, Subgroup.zpowers s⁆ := by rw [← hSz]; exact hYeq.le
  have hsN : s ∈ Subgroup.normalizer (Yh : Set Q) := hSN hsS
  have hinj_Y : ∀ y ∈ Yh, ρ y = 1 → y = 1 := fun y hy hρy =>
    eq_one_of_commute_of_le_commutator hab hY_odd hs2 hsN hYc hy
      (hcentral y (hYW hy) hρy s)
  refine ⟨hρY, hinj_Y, ?_, s, hsS, hSz, hs2, hs1, inv_of_le_commutator hab hs2 hsN hYc⟩
  have hinj : Function.Injective (ρ.comp Yh.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj_Y x x.2 hx)
  have hrange : (ρ.comp Yh.subtype).range = P := by
    rw [← hρY]
    ext a
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  calc Nat.card Yh = Nat.card (ρ.comp Yh.subtype).range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ = Nat.card P := by rw [hrange]
    _ = 3 := hP3

end Main

end CFSG.Quasithin
