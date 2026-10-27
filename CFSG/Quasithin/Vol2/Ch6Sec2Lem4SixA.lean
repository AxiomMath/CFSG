module

public import CFSG.RankThree.PartOne.K1214.PGroupCyclic
public import CFSG.CGT.PushingUpLit.CGT6.Diag.S2Transfer
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

theorem exists_noncentral_order_three624 {P : Type*} [Group P] [Finite P]
    (hperf : commutator P = ⊤) (h3 : 3 ∣ Nat.card P)
    (hZ : ∀ z ∈ Subgroup.center P, orderOf z = 3 → ∀ z' ∈ Subgroup.center P, orderOf z' = 3 →
      z' ∈ Subgroup.zpowers z) :
    ∃ x : P, orderOf x = 3 ∧ x ∉ Subgroup.center P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨S⟩ : Nonempty (Sylow 3 P) := inferInstance
  have hidx : ¬ 3 ∣ (S : Subgroup P).index := S.not_dvd_index
  have h3S : 3 ∣ Nat.card (S : Subgroup P) := by
    have hmul := (S : Subgroup P).card_mul_index
    rw [← hmul] at h3
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp h3 |>.resolve_right hidx
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S : Subgroup P)) 3 h3S
  have hb' : orderOf (b : P) = 3 := by rw [Subgroup.orderOf_coe, hb]
  have hbc : (b : P) ∈ Subgroup.center P := hcon _ hb'
  have hsub : ∀ z ∈ (S : Subgroup P), z ^ 3 = 1 → z ∈ Subgroup.zpowers (b : P) := by
    intro z _ hz3
    by_cases h1 : z = 1
    · rw [h1]
      exact Subgroup.one_mem _
    have hzo : orderOf z = 3 := orderOf_eq_prime hz3 h1
    exact hZ _ hbc hb' z (hcon z hzo) hzo
  have hcyc : IsCyclic ↥(S : Subgroup P) :=
    CFSG.RankThree.PartOne.K1214.isCyclic_subgroup_of_pow_eq_one_subset Nat.prime_three
      (by norm_num) S.isPGroup' b.2 hb' hsub
  have : IsMulCommutative ↥(S : Subgroup P) := ⟨⟨fun x y => IsCyclic.commGroup.mul_comm x y⟩⟩
  have hcop : Nat.Coprime (orderOf (b : P)) (S : Subgroup P).index := by
    rw [hb']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx
  have h1 := CFSG.CGT.PushingUpLit.CGT6.Diag.S2.central_eq_one_of_abelian_index hperf hbc hcop
  rw [h1, orderOf_one] at hb'
  omega

theorem comm_of_card_three624 {X : Type*} [Group X] {A : Subgroup X} (h : Nat.card A = 3)
    (a b : ↥A) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥A := isCyclic_of_prime_card h
  exact IsCyclic.commGroup.mul_comm a b

theorem pow_three_of_card624 {X : Type*} [Group X] {A : Subgroup X} (h : Nat.card A = 3)
    (a : ↥A) : a ^ 3 = 1 := by
  rw [← h]
  exact pow_card_eq_one'

theorem exists_elemAbelian27_of_commuting624 {X : Type*} [Group X] {A B C : Subgroup X}
    (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3) (hC3 : Nat.card C = 3)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hind : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  classical
  have hcBC : ∀ (b : ↥B) (c : ↥C), Commute (B.subtype b) (C.subtype c) := fun b c =>
    hBC b b.2 c c.2
  let fBC : ↥B × ↥C →* X := MonoidHom.noncommCoprod B.subtype C.subtype hcBC
  have hfBC : ∀ x : ↥B × ↥C, fBC x = (x.1 : X) * x.2 := fun x => rfl
  have hcA : ∀ (a : ↥A) (x : ↥B × ↥C), Commute (A.subtype a) (fBC x) := by
    intro a x
    rw [hfBC]
    exact Commute.mul_right (hAB a a.2 x.1 x.1.2) (hAC a a.2 x.2 x.2.2)
  let f : ↥A × (↥B × ↥C) →* X := MonoidHom.noncommCoprod A.subtype fBC hcA
  have hf' : ∀ x : ↥A × (↥B × ↥C), f x = (x.1 : X) * ((x.2.1 : X) * x.2.2) := fun x => rfl
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b, c⟩ h
    have h' : (a : X) * ((b : X) * c) = 1 := (hf' (a, b, c)).symm.trans (MonoidHom.mem_ker.1 h)
    obtain ⟨ha, hb, hc⟩ := hind a a.2 b b.2 c c.2 (by rw [mul_assoc]; exact h')
    rw [Subgroup.mem_bot]
    ext <;> simp [ha, hb, hc]
  have hcomm : ∀ x y : ↥A × (↥B × ↥C), x * y = y * x := by
    intro x y
    ext
    · exact congrArg Subtype.val (comm_of_card_three624 hA3 x.1 y.1)
    · exact congrArg Subtype.val (comm_of_card_three624 hB3 x.2.1 y.2.1)
    · exact congrArg Subtype.val (comm_of_card_three624 hC3 x.2.2 y.2.2)
  have hpow : ∀ x : ↥A × (↥B × ↥C), x ^ 3 = 1 := by
    intro x
    ext
    · exact congrArg Subtype.val (pow_three_of_card624 hA3 x.1)
    · exact congrArg Subtype.val (pow_three_of_card624 hB3 x.2.1)
    · exact congrArg Subtype.val (pow_three_of_card624 hC3 x.2.2)
  refine ⟨f.range, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x', hx'⟩ := x.2
    obtain ⟨y', hy'⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hx', ← hy', ← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, hpow, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, Nat.card_prod, hA3,
      hB3, hC3]
    norm_num

theorem exists_elemAbelian27_of_elements624 {X : Type*} [Group X] {x y z : X}
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hz : orderOf z = 3) (hxy : Commute x y)
    (hxz : Commute x z) (hyz : Commute y z)
    (hind : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, ∀ c ∈ Subgroup.zpowers z,
      a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  refine exists_elemAbelian27_of_commuting624 (by rw [Nat.card_zpowers, hx])
    (by rw [Nat.card_zpowers, hy]) (by rw [Nat.card_zpowers, hz]) ?_ ?_ ?_ hind
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hxy.zpow_zpow i j).eq
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hxz.zpow_zpow i j).eq
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hyz.zpow_zpow i j).eq

theorem mem_zpowers_of_ne_one624 {X : Type*} [Group X] {x c : X} (hx : orderOf x = 3)
    (hc : c ∈ Subgroup.zpowers x) (hc1 : c ≠ 1) : x ∈ Subgroup.zpowers c := by
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hle : Subgroup.zpowers c ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hc
  have : Finite (Subgroup.zpowers x) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hx]; norm_num)
  have heq : Subgroup.zpowers c = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hco])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem exists_orderOf_three_mem_centralizer624 {X : Type*} [Group X] [Finite X] {C Y : Subgroup X}
    (hYC : Y ≤ Subgroup.normalizer (C : Set X)) (hY : IsPGroup 3 Y) (h3 : 3 ∣ Nat.card C) :
    ∃ w ∈ C ⊓ Subgroup.centralizer (Y : Set X), orderOf w = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥Y →* MulAut ↥C := C.normalizerMonoidHom.comp (Subgroup.inclusion hYC)
  let _ : MulAction ↥Y ↥C := MulAction.compHom ↥C φ
  have hmod := IsPGroup.card_modEq_card_fixedPoints (α := ↥C) hY
  have hφ : ∀ (y : ↥Y) (c : ↥C), ((y • c : ↥C) : X) = y * c * (y : X)⁻¹ := fun _ _ => rfl
  have hF : Nat.card (MulAction.fixedPoints ↥Y ↥C) =
      Nat.card ↥(C ⊓ Subgroup.centralizer (Y : Set X)) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨(c.1 : X), c.1.2, Subgroup.mem_centralizer_iff.2 fun y hy => by
          have h1 := congrArg Subtype.val (c.2 ⟨y, hy⟩)
          rw [hφ] at h1
          calc y * (c.1 : X) = y * c.1 * y⁻¹ * y := by group
            _ = c.1 * y := by rw [h1]⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun y => by
          apply Subtype.ext
          rw [hφ]
          have h1 := Subgroup.mem_centralizer_iff.1 v.2.2 y y.2
          show (y : X) * v.1 * (y : X)⁻¹ = v.1
          rw [h1]
          group⟩
        left_inv := fun c => by ext; rfl
        right_inv := fun v => by ext; rfl }
  have h3F : 3 ∣ Nat.card ↥(C ⊓ Subgroup.centralizer (Y : Set X)) := by
    rw [← hF]
    exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h3)))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ Subgroup.centralizer (Y : Set X)))
    3 h3F
  exact ⟨w, w.2, by rw [Subgroup.orderOf_coe, hw]⟩

end CFSG.Quasithin.H13
