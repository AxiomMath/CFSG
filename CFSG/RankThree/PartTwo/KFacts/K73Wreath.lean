module

public import CFSG.RankThree.PartTwo.Sec11.WreathFacts

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

abbrev M3 : Type := Multiplicative (ZMod 3)

@[expose] def wreathAb : W33 →* M3 × M3 where
  toFun y := (∏ x, y.left x, y.right)
  map_one' := by
    ext
    · exact (by decide : (∏ x : M3, (1 : W33).left x) = 1)
    · rfl
  map_mul' y z := by
    ext
    · simp only [RegularWreathProduct.mul_left, Pi.mul_apply, Finset.prod_mul_distrib,
        Prod.fst_mul]
      exact congrArg ((∏ x, y.left x) * ·) (Fintype.prod_equiv (Equiv.mulLeft y.right⁻¹)
        (fun x => z.left (y.right⁻¹ * x)) z.left (fun x => rfl))
    · rfl

theorem mem_ker_wreathAb {y : W33} :
    y ∈ wreathAb.ker ↔ y.right = 1 ∧ ∏ x, y.left x = 1 := by
  rw [MonoidHom.mem_ker, Prod.ext_iff]
  exact and_comm

theorem exists_commutator_eq :
    ∀ f : M3 → M3, (∏ x, f x) = 1 → ∃ g : M3 → M3,
      (⁅(⟨g, 1⟩ : W33), (⟨1, wreathT⟩ : W33)⁆).left = f ∧
        (⁅(⟨g, 1⟩ : W33), (⟨1, wreathT⟩ : W33)⁆).right = 1 := by
  decide

theorem commutator_eq_ker_wreathAb : ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ = wreathAb.ker := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro y _ z _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · intro y hy
    rw [mem_ker_wreathAb] at hy
    obtain ⟨g, hg1, hg2⟩ := exists_commutator_eq y.left hy.2
    have e : y = ⁅(⟨g, 1⟩ : W33), (⟨1, wreathT⟩ : W33)⁆ :=
      RegularWreathProduct.ext hg1.symm (hy.1.trans hg2.symm)
    rw [e]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem card_prod_eq_one : Fintype.card {f : M3 → M3 // (∏ x, f x) = 1} = 9 := by
  decide

theorem card_commutator_wreath :
    Nat.card (⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ : Subgroup W33) = 9 := by
  rw [commutator_eq_ker_wreathAb, ← card_prod_eq_one, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun y => ⟨(y : W33).left, (mem_ker_wreathAb.mp y.2).2⟩
      invFun := fun f => ⟨⟨f.1, 1⟩, mem_ker_wreathAb.mpr ⟨rfl, f.2⟩⟩
      left_inv := fun y => Subtype.ext (RegularWreathProduct.ext rfl
        (mem_ker_wreathAb.mp y.2).1.symm)
      right_inv := fun f => rfl }

theorem commutator_const :
    ∀ f : M3 → M3, (∏ x, f x) = 1 → ∀ (f' : M3 → M3) (q' : M3),
      (⁅(⟨f, 1⟩ : W33), (⟨f', q'⟩ : W33)⁆).right = 1 ∧
        ∀ x, (⁅(⟨f, 1⟩ : W33), (⟨f', q'⟩ : W33)⁆).left x =
          (⁅(⟨f, 1⟩ : W33), (⟨f', q'⟩ : W33)⁆).left 1 := by
  decide

theorem const_eq :
    ∀ f : M3 → M3, (∀ x, f x = f 1) →
      f = (1 : W33).left ∨ f = wreathZ.left ∨ f = wreathZ⁻¹.left := by
  decide

theorem mem_center_of_const {y : W33} (hy : y.right = 1) (hc : ∀ x, y.left x = y.left 1) :
    y ∈ Subgroup.center W33 := by
  rw [center_eq_zpowers_wreathZ]
  rcases const_eq y.left hc with h | h | h
  · have e : y = 1 := RegularWreathProduct.ext h hy
    rw [e]
    exact Subgroup.one_mem _
  · have e : y = wreathZ := RegularWreathProduct.ext h (hy.trans wreathZ_right.symm)
    rw [e]
    exact Subgroup.mem_zpowers _
  · have e : y = wreathZ⁻¹ := RegularWreathProduct.ext h (hy.trans wreathZ_inv_right.symm)
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem prod_id : (∏ x : M3, x) = 1 := by decide

theorem commutator_commutator_wreath :
    ⁅⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆, (⊤ : Subgroup W33)⁆ = Subgroup.center W33 := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro y hy z _
    rw [commutator_eq_ker_wreathAb, mem_ker_wreathAb] at hy
    obtain ⟨f, q⟩ := y
    change q = 1 ∧ _ at hy
    obtain ⟨rfl, hf⟩ := hy
    obtain ⟨h1, h2⟩ := commutator_const f hf z.left z.right
    exact mem_center_of_const h1 h2
  · rw [center_eq_zpowers_wreathZ, Subgroup.zpowers_le]
    have hid : (⟨fun x => x, 1⟩ : W33) ∈ ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ := by
      rw [commutator_eq_ker_wreathAb, mem_ker_wreathAb]
      exact ⟨rfl, prod_id⟩
    exact Subgroup.commutator_mem_commutator hid (Subgroup.mem_top _)

@[expose] def wreathBase : Subgroup W33 := RegularWreathProduct.rightHom.ker

theorem mem_wreathBase {y : W33} : y ∈ wreathBase ↔ y.right = 1 := MonoidHom.mem_ker

theorem not_const_shift :
    ∀ f : M3 → M3, (∏ x, f x) ≠ 1 → ∀ c : M3, ¬ ∀ x, f (wreathT⁻¹ * x) * (f x)⁻¹ = c := by
  decide

theorem commutator_top_left :
    ∀ f : M3 → M3, (⁅(⟨1, wreathT⟩ : W33), (⟨f, 1⟩ : W33)⁆).left =
      (fun x => f (wreathT⁻¹ * x) * (f x)⁻¹) ∧
        (⁅(⟨1, wreathT⟩ : W33), (⟨f, 1⟩ : W33)⁆).right = 1 := by
  decide

theorem eq_commutator_of_normal_of_card_nine {N : Subgroup W33} (hN : N.Normal)
    (h9 : Nat.card N = 9) : N = ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := N) (by
      rw [h9]; norm_num)).is_comm.comm
    intro x hx y hy
    exact congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩)
  have hNB : ∀ y ∈ N, y.right = 1 := right_eq_one_of_abelian_normal hN hcomm
  have hW3 : IsPGroup 3 W33 := IsPGroup.of_card (n := 4) (by rw [card_wreath]; norm_num)
  have : Group.IsNilpotent W33 := hW3.isNilpotent
  have hZ3 : Nat.card (Subgroup.center W33) = 3 := by
    rw [center_eq_zpowers_wreathZ, Nat.card_zpowers,
      orderOf_eq_prime (pow_three_eq_one_of_right_eq_one wreathZ_right) wreathZ_ne_one]
  have hZN : Subgroup.center W33 ≤ N := by
    have hne : N ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at h9
      exact absurd h9 (by norm_num)
    have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    have hdvd : Nat.card (N ⊓ Subgroup.center W33 : Subgroup W33) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_right : N ⊓ Subgroup.center W33 ≤ Subgroup.center W33)
      rwa [hZ3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) h1
    · have := Subgroup.eq_of_le_of_card_ge (inf_le_right : N ⊓ Subgroup.center W33 ≤ _)
        (by rw [h, hZ3])
      rw [← this]
      exact inf_le_left
  have hle : N ≤ ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ := by
    intro y hy
    by_contra hyK
    have hprod : ∏ x, y.left x ≠ 1 := by
      intro h
      apply hyK
      rw [commutator_eq_ker_wreathAb, mem_ker_wreathAb]
      exact ⟨hNB y hy, h⟩
    set k : W33 := ⁅(⟨1, wreathT⟩ : W33), y⁆ with hk
    have hkN : k ∈ N := by
      rw [hk, commutatorElement_def]
      exact N.mul_mem (hN.conj_mem y hy _) (N.inv_mem hy)
    have hkK : k ∈ ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hkZ : k ∉ Subgroup.center W33 := by
      intro hkc
      obtain ⟨-, hconst⟩ := eq_const_of_mem_center hkc
      have hyq : y.right = 1 := hNB y hy
      obtain ⟨f, q⟩ := y
      change q = 1 at hyq
      subst hyq
      obtain ⟨hl, -⟩ := commutator_top_left f
      apply not_const_shift f hprod (k.left 1)
      intro x
      have := hconst x
      rw [hk, hl] at this ⊢
      exact this
    set H := Subgroup.center W33 ⊔ Subgroup.zpowers k with hH
    have hHN : H ≤ N ⊓ ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ := by
      refine sup_le (le_inf hZN ?_) (Subgroup.zpowers_le.mpr ⟨hkN, hkK⟩)
      rw [← commutator_commutator_wreath]
      exact Subgroup.commutator_le_left _ _
    have hZH : Subgroup.center W33 ≤ H := le_sup_left
    have hkH : k ∈ H := le_sup_right (a := Subgroup.center W33) (Subgroup.mem_zpowers k)
    have hH9 : 9 ≤ Nat.card H := by
      have hdvd : Nat.card H ∣ 3 ^ 4 := by
        rw [← card_wreath.trans (by norm_num : 81 = 3 ^ 4)]
        exact Subgroup.card_subgroup_dvd_card H
      obtain ⟨m, hm, hHm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      have h3 : 3 ≤ Nat.card H := by
        have h := Subgroup.card_le_of_le hZH
        rwa [hZ3] at h
      have hne3 : Nat.card H ≠ 3 := by
        intro h
        have := Subgroup.eq_of_le_of_card_ge hZH (by rw [h, hZ3])
        rw [← this] at hkH
        exact hkZ hkH
      rw [hHm] at h3 hne3 ⊢
      rcases m with _ | _ | m
      · norm_num at h3
      · norm_num at hne3
      · calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hNK : N ⊓ ⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ = N :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [h9]
        exact hH9.trans (Subgroup.card_le_of_le hHN))
    exact hyK (Subgroup.mem_inf.mp (hNK.symm ▸ hy)).2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h9, card_commutator_wreath])

theorem const_of_commute :
    ∀ (f f' : M3 → M3) (q' : M3), q' ≠ 1 →
      ((⟨f, 1⟩ : W33) * ⟨f', q'⟩).left = ((⟨f', q'⟩ : W33) * ⟨f, 1⟩).left → ∀ x, f x = f 1 := by
  decide

theorem inf_centralizer_eq_center {y : W33} (hy : y.right ≠ 1) :
    wreathBase ⊓ Subgroup.centralizer {y} = Subgroup.center W33 := by
  apply le_antisymm
  · intro b hb
    obtain ⟨hbB, hbc⟩ := Subgroup.mem_inf.mp hb
    rw [mem_wreathBase] at hbB
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hbc
    obtain ⟨f, q⟩ := b
    change q = 1 at hbB
    subst hbB
    exact mem_center_of_const rfl
      (const_of_commute f y.left y.right hy (congrArg RegularWreathProduct.left hc))
  · intro z hz
    refine Subgroup.mem_inf.mpr ⟨mem_wreathBase.mpr (eq_const_of_mem_center hz).1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_center_iff.mp hz) y).symm

end CFSG.RankThree.PartTwo.KFacts
