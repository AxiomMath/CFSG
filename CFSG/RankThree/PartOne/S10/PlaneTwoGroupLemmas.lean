module

import CFSG.RankThree.PartOne.S10.PlaneSemidirect
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG
open scoped commutatorElement Pointwise

namespace PlaneCommuting

variable {S : Type*} [Group S]

theorem exists_mul_of_mem_sup {X Y : Subgroup S} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : S}
    (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hXN : X ≤ Subgroup.normalizer (Y : Set S) := fun x hx =>
    PlaneSemidirect.mem_normalizer_of_commutes fun u hu => h x hx u hu
  have hg' : g ∈ (↑(X ⊔ Y) : Set S) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXN] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem commutatorElement_mul_mul {X Y : Subgroup S} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (a c : X) (b d : Y) :
    ⁅(a : S) * b, (c : S) * d⁆ = ⁅(a : S), (c : S)⁆ * ⁅(b : S), (d : S)⁆ := by
  let φ : X × Y →* S := X.subtype.noncommCoprod Y.subtype (fun x y => h x x.2 y y.2)
  have hφ : ∀ (x : X) (y : Y), φ (x, y) = (x : S) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have h1 := map_commutatorElement φ (a, b) (c, d)
  have e1 : (⁅((a, b) : X × Y), (c, d)⁆) = (⁅a, c⁆, ⁅b, d⁆) := by
    ext <;> simp [commutatorElement_def]
  rw [e1, hφ, hφ, hφ] at h1
  simpa [commutatorElement_def] using h1.symm

theorem card_sup_mul_card_inf [Finite S] {X Y : Subgroup S}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    Nat.card (X ⊔ Y : Subgroup S) * Nat.card (X ⊓ Y : Subgroup S) = Nat.card X * Nat.card Y := by
  let φ : X × Y →* S := X.subtype.noncommCoprod Y.subtype (fun x y => h x x.2 y y.2)
  have hφ : ∀ (x : X) (y : Y), φ (x, y) = (x : S) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hrange : φ.range = X ⊔ Y := by
    ext g
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      exact Subgroup.mul_mem_sup x.2 y.2
    · intro hg
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup h hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hφ _ _⟩
  have hker : Nat.card φ.ker = Nat.card (X ⊓ Y : Subgroup S) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : S), k.1.1.2, by
          have h1 : (k.1.1 : S) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          have h2 : (k.1.1 : S) = (k.1.2 : S)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [h2]
          exact Y.inv_mem k.1.2.2⟩
        invFun := fun g => ⟨(⟨g, g.2.1⟩, ⟨(g : S)⁻¹, Y.inv_mem g.2.2⟩), by
          rw [MonoidHom.mem_ker, hφ]
          exact mul_inv_cancel _⟩
        left_inv := fun k => by
          refine Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext ?_))
          have h1 : (k.1.1 : S) * k.1.2 = 1 := by
            have := k.2
            rwa [MonoidHom.mem_ker, hφ] at this
          exact inv_eq_of_mul_eq_one_right h1
        right_inv := fun g => Subtype.ext rfl }
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker, Nat.card_prod] at h
  rw [mul_comm]
  exact h


variable {P : Type*} [Group P] [Finite P]

theorem isExtraspecialPGroup_of_pairing (hP : IsPGroup 2 P) {Z : Subgroup P}
    (hZ : Nat.card Z = 2) (hZc : Z ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Z)
    (hsq : ∀ x : P, x ^ 2 ∈ Z) (hcent : ∀ x : P, (∀ y : P, x * y = y * x) → x ∈ Z)
    (hnab : ∃ x : P, x ∉ Z) : IsExtraspecialPGroup 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hcenter : Subgroup.center P = Z := by
    refine le_antisymm (fun x hx => hcent x fun y => ?_) hZc
    exact (Subgroup.mem_center_iff.mp hx y).symm
  have hcom_le : commutator P ≤ Z := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcomm x y
  have hcom : commutator P = Z := by
    refine le_antisymm hcom_le ?_
    obtain ⟨x, hx⟩ := hnab
    have hnc : ¬ ∀ y : P, x * y = y * x := fun h => hx (hcent x h)
    push Not at hnc
    obtain ⟨y, hy⟩ := hnc
    have hg1 : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hgZ : ⁅x, y⁆ ∈ Z := hcomm x y
    have hgc : ⁅x, y⁆ ∈ commutator P := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hzp : Subgroup.zpowers ⁅x, y⁆ = Z := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgZ) ?_
      rw [hZ, Nat.card_zpowers]
      have h2 : orderOf ⁅x, y⁆ ∣ 2 := by
        have := orderOf_dvd_natCard (⟨_, hgZ⟩ : Z)
        rwa [hZ, Subgroup.orderOf_mk] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h.ge
    rw [← hzp]
    exact (Subgroup.zpowers_le).mpr hgc
  have hfr : frattini P = Z := by
    refine le_antisymm ?_ (hcom ▸ commutator_le_frattini_of_isPGroup (R := P) (p := 2))
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (hx | ⟨y, rfl⟩)
    · exact hcom_le hx
    · exact hsq y
  refine ⟨hP, ?_, ?_, ?_⟩
  · rw [hcom, hcenter]
  · rw [hfr, hcenter]
  · rw [hcenter]
    exact hZ


variable {S : Type*} [Group S]

theorem isExtraspecialPGroup_sup [Finite S] {X Y Z : Subgroup S} (hS : IsPGroup 2 S)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hZ : Nat.card Z = 2) (hZX : Z ≤ X)
    (hXcomm : ⁅X, X⁆ = Z) (hYcomm : ⁅Y, Y⁆ = Z) (hXsq : ∀ x ∈ X, x ^ 2 ∈ Z)
    (hYsq : ∀ y ∈ Y, y ^ 2 ∈ Z) (hXcent : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z)
    (hXcl : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x ∈ Z)
    (hYcl : ∀ x ∈ Y, (∀ y ∈ Y, x * y = y * x) → x ∈ Z) (hXne : ∃ x ∈ X, x ∉ Z) :
    IsExtraspecialPGroup 2 ↥(X ⊔ Y) := by
  have hZP : Z ≤ X ⊔ Y := hZX.trans le_sup_left
  refine isExtraspecialPGroup_of_pairing (Z := Z.subgroupOf (X ⊔ Y)) (hS.to_subgroup _) ?_ ?_ ?_ ?_
    ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv]
    exact hZ
  · intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, ha, b, hb, hg⟩ := exists_mul_of_mem_sup hXY g.2
    have hz' : (z : S) ∈ Z := hz
    refine Subtype.ext ?_
    change (g : S) * z = z * g
    rw [hg]
    calc a * b * (z : S) = a * (b * z) := mul_assoc _ _ _
      _ = a * (z * b) := by rw [← hXY (z : S) (hZX hz') b hb]
      _ = a * z * b := (mul_assoc _ _ _).symm
      _ = z * a * b := by rw [← hXcent (z : S) hz' a ha]
      _ = z * (a * b) := mul_assoc _ _ _
  · intro x y
    obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup hXY x.2
    obtain ⟨c, hc, d, hd, hy⟩ := exists_mul_of_mem_sup hXY y.2
    rw [Subgroup.mem_subgroupOf]
    have e : ((⁅x, y⁆ : ↥(X ⊔ Y)) : S) = ⁅a, c⁆ * ⁅b, d⁆ := by
      have h1 := commutatorElement_mul_mul hXY ⟨a, ha⟩ ⟨c, hc⟩ ⟨b, hb⟩ ⟨d, hd⟩
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
      rw [hx, hy]
      exact h1
    rw [e]
    exact Z.mul_mem (hXcomm ▸ Subgroup.commutator_mem_commutator ha hc)
      (hYcomm ▸ Subgroup.commutator_mem_commutator hb hd)
  · intro x
    obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup hXY x.2
    rw [Subgroup.mem_subgroupOf]
    change (x : S) ^ 2 ∈ Z
    rw [hx, (show Commute a b from hXY a ha b hb).mul_pow]
    exact Z.mul_mem (hXsq a ha) (hYsq b hb)
  · intro x hx
    obtain ⟨a, ha, b, hb, hxab⟩ := exists_mul_of_mem_sup hXY x.2
    rw [Subgroup.mem_subgroupOf]
    have haZ : a ∈ Z := by
      refine hXcl a ha fun y hy => ?_
      have h1 := congrArg Subtype.val (hx ⟨y, Subgroup.mem_sup_left hy⟩)
      change (x : S) * y = y * x at h1
      rw [hxab] at h1
      have h2 : a * y * b = y * a * b := by
        calc a * y * b = a * (y * b) := mul_assoc _ _ _
          _ = a * (b * y) := by rw [hXY y hy b hb]
          _ = a * b * y := (mul_assoc _ _ _).symm
          _ = y * (a * b) := h1
          _ = y * a * b := (mul_assoc _ _ _).symm
      exact mul_right_cancel h2
    have hbZ : b ∈ Z := by
      refine hYcl b hb fun w hw => ?_
      have h1 := congrArg Subtype.val (hx ⟨w, Subgroup.mem_sup_right hw⟩)
      change (x : S) * w = w * x at h1
      rw [hxab] at h1
      have h2 : a * (b * w) = a * (w * b) := by
        calc a * (b * w) = a * b * w := (mul_assoc _ _ _).symm
          _ = w * (a * b) := h1
          _ = (w * a) * b := (mul_assoc _ _ _).symm
          _ = (a * w) * b := by rw [← hXY a ha w hw]
          _ = a * (w * b) := mul_assoc _ _ _
      exact mul_left_cancel h2
    change (x : S) ∈ Z
    rw [hxab]
    exact Z.mul_mem haZ hbZ
  · obtain ⟨x, hx, hxZ⟩ := hXne
    refine ⟨⟨x, Subgroup.mem_sup_left hx⟩, fun h => hxZ ?_⟩
    exact Subgroup.mem_subgroupOf.mp h

end PlaneCommuting

end CFSG.RankThree.PartOne
