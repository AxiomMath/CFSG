module

public import CFSG.Quasithin.H13.L32NQ8Pow
public import CFSG.Quasithin.Recognition.HSTypeDefs

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

namespace Q8Pow

variable {G : Type*} [Group G]

namespace CommPair

variable {z : G} {U : Subgroup G} (S : CommPair z U)
include S

theorem exists_sq_eq {c : G} (hcU : c ∈ U) (hcc : c * c = z) (hcZ : ∀ u ∈ U, c * u = u * c)
    {x : G} (hx : x ∈ U) : ∃ x' ∈ U, x' * x' = z ∧ (x' = x ∨ x' = x * c) := by
  rcases S.sq x hx with h1 | h1
  · refine ⟨x * c, U.mul_mem hx hcU, ?_, Or.inr rfl⟩
    calc x * c * (x * c) = x * (c * x) * c := by group
      _ = x * (x * c) * c := by rw [hcZ x hx]
      _ = (x * x) * (c * c) := by group
      _ = z := by rw [h1, hcc, one_mul]
  · exact ⟨x, hx, h1, Or.inl rfl⟩

theorem comm_mul_central {c x w : G} (hcU : c ∈ U) (hcZ : ∀ u ∈ U, c * u = u * c)
    (hx : x ∈ U) (hw : w ∈ U) : ⁅x * c, w⁆ = ⁅x, w⁆ := by
  rw [S.comm_mul_left hx hcU hw, commutatorElement_eq_one_iff_mul_comm.mpr (hcZ w hw), mul_one]

theorem comm_mul_central_right {c x w : G} (hcU : c ∈ U) (hcZ : ∀ u ∈ U, c * u = u * c)
    (hx : x ∈ U) (hw : w ∈ U) : ⁅w, x * c⁆ = ⁅w, x⁆ := by
  rw [S.comm_mul_right hw hx hcU, commutatorElement_eq_one_iff_mul_comm.mpr (hcZ w hw).symm,
    mul_one]

theorem exists_q8_pair {c : G} (hcU : c ∈ U) (hcc : c * c = z) (hcZ : ∀ u ∈ U, c * u = u * c)
    {x : G} (hx : x ∈ U) (hnc : ¬ ∀ w ∈ U, x * w = w * x) :
    ∃ x' ∈ U, ∃ y' ∈ U, x' * x' = z ∧ y' * y' = z ∧ ⁅x', y'⁆ = z := by
  push Not at hnc
  obtain ⟨y, hy, hxy⟩ := hnc
  have hz : ⁅x, y⁆ = z := (S.comm x hx y hy).resolve_left fun h =>
    hxy (commutatorElement_eq_one_iff_mul_comm.mp h)
  obtain ⟨x', hx'U, hx'x', hx'⟩ := S.exists_sq_eq hcU hcc hcZ hx
  obtain ⟨y', hy'U, hy'y', hy'⟩ := S.exists_sq_eq hcU hcc hcZ hy
  refine ⟨x', hx'U, y', hy'U, hx'x', hy'y', ?_⟩
  have h1 : ⁅x', y⁆ = z := by
    rcases hx' with rfl | rfl
    · exact hz
    · rw [S.comm_mul_central hcU hcZ hx hy]; exact hz
  rcases hy' with rfl | rfl
  · exact h1
  · rw [S.comm_mul_central_right hcU hcZ hy hx'U]; exact h1

end CommPair

abbrev Z4Q8Q8Pre : Type := Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2

@[expose] def zmodFourHom {c : G} (hc4 : c ^ 4 = 1) : Multiplicative (ZMod 4) →* G where
  toFun k := c ^ (Multiplicative.toAdd k).val
  map_one' := by
    show c ^ (0 : ZMod 4).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' k k' := by
    show c ^ (Multiplicative.toAdd k + Multiplicative.toAdd k').val =
      c ^ (Multiplicative.toAdd k).val * c ^ (Multiplicative.toAdd k').val
    rw [pow_val_eq hc4 _ ((Multiplicative.toAdd k).val + (Multiplicative.toAdd k').val : ℤ)
      (by push_cast [ZMod.natCast_zmod_val]; rfl), zpow_add, zpow_natCast, zpow_natCast]

theorem nonempty_mulEquiv_z4Q8Q8 [Finite G] {U : Subgroup G} {z c : G} (S : CommPair z U)
    (hcU : c ∈ U) (hcc : c * c = z) (hcZ : ∀ u ∈ U, c * u = u * c)
    (hcen : ∀ u ∈ U, (∀ w ∈ U, u * w = w * u) → u ∈ Subgroup.zpowers c)
    (hcard : Nat.card U = 64) : HSType.IsZ4Q8Q8 ↥U := by
  have hzz := S.z_sq
  have hc4 : c ^ 4 = 1 := by
    calc c ^ 4 = (c * c) * (c * c) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hcc, hzz]
  have hord : orderOf c = 4 := by
    have hdvd : orderOf c ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hc4
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hk'
      apply S.z_ne
      rw [← hcc, hk', one_mul]
    · exfalso
      rw [pow_one] at hk'
      apply S.z_ne
      rw [← hcc, ← pow_two, ← hk', pow_orderOf_eq_one]
    · rw [hk']; norm_num
  have hcard4 : Nat.card (Subgroup.zpowers c) = 4 := by rw [Nat.card_zpowers, hord]
  have hout : ∀ (B : Subgroup G), 4 < Nat.card B → ∃ x ∈ B, x ∉ Subgroup.zpowers c := by
    intro B hB
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers c from hne)
    omega
  obtain ⟨x₀, hx₀U, hx₀c⟩ := hout U (by omega)
  obtain ⟨x₁, hx₁U, y₁, hy₁U, hx₁x₁, hy₁y₁, hxy₁⟩ := S.exists_q8_pair hcU hcc hcZ hx₀U
    (fun h => hx₀c (hcen x₀ hx₀U h))
  obtain ⟨φ₁, hφ₁inj, hφ₁r, hφ₁a, hφ₁x, hφ₁z⟩ := exists_quatHom hx₁x₁ hy₁y₁ S.z_ne hzz hxy₁
  have hcard₁ := S.card_peel hx₁U hy₁U hxy₁
  set C₁ := U ⊓ Subgroup.centralizer {x₁} ⊓ Subgroup.centralizer {y₁} with hC₁
  have hcC₁ : c ∈ C₁ := Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcU,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcZ x₁ hx₁U)⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcZ y₁ hy₁U)⟩
  have hC₁U : C₁ ≤ U := inf_le_left.trans inf_le_left
  have S₁ : CommPair z C₁ := S.mono hC₁U (by
    rw [← hcc]; exact C₁.mul_mem hcC₁ hcC₁)
  have hcZ₁ : ∀ u ∈ C₁, c * u = u * c := fun u hu => hcZ u (hC₁U hu)
  have hcen₁ : ∀ u ∈ C₁, (∀ w ∈ C₁, u * w = w * u) → u ∈ Subgroup.zpowers c := by
    intro u hu h
    obtain ⟨hu1, huy⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨huU, hux⟩ := Subgroup.mem_inf.mp hu1
    refine hcen u huU fun w hw => ?_
    obtain ⟨e, he, hwe⟩ := S.decomp hx₁U hy₁U hxy₁ hw
    have hce : Commute u e := h e he
    have hcx : Commute u x₁ := Subgroup.mem_centralizer_singleton_iff.mp hux
    have hcy : Commute u y₁ := Subgroup.mem_centralizer_singleton_iff.mp huy
    rcases hwe with rfl | rfl | rfl | rfl
    · exact hce
    · exact hce.mul_right hcx.inv_right
    · exact hce.mul_right hcy.inv_right
    · exact (hce.mul_right hcy.inv_right).mul_right hcx.inv_right
  obtain ⟨x₂', hx₂'C, hx₂'c⟩ := hout C₁ (by omega)
  obtain ⟨x₂, hx₂C, y₂, hy₂C, hx₂x₂, hy₂y₂, hxy₂⟩ := S₁.exists_q8_pair hcC₁ hcc hcZ₁ hx₂'C
    (fun h => hx₂'c (hcen₁ x₂' hx₂'C h))
  obtain ⟨φ₂, hφ₂inj, hφ₂r, hφ₂a, hφ₂x, hφ₂z⟩ := exists_quatHom hx₂x₂ hy₂y₂ S.z_ne hzz hxy₂
  have hcard₂ := S₁.card_peel hx₂C hy₂C hxy₂
  set C₂ := C₁ ⊓ Subgroup.centralizer {x₂} ⊓ Subgroup.centralizer {y₂} with hC₂
  have hC₂c : C₂ = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ?_) ?_).symm
    · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcC₁,
        Subgroup.mem_centralizer_singleton_iff.mpr (hcZ₁ x₂ hx₂C)⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (hcZ₁ y₂ hy₂C)⟩
    · have hle : Subgroup.zpowers c ≤ C₂ := Subgroup.zpowers_le.mpr
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcC₁,
          Subgroup.mem_centralizer_singleton_iff.mpr (hcZ₁ x₂ hx₂C)⟩,
          Subgroup.mem_centralizer_singleton_iff.mpr (hcZ₁ y₂ hy₂C)⟩)
      omega
  have hφ₁U : ∀ q, φ₁ q ∈ U := fun q => by
    have : φ₁ q ∈ φ₁.range := ⟨q, rfl⟩
    rw [hφ₁r] at this
    exact (Subgroup.closure_le U).mpr (by
      rintro _ (rfl | rfl)
      · exact hx₁U
      · exact hy₁U) this
  have hφ₂C : ∀ q, φ₂ q ∈ C₁ := fun q => by
    have : φ₂ q ∈ φ₂.range := ⟨q, rfl⟩
    rw [hφ₂r] at this
    exact (Subgroup.closure_le C₁).mpr (by
      rintro _ (rfl | rfl)
      · exact hx₂C
      · exact hy₂C) this
  have h12 : ∀ q₁ q₂, Commute (φ₁ q₁) (φ₂ q₂) := by
    intro q₁ q₂
    have hle : φ₁.range ≤ Subgroup.centralizer (φ₂.range : Set G) := by
      rw [hφ₁r, hφ₂r]
      refine closure_le_centralizer_closure ?_
      rintro s (rfl | rfl) t ht
      · have htC := (Subgroup.closure_le C₁).mpr (by
          rintro _ (rfl | rfl)
          · exact hx₂C
          · exact hy₂C) (Subgroup.subset_closure ht)
        exact (Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htC).1).2).symm
      · have htC := (Subgroup.closure_le C₁).mpr (by
          rintro _ (rfl | rfl)
          · exact hx₂C
          · exact hy₂C) (Subgroup.subset_closure ht)
        exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp htC).2).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle ⟨q₁, rfl⟩) _ ⟨q₂, rfl⟩).symm
  set ψc := zmodFourHom hc4 with hψc
  have hψcU : ∀ k, ψc k ∈ U := fun k => U.pow_mem hcU _
  have hc12 : ∀ k (q : QuaternionGroup 2 × QuaternionGroup 2),
      Commute (ψc k) ((φ₁.noncommCoprod φ₂ h12) q) := by
    intro k q
    rw [MonoidHom.noncommCoprod_apply]
    exact (Commute.pow_left (hcZ _ (hφ₁U q.1)) _).mul_right
      (Commute.pow_left (hcZ _ (hC₁U (hφ₂C q.2))) _)
  set F := ψc.noncommCoprod (φ₁.noncommCoprod φ₂ h12) hc12 with hF
  have hFU : ∀ p, F p ∈ U := by
    intro p
    rw [hF, MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply]
    exact U.mul_mem (hψcU _) (U.mul_mem (hφ₁U _) (hC₁U (hφ₂C _)))
  set F' := F.codRestrict U hFU with hF'
  have hrange : ∀ u ∈ U, u ∈ F.range := by
    have hφ₁R : ∀ q, φ₁ q ∈ F.range := fun q => ⟨(1, q, 1), by
      show ψc 1 * (φ₁ q * φ₂ 1) = φ₁ q
      rw [map_one ψc, map_one φ₂, one_mul, mul_one]⟩
    have hφ₂R : ∀ q, φ₂ q ∈ F.range := fun q => ⟨(1, 1, q), by
      show ψc 1 * (φ₁ 1 * φ₂ q) = φ₂ q
      rw [map_one ψc, map_one φ₁, one_mul, one_mul]⟩
    have hcR : c ∈ F.range := ⟨(Multiplicative.ofAdd 1, 1, 1), by
      show ψc (Multiplicative.ofAdd 1) * (φ₁ 1 * φ₂ 1) = c
      rw [map_one φ₁, map_one φ₂, mul_one, mul_one]
      show c ^ (1 : ZMod 4).val = c
      rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]⟩
    have hx₁R : x₁ ∈ F.range := hφ₁a ▸ hφ₁R _
    have hy₁R : y₁ ∈ F.range := hφ₁x ▸ hφ₁R _
    have hx₂R : x₂ ∈ F.range := hφ₂a ▸ hφ₂R _
    have hy₂R : y₂ ∈ F.range := hφ₂x ▸ hφ₂R _
    intro u hu
    obtain ⟨e₁, he₁, hue⟩ := S.decomp hx₁U hy₁U hxy₁ hu
    obtain ⟨e₂, he₂, hee⟩ := S₁.decomp hx₂C hy₂C hxy₂ he₁
    have he₂R : e₂ ∈ F.range := (Subgroup.zpowers_le.mpr hcR) (hC₂c ▸ he₂)
    have he₁R : e₁ ∈ F.range := by
      rcases hee with rfl | rfl | rfl | rfl
      · exact he₂R
      · exact F.range.mul_mem he₂R (F.range.inv_mem hx₂R)
      · exact F.range.mul_mem he₂R (F.range.inv_mem hy₂R)
      · exact F.range.mul_mem (F.range.mul_mem he₂R (F.range.inv_mem hy₂R))
          (F.range.inv_mem hx₂R)
    rcases hue with rfl | rfl | rfl | rfl
    · exact he₁R
    · exact F.range.mul_mem he₁R (F.range.inv_mem hx₁R)
    · exact F.range.mul_mem he₁R (F.range.inv_mem hy₁R)
    · exact F.range.mul_mem (F.range.mul_mem he₁R (F.range.inv_mem hy₁R))
        (F.range.inv_mem hx₁R)
  have hsurj : Function.Surjective F' := by
    rintro ⟨u, hu⟩
    obtain ⟨p, hp⟩ := hrange u hu
    exact ⟨p, Subtype.ext hp⟩
  have hIdle : HSType.z4Q8Q8Ident ≤ F'.ker := by
    rw [HSType.z4Q8Q8Ident, Subgroup.closure_le]
    have hc2 : ψc (Multiplicative.ofAdd 2) = z := by
      show c ^ (2 : ZMod 4).val = z
      rw [show (2 : ZMod 4).val = 2 from rfl, pow_two, hcc]
    rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, MonoidHom.mem_ker] <;> refine Subtype.ext ?_ <;>
      show F _ = 1 <;>
      rw [hF, MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply, hc2]
    · show z * (φ₁ (QuaternionGroup.a 2) * φ₂ 1) = 1
      rw [hφ₁z, map_one, mul_one, hzz]
    · show z * (φ₁ 1 * φ₂ (QuaternionGroup.a 2)) = 1
      rw [hφ₂z, map_one, one_mul, hzz]
  have hdom : Nat.card (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) = 256 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2),
      QuaternionGroup.card, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 4))]
    rfl
  have hker4 : Nat.card F'.ker = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup F'.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F' hsurj).toEquiv, hcard,
      hdom] at h1
    omega
  have hId4 : 4 ≤ Nat.card ↥HSType.z4Q8Q8Ident := by
    set g₁ : Z4Q8Q8Pre :=
      (Multiplicative.ofAdd 2, QuaternionGroup.a 2, 1) with hg₁
    set g₂ : Z4Q8Q8Pre :=
      (Multiplicative.ofAdd 2, 1, QuaternionGroup.a 2) with hg₂
    have hg₁m : g₁ ∈ HSType.z4Q8Q8Ident := Subgroup.subset_closure (Set.mem_insert _ _)
    have hg₂m : g₂ ∈ HSType.z4Q8Q8Ident :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hsub : (({1, g₁, g₂, g₁ * g₂} : Finset Z4Q8Q8Pre) : Set Z4Q8Q8Pre) ⊆
        (HSType.z4Q8Q8Ident : Set Z4Q8Q8Pre) := by
      intro w hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hg₁m
      · exact hg₂m
      · exact Subgroup.mul_mem _ hg₁m hg₂m
    have hc : ({1, g₁, g₂, g₁ * g₂} : Finset Z4Q8Q8Pre).card = 4 := by
      rw [hg₁, hg₂]; decide
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hc] at h1
    calc 4 ≤ (HSType.z4Q8Q8Ident : Set Z4Q8Q8Pre).ncard := h1
      _ = Nat.card ↥HSType.z4Q8Q8Ident := Nat.card_coe_set_eq _ |>.symm
  have hkerEq : F'.ker = HSType.z4Q8Q8Ident :=
    (Subgroup.eq_of_le_of_card_ge hIdle (by omega)).symm
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective F' hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkerEq)⟩

end Q8Pow

end CFSG.Quasithin.H13
