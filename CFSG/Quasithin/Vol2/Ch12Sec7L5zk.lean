module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zb
public import CFSG.Quasithin.Vol2.Ch12Sec7L5ze

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ElemAb

theorem exists_mulAut_apply_eq {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {w₁ w₂ : W} (h₁ : w₁ ≠ 1) (h₂ : w₂ ≠ 1) : ∃ φ : MulAut W, φ w₁ = w₂ := by
  classical
  by_cases h12 : w₁ = w₂
  · exact ⟨1, by rw [MulAut.one_apply, h12]⟩
  have hc2 : (w₁ * w₂) ^ 2 = 1 := hW _
  obtain ⟨C, hCE, hCEt⟩ := Lift3.exists_compl hW (Subgroup.closure {w₁, w₂})
  set H := C ⊔ Subgroup.zpowers (w₁ * w₂) with hH
  have hcH : w₁ * w₂ ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hcE : w₁ * w₂ ∈ Subgroup.closure {w₁, w₂} :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hw₁H : w₁ ∉ H := by
    intro hw
    obtain ⟨a, ha, y, hy, hay⟩ := Subgroup.mem_sup.mp hw
    have hyE : y ∈ Subgroup.closure {w₁, w₂} :=
      Subgroup.zpowers_le_of_mem hcE hy
    have haE : a ∈ Subgroup.closure {w₁, w₂} := by
      have e : a = w₁ * y⁻¹ := by rw [← hay, mul_inv_cancel_right]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.inv_mem _ hyE)
    have ha1 : a = 1 := by
      have : a ∈ C ⊓ Subgroup.closure {w₁, w₂} := ⟨ha, haE⟩
      rwa [hCE, Subgroup.mem_bot] at this
    rw [ha1, one_mul] at hay
    rcases Lift3.mem_zpowers_two hc2 hy with h | h
    · exact h₁ (hay ▸ h)
    · apply h₂
      have : w₁ = w₁ * w₂ := hay ▸ h
      calc w₂ = w₁⁻¹ * (w₁ * w₂) := by rw [inv_mul_cancel_left]
        _ = 1 := by rw [← this, inv_mul_cancel]
  have hdich : ∀ x, x ∈ H ∨ w₁ * x ∈ H := by
    intro x
    have hx : x ∈ C ⊔ Subgroup.closure {w₁, w₂} := hCEt ▸ Subgroup.mem_top x
    obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨m, n, rfl⟩ := Subgroup.mem_closure_pair.mp he
    have haH : a ∈ H := Subgroup.mem_sup_left ha
    rcases Lift3.mem_zpowers_two (hW w₁) (Subgroup.zpow_mem_zpowers w₁ m) with h1 | h1 <;>
      rcases Lift3.mem_zpowers_two (hW w₂) (Subgroup.zpow_mem_zpowers w₂ n) with h2 | h2 <;>
      rw [h1, h2]
    · left
      simpa using haH
    · right
      rw [one_mul, mul_left_comm]
      exact H.mul_mem haH hcH
    · right
      rw [mul_one, mul_left_comm, ← pow_two, hW, mul_one]
      exact haH
    · left
      exact H.mul_mem haH hcH
  have hHmul : ∀ x y, x ∈ H → y ∉ H → x * y ∉ H := fun x y hx hy hxy =>
    hy (by have := H.mul_mem (H.inv_mem hx) hxy; rwa [inv_mul_cancel_left] at this)
  have hnn : ∀ x y, x ∉ H → y ∉ H → x * y ∈ H := by
    intro x y hx hy
    have := H.mul_mem ((hdich x).resolve_left hx) ((hdich y).resolve_left hy)
    rwa [mul_mul_mul_comm, ← pow_two, hW, one_mul] at this
  set f : W → W := fun x => if x ∈ H then x else w₁ * w₂ * x with hf
  have hff : ∀ x, f (f x) = x := by
    intro x
    by_cases hx : x ∈ H
    · simp only [hf, hx, ↓reduceIte]
    · have hcx : w₁ * w₂ * x ∉ H := hHmul _ _ hcH hx
      simp only [hf, hx, hcx, ↓reduceIte]
      rw [← mul_assoc, ← pow_two, hc2, one_mul]
  have hfmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x ∈ H <;> by_cases hy : y ∈ H
    · simp only [hf, hx, hy, H.mul_mem hx hy, ↓reduceIte]
    · simp only [hf, hx, hy, hHmul x y hx hy, ↓reduceIte]
      rw [mul_left_comm]
    · have hxy : x * y ∉ H := by rw [mul_comm]; exact hHmul y x hy hx
      simp only [hf, hx, hy, hxy, ↓reduceIte]
      simp only [mul_assoc]
    · simp only [hf, hx, hy, hnn x y hx hy, ↓reduceIte]
      rw [mul_mul_mul_comm, ← pow_two, hc2, one_mul]
  refine ⟨{ toFun := f, invFun := f, left_inv := hff, right_inv := hff, map_mul' := hfmul }, ?_⟩
  show f w₁ = w₂
  simp only [hf, hw₁H, ↓reduceIte]
  rw [mul_comm w₁ w₂, mul_assoc, ← pow_two, hW, mul_one]

theorem sq_eq_one_of_sq_eq {U W : Type*} [Group U] [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (π : U →* W) (hπ : Function.Surjective π) {z : U}
    (hz : ∀ u, π u = 1 ↔ u = 1 ∨ u = z) (hzc : ∀ u, z * u = u * z) (hz2 : z ^ 2 = 1)
    (hsq : ∀ u v, π u ≠ 1 → π v ≠ 1 → u ^ 2 = v ^ 2) (h8 : 8 ≤ Nat.card W) :
    ∀ u : U, u ^ 2 = 1 := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hsq1 : ∀ u : U, u ^ 2 = 1 ∨ u ^ 2 = z := fun u =>
    (hz _).mp (by rw [map_pow, hW])
  have hcomm1 : ∀ u v : U, u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = z := fun u v =>
    (hz _).mp (by
      simp only [map_mul, map_inv]
      rw [mul_comm (π u) (π v), mul_inv_cancel_right, mul_inv_cancel])
  have hinvW : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (by rw [← pow_two, hW])
  by_contra hne
  push Not at hne
  obtain ⟨u₀, hu₀⟩ := hne
  have hu₀z : u₀ ^ 2 = z := (hsq1 u₀).resolve_left hu₀
  have hz1 : z ≠ 1 := fun h => hu₀ (hu₀z.trans h)
  have hπu₀ : π u₀ ≠ 1 := fun h => by
    rcases (hz u₀).mp h with h | h
    · exact hu₀ (by rw [h, one_pow])
    · exact hu₀ (by rw [h, hz2])
  have hallz : ∀ v, π v ≠ 1 → v ^ 2 = z := fun v hv => (hsq v u₀ hv hπu₀).trans hu₀z
  have hcz : ∀ u x : U, π u ≠ 1 → π x ≠ 1 → π x ≠ π u → u * x * u⁻¹ * x⁻¹ = z := by
    intro u x hu hx hxu
    have hux : π (u * x) ≠ 1 := by
      rw [map_mul]
      intro h
      apply hxu
      calc π x = (π u)⁻¹ * (π u * π x) := by rw [inv_mul_cancel_left]
        _ = π u := by rw [h, mul_one, hinvW]
    have h1 := hallz _ hux
    rcases hcomm1 u x with hc | hc
    · exfalso
      have hc' : u * x = x * u := by
        calc u * x = u * x * u⁻¹ * x⁻¹ * (x * u) := by group
          _ = x * u := by rw [hc, one_mul]
      have : (u * x) ^ 2 = 1 := by
        rw [pow_two, show u * x * (u * x) = u * u * (x * x) by
          rw [mul_assoc, ← mul_assoc x u x, ← hc', mul_assoc, mul_assoc]]
        rw [← pow_two, ← pow_two, hallz u hu, hallz x hx, ← pow_two, hz2]
      exact hz1 (h1.symm.trans this)
    · exact hc
  obtain ⟨y₁, -, hy₁⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, π u₀} : Finset W)) (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      calc ({1, π u₀} : Finset W).card ≤ 2 := Finset.card_le_two
        _ < 8 := by norm_num
        _ ≤ _ := h8)
  obtain ⟨v, rfl⟩ := hπ y₁
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy₁
  obtain ⟨hv1, hvu⟩ := hy₁
  obtain ⟨y₂, -, hy₂⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, π u₀, π v, π u₀ * π v} : Finset W)) (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      calc ({1, π u₀, π v, π u₀ * π v} : Finset W).card ≤ 4 := Finset.card_le_four
        _ < 8 := by norm_num
        _ ≤ _ := h8)
  obtain ⟨w, rfl⟩ := hπ y₂
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy₂
  obtain ⟨hw1, hwu, hwv, hwuv⟩ := hy₂
  have hcv := hcz u₀ v hπu₀ hv1 hvu
  have hcw := hcz u₀ w hπu₀ hw1 hwu
  have hvw1 : π (v * w) ≠ 1 := by
    rw [map_mul]
    intro h
    apply hwv
    calc π w = (π v)⁻¹ * (π v * π w) := by rw [inv_mul_cancel_left]
      _ = π v := by rw [h, mul_one, hinvW]
  have hvwu : π (v * w) ≠ π u₀ := by
    rw [map_mul]
    intro h
    apply hwuv
    calc π w = (π v)⁻¹ * (π v * π w) := by rw [inv_mul_cancel_left]
      _ = π v * π u₀ := by rw [h, hinvW]
      _ = π u₀ * π v := mul_comm _ _
  have hcvw := hcz u₀ (v * w) hπu₀ hvw1 hvwu
  have hv' : u₀ * v * u₀⁻¹ = z * v := by
    calc u₀ * v * u₀⁻¹ = u₀ * v * u₀⁻¹ * v⁻¹ * v := by group
      _ = z * v := by rw [hcv]
  have hw' : u₀ * w * u₀⁻¹ = z * w := by
    calc u₀ * w * u₀⁻¹ = u₀ * w * u₀⁻¹ * w⁻¹ * w := by group
      _ = z * w := by rw [hcw]
  have h1 : u₀ * (v * w) * u₀⁻¹ * (v * w)⁻¹ = 1 := by
    calc u₀ * (v * w) * u₀⁻¹ * (v * w)⁻¹ =
        (u₀ * v * u₀⁻¹) * (u₀ * w * u₀⁻¹) * w⁻¹ * v⁻¹ := by group
      _ = z * v * (z * w) * w⁻¹ * v⁻¹ := by rw [hv', hw']
      _ = z * (v * z) * v⁻¹ := by group
      _ = z * (z * v) * v⁻¹ := by rw [← hzc v]
      _ = 1 := by rw [← mul_assoc, ← pow_two, hz2]; group
  exact hz1 (hcvw.symm.trans h1)

end CFSG.Quasithin.ElemAb

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  (s : Set714 G T L V t z)
include s

theorem U_le_N
    (h1222 : Stmt12_2_2) :
    U714 T L V z ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun _ hu =>
  centralizer_le_normalizer_zpowers z (s.le_cent ((s.U_le_T h1222).1 hu))

@[expose] noncomputable def piU
    (h1222 : Stmt12_2_2) : ↥(U714 T L V z) →* ↥(Ut T L V z) :=
  ((tmk (Subgroup.zpowers z)).comp (Subgroup.inclusion (s.U_le_N h1222))).codRestrict _
    fun u => secMk_mem_secImg u.2

theorem piU_coe
    (h1222 : Stmt12_2_2) (u : ↥(U714 T L V z)) :
    ((s.piU h1222 u : ↥(Ut T L V z)) : Gt z) =
      tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.U_le_N h1222) u) := rfl

theorem piU_surjective
    (h1222 : Stmt12_2_2) : Function.Surjective (s.piU h1222) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem z_mem_U : z ∈ U714 T L V z := le_conjClosure _ _ s.mem

theorem piU_eq_one_iff
    (h1222 : Stmt12_2_2) (u : ↥(U714 T L V z)) :
    s.piU h1222 u = 1 ↔ u = 1 ∨ u = ⟨z, s.z_mem_U⟩ := by
  have hz2 : z ^ 2 = 1 := by rw [← s.orderOf_z]; exact pow_orderOf_eq_one z
  rw [← Subtype.coe_inj, s.piU_coe, OneMemClass.coe_one, secMk_eq_one_iff]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hk' : z ^ k = (u : G) := hk
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      refine Subtype.ext ?_
      show (u : G) = 1
      rw [← hk', hm, zpow_mul, show z ^ (2 : ℤ) = 1 by exact_mod_cast hz2, one_zpow]
    · right
      refine Subtype.ext ?_
      show (u : G) = z
      rw [← hk', hm, zpow_add, zpow_mul, show z ^ (2 : ℤ) = 1 by exact_mod_cast hz2, one_zpow,
        one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z

theorem sq_eq_one_U
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    ∀ u ∈ U714 T L V z, u ^ 2 = 1 := by
  obtain ⟨hHs, h8⟩ := s.Hs_eq_top h1222 h37 h38 h39 hU
  have hW : ∀ w : ↥(Ut T L V z), w ^ 2 = 1 := fun w =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ w.2)
  have hz2 : z ^ 2 = 1 := by rw [← s.orderOf_z]; exact pow_orderOf_eq_one z
  have hzU : ∀ u ∈ U714 T L V z, z * u = u * z := fun u hu =>
    (Subgroup.mem_centralizer_singleton_iff.mp (s.le_cent ((s.U_le_T h1222).1 hu))).symm
  have hsqz : ∀ u ∈ U714 T L V z, u ^ 2 ∈ Subgroup.zpowers z := by
    intro u hu
    have h1 := hW (s.piU h1222 ⟨u, hu⟩)
    rw [← map_pow, s.piU_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · rw [show u ^ 2 = 1 from congrArg Subtype.val h1]
      exact Subgroup.one_mem _
    · rw [show u ^ 2 = z from congrArg Subtype.val h1]
      exact Subgroup.mem_zpowers z
  have hsq : ∀ u v : ↥(U714 T L V z), s.piU h1222 u ≠ 1 → s.piU h1222 v ≠ 1 →
      u ^ 2 = v ^ 2 := by
    intro u v hu hv
    obtain ⟨φ, hφ⟩ := ElemAb.exists_mulAut_apply_eq hW hu hv
    have hφr : φ ∈ (s.rho h1222).range := by
      rw [s.range_rho h1222, hHs]
      exact Subgroup.mem_top φ
    obtain ⟨h, rfl⟩ := hφr
    have hv' := congrArg Subtype.val hφ
    rw [s.rho_apply, s.piU_coe, s.piU_coe] at hv'
    have e : tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h) *
        tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.U_le_N h1222) u) *
        (tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h))⁻¹ =
        tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h *
          Subgroup.inclusion (s.U_le_N h1222) u * (Subgroup.inclusion (s.H_le_N h1222) h)⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e] at hv'
    have hk := secMk_eq_secMk_iff.mp hv'
    set a : G := (h : G) * u * (h : G)⁻¹ with ha
    have hk' : a⁻¹ * v ∈ Subgroup.zpowers z := hk
    have hzh : (h : G) * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp
      (s.H_le_Gz h1222 h.2)
    have hu2h : (h : G) * ((u : G) ^ 2) * (h : G)⁻¹ = (u : G) ^ 2 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hsqz u u.2)
      rw [← hk, ((Commute.zpow_right (show Commute (h : G) z from hzh) k)).eq,
        mul_inv_cancel_right]
    have ha2 : a ^ 2 = (u : G) ^ 2 := by
      rw [ha, ← hu2h, pow_two, pow_two]
      group
    obtain ⟨k, hk2⟩ := Subgroup.mem_zpowers_iff.mp hk'
    have hv2 : (v : G) = a * z ^ k := by rw [hk2, mul_inv_cancel_left]
    apply Subtype.ext
    show (u : G) ^ 2 = (v : G) ^ 2
    have haz : Commute z a := by
      have hzh' : Commute z (h : G) := hzh.symm
      have hzu : Commute z (u : G) := hzU u u.2
      exact (hzh'.mul_right hzu).mul_right hzh'.inv_right
    have hzk : (z ^ k) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show z ^ ((2 : ℕ) : ℤ) = 1 by
        exact_mod_cast hz2, one_zpow]
    rw [hv2, (Commute.mul_pow (haz.zpow_left k).symm 2), hzk, mul_one, ha2]
  have hall := ElemAb.sq_eq_one_of_sq_eq hW (s.piU h1222) (s.piU_surjective h1222)
    (z := ⟨z, s.z_mem_U⟩) (s.piU_eq_one_iff h1222)
    (fun u => Subtype.ext (hzU u u.2)) (Subtype.ext hz2) hsq h8
  intro u hu
  exact congrArg Subtype.val (hall ⟨u, hu⟩)

end CFSG.Quasithin.H13.S127.L715.Set714
