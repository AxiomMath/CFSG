module

public import CFSG.RankThree.GF2n.Parrott.Section5KLFixed
public import CFSG.RankThree.GF2n.Parrott.Section5LocalW

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

private theorem mem_closure_t_uv_iff_kl (e : A45) :
    e ∈ Subgroup.closure ({tA, uA * vA} : Set A45) ↔
      e = 1 ∨ e = tA ∨ e = uA * vA ∨ e = tA * (uA * vA) := by
  constructor
  · intro he
    let S : Subgroup A45 :=
      { carrier := {y | y = 1 ∨ y = tA ∨ y = uA * vA ∨ y = tA * (uA * vA)}
        one_mem' := Or.inl rfl
        mul_mem' := by
          intro y w hy hw
          simp only [Set.mem_setOf_eq] at hy hw ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            rcases hw with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one] <;>
            decide +kernel
        inv_mem' := by
          intro y hy
          simp only [Set.mem_setOf_eq] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] <;>
            decide +kernel }
    have hle : Subgroup.closure ({tA, uA * vA} : Set A45) ≤ S := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle he
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private theorem mul_self_eq_one_of_mem_closure_t_uv_kl {e : A45}
    (he : e ∈ Subgroup.closure ({tA, uA * vA} : Set A45)) : e * e = 1 := by
  rcases (mem_closure_t_uv_iff_kl e).mp he with rfl | rfl | rfl | rfl
  · simp
  · apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using t_sq
  · apply Subtype.ext
    show u * v * (u * v) = 1
    decide +kernel
  · apply Subtype.ext
    show t * (u * v) * (t * (u * v)) = 1
    decide +kernel

theorem closure_mul_self_of_qH_eq_t_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = tA * (uA * vA)) (K : Subgroup G)
    (hK : IsSylowOf 2 K
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(x : G)} : Set G))) :
    z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)) ∧
      Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z := by
  classical
  let σH : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let Cσ : Subgroup G := Subgroup.centralizer ({(σH : G)} : Set G)
  let Cx : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G)
  let Yx : Subgroup G := H z ⊓ Cσ ⊓ Cx
  let C : Subgroup G := J z ⊓ Cσ ⊓ Cx
  have hYxK : IsSylowOf 2 K Yx := hK
  have hqσ : qH (z := z) D σH = s1A * s2A⁻¹ := by
    dsimp only [σH]
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hsq_le : Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z := by
    rw [Subgroup.closure_le]
    rintro w ⟨k, hkK, rfl⟩
    have hkYx : k ∈ Yx := hYxK.le hkK
    have hkH : k ∈ H z := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hkYx).1).1
    have hkσmem : k ∈ Cσ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hkYx).1).2
    have hkσ : k * (σH : G) = (σH : G) * k :=
      Subgroup.mem_centralizer_singleton_iff.mp hkσmem
    let kH : ↥(H z) := ⟨k, hkH⟩
    let a : A45 := qH (z := z) D kH
    have hkHσH : kH * σH = σH * kH := Subtype.ext hkσ
    have ha_comm : a * qH (z := z) D σH = qH (z := z) D σH * a := by
      have h := congrArg (qH (z := z) D) hkHσH
      simpa only [map_mul, a] using h
    have haC : a ∈ Subgroup.centralizer ({(s1A * s2A⁻¹)} : Set A45) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rwa [hqσ] at ha_comm
    have ha_pow : ∃ m, orderOf a = 2 ^ m := by
      obtain ⟨n, hn⟩ := hYxK.isPGroup.exists_orderOf_dvd_pow ⟨k, hkK⟩
      have hkHord : orderOf kH ∣ 2 ^ n := by
        change orderOf (⟨k, hkH⟩ : ↥(H z)) ∣ 2 ^ n
        rw [Subgroup.orderOf_mk]
        show orderOf ((⟨k, hkK⟩ : K) : G) ∣ 2 ^ n
        rw [Subgroup.orderOf_coe]
        exact hn
      have hdvd : orderOf a ∣ 2 ^ n := (orderOf_map_dvd (qH (z := z) D) kH).trans hkHord
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨m, hm⟩
    obtain ⟨b, -, hbE⟩ := exists_conj_mem_closure_t_uv_of_mem_centralizer haC ha_pow
    have hb_sq : (b * a * b⁻¹) * (b * a * b⁻¹) = 1 :=
      mul_self_eq_one_of_mem_closure_t_uv_kl hbE
    have ha_sq : a * a = 1 := by
      calc a * a = b⁻¹ * ((b * a * b⁻¹) * (b * a * b⁻¹)) * b := by group
        _ = b⁻¹ * 1 * b := by rw [hb_sq]
        _ = 1 := by group
    have hkkH : k * k ∈ H z := Subgroup.mul_mem _ hkH hkH
    have hq_kk : qH (z := z) D ⟨k * k, hkkH⟩ = 1 := by
      have hkk : (⟨k * k, hkkH⟩ : ↥(H z)) = kH * kH := rfl
      rw [hkk, map_mul]
      simpa only [a] using ha_sq
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D ⟨k * k, hkkH⟩).mpr hq_kk)
  refine ⟨?_, hsq_le⟩
  obtain ⟨c, hcC, hcc⟩ :=
    exists_mem_centralizer_mul_self_eq_z_of_qH_eq_t_uv D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
      hxσ hx2 hqx
  have hHnorm : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hCY : C ≤ Yx := by
    intro c hc
    rcases Subgroup.mem_inf.mp hc with ⟨hc1, hcx⟩
    rcases Subgroup.mem_inf.mp hc1 with ⟨hcJ, hcσ⟩
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨J_le_H hcJ, hcσ⟩, hcx⟩
  have hYnorm : Yx ≤ Subgroup.normalizer (C : Set G) := by
    intro y hy
    rcases Subgroup.mem_inf.mp hy with ⟨hy1, hyx⟩
    rcases Subgroup.mem_inf.mp hy1 with ⟨hyH, hyσ⟩
    have hyJ : y ∈ Subgroup.normalizer (J z : Set G) := hHnorm hyH
    have hyσ' : y ∈ Subgroup.normalizer (Cσ : Set G) := Subgroup.le_normalizer hyσ
    have hyx' : y ∈ Subgroup.normalizer (Cx : Set G) := Subgroup.le_normalizer hyx
    have h1 : y ∈ Subgroup.normalizer (J z : Set G) ⊓ Subgroup.normalizer (Cσ : Set G) :=
      ⟨hyJ, hyσ'⟩
    have h2 : y ∈ Subgroup.normalizer ((J z ⊓ Cσ : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := J z) (K := Cσ) h1
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := J z ⊓ Cσ) (K := Cx) ⟨h2, hyx'⟩
  have hC2 : IsPGroup 2 C := by
    refine (isPGroup_J h).to_le ?_
    intro c hc
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).1).1
  have hKC' : K.subgroupOf Yx ≤
      Subgroup.normalizer ((C.subgroupOf Yx : Subgroup ↥Yx) : Set ↥Yx) := by
    rw [Subgroup.le_normalizer_iff]
    intro k' _ c' hc'
    have hkY : (k' : G) ∈ Yx := k'.2
    have hcC : (c' : G) ∈ C := hc'
    have h := (Subgroup.le_normalizer_iff.mp hYnorm) (k' : G) hkY (c' : G) hcC
    exact h
  have hC2' : IsPGroup 2 (C.subgroupOf Yx) := hC2.comap_subtype (K := Yx)
  have hK2' : IsPGroup 2 (K.subgroupOf Yx) := hYxK.isPGroup.comap_subtype (K := Yx)
  have hsupP : IsPGroup 2 ((K.subgroupOf Yx ⊔ C.subgroupOf Yx : Subgroup ↥Yx)) :=
    IsPGroup.to_sup_of_normal_right' hK2' hC2' hKC'
  obtain ⟨Q, hQ⟩ := hYxK.exists_sylow_eq_subgroupOf
  have hmax : K.subgroupOf Yx ⊔ C.subgroupOf Yx = (Q : Subgroup ↥Yx) := by
    refine Q.is_maximal' hsupP ?_
    rw [hQ]
    exact le_sup_left
  have hCQ : C.subgroupOf Yx ≤ (Q : Subgroup ↥Yx) := by
    rw [← hmax]
    exact le_sup_right
  have hCK : C ≤ K := by
    intro c hc
    have hc' : (⟨c, hCY hc⟩ : ↥Yx) ∈ C.subgroupOf Yx := hc
    have hle := hCQ hc'
    rw [hQ] at hle
    exact Subgroup.mem_subgroupOf.mp hle
  exact Subgroup.subset_closure ⟨c, hCK hcC, hcc⟩

end CFSG.RankThree.GF2n.Parrott
