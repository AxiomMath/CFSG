module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalT23
public import CFSG.RankThree.GF2n.Parrott.SpinSigmaUVForms
public import CFSG.RankThree.GF2n.Parrott.SpinBridge
public import CFSG.RankThree.GF2n.Parrott.Lemma16
public import CFSG.RankThree.GF2n.Parrott.LiftSquare

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
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)


omit hN in
private theorem z_centralizes_element_kl (h : Tim79a.ParrottHyp z) (g : ↥(H z)) :
    (g : G) * z = z * (g : G) :=
  Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) (g : G) g.2

omit hN in
private theorem conjV_pi_eq_self_of_mem_centralizer_kl (h : Tim79a.ParrottHyp z) {g : ↥(H z)}
    {y : J z} (hy : (y : G) ∈ Subgroup.centralizer ({(g : G)} : Set G)) :
    conjV h g (QuotientV.pi z y) = QuotientV.pi z y := by
  rw [conjV_mk h g y]
  congr 1
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  have hc : (y : G) * (g : G) = (g : G) * (y : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hy
  rw [← hc]
  group

private theorem not_mem_centralizer_z1_of_qH_eq_uv_kl (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) {x : ↥(H z)}
    (hqx : qH (z := z) D x = uA * vA ∨ qH (z := z) D x = tA * (uA * vA)) :
    (x : G) ∉ Subgroup.centralizer ({z₁} : Set G) := by
  intro hxz₁
  have hqmem := (mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord x).mp hxz₁
  rcases hqx with hq | hq
  · rw [hq] at hqmem
    exact uvA_not_mem_QP45 hqmem
  · rw [hq, tA_mul_uvA_comm] at hqmem
    exact uvtA_not_mem_QP45 hqmem

private theorem nat_card_fixed_eq_fixCard_kl (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Nat.card {v : Fin 8 → ZMod 2 // M *ᵥ v = v} = fixCard M := by
  rw [fixCard, Nat.card_eq_fintype_card]

private theorem card_fixed_inf_kl (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (g₁ g₂ : ↥(H z)) :
    Nat.card ↥(autFixedSubgroup (conjV h g₁) ⊓ autFixedSubgroup (conjV h g₂)) =
      Nat.card {w : Fin 8 → ZMod 2 //
        ((rhoA (qH (z := z) D g₁) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
        ((rhoA (qH (z := z) D g₂) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} := by
  classical
  have himage : spinVecToV h P '' {w : Fin 8 → ZMod 2 |
      ((rhoA (qH (z := z) D g₁) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA (qH (z := z) D g₂) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} =
      (↑(autFixedSubgroup (conjV h g₁) ⊓ autFixedSubgroup (conjV h g₂)) :
        Set (QuotientV.V z)) := by
    ext v
    constructor
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup]
      exact ⟨by rw [conjV_spinVecToV D h P hP, h1],
        by rw [conjV_spinVecToV D h P hP, h2]⟩
    · intro hv
      rw [SetLike.mem_coe, Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup] at hv
      obtain ⟨h1v, h2v⟩ := hv
      obtain ⟨w, rfl⟩ := spinVecToV_surjective h P v
      refine ⟨w, ⟨?_, ?_⟩, rfl⟩
      · have h' := h1v
        rw [conjV_spinVecToV D h P hP] at h'
        exact spinVecToV_injective h P h'
      · have h' := h2v
        rw [conjV_spinVecToV D h P hP] at h'
        exact spinVecToV_injective h P h'
  have hset : Nat.card ↥(autFixedSubgroup (conjV h g₁) ⊓ autFixedSubgroup (conjV h g₂)) =
      Nat.card ↥(↑(autFixedSubgroup (conjV h g₁) ⊓ autFixedSubgroup (conjV h g₂)) :
        Set (QuotientV.V z)) := rfl
  rw [hset, ← himage, Nat.card_image_of_injective (spinVecToV_injective h P)]
  rfl

private theorem nat_card_fixed_sigma_mul_b_kl {b : A45}
    (hb : b = uA * vA ∨ b = tA * (uA * vA)) :
    Nat.card {w : Fin 8 → ZMod 2 //
      ((rhoA (s1A * s2A⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA b : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} = 4 := by
  classical
  rcases hb with rfl | rfl
  · have hbmem : (uA * vA : A45) ∈
        Subgroup.closure ({tA, uA * vA} : Set A45) :=
      Subgroup.subset_closure (by simp)
    have hb1 : (uA * vA : A45) ≠ 1 := by
      intro h1
      exact uvA_not_mem_QP45 (h1 ▸ Subgroup.one_mem _)
    have hcard := spinFixedCard_sigma1_mul_sigma2_inv_mul hbmem hb1
    have heq : ∀ w : Fin 8 → ZMod 2,
        (((rhoA (s1A * s2A⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
          ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) ↔
        ((rhoA (s1A * s2A⁻¹ * (uA * vA)) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
      intro w
      constructor
      · rintro ⟨h1, h2⟩
        rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h2, h1]
      · intro hw
        exact spin_fixed_of_fixed_sigma_mul_uv hw
    rw [Nat.card_congr (Equiv.subtypeEquivRight heq), nat_card_fixed_eq_fixCard_kl, hcard]
  · have hbmem : (tA * (uA * vA) : A45) ∈
        Subgroup.closure ({tA, uA * vA} : Set A45) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    have hb1 : (tA * (uA * vA) : A45) ≠ 1 := by
      intro h1
      apply uvtA_not_mem_QP45
      rw [← tA_mul_uvA_comm, h1]
      exact Subgroup.one_mem _
    have hcard := spinFixedCard_sigma1_mul_sigma2_inv_mul hbmem hb1
    have heq : ∀ w : Fin 8 → ZMod 2,
        (((rhoA (s1A * s2A⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
          ((rhoA (tA * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) ↔
        ((rhoA (s1A * s2A⁻¹ * (tA * (uA * vA))) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
      intro w
      constructor
      · rintro ⟨h1, h2⟩
        rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h2, h1]
      · intro hw
        exact spin_fixed_of_fixed_sigma_mul_t_uv hw
    rw [Nat.card_congr (Equiv.subtypeEquivRight heq), nat_card_fixed_eq_fixCard_kl, hcard]

private theorem nat_card_fixed_sigma_mul_uv_inf_t_kl :
    Nat.card {w : Fin 8 → ZMod 2 //
      ((rhoA (s1A * s2A⁻¹ * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} = 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact spin_card_fixed_sigma_mul_uv_t


omit hN in
private theorem not_mem_centralizer_z_mul_z1_kl (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {x : ↥(H z)} (hxz₁ : (x : G) ∉ Subgroup.centralizer ({z₁} : Set G))
    (hx : (x : G) ∈ Subgroup.centralizer ({z * z₁} : Set G)) : False := by
  have hz2 : z * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at h2
  have hz1eq : z₁ = z * (z * z₁) := by
    calc z₁ = (z * z) * z₁ := by rw [hz2, one_mul]
      _ = z * (z * z₁) := by group
  have hzx : (x : G) * z = z * (x : G) :=
    Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) (x : G) x.2
  have hxconj : (x : G) * (z * z₁) * (x : G)⁻¹ = z * z₁ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx]
    group
  have hz1conj : (x : G) * z₁ * (x : G)⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord x.2 hxz₁
  have hxzx : (x : G) * z * (x : G)⁻¹ = z := by
    calc (x : G) * z * (x : G)⁻¹ = (z * (x : G)) * (x : G)⁻¹ := by rw [hzx]
      _ = z := by group
  have hconj1 : (x : G) * z₁ * (x : G)⁻¹ = z₁ := by
    calc (x : G) * z₁ * (x : G)⁻¹
        = (x : G) * (z * (z * z₁)) * (x : G)⁻¹ := by
          conv_lhs => rw [hz1eq]
      _ = ((x : G) * z * (x : G)⁻¹) * ((x : G) * (z * z₁) * (x : G)⁻¹) := by group
      _ = z * (z * z₁) := by rw [hxzx, hxconj]
      _ = z₁ := hz1eq.symm
  apply hxz₁
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (x : G) * z₁ = ((x : G) * z₁ * (x : G)⁻¹) * (x : G) := by group
    _ = z₁ * (x : G) := by rw [hconj1]

theorem card_J_inf_centralizer_sigma1Nine_mul_inv_eq (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    Nat.card ↥(J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) =
      64 := by
  exact (card_J_inf_centralizer_sigma1Nine_mul_inv_of_spin (z := z) D h P hP hσ₂ hq₂ hc₂).trans
    (by norm_num)

theorem exists_mem_centralizer_pi_eq_of_fixed (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {σ x : ↥(H z)} (hσ : orderOf σ = 3) (hZσ : conjZ z σ = 1) (hx2 : x * x = 1)
    (hxz₁ : (x : G) ∉ centralizer ({z₁} : Set G))
    {w : QuotientV.V z} (hwσ : conjV h σ w = w) (hwx : conjV h x w = w) :
    ∃ c : J z, (c : G) ∈ centralizer ({(σ : G)} : Set G) ∧
      (c : G) ∈ centralizer ({(x : G)} : Set G) ∧ QuotientV.pi z c = w := by
  classical
  obtain ⟨j, hj⟩ := QuotientV.pi_surjective z w
  have hσ3H : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hjσ : j ∈ centralizerJ σ :=
    mem_centralizerJ_of_conjV_pi_eq (z := z) h hσ3H hZσ (by rw [hj]; exact hwσ)
  have hjσG : (j : G) ∈ centralizer ({(σ : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hjσ)
  have hjx2 : (x : G) * (x : G) = 1 := congrArg Subtype.val hx2
  let eJ : J z := conjJ' z x j * j⁻¹
  have heJ : (eJ : G) ∈ centerIn (J z) := by
    refine (pi_eq_one_iff_mem_centerIn eJ.2).mp ?_
    change QuotientV.pi z (conjJ' z x j * j⁻¹) = 1
    rw [map_mul, map_inv, ← conjV_mk h x j, hj, hwx, mul_inv_cancel]
  have hrel : conjJ' z x j = eJ * j := by
    show conjJ' z x j = conjJ' z x j * j⁻¹ * j
    group
  have hx2aut : (conjJ' z x : MulAut (J z)) ^ 2 = 1 := by
    rw [← map_pow, pow_two, hx2, map_one]
  have hxxJ : conjJ' z x (conjJ' z x j) = j := by
    have h1 := congrArg (fun f : MulAut (J z) => f j) hx2aut
    simpa [pow_two] using h1
  have hefix : conjJ' z x eJ = eJ := by
    have h1 : j = conjJ' z x (eJ * j) := by rw [← hrel]; exact hxxJ.symm
    rw [map_mul, hrel] at h1
    have h1' : j = (conjJ' z x eJ * eJ) * j := by
      calc j = conjJ' z x eJ * (eJ * j) := h1
        _ = (conjJ' z x eJ * eJ) * j := by group
    have h2 : conjJ' z x eJ * eJ = 1 := mul_right_cancel (by rw [one_mul]; exact h1'.symm)
    have he2 : eJ * eJ = 1 := by
      apply Subtype.ext
      simpa using centerIn_J_sq h heJ
    calc conjJ' z x eJ = conjJ' z x eJ * (eJ * eJ) := by rw [he2, mul_one]
      _ = (conjJ' z x eJ * eJ) * eJ := by group
      _ = eJ := by rw [h2, one_mul]
  have hxe : (x : G) * (eJ : G) * (x : G)⁻¹ = (eJ : G) := by
    have h1 := congrArg (fun y : J z => (y : G)) hefix
    rwa [conjJ'_apply_coe] at h1
  have hxe_cent : (x : G) ∈ centralizer ({(eJ : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (x : G) * (eJ : G) = ((x : G) * (eJ : G) * (x : G)⁻¹) * (x : G) := by group
        _ = (eJ : G) * (x : G) := by rw [hxe])
  have hxz_cent : (x : G) ∈ centralizer ({(z : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (z_centralizes_element_kl h x)
  have hzsq : z * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at h2
  have hz1sq : z₁ * z₁ = 1 := by
    have h2 := pow_orderOf_eq_one z₁
    rwa [hord, pow_two] at h2
  have hcases : (eJ : G) = 1 ∨ (eJ : G) = z := by
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp heJ with he | he | he | he
    · exact Or.inl he
    · exact Or.inr he
    · exfalso
      exact hxz₁ (by rwa [he] at hxe_cent)
    · exfalso
      have hxzz1 : (x : G) * (z * z₁) * (x : G)⁻¹ = z * z₁ := by rw [← he]; exact hxe
      have hxz1conj : (x : G) * z₁ * (x : G)⁻¹ = z * z₁ :=
        conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord x.2 hxz₁
      have hcontra : z₁ = z * z₁ := by
        have h1 : (x : G) * z₁ * (x : G)⁻¹ = (x : G) * (z * z₁) * (x : G)⁻¹ := by
          rw [hxz1conj, hxzz1]
        have h2 := congrArg (fun t : G => (x : G)⁻¹ * t * (x : G)) h1
        simpa [mul_assoc] using h2
      have hzone : z = 1 := by
        calc z = z * (z₁ * z₁) := by rw [hz1sq, mul_one]
          _ = (z * z₁) * z₁ := by group
          _ = z₁ * z₁ := by rw [← hcontra]
          _ = 1 := hz1sq
      have hordz : orderOf z = 2 := h.1
      rw [hzone, orderOf_one] at hordz
      norm_num at hordz
  rcases hcases with he | he
  · refine ⟨j, hjσG, ?_, hj⟩
    have heJ_eq : eJ = 1 := Subtype.ext he
    have hjx : conjJ' z x j = j := by rw [hrel, heJ_eq, one_mul]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg (fun y : J z => (y : G)) hjx
    rw [conjJ'_apply_coe] at h1
    calc (j : G) * (x : G) = ((x : G) * (j : G) * (x : G)⁻¹) * (x : G) := by rw [h1]
      _ = (x : G) * (j : G) := by group
  ·
    have heJ_eq : eJ = (⟨z, z_mem_J h⟩ : J z) := Subtype.ext he
    have hxjz : (x : G) * (j : G) * (x : G)⁻¹ = (j : G) * z := by
      have h1 := congrArg (fun y : J z => (y : G)) (hrel.trans (by rw [heJ_eq]))
      rw [conjJ'_apply_coe, Subgroup.coe_mul] at h1
      have hzj : z * (j : G) = (j : G) * z :=
        (Subgroup.mem_centralizer_iff.mp (z_mem_centerIn_J h).2 (j : G) j.2).symm
      rw [← hzj]
      exact h1
    have hxz1conj : (x : G) * z₁ * (x : G)⁻¹ = z * z₁ :=
      conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord x.2 hxz₁
    have hxjz1 : (x : G) * ((j : G) * z₁) * (x : G)⁻¹ = (j : G) * z₁ := by
      calc (x : G) * ((j : G) * z₁) * (x : G)⁻¹
          = ((x : G) * (j : G) * (x : G)⁻¹) * ((x : G) * z₁ * (x : G)⁻¹) := by group
        _ = ((j : G) * z) * (z * z₁) := by rw [hxjz, hxz1conj]
        _ = (j : G) * z₁ := by
            rw [mul_assoc, ← mul_assoc z z z₁, hzsq, one_mul]
    have hz₁J : z₁ ∈ J z :=
      (Subgroup.mem_inf.mp (show z₁ ∈ J z ⊓ Subgroup.centralizer (J z : Set G) from hz₁)).1
    refine ⟨j * ⟨z₁, hz₁J⟩, ?_, ?_, ?_⟩
    · have hz1σ : z₁ ∈ centralizer ({(σ : G)} : Set G) :=
        centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := σ) hZσ hz₁
      have hprod : ((j : G) * z₁) ∈ centralizer ({(σ : G)} : Set G) :=
        Subgroup.mul_mem _ hjσG hz1σ
      simpa using hprod
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((j : G) * z₁) * (x : G)
          = ((x : G) * ((j : G) * z₁) * (x : G)⁻¹) * (x : G) := by rw [hxjz1]
        _ = (x : G) * ((j : G) * z₁) := by group
    · rw [map_mul]
      have hzj : QuotientV.pi z ⟨z₁, hz₁J⟩ = 1 :=
        (pi_eq_one_iff_mem_centerIn hz₁J).mpr hz₁
      rw [hzj, mul_one, hj]

theorem card_J_inf_centralizer_inf_centralizer_eq_eight (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = uA * vA ∨ qH (z := z) D x = tA * (uA * vA)) :
    Nat.card ↥(J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(x : G)} : Set G)) = 8 := by
  classical
  have _ := hxσ
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hqσ : qH (z := z) D σ = s1A * s2A⁻¹ := by
    show qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) = s1A * s2A⁻¹
    rw [map_mul, map_inv, qH_sigma1Nine (z := z) D, hq₂]
  have hZσ : conjZ z σ = 1 := by
    show conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1
    have h2 : conjZ z σ₂ = 1 :=
      conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
    rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D, h2, inv_one, mul_one]
  have hσord : orderOf σ = 3 := by
    change orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hxz₁ : (x : G) ∉ Subgroup.centralizer ({z₁} : Set G) :=
    not_mem_centralizer_z1_of_qH_eq_uv_kl (z := z) D h hZ hz₁ hz₁z hord hqx
  have hzA : (z : G) ∈ J z ⊓ Subgroup.centralizer ({(σ : G)} : Set G) ⊓
      Subgroup.centralizer ({(x : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨z_mem_J h, Subgroup.mem_centralizer_singleton_iff.mpr
        (z_centralizes_element_kl h σ).symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (z_centralizes_element_kl h x).symm⟩
  let A : Subgroup G := J z ⊓ Subgroup.centralizer ({(σ : G)} : Set G) ⊓
    Subgroup.centralizer ({(x : G)} : Set G)
  have hAJ : A ≤ J z := fun a ha => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).1
  let g : A →* J z := (Subgroup.subtype A).codRestrict (J z) (fun a => hAJ a.2)
  let f : A →* QuotientV.V z := (QuotientV.pi z).comp g
  have hcard := Subgroup.card_ker_mul_card_range f
  have hAZ : A ⊓ centerIn (J z) = Subgroup.zpowers z := by
    refine le_antisymm ?_ ?_
    · intro e he
      obtain ⟨heA, heZ⟩ := Subgroup.mem_inf.mp he
      have heCx : (e : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) :=
        (Subgroup.mem_inf.mp heA).2
      rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp heZ with he1 | he1 | he1 | he1
      · rw [he1]; exact Subgroup.one_mem _
      · rw [he1]; exact Subgroup.mem_zpowers z
      · have heCx₁ : (z₁ : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
          rw [← he1]; exact heCx
        exfalso
        exact hxz₁ (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp heCx₁).symm)
      · have heCx' : (z * z₁ : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
          rw [← he1]; exact heCx
        exfalso
        exact not_mem_centralizer_z_mul_z1_kl h hz₁ hz₁z hord hxz₁
          (Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp heCx').symm)
    · intro e he
      have heZ : e ∈ centerIn (J z) := Subgroup.zpowers_le.mpr (z_mem_centerIn_J h) he
      have heA : e ∈ A := Subgroup.zpowers_le.mpr hzA he
      exact Subgroup.mem_inf.mpr ⟨heA, heZ⟩
  have hker : Nat.card ↥f.ker = 2 := by
    have hker_eq : f.ker = (centerIn (J z)).subgroupOf A := by
      ext a
      constructor
      · intro ha
        rw [MonoidHom.mem_ker] at ha
        have haJ : (a : G) ∈ J z := hAJ a.2
        have h1 : QuotientV.pi z ⟨(a : G), haJ⟩ = 1 := ha
        exact Subgroup.mem_subgroupOf.mpr ((pi_eq_one_iff_mem_centerIn haJ).mp h1)
      · intro ha
        rw [MonoidHom.mem_ker]
        exact (pi_eq_one_iff_mem_centerIn (hAJ a.2)).mpr (Subgroup.mem_subgroupOf.mp ha)
    rw [hker_eq, ← Subgroup.card_map_of_injective (Subgroup.subtype_injective A),
      Subgroup.subgroupOf_map_subtype, inf_comm, hAZ, Nat.card_zpowers, h.1]
  have hrange_eq : f.range =
      autFixedSubgroup (conjV h σ) ⊓ autFixedSubgroup (conjV h x) := by
    ext v
    constructor
    · intro hv
      rw [MonoidHom.mem_range] at hv
      obtain ⟨a, rfl⟩ := hv
      obtain ⟨⟨haJ, haσ⟩, hax⟩ := Subgroup.mem_inf.mp a.2
      rw [Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup]
      exact ⟨conjV_pi_eq_self_of_mem_centralizer_kl h (y := ⟨(a : G), haJ⟩) haσ,
        conjV_pi_eq_self_of_mem_centralizer_kl h (y := ⟨(a : G), haJ⟩) hax⟩
    · intro hv
      rw [Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup] at hv
      obtain ⟨hσv, hxv⟩ := hv
      obtain ⟨c, hcσ, hcx, hpic⟩ :=
        exists_mem_centralizer_pi_eq_of_fixed h hz₁ hz₁z hord hσord hZσ hx2 hxz₁ hσv hxv
      rw [MonoidHom.mem_range]
      refine ⟨⟨(c : G), Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨c.2, hcσ⟩, hcx⟩⟩, ?_⟩
      change QuotientV.pi z ⟨(c : G), c.2⟩ = v
      rw [hpic]
  have hrange : Nat.card ↥f.range = 4 := by
    rw [hrange_eq, card_fixed_inf_kl (z := z) D h P hP σ x, hqσ]
    exact nat_card_fixed_sigma_mul_b_kl hqx
  rw [hker, hrange] at hcard
  change Nat.card ↥A = 8
  omega



private theorem sigma_facts_kl (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) = s1A * s2A⁻¹ ∧
      conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 ∧
      orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, map_inv, qH_sigma1Nine (z := z) D, hq₂]
  · have h2 : conjZ z σ₂ = 1 :=
      conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
    rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D, h2, inv_one, mul_one]
  · rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂

theorem mul_self_eq_one_of_conjV_pi_eq_of_qH_eq_uv (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {x : ↥(H z)}
    (hqx : qH (z := z) D x = uA * vA) {b : J z}
    (hbσ : (b : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hbx : conjV h x (QuotientV.pi z b) = QuotientV.pi z b) :
    (b : G) * b = 1 := by
  classical
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hqσ : qH (z := z) D σ = s1A * s2A⁻¹ := by
    show qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) = s1A * s2A⁻¹
    rw [map_mul, map_inv, qH_sigma1Nine (z := z) D, hq₂]
  have hσfix : conjV h σ (QuotientV.pi z b) = QuotientV.pi z b :=
    conjV_pi_eq_self_of_mem_centralizer_kl h hbσ
  obtain ⟨w, hw⟩ := spinVecToV_surjective h P (QuotientV.pi z b)
  have hσw : ((rhoA (s1A * s2A⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    have h1 : spinVecToV h P
        (((rhoA (qH (z := z) D σ) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
        spinVecToV h P w := by
      rw [← conjV_spinVecToV D h P hP σ w, hw, hσfix]
    rw [hqσ] at h1
    exact spinVecToV_injective h P h1
  have hxw : ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    have h1 : spinVecToV h P
        (((rhoA (qH (z := z) D x) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
        spinVecToV h P w := by
      rw [← conjV_spinVecToV D h P hP x w, hw, hbx]
    rw [hqx] at h1
    exact spinVecToV_injective h P h1
  have hsb : ((rhoA (s1A * s2A⁻¹ * (uA * vA)) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hxw, hσw]
  have hq0 : q w = 0 := spin_q_eq_zero_of_fixed_sigma_mul_uv w hsb
  have hqV0 : qVZMod h (QuotientV.pi z b) = 0 := by
    rw [← hw, qVZMod_spinVecToV_eq_q D h P hP, hq0]
  have hqV : qV h (QuotientV.pi z b) = 1 := (qVZMod_eq_zero_iff h _).mp hqV0
  have hqJ : qJ h b = 1 := by rwa [qV_pi] at hqV
  have hcoe : (b : G) ^ 2 = 1 := by
    have hone := congrArg (fun a : Subgroup.zpowers z => (a : G)) hqJ
    simpa [qJ_coe] using hone
  rwa [pow_two] at hcoe



theorem exists_mem_centralizer_mul_self_eq_z_of_qH_eq_t_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = tA * (uA * vA)) :
    ∃ c ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(x : G)} : Set G), c * c = z := by
  classical
  have _ := hxσ
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  obtain ⟨hqσ, hZσ, hσord⟩ := sigma_facts_kl (z := z) D h hσ₂ hq₂ hc₂
  have hxz₁ : (x : G) ∉ Subgroup.centralizer ({z₁} : Set G) :=
    not_mem_centralizer_z1_of_qH_eq_uv_kl (z := z) D h hZ hz₁ hz₁z hord (Or.inr hqx)
  obtain ⟨w, hwfix, hqw⟩ := spin_exists_fixed_sigma_mul_t_uv_q_eq_one
  obtain ⟨hσw, htw⟩ := spin_fixed_of_fixed_sigma_mul_t_uv hwfix
  have hσv : conjV h σ (spinVecToV h P w) = spinVecToV h P w := by
    rw [conjV_spinVecToV D h P hP, hqσ, hσw]
  have hxv : conjV h x (spinVecToV h P w) = spinVecToV h P w := by
    rw [conjV_spinVecToV D h P hP, hqx, htw]
  obtain ⟨c, hcσ, hcx, hpic⟩ :=
    exists_mem_centralizer_pi_eq_of_fixed h hz₁ hz₁z hord hσord hZσ hx2 hxz₁ hσv hxv
  refine ⟨(c : G), Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨c.2, hcσ⟩, hcx⟩, ?_⟩
  have hqV1 : qVZMod h (QuotientV.pi z c) = 1 := by
    rw [hpic, qVZMod_spinVecToV_eq_q D h P hP, hqw]
  have hqVne : qV h (QuotientV.pi z c) ≠ 1 := by
    intro h1
    have h0 : qVZMod h (QuotientV.pi z c) = 0 := (qVZMod_eq_zero_iff h _).mpr h1
    rw [hqV1] at h0
    norm_num at h0
  have hsq_mem : (c : G) * (c : G) ∈ Subgroup.zpowers z := by
    have h := (qJ h c).2
    rwa [qJ_coe, pow_two] at h
  have hsq_ne : (c : G) * (c : G) ≠ 1 := by
    intro h1
    apply hqVne
    rw [qV_pi]
    apply Subtype.ext
    rw [qJ_coe, pow_two, h1]
    rfl
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hsq_mem with h1 | h1
  · exact absurd h1 hsq_ne
  · exact h1



theorem qH_ne_t_of_forall_commute_of_qH_eq_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = uA * vA) {e : ↥(H z)}
    (he : ∀ c ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(x : G)} : Set G), (e : G) * c = c * e) :
    qH (z := z) D e ≠ tA ∧ qH (z := z) D e ≠ tA * (uA * vA) := by
  classical
  have _ := hxσ
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  obtain ⟨hqσ, hZσ, hσord⟩ := sigma_facts_kl (z := z) D h hσ₂ hq₂ hc₂
  have hxz₁ : (x : G) ∉ Subgroup.centralizer ({z₁} : Set G) :=
    not_mem_centralizer_z1_of_qH_eq_uv_kl (z := z) D h hZ hz₁ hz₁z hord (Or.inl hqx)
  obtain ⟨w, hwfix, hwnt⟩ := spin_exists_fixed_sigma_mul_uv_not_fixed_t
  obtain ⟨hσw, huvw⟩ := spin_fixed_of_fixed_sigma_mul_uv hwfix
  have hσv : conjV h σ (spinVecToV h P w) = spinVecToV h P w := by
    rw [conjV_spinVecToV D h P hP, hqσ, hσw]
  have hxv : conjV h x (spinVecToV h P w) = spinVecToV h P w := by
    rw [conjV_spinVecToV D h P hP, hqx, huvw]
  obtain ⟨c, hcσ, hcx, hpic⟩ :=
    exists_mem_centralizer_pi_eq_of_fixed h hz₁ hz₁z hord hσord hZσ hx2 hxz₁ hσv hxv
  have hcA : (c : G) ∈ J z ⊓ centralizer ({(σ : G)} : Set G) ⊓
      centralizer ({(x : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨c.2, hcσ⟩, hcx⟩
  have hce : (c : G) ∈ Subgroup.centralizer ({(e : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (he (c : G) hcA).symm
  have hfix : conjV h e (QuotientV.pi z c) = QuotientV.pi z c :=
    conjV_pi_eq_self_of_mem_centralizer_kl h hce
  have hew : ((rhoA (qH (z := z) D e) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    have h1 : spinVecToV h P
        (((rhoA (qH (z := z) D e) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
        spinVecToV h P w := by
      rw [← conjV_spinVecToV D h P hP e w, ← hpic]
      exact hfix
    exact spinVecToV_injective h P h1
  constructor
  · intro hq
    apply hwnt
    rw [← hq]
    exact hew
  · intro hq
    apply hwnt
    have h1 : ((rhoA (tA * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
      rw [← hq]
      exact hew
    have h2 : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) = w := by
      have h1' := h1
      rw [map_mul, Matrix.GeneralLinearGroup.coe_mul] at h1'
      simpa only [Matrix.mulVec_mulVec] using h1'
    rw [huvw] at h2
    exact h2



theorem card_centralizer_le_four_of_qH_eq_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = uA * vA) {k : ↥(H z)}
    (hk : qH (z := z) D k = tA) :
    Nat.card ↥(J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(x : G)} : Set G) ⊓ centralizer ({(k : G)} : Set G)) ≤ 4 := by
  classical
  have _ := hxσ
  have _ := hx2
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  obtain ⟨hqσ, hZσ, hσord⟩ := sigma_facts_kl (z := z) D h hσ₂ hq₂ hc₂
  have hxz₁ : (x : G) ∉ Subgroup.centralizer ({z₁} : Set G) :=
    not_mem_centralizer_z1_of_qH_eq_uv_kl (z := z) D h hZ hz₁ hz₁z hord (Or.inl hqx)
  let A : Subgroup G := J z ⊓ Subgroup.centralizer ({(σ : G)} : Set G) ⊓
    Subgroup.centralizer ({(x : G)} : Set G) ⊓ Subgroup.centralizer ({(k : G)} : Set G)
  have hAJ : A ≤ J z := fun a ha =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).1).1
  let g : A →* J z := (Subgroup.subtype A).codRestrict (J z) (fun a => hAJ a.2)
  let f : A →* QuotientV.V z := (QuotientV.pi z).comp g
  have hcard := Subgroup.card_ker_mul_card_range f
  have hker_eq : f.ker = (centerIn (J z)).subgroupOf A := by
    ext a
    constructor
    · intro ha
      rw [MonoidHom.mem_ker] at ha
      have haJ : (a : G) ∈ J z := hAJ a.2
      have h1 : QuotientV.pi z ⟨(a : G), haJ⟩ = 1 := ha
      exact Subgroup.mem_subgroupOf.mpr ((pi_eq_one_iff_mem_centerIn haJ).mp h1)
    · intro ha
      rw [MonoidHom.mem_ker]
      exact (pi_eq_one_iff_mem_centerIn (hAJ a.2)).mpr (Subgroup.mem_subgroupOf.mp ha)
  have hker_le : Nat.card ↥f.ker ≤ 2 := by
    rw [hker_eq, ← Subgroup.card_map_of_injective (Subgroup.subtype_injective A),
      Subgroup.subgroupOf_map_subtype, inf_comm]
    calc Nat.card ↥(A ⊓ centerIn (J z)) ≤ Nat.card ↥(Subgroup.zpowers z) := by
          refine Subgroup.card_le_of_le ?_
          intro e he
          obtain ⟨heA, heZ⟩ := Subgroup.mem_inf.mp he
          have heCx : (e : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) :=
            (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp heA).1).2
          rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp heZ with he1 | he1 | he1 | he1
          · rw [he1]; exact Subgroup.one_mem _
          · rw [he1]; exact Subgroup.mem_zpowers z
          · exfalso
            have heCx₁ : (z₁ : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
              rw [← he1]; exact heCx
            exact hxz₁ (Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_singleton_iff.mp heCx₁).symm)
          · exfalso
            have heCx' : (z * z₁ : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
              rw [← he1]; exact heCx
            exact not_mem_centralizer_z_mul_z1_kl h hz₁ hz₁z hord hxz₁
              (Subgroup.mem_centralizer_singleton_iff.mpr
                (Subgroup.mem_centralizer_singleton_iff.mp heCx').symm)
      _ = 2 := by rw [Nat.card_zpowers, h.1]
  have hrange_le : f.range ≤
      autFixedSubgroup (conjV h (σ * x)) ⊓ autFixedSubgroup (conjV h k) := by
    intro v hv
    rw [MonoidHom.mem_range] at hv
    obtain ⟨a, rfl⟩ := hv
    obtain ⟨⟨⟨haJ, haσ⟩, hax⟩, hak⟩ := Subgroup.mem_inf.mp a.2
    rw [Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup]
    constructor
    · rw [map_mul, MulAut.mul_apply]
      have hfa : f a = QuotientV.pi z ⟨(a : G), haJ⟩ := rfl
      rw [hfa, conjV_pi_eq_self_of_mem_centralizer_kl h (y := ⟨(a : G), haJ⟩) hax]
      exact conjV_pi_eq_self_of_mem_centralizer_kl h (y := ⟨(a : G), haJ⟩) haσ
    · exact conjV_pi_eq_self_of_mem_centralizer_kl h (y := ⟨(a : G), haJ⟩) hak
  have hrange_card : Nat.card ↥(autFixedSubgroup (conjV h (σ * x)) ⊓
      autFixedSubgroup (conjV h k)) = 2 := by
    rw [card_fixed_inf_kl (z := z) D h P hP (σ * x) k]
    have hqσx : qH (z := z) D (σ * x) = s1A * s2A⁻¹ * (uA * vA) := by
      rw [map_mul, hqσ, hqx]
    rw [hqσx, hk]
    exact nat_card_fixed_sigma_mul_uv_inf_t_kl
  have hrange_le_card : Nat.card ↥f.range ≤ 2 :=
    le_trans (Subgroup.card_le_of_le hrange_le) (le_of_eq hrange_card)
  have hmul : Nat.card ↥A ≤ 2 * 2 := by
    rw [← hcard]
    exact Nat.mul_le_mul hker_le hrange_le_card
  change Nat.card ↥A ≤ 4
  omega



end CFSG.RankThree.GF2n.Parrott
