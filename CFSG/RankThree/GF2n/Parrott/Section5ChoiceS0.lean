module

public import CFSG.RankThree.GF2n.Parrott.Section5CenterT1
public import CFSG.RankThree.GF2n.Parrott.Section5LocalT

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

omit [Finite G]
  in
private theorem exists_isSylowOf_le_of_isPGroup {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsPGroup p P) (hPK : P ≤ K) : ∃ T : Subgroup G, IsSylowOf p T K ∧ P ≤ T := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨T₀, hT₀⟩ := hP'.exists_le_sylow
  refine ⟨(T₀ : Subgroup K).map K.subtype, ⟨T₀, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hT₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

omit [Finite G]
  in
private theorem conj_eq_or_inv_of_mem_normalizer_zpowers {σ n : G} (hσ : orderOf σ = 3)
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G)) :
    n * σ * n⁻¹ = σ ∨ n * σ * n⁻¹ = σ⁻¹ := by
  have hσ3 : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  have hσ2 : σ ^ 2 = σ⁻¹ := by
    have h2 : σ ^ 2 * σ = 1 := by
      calc σ ^ 2 * σ = σ ^ 3 := by group
        _ = 1 := hσ3
    exact eq_inv_of_mul_eq_one_left h2
  have hnσ : n * σ * n⁻¹ ∈ Subgroup.zpowers σ :=
    (Subgroup.mem_normalizer_iff.mp hn σ).mp (Subgroup.mem_zpowers σ)
  have hord : orderOf (n * σ * n⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hσ]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnσ
  have hkmod : n * σ * n⁻¹ = σ ^ (k % (3 : ℤ)) := by
    rw [← hk]
    exact zpow_eq_zpow_emod' k hσ3
  have hk3 : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by
    have h0 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
    have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hk3 with h | h | h
  · rw [h, zpow_zero] at hkmod
    rw [hkmod, orderOf_one] at hord
    norm_num at hord
  · left
    rwa [h, zpow_one] at hkmod
  · right
    rw [h] at hkmod
    have hσ2z : σ ^ (2 : ℤ) = σ⁻¹ := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact hσ2
    exact hkmod.trans hσ2z

omit
  hN in
private theorem mem_centerIn_J_fixed_eq_one_or_z (h : Tim79a.ParrottHyp z) {z₁ y e : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hyH : y ∈ H z) (hy : y ∉ Subgroup.centralizer ({z₁} : Set G))
    (he : e ∈ centerIn (J z)) (hfix : y * e * y⁻¹ = e) :
    e = 1 ∨ e = z := by
  have hyz₁ : y * z₁ * y⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hyH hy
  have hzne1 : z ≠ 1 := by
    intro hz
    have h2 : orderOf z = 2 := h.1
    rw [hz, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hzsq : z * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at h2
  have hyz : y * z * y⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hyH, mul_inv_cancel_right]
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    apply hzne1
    have heq : z₁ = z * z₁ := by
      calc z₁ = e := h1.symm
        _ = y * e * y⁻¹ := hfix.symm
        _ = y * z₁ * y⁻¹ := by rw [h1]
        _ = z * z₁ := hyz₁
    calc z = (z * z₁) * z₁⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = z₁ * z₁⁻¹ := by rw [← heq]
      _ = 1 := mul_inv_cancel z₁
  · exfalso
    apply hzne1
    have hconj : y * (z * z₁) * y⁻¹ = z₁ := by
      calc y * (z * z₁) * y⁻¹ = (y * z * y⁻¹) * (y * z₁ * y⁻¹) := by group
        _ = z * (z * z₁) := by rw [hyz, hyz₁]
        _ = z₁ := by rw [← mul_assoc, hzsq, one_mul]
    have heq : z * z₁ = z₁ := by
      calc z * z₁ = e := h1.symm
        _ = y * e * y⁻¹ := hfix.symm
        _ = y * (z * z₁) * y⁻¹ := by rw [h1]
        _ = z₁ := hconj
    calc z = (z * z₁) * z₁⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = z₁ * z₁⁻¹ := by rw [heq]
      _ = 1 := mul_inv_cancel z₁

theorem qH_eq_t_of_mem_of_map_eq {T₁ : Subgroup G}
    (hmap : (T₁.subgroupOf (H z)).map (qH D) = Subgroup.closure
      ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup))
    {x : ↥(H z)} (hxT : (x : G) ∈ T₁) (hx2 : (x : G) * (x : G) = 1) (hxJ : (x : G) ∉ J z) :
    qH D x = (⟨t, t_mem_A⟩ : QA45.originalSubgroup) := by
  classical
  let a2A : QA45.originalSubgroup := ⟨alpha2, alpha2_mem_A⟩
  let b2A : QA45.originalSubgroup := ⟨beta2, beta2_mem_A⟩
  let tA : QA45.originalSubgroup := ⟨t, t_mem_A⟩
  let A : Subgroup QA45.originalSubgroup := Subgroup.closure ({a2A, b2A} : Set QA45.originalSubgroup)
  have hqxA : qH D x ∈ A := by
    change qH D x ∈ Subgroup.closure
      ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup)
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hxT, rfl⟩
  have htA : tA ∈ A := by
    have h1 : a2A ∈ A := Subgroup.subset_closure (by simp [a2A, b2A])
    have h2 : a2A * a2A ∈ A := Subgroup.mul_mem _ h1 h1
    have h3 : a2A * a2A = tA := Subtype.ext alpha2_sq
    rwa [h3] at h2
  obtain ⟨e⟩ := qa45_sigma_centralizer_sylow.1.2.2
  have hsq : ∀ q : QuaternionGroup 2, q * q = 1 → q ≠ 1 → q = QuaternionGroup.a 2 := by decide
  have hx2H : x * x = 1 := Subtype.ext (by simpa using hx2)
  have hqxsq : (⟨qH D x, hqxA⟩ : ↥A) * ⟨qH D x, hqxA⟩ = 1 := by
    apply Subtype.ext
    show qH D x * qH D x = 1
    have h := congrArg (qH D) hx2H
    simpa using h
  have hqx : e ⟨qH D x, hqxA⟩ = QuaternionGroup.a 2 := by
    refine hsq _ ?_ ?_
    · rw [← map_mul, hqxsq, map_one]
    · intro h1
      have h2 : (⟨qH D x, hqxA⟩ : ↥A) = 1 := e.injective (by rw [h1, map_one])
      have hq1 : qH D x = 1 := by simpa using congrArg Subtype.val h2
      exact hxJ (by
        have hmem : x ∈ (J z).subgroupOf (H z) := (J_mem_iff D x).mpr hq1
        simpa using Subgroup.mem_subgroupOf.mp hmem)
  have htAsq : (⟨tA, htA⟩ : ↥A) * ⟨tA, htA⟩ = 1 := by
    apply Subtype.ext
    show tA * tA = 1
    exact Subtype.ext t_sq
  have htx : e ⟨tA, htA⟩ = QuaternionGroup.a 2 := by
    refine hsq _ ?_ ?_
    · rw [← map_mul, htAsq, map_one]
    · intro h1
      have h2 : (⟨tA, htA⟩ : ↥A) = 1 := by
        apply e.injective
        rw [h1, map_one]
      exact t_ne_one (by simpa [tA] using congrArg Subtype.val h2)
  have heq : (⟨qH D x, hqxA⟩ : ↥A) = ⟨tA, htA⟩ := e.injective (hqx.trans htx.symm)
  exact congrArg Subtype.val heq

theorem mem_centerIn_J_of_mem_centerIn_of_mem_J (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    {x : G} (hx : x ∈ centerIn T₁) (hxJ : x ∈ J z) : x ∈ centerIn (J z) := by
  classical
  have hxN : x ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxJ, (Subgroup.mem_inf.mp (hT₁.le hx.1)).2⟩
  have hxcent : x ∈ Subgroup.centralizer
      ((J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) : Set G)) :=
    Subgroup.centralizer_le (J_inf_centralizer_le_of_isSylowOf h hT₁) hx.2
  have hx' : x ∈ centerIn
      (J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) :=
    Subgroup.mem_inf.mpr ⟨hxN, hxcent⟩
  rwa [centerIn_J_inf_centralizer_sigma1Nine_eq (z := z) D h] at hx'

theorem exists_mem_centerIn_not_mem_J_of_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    ∃ x ∈ centerIn T₁, x ∉ J z := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : centerIn T₁ ≤ centerIn (J z) := fun x hx =>
    mem_centerIn_J_of_mem_centerIn_of_mem_J (z := z) D h hT₁ hx (hcon x hx)
  have hle' : centerIn (J z) ≤ centerIn T₁ :=
    centerIn_J_le_centerIn_of_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁
  have heq : centerIn T₁ = centerIn (J z) := le_antisymm hle hle'
  have h8 := card_centerIn_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁
  rw [heq, card_centerIn_J h] at h8
  exact absurd h8 (by norm_num)

theorem exists_isSylowOf_normalizer_sigma1Nine_not_le_centralizer_z1 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    ∃ S₀ : Subgroup G,
      IsSylowOf 2 S₀
        (H z ⊓ normalizer (zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) : Set G)) ∧
      T₁ ≤ S₀ ∧ ∃ y ∈ S₀, y ∉ centralizer ({z₁} : Set G) := by
  classical
  set σ₁ : G := ((sigma1Nine (z := z) D : ↥(H z)) : G) with hσ₁def
  set N₁ : Subgroup G := H z ⊓ Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G) with hN₁def
  have hm : qH D (vH D * sigma1Nine (z := z) D * (vH D)⁻¹) =
      (qH D (sigma1Nine (z := z) D))⁻¹ := by
    rw [map_mul, map_mul, map_inv, qH_vH, qH_sigma1Nine]
    apply Subtype.ext
    exact sigma1_conj_v
  have hm3 : orderOf (vH D * sigma1Nine (z := z) D * (vH D)⁻¹) = 3 := by
    rw [show vH D * sigma1Nine (z := z) D * (vH D)⁻¹ =
      MulAut.conj (vH D) (sigma1Nine (z := z) D) by rw [MulAut.conj_apply]]
    exact (MulEquiv.orderOf_eq (MulAut.conj (vH D)) (sigma1Nine (z := z) D)).trans
      (sigma1Nine_order (z := z) D)
  have hcos : (sigma1Nine (z := z) D)⁻¹ *
      (vH D * sigma1Nine (z := z) D * (vH D)⁻¹)⁻¹ ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D]
    rw [map_mul, map_inv, map_inv, hm]
    group
  obtain ⟨j, hjN, hj⟩ := exists_conj_of_order_three_of_mul_inv_mem
    (isPGroup_J_subgroupOf (z := z))
    (by rw [orderOf_inv, sigma1Nine_order (z := z) D]) hm3 hcos
  have hwconjH : (j * vH D) * sigma1Nine (z := z) D * (j * vH D)⁻¹ =
      (sigma1Nine (z := z) D)⁻¹ := by
    calc (j * vH D) * sigma1Nine (z := z) D * (j * vH D)⁻¹
        = j * (vH D * sigma1Nine (z := z) D * (vH D)⁻¹) * j⁻¹ := by group
      _ = (sigma1Nine (z := z) D)⁻¹ := hj
  have hwH : (((j * vH D : ↥(H z)) : G)) ∈ H z := (j * vH D).2
  have hwconj : (((j * vH D : ↥(H z)) : G)) * σ₁ * (((j * vH D : ↥(H z)) : G))⁻¹ = σ₁⁻¹ := by
    have hval := congrArg (fun x : ↥(H z) => (x : G)) hwconjH
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, hσ₁def] using hval
  have hwq : qH D (j * vH D) = (⟨v, v_mem_A⟩ : QA45.originalSubgroup) := by
    rw [map_mul, (J_mem_iff D j).mp hjN, one_mul, qH_vH]
  have hwN : (((j * vH D : ↥(H z)) : G)) ∈ N₁ := by
    refine Subgroup.mem_inf.mpr ⟨hwH, ?_⟩
    rw [mem_normalizer_zpowers_iff]
    rw [hwconj]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers σ₁)
  have hwNotC : (((j * vH D : ↥(H z)) : G)) ∉ Subgroup.centralizer ({z₁} : Set G) := by
    intro hmem
    have hqP := (mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord
      (j * vH D)).mp hmem
    rw [hwq] at hqP
    exact qH_vH_not_mem_Q (z := z) D (by simpa [qH_vH] using hqP)
  have hT₁N : T₁ ≤ N₁ := by
    intro t ht
    have htC : t * σ₁ * t⁻¹ = σ₁ := by
      have hcomm : t * σ₁ = σ₁ * t :=
        Subgroup.mem_centralizer_singleton_iff.mp
          ((Subgroup.mem_inf.mp (hT₁.le ht)).2)
      rw [hcomm, mul_inv_cancel_right]
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hT₁.le ht)).1, ?_⟩
    rw [mem_normalizer_zpowers_iff, htC]
    exact Subgroup.mem_zpowers σ₁
  set K : Subgroup G := N₁ ⊓ Subgroup.centralizer ({z₁} : Set G) with hKdef
  have hwK : (((j * vH D : ↥(H z)) : G)) ∉ K := by
    intro hmem
    exact hwNotC (Subgroup.mem_inf.mp hmem).2
  have hrelK : K.relIndex N₁ = 2 := by
    refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
      ⟨(((j * vH D : ↥(H z)) : G)), hwN, hwK, ?_⟩
    intro b hbN
    by_cases hbK : b ∈ K
    · exact Or.inr hbK
    · left
      have hbH : b ∈ H z := (Subgroup.mem_inf.mp hbN).1
      have hbNotC : b ∉ Subgroup.centralizer ({z₁} : Set G) := fun hc =>
        hbK (Subgroup.mem_inf.mpr ⟨hbN, hc⟩)
      have hbconj : b * z₁ * b⁻¹ = z * z₁ :=
        conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hbH hbNotC
      have hbz : b * z * b⁻¹ = z := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hbH, mul_inv_cancel_right]
      have hwconj_z₁ : (((j * vH D : ↥(H z)) : G)) * z₁ *
          (((j * vH D : ↥(H z)) : G))⁻¹ = z * z₁ :=
        conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hwH hwNotC
      have hzsq : z * z = 1 := by
        have h2 := pow_orderOf_eq_one z
        rwa [h.1, pow_two] at h2
      have hconj : (b * (((j * vH D : ↥(H z)) : G))) * z₁ *
          (b * (((j * vH D : ↥(H z)) : G)))⁻¹ = z₁ := by
        calc (b * (((j * vH D : ↥(H z)) : G))) * z₁ *
              (b * (((j * vH D : ↥(H z)) : G)))⁻¹
            = b * (((((j * vH D : ↥(H z)) : G))) * z₁ *
              ((((j * vH D : ↥(H z)) : G)))⁻¹) * b⁻¹ := by group
          _ = b * (z * z₁) * b⁻¹ := by rw [hwconj_z₁]
          _ = (b * z * b⁻¹) * (b * z₁ * b⁻¹) := by group
          _ = z * (z * z₁) := by rw [hbz, hbconj]
          _ = z₁ := by rw [← mul_assoc, hzsq, one_mul]
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hbN hwN, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc b * (((j * vH D : ↥(H z)) : G)) * z₁
            = ((b * (((j * vH D : ↥(H z)) : G))) * z₁ *
                (b * (((j * vH D : ↥(H z)) : G)))⁻¹) *
                (b * (((j * vH D : ↥(H z)) : G))) := by group
          _ = z₁ * (b * (((j * vH D : ↥(H z)) : G))) := by rw [hconj])
  obtain ⟨S₀, hS₀, hTS⟩ := exists_isSylowOf_le_of_isPGroup (p := 2)
    (P := T₁) (K := N₁) hT₁.isPGroup hT₁N
  refine ⟨S₀, hS₀, hTS, ?_⟩
  by_contra hcon
  push Not at hcon
  have hS₀K : S₀ ≤ K := fun s hs => Subgroup.mem_inf.mpr ⟨hS₀.le hs, hcon s hs⟩
  have hdvd : ¬ 2 ∣ S₀.relIndex N₁ := (isSylowOf_iff.mp hS₀).2.2
  have hmul := Subgroup.relIndex_mul_relIndex (H := S₀) (K := K) (L := N₁) hS₀K
    (inf_le_left)
  exact hdvd ⟨S₀.relIndex K, by rw [← hmul, hrelK, mul_comm]⟩

theorem exists_mem_centerIn_forall_mem_centerIn_eq (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {T₁ S₀ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    (hmap : (T₁.subgroupOf (H z)).map (qH D) = Subgroup.closure
      ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup))
    (hS₀ : IsSylowOf 2 S₀
      (H z ⊓ normalizer (zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) : Set G)))
    (hTS : T₁ ≤ S₀) {y : G} (hyS : y ∈ S₀) (hy : y ∉ centralizer ({z₁} : Set G)) :
    ∃ t ∈ centerIn T₁, t ∉ J z ∧
      ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = t * z₁ ∨ e = t * z₁ * z := by
  classical
  set σ₁ : G := ((sigma1Nine (z := z) D : ↥(H z)) : G) with hσ₁def
  have hσ₁ : orderOf σ₁ = 3 := by
    rw [hσ₁def]
    exact (Subgroup.orderOf_coe (sigma1Nine (z := z) D)).trans
      (sigma1Nine_order (z := z) D)
  have hT₁H : T₁ ≤ H z := hT₁.le.trans inf_le_left
  have hT₁Cσ : T₁ ≤ Subgroup.centralizer ({σ₁} : Set G) :=
    hT₁.le.trans inf_le_right
  have hS₀H : S₀ ≤ H z := hS₀.le.trans inf_le_left
  have hS₀N : S₀ ≤ Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G) :=
    hS₀.le.trans inf_le_right
  have hZJT : centerIn (J z) ≤ centerIn T₁ :=
    centerIn_J_le_centerIn_of_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁
  have hz₁cT₁ : z₁ ∈ centerIn T₁ := hZJT hz₁
  have hzcT₁ : z ∈ centerIn T₁ := hZJT (z_mem_centerIn_J h)
  have hz₁T₁ : z₁ ∈ T₁ := hz₁cT₁.1
  have hz₁S₀ : z₁ ∈ S₀ := hTS hz₁T₁
  have hz₁sq : z₁ * z₁ = 1 := by
    have h2 := pow_orderOf_eq_one z₁
    rwa [hord, pow_two] at h2
  have hT₁Cz₁ : T₁ ≤ Subgroup.centralizer ({z₁} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz₁cT₁.2 g hg)
  have hSC_eq : S₀ ⊓ Subgroup.centralizer ({σ₁} : Set G) = T₁ := by
    refine hT₁.eq_of_le ?_ ?_ ?_
    · intro t ht
      exact Subgroup.mem_inf.mpr ⟨hTS ht, (Subgroup.mem_inf.mp (hT₁.le ht)).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hS₀H hx.1, hx.2⟩
    · exact hS₀.isPGroup.to_inf_left
  have hmem_T₁_of_mem_S₀_of_mem_centralizer :
      ∀ a ∈ S₀, a ∈ Subgroup.centralizer ({σ₁} : Set G) → a ∈ T₁ := by
    intro a haS haC
    rw [← hSC_eq]
    exact Subgroup.mem_inf.mpr ⟨haS, haC⟩
  have hconj_y : y * σ₁ * y⁻¹ = σ₁⁻¹ := by
    rcases conj_eq_or_inv_of_mem_normalizer_zpowers hσ₁ (hS₀N hyS) with hfix | hinv
    · exfalso
      have hyT : y ∈ T₁ := hmem_T₁_of_mem_S₀_of_mem_centralizer y hyS
        (Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc y * σ₁ = (y * σ₁ * y⁻¹) * y := by group
            _ = σ₁ * y := by rw [hfix]))
      exact hy (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz₁cT₁.2 y hyT))
    · exact hinv
  have hmem_T₁_of_mem_S₀_of_mem_centralizer_z₁ :
      ∀ a ∈ S₀, a ∈ Subgroup.centralizer ({z₁} : Set G) → a ∈ T₁ := by
    intro a haS haC
    rcases conj_eq_or_inv_of_mem_normalizer_zpowers hσ₁ (hS₀N haS) with hfix | hinv
    · exact hmem_T₁_of_mem_S₀_of_mem_centralizer a haS
        (Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc a * σ₁ = (a * σ₁ * a⁻¹) * a := by group
            _ = σ₁ * a := by rw [hfix]))
    · exfalso
      have hyinv_conj : y⁻¹ * σ₁⁻¹ * y = σ₁ := by
        have h := congrArg (fun t => y⁻¹ * t * y) hconj_y
        have hL : y⁻¹ * (y * σ₁ * y⁻¹) * y = σ₁ := by group
        rw [hL] at h
        exact h.symm
      have hcS : y⁻¹ * a ∈ S₀ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) haS
      have hc_conj : (y⁻¹ * a) * σ₁ * (y⁻¹ * a)⁻¹ = σ₁ := by
        calc (y⁻¹ * a) * σ₁ * (y⁻¹ * a)⁻¹ = y⁻¹ * (a * σ₁ * a⁻¹) * y := by group
          _ = y⁻¹ * σ₁⁻¹ * y := by rw [hinv]
          _ = σ₁ := hyinv_conj
      have hcσ : y⁻¹ * a ∈ Subgroup.centralizer ({σ₁} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (y⁻¹ * a) * σ₁ = ((y⁻¹ * a) * σ₁ * (y⁻¹ * a)⁻¹) * (y⁻¹ * a) := by group
          _ = σ₁ * (y⁻¹ * a) := by rw [hc_conj]
      have hcT : y⁻¹ * a ∈ T₁ := hmem_T₁_of_mem_S₀_of_mem_centralizer _ hcS hcσ
      have hcCz₁ : y⁻¹ * a ∈ Subgroup.centralizer ({z₁} : Set G) := hT₁Cz₁ hcT
      have hprod : y = a * (y⁻¹ * a)⁻¹ := by group
      have hyC : y ∈ Subgroup.centralizer ({z₁} : Set G) := by
        rw [hprod]
        exact Subgroup.mul_mem _ haC (Subgroup.inv_mem _ hcCz₁)
      exact hy hyC
  have hcenter_S₀_le_T₁ : centerIn S₀ ≤ T₁ := by
    intro e he
    exact hmem_T₁_of_mem_S₀_of_mem_centralizer_z₁ e he.1
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp he.2 z₁ hz₁S₀).symm)
  have hcenter_S₀_le_centerIn_T₁ : centerIn S₀ ≤ centerIn T₁ := by
    intro e he
    exact Subgroup.mem_inf.mpr ⟨hcenter_S₀_le_T₁ he, Subgroup.centralizer_le hTS he.2⟩
  have hcenter_comm_y : ∀ e ∈ centerIn S₀, e * y = y * e := by
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp he.2 y hyS).symm
  have hconj_mem_T₁ : ∀ a ∈ S₀, ∀ g ∈ T₁, a * g * a⁻¹ ∈ T₁ := by
    intro a haS g hgT
    have hgCσ : g * σ₁ = σ₁ * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT₁Cσ hgT)
    have hgCσinv : g * σ₁⁻¹ = σ₁⁻¹ * g := by
      have hgconj : g * σ₁ * g⁻¹ = σ₁ := by rw [hgCσ, mul_inv_cancel_right]
      have hgconjinv : g * σ₁⁻¹ * g⁻¹ = σ₁⁻¹ := by
        calc g * σ₁⁻¹ * g⁻¹ = (g * σ₁ * g⁻¹)⁻¹ := by group
          _ = σ₁⁻¹ := by rw [hgconj]
      calc g * σ₁⁻¹ = (g * σ₁⁻¹ * g⁻¹) * g := by group
        _ = σ₁⁻¹ * g := by rw [hgconjinv]
    have hcomm : (a * g * a⁻¹) * σ₁ = σ₁ * (a * g * a⁻¹) := by
      rcases conj_eq_or_inv_of_mem_normalizer_zpowers hσ₁ (hS₀N haS) with hfix | hinv
      · have hconjA : a⁻¹ * σ₁ * a = σ₁ := by
          calc a⁻¹ * σ₁ * a = a⁻¹ * (a * σ₁ * a⁻¹) * a := by rw [hfix]
            _ = σ₁ := by group
        have hca : a * σ₁ = σ₁ * a := by
          calc a * σ₁ = (a * σ₁ * a⁻¹) * a := by group
            _ = σ₁ * a := by rw [hfix]
        calc (a * g * a⁻¹) * σ₁ = a * g * (a⁻¹ * σ₁ * a) * a⁻¹ := by group
          _ = a * g * σ₁ * a⁻¹ := by rw [hconjA]
          _ = a * (g * σ₁) * a⁻¹ := by group
          _ = a * (σ₁ * g) * a⁻¹ := by rw [hgCσ]
          _ = (a * σ₁) * (g * a⁻¹) := by group
          _ = σ₁ * (a * g * a⁻¹) := by rw [hca]; group
      · have hconjA : a⁻¹ * σ₁ * a = σ₁⁻¹ := by
          have h := congrArg (fun t => a⁻¹ * t * a) hinv
          have hL : a⁻¹ * (a * σ₁ * a⁻¹) * a = σ₁ := by group
          rw [hL] at h
          calc a⁻¹ * σ₁ * a = (a⁻¹ * σ₁⁻¹ * a)⁻¹ := by group
            _ = σ₁⁻¹ := by rw [h.symm]
        have hconjA' : a * σ₁⁻¹ * a⁻¹ = σ₁ := by
          calc a * σ₁⁻¹ * a⁻¹ = (a * σ₁ * a⁻¹)⁻¹ := by group
            _ = σ₁ := by rw [hinv, inv_inv]
        calc (a * g * a⁻¹) * σ₁ = a * g * (a⁻¹ * σ₁ * a) * a⁻¹ := by group
          _ = a * g * σ₁⁻¹ * a⁻¹ := by rw [hconjA]
          _ = a * (g * σ₁⁻¹) * a⁻¹ := by group
          _ = a * (σ₁⁻¹ * g) * a⁻¹ := by rw [hgCσinv]
          _ = (a * σ₁⁻¹ * a⁻¹) * (a * g * a⁻¹) := by group
          _ = σ₁ * (a * g * a⁻¹) := by rw [hconjA']
    exact hmem_T₁_of_mem_S₀_of_mem_centralizer (a * g * a⁻¹)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ haS (hTS hgT)) (Subgroup.inv_mem _ haS))
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have hy2T₁ : y * y ∈ T₁ := by
    have hy2S : y * y ∈ S₀ := Subgroup.mul_mem _ hyS hyS
    have hyinvconj : y * σ₁⁻¹ * y⁻¹ = σ₁ := by
      calc y * σ₁⁻¹ * y⁻¹ = (y * σ₁ * y⁻¹)⁻¹ := by group
        _ = σ₁ := by rw [hconj_y, inv_inv]
    have hyσmul : y * σ₁ = σ₁⁻¹ * y := by
      calc y * σ₁ = (y * σ₁ * y⁻¹) * y := by group
        _ = σ₁⁻¹ * y := by rw [hconj_y]
    have hyσinvmul : y * σ₁⁻¹ = σ₁ * y := by
      calc y * σ₁⁻¹ = (y * σ₁⁻¹ * y⁻¹) * y := by group
        _ = σ₁ * y := by rw [hyinvconj]
    have hcomm : (y * y) * σ₁ = σ₁ * (y * y) := by
      calc (y * y) * σ₁ = y * (y * σ₁) := by group
        _ = y * (σ₁⁻¹ * y) := by rw [hyσmul]
        _ = (y * σ₁⁻¹) * y := by group
        _ = (σ₁ * y) * y := by rw [hyσinvmul]
        _ = σ₁ * (y * y) := by group
    exact hmem_T₁_of_mem_S₀_of_mem_centralizer (y * y) hy2S
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  obtain ⟨t₀, ht₀cT₁, ht₀J⟩ :=
    exists_mem_centerIn_not_mem_J_of_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁
  have ht₀sq : t₀ * t₀ = 1 :=
    mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁ t₀ ht₀cT₁
  have ht₀T₁ : t₀ ∈ T₁ := ht₀cT₁.1
  have ht₀H : t₀ ∈ H z := hT₁H ht₀T₁
  have ht₀inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀sq
  have hq_centerIn : ∀ (x : G) (hxT : x ∈ T₁), x ∈ centerIn T₁ → x ∉ J z →
      qH D ⟨x, hT₁H hxT⟩ = (⟨t, t_mem_A⟩ : QA45.originalSubgroup) := by
    intro x hxT hxc hxJ
    exact qH_eq_t_of_mem_of_map_eq (z := z) D hmap hxT
      (mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁ x hxc)
      hxJ
  have hyt₀T₁ : y * t₀ * y⁻¹ ∈ T₁ := hconj_mem_T₁ y hyS t₀ ht₀T₁
  have hyt₀cent : y * t₀ * y⁻¹ ∈ Subgroup.centralizer (T₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgy : y⁻¹ * g * y ∈ T₁ := by
      simpa using hconj_mem_T₁ y⁻¹ (Subgroup.inv_mem _ hyS) g hg
    have hcomm := Subgroup.mem_centralizer_iff.mp ht₀cT₁.2 (y⁻¹ * g * y) hgy
    calc g * (y * t₀ * y⁻¹) = y * ((y⁻¹ * g * y) * t₀) * y⁻¹ := by group
      _ = y * (t₀ * (y⁻¹ * g * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * t₀ * y⁻¹) * g := by group
  have hyt₀cT₁ : y * t₀ * y⁻¹ ∈ centerIn T₁ :=
    Subgroup.mem_inf.mpr ⟨hyt₀T₁, hyt₀cent⟩
  have hyt₀J : y * t₀ * y⁻¹ ∉ J z := by
    have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
        (J_subgroupOf_normal z)
    intro hmem
    exact ht₀J ((Subgroup.mem_normalizer_iff.mp (hHN (hS₀H hyS)) t₀).mpr hmem)
  have hqyt₀ : qH D ⟨y * t₀ * y⁻¹, hT₁H hyt₀T₁⟩ = (⟨t, t_mem_A⟩ : QA45.originalSubgroup) :=
    hq_centerIn _ hyt₀T₁ hyt₀cT₁ hyt₀J
  have hqt₀ : qH D ⟨t₀, ht₀H⟩ = (⟨t, t_mem_A⟩ : QA45.originalSubgroup) :=
    hq_centerIn t₀ ht₀T₁ ht₀cT₁ ht₀J
  set k : G := t₀⁻¹ * (y * t₀ * y⁻¹) with hkdef
  have hkcT₁ : k ∈ centerIn T₁ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ht₀cT₁) hyt₀cT₁
  have hkT₁ : k ∈ T₁ := hkcT₁.1
  have hkH : k ∈ H z := hT₁H hkT₁
  have hkq : qH D (⟨k, hkH⟩ : ↥(H z)) = 1 := by
    have hsub : (⟨k, hkH⟩ : ↥(H z)) =
        (⟨t₀, ht₀H⟩ : ↥(H z))⁻¹ * ⟨y * t₀ * y⁻¹, hT₁H hyt₀T₁⟩ := by
      apply Subtype.ext
      simp [hkdef]
    rw [hsub, map_mul, map_inv, hqt₀, hqyt₀, inv_mul_cancel]
  have hkJ : k ∈ J z := by
    have hmem : (⟨k, hkH⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z) := (J_mem_iff D _).mpr hkq
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hkcJ : k ∈ centerIn (J z) :=
    mem_centerIn_J_of_mem_centerIn_of_mem_J (z := z) D h hT₁ hkcT₁ hkJ
  have hyky : y * k * y⁻¹ = k := by
    have ha_sq : (y * t₀ * y⁻¹) * (y * t₀ * y⁻¹) = 1 := by
      calc (y * t₀ * y⁻¹) * (y * t₀ * y⁻¹) = y * (t₀ * t₀) * y⁻¹ := by group
        _ = 1 := by rw [ht₀sq]; group
    have ha_inv : (y * t₀ * y⁻¹)⁻¹ = y * t₀ * y⁻¹ := inv_eq_of_mul_eq_one_right ha_sq
    have hy2conj : (y * y) * t₀ * (y * y)⁻¹ = t₀ := by
      have hcomm := Subgroup.mem_centralizer_iff.mp ht₀cT₁.2 (y * y) hy2T₁
      rw [hcomm, mul_inv_cancel_right]
    calc y * k * y⁻¹
        = (y * t₀⁻¹ * y⁻¹) * (y * (y * t₀ * y⁻¹) * y⁻¹) := by rw [hkdef]; group
      _ = (y * t₀ * y⁻¹)⁻¹ * ((y * y) * t₀ * (y * y)⁻¹) := by group
      _ = (y * t₀ * y⁻¹)⁻¹ * t₀ := by rw [hy2conj]
      _ = (y * t₀ * y⁻¹) * t₀ := by rw [ha_inv]
      _ = t₀ * (y * t₀ * y⁻¹) :=
        Subgroup.mem_centralizer_iff.mp ht₀cT₁.2 (y * t₀ * y⁻¹) hyt₀T₁
      _ = t₀⁻¹ * (y * t₀ * y⁻¹) := by rw [ht₀inv]
      _ = k := by rw [hkdef]
  have hk_eq : k = 1 ∨ k = z :=
    mem_centerIn_J_fixed_eq_one_or_z h hz₁ hz₁z hord (hS₀H hyS) hy hkcJ hyky
  obtain ⟨t', ht'cT₁, ht'J, ht'y⟩ : ∃ t' : G, t' ∈ centerIn T₁ ∧ t' ∉ J z ∧ y * t' * y⁻¹ = t' := by
    rcases hk_eq with hkone | hkz
    · refine ⟨t₀, ht₀cT₁, ht₀J, ?_⟩
      have h1 : t₀⁻¹ * (y * t₀ * y⁻¹) = 1 := by rw [← hkdef, hkone]
      calc y * t₀ * y⁻¹ = t₀ * (t₀⁻¹ * (y * t₀ * y⁻¹)) := by group
        _ = t₀ * 1 := by rw [h1]
        _ = t₀ := mul_one t₀
    · refine ⟨t₀ * z₁, Subgroup.mul_mem _ ht₀cT₁ hz₁cT₁, ?_, ?_⟩
      · intro hmem
        have ht₀eq : t₀ = (t₀ * z₁) * z₁ := by rw [mul_assoc, hz₁sq, mul_one]
        exact ht₀J (by rw [ht₀eq]; exact Subgroup.mul_mem _ hmem hz₁.1)
      · have hk1 : y * t₀ * y⁻¹ = t₀ * z := by
          calc y * t₀ * y⁻¹ = t₀ * (t₀⁻¹ * (y * t₀ * y⁻¹)) := by group
            _ = t₀ * z := by rw [← hkdef, hkz]
        have hyz₁ : y * z₁ * y⁻¹ = z * z₁ :=
          conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord (hS₀H hyS) hy
        have hzsq : z * z = 1 := by
          have h2 := pow_orderOf_eq_one z
          rwa [h.1, pow_two] at h2
        calc y * (t₀ * z₁) * y⁻¹ = (y * t₀ * y⁻¹) * (y * z₁ * y⁻¹) := by group
          _ = (t₀ * z) * (z * z₁) := by rw [hk1, hyz₁]
          _ = t₀ * z₁ := by rw [mul_assoc, ← mul_assoc z z z₁, hzsq, one_mul]
  have ht'z₁cT₁ : t' * z₁ ∈ centerIn T₁ := Subgroup.mul_mem _ ht'cT₁ hz₁cT₁
  have ht'z₁J : t' * z₁ ∉ J z := by
    intro hmem
    apply ht'J
    have ht'eq : t' = (t' * z₁) * z₁ := by rw [mul_assoc, hz₁sq, mul_one]
    rw [ht'eq]
    exact Subgroup.mul_mem _ hmem hz₁.1
  refine ⟨t' * z₁, ht'z₁cT₁, ht'z₁J, ?_⟩
  intro e he
  have heT₁ : e ∈ centerIn T₁ := hcenter_S₀_le_centerIn_T₁ he
  have heTy : e ∈ T₁ := heT₁.1
  by_cases heJ : e ∈ J z
  · have hecJ : e ∈ centerIn (J z) :=
      mem_centerIn_J_of_mem_centerIn_of_mem_J (z := z) D h hT₁ heT₁ heJ
    have hefix : y * e * y⁻¹ = e := by
      have hcomm := Subgroup.mem_centralizer_iff.mp he.2 y hyS
      rw [hcomm, mul_inv_cancel_right]
    rcases mem_centerIn_J_fixed_eq_one_or_z h hz₁ hz₁z hord (hS₀H hyS) hy hecJ hefix with
      h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hmcT₁ : t'⁻¹ * e ∈ centerIn T₁ :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ ht'cT₁) heT₁
    have hmq : qH D (⟨t'⁻¹ * e, hT₁H hmcT₁.1⟩ : ↥(H z)) = 1 := by
      have h1 : qH D (⟨t', hT₁H ht'cT₁.1⟩ : ↥(H z)) =
          (⟨t, t_mem_A⟩ : QA45.originalSubgroup) := hq_centerIn t' ht'cT₁.1 ht'cT₁ ht'J
      have h2 : qH D (⟨e, hT₁H heTy⟩ : ↥(H z)) =
          (⟨t, t_mem_A⟩ : QA45.originalSubgroup) := hq_centerIn e heTy heT₁ heJ
      have hsub : (⟨t'⁻¹ * e, hT₁H hmcT₁.1⟩ : ↥(H z)) =
          (⟨t', hT₁H ht'cT₁.1⟩ : ↥(H z))⁻¹ * ⟨e, hT₁H heTy⟩ := by
        apply Subtype.ext
        simp
      rw [hsub, map_mul, map_inv, h1, h2, inv_mul_cancel]
    have hmJ : t'⁻¹ * e ∈ J z := by
      have hmem : (⟨t'⁻¹ * e, hT₁H hmcT₁.1⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z) :=
        (J_mem_iff D _).mpr hmq
      simpa using Subgroup.mem_subgroupOf.mp hmem
    have hmcJ : t'⁻¹ * e ∈ centerIn (J z) :=
      mem_centerIn_J_of_mem_centerIn_of_mem_J (z := z) D h hT₁ hmcT₁ hmJ
    have hefix : y * e * y⁻¹ = e := by
      have hcomm := Subgroup.mem_centralizer_iff.mp he.2 y hyS
      rw [hcomm, mul_inv_cancel_right]
    have hmfix : y * (t'⁻¹ * e) * y⁻¹ = t'⁻¹ * e := by
      calc y * (t'⁻¹ * e) * y⁻¹ = (y * t' * y⁻¹)⁻¹ * (y * e * y⁻¹) := by group
        _ = t'⁻¹ * e := by rw [ht'y, hefix]
    rcases mem_centerIn_J_fixed_eq_one_or_z h hz₁ hz₁z hord (hS₀H hyS) hy hmcJ hmfix with
      h1 | h1
    · have heq : e = t' := by
        calc e = t' * (t'⁻¹ * e) := by group
          _ = t' * 1 := by rw [h1]
          _ = t' := mul_one t'
      exact Or.inr (Or.inr (Or.inl (by
        calc e = t' := heq
          _ = (t' * z₁) * z₁ := by
            rw [show (t' * z₁) * z₁ = t' by rw [mul_assoc, hz₁sq, mul_one]])))
    · have heq : e = t' * z := by
        calc e = t' * (t'⁻¹ * e) := by group
          _ = t' * z := by rw [h1]
      exact Or.inr (Or.inr (Or.inr (by
        calc e = t' * z := heq
          _ = ((t' * z₁) * z₁) * z := by
            rw [show (t' * z₁) * z₁ = t' by rw [mul_assoc, hz₁sq, mul_one]])))

theorem mul_z1_mem_centerIn_of_forall_mem_centerIn_eq (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {T₁ S₀ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    (hmap : (T₁.subgroupOf (H z)).map (qH D) = Subgroup.closure
      ({⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set QA45.originalSubgroup))
    (hS₀ : IsSylowOf 2 S₀
      (H z ⊓ normalizer (zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) : Set G)))
    (hTS : T₁ ≤ S₀) {y : G} (hyS : y ∈ S₀) (hy : y ∉ centralizer ({z₁} : Set G))
    {t : G} (htT : t ∈ centerIn T₁) (htJ : t ∉ J z)
    (hZS : ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = t * z₁ ∨ e = t * z₁ * z) :
    t * z₁ ∈ centerIn S₀ := by
  classical
  set σ₁ : G := ((sigma1Nine (z := z) D : ↥(H z)) : G) with hσ₁def
  have hσ₁ : orderOf σ₁ = 3 := by
    rw [hσ₁def]
    exact (Subgroup.orderOf_coe (sigma1Nine (z := z) D)).trans
      (sigma1Nine_order (z := z) D)
  have hT₁H : T₁ ≤ H z := hT₁.le.trans inf_le_left
  have hT₁Cσ : T₁ ≤ Subgroup.centralizer ({σ₁} : Set G) :=
    hT₁.le.trans inf_le_right
  have hS₀H : S₀ ≤ H z := hS₀.le.trans inf_le_left
  have hS₀N : S₀ ≤ Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G) :=
    hS₀.le.trans inf_le_right
  have hZJT : centerIn (J z) ≤ centerIn T₁ :=
    centerIn_J_le_centerIn_of_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁
  have hz₁cT₁ : z₁ ∈ centerIn T₁ := hZJT hz₁
  have hz₁T₁ : z₁ ∈ T₁ := hz₁cT₁.1
  have hz₁sq : z₁ * z₁ = 1 := by
    have h2 := pow_orderOf_eq_one z₁
    rwa [hord, pow_two] at h2
  have hzsq : z * z = 1 := by
    have h2 := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at h2
  have hzne1 : z ≠ 1 := by
    intro hz
    have h2 : orderOf z = 2 := h.1
    rw [hz, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hSC_eq : S₀ ⊓ Subgroup.centralizer ({σ₁} : Set G) = T₁ := by
    refine hT₁.eq_of_le ?_ ?_ ?_
    · intro t ht
      exact Subgroup.mem_inf.mpr ⟨hTS ht, (Subgroup.mem_inf.mp (hT₁.le ht)).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hS₀H hx.1, hx.2⟩
    · exact hS₀.isPGroup.to_inf_left
  have hmem_T₁_of_mem_S₀_of_mem_centralizer :
      ∀ a ∈ S₀, a ∈ Subgroup.centralizer ({σ₁} : Set G) → a ∈ T₁ := by
    intro a haS haC
    rw [← hSC_eq]
    exact Subgroup.mem_inf.mpr ⟨haS, haC⟩
  have hconj_y : y * σ₁ * y⁻¹ = σ₁⁻¹ := by
    rcases conj_eq_or_inv_of_mem_normalizer_zpowers hσ₁ (hS₀N hyS) with hfix | hinv
    · exfalso
      have hyT : y ∈ T₁ := hmem_T₁_of_mem_S₀_of_mem_centralizer y hyS
        (Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc y * σ₁ = (y * σ₁ * y⁻¹) * y := by group
            _ = σ₁ * y := by rw [hfix]))
      exact hy (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz₁cT₁.2 y hyT))
    · exact hinv
  have hyinv_conj : y⁻¹ * σ₁⁻¹ * y = σ₁ := by
    have h := congrArg (fun t => y⁻¹ * t * y) hconj_y
    have hL : y⁻¹ * (y * σ₁ * y⁻¹) * y = σ₁ := by group
    rw [hL] at h
    exact h.symm
  have hconj_mem_T₁ : ∀ a ∈ S₀, ∀ g ∈ T₁, a * g * a⁻¹ ∈ T₁ := by
    intro a haS g hgT
    have hgCσ : g * σ₁ = σ₁ * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT₁Cσ hgT)
    have hgCσinv : g * σ₁⁻¹ = σ₁⁻¹ * g := by
      have hgconj : g * σ₁ * g⁻¹ = σ₁ := by rw [hgCσ, mul_inv_cancel_right]
      have hgconjinv : g * σ₁⁻¹ * g⁻¹ = σ₁⁻¹ := by
        calc g * σ₁⁻¹ * g⁻¹ = (g * σ₁ * g⁻¹)⁻¹ := by group
          _ = σ₁⁻¹ := by rw [hgconj]
      calc g * σ₁⁻¹ = (g * σ₁⁻¹ * g⁻¹) * g := by group
        _ = σ₁⁻¹ * g := by rw [hgconjinv]
    have hcomm : (a * g * a⁻¹) * σ₁ = σ₁ * (a * g * a⁻¹) := by
      rcases conj_eq_or_inv_of_mem_normalizer_zpowers hσ₁ (hS₀N haS) with hfix | hinv
      · have hconjA : a⁻¹ * σ₁ * a = σ₁ := by
          calc a⁻¹ * σ₁ * a = a⁻¹ * (a * σ₁ * a⁻¹) * a := by rw [hfix]
            _ = σ₁ := by group
        have hca : a * σ₁ = σ₁ * a := by
          calc a * σ₁ = (a * σ₁ * a⁻¹) * a := by group
            _ = σ₁ * a := by rw [hfix]
        calc (a * g * a⁻¹) * σ₁ = a * g * (a⁻¹ * σ₁ * a) * a⁻¹ := by group
          _ = a * g * σ₁ * a⁻¹ := by rw [hconjA]
          _ = a * (g * σ₁) * a⁻¹ := by group
          _ = a * (σ₁ * g) * a⁻¹ := by rw [hgCσ]
          _ = (a * σ₁) * (g * a⁻¹) := by group
          _ = σ₁ * (a * g * a⁻¹) := by rw [hca]; group
      · have hconjA : a⁻¹ * σ₁ * a = σ₁⁻¹ := by
          have h := congrArg (fun t => a⁻¹ * t * a) hinv
          have hL : a⁻¹ * (a * σ₁ * a⁻¹) * a = σ₁ := by group
          rw [hL] at h
          calc a⁻¹ * σ₁ * a = (a⁻¹ * σ₁⁻¹ * a)⁻¹ := by group
            _ = σ₁⁻¹ := by rw [h.symm]
        have hconjA' : a * σ₁⁻¹ * a⁻¹ = σ₁ := by
          calc a * σ₁⁻¹ * a⁻¹ = (a * σ₁ * a⁻¹)⁻¹ := by group
            _ = σ₁ := by rw [hinv, inv_inv]
        calc (a * g * a⁻¹) * σ₁ = a * g * (a⁻¹ * σ₁ * a) * a⁻¹ := by group
          _ = a * g * σ₁⁻¹ * a⁻¹ := by rw [hconjA]
          _ = a * (g * σ₁⁻¹) * a⁻¹ := by group
          _ = a * (σ₁⁻¹ * g) * a⁻¹ := by rw [hgCσinv]
          _ = (a * σ₁⁻¹ * a⁻¹) * (a * g * a⁻¹) := by group
          _ = σ₁ * (a * g * a⁻¹) := by rw [hconjA']
    exact hmem_T₁_of_mem_S₀_of_mem_centralizer (a * g * a⁻¹)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ haS (hTS hgT)) (Subgroup.inv_mem _ haS))
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have hy2T₁ : y * y ∈ T₁ := by
    have hy2S : y * y ∈ S₀ := Subgroup.mul_mem _ hyS hyS
    have hyinvconj : y * σ₁⁻¹ * y⁻¹ = σ₁ := by
      calc y * σ₁⁻¹ * y⁻¹ = (y * σ₁ * y⁻¹)⁻¹ := by group
        _ = σ₁ := by rw [hconj_y, inv_inv]
    have hyσmul : y * σ₁ = σ₁⁻¹ * y := by
      calc y * σ₁ = (y * σ₁ * y⁻¹) * y := by group
        _ = σ₁⁻¹ * y := by rw [hconj_y]
    have hyσinvmul : y * σ₁⁻¹ = σ₁ * y := by
      calc y * σ₁⁻¹ = (y * σ₁⁻¹ * y⁻¹) * y := by group
        _ = σ₁ * y := by rw [hyinvconj]
    have hcomm : (y * y) * σ₁ = σ₁ * (y * y) := by
      calc (y * y) * σ₁ = y * (y * σ₁) := by group
        _ = y * (σ₁⁻¹ * y) := by rw [hyσmul]
        _ = (y * σ₁⁻¹) * y := by group
        _ = (σ₁ * y) * y := by rw [hyσinvmul]
        _ = σ₁ * (y * y) := by group
    exact hmem_T₁_of_mem_S₀_of_mem_centralizer (y * y) hy2S
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have hmem_T₁_of_mem_S₀_of_conj_inv :
      ∀ a ∈ S₀, a * σ₁ * a⁻¹ = σ₁⁻¹ → y⁻¹ * a ∈ T₁ := by
    intro a haS hinv
    have hc_conj : (y⁻¹ * a) * σ₁ * (y⁻¹ * a)⁻¹ = σ₁ := by
      calc (y⁻¹ * a) * σ₁ * (y⁻¹ * a)⁻¹ = y⁻¹ * (a * σ₁ * a⁻¹) * y := by group
        _ = y⁻¹ * σ₁⁻¹ * y := by rw [hinv]
        _ = σ₁ := hyinv_conj
    exact hmem_T₁_of_mem_S₀_of_mem_centralizer _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) haS)
      (Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc (y⁻¹ * a) * σ₁ = ((y⁻¹ * a) * σ₁ * (y⁻¹ * a)⁻¹) * (y⁻¹ * a) := by group
          _ = σ₁ * (y⁻¹ * a) := by rw [hc_conj]))
  have hcenter_of_centerIn_T₁_of_comm_y :
      ∀ e ∈ centerIn T₁, e * y = y * e → e ∈ centerIn S₀ := by
    intro e heT hey
    refine Subgroup.mem_inf.mpr ⟨hTS heT.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a haS
    rcases conj_eq_or_inv_of_mem_normalizer_zpowers hσ₁ (hS₀N haS) with hfix | hinv
    · have haT : a ∈ T₁ := hmem_T₁_of_mem_S₀_of_mem_centralizer a haS
        (Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc a * σ₁ = (a * σ₁ * a⁻¹) * a := by group
            _ = σ₁ * a := by rw [hfix]))
      exact Subgroup.mem_centralizer_iff.mp heT.2 a haT
    · have hbT : y⁻¹ * a ∈ T₁ := hmem_T₁_of_mem_S₀_of_conj_inv a haS hinv
      have hbe : (y⁻¹ * a) * e = e * (y⁻¹ * a) :=
        Subgroup.mem_centralizer_iff.mp heT.2 (y⁻¹ * a) hbT
      calc a * e = (y * (y⁻¹ * a)) * e := by group
        _ = y * ((y⁻¹ * a) * e) := by group
        _ = y * (e * (y⁻¹ * a)) := by rw [hbe]
        _ = (y * e) * (y⁻¹ * a) := by group
        _ = (e * y) * (y⁻¹ * a) := by rw [← hey]
        _ = e * a := by group
  have ht_sq : t * t = 1 :=
    mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁ t htT
  have htH : t ∈ H z := hT₁H htT.1
  let tA : QA45.originalSubgroup := ⟨CFSG.RankThree.GF2n.Parrott.t, t_mem_A⟩
  have hq_centerIn : ∀ (x : G) (hxT : x ∈ T₁), x ∈ centerIn T₁ → x ∉ J z →
      qH D ⟨x, hT₁H hxT⟩ = tA := by
    intro x hxT hxc hxJ
    exact qH_eq_t_of_mem_of_map_eq (z := z) D hmap hxT
      (mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁ x hxc)
      hxJ
  have hytT₁ : y * t * y⁻¹ ∈ T₁ := hconj_mem_T₁ y hyS t htT.1
  have hytcent : y * t * y⁻¹ ∈ Subgroup.centralizer (T₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgy : y⁻¹ * g * y ∈ T₁ := by
      simpa using hconj_mem_T₁ y⁻¹ (Subgroup.inv_mem _ hyS) g hg
    have hcomm := Subgroup.mem_centralizer_iff.mp htT.2 (y⁻¹ * g * y) hgy
    calc g * (y * t * y⁻¹) = y * ((y⁻¹ * g * y) * t) * y⁻¹ := by group
      _ = y * (t * (y⁻¹ * g * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * t * y⁻¹) * g := by group
  have hytcT₁ : y * t * y⁻¹ ∈ centerIn T₁ :=
    Subgroup.mem_inf.mpr ⟨hytT₁, hytcent⟩
  have hytJ : y * t * y⁻¹ ∉ J z := by
    have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
        (J_subgroupOf_normal z)
    intro hmem
    exact htJ ((Subgroup.mem_normalizer_iff.mp (hHN (hS₀H hyS)) t).mpr hmem)
  have hqyt : qH D ⟨y * t * y⁻¹, hT₁H hytT₁⟩ = tA :=
    hq_centerIn _ hytT₁ hytcT₁ hytJ
  have hqt : qH D ⟨t, htH⟩ = tA := hq_centerIn t htT.1 htT htJ
  set c : G := (y * t * y⁻¹) * t⁻¹ with hcdef
  have hccT₁ : c ∈ centerIn T₁ :=
    Subgroup.mul_mem _ hytcT₁ (Subgroup.inv_mem _ htT)
  have hcH : c ∈ H z := hT₁H hccT₁.1
  have hcq : qH D (⟨c, hcH⟩ : ↥(H z)) = 1 := by
    have hsub : (⟨c, hcH⟩ : ↥(H z)) =
        (⟨y * t * y⁻¹, hT₁H hytT₁⟩ : ↥(H z)) * (⟨t, htH⟩ : ↥(H z))⁻¹ := by
      apply Subtype.ext
      simp [hcdef]
    rw [hsub, map_mul, map_inv, hqyt, hqt, mul_inv_cancel]
  have hcJ : c ∈ J z := by
    have hmem : (⟨c, hcH⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z) := (J_mem_iff D _).mpr hcq
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hccJ : c ∈ centerIn (J z) :=
    mem_centerIn_J_of_mem_centerIn_of_mem_J (z := z) D h hT₁ hccT₁ hcJ
  have hyz : y * z * y⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hS₀H hyS), mul_inv_cancel_right]
  have hyz₁ : y * z₁ * y⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord (hS₀H hyS) hy
  have hzz₁ : z * z₁ = z₁ * z :=
    Subgroup.mem_centralizer_iff.mp hz₁.2 z (z_mem_J h)
  have hzt : t * z = z * t :=
    Subgroup.mem_centralizer_iff.mp (hZJT (z_mem_centerIn_J h)).2 t htT.1
  have hz₁t : t * z₁ = z₁ * t :=
    Subgroup.mem_centralizer_iff.mp hz₁cT₁.2 t htT.1
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hccJ with hc1 | hcz | hcz₁ | hczz₁
  ·
    have hyty : y * t * y⁻¹ = t := by
      calc y * t * y⁻¹ = ((y * t * y⁻¹) * t⁻¹) * t := by group
        _ = c * t := by rw [hcdef]
        _ = 1 * t := by rw [hc1]
        _ = t := one_mul t
    have hcomm : t * y = y * t := by
      calc t * y = (y * t * y⁻¹) * y := by rw [hyty]
        _ = y * t := by group
    have htcS : t ∈ centerIn S₀ := hcenter_of_centerIn_T₁_of_comm_y t htT hcomm
    exfalso
    rcases hZS t htcS with h1 | h1 | h1 | h1
    · exact htJ (h1 ▸ Subgroup.one_mem (J z))
    · exact htJ (h1 ▸ z_mem_J (z := z) h)
    · have hz₁one : z₁ = 1 := by
        have h : t * 1 = t * z₁ := by
          rw [mul_one]
          exact h1
        exact (mul_left_cancel h).symm
      exact hz₁z (hz₁one ▸ Subgroup.one_mem (Subgroup.zpowers z))
    · have hzprod : z₁ * z = 1 := by
        have h : t * 1 = t * (z₁ * z) := by
          rw [mul_one]
          calc t = t * z₁ * z := h1
            _ = t * (z₁ * z) := by group
        exact (mul_left_cancel h).symm
      have hz₁eq : z₁ = z := by
        calc z₁ = z₁ * (z * z) := by rw [hzsq, mul_one]
          _ = (z₁ * z) * z := by group
          _ = 1 * z := by rw [hzprod]
          _ = z := one_mul z
      exact hz₁z (hz₁eq ▸ Subgroup.mem_zpowers z)
  ·
    have hyty : y * t * y⁻¹ = z * t := by
      calc y * t * y⁻¹ = ((y * t * y⁻¹) * t⁻¹) * t := by group
        _ = c * t := by rw [hcdef]
        _ = z * t := by rw [hcz]
    have hconj_prod : (y * t * y⁻¹) * (y * z₁ * y⁻¹) = t * z₁ := by
      rw [hyty, hyz₁]
      calc (z * t) * (z * z₁) = z * (t * z) * z₁ := by group
        _ = z * (z * t) * z₁ := by rw [hzt]
        _ = (z * z) * (t * z₁) := by group
        _ = t * z₁ := by rw [hzsq, one_mul]
    have hcomm : (t * z₁) * y = y * (t * z₁) := by
      calc (t * z₁) * y = ((y * t * y⁻¹) * (y * z₁ * y⁻¹)) * y := by rw [hconj_prod]
        _ = y * (t * z₁) := by group
    exact hcenter_of_centerIn_T₁_of_comm_y (t * z₁)
      (Subgroup.mul_mem _ htT hz₁cT₁) hcomm
  ·
    exfalso
    have hyty : y * t * y⁻¹ = z₁ * t := by
      calc y * t * y⁻¹ = ((y * t * y⁻¹) * t⁻¹) * t := by group
        _ = c * t := by rw [hcdef]
        _ = z₁ * t := by rw [hcz₁]
    have hy2t : (y * y) * t * (y * y)⁻¹ = t := by
      have hcomm := Subgroup.mem_centralizer_iff.mp htT.2 (y * y) hy2T₁
      rw [hcomm, mul_inv_cancel_right]
    have hconj : (y * y) * t * (y * y)⁻¹ = z * t := by
      calc (y * y) * t * (y * y)⁻¹ = y * (y * t * y⁻¹) * y⁻¹ := by group
        _ = y * (z₁ * t) * y⁻¹ := by rw [hyty]
        _ = (y * z₁ * y⁻¹) * (y * t * y⁻¹) := by group
        _ = (z * z₁) * (z₁ * t) := by rw [hyz₁, hyty]
        _ = z * t := by
            calc (z * z₁) * (z₁ * t) = z * (z₁ * z₁) * t := by group
              _ = z * t := by rw [hz₁sq, mul_one]
    have hzt' : t = z * t := hy2t.symm.trans hconj
    have h1 : (1 : G) = z := by
      calc (1 : G) = t * t⁻¹ := (mul_inv_cancel t).symm
        _ = (z * t) * t⁻¹ := congrArg (fun x => x * t⁻¹) hzt'
        _ = z * (t * t⁻¹) := by rw [mul_assoc]
        _ = z * 1 := by rw [mul_inv_cancel]
        _ = z := mul_one z
    exact hzne1 h1.symm
  ·
    exfalso
    have hyty : y * t * y⁻¹ = (z * z₁) * t := by
      calc y * t * y⁻¹ = ((y * t * y⁻¹) * t⁻¹) * t := by group
        _ = c * t := by rw [hcdef]
        _ = (z * z₁) * t := by rw [hczz₁]
    have hy2t : (y * y) * t * (y * y)⁻¹ = t := by
      have hcomm := Subgroup.mem_centralizer_iff.mp htT.2 (y * y) hy2T₁
      rw [hcomm, mul_inv_cancel_right]
    have hcy_prod : y * (z * z₁) * y⁻¹ = z * (z * z₁) := by
      calc y * (z * z₁) * y⁻¹ = (y * z * y⁻¹) * (y * z₁ * y⁻¹) := by group
        _ = z * (z * z₁) := by rw [hyz, hyz₁]
    have hconj : (y * y) * t * (y * y)⁻¹ = z * t := by
      calc (y * y) * t * (y * y)⁻¹ = y * (y * t * y⁻¹) * y⁻¹ := by group
        _ = y * ((z * z₁) * t) * y⁻¹ := by rw [hyty]
        _ = (y * (z * z₁) * y⁻¹) * (y * t * y⁻¹) := by group
        _ = (z * (z * z₁)) * ((z * z₁) * t) := by rw [hcy_prod, hyty]
        _ = z * t := by
            calc (z * (z * z₁)) * ((z * z₁) * t) = z₁ * ((z * z₁) * t) := by
                  rw [show z * (z * z₁) = z₁ by rw [← mul_assoc, hzsq, one_mul]]
              _ = ((z₁ * z) * z₁) * t := by group
              _ = ((z * z₁) * z₁) * t := by rw [← hzz₁]
              _ = z * (z₁ * z₁) * t := by group
              _ = z * t := by rw [hz₁sq, mul_one]
    have hzt' : t = z * t := hy2t.symm.trans hconj
    have h1 : (1 : G) = z := by
      calc (1 : G) = t * t⁻¹ := (mul_inv_cancel t).symm
        _ = (z * t) * t⁻¹ := congrArg (fun x => x * t⁻¹) hzt'
        _ = z * (t * t⁻¹) := by rw [mul_assoc]
        _ = z * 1 := by rw [mul_inv_cancel]
        _ = z := mul_one z
    exact hzne1 h1.symm

end CFSG.RankThree.GF2n.Parrott
