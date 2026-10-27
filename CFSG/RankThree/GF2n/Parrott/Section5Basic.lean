module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42
public import CFSG.Goldschmidt75.TheoremBcN1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem conj_z1_mem_centerIn (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) {x : G} (hx : x ∈ H z) :
    x * z₁ * x⁻¹ ∈ centerIn (J z) := by
  have hHN : H z ≤ Subgroup.normalizer (centerIn (J z) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centerIn_le_H (z := z))).mp
      (centerIn_subgroupOf_normal z)
  exact (Subgroup.mem_normalizer_iff.mp (hHN hx) z₁).mp hz₁

private theorem conj_z1_eq_z1_or_mul (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {x : G} (hx : x ∈ H z) :
    x * z₁ * x⁻¹ = z₁ ∨ x * z₁ * x⁻¹ = z * z₁ := by
  have hmem := conj_z1_mem_centerIn h hz₁ hx
  have hord' : orderOf (x * z₁ * x⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]
  have hxz : x * z * x⁻¹ = z := by
    have hcomm : x * z = z * x := by
      rw [H_eq_centralizer] at hx
      exact Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [hcomm, mul_inv_cancel_right]
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hmem with h1 | h1 | h1 | h1
  · exfalso
    rw [h1, orderOf_one] at hord'
    exact absurd hord' (by norm_num)
  · exfalso
    have hz₁eqz : z₁ = z := by
      have h2 : x * z₁ * x⁻¹ = x * z * x⁻¹ := by rw [h1, hxz]
      have := congrArg (fun t => x⁻¹ * t * x) h2
      simpa [mul_assoc] using this
    exact hz₁z (hz₁eqz ▸ Subgroup.mem_zpowers z)
  · exact Or.inl h1
  · exact Or.inr h1

theorem exists_mem_H_not_mem_centralizer_z1 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    ∃ x ∈ H z, x ∉ Subgroup.centralizer ({z₁} : Set G) := by
  have hzH : z ∈ centerIn (H z) := ⟨z_mem_H, z_centralizes_H h⟩
  have hz₁_not_ZH : z₁ ∉ centerIn (H z) := by
    intro hz₁ZH
    apply hZ
    apply le_antisymm
    · intro e he
      rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact hzH
      · exact hz₁ZH
      · exact Subgroup.mul_mem _ hzH hz₁ZH
    · intro e he
      have heC : e ∈ Subgroup.centralizer (H z : Set G) := he.2
      have heJ : e ∈ Subgroup.centralizer (J z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact Subgroup.mem_centralizer_iff.mp heC j (J_le_H hj)
      rw [← centralizer_J_eq_centerIn h]
      exact ⟨he.1, heJ⟩
  have hnotC : z₁ ∉ Subgroup.centralizer (H z : Set G) := fun hC =>
    hz₁_not_ZH ⟨centerIn_le_H (z := z) hz₁, hC⟩
  rw [Subgroup.mem_centralizer_iff] at hnotC
  push Not at hnotC
  obtain ⟨x, hxH, hxne⟩ := hnotC
  exact ⟨x, hxH, fun hxC => hxne (Subgroup.mem_centralizer_singleton_iff.mp hxC)⟩

private theorem mul_mem_centralizer_z1_iff (hz2 : orderOf z = 2) {z₁ x₀ b : G}
    (hb : b ∈ H z) (hx₀ : x₀ * z₁ * x₀⁻¹ = z * z₁) :
    b * x₀ ∈ Subgroup.centralizer ({z₁} : Set G) ↔ b * z₁ * b⁻¹ = z * z₁ := by
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hbz : b * z * b⁻¹ = z := by
    have hcomm : b * z = z * b := by
      rw [H_eq_centralizer] at hb
      exact Subgroup.mem_centralizer_singleton_iff.mp hb
    rw [hcomm, mul_inv_cancel_right]
  have hconj : (b * x₀) * z₁ * (b * x₀)⁻¹ = z * (b * z₁ * b⁻¹) := by
    calc (b * x₀) * z₁ * (b * x₀)⁻¹ = b * (x₀ * z₁ * x₀⁻¹) * b⁻¹ := by group
      _ = b * (z * z₁) * b⁻¹ := by rw [hx₀]
      _ = (b * z * b⁻¹) * (b * z₁ * b⁻¹) := by group
      _ = z * (b * z₁ * b⁻¹) := by rw [hbz]
  constructor
  · intro hmem
    have hcomm : (b * x₀) * z₁ = z₁ * (b * x₀) :=
      Subgroup.mem_centralizer_singleton_iff.mp hmem
    have h1 : (b * x₀) * z₁ * (b * x₀)⁻¹ = z₁ := by
      rw [hcomm, mul_inv_cancel_right]
    have h2 : z * (b * z₁ * b⁻¹) = z₁ := by rw [← hconj, h1]
    calc b * z₁ * b⁻¹ = z * (z * (b * z₁ * b⁻¹)) := by
          rw [← mul_assoc, hzsq, one_mul]
      _ = z * z₁ := by rw [h2]
  · intro h
    have h1 : (b * x₀) * z₁ * (b * x₀)⁻¹ = z₁ := by
      rw [hconj, h]
      calc z * (z * z₁) = (z * z) * z₁ := by group
        _ = z₁ := by rw [hzsq, one_mul]
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (b * x₀) * z₁ = (b * x₀) * z₁ * (b * x₀)⁻¹ * (b * x₀) := by group
      _ = z₁ * (b * x₀) := by rw [h1]

theorem relIndex_inf_centralizer_z1 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    (H z ⊓ centralizer ({z₁} : Set G)).relIndex (H z) = 2 := by
  obtain ⟨x₀, hx₀H, hx₀C⟩ := exists_mem_H_not_mem_centralizer_z1 h hZ hz₁ hz₁z hord
  have hx₀Inf : x₀ ∉ H z ⊓ Subgroup.centralizer ({z₁} : Set G) :=
    fun hx => hx₀C hx.2
  have hx₀_conj : x₀ * z₁ * x₀⁻¹ = z * z₁ := by
    rcases conj_z1_eq_z1_or_mul h hz₁ hz₁z hord hx₀H with h | h
    · exfalso
      apply hx₀C
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x₀ * z₁ = (x₀ * z₁ * x₀⁻¹) * x₀ := by group
        _ = z₁ * x₀ := by rw [h]
    · exact h
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨x₀, hx₀H, hx₀Inf, fun b hb => ?_⟩
  by_cases hbC : b ∈ H z ⊓ Subgroup.centralizer ({z₁} : Set G)
  · exact Or.inr hbC
  · left
    refine Subgroup.mem_inf.mpr ⟨(H z).mul_mem hb hx₀H, ?_⟩
    refine (mul_mem_centralizer_z1_iff h.1 hb hx₀_conj).mpr ?_
    rcases conj_z1_eq_z1_or_mul h hz₁ hz₁z hord hb with h | h
    · exfalso
      exact hbC (Subgroup.mem_inf.mpr ⟨hb, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc b * z₁ = (b * z₁ * b⁻¹) * b := by group
          _ = z₁ * b := by rw [h]⟩)
    · exact h

theorem conj_z1_eq_of_not_mem_centralizer (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {x : G} (hx : x ∈ H z) (hxz₁ : x ∉ centralizer ({z₁} : Set G)) :
    x * z₁ * x⁻¹ = z * z₁ := by
  rcases conj_z1_eq_z1_or_mul h hz₁ hz₁z hord hx with h | h
  · exfalso
    apply hxz₁
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * z₁ = (x * z₁ * x⁻¹) * x := by group
      _ = z₁ * x := by rw [h]
  · exact h

private theorem z1_not_mem_centerIn_of_isSylowOf (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z))
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) : z₁ ∉ centerIn T := by
  intro hz₁T
  have hTC : T ≤ H z ⊓ Subgroup.centralizer ({z₁} : Set G) := by
    intro t ht
    exact Subgroup.mem_inf.mpr ⟨hT.le ht,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz₁T.2 t ht)⟩
  have hTCsylow : IsSylowOf 2 T (H z ⊓ Subgroup.centralizer ({z₁} : Set G)) :=
    hT.of_le hTC inf_le_left
  have hndvdH : ¬ 2 ∣ T.relIndex (H z) := (isSylowOf_iff.mp hT).2.2
  apply hndvdH
  rw [← Subgroup.relIndex_mul_relIndex
      (H := T) (K := H z ⊓ Subgroup.centralizer ({z₁} : Set G)) (L := H z)
      hTC inf_le_left,
    relIndex_inf_centralizer_z1 h hZ hz₁ hz₁z hord]
  exact dvd_mul_of_dvd_right (dvd_refl 2) _

private theorem centerIn_le_zpowers_of_isSylowOf (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z))
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) : centerIn T ≤ Subgroup.zpowers z := by
  have hJT : J z ≤ T := J_le_of_isSylowOf T hT
  have hzT : z ∈ T := hJT (z_mem_J h)
  have hzCT : z ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.centralizer_le hT.le (z_centralizes_H h)
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  intro x hx
  have hxH : x ∈ H z := hT.le hx.1
  have hxJ : x ∈ Subgroup.centralizer (J z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_iff.mp hx.2 j (hJT hj)
  have hxZ : x ∈ centerIn (J z) := by
    rw [← centralizer_J_eq_centerIn h]
    exact ⟨hxH, hxJ⟩
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hxZ with h1 | h1 | h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h1]
    exact Subgroup.mem_zpowers z
  · exact absurd (h1 ▸ hx) (z1_not_mem_centerIn_of_isSylowOf h hZ T hT hz₁ hz₁z hord)
  · have hz₁mem : z₁ ∈ centerIn T := by
      have hzmem : z ∈ centerIn T := ⟨hzT, hzCT⟩
      have hzzmem : z * z₁ ∈ centerIn T := h1 ▸ hx
      rw [← show z * (z * z₁) = z₁ from by rw [← mul_assoc, hzsq, one_mul]]
      exact Subgroup.mul_mem _ hzmem hzzmem
    exact absurd hz₁mem (z1_not_mem_centerIn_of_isSylowOf h hZ T hT hz₁ hz₁z hord)

theorem centerIn_eq_zpowers_of_isSylowOf (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z)) :
    centerIn T = Subgroup.zpowers z := by
  obtain ⟨z₁, hz₁sup, hz₁z, hord⟩ := exists_z1 h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hz₁sup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  refine le_antisymm (centerIn_le_zpowers_of_isSylowOf h hZ T hT hz₁ hz₁z hord) ?_
  exact Subgroup.zpowers_le.mpr
    ⟨J_le_of_isSylowOf T hT (z_mem_J h), Subgroup.centralizer_le hT.le (z_centralizes_H h)⟩

theorem normalizer_le_H_of_isSylowOf_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z)) :
    normalizer (T : Set G) ≤ H z := by
  have hJT : J z ≤ T := J_le_of_isSylowOf T hT
  have hzT : z ∈ T := hJT (z_mem_J h)
  have hzCT : z ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.centralizer_le hT.le (z_centralizes_H h)
  have hzTcenter : z ∈ centerIn T := ⟨hzT, hzCT⟩
  have hcenter : centerIn T = Subgroup.zpowers z :=
    centerIn_eq_zpowers_of_isSylowOf h hZ T hT
  intro n hn
  have hnZ : n ∈ Subgroup.normalizer (centerIn T : Set G) := by
    simpa [CFSG.centerIn, CFSG.Quasithin.centerOf] using
      (CFSG.Quasithin.H13.C23.mem_normalizer_centerOf hn)
  have hzn : n * z * n⁻¹ ∈ Subgroup.zpowers z := by
    rw [← hcenter]
    exact (Subgroup.mem_normalizer_iff.mp hnZ z).mp hzTcenter
  have hne : n * z * n⁻¹ ≠ 1 := by
    intro h1
    have hz1 : z = 1 := by
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    have hz2 : orderOf z = 2 := h.1
    rw [hz1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzn' : n * z * n⁻¹ = z := by
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hzn with h1 | h1
    · exact absurd h1 hne
    · exact h1
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc n * z = (n * z * n⁻¹) * n := by group
    _ = z * n := by rw [hzn']

theorem isSylowOf_top_of_isSylowOf_H_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z)) :
    IsSylowOf 2 T ⊤ := by
  have hT' : IsSylowOf 2 T (H z ⊓ ⊤) := by rwa [inf_top_eq]
  refine isSylowOf_of_normalizer_inf_le hT' ?_
  rw [inf_top_eq]
  exact normalizer_le_H_of_isSylowOf_of_ne h hZ T hT

theorem z_mem_of_normal_of_two_dvd (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {N : Subgroup G} (hN : N.Normal)
    (h2 : 2 ∣ Nat.card N) : z ∈ N := by
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
  have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H_of_ne h hZ T hT
  have hNTsylow : IsSylowOf 2 (N ⊓ T) N := by
    have h := hTtop.inf_of_le_normalizer (N := N) le_top
      (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hN).symm)
    simpa [inf_comm] using h
  have hQne : N ⊓ T ≠ ⊥ := by
    have hfacpos : 0 < (Nat.card N).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have hcard : Nat.card (N ⊓ T : Subgroup G) = 2 ^ (Nat.card N).factorization 2 := hNTsylow.card_eq
    have hgt : 1 < Nat.card (N ⊓ T : Subgroup G) := by
      rw [hcard]
      exact one_lt_pow' (by norm_num) (Nat.pos_iff_ne_zero.mp hfacpos)
    exact (Subgroup.nontrivial_iff_ne_bot (N ⊓ T)).mp (Finite.one_lt_card_iff_nontrivial.mp hgt)
  have hTN : T ≤ Subgroup.normalizer ((N ⊓ T : Subgroup G) : Set G) := by
    haveI : ((N ⊓ T).subgroupOf T).Normal := by
      rw [Subgroup.inf_subgroupOf_right]
      exact hN.subgroupOf T
    exact Subgroup.le_normalizer_of_normal_subgroupOf inf_le_right
  have hcenterNe : (N ⊓ T) ⊓ centerIn T ≠ ⊥ := by
    have h := CFSG.Goldschmidt75.inf_centralizer_ne_bot (p := 2) hTtop.isPGroup
      (inf_le_right : N ⊓ T ≤ T) hTN hQne
    rw [show centerIn T = T ⊓ Subgroup.centralizer (T : Set G) from rfl,
      ← inf_assoc, inf_eq_left.mpr inf_le_right]
    exact h
  have hzp : centerIn T = Subgroup.zpowers z := centerIn_eq_zpowers_of_isSylowOf h hZ T hT
  have hcenterZ : (N ⊓ T) ⊓ Subgroup.zpowers z ≠ ⊥ := by
    rwa [← hzp]
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenterZ
  have hyN : (y : G) ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp y.2).1).1
  have hyz : (y : G) ∈ Subgroup.zpowers z := (Subgroup.mem_inf.mp y.2).2
  have hyne : (y : G) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hyz with h1 | h1
  · exact absurd h1 hyne
  · rwa [h1] at hyN

end CFSG.RankThree.GF2n.Parrott
