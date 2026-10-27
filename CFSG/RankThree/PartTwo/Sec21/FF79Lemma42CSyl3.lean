module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem zpow_eq_of_dvd {x : G} (hx : x ^ 3 = 1) {i j : ℤ} (h : (3 : ℤ) ∣ i - j) :
    x ^ i = x ^ j := by
  obtain ⟨m, hm⟩ := h
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  rw [show i = j + 3 * m by omega, zpow_add, zpow_mul, h3, one_zpow, mul_one]

namespace BGen

variable {b b₁ b₂ : G} {B : Subgroup G} (hB : BGen b b₁ b₂ B)
include hB

theorem crd_mem (p : ℤ × ℤ × ℤ) : crd b b₁ b₂ p ∈ B :=
  B.mul_mem (B.mul_mem (B.zpow_mem hB.bmem.1 _) (B.zpow_mem hB.bmem.2.1 _))
    (B.zpow_mem hB.bmem.2.2 _)

theorem exists_crd (x : ↥B) : ∃ p : ℤ × ℤ × ℤ, (x : G) = crd b b₁ b₂ p := by
  obtain ⟨i, j, k, h⟩ := hB.mem x x.2
  exact ⟨(i, j, k), h⟩

theorem crd_eq_of_dvd {p q : ℤ × ℤ × ℤ}
    (h : (3 : ℤ) ∣ p.1 - q.1 ∧ (3 : ℤ) ∣ p.2.1 - q.2.1 ∧ (3 : ℤ) ∣ p.2.2 - q.2.2) :
    crd b b₁ b₂ p = crd b b₁ b₂ q := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [crd]
  rw [zpow_eq_of_dvd hB.cube.1 h1, zpow_eq_of_dvd hB.cube.2.1 h2,
    zpow_eq_of_dvd hB.cube.2.2 h3]

end BGen

section Psi

variable {b b₁ b₂ : G} {B : Subgroup G} (hB : BGen b b₁ b₂ B)
include hB

noncomputable def psiFun (x : ↥B) : Multiplicative (ZMod 3) :=
  Multiplicative.ofAdd
    ((((Classical.choose (hB.exists_crd x)).2.1 + (Classical.choose (hB.exists_crd x)).2.2 :
      ℤ)) : ZMod 3)

theorem psiFun_eq (x : ↥B) {q : ℤ × ℤ × ℤ} (hq : (x : G) = crd b b₁ b₂ q) :
    psiFun hB x = Multiplicative.ofAdd (((q.2.1 + q.2.2 : ℤ)) : ZMod 3) := by
  have hc := Classical.choose_spec (hB.exists_crd x)
  obtain ⟨h1, h2, h3⟩ := hB.crd_eq (hc.symm.trans hq)
  unfold psiFun
  congr 1
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have : (Classical.choose (hB.exists_crd x)).2.1 + (Classical.choose (hB.exists_crd x)).2.2 -
    (q.2.1 + q.2.2) = ((Classical.choose (hB.exists_crd x)).2.1 - q.2.1) +
      ((Classical.choose (hB.exists_crd x)).2.2 - q.2.2) := by ring
  rw [this]
  exact_mod_cast dvd_add h2 h3

noncomputable def psi : ↥B →* Multiplicative (ZMod 3) where
  toFun := psiFun hB
  map_one' := by
    rw [psiFun_eq hB 1 (q := (0, 0, 0)) (by simp [crd])]
    simp
  map_mul' x y := by
    obtain ⟨p, hp⟩ := hB.exists_crd x
    obtain ⟨q, hq⟩ := hB.exists_crd y
    rw [psiFun_eq hB x hp, psiFun_eq hB y hq,
      psiFun_eq hB (x * y) (q := p + q) (by
        rw [Subgroup.coe_mul, hp, hq, hB.crd_mul])]
    simp only [Prod.fst_add, Prod.snd_add]
    rw [← ofAdd_add]
    congr 1
    push_cast
    ring

theorem psi_apply (x : ↥B) {q : ℤ × ℤ × ℤ} (hq : (x : G) = crd b b₁ b₂ q) :
    psi hB x = Multiplicative.ofAdd (((q.2.1 + q.2.2 : ℤ)) : ZMod 3) := psiFun_eq hB x hq

theorem psi_b : psi hB ⟨b, hB.bmem.1⟩ = 1 := by
  rw [psi_apply hB _ (q := (1, 0, 0)) (by simp [crd])]
  simp

theorem psi_gamma : psi hB ⟨b₁ ^ 2 * b₂, B.mul_mem (B.pow_mem hB.bmem.2.1 2) hB.bmem.2.2⟩ = 1 := by
  rw [psi_apply hB _ (q := (0, 2, 1)) (by simp [crd])]
  decide

theorem psi_beta : psi hB ⟨b₁ * b₂, B.mul_mem hB.bmem.2.1 hB.bmem.2.2⟩ ≠ 1 := by
  rw [psi_apply hB _ (q := (0, 1, 1)) (by simp [crd])]
  decide

theorem psi_surjective : Function.Surjective (psi hB) := by
  intro t
  refine ⟨⟨crd b b₁ b₂ (0, (Multiplicative.toAdd t).val, 0), hB.crd_mem _⟩, ?_⟩
  rw [psi_apply hB _ (q := (0, (Multiplicative.toAdd t).val, 0)) rfl]
  simp

theorem closure_eq_ker :
    Subgroup.closure {b, b₁ ^ 2 * b₂} = (psi hB).ker.map B.subtype := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨⟨x, hB.bmem.1⟩, psi_b hB, rfl⟩
    · exact ⟨⟨_, B.mul_mem (B.pow_mem hB.bmem.2.1 2) hB.bmem.2.2⟩, psi_gamma hB, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨i, j, k⟩, hp⟩ := hB.exists_crd x
    rw [SetLike.mem_coe, MonoidHom.mem_ker, psi_apply hB x hp] at hx
    have hx' : (((j + k : ℤ)) : ZMod 3) = 0 := by
      have := congrArg Multiplicative.toAdd hx
      simpa using this
    have hd : (3 : ℤ) ∣ j + k := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hx'
    have hmem : b ^ i * (b₁ ^ 2 * b₂) ^ k ∈ Subgroup.closure {b, b₁ ^ 2 * b₂} :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    have hc : Commute b₁ b₂ := hB.comm.2.2
    have hrw : b ^ i * (b₁ ^ 2 * b₂) ^ k = crd b b₁ b₂ (i, 2 * k, k) := by
      simp only [crd]
      rw [(hc.pow_left 2).mul_zpow, ← zpow_natCast, ← zpow_mul]
      norm_num
      simp only [mul_assoc]
    have hq : crd b b₁ b₂ (i, j, k) = crd b b₁ b₂ (i, 2 * k, k) :=
      hB.crd_eq_of_dvd ⟨by simp, by simp only; omega, by simp⟩
    rw [Subgroup.coe_subtype, hp, hq, ← hrw]
    exact hmem

theorem card_closure (hcard : Nat.card B = 3 ^ 3) :
    Nat.card (Subgroup.closure {b, b₁ ^ 2 * b₂}) = 9 := by
  rw [closure_eq_ker hB, Subgroup.card_map_of_injective B.subtype_injective]
  have h := Subgroup.card_ker_mul_card_of_surjective (psi_surjective hB)
  rw [hcard] at h
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  rw [h3] at h
  omega

end Psi

section Sec4

private theorem conj_inv_eq {n x y : G} (h : n * x * n⁻¹ = y) : n⁻¹ * y * n = x := by
  rw [← h]; group

private theorem conj_mul3 (n : G) (u v w : G) (i j k : ℤ) :
    n * (u ^ i * v ^ j * w ^ k) * n⁻¹ = (n * u * n⁻¹) ^ i * (n * v * n⁻¹) ^ j *
      (n * w * n⁻¹) ^ k := by
  rw [conj_zpow, conj_zpow, conj_zpow]; group

variable {b b₁ b₂ : G} {J B : Subgroup G} (h4 : FF79Sec4 b J B b₁ b₂)
include h4

theorem psi_invariant {n : G} (hn : n ∈ Nor B) (hβ : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂)
    (x y : ↥B) (hxy : n * (x : G) * n⁻¹ = (y : G)) :
    psi (bgen_of_sec4 h4) y = psi (bgen_of_sec4 h4) x := by
  have hB := bgen_of_sec4 h4
  obtain ⟨⟨i, j, k⟩, hp⟩ := hB.exists_crd x
  obtain ⟨h1, h2⟩ := mono_fix_beta h4 hn hβ
  have hc : Commute b₁ b₂ := hB.comm.2.2
  have hx := psi_apply hB x hp
  rw [hp, crd] at hxy
  simp only at hxy
  rw [conj_mul3] at hxy
  have hb : ∃ a : ℤ, (n * b * n⁻¹) ^ i = b ^ a := by
    rcases h1 with h | h
    · exact ⟨i, by rw [h]⟩
    · exact ⟨-i, by rw [h, zpow_neg, ← inv_zpow]⟩
  obtain ⟨a, ha⟩ := hb
  rcases h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [ha, e1, e2] at hxy
    rw [psi_apply hB y (q := (a, j, k)) (by rw [← hxy]; rfl), hx]
  · rw [ha, e1, e2] at hxy
    have hy : (y : G) = crd b b₁ b₂ (a, k, j) := by
      rw [← hxy, crd]
      simp only
      rw [mul_assoc, mul_assoc, (hc.symm.zpow_zpow j k).eq]
    rw [psi_apply hB y hy, hx]
    simp only [add_comm]

theorem exists_inv_b : ∃ n : G, n ∈ Nor B ∧ n ∈ Cen (b₁ * b₂) ∧ n * b * n⁻¹ = b⁻¹ := by
  obtain ⟨n, hn, e0, e1, e2⟩ := h4.mono.2.2.2.1
  refine ⟨n, hn, ?_, e0⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.mp hh]
  have : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂ := by
    calc n * (b₁ * b₂) * n⁻¹ = (n * b₁ * n⁻¹) * (n * b₂ * n⁻¹) := by group
      _ = b₁ * b₂ := by rw [e1, e2]
  exact (mul_inv_eq_iff_eq_mul.mp this).symm

theorem exists_inv_gamma :
    ∃ t : G, t ∈ Cen (b₁ * b₂) ∧ t * (b₁ ^ 2 * b₂) * t⁻¹ = (b₁ ^ 2 * b₂)⁻¹ := by
  have hB := bgen_of_sec4 h4
  obtain ⟨a, ha, a0, a1, a2⟩ := h4.mono.2.2.2.2.1
  obtain ⟨c, hc, c0, c1, c2⟩ := h4.mono.2.2.2.2.2
  set t := c * a * c⁻¹ with ht
  have t1 : t * b₁ * t⁻¹ = b₂ := by
    calc t * b₁ * t⁻¹ = c * (a * (c⁻¹ * b₁ * c) * a⁻¹) * c⁻¹ := by rw [ht]; group
      _ = b₂ := by rw [conj_inv_eq c0, a0, c1]
  have t2 : t * b₂ * t⁻¹ = b₁ := by
    calc t * b₂ * t⁻¹ = c * (a * (c⁻¹ * b₂ * c) * a⁻¹) * c⁻¹ := by rw [ht]; group
      _ = b₁ := by rw [conj_inv_eq c1, a1, c0]
  have hβ : t * (b₁ * b₂) * t⁻¹ = b₁ * b₂ := by
    calc t * (b₁ * b₂) * t⁻¹ = (t * b₁ * t⁻¹) * (t * b₂ * t⁻¹) := by group
      _ = b₁ * b₂ := by rw [t1, t2, hB.comm.2.2]
  refine ⟨t, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (mul_inv_eq_iff_eq_mul.mp hβ).symm
  · have hg : t * (b₁ ^ 2 * b₂) * t⁻¹ = b₂ * b₂ * b₁ := by
      calc t * (b₁ ^ 2 * b₂) * t⁻¹
          = (t * b₁ * t⁻¹) * (t * b₁ * t⁻¹) * (t * b₂ * t⁻¹) := by rw [pow_two]; group
        _ = b₂ * b₂ * b₁ := by rw [t1, t2]
    rw [hg]
    refine eq_inv_of_mul_eq_one_left ?_
    obtain ⟨e1, e2, e3⟩ := hB.cube
    calc b₂ * b₂ * b₁ * (b₁ ^ 2 * b₂) = b₂ ^ 2 * b₁ ^ 3 * b₂ := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [e2, mul_one, ← pow_succ]; exact e3

end Sec4

end CFSG.RankThree.PartTwo.Sec21.FF79
