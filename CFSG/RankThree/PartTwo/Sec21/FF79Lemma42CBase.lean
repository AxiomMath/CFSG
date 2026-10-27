module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

structure BGen (b b₁ b₂ : G) (B : Subgroup G) : Prop where
  cube : b ^ 3 = 1 ∧ b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1
  comm : b * b₁ = b₁ * b ∧ b * b₂ = b₂ * b ∧ b₁ * b₂ = b₂ * b₁
  indep : ∀ i j k : ℤ, b ^ i * b₁ ^ j * b₂ ^ k = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k
  mem : ∀ x ∈ B, ∃ i j k : ℤ, x = b ^ i * b₁ ^ j * b₂ ^ k
  bmem : b ∈ B ∧ b₁ ∈ B ∧ b₂ ∈ B

private theorem zpow_mod_three {x : G} (hx : x ^ 3 = 1) (i : ℤ) : x ^ i = x ^ (i % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv i 3, zpow_add, zpow_mul]
  have : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  rw [this, one_zpow, mul_one]


private theorem zpow_eq_pow_fin {A : Type} [Group A] {y : A} (hy : y ^ 3 = 1) (i : ℤ) :
    ∃ r : Fin 3, y ^ i = y ^ (r : ℕ) ∧ ((r : ℕ) : ℤ) = i % 3 := by
  have h : (((i % 3).toNat : ℕ) : ℤ) = i % 3 := Int.toNat_of_nonneg (by omega)
  refine ⟨⟨(i % 3).toNat, by omega⟩, ?_, h⟩
  rw [zpow_mod_three hy i]
  show y ^ (i % 3) = y ^ ((i % 3).toNat)
  conv_lhs => rw [← h]
  rw [zpow_natCast]

private theorem coord_mul {A : Type} [CommGroup A] (b b₁ b₂ : A) (i j k i' j' k' : ℤ) :
    (b ^ i * b₁ ^ j * b₂ ^ k) * (b ^ i' * b₁ ^ j' * b₂ ^ k') =
      b ^ (i + i') * b₁ ^ (j + j') * b₂ ^ (k + k') := by
  simp only [zpow_add]
  ac_rfl

variable [Finite G]

theorem bgen_of_sec4 {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    BGen b b₁ b₂ B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEl, hcardB⟩ := h4.mono.1
  haveI := hEl
  have hBeq := h4.mono.2.1
  have hbB : b ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hB3 : ∀ g ∈ B, g ^ 3 = 1 := fun g hg =>
    elemPow_eq_one_of_isElementaryAbelian (A := B) g hg
  have hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hEl.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  letI : CommGroup ↥B :=
    { (inferInstance : Group ↥B) with
      mul_comm := fun x y => Subtype.ext (hcomm _ x.2 _ y.2) }
  let b' : ↥B := ⟨b, hbB⟩
  let b₁' : ↥B := ⟨b₁, hb₁B⟩
  let b₂' : ↥B := ⟨b₂, hb₂B⟩
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (hB3 b hbB)
  have hb₁'3 : b₁' ^ 3 = 1 := Subtype.ext (hB3 b₁ hb₁B)
  have hb₂'3 : b₂' ^ 3 = 1 := Subtype.ext (hB3 b₂ hb₂B)
  have hmem : ∀ x ∈ B, ∃ i j k : ℤ, x = b ^ i * b₁ ^ j * b₂ ^ k := by
    intro x hx
    rw [hBeq] at hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ i j k : ℤ, x = b ^ i * b₁ ^ j * b₂ ^ k)
      ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    · exact ⟨0, 0, 0, by simp⟩
    · rintro y z _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
      refine ⟨i + i', j + j', k + k', ?_⟩
      have := coord_mul b' b₁' b₂' i j k i' j' k'
      exact congrArg Subtype.val this
    · rintro y _ ⟨i, j, k, rfl⟩
      refine ⟨-i, -j, -k, ?_⟩
      have h0 := coord_mul b' b₁' b₂' i j k (-i) (-j) (-k)
      simp only [add_neg_cancel, zpow_zero, mul_one] at h0
      have h1 : (b' ^ i * b₁' ^ j * b₂' ^ k)⁻¹ = b' ^ (-i) * b₁' ^ (-j) * b₂' ^ (-k) :=
        inv_eq_of_mul_eq_one_right h0
      exact congrArg Subtype.val h1
  have hindep : ∀ i j k : ℤ, b ^ i * b₁ ^ j * b₂ ^ k = 1 →
      (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
    let g : Fin 3 × Fin 3 × Fin 3 → ↥B := fun p =>
      b' ^ (p.1 : ℕ) * b₁' ^ (p.2.1 : ℕ) * b₂' ^ (p.2.2 : ℕ)
    have hsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨i, j, k, rfl⟩ := hmem x hx
      obtain ⟨r1, e1, -⟩ := zpow_eq_pow_fin hb'3 i
      obtain ⟨r2, e2, -⟩ := zpow_eq_pow_fin hb₁'3 j
      obtain ⟨r3, e3, -⟩ := zpow_eq_pow_fin hb₂'3 k
      refine ⟨(r1, r2, r3), ?_⟩
      simp only [g]
      apply Subtype.ext
      show (b' ^ (r1 : ℕ) * b₁' ^ (r2 : ℕ) * b₂' ^ (r3 : ℕ) : ↥B).1 = _
      rw [← e1, ← e2, ← e3]
      rfl
    have hbij : Function.Bijective g := by
      rw [Nat.bijective_iff_surjective_and_card]
      refine ⟨hsurj, ?_⟩
      rw [Nat.card_prod, Nat.card_prod, hcardB]
      simp
    intro i j k hijk
    obtain ⟨r1, e1, f1⟩ := zpow_eq_pow_fin hb'3 i
    obtain ⟨r2, e2, f2⟩ := zpow_eq_pow_fin hb₁'3 j
    obtain ⟨r3, e3, f3⟩ := zpow_eq_pow_fin hb₂'3 k
    have hg0 : g (0, 0, 0) = 1 := by simp [g]
    have hg : g (r1, r2, r3) = g (0, 0, 0) := by
      rw [hg0]
      apply Subtype.ext
      show (b' ^ (r1 : ℕ) * b₁' ^ (r2 : ℕ) * b₂' ^ (r3 : ℕ) : ↥B).1 = 1
      rw [← e1, ← e2, ← e3]
      exact hijk
    have := hbij.1 hg
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2, h3⟩ := this
    subst h1 h2 h3
    refine ⟨?_, ?_, ?_⟩ <;> omega
  exact ⟨⟨hB3 b hbB, hB3 b₁ hb₁B, hB3 b₂ hb₂B⟩,
    ⟨hcomm _ hbB _ hb₁B, hcomm _ hbB _ hb₂B, hcomm _ hb₁B _ hb₂B⟩, hindep, hmem,
    hbB, hb₁B, hb₂B⟩


@[expose] def crd (b b₁ b₂ : G) (p : ℤ × ℤ × ℤ) : G := b ^ p.1 * b₁ ^ p.2.1 * b₂ ^ p.2.2

namespace BGen

variable {b b₁ b₂ : G} {B : Subgroup G} (hB : BGen b b₁ b₂ B)
include hB

theorem crd_mul (p q : ℤ × ℤ × ℤ) : crd b b₁ b₂ p * crd b b₁ b₂ q = crd b b₁ b₂ (p + q) := by
  obtain ⟨hb1, hb2, hb12⟩ := hB.comm
  have c1 : Commute b b₁ := hb1
  have c2 : Commute b b₂ := hb2
  have c3 : Commute b₁ b₂ := hb12
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only [crd, Prod.fst_add, Prod.snd_add, zpow_add]
  have h1 : b₂ ^ k * b ^ i' = b ^ i' * b₂ ^ k := (c2.symm.zpow_zpow k i').eq
  have h2 : b₁ ^ j * b ^ i' = b ^ i' * b₁ ^ j := (c1.symm.zpow_zpow j i').eq
  have h3 : b₂ ^ k * b₁ ^ j' = b₁ ^ j' * b₂ ^ k := (c3.symm.zpow_zpow k j').eq
  have swap : ∀ {a q : G}, a * q = q * a → ∀ y : G, a * (q * y) = q * (a * y) := by
    intro a q h y; rw [← mul_assoc, h, mul_assoc]
  calc b ^ i * b₁ ^ j * b₂ ^ k * (b ^ i' * b₁ ^ j' * b₂ ^ k')
      = b ^ i * (b₁ ^ j * (b₂ ^ k * (b ^ i' * (b₁ ^ j' * b₂ ^ k')))) := by simp only [mul_assoc]
    _ = b ^ i * (b₁ ^ j * (b ^ i' * (b₂ ^ k * (b₁ ^ j' * b₂ ^ k')))) := by
        rw [swap h1 (b₁ ^ j' * b₂ ^ k')]
    _ = b ^ i * (b₁ ^ j * (b ^ i' * (b₁ ^ j' * (b₂ ^ k * b₂ ^ k')))) := by
        rw [swap h3 (b₂ ^ k')]
    _ = b ^ i * (b ^ i' * (b₁ ^ j * (b₁ ^ j' * (b₂ ^ k * b₂ ^ k')))) := by
        rw [swap h2 (b₁ ^ j' * (b₂ ^ k * b₂ ^ k'))]
    _ = _ := by simp only [mul_assoc]

theorem crd_zero : crd b b₁ b₂ (0, 0, 0) = 1 := by simp [crd]

theorem crd_eq {p q : ℤ × ℤ × ℤ} (h : crd b b₁ b₂ p = crd b b₁ b₂ q) :
    (3 : ℤ) ∣ p.1 - q.1 ∧ (3 : ℤ) ∣ p.2.1 - q.2.1 ∧ (3 : ℤ) ∣ p.2.2 - q.2.2 := by
  have h1 : crd b b₁ b₂ q * crd b b₁ b₂ (-q) = 1 := by
    rw [hB.crd_mul, ← hB.crd_zero]; congr 1; simp; rfl
  have h2 : crd b b₁ b₂ (p + -q) = 1 := by
    rw [← hB.crd_mul, h, h1]
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  have := hB.indep (i + -i') (j + -j') (k + -k') h2
  simp only [Prod.mk_add_mk, Prod.neg_mk, crd] at h2 ⊢
  omega

theorem crd_b : b = crd b b₁ b₂ (1, 0, 0) := by simp [crd]
theorem crd_b₁ : b₁ = crd b b₁ b₂ (0, 1, 0) := by simp [crd]
theorem crd_b₂ : b₂ = crd b b₁ b₂ (0, 0, 1) := by simp [crd]
theorem crd_binv : b⁻¹ = crd b b₁ b₂ (-1, 0, 0) := by simp [crd]
theorem crd_b₁inv : b₁⁻¹ = crd b b₁ b₂ (0, -1, 0) := by simp [crd]
theorem crd_b₂inv : b₂⁻¹ = crd b b₁ b₂ (0, 0, -1) := by simp [crd]

theorem S_cases {x : G} (hx : x ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) :
    ∃ p ∈ ({(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)} :
      Set (ℤ × ℤ × ℤ)), x = crd b b₁ b₂ p := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, hB.crd_b⟩
  · exact ⟨_, by simp, hB.crd_binv⟩
  · exact ⟨_, by simp, hB.crd_b₁⟩
  · exact ⟨_, by simp, hB.crd_b₁inv⟩
  · exact ⟨_, by simp, hB.crd_b₂⟩
  · exact ⟨_, by simp, hB.crd_b₂inv⟩

end BGen

theorem mono_fix_beta {b b₁ b₂ : G} {J B : Subgroup G} (h4 : FF79Sec4 b J B b₁ b₂) {n : G}
    (hn : n ∈ Nor B) (hβ : n * (b₁ * b₂) * n⁻¹ = b₁ * b₂) :
    (n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) ∧
    ((n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₂) ∨ (n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₁)) := by
  have hB := bgen_of_sec4 h4
  have hmono := h4.mono.2.2.1 n hn
  obtain ⟨u, hu, h1⟩ := hB.S_cases (hmono b₁ (by simp))
  obtain ⟨v, hv, h2⟩ := hB.S_cases (hmono b₂ (by simp))
  obtain ⟨w, hw, h0⟩ := hB.S_cases (hmono b (by simp))
  have heq : crd b b₁ b₂ (u + v) = crd b b₁ b₂ (0, 1, 1) := by
    rw [← hB.crd_mul, ← h1, ← h2]
    have : crd b b₁ b₂ (0, 1, 1) = b₁ * b₂ := by simp [crd]
    rw [this, ← hβ]; group
  have hk := hB.crd_eq heq
  have hinj : ∀ x y : G, n * x * n⁻¹ = n * y * n⁻¹ → x = y := fun x y h => by
    simpa using h
  have hcn : ∀ (x y : G) (i j : ℤ), n * (x ^ i * y ^ j) * n⁻¹ =
      (n * x * n⁻¹) ^ i * (n * y * n⁻¹) ^ j := fun x y i j => by
    rw [conj_zpow, conj_zpow]; group
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv hw
  obtain ⟨u1, u2, u3⟩ := u
  obtain ⟨v1, v2, v3⟩ := v
  obtain ⟨w1, w2, w3⟩ := w
  simp only [Prod.mk.injEq] at hu hv hw
  simp only [Prod.mk_add_mk] at hk
  have hcases : (u1 = 0 ∧ u2 = 1 ∧ u3 = 0 ∧ v1 = 0 ∧ v2 = 0 ∧ v3 = 1) ∨
      (u1 = 0 ∧ u2 = 0 ∧ u3 = 1 ∧ v1 = 0 ∧ v2 = 1 ∧ v3 = 0) := by
    rcases hu with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hv with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    first | (exfalso; omega) | (simp)
  have hb₁c : ∀ j k : ℤ, crd b b₁ b₂ (0, j, k) = b₁ ^ j * b₂ ^ k := fun j k => by simp [crd]
  have hw23 : w2 = 0 ∧ w3 = 0 := by
    have hw' : w2 = 0 ∧ w3 = 0 ∨ (w1 = 0 ∧ (w2 ≠ 0 ∨ w3 ≠ 0)) := by
      rcases hw with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
    rcases hw' with h | ⟨hw1, hne⟩
    · exact h
    · exfalso
      subst hw1
      have hbw : n * b * n⁻¹ = crd b b₁ b₂ (0, w2, w3) := h0
      have hc12 : b₂ ^ w3 * b₁ ^ w2 = b₁ ^ w2 * b₂ ^ w3 :=
        ((show Commute b₁ b₂ from hB.comm.2.2).symm.zpow_zpow w3 w2).eq
      rcases hcases with ⟨hu1, hu2, hu3, hv1, hv2, hv3⟩ | ⟨hu1, hu2, hu3, hv1, hv2, hv3⟩
      · subst hu1 hu2 hu3 hv1 hv2 hv3
        have e1 : n * b₁ * n⁻¹ = b₁ := by rw [h1, ← hB.crd_b₁]
        have e2 : n * b₂ * n⁻¹ = b₂ := by rw [h2, ← hB.crd_b₂]
        have hfix : n * crd b b₁ b₂ (0, w2, w3) * n⁻¹ = crd b b₁ b₂ (0, w2, w3) := by
          rw [hb₁c, hcn, e1, e2]
        have hb : b = crd b b₁ b₂ (0, w2, w3) := hinj _ _ (hbw.trans hfix.symm)
        have hb' : crd b b₁ b₂ (1, 0, 0) = crd b b₁ b₂ (0, w2, w3) := by
          rw [← hB.crd_b]; exact hb
        have := hB.crd_eq hb'
        omega
      · subst hu1 hu2 hu3 hv1 hv2 hv3
        have e1 : n * b₁ * n⁻¹ = b₂ := by rw [h1, ← hB.crd_b₂]
        have e2 : n * b₂ * n⁻¹ = b₁ := by rw [h2, ← hB.crd_b₁]
        have hfix : n * crd b b₁ b₂ (0, w3, w2) * n⁻¹ = crd b b₁ b₂ (0, w2, w3) := by
          rw [hb₁c, hcn, e1, e2, hc12, hb₁c]
        have hb : b = crd b b₁ b₂ (0, w3, w2) := hinj _ _ (hbw.trans hfix.symm)
        have hb' : crd b b₁ b₂ (1, 0, 0) = crd b b₁ b₂ (0, w3, w2) := by
          rw [← hB.crd_b]; exact hb
        have := hB.crd_eq hb'
        omega
  obtain ⟨hw2, hw3⟩ := hw23
  subst hw2 hw3
  refine ⟨?_, ?_⟩
  · rcases hw with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · left; rw [h0, ← hB.crd_b]
    · right; rw [h0, ← hB.crd_binv]
    all_goals omega
  · rcases hcases with ⟨hu1, hu2, hu3, hv1, hv2, hv3⟩ | ⟨hu1, hu2, hu3, hv1, hv2, hv3⟩
    · subst hu1 hu2 hu3 hv1 hv2 hv3
      left; exact ⟨by rw [h1, ← hB.crd_b₁], by rw [h2, ← hB.crd_b₂]⟩
    · subst hu1 hu2 hu3 hv1 hv2 hv3
      right; exact ⟨by rw [h1, ← hB.crd_b₂], by rw [h2, ← hB.crd_b₁]⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
