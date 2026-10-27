module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique
open scoped commutatorElement

section DirectProduct

variable {Γ : Type*} [Group Γ] {G₁ G₂ : Subgroup Γ}

theorem mem_sup_iff_of_commute_ch615 (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) {g : Γ} :
    g ∈ G₁ ⊔ G₂ ↔ ∃ a ∈ G₁, ∃ b ∈ G₂, a * b = g := by
  have hN : G₁ ≤ Subgroup.normalizer (G₂ : Set Γ) :=
    Lin2.le_normalizer_of_commute fun b hb a ha => (hc a ha b hb).symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right G₁ G₂ hN]
  exact Set.mem_mul

theorem sup_le_normalizer_ch615 (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    G₁ ⊔ G₂ ≤ Subgroup.normalizer (G₁ : Set Γ) :=
  sup_le Subgroup.le_normalizer (Lin2.le_normalizer_of_commute hc)

theorem mem_of_commute_ch615 (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hZ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1) {g : Γ} (hg : g ∈ G₁ ⊔ G₂)
    (hgc : ∀ x ∈ G₁, g * x = x * g) : g ∈ G₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute_ch615 hc).mp hg
  have ha1 : a = 1 := hZ a ha fun x hx => by
    have h1 := hgc x hx
    have h2 : b * x = x * b := (hc x hx b hb).symm
    calc a * x = a * (x * b) * b⁻¹ := by group
      _ = a * b * x * b⁻¹ := by rw [← h2]; group
      _ = x * (a * b) * b⁻¹ := by rw [h1]
      _ = x * a := by group
  rw [ha1, one_mul]
  exact hb

theorem map_conj_eq_or_le_ch615 [Finite Γ] (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hs : IsSimpleGroup ↥G₁) (hZ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1) {x : Γ}
    (hx : x ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Γ) : Set Γ)) :
    G₁.map (MulAut.conj x).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj x).toMonoidHom ≤ G₂ := by
  set N := G₁.map (MulAut.conj x).toMonoidHom with hNdef
  have hxi : x⁻¹ ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Γ) : Set Γ) :=
    Subgroup.inv_mem _ hx
  have hNG : N ≤ G₁ ⊔ G₂ := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp (Subgroup.mem_sup_left ha)
  have hNn : ∀ g ∈ G₁ ⊔ G₂, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    rintro g hg _ ⟨a, ha, rfl⟩
    have hg' : x⁻¹ * g * x⁻¹⁻¹ ∈ G₁ ⊔ G₂ := (Subgroup.mem_normalizer_iff.mp hxi g).mp hg
    rw [inv_inv] at hg'
    have h1 := (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_ch615 hc hg') a).mp ha
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hsN : IsSimpleGroup ↥N :=
    (Subgroup.equivMapOfInjective G₁ _ (MulAut.conj x).injective).symm.isSimpleGroup
  have hnorm : (G₁.subgroupOf N).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_ch615 hc (hNG k.2)) n).mp hn
    simpa using this⟩
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · right
    intro n hn
    refine mem_of_commute_ch615 hc hZ (hNG hn) fun y hy => ?_
    have h1 : n * y * n⁻¹ * y⁻¹ ∈ N := by
      have := hNn y (Subgroup.mem_sup_left hy) n⁻¹ (N.inv_mem hn)
      have h2 := N.mul_mem hn this
      simpa [mul_assoc] using h2
    have h2 : n * y * n⁻¹ * y⁻¹ ∈ G₁ :=
      G₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_ch615 hc (hNG hn)) y).mp hy)
        (G₁.inv_mem hy)
    have h3 : (⟨_, h1⟩ : ↥N) ∈ G₁.subgroupOf N := Subgroup.mem_subgroupOf.mpr h2
    rw [hb, Subgroup.mem_bot] at h3
    have h4 : n * y * n⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h3
    calc n * y = n * y * n⁻¹ * y⁻¹ * (y * n) := by group
      _ = y * n := by rw [h4, one_mul]
  · left
    have hle : N ≤ G₁ := fun n hn => by
      have : (⟨n, hn⟩ : ↥N) ∈ G₁.subgroupOf N := ht ▸ Subgroup.mem_top _
      exact this
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [hNdef, Subgroup.card_map_of_injective (MulAut.conj x).injective])

theorem le_sup_inf_of_isSylowTwoOf_ch615 [Finite Γ] (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hinf : G₁ ⊓ G₂ = ⊥) {P : Subgroup Γ} (hP : IsSylowTwoOf P (G₁ ⊔ G₂)) :
    P ≤ (P ⊓ G₁) ⊔ (P ⊓ G₂) := by
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hn₁ : (G₁.subgroupOf (G₁ ⊔ G₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le_normalizer_ch615 hc)
  have hn₂ : (G₂.subgroupOf (G₁ ⊔ G₂)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
    rw [sup_comm]
    exact sup_le_normalizer_ch615 hc'
  have hP₁ : IsSylowTwoOf (P ⊓ G₁) G₁ :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hP le_sup_left hn₁.isSubnormal
  have hP₂ : IsSylowTwoOf (P ⊓ G₂) G₂ :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hP le_sup_right hn₂.isSubnormal
  have hQ := Lin2.isSylowTwoOf_sup_of_commuting hc hP₁ hP₂ (by rw [hinf]; exact bot_le)
  have hQP : (P ⊓ G₁) ⊔ (P ⊓ G₂) ≤ P := sup_le inf_le_left inf_le_left
  exact (hQ.eq_of_le hQP hP.le hP.isPGroup).le

theorem commutator_le_sup_inf_ch615 (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    {K J P : Subgroup Γ} (hK : K ≤ G₁ ⊔ G₂) (hJ : J ≤ (P ⊓ G₁) ⊔ (P ⊓ G₂))
    (hPK : P ≤ Subgroup.normalizer (K : Set Γ)) : ⁅K, J⁆ ≤ (K ⊓ G₁) ⊔ (K ⊓ G₂) := by
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hcP : ∀ a ∈ P ⊓ G₁, ∀ b ∈ P ⊓ G₂, a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have hN₁ := sup_le_normalizer_ch615 hc
  have hN₂ : G₁ ⊔ G₂ ≤ Subgroup.normalizer (G₂ : Set Γ) := by
    rw [sup_comm]
    exact sup_le_normalizer_ch615 hc'
  have key : ∀ k ∈ K, ∀ (G' : Subgroup Γ), G₁ ⊔ G₂ ≤ Subgroup.normalizer (G' : Set Γ) →
      ∀ y ∈ P ⊓ G', ⁅k, y⁆ ∈ K ⊓ G' := by
    intro k hk G' hG' y hy
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hPK hy.1) k⁻¹).mp (K.inv_mem hk)
      simpa [mul_assoc] using K.mul_mem hk this
    · exact G'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hG' (hK hk)) y).mp hy.2)
        (G'.inv_mem hy.2)
  rw [Subgroup.commutator_le]
  intro k hk j hj
  obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := (mem_sup_iff_of_commute_ch615 hcP).mp (hJ hj)
  have h1 := key k hk G₁ hN₁ j₁ hj₁
  have h2 := key k hk G₂ hN₂ j₂ hj₂
  have e : ⁅k, j₁ * j₂⁆ = ⁅k, j₁⁆ * (j₁ * ⁅k, j₂⁆ * j₁⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h3 : j₁ * ⁅k, j₂⁆ * j₁⁻¹ = ⁅k, j₂⁆ := by
    rw [hc j₁ hj₁.2 _ h2.2, mul_inv_cancel_right]
  rw [e, h3]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

end DirectProduct

section SLTwo

variable {K : Type} [Field K]

theorem sq_eq_one_of_pow_four_ch615 (h2 : (2 : K) = 0) (M : Matrix (Fin 2) (Fin 2) K)
    (hdet : M.det = 1) (h4 : M ^ 4 = 1) : M ^ 2 = 1 := by
  set t := M 0 0 + M 1 1 with ht
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rwa [Matrix.det_fin_two] at hdet
  have hsq : M ^ 2 = t • M + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_two, ht] <;>
      first | linear_combination (-1 : K) * hd - h2 | ring
  have h22 : (2 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    rw [show (2 : Matrix (Fin 2) (Fin 2) K) = (2 : K) • 1 by simp [two_smul, one_add_one_eq_two],
      h2, zero_smul]
  have hexp : (t • M + 1) ^ 2 = t ^ 2 • M ^ 2 + 1 := by
    rw [(Commute.one_right (t • M)).add_sq, smul_pow, one_pow, mul_one, h22, zero_mul, add_zero]
  have hN : t ^ 2 • M ^ 2 = 0 := by
    have : (M ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
    rw [hsq, hexp] at this
    exact add_eq_right.mp this
  have hdet2 : (t ^ 2 • M ^ 2).det = (t ^ 2) ^ 2 := by
    rw [Matrix.det_smul, Matrix.det_pow, hdet, one_pow, mul_one, Fintype.card_fin]
  rw [hN, Matrix.det_zero] at hdet2
  have ht0 : t = 0 := by
    have : (t ^ 2) ^ 2 = 0 := hdet2.symm
    exact pow_eq_zero_iff (by norm_num) |>.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  rw [hsq, ht0, zero_smul, zero_add]

theorem det_eq_one_of_mem_statedSL_ch615 {n : ℕ} {A : GL (Fin n) K}
    (hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSL n K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem not_four_dvd_orderOf_ch615 [Finite K] (h2 : (2 : K) = 0)
    (A : CFSG.Assembly.LowTwoRank.StatedSL 2 K) : ¬ 4 ∣ orderOf A := by
  intro h4
  set B := A ^ (orderOf A / 4) with hB
  have hBo : orderOf B = 4 := by
    rw [hB, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos A) h4) (by norm_num)).ne'
      (Nat.div_dvd_of_dvd h4)]
    exact Nat.div_div_self h4 (orderOf_pos A).ne'
  have hB4 : B ^ 4 = 1 := by rw [← hBo]; exact pow_orderOf_eq_one B
  have hM4 : ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 4 = 1 := by
    have := congrArg (fun C : CFSG.Assembly.LowTwoRank.StatedSL 2 K =>
      ((C : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hB4
    simpa using this
  have hM2 := sq_eq_one_of_pow_four_ch615 h2 _ (det_eq_one_of_mem_statedSL_ch615 B.2) hM4
  have hB2 : B ^ 2 = 1 := Subtype.ext (Units.ext (by simpa using hM2))
  have := orderOf_dvd_of_pow_eq_one hB2
  rw [hBo] at this
  omega

end SLTwo

end CFSG.Quasithin.H13
