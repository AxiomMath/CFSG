module

public import CFSG.RankThree.PartOne.SEITZ2.G2F2Rad

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) K

theorem eq_zero_or_one_of_card_two {k : Subfield K} (hk : Nat.card k = 2) {c : K} (hc : c ∈ k) :
    c = 0 ∨ c = 1 := by
  by_contra h
  push Not at h
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
  have h1 : (⟨1, k.one_mem⟩ : k) = y := huniq _ (fun h' => one_ne_zero (congrArg Subtype.val h'))
  have h2 : (⟨c, hc⟩ : k) = y := huniq _ (fun h' => h.1 (congrArg Subtype.val h'))
  exact h.2 (congrArg Subtype.val (h2.trans h1.symm))


@[expose] noncomputable def Gam (t₁ t₂ μ : K) : Subgroup (adjointGroup .G2 K) :=
  Subgroup.closure {xp 0 1, xp 2 μ, xp 7 1 * xp 0 t₁, xp 4 1 * xp 0 t₂}

theorem x0_mem_Gam (t₁ t₂ μ : K) : xp 0 1 ∈ Gam t₁ t₂ μ :=
  Subgroup.subset_closure (by simp)

theorem x2_mem_Gam (t₁ t₂ μ : K) : xp 2 μ ∈ Gam t₁ t₂ μ :=
  Subgroup.subset_closure (by simp)

theorem b1_mem_Gam (t₁ t₂ μ : K) : xp 7 1 * xp 0 t₁ ∈ Gam t₁ t₂ μ :=
  Subgroup.subset_closure (by simp)

theorem b2_mem_Gam (t₁ t₂ μ : K) : xp 4 1 * xp 0 t₂ ∈ Gam t₁ t₂ μ :=
  Subgroup.subset_closure (by simp)

theorem xp_inj {p : ℕ} (hp : p < 12) {a b : K} (h : xp p a = xp p b) : a = b :=
  xPar_injective (F := rootOperatorFamily .G2) (K := K) (isRoot_rt hp) h

variable [CharP K 2]

omit [CharP K 2] in
theorem xp_ne_one {p : ℕ} (hp : p < 12) {a : K} (ha : a ≠ 0) : xp p a ≠ 1 := fun h =>
  ha (xp_inj hp (h.trans (xp_zero p).symm))

omit [CharP K 2] in
theorem Gam_le_PL (t₁ t₂ μ : K) : Gam t₁ t₂ μ ≤ (rhoB K).range ⊔ Qb K := by
  have hL : ∀ c : K, xp 0 c ∈ (rhoB K).range ⊔ Qb K := fun c =>
    Subgroup.mem_sup_left (⟨u2 c, rhoB_u2 c⟩ : xp 0 c ∈ (rhoB K).range)
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl | rfl)
  · exact hL 1
  · exact Subgroup.mem_sup_left (⟨l2 μ, rhoB_l2 μ⟩ : xp 2 μ ∈ (rhoB K).range)
  · exact mul_mem (Subgroup.mem_sup_right (xp_mem_Qb (p := 7) (by simp [qbList]) 1)) (hL t₁)
  · exact mul_mem (Subgroup.mem_sup_right (xp_mem_Qb (p := 4) (by simp [qbList]) 1)) (hL t₂)

theorem ActsAs.Qb_mul {g q : adjointGroup .G2 K} {A : SL2} (hg : ActsAs g A) (hq : q ∈ Qb K) :
    ActsAs (q * g) A := fun v => by
  rw [show q * g * dvv v * (q * g)⁻¹ = q * (g * dvv v * g⁻¹) * q⁻¹ by group, hg v, Qb_conj_dvv hq]

theorem exists_actsAs_of_mem_PL {g : adjointGroup .G2 K} (hg : g ∈ (rhoB K).range ⊔ Qb K) :
    ∃ A : SL2, ∃ q ∈ Qb K, g = rhoB K A * q ∧ ActsAs g A := by
  obtain ⟨A, q, hq, rfl⟩ := mem_PL hg
  exact ⟨A, q, hq, rfl, (actsAs_rhoB A).mul_Qb hq⟩

@[expose] def lev (H : Subgroup (adjointGroup .G2 K)) : Subgroup SL2 where
  carrier := {A | ∃ g ∈ H, ActsAs g A}
  mul_mem' := by
    rintro A B ⟨g, hg, hA⟩ ⟨g', hg', hB⟩
    exact ⟨g * g', mul_mem hg hg', hA.mul hB⟩
  one_mem' := ⟨1, one_mem _, ActsAs.one⟩
  inv_mem' := by
    rintro A ⟨g, hg, hA⟩
    exact ⟨g⁻¹, inv_mem hg, hA.inv⟩

omit [CharP K 2] in
theorem mem_lev {H : Subgroup (adjointGroup .G2 K)} {A : SL2} :
    A ∈ lev H ↔ ∃ g ∈ H, ActsAs g A := Iff.rfl

theorem lev_eq_top [Finite K] {k : Subfield K} (hk : Nat.card k = 2)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d) {t₁ t₂ μ : K}
    (hμ : μ ≠ 0) (ht : ¬ (t₁ ∈ k ∧ t₂ ∈ k)) : lev (Gam t₁ t₂ μ) = ⊤ := by
  have hu1 : u2 (1 : K) ∈ lev (Gam t₁ t₂ μ) := ⟨xp 0 1, x0_mem_Gam t₁ t₂ μ, actsAs_x0 1⟩
  have hl : l2 μ ∈ lev (Gam t₁ t₂ μ) := ⟨xp 2 μ, x2_mem_Gam t₁ t₂ μ, actsAs_x2 μ⟩
  have hut1 : u2 t₁ ∈ lev (Gam t₁ t₂ μ) :=
    ⟨xp 7 1 * xp 0 t₁, b1_mem_Gam t₁ t₂ μ,
      (actsAs_x0 t₁).Qb_mul (xp_mem_Qb (p := 7) (by simp [qbList]) 1)⟩
  have hut2 : u2 t₂ ∈ lev (Gam t₁ t₂ μ) :=
    ⟨xp 4 1 * xp 0 t₂, b2_mem_Gam t₁ t₂ μ,
      (actsAs_x0 t₂).Qb_mul (xp_mem_Qb (p := 4) (by simp [qbList]) 1)⟩
  obtain ⟨c, huc, hck⟩ : ∃ c : K, u2 c ∈ lev (Gam t₁ t₂ μ) ∧ c ∉ k := by
    by_cases h1 : t₁ ∈ k
    · exact ⟨t₂, hut2, fun h2 => ht ⟨h1, h2⟩⟩
    · exact ⟨t₁, hut1, h1⟩
  refine sl2_eq_top_of_root_groups hd hd2 hK (a₁ := 1) (a₂ := c) (b₀ := μ) one_ne_zero
    (by simpa using hck) hμ ?_ hl
  intro c₁ hc₁ c₂ hc₂
  rcases eq_zero_or_one_of_card_two hk hc₁ with rfl | rfl <;>
    rcases eq_zero_or_one_of_card_two hk hc₂ with rfl | rfl
  · simp only [zero_mul, add_zero, u2_zero]
    exact one_mem _
  · simpa using huc
  · simpa using hu1
  · rw [show (1 : K) * 1 + 1 * c = 1 + c by ring, u2_add]
    exact mul_mem hu1 huc

theorem comm0 (c : ℕ → K) (d : K) :
    xp 0 d * (ordProd c * xp 0 d * (ordProd c)⁻¹) =
      xp 4 (c 1 * d) * (xp 8 (c 1 ^ 2 * d) * (xp 3 (c 1 ^ 3 * d) *
        xp 7 (c 0 * c 1 ^ 3 * d + c 1 ^ 3 * d ^ 2 + c 3 * d))) := by
  rw [conj_x0, xp_cancel]

theorem exists_nontriv [Finite K] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hK : Nat.card K = Nat.card k ^ d) {t₁ t₂ μ : K} (hμ : μ ≠ 0) (ht : ¬ (t₁ ∈ k ∧ t₂ ∈ k)) :
    ∃ n ∈ Gam t₁ t₂ μ, n ∈ Ug K ∧ ActsAs n 1 ∧ n ≠ 1 := by
  have htop := lev_eq_top hk hd hd2 hK hμ ht
  have hq4 : xp 4 (1 : K) ∈ Qb K := xp_mem_Qb (p := 4) (by simp [qbList]) 1
  have hb2 : ActsAs (xp 4 1 * xp 0 t₂) (u2 t₂) := (actsAs_x0 t₂).Qb_mul hq4
  have hb2Ug : xp 4 1 * xp 0 t₂ ∈ Ug K :=
    mul_mem (xp_mem_Ug (by simp [posList]) 1) (xp_mem_Ug (by simp [posList]) t₂)
  by_cases h2 : t₂ = 0
  · subst h2
    refine ⟨xp 4 1 * xp 0 0, b2_mem_Gam _ _ _, hb2Ug, ?_, ?_⟩
    · simpa [u2_zero] using hb2
    · rw [xp_zero, mul_one]
      exact xp_ne_one (by norm_num) one_ne_zero
  · obtain ⟨r, hr⟩ := exists_sq_eq (K := K) t₂
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply h2
      rw [← hr]
      ring
    obtain ⟨γ, hγ, hγA⟩ :=
      (mem_lev (H := Gam t₁ t₂ μ) (A := dg r hr0)).1 (htop ▸ Subgroup.mem_top _)
    obtain ⟨A', q, hq, hγeq, hγA'⟩ := exists_actsAs_of_mem_PL (Gam_le_PL t₁ t₂ μ hγ)
    have hAA : A' = dg r hr0 := hγA'.unique hγA
    have hu2 : A' * u2 1 * A'⁻¹ = u2 t₂ := by
      rw [hAA, dg_mul_u2_mul_dg_inv, mul_one, hr]
    have e1 : rhoB K A' * xp 0 1 * (rhoB K A')⁻¹ = xp 0 t₂ := by
      calc rhoB K A' * xp 0 1 * (rhoB K A')⁻¹ = rhoB K (A' * u2 1 * A'⁻¹) := by
            rw [map_mul, map_mul, map_inv, rhoB_u2]
        _ = xp 0 t₂ := by rw [hu2, rhoB_u2]
    set q' : adjointGroup .G2 K := rhoB K A' * q * (rhoB K A')⁻¹ with hq'
    have hq'Qb : q' ∈ Qb K := rhoB_conj_Qb A' hq
    have hconj : γ * xp 0 1 * γ⁻¹ = q' * xp 0 t₂ * q'⁻¹ := by
      calc γ * xp 0 1 * γ⁻¹ = (rhoB K A' * q * (rhoB K A')⁻¹) *
            (rhoB K A' * xp 0 1 * (rhoB K A')⁻¹) * (rhoB K A' * q * (rhoB K A')⁻¹)⁻¹ := by
            rw [hγeq]
            group
        _ = q' * xp 0 t₂ * q'⁻¹ := by rw [e1]
    have hγact : ActsAs (γ * xp 0 1 * γ⁻¹) (u2 t₂) := by
      have := (hγA.mul (actsAs_x0 1)).mul hγA.inv
      rwa [show dg r hr0 * u2 1 * (dg r hr0)⁻¹ = u2 t₂ by rw [← hAA]; exact hu2] at this
    refine ⟨(xp 4 1 * xp 0 t₂) * (γ * xp 0 1 * γ⁻¹),
      mul_mem (b2_mem_Gam _ _ _) (mul_mem (mul_mem hγ (x0_mem_Gam _ _ _)) (inv_mem hγ)),
      mul_mem hb2Ug ?_, ?_, ?_⟩
    · rw [hconj]
      exact mul_mem (mul_mem (Qb_le_Ug hq'Qb) (xp_mem_Ug (by simp [posList]) t₂))
        (inv_mem (Qb_le_Ug hq'Qb))
    · rw [← u2_mul_self t₂]
      exact hb2.mul hγact
    · intro h1
      rw [hconj] at h1
      have h3 : q' * xp 0 t₂ * q'⁻¹ = (xp 4 1 * xp 0 t₂)⁻¹ := eq_inv_of_mul_eq_one_right h1
      obtain ⟨c, hc⟩ := exists_ordProd (Qb_le_Ug hq'Qb)
      rw [hc, conj_x0, mul_inv_rev, xp_inv, xp_inv] at h3
      have h4 := mul_left_cancel h3
      generalize c 0 * c 1 ^ 3 * t₂ + c 1 ^ 3 * t₂ ^ 2 + c 3 * t₂ = E at h4
      have h6 : xp 0 0 * xp 1 0 * xp 4 (c 1 * t₂) * xp 8 (c 1 ^ 2 * t₂) * xp 3 (c 1 ^ 3 * t₂) *
          xp 7 E = xp 0 0 * xp 1 0 * xp 4 1 * xp 8 0 * xp 3 0 * xp 7 0 := by
        simp only [xp_zero, one_mul, mul_one, mul_assoc]
        exact h4
      obtain ⟨-, -, h41, h81, -, -⟩ := six_inj h6
      have h5 : c 1 ^ 2 * t₂ = c 1 * (c 1 * t₂) := by ring
      rw [h5, h41, mul_one] at h81
      rw [h81, zero_mul] at h41
      exact zero_ne_one h41

end CFSG.RankThree.PartOne.SEITZ2
