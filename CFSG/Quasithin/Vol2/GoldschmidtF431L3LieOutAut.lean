module

public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.F431.L3.P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2]

theorem mul_eq_of_apply_G2 {A : GL (Fin 3) F} {σ : F ≃+* F} {b c a c' : F}
    (h : (LinearFlag.conjAut 3 F A * fieldAut 3 F σ) (yP b * wP c) = xP a * wP c') :
    (A : Matrix (Fin 3) (Fin 3) F) *
        ((G2 b c : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((G1 a c' : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (A : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := standard_apply_proj A σ 0 (G2 b c)
  rw [pow_zero, mul_one, proj_G2, h, ← proj_G1] at h1
  have h2 : Phi A σ 0 (G2 b c) = G1 a c' := by
    refine eq_of_proj_eq_of_sq ?_ (G1_mul_self _ _) h1.symm
    rw [← map_mul, G2_mul_self, map_one]
  have h3 := congrArg
    (fun x : Matrix.SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h2
  simp only [coe_Phi_zero] at h3
  exact mul_eq_of_phi h3

theorem not_forall_V2_mem_V1 {θ : MulAut (projectiveSL 3 F)} (hθ : θ ∈ semilinearAutGroup 3 F) :
    ¬ ∀ g ∈ (V2 : Subgroup (projectiveSL 3 F)), θ g ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  intro hall
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hθ
  obtain ⟨a₁, c₁, h₁⟩ := mem_V1.mp (hall (yP 1 * wP 0) ⟨1, 0, rfl⟩)
  obtain ⟨a₂, c₂, h₂⟩ := mem_V1.mp (hall (yP 0 * wP 1) ⟨0, 1, rfl⟩)
  have e1 := mul_eq_of_apply_G2 h₁
  have e2 := mul_eq_of_apply_G2 h₂
  rw [coe_G2, coe_G1] at e1 e2
  have f1 := congrFun (congrFun e1 1) 2
  have f2 := congrFun (congrFun e1 2) 2
  have f3 := congrFun (congrFun e2 1) 2
  have f4 := congrFun (congrFun e2 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply] at f1 f2 f3 f4
  apply det_ne_zero A
  rw [Matrix.det_fin_three, f1, f2, f3, f4]
  ring

omit [CharP F 2] in
theorem inverseTranspose_W0 :
    Matrix.GeneralLinearGroup.inverseTranspose (W0 : GL (Fin 3) F) = W0 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
  show (((W0 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose = _
  rw [coe_W0_inv, coe_W0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharP F 2] in
theorem W0_mul_self : (W0 : GL (Fin 3) F) * W0 = 1 := by
  apply Units.ext
  show ((W0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
    ((W0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_W0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

omit [CharP F 2] in
theorem iota_mul_iota : (iota : MulAut (projectiveSL 3 F)) * iota = 1 := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  unfold iota
  calc LinearFlag.conjAut 3 F W0 * dualAut 3 F * (LinearFlag.conjAut 3 F W0 * dualAut 3 F)
      = LinearFlag.conjAut 3 F W0 *
          (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) := by group
    _ = LinearFlag.conjAut 3 F W0 *
          LinearFlag.conjAut 3 F (Matrix.GeneralLinearGroup.inverseTranspose W0) := by
        rw [htrans.2.2.2.2.1]
    _ = LinearFlag.conjAut 3 F (W0 * Matrix.GeneralLinearGroup.inverseTranspose W0) := by
        rw [htrans.1]
    _ = 1 := by rw [inverseTranspose_W0, W0_mul_self, map_one]

omit [CharP F 2] in
theorem iota_inv : (iota : MulAut (projectiveSL 3 F))⁻¹ = iota :=
  inv_eq_of_mul_eq_one_right iota_mul_iota

theorem iota_mem_V2 {g : projectiveSL 3 F} (hg : g ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    iota g ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨a, c, rfl⟩ := mem_V1.mp hg
  have h : iota (xP a * wP c) = yP a * wP c := by
    rw [← iota_yP_wP a c, ← MulAut.mul_apply, iota_mul_iota, MulAut.one_apply]
  rw [h]
  exact mem_V2.mpr ⟨a, c, rfl⟩

theorem mem_semilinear_of_map_V1 [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (h : ∀ g ∈ (V1 : Subgroup (projectiveSL 3 F)), θ g ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    θ ∈ semilinearAutGroup 3 F := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  have hθ : θ ∈ standardAutGroup 3 F := by rw [hR]; exact Subgroup.mem_top θ
  rcases mem_or_mul_dualAut_mem hθ with h1 | h1
  · exact h1
  · exfalso
    have hδδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
    have he : θ * iota =
        (θ * dualAut 3 F) * (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) := by
      rw [show (θ * dualAut 3 F) * (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) =
        θ * (dualAut 3 F * dualAut 3 F) * LinearFlag.conjAut 3 F W0 * dualAut 3 F by group,
        hδδ, mul_one]
      unfold iota
      group
    have he' : θ * iota ∈ semilinearAutGroup 3 F := by
      rw [he, htrans.2.2.2.2.1]
      exact mul_mem h1 (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
    refine not_forall_V2_mem_V1 he' fun g hg => ?_
    rw [MulAut.mul_apply]
    exact h _ (iota_mem_V1 hg)

theorem mem_semilinear_of_map_V2 [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (h : ∀ g ∈ (V2 : Subgroup (projectiveSL 3 F)), θ g ∈ (V2 : Subgroup (projectiveSL 3 F))) :
    θ ∈ semilinearAutGroup 3 F := by
  have h1 : iota * θ * iota ∈ semilinearAutGroup 3 F := by
    refine mem_semilinear_of_map_V1 fun g hg => ?_
    simp only [MulAut.mul_apply]
    exact iota_mem_V1 (h _ (iota_mem_V2 hg))
  have h2 := (conj_mem_iff_semilinear (iota : MulAut (projectiveSL 3 F))⁻¹ θ).mp
  rw [iota_inv] at h2
  exact h2 (by rw [iota_inv]; exact h1)

theorem card_sq_le_center [Finite F] {B : Subgroup (projectiveSL 3 F)}
    (hB : B ≤ (Wg : Subgroup (projectiveSL 3 F))) {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∈ semilinearAutGroup 3 F) (hθD : θ ∉ linearAutGroup 3 F)
    (hfix : ∀ g ∈ B, θ g = g) : Nat.card B ^ 2 ≤ Nat.card F := by
  obtain ⟨σ, m₁₁, m₁₂, m₂₁, m₂₂, hσ, hsub⟩ := fixes_type0 hθ hθD
  have hv₀ : ((0 : F), (1 : F)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  have h1 : Nat.card B ≤ Nat.card {v : F × F | Semilin.InS σ m₁₁ m₁₂ m₂₁ m₂₂ v ∧
      ∃ t : F, v = (t * ((0 : F), (1 : F)).1, t * ((0 : F), (1 : F)).2)} := by
    refine card_le_of_pairs (hB.trans Wg_le_V1) _ fun a c h => ⟨hsub (hfix _ h), c, ?_⟩
    have haz : a = 0 := by
      by_contra ha
      obtain ⟨c', hc'⟩ := hB h
      exact xP_wP_ne a c c' ha hc'
    simp [haz]
  have h2 := h1.trans (Semilin.card_inS_line_le σ m₁₁ m₁₂ m₂₁ m₂₂ hv₀)
  calc Nat.card B ^ 2 ≤ Nat.card (Semilin.FixSet σ) ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ Nat.card F := Semilin.card_fixSet_sq_le σ hσ

theorem card_V2 [Finite F] : Nat.card (V2 : Subgroup (projectiveSL 3 F)) = Nat.card F ^ 2 :=
  card_V1_eq_card_V2.symm.trans card_V1

theorem card_Wg : Nat.card (Wg : Subgroup (projectiveSL 3 F)) = Nat.card F := by
  have e : F ≃ (Wg : Subgroup (projectiveSL 3 F)) :=
    Equiv.ofBijective (fun c => ⟨wP c, c, rfl⟩)
      ⟨fun p q h => wP_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨c, hg⟩ := mem_Wg.mp g.2
        exact ⟨c, Subtype.ext hg.symm⟩⟩
  exact (Nat.card_congr e).symm

omit [CharP F 2] in
theorem autField_pow_eq_one {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (σ : F ≃+* F) :
    σ ^ f = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hF
  rw [← hcard]
  exact pow_card_eq_one'

omit [CharP F 2] in
theorem pow_mem_linearAut {n : ℕ} (hn : ∀ σ : F ≃+* F, σ ^ n = 1)
    {θ : MulAut (projectiveSL 3 F)} (hθ : θ ∈ semilinearAutGroup 3 F) :
    θ ^ n ∈ linearAutGroup 3 F := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hθ
  have key : ∀ m : ℕ, ∃ B : GL (Fin 3) F, (LinearFlag.conjAut 3 F A * fieldAut 3 F σ) ^ m =
      LinearFlag.conjAut 3 F B * fieldAut 3 F (σ ^ m) := by
    intro m
    induction m with
    | zero => exact ⟨1, by simp⟩
    | succ m ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨B * Matrix.GeneralLinearGroup.map ((σ ^ m : F ≃+* F) : F →+* F) A, ?_⟩
      rw [pow_succ, hB, conjAut_mul_fieldAut_mul, pow_succ]
  obtain ⟨B, hB⟩ := key n
  rw [hB, hn σ, map_one, mul_one]
  exact conjAut_mem_linearAutGroup B

omit [CharP F 2] in
theorem not_mem_linearAut_of_two_power [Finite F] {θ : MulAut (projectiveSL 3 F)} {k : ℕ}
    (hk : orderOf θ = 2 ^ k)
    (hθ : θ ∉ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) :
    θ ∉ linearAutGroup 3 F := by
  intro hD
  refine hθ ?_
  have hdiag : ¬ 2 ∣ Nat.gcd 3 (Nat.card F - 1) := fun h => by
    have := Nat.dvd_trans h (Nat.gcd_dvd_left 3 _)
    omega
  refine CFSG.RankThree.PartOne.OutStructure.linear_D2 (K := F) Nat.prime_two le_rfl hdiag θ hD k ?_
  rw [← hk, pow_orderOf_eq_one]
  exact Subgroup.one_mem _

omit [CharP F 2] in
theorem isCyclic_card_le [Finite F] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {X : Subgroup (MulAut (projectiveSL 3 F))} (hX : IsPGroup 2 X)
    (hXE : X ≤ semilinearAutGroup 3 F)
    (hXI : ∀ x ∈ X, x ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range →
      x = 1) : IsCyclic X ∧ Nat.card X ≤ f := by
  have hDX : ∀ x ∈ X, x ∈ linearAutGroup 3 F → x = 1 := by
    intro x hx hxD
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨x, hx⟩
    have hk' : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hx]; exact hk
    by_contra hx1
    exact not_mem_linearAut_of_two_power hk' (fun hI => hx1 (hXI x hx hI)) hxD
  obtain ⟨-, -, hDn, -, -, ⟨g, -, hg⟩, -, -, -, -⟩ :=
    standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  have hDnorm : (linearAutGroup 3 F).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup 3 F := hR ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup 3 F := hR ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  let φ : X →* (MulAut (projectiveSL 3 F)) ⧸ (linearAutGroup 3 F) :=
    (QuotientGroup.mk' (linearAutGroup 3 F)).comp X.subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : MulAut (projectiveSL 3 F)) ∈ linearAutGroup 3 F :=
      (QuotientGroup.eq_one_iff _).mp hx
    exact Subtype.ext (hDX x x.2 hx')
  have hφrange : ∀ x : X, φ x ∈ Subgroup.zpowers (QuotientGroup.mk' (linearAutGroup 3 F) g) := by
    intro x
    obtain ⟨k, hk⟩ := hg x (hXE x.2)
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    have h1 : (QuotientGroup.mk' (linearAutGroup 3 F)) (g ^ k * (x : MulAut (projectiveSL 3 F))) =
        1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [map_mul, map_zpow] at h1
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  let φ' : X →* ↥(Subgroup.zpowers (QuotientGroup.mk' (linearAutGroup 3 F) g)) :=
    φ.codRestrict _ hφrange
  have hφ'inj : Function.Injective φ' := fun a b h => hφinj (congrArg Subtype.val h)
  have hcyc : IsCyclic X := isCyclic_of_injective φ' hφ'inj
  refine ⟨hcyc, ?_⟩
  obtain ⟨y, hy⟩ := hcyc.exists_generator
  have hord : orderOf y = Nat.card X := orderOf_eq_card_of_forall_mem_zpowers hy
  have hy1 : y ^ f = 1 := by
    have h1 : (y : MulAut (projectiveSL 3 F)) ^ f = 1 :=
      hDX _ (X.pow_mem y.2 f) (pow_mem_linearAut (autField_pow_eq_one hf hF) (hXE y.2))
    exact Subtype.ext (by simpa using h1)
  rw [← hord]
  exact Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hy1)

end CFSG.Quasithin.H13.F431.L3.P3
