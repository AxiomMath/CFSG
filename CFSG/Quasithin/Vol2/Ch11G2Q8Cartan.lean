module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Borel
public import CFSG.Quasithin.Vol2.KGNatSL3Lev

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

theorem pCoreOf_stabV0 [Finite F] :
    pCoreOf 2 (stabV0 F) = (levi1 (F := F)).ker.map (stabV0 F).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := F)
  unfold pCoreOf
  congr 1
  apply le_antisymm
  · have : ((CFSG.Open.pCore 2 ↥(stabV0 F)).map (levi1 (F := F))).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).map _ levi1_surjective
    have h := eq_bot_of_normal_isPGroup_SL2
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥(stabV0 F))).map (levi1 (F := F)))
    rwa [Subgroup.map_eq_bot_iff] at h
  · exact CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) isPGroup_ker_levi1

theorem mem_pCoreOf_stabV0_iff [Finite F] {x : ↥(cayleyGroup F)} :
    x ∈ pCoreOf 2 (stabV0 F) ↔ x ∈ stabV0 F ∧ levi1Mat x = 1 := by
  rw [pCoreOf_stabV0]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 := congrArg (fun N : SpecialLinearGroup (Fin 2) F => (N : Matrix (Fin 2) (Fin 2) F))
      (MonoidHom.mem_ker.mp hy)
    simp only [levi1_apply, Matrix.SpecialLinearGroup.coe_one] at h1
    exact h1
  · rintro ⟨hx, h1⟩
    refine ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
    rw [levi1_apply, Matrix.SpecialLinearGroup.coe_one]
    exact h1

theorem pCoreOf_gam2 [Finite F] (h4 : 4 ≤ Nat.card F) :
    pCoreOf 2 (perfectCore (stabQ (stdF F 2))) =
      (levi2 (F := F)).ker.map (perfectCore (stabQ (stdF F 2))).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := F)
  unfold pCoreOf
  congr 1
  apply le_antisymm
  · have : ((CFSG.Open.pCore 2 ↥(perfectCore (stabQ (stdF F 2)))).map
        (levi2 (F := F))).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).map _ (levi2_surjective h4)
    have h := eq_bot_of_normal_isPGroup_SL2
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2
        (G := ↥(perfectCore (stabQ (stdF F 2))))).map (levi2 (F := F)))
    rwa [Subgroup.map_eq_bot_iff] at h
  · exact CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) isPGroup_ker_levi2

theorem mem_pCoreOf_gam2_iff [Finite F] (h4 : 4 ≤ Nat.card F) {x : ↥(cayleyGroup F)} :
    x ∈ pCoreOf 2 (perfectCore (stabQ (stdF F 2))) ↔
      x ∈ perfectCore (stabQ (stdF F 2)) ∧ levi2Mat x = 1 := by
  rw [pCoreOf_gam2 h4]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 := congrArg (fun N : SpecialLinearGroup (Fin 2) F => (N : Matrix (Fin 2) (Fin 2) F))
      (MonoidHom.mem_ker.mp hy)
    simp only [levi2_apply, Matrix.SpecialLinearGroup.coe_one] at h1
    exact h1
  · rintro ⟨hx, h1⟩
    refine ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
    rw [levi2_apply, Matrix.SpecialLinearGroup.coe_one]
    exact h1

theorem g2T_mem_stabQ (s : Fˣ × Fˣ) (h : ℕ) : g2T s ∈ stabQ (stdF F h) :=
  mem_stabQ.mpr fun w => (g2T_inF s w).symm

theorem vpart_g2T (s : Fˣ × Fˣ) (w : Ix3 → F) :
    vpart (g2Act (g2T s) w) = levi1Mat (g2T s) *ᵥ vpart w := by
  rw [g2Act_g2T, levi1Mat_g2T]
  funext i
  fin_cases i <;> simp [vpart, q6, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem levi1Mat_conj_g2T (s : Fˣ × Fˣ) {γ : ↥(cayleyGroup F)} (hγ : γ ∈ stabV0 F) :
    levi1Mat (g2T s * γ * (g2T s)⁻¹) =
      levi1Mat (g2T s) * levi1Mat γ * levi1Mat (g2T s⁻¹) := by
  ext i j
  have hb : g2Act (g2T s⁻¹) (q6 0 0 0 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)) ∈
      stdF F 3 := (g2T_inF s⁻¹ _).mpr (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
  rw [levi1Mat_apply, ← map_inv, g2Act_mul_apply, g2Act_mul_apply, vpart_g2T, vpart_act hγ hb,
    vpart_g2T, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  fin_cases j <;> simp [vpart, q6, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem levi1Mat_g2T_mul_inv (s : Fˣ × Fˣ) : levi1Mat (g2T s) * levi1Mat (g2T s⁻¹) = 1 := by
  have h1 : (s.1 : F) ≠ 0 := s.1.ne_zero
  have h2 : (s.2 : F) ≠ 0 := s.2.ne_zero
  rw [levi1Mat_g2T, levi1Mat_g2T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem levi2Mat_g2T (s : Fˣ × Fˣ) :
    levi2Mat (g2T s) = !![(s.1 : F), 0; 0, (s.1 : F) * s.2] := by
  ext i j
  rw [levi2Mat_apply, g2Act_g2T]
  fin_cases i <;> fin_cases j <;> simp [upart, q6]

theorem levi2Mat_conj_g2T (s : Fˣ × Fˣ) {γ : ↥(cayleyGroup F)} (hγ : γ ∈ stabQ (stdF F 2)) :
    levi2Mat (g2T s * γ * (g2T s)⁻¹) =
      levi2Mat (g2T s) * levi2Mat γ * levi2Mat (g2T s⁻¹) := by
  rw [← map_inv, levi2Mat_mul (g2T_mem_stabQ s⁻¹ 2), levi2Mat_mul hγ]

theorem levi2Mat_g2T_mul_inv (s : Fˣ × Fˣ) : levi2Mat (g2T s) * levi2Mat (g2T s⁻¹) = 1 := by
  have h1 : (s.1 : F) ≠ 0 := s.1.ne_zero
  have h2 : (s.2 : F) ≠ 0 := s.2.ne_zero
  rw [levi2Mat_g2T, levi2Mat_g2T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem g2T_conj_mem_stabV0 (s : Fˣ × Fˣ) {γ : ↥(cayleyGroup F)} (hγ : γ ∈ stabV0 F) :
    g2T s * γ * (g2T s)⁻¹ ∈ stabV0 F := by
  have hγ' := mem_stabV0.mp hγ
  rw [mem_stabV0, ← map_inv, g2Act_mul_apply, g2Act_mul_apply, g2Act_g2T_eu, mul_one,
    show (eu 0 ((s⁻¹).1 : F) : Ix3 → F) = ((s⁻¹).1 : F) • eu 0 1 by rw [smul_eu, mul_one],
    g2Act_smul, hγ', g2Act_smul, g2Act_g2T_eu, smul_eu]
  congr 1
  simp

theorem map_conj_eq_of_mem {G : Type*} [Group G] {S : Subgroup G} {d : G} (hd : d ∈ S) :
    S.map (MulAut.conj d).toMonoidHom = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem hd hy) (S.inv_mem hd)
  · intro hx
    refine ⟨d⁻¹ * x * d, S.mul_mem (S.mul_mem (S.inv_mem hd) hx) hd, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem g2T_conj_mem_gam2 (s : Fˣ × Fˣ) {γ : ↥(cayleyGroup F)}
    (hγ : γ ∈ perfectCore (stabQ (stdF F 2))) :
    g2T s * γ * (g2T s)⁻¹ ∈ perfectCore (stabQ (stdF F 2)) := by
  have h1 : g2T s * γ * (g2T s)⁻¹ ∈
      (perfectCore (stabQ (stdF F 2))).map (MulAut.conj (g2T s)).toMonoidHom := ⟨γ, hγ, rfl⟩
  rwa [← perfectCore_map _ (MulAut.conj (g2T s)).injective,
    map_conj_eq_of_mem (g2T_mem_stabQ s 2)] at h1

theorem g2T_conj_mem_pCoreOf_stabV0 [Finite F] (s : Fˣ × Fˣ) {k : ↥(cayleyGroup F)}
    (hk : k ∈ pCoreOf 2 (stabV0 F)) : g2T s * k * (g2T s)⁻¹ ∈ pCoreOf 2 (stabV0 F) := by
  rw [mem_pCoreOf_stabV0_iff] at hk ⊢
  refine ⟨g2T_conj_mem_stabV0 s hk.1, ?_⟩
  rw [levi1Mat_conj_g2T s hk.1, hk.2, mul_one, levi1Mat_g2T_mul_inv]

theorem g2T_conj_mem_pCoreOf_gam2 [Finite F] (h4 : 4 ≤ Nat.card F) (s : Fˣ × Fˣ)
    {k : ↥(cayleyGroup F)} (hk : k ∈ pCoreOf 2 (perfectCore (stabQ (stdF F 2)))) :
    g2T s * k * (g2T s)⁻¹ ∈ pCoreOf 2 (perfectCore (stabQ (stdF F 2))) := by
  rw [mem_pCoreOf_gam2_iff h4] at hk ⊢
  refine ⟨g2T_conj_mem_gam2 s hk.1, ?_⟩
  rw [levi2Mat_conj_g2T s (perfectCore_le _ hk.1), hk.2, mul_one, levi2Mat_g2T_mul_inv]

omit [CharP F 2] in
theorem g2T_mem_normalizer {X : Subgroup ↥(cayleyGroup F)}
    (hX : ∀ (s : Fˣ × Fˣ) (x : ↥(cayleyGroup F)), x ∈ X → g2T s * x * (g2T s)⁻¹ ∈ X)
    (s : Fˣ × Fˣ) : g2T s ∈ Subgroup.normalizer (X : Set ↥(cayleyGroup F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hX s x, fun h => ?_⟩
  have h1 := hX s⁻¹ _ h
  rwa [map_inv, inv_inv, show (g2T s)⁻¹ * (g2T s * x * (g2T s)⁻¹) * g2T s = x by group] at h1

@[expose] def torHomC1 (F : Type) [Field F] : Fˣ →* Fˣ × Fˣ where
  toFun c := (c⁻¹ * c⁻¹, c)
  map_one' := by simp
  map_mul' a b := by
    ext
    · simp only [mul_inv, Prod.fst_mul, Units.val_mul]
      ring
    · rfl

@[expose] def torHom2 (F : Type) [Field F] : Fˣ →* Fˣ × Fˣ where
  toFun c := (c, c⁻¹ * c⁻¹)
  map_one' := by simp
  map_mul' a b := by
    ext
    · rfl
    · simp only [mul_inv, Prod.snd_mul, Units.val_mul]
      ring

omit [CharP F 2] in
theorem torHomC1_apply (c : Fˣ) : torHomC1 F c = (c⁻¹ * c⁻¹, c) := rfl

omit [CharP F 2] in
theorem torHom2_apply (c : Fˣ) : torHom2 F c = (c, c⁻¹ * c⁻¹) := rfl

theorem levi1Mat_g2T_torHomC1 (c : Fˣ) :
    levi1Mat (g2T (torHomC1 F c)) = (c : F)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [levi1Mat_g2T, torHomC1_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem levi2Mat_g2T_inl (c : Fˣ) :
    levi2Mat (g2T (c, 1)) = (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [levi2Mat_g2T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem card_range_g2T_comp [Finite F] (φ : Fˣ →* Fˣ × Fˣ) (hφ : Function.Injective φ) :
    Nat.card ↥((g2T (F := F)).comp φ).range = Nat.card F - 1 := by
  have hinj : Function.Injective ((g2T (F := F)).comp φ) := g2T_injective.comp hφ
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]

theorem g2T_mem_stabV0_iff (s : Fˣ × Fˣ) : g2T s ∈ stabV0 F ↔ s.1 = 1 := by
  rw [mem_stabV0, g2Act_g2T_eu, mul_one]
  constructor
  · intro h
    have h1 := congrFun h (.inl 0)
    simpa [eu] using h1
  · intro h
    rw [h, Units.val_one]

theorem torusG_inf_stabV0 :
    torusG F ⊓ stabV0 F = ((g2T (F := F)).comp (MonoidHom.inr Fˣ Fˣ)).range := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    have h1 := (g2T_mem_stabV0_iff s).mp hs
    refine ⟨s.2, ?_⟩
    change g2T (1, s.2) = g2T s
    rw [← h1]
  · rintro ⟨c, rfl⟩
    exact ⟨⟨_, rfl⟩, (g2T_mem_stabV0_iff (1, c)).mpr rfl⟩

theorem card_torusG_inf_stabV0 [Finite F] : Nat.card ↥(torusG F ⊓ stabV0 F) = Nat.card F - 1 := by
  rw [torusG_inf_stabV0, card_range_g2T_comp _ fun a b h => (Prod.ext_iff.mp h).2]

theorem cayley_ext {g h : ↥(cayleyGroup F)} (H : ∀ w, g2Act g w = g2Act h w) : g = h := by
  have h1 : h⁻¹ * g = 1 := cayley_eq_one fun w => by rw [g2Act_mul_apply, H, g2Act_inv_apply]
  exact (inv_mul_eq_one.mp h1).symm

theorem g2Act_swapW (a b k d e f : F) :
    g2Act (g2Y ![0, 1, 0] * g2X ![0, 1, 0] * g2Y ![0, 1, 0]) (q6 a b k d e f) =
      q6 f e d k b a := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_y1q, g2Act_x1q, g2Act_y1q]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination (a + f) * h2
  · linear_combination b * h2
  · linear_combination (k + d) * h2
  · linear_combination d * h2
  · linear_combination (e + b) * h2
  · linear_combination f * h2

theorem g2Act_wElt {c : F} (hc : c ≠ 0) (a b k d e f : F) :
    g2Act (g2Y ![0, c, 0] * g2X ![0, c⁻¹, 0] * g2Y ![0, c, 0]) (q6 a b k d e f) =
      q6 (c * f) (c⁻¹ * c⁻¹ * e) (c * d) (c⁻¹ * k) (c * c * b) (c⁻¹ * a) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hu : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_y1q, g2Act_x1q, g2Act_y1q]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination (a + c * f) * h2 + (a + c * f) * hu
  · linear_combination b * h2 + b * (c * c⁻¹ + 1) * hu
  · linear_combination (k + c * d) * h2 + (k + c * d) * hu
  · linear_combination d * h2 + d * hu
  · linear_combination (e + c * c * b) * h2 + (e + c * c * b) * (c * c⁻¹ + 1) * hu
  · linear_combination f * h2 + f * hu

theorem g2T_torHom2_eq (c : Fˣ) :
    g2T (torHom2 F c) = g2Y ![0, (c : F), 0] * g2X ![0, (c : F)⁻¹, 0] * g2Y ![0, (c : F), 0] *
      (g2Y ![0, 1, 0] * g2X ![0, 1, 0] * g2Y ![0, 1, 0]) := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  apply cayley_ext
  intro w
  rw [q6_eta w, g2Act_mul_apply (g2Y _ * _ * _), g2Act_swapW, g2Act_wElt hc, g2Act_g2T,
    torHom2_apply]
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2, Units.val_mul, Units.val_inv_eq_inv_val]
  refine q6_congr rfl rfl ?_ rfl ?_ ?_
  · field_simp
  · field_simp
  · field_simp

theorem g2T_torHom2_mem_sl2E1 (c : Fˣ) : g2T (torHom2 F c) ∈ sl2E1 F := by
  rw [g2T_torHom2_eq]
  have hX : ∀ t : F, g2X ![0, t, 0] ∈ sl2E1 F := fun t => Subgroup.subset_closure ⟨t, Or.inl rfl⟩
  have hY : ∀ t : F, g2Y ![0, t, 0] ∈ sl2E1 F := fun t => Subgroup.subset_closure ⟨t, Or.inr rfl⟩
  exact mul_mem (mul_mem (mul_mem (hY _) (hX _)) (hY _)) (mul_mem (mul_mem (hY _) (hX _)) (hY _))

theorem sl2E1_le_gam2 [Finite F] (h3 : 2 < Nat.card F) :
    sl2E1 F ≤ perfectCore (stabQ (stdF F 2)) := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one h3
  exact le_perfectCore_of_perfect sl2E1_le_stabQ (sl2E1_perfect hc0 hc1)

theorem torusG_inf_gam2 [Finite F] (h3 : 2 < Nat.card F) :
    torusG F ⊓ perfectCore (stabQ (stdF F 2)) = ((g2T (F := F)).comp (torHom2 F)).range := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    have hdet := (perfectCore_stabQ_two_le hs).2
    rw [levi2Mat_g2T, det_fin_two_of, mul_zero, sub_zero] at hdet
    refine ⟨s.1, ?_⟩
    change g2T (torHom2 F s.1) = g2T s
    congr 1
    refine Prod.ext rfl (Units.ext ?_)
    rw [torHom2_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have h1 : (s.1 : F) ≠ 0 := s.1.ne_zero
    field_simp
    linear_combination -hdet
  · rintro ⟨c, rfl⟩
    exact ⟨⟨_, rfl⟩, sl2E1_le_gam2 h3 (g2T_torHom2_mem_sl2E1 c)⟩

theorem card_torusG_inf_gam2 [Finite F] (h3 : 2 < Nat.card F) :
    Nat.card ↥(torusG F ⊓ perfectCore (stabQ (stdF F 2))) = Nat.card F - 1 := by
  rw [torusG_inf_gam2 h3, card_range_g2T_comp _ fun a b h => (Prod.ext_iff.mp h).1]

theorem torusG_inf_sc1 [Finite F] :
    torusG F ⊓ sectionCentralizer (stabV0 F) (pCoreOf 2 (stabV0 F)) =
      ((g2T (F := F)).comp (torHomC1 F)).range := by
  have hγ₀ : g2A (uSL 0 0 (1 : F)) ∈ stabV0 F := U0_le_stabV0 (g2A_mem_U0 0 0 1)
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, -, -, hc⟩
    have h1 := hc _ hγ₀
    rw [mem_pCoreOf_stabV0_iff] at h1
    obtain ⟨hS, hM⟩ := h1
    have hA : g2T s * g2A (uSL 0 0 1) * (g2T s)⁻¹ ∈ stabV0 F := g2T_conj_mem_stabV0 s hγ₀
    have hM' : levi1Mat (g2T s * g2A (uSL 0 0 1) * (g2T s)⁻¹) =
        levi1Mat (g2A (uSL 0 0 (1 : F))) := by
      have e := levi1Mat_mul hS hγ₀
      rw [show g2T s * g2A (uSL 0 0 1) * (g2T s)⁻¹ * (g2A (uSL 0 0 1))⁻¹ * g2A (uSL 0 0 1) =
        g2T s * g2A (uSL 0 0 1) * (g2T s)⁻¹ by group, hM, one_mul] at e
      exact e
    rw [levi1Mat_conj_g2T s hγ₀, levi1Mat_g2T, levi1Mat_g2T, levi1Mat_uSL] at hM'
    have e10 := congrFun (congrFun hM' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e10
    refine ⟨s.2, ?_⟩
    change g2T (torHomC1 F s.2) = g2T s
    congr 1
    refine Prod.ext (Units.ext ?_) rfl
    rw [torHomC1_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have h2 : (s.2 : F) ≠ 0 := s.2.ne_zero
    field_simp
    linear_combination -e10
  · rintro ⟨c, rfl⟩
    have hsc : ∀ γ ∈ stabV0 F,
        levi1Mat (g2T (torHomC1 F c) * γ * (g2T (torHomC1 F c))⁻¹) = levi1Mat γ := by
      intro γ hγ
      have hc : (c : F) ≠ 0 := c.ne_zero
      rw [levi1Mat_conj_g2T _ hγ, ← map_inv, levi1Mat_g2T_torHomC1, levi1Mat_g2T_torHomC1,
        Units.val_inv_eq_inv_val, inv_inv]
      simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, smul_smul]
      rw [mul_inv_cancel₀ hc, one_smul]
    refine ⟨⟨_, rfl⟩, g2T_mem_normalizer (fun s x hx => g2T_conj_mem_stabV0 s hx) _,
      g2T_mem_normalizer (fun s x hx => g2T_conj_mem_pCoreOf_stabV0 s hx) _, fun γ hγ => ?_⟩
    have hA := g2T_conj_mem_stabV0 (torHomC1 F c) hγ
    rw [mem_pCoreOf_stabV0_iff]
    refine ⟨(stabV0 F).mul_mem hA ((stabV0 F).inv_mem hγ), ?_⟩
    change levi1Mat (g2T (torHomC1 F c) * γ * (g2T (torHomC1 F c))⁻¹ * γ⁻¹) = 1
    rw [levi1Mat_mul hA ((stabV0 F).inv_mem hγ), hsc γ hγ,
      ← levi1Mat_mul hγ ((stabV0 F).inv_mem hγ), mul_inv_cancel, levi1Mat_one]

theorem card_torusG_inf_sc1 [Finite F] :
    Nat.card ↥(torusG F ⊓ sectionCentralizer (stabV0 F) (pCoreOf 2 (stabV0 F))) =
      Nat.card F - 1 := by
  rw [torusG_inf_sc1, card_range_g2T_comp _ fun a b h => (Prod.ext_iff.mp h).2]

theorem snd_eq_one_of_mem_sc2 [Finite F] (h4 : 4 ≤ Nat.card F) {s : Fˣ × Fˣ}
    (hs : g2T s ∈ sectionCentralizer (perfectCore (stabQ (stdF F 2)))
      (pCoreOf 2 (perfectCore (stabQ (stdF F 2))))) : s.2 = 1 := by
  have hγ₀ : g2Y ![0, (1 : F), 0] ∈ perfectCore (stabQ (stdF F 2)) :=
    sl2E1_le_gam2 (by omega) (Subgroup.subset_closure ⟨1, Or.inr rfl⟩)
  have hγ₀Q := perfectCore_le _ hγ₀
  obtain ⟨-, -, hc⟩ := hs
  have h1 := hc _ hγ₀
  rw [mem_pCoreOf_gam2_iff h4] at h1
  obtain ⟨hS, hM⟩ := h1
  have hM' : levi2Mat (g2T s * g2Y ![0, 1, 0] * (g2T s)⁻¹) =
      levi2Mat (g2Y ![0, (1 : F), 0]) := by
    have e := levi2Mat_mul (g := g2T s * g2Y ![0, 1, 0] * (g2T s)⁻¹ * (g2Y ![0, 1, 0])⁻¹) hγ₀Q
    rw [show g2T s * g2Y ![0, 1, 0] * (g2T s)⁻¹ * (g2Y ![0, 1, 0])⁻¹ * g2Y ![0, 1, 0] =
      g2T s * g2Y ![0, 1, 0] * (g2T s)⁻¹ by group, hM, one_mul] at e
    exact e
  rw [levi2Mat_conj_g2T s hγ₀Q, levi2Mat_g2T, levi2Mat_g2T, levi2Mat_y1] at hM'
  have e01 := congrFun (congrFun hM' 0) 1
  have h1 : (s.1 : F) ≠ 0 := s.1.ne_zero
  simp [Matrix.mul_apply, Fin.sum_univ_two, h1] at e01
  simpa using e01

theorem torusG_inf_sc2 [Finite F] (h4 : 4 ≤ Nat.card F) :
    torusG F ⊓ sectionCentralizer (perfectCore (stabQ (stdF F 2)))
      (pCoreOf 2 (perfectCore (stabQ (stdF F 2)))) =
      ((g2T (F := F)).comp (MonoidHom.inl Fˣ Fˣ)).range := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    have h1 := snd_eq_one_of_mem_sc2 h4 hs
    refine ⟨s.1, ?_⟩
    change g2T (s.1, 1) = g2T s
    rw [← h1]
  · rintro ⟨c, rfl⟩
    have hsc : ∀ γ ∈ stabQ (stdF F 2),
        levi2Mat (g2T (c, 1) * γ * (g2T (c, 1))⁻¹) = levi2Mat γ := by
      intro γ hγ
      have hc : (c : F) ≠ 0 := c.ne_zero
      rw [levi2Mat_conj_g2T _ hγ, Prod.inv_mk, inv_one, levi2Mat_g2T_inl, levi2Mat_g2T_inl,
        Units.val_inv_eq_inv_val]
      simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, smul_smul]
      rw [inv_mul_cancel₀ hc, one_smul]
    refine ⟨⟨(c, 1), rfl⟩, g2T_mem_normalizer (fun s x hx => g2T_conj_mem_gam2 s hx) _,
      g2T_mem_normalizer (fun s x hx => g2T_conj_mem_pCoreOf_gam2 h4 s hx) _, fun γ hγ => ?_⟩
    have hA := g2T_conj_mem_gam2 (c, 1) hγ
    have hγQ := perfectCore_le _ hγ
    have hγiQ := (stabQ (stdF F 2)).inv_mem hγQ
    rw [mem_pCoreOf_gam2_iff h4]
    refine ⟨(perfectCore (stabQ (stdF F 2))).mul_mem hA
      ((perfectCore (stabQ (stdF F 2))).inv_mem hγ), ?_⟩
    change levi2Mat (g2T (c, 1) * γ * (g2T (c, 1))⁻¹ * γ⁻¹) = 1
    rw [levi2Mat_mul hγiQ, hsc γ hγQ, ← levi2Mat_mul hγiQ, mul_inv_cancel, levi2Mat_one]

theorem card_torusG_inf_sc2 [Finite F] (h4 : 4 ≤ Nat.card F) :
    Nat.card ↥(torusG F ⊓ sectionCentralizer (perfectCore (stabQ (stdF F 2)))
      (pCoreOf 2 (perfectCore (stabQ (stdF F 2))))) = Nat.card F - 1 := by
  rw [torusG_inf_sc2 h4, card_range_g2T_comp _ fun a b h => (Prod.ext_iff.mp h).1]

theorem torusG_le_sc1_sup [Finite F] :
    torusG F ≤ (torusG F ⊓ sectionCentralizer (stabV0 F) (pCoreOf 2 (stabV0 F))) ⊔
      (torusG F ⊓ stabV0 F) := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((s.1 : F)⁻¹)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, inv_eq_zero] at hr
    exact s.1.ne_zero hr
  set b : Fˣ := Units.mk0 r hr0 with hb
  have hs : s = torHomC1 F b * MonoidHom.inr Fˣ Fˣ (b⁻¹ * s.2) := by
    refine Prod.ext (Units.ext ?_) ?_
    · rw [Prod.fst_mul, torHomC1_apply, MonoidHom.inr_apply, mul_one, Units.val_mul,
        Units.val_inv_eq_inv_val, hb, Units.val_mk0, ← mul_inv, ← hr, inv_inv]
    · rw [Prod.snd_mul, torHomC1_apply, MonoidHom.inr_apply, mul_inv_cancel_left]
  rw [hs, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · rw [torusG_inf_sc1]
    exact ⟨b, rfl⟩
  · rw [torusG_inf_stabV0]
    exact ⟨b⁻¹ * s.2, rfl⟩

theorem torusG_le_sup12 [Finite F] (h3 : 2 < Nat.card F) :
    torusG F ≤ (torusG F ⊓ stabV0 F) ⊔ (torusG F ⊓ perfectCore (stabQ (stdF F 2))) := by
  rintro _ ⟨s, rfl⟩
  have hs : s = MonoidHom.inr Fˣ Fˣ (s.2 * s.1 * s.1) * torHom2 F s.1 := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, MonoidHom.inr_apply, torHom2_apply, one_mul]
    · rw [Prod.snd_mul, MonoidHom.inr_apply, torHom2_apply]
      group
  rw [hs, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · rw [torusG_inf_stabV0]
    exact ⟨_, rfl⟩
  · rw [torusG_inf_gam2 h3]
    exact ⟨s.1, rfl⟩

theorem torusG_inf_inf_sc2 [Finite F] (h4 : 4 ≤ Nat.card F) :
    torusG F ⊓ stabV0 F ⊓ sectionCentralizer (perfectCore (stabQ (stdF F 2)))
      (pCoreOf 2 (perfectCore (stabQ (stdF F 2)))) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨⟨s, rfl⟩, hs1⟩, hs2⟩
  have h1 := (g2T_mem_stabV0_iff s).mp hs1
  have h2 := snd_eq_one_of_mem_sc2 h4 hs2
  rw [Subgroup.mem_bot, show s = 1 from Prod.ext h1 h2, map_one]

theorem torusG_inf_sc1_le_gam2 [Finite F] (hq : Nat.card F = 4) :
    torusG F ⊓ sectionCentralizer (stabV0 F) (pCoreOf 2 (stabV0 F)) ≤
      perfectCore (stabQ (stdF F 2)) := by
  rw [torusG_inf_sc1]
  rintro _ ⟨b, rfl⟩
  have hb3 : b ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Fˣ) (x := b)
    rwa [Nat.card_units, hq] at h
  have hb : torHomC1 F b = torHom2 F (b⁻¹ * b⁻¹) := by
    rw [torHomC1_apply, torHom2_apply]
    refine Prod.ext rfl ?_
    rw [mul_inv, inv_inv]
    calc b = b * b ^ 3 := by rw [hb3, mul_one]
      _ = b * b * (b * b) := by
        rw [pow_succ, pow_succ, pow_one]
        simp only [mul_assoc]
  change g2T (torHomC1 F b) ∈ _
  rw [hb]
  exact sl2E1_le_gam2 (by omega) (g2T_torHom2_mem_sl2E1 _)

end CFSG.Quasithin.Vol2.Ch11.G2Q8
