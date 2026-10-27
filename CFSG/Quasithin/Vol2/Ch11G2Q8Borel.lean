module

public import CFSG.Quasithin.Vol2.Ch11G2Q8NatPoint
public import CFSG.Quasithin.Vol2.Ch11G2Q8Levi2
public import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

theorem g2Act_g2T (s : Fˣ × Fˣ) (w : Ix3 → F) :
    g2Act (g2T s) w = q6 ((s.1 : F) * w (.inl 0)) ((s.2 : F) * w (.inl 1))
      (((s.1 : F) * s.2)⁻¹ * w (.inl 2)) ((s.1 : F)⁻¹ * w (.inr 0)) ((s.2 : F)⁻¹ * w (.inr 1))
      ((s.1 : F) * s.2 * w (.inr 2)) := by
  have h1 : (s.1 : F) ≠ 0 := s.1.ne_zero
  have h2 : (s.2 : F) ≠ 0 := s.2.ne_zero
  conv_lhs => rw [q6_eta w]
  rw [g2T_apply, g2Act_diag3]
  refine q6_congr rfl rfl rfl ?_ ?_ rfl
  · field_simp
  · field_simp

theorem g2Act_g2T_eu (s : Fˣ × Fˣ) (t : F) : g2Act (g2T s) (eu 0 t) = eu 0 ((s.1 : F) * t) := by
  rw [g2Act_g2T]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [eu, q6]

theorem g2T_inF (s : Fˣ × Fˣ) {h : ℕ} (w : Ix3 → F) : InF h (g2Act (g2T s) w) ↔ InF h w := by
  rw [g2Act_g2T]
  conv_rhs => rw [q6_eta w]
  rw [inF_q6_iff, inF_q6_iff]
  simp only [mul_eq_zero, inv_eq_zero, Units.ne_zero, false_or]

theorem g2T_conj_mem_U0 (s : Fˣ × Fˣ) {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    g2T s * u * (g2T s)⁻¹ ∈ U0 F := by
  refine mem_U0.mpr fun h w hw => ?_
  rw [← map_inv, g2Act_mul_apply, g2Act_mul_apply]
  have h1 : InF (h + 1) (g2Act (g2T s⁻¹) w) := (g2T_inF _ w).mpr hw
  have h2 := (mem_U0.mp hu) h _ h1
  have e : g2Act (g2T s) (g2Act u (g2Act (g2T s⁻¹) w)) - w =
      g2Act (g2T s) (g2Act u (g2Act (g2T s⁻¹) w) - g2Act (g2T s⁻¹) w) := by
    rw [map_sub, map_inv, g2Act_apply_inv]
  rw [e]
  exact (g2T_inF s _).mpr h2

theorem g2T_mem_normalizer_U0 (s : Fˣ × Fˣ) :
    g2T s ∈ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨g2T_conj_mem_U0 s, fun h => ?_⟩
  have h1 := g2T_conj_mem_U0 s⁻¹ h
  rwa [map_inv, inv_inv, show (g2T s)⁻¹ * (g2T s * u * (g2T s)⁻¹) * g2T s = u by group] at h1

@[expose] noncomputable def torusG (F : Type) [Field F] [CharP F 2] :
    Subgroup ↥(cayleyGroup F) :=
  (g2T (F := F)).range

theorem torusG_le_normalizer : torusG F ≤ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
  rintro _ ⟨s, rfl⟩
  exact g2T_mem_normalizer_U0 s

theorem g2T_injective : Function.Injective (g2T (F := F)) := by
  intro s s' h
  have e1 := congrArg (fun g => g2Act g (q6 (1 : F) 0 0 0 0 0)) h
  have e2 := congrArg (fun g => g2Act g (q6 (0 : F) 1 0 0 0 0)) h
  simp only [g2Act_g2T] at e1 e2
  obtain ⟨a1, -, -, -, -, -⟩ := q6_inj e1
  obtain ⟨-, a2, -, -, -, -⟩ := q6_inj e2
  simp only [q6_apply_inl0, q6_apply_inl1, mul_one] at a1 a2
  exact Prod.ext (Units.ext a1) (Units.ext a2)

theorem card_torusG [Finite F] : Nat.card ↥(torusG F) = (Nat.card F - 1) ^ 2 := by
  rw [torusG, ← Nat.card_congr (MonoidHom.ofInjective g2T_injective).toEquiv, Nat.card_prod,
    Nat.card_units, sq]

theorem odd_card_torusG [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    Odd (Nat.card ↥(torusG F)) := by
  rw [card_torusG, hF]
  refine Odd.pow (Nat.Even.sub_odd (Nat.one_le_two_pow) ?_ odd_one)
  exact Nat.even_pow.mpr ⟨even_two, by omega⟩

theorem U0_fix_one {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) {w : Ix3 → F} (hw : w ∈ stdF F 1) :
    g2Act u w = w :=
  sub_eq_zero.mp (eq_zero_of_inF_zero ((mem_U0.mp hu) 0 w hw))

theorem g2Act_mem_stdF_one_of_normalizer {b : ↥(cayleyGroup F)}
    (hb : b ∈ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F))) {w : Ix3 → F}
    (hw : w ∈ stdF F 1) : g2Act b w ∈ stdF F 1 := by
  refine fixed_U0 fun u hu => ?_
  have hu' : b⁻¹ * u * b ∈ U0 F := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) u).mp hu
    rwa [inv_inv] at this
  have h1 := U0_fix_one hu' hw
  rw [g2Act_mul_apply, g2Act_mul_apply] at h1
  calc g2Act u (g2Act b w) = g2Act b (g2Act b⁻¹ (g2Act u (g2Act b w))) :=
        (g2Act_apply_inv b _).symm
    _ = g2Act b w := by rw [h1]

theorem exists_smul_of_mem_normalizer {b : ↥(cayleyGroup F)}
    (hb : b ∈ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F))) :
    ∃ c : F, c ≠ 0 ∧ g2Act b (eu 0 1) = c • eu 0 1 := by
  obtain ⟨c, hc⟩ := mem_stdF_one_iff.mp
    (g2Act_mem_stdF_one_of_normalizer hb (mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩))
  refine ⟨c, fun h0 => g2Act_eu_ne_zero b ?_, hc⟩
  rw [hc, h0, zero_smul]

theorem levi1Mat_00 (g : ↥(cayleyGroup F)) :
    levi1Mat g 0 0 = g2Act g (q6 0 0 0 0 1 0) (.inr 1) := by
  simp [levi1Mat_apply, vpart]

theorem levi1Mat_01 (g : ↥(cayleyGroup F)) :
    levi1Mat g 0 1 = g2Act g (q6 0 0 0 0 0 1) (.inr 1) := by
  simp [levi1Mat_apply, vpart]

theorem levi1Mat_11 (g : ↥(cayleyGroup F)) :
    levi1Mat g 1 1 = g2Act g (q6 0 0 0 0 0 1) (.inr 2) := by
  simp [levi1Mat_apply, vpart]

theorem levi1Mat_g2T (s : Fˣ × Fˣ) :
    levi1Mat (g2T s) = !![(s.2 : F)⁻¹, 0; 0, (s.1 : F) * s.2] := by
  ext i j
  rw [levi1Mat_apply, g2Act_g2T]
  fin_cases i <;> fin_cases j <;> simp [vpart, q6]

theorem levi1Mat_U0 {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    levi1Mat u 0 0 = 1 ∧ levi1Mat u 0 1 = 0 ∧ levi1Mat u 1 1 = 1 := by
  have h1 := (mem_U0.mp hu) 2 (q6 0 0 0 0 1 0) (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
  have h2 := (mem_U0.mp hu) 1 (q6 0 0 0 0 0 1) (mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩)
  have e1 := h1 (.inr 1) (by decide)
  have e2 := h2 (.inr 1) (by decide)
  have e3 := h2 (.inr 2) (by decide)
  simp only [Pi.sub_apply, sub_eq_zero, q6_apply_inr1, q6_apply_inr2] at e1 e2 e3
  exact ⟨by rw [levi1Mat_00, e1], by rw [levi1Mat_01, e2], by rw [levi1Mat_11, e3]⟩

theorem levi1Mat_uSL (t : F) : levi1Mat (g2A (uSL 0 0 t)) = !![1, 0; t, 1] := by
  rw [levi1Mat_g2A (uSL_mulVec_e0 0 0 t)]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem levi1Mat_01_eq_zero {b : ↥(cayleyGroup F)} (hb : b ∈ stabV0 F)
    (hbN : b ∈ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F))) : levi1Mat b 0 1 = 0 := by
  have hu : g2A (uSL 0 0 (1 : F)) ∈ U0 F := g2A_mem_U0 0 0 1
  have huS : g2A (uSL 0 0 (1 : F)) ∈ stabV0 F := U0_le_stabV0 hu
  have hc : b * g2A (uSL 0 0 1) * b⁻¹ ∈ U0 F := (Subgroup.mem_normalizer_iff.mp hbN _).mp hu
  have hcS : b * g2A (uSL 0 0 1) * b⁻¹ ∈ stabV0 F := U0_le_stabV0 hc
  obtain ⟨l00, l01, -⟩ := levi1Mat_U0 hc
  have e : levi1Mat (b * g2A (uSL 0 0 1)) =
      levi1Mat (b * g2A (uSL 0 0 1) * b⁻¹) * levi1Mat b := by
    rw [← levi1Mat_mul hcS hb, show b * g2A (uSL 0 0 1) * b⁻¹ * b = b * g2A (uSL 0 0 1) by group]
  rw [levi1Mat_mul hb huS, levi1Mat_uSL] at e
  have e00 := congrFun (congrFun e 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, l00, l01] at e00
  simp at e00
  linear_combination e00

theorem inv_mul_mem_U0_of_levi1Mat {x y : ↥(cayleyGroup F)} (hx : x ∈ stabV0 F) (hy : y ∈ U0 F)
    (h : levi1Mat x = levi1Mat y) : y⁻¹ * x ∈ U0 F := by
  have hyS := U0_le_stabV0 hy
  have hk : levi1 (⟨y⁻¹ * x, (stabV0 F).mul_mem ((stabV0 F).inv_mem hyS) hx⟩ : ↥(stabV0 F)) =
      1 := by
    apply Subtype.ext
    rw [levi1_apply, Matrix.SpecialLinearGroup.coe_one]
    change levi1Mat (y⁻¹ * x) = 1
    rw [levi1Mat_mul ((stabV0 F).inv_mem hyS) hx, h, ← levi1Mat_mul ((stabV0 F).inv_mem hyS) hyS,
      inv_mul_cancel, levi1Mat_one]
  have h1 := ker_levi1_le hk
  exact h1

theorem normalizer_U0_le :
    Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) ≤ U0 F ⊔ torusG F := by
  intro b hb
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_normalizer hb
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : Fˣ × Fˣ, s₁ = (Units.mk0 c hc0, 1) := ⟨_, rfl⟩
  have hN₁ : (g2T s₁)⁻¹ ∈ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) :=
    Subgroup.inv_mem _ (g2T_mem_normalizer_U0 s₁)
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = (g2T s₁)⁻¹ * b := ⟨_, rfl⟩
  have hb₁N : b₁ ∈ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
    rw [hb₁]
    exact Subgroup.mul_mem _ hN₁ hb
  have hb₁S : b₁ ∈ stabV0 F := by
    rw [mem_stabV0, hb₁, g2Act_mul_apply, hc, g2Act_smul, ← map_inv, g2Act_g2T_eu, smul_eu]
    congr 1
    simp [hs₁, hc0]
  have h01 := levi1Mat_01_eq_zero hb₁S hb₁N
  have hdet := det_levi1Mat hb₁S
  rw [det_fin_two, h01, zero_mul, sub_zero] at hdet
  have hx0 : levi1Mat b₁ 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  obtain ⟨s₂, hs₂⟩ : ∃ s₂ : Fˣ × Fˣ, s₂ = (1, Units.mk0 (levi1Mat b₁ 0 0) hx0) := ⟨_, rfl⟩
  have ht₂S : g2T s₂ ∈ stabV0 F := by
    rw [mem_stabV0, g2Act_g2T_eu]
    simp [hs₂]
  obtain ⟨r, hr⟩ : ∃ r : F, r = levi1Mat b₁ 0 0 * levi1Mat b₁ 1 0 := ⟨_, rfl⟩
  have hu₂ : g2A (uSL 0 0 r) ∈ U0 F := g2A_mem_U0 0 0 _
  have hM : levi1Mat (g2T s₂ * b₁) = levi1Mat (g2A (uSL 0 0 r)) := by
    rw [levi1Mat_mul ht₂S hb₁S, levi1Mat_g2T, levi1Mat_uSL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hs₂, h01, hx0, hdet, hr]
  have hb₃ := inv_mul_mem_U0_of_levi1Mat ((stabV0 F).mul_mem ht₂S hb₁S) hu₂ hM
  have hbeq : b = g2T s₁ * (g2T s₂)⁻¹ * (g2A (uSL 0 0 r) * ((g2A (uSL 0 0 r))⁻¹ *
      (g2T s₂ * b₁))) := by
    rw [hb₁]
    group
  rw [hbeq]
  refine Subgroup.mul_mem _ (le_sup_right (a := U0 F) ?_) (le_sup_left (b := torusG F) ?_)
  · exact Subgroup.mul_mem _ ⟨s₁, rfl⟩ (Subgroup.inv_mem _ ⟨s₂, rfl⟩)
  · exact Subgroup.mul_mem _ hu₂ hb₃

theorem normalizer_U0_eq :
    Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) = U0 F ⊔ torusG F :=
  le_antisymm normalizer_U0_le (sup_le (Subgroup.le_normalizer) torusG_le_normalizer)

variable [Finite F]

theorem U0_inf_eq_bot_of_odd {D : Subgroup ↥(cayleyGroup F)} (hD : Odd (Nat.card D)) :
    U0 F ⊓ D = ⊥ := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_U0 (F := F))
  exact (Subgroup.disjoint_of_coprime_natCard (by
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hD))).eq_bot

theorem exists_conj_torusG_of_isHall {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {D : Subgroup ↥(cayleyGroup F)}
    (hD : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf D
      (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)))) :
    ∃ x ∈ U0 F, D = (torusG F).map (MulAut.conj x).toMonoidHom := by
  have := finite_cayleyGroup (F := F)
  obtain ⟨hDB, hDodd, k, hk⟩ := hD
  have hU2 := isPGroup_U0 (F := F)
  have hUB : U0 F ≤ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := Subgroup.le_normalizer
  have hodd : Odd ((U0 F).relIndex (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)))) := by
    have h1 := not_two_dvd_index_U0 hF hn
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      h1 (h.trans (Subgroup.relIndex_dvd_index_of_le hUB)))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hUD := U0_inf_eq_bot_of_odd hDodd
  have hcU := Subgroup.relIndex_mul_card (U0 F) (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)))
  have hcD := Subgroup.relIndex_mul_card D (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)))
  rw [inf_of_le_left hUB, hm] at hcU
  rw [inf_of_le_left hDB, hk] at hcD
  have hmk : m = k := CFSG.Quasithin.Vol2.Ch11.SecA.eq_of_two_pow_mul_odd
    (m := (U0 F).relIndex (Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F))))
    (m' := Nat.card D) hodd hDodd (by rw [mul_comm, hcU, ← hcD])
  subst hmk
  have hB : Nat.card ↥(Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F))) =
      Nat.card ↥(U0 F) * Nat.card D := by
    rw [hm, ← hcD]
  have hUDs : U0 F ⊔ D = Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUB hDB) ?_
    rw [hB]
    refine Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_
      (Subgroup.card_dvd_of_le le_sup_left) (Subgroup.card_dvd_of_le le_sup_right))
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hDodd)
  exact CFSG.Quasithin.H13.exists_mem_conj_of_complements hUB le_rfl hU2 hodd
    torusG_le_normalizer (U0_inf_eq_bot_of_odd (odd_card_torusG hF hn)) normalizer_U0_eq.symm
    hDB hUD hUDs

end CFSG.Quasithin.Vol2.Ch11.G2Q8
