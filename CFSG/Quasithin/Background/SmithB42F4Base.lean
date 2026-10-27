module

public import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers

public section

namespace CFSG.Quasithin.B42F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom f4i)

section Classes

variable (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime]

@[expose] def IsZConj (y : ModGL F4.tag K) : Prop :=
  ∃ g ∈ F4.reeGamma K m, g * y * g⁻¹ = sylowH m K 0 1

@[expose] def IsTConj (y : ModGL F4.tag K) : Prop :=
  ∃ g ∈ F4.reeGamma K m, g * y * g⁻¹ = sylowL m K 1

variable {m K}

theorem IsZConj.conj {y g : ModGL F4.tag K} (hy : IsZConj m K y) (hg : g ∈ F4.reeGamma K m) :
    IsZConj m K (g * y * g⁻¹) := by
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨x * g⁻¹, mul_mem hx (inv_mem hg), ?_⟩
  rw [← hxy]
  group

theorem IsTConj.conj {y g : ModGL F4.tag K} (hy : IsTConj m K y) (hg : g ∈ F4.reeGamma K m) :
    IsTConj m K (g * y * g⁻¹) := by
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨x * g⁻¹, mul_mem hx (inv_mem hg), ?_⟩
  rw [← hxy]
  group

theorem IsTConj.of_conj {y g : ModGL F4.tag K} (hg : g ∈ F4.reeGamma K m)
    (hy : IsTConj m K (g * y * g⁻¹)) : IsTConj m K y := by
  have h := hy.conj (inv_mem hg)
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h

theorem isTConj_tOne : IsTConj m K (sylowL m K 1) :=
  ⟨1, one_mem _, by group⟩

theorem not_isZConj_of_isTConj
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {y : ModGL F4.tag K} (ht : IsTConj m K y) : ¬ IsZConj m K y := by
  rintro ⟨g, hg, hgy⟩
  obtain ⟨x, hx, hxy⟩ := ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hne⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  apply hne (x * g⁻¹) (mul_mem hx (inv_mem hg))
  rw [← sylowH_zero_eq_centralZ, ← hgy, ← hxy]
  group

theorem isZConj_or_isTConj (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    {y : ModGL F4.tag K} (hy : y ∈ F4.reeGamma K m) (hsq : y ^ 2 = 1) (hne : y ≠ 1) :
    IsZConj m K y ∨ IsTConj m K y :=
  (large_Ree_every_involution_fuses m hm K hK).1 y hy hsq hne

end Classes

section Coordinates

variable {m : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K F4.prime]

theorem isTConj_of_coord_zero_ne (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K}
    (hsq : sylowVec m K x ^ 2 = 1) (hx : x 0 ≠ 0) : IsTConj m K (sylowVec m K x) :=
  conj_tOne_of_coord_zero_ne hK hsq hx

theorem isTConj_sylowB_mul_sylowH (hK : Nat.card K = 2 ^ (2 * m + 1)) {c i : K} (hc : c ≠ 0)
    (hi : i ≠ 0) : IsTConj m K (sylowB m K 0 c * sylowH m K 0 i) := by
  obtain ⟨h, hh, hh'⟩ := exists_torus_conj_sylowB_mul_sylowH hK hc hi one_ne_zero one_ne_zero
  have hBU : sylowB m K 1 0 ∈ F4.reeGamma K m :=
    reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK 1 0))
  have hAU : sylowA m K 1 ∈ F4.reeGamma K m :=
    reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK 1))
  refine ⟨(sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h,
    mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hBU weylTwo_mem) hBU) hAU) weylOne_mem)
      (reeFixedTorus_le_reeGamma' hh), ?_⟩
  calc (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h *
        (sylowB m K 0 c * sylowH m K 0 i) *
          ((sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h)⁻¹ =
      (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) *
        (h * (sylowB m K 0 c * sylowH m K 0 i) * h⁻¹) *
          (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K)⁻¹ := by
        group
    _ = sylowL m K 1 := by rw [hh', fusion_word]

omit [Finite K] [CharP K F4.prime] in
theorem sylowV_eq_blocks_of_e (g i j k l : K) :
    sylowV m K 0 0 0 0 0 0 g 0 i j k l =
      sylowF m K 0 g * sylowH m K 0 i * sylowJ m K j * sylowK m K k * sylowL m K l := by
  rw [sylowV_blocks, sylowD_zero_zero, one_mul]

theorem isTConj_of_coord_nine_ne (hK : Nat.card K = 2 ^ (2 * m + 1)) {g i j k l : K}
    (hsq : sylowV m K 0 0 0 0 0 0 g 0 i j k l ^ 2 = 1) (hj : j ≠ 0) :
    IsTConj m K (sylowV m K 0 0 0 0 0 0 g 0 i j k l) := by
  have hvΓ := reeFixedPosUnipotent_le_reeGamma' (sylowV_mem (a := m) hK 0 0 0 0 0 0 g 0 i j k l)
  have hE : weylTwo K * sylowV m K 0 0 0 0 0 0 g 0 i j k l * (weylTwo K)⁻¹ =
      sylowD m K 0 g * sylowH m K 0 i * sylowA m K j * sylowL m K k * sylowK m K l := by
    rw [sylowV_eq_blocks_of_e, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul,
      weylTwo_conj_sylowF, weylTwo_conj_sylowH, weylTwo_conj_sylowJ, weylTwo_conj_sylowK,
      weylTwo_conj_sylowL]
  obtain ⟨-, ⟨hD1, -⟩, -, ⟨hH1, -⟩, -, ⟨hK1, -⟩, ⟨hL1, -⟩⟩ := blocks_mem (m := m) hK 0 g 0 i 0 l k
  have hU : ∀ {E : ModGL F4.tag K},
      E ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ →
        E ∈ posUnipotent F4.tag K := fun hE => (Subgroup.mem_inf.1 (complement_le_U _ hE)).1
  have hP : sylowD m K 0 g * sylowH m K 0 i ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ := mul_mem hD1 hH1
  have hEU := conj_mem_U hvΓ weylTwo_mem hE (mul_mem (mul_mem (mul_mem (hU hP)
    (Subgroup.mem_inf.1 (complement_le_U _ (sylowA_mem_complement_one hK j))).1) (hU hL1))
      (hU hK1))
  refine IsTConj.of_conj weylTwo_mem ?_
  rw [hE]
  refine conj_tOne_of_eq_sylowA_mul hK hEU (by rw [← hE]; exact conj_sq_eq_one hsq) hj
    (w := (sylowA m K j)⁻¹ * (sylowD m K 0 g * sylowH m K 0 i) * sylowA m K j *
      (sylowL m K k * sylowK m K l)) (mul_mem ?_ (mul_mem hL1 hK1)) (by group)
  have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer
    ⟨0, by decide⟩ (inv_mem (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK j)))) _).1 hP
  rwa [inv_inv] at this

theorem isTConj_sylowH_mul_sylowL (hK : Nat.card K = 2 ^ (2 * m + 1)) {i l : K} (hl : l ≠ 0) :
    IsTConj m K (sylowH m K 0 i * sylowL m K l) := by
  have hv : sylowH m K 0 i * sylowL m K l = sylowV m K 0 0 0 0 0 0 0 0 i 0 0 l := by
    rw [sylowV_eq_blocks_of_e, sylowF_zero_zero, sylowJ_zero, sylowK_zero, one_mul, mul_one,
      mul_one]
  have hsq : (sylowH m K 0 i * sylowL m K l) ^ 2 = 1 := by
    rw [hv]
    exact (sylowV_zero_zero_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _).2
      ⟨rfl, rfl, rfl, rfl, zero_mul _⟩
  have hvΓ : sylowH m K 0 i * sylowL m K l ∈ F4.reeGamma K m := by
    rw [hv]
    exact reeFixedPosUnipotent_le_reeGamma' (sylowV_mem (a := m) hK 0 0 0 0 0 0 0 0 i 0 0 l)
  set w := weylTwo K * weylOne K * weylTwo K with hw
  have hwΓ : w ∈ F4.reeGamma K m := mul_mem (mul_mem weylTwo_mem weylOne_mem) weylTwo_mem
  have hE : w * (sylowH m K 0 i * sylowL m K l) * w⁻¹ = sylowD m K 0 i * sylowA m K l := by
    rw [hw]
    calc weylTwo K * weylOne K * weylTwo K * (sylowH m K 0 i * sylowL m K l) *
          (weylTwo K * weylOne K * weylTwo K)⁻¹ =
        weylTwo K * (weylOne K * (weylTwo K * sylowH m K 0 i * (weylTwo K)⁻¹) *
          (weylOne K)⁻¹) * (weylTwo K)⁻¹ *
        (weylTwo K * (weylOne K * (weylTwo K * sylowL m K l * (weylTwo K)⁻¹) *
          (weylOne K)⁻¹) * (weylTwo K)⁻¹) := by group
      _ = _ := by
        rw [weylTwo_conj_sylowH, weylOne_conj_sylowH, weylTwo_conj_sylowF,
          weylTwo_conj_sylowL, weylOne_conj_sylowK, weylTwo_conj_sylowJ]
  obtain ⟨-, ⟨hD1, -⟩, -⟩ := blocks_mem (m := m) hK 0 i 0 0 0 0 0
  have hEU := conj_mem_U hvΓ hwΓ hE (mul_mem (Subgroup.mem_inf.1 (complement_le_U _ hD1)).1
    (Subgroup.mem_inf.1 (complement_le_U _ (sylowA_mem_complement_one hK l))).1)
  refine IsTConj.of_conj hwΓ ?_
  rw [hE]
  refine conj_tOne_of_eq_sylowA_mul hK hEU (by rw [← hE]; exact conj_sq_eq_one hsq) hl
    (w := (sylowA m K l)⁻¹ * sylowD m K 0 i * sylowA m K l) ?_ (by group)
  have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer
    ⟨0, by decide⟩ (inv_mem (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK l)))) _).1 hD1
  rwa [inv_inv] at this

end Coordinates

section Sylow

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem exists_conj_le_U (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (F4.reeGamma K m)} (hE : IsPGroup 2 E) :
    ∃ y : F4.reeGamma K m, ∀ e ∈ E,
      ((y * e * y⁻¹ : F4.reeGamma K m) : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K m := by
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨S, hS⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center m hm K hK).1
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (F4.reeGamma K m) P S
  refine ⟨y, fun e he => ?_⟩
  have hmem : y * e * y⁻¹ ∈ ((y • P : Sylow 2 (F4.reeGamma K m)) :
      Set (F4.reeGamma K m)) := by
    rw [Sylow.coe_smul]
    exact ⟨e, hP he, rfl⟩
  rw [hy] at hmem
  have hmem' : y * e * y⁻¹ ∈ (S : Subgroup (F4.reeGamma K m)) := hmem
  rw [hS, Subgroup.mem_subgroupOf] at hmem'
  exact hmem'

end Sylow

theorem card_le_mul_card_ker {A M : Type*} [Group A] [Finite A] [Group M] (ψ : A →* M) {n : ℕ}
    (hrange : Nat.card ψ.range ≤ n) : Nat.card A ≤ n * Nat.card ψ.ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ hrange

section Coord

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable (m K) in
noncomputable def sylowCoord (g : ModGL F4.tag K) : Fin 12 → K :=
  Function.invFunOn (sylowVec m K) Set.univ g

theorem sylowVec_sylowCoord (hK : Nat.card K = 2 ^ (2 * m + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedPosUnipotent K m) : sylowVec m K (sylowCoord m K g) = g :=
  Function.invFunOn_eq ((bijOn_sylowVec hK).2.2 hg)

theorem sylowCoord_sylowVec (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : Fin 12 → K) :
    sylowCoord m K (sylowVec m K x) = x :=
  (bijOn_sylowVec hK).2.1 (Function.invFunOn_mem ⟨x, Set.mem_univ x, rfl⟩) (Set.mem_univ x)
    (Function.invFunOn_eq ⟨x, Set.mem_univ x, rfl⟩)

theorem sylowCoord_eq_of_sylowVec_eq (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K}
    {g : ModGL F4.tag K} (h : sylowVec m K x = g) : sylowCoord m K g = x := by
  rw [← h, sylowCoord_sylowVec hK]

theorem card_le_of_coord_eq_zero (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m) (Z : Finset (Fin 12))
    (hZ : ∀ g ∈ E, ∀ i ∈ Z, sylowCoord m K g i = 0) :
    Nat.card E ≤ (2 ^ (2 * m + 1)) ^ (12 - Z.card) := by
  rw [← card_image_sylowVec hK Z]
  have hsub : (E : Set (ModGL F4.tag K)) ⊆ sylowVec m K '' {x | ∀ i ∈ Z, x i = 0} :=
    fun g hg => ⟨sylowCoord m K g, hZ g hg, sylowVec_sylowCoord hK (hEU hg)⟩
  exact Nat.card_mono (Set.toFinite _) hsub

theorem sylowB_zero_mul (hK : Nat.card K = 2 ^ (2 * m + 1)) (c c' : K) :
    sylowB m K 0 c * sylowB m K 0 c' = sylowB m K 0 (c + c') := by
  have h := largeReeCoord_mul (a := m) hK 0 c 0 c'
  rw [add_zero, largeReeSigma_zero, zero_mul, add_zero] at h
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord]
  exact h

omit [Finite K] [CharP K F4.prime] in
theorem sylowH_zero_zero : sylowH m K 0 (0 : K) = 1 := by
  simp [sylowH, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowL_zero : sylowL m K (0 : K) = 1 := by
  simp [sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowVec_zero : sylowVec m K 0 = 1 := by
  simp only [sylowVec, sylowV, Pi.zero_apply, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero,
    sylowF_zero_zero, sylowH_zero_zero, sylowJ_zero, sylowK_zero, sylowL_zero, mul_one]

theorem sylowL_one_ne_one (hK : Nat.card K = 2 ^ (2 * m + 1)) : sylowL m K 1 ≠ 1 := by
  intro h
  have h1 : sylowVec m K ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = sylowVec m K 0 := by
    rw [sylowVec_zero, ← h]
    simp [sylowVec, sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
      sylowH_zero_zero, sylowJ_zero, sylowK_zero]
  have h2 := congrFun ((bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) h1) 11
  simp at h2

theorem IsTConj.ne_one (hK : Nat.card K = 2 ^ (2 * m + 1)) {y : ModGL F4.tag K}
    (hy : IsTConj m K y) : y ≠ 1 := by
  rintro rfl
  obtain ⟨g, -, hg⟩ := hy
  apply sylowL_one_ne_one hK
  rw [← hg]
  group

theorem coord_two_mul (hK : Nat.card K = 2 ^ (2 * m + 1)) {g h : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedPosUnipotent K m) (hh : h ∈ F4.reeFixedPosUnipotent K m)
    (hg1 : sylowCoord m K g 1 = 0) (hh1 : sylowCoord m K h 1 = 0) :
    sylowCoord m K (g * h) 1 = 0 ∧
      sylowCoord m K (g * h) 2 = sylowCoord m K g 2 + sylowCoord m K h 2 := by
  obtain ⟨ng, hng, hg'⟩ := exists_sylowVec_eq_sylowB_mul hK (sylowCoord m K g)
  obtain ⟨nh, hnh, hh'⟩ := exists_sylowVec_eq_sylowB_mul hK (sylowCoord m K h)
  rw [sylowVec_sylowCoord hK hg, hg1] at hg'
  rw [sylowVec_sylowCoord hK hh, hh1] at hh'
  set cg := sylowCoord m K g 2 with hcg
  set ch := sylowCoord m K h 2 with hch
  have hBU : sylowB m K 0 ch ∈ F4.reeFixedPosUnipotent K m :=
    reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK _ _)
  have hconj : (sylowB m K 0 ch)⁻¹ * ng * sylowB m K 0 ch ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
    have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer ⟨1, by decide⟩
      (inv_mem hBU)) _).1 hng
    rwa [inv_inv] at this
  have hgh : sylowVec m K (sylowCoord m K (g * h)) =
      sylowB m K 0 (cg + ch) * ((sylowB m K 0 ch)⁻¹ * ng * sylowB m K 0 ch * nh) := by
    rw [sylowVec_sylowCoord hK (mul_mem hg hh)]
    calc g * h = sylowB m K 0 cg * ng * (sylowB m K 0 ch * nh) := by rw [← hg', ← hh']
      _ = _ := by rw [← sylowB_zero_mul hK]; group
  exact coord_one_two_eq hK (mul_mem hconj hnh) hgh

noncomputable def coordTwoHom (hK : Nat.card K = 2 ^ (2 * m + 1)) {E : Subgroup (ModGL F4.tag K)}
    (hEU : E ≤ F4.reeFixedPosUnipotent K m) (hb : ∀ y ∈ E, sylowCoord m K y 1 = 0) :
    E →* Multiplicative K :=
  MonoidHom.mk' (fun y => Multiplicative.ofAdd (sylowCoord m K (y : ModGL F4.tag K) 2))
    (fun y₁ y₂ => by
      rw [Subgroup.coe_mul, (coord_two_mul hK (hEU y₁.2) (hEU y₂.2) (hb _ y₁.2)
        (hb _ y₂.2)).2, ofAdd_add])

theorem mem_ker_coordTwoHom (hK : Nat.card K = 2 ^ (2 * m + 1)) {E : Subgroup (ModGL F4.tag K)}
    (hEU : E ≤ F4.reeFixedPosUnipotent K m) (hb : ∀ y ∈ E, sylowCoord m K y 1 = 0) {y : E} :
    y ∈ (coordTwoHom hK hEU hb).ker ↔ sylowCoord m K (y : ModGL F4.tag K) 2 = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one]

theorem card_le_mul_card_ker_coordTwoHom (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m)
    (hb : ∀ y ∈ E, sylowCoord m K y 1 = 0) :
    Nat.card E ≤ 2 ^ (2 * m + 1) * Nat.card (coordTwoHom hK hEU hb).ker := by
  have := finite_modGL (τ := F4.tag) (K := K)
  refine card_le_mul_card_ker _ ?_
  calc Nat.card (coordTwoHom hK hEU hb).range ≤ Nat.card (Multiplicative K) :=
        Subgroup.card_le_card_group _
    _ = 2 ^ (2 * m + 1) := by rw [← hK]; rfl

theorem coords_of_commute_sylowB (hK : Nat.card K = 2 ^ (2 * m + 1)) {y : ModGL F4.tag K}
    (hyU : y ∈ F4.reeFixedPosUnipotent K m) (hyB : y * sylowB m K 0 1 = sylowB m K 0 1 * y)
    (hsq : y ^ 2 = 1) :
    sylowCoord m K y 0 = 0 ∧ sylowCoord m K y 1 = 0 ∧ sylowCoord m K y 3 = 0 ∧
      sylowCoord m K y 4 = 0 ∧ sylowCoord m K y 10 = 0 := by
  have hyC : y ∈ ((F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowB m K 0 1} :
      Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) :=
    Subgroup.mem_inf.2 ⟨hyU, Subgroup.mem_centralizer_singleton_iff.2 hyB⟩
  rw [centralizer_sylowB_zero_one hK] at hyC
  obtain ⟨x, ⟨hx0, hx3, hx4, hx10⟩, hxy⟩ := hyC
  have hsqx : sylowVec m K x ^ 2 = 1 := by rw [hxy]; exact hsq
  rw [sylowCoord_eq_of_sylowVec_eq hK hxy]
  exact ⟨hx0, sq_eq_one_b hsqx, hx3, hx4, hx10⟩

omit [Finite K] [CharP K F4.prime] in
theorem sylowVec_eq_of_zero_two {x : Fin 12 → K} (h0 : x 0 = 0) (h2 : x 2 = 0) :
    sylowVec m K x = sylowV m K 0 (x 1) 0 (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
      (x 11) := by
  simp only [sylowVec, h0, h2]

theorem coords_of_sq_of_zero_two (hK : Nat.card K = 2 ^ (2 * m + 1)) {y : ModGL F4.tag K}
    (hyU : y ∈ F4.reeFixedPosUnipotent K m) (hsq : y ^ 2 = 1) (h0 : sylowCoord m K y 0 = 0)
    (h2 : sylowCoord m K y 2 = 0) :
    sylowCoord m K y 1 = 0 ∧ sylowCoord m K y 3 = 0 ∧ sylowCoord m K y 5 = 0 ∧
      sylowCoord m K y 7 = 0 ∧ sylowCoord m K y 4 * sylowCoord m K y 9 = 0 := by
  have h := hsq
  rw [← sylowVec_sylowCoord hK hyU, sylowVec_eq_of_zero_two h0 h2] at h
  exact (sylowV_zero_zero_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _).1 h

end Coord

section Borel

variable {m : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K F4.prime]

@[expose] def NormalizesU (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime]
    (b : ModGL F4.tag K) : Prop :=
  ∀ u ∈ F4.reeFixedPosUnipotent K m, b * u * b⁻¹ ∈ F4.reeFixedPosUnipotent K m

theorem normalizesU_torus_mul_inv {T u : ModGL F4.tag K} (hT : T ∈ F4.reeFixedTorus K m)
    (hu : u ∈ F4.reeFixedPosUnipotent K m) : NormalizesU m K (T * u⁻¹) := by
  intro v hv
  have e : T * u⁻¹ * v * (T * u⁻¹)⁻¹ = T * (u⁻¹ * v * u⁻¹⁻¹) * T⁻¹ := by group
  rw [e]
  exact torus_conj_mem hT (mul_mem (mul_mem (inv_mem hu) hv) (inv_mem (inv_mem hu)))

theorem exists_conj_sylowA_one (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K}
    (hsq : sylowVec m K x ^ 2 = 1) (hx : x 0 ≠ 0) :
    ∃ b ∈ F4.reeGamma K m, NormalizesU m K b ∧ b * sylowVec m K x * b⁻¹ = sylowA m K 1 := by
  set s : Kˣ := Units.mk0 ((x 0)⁻¹ ^ 2 ^ m) (pow_ne_zero _ (inv_ne_zero hx)) with hs
  have hσs : largeReeSigma m (s : K) = (x 0)⁻¹ := by rw [hs, Units.val_mk0, largeReeSigma_pow hK]
  set T := pairedTorusHom m (f4i 0) (f4i 3) s with hT
  have hTmem := torusOne_mem (m := m) hK s
  obtain ⟨y, -, hy⟩ := (bijOn_sylowVec hK).2.2 (torus_conj_mem hTmem
    ((bijOn_sylowVec hK).1 (Set.mem_univ x)))
  have hw := sylowV_zero_mem_complement hK (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
    (x 10) (x 11)
  have hw' : T * sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
      (x 11) * T⁻¹ ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ :=
    (Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_complement _ hTmem) _).1 hw
  have e : sylowVec m K y = sylowA m K (largeReeSigma m (s : K) * x 0) *
      (T * sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) *
        T⁻¹) := by
    rw [hy, sylowVec_eq_sylowA_mul x, hT, ← torusOne_conj_sylowA hK]
    group
  have hy0 := coord_zero_eq hK hw' e
  rw [hσs, inv_mul_cancel₀ hx] at hy0
  have hyS : sylowVec m K y ∈ sylowVec m K '' {x | x 0 = 1 ∧ sylowVec m K x ^ 2 = 1} :=
    ⟨y, ⟨hy0, by rw [hy]; exact conj_sq_eq_one hsq⟩, rfl⟩
  rw [← uClass_sylowA_one_eq hK] at hyS
  obtain ⟨u, hu, hu'⟩ := hyS
  refine ⟨u⁻¹ * T, mul_mem (inv_mem (reeFixedPosUnipotent_le_reeGamma' hu))
    (reeFixedTorus_le_reeGamma' hTmem), ?_, ?_⟩
  · intro v hv
    have e2 : u⁻¹ * T * v * (u⁻¹ * T)⁻¹ = u⁻¹ * (T * v * T⁻¹) * u⁻¹⁻¹ := by group
    rw [e2]
    exact mul_mem (mul_mem (inv_mem hu) (torus_conj_mem hTmem hv)) (inv_mem (inv_mem hu))
  · calc u⁻¹ * T * sylowVec m K x * (u⁻¹ * T)⁻¹ = u⁻¹ * (T * sylowVec m K x * T⁻¹) * u := by
          group
      _ = sylowA m K 1 := by rw [← hy, ← hu']; group

theorem exists_conj_sylowB_one (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {x : Fin 12 → K} (hsq : sylowVec m K x ^ 2 = 1) (hx0 : x 0 = 0) (hx2 : x 2 ≠ 0) :
    ∃ b ∈ F4.reeGamma K m, NormalizesU m K b ∧ ∃ i : K,
      b * sylowVec m K x * b⁻¹ = sylowB m K 0 1 * sylowH m K 0 i := by
  have hmem : sylowVec m K x ∈ sylowVec m K '' {y | y 0 = 0 ∧ y 2 = x 2 ∧ sylowVec m K y ^ 2 = 1} :=
    ⟨x, ⟨hx0, rfl, hsq⟩, rfl⟩
  rw [(stratumZero_eq hm hK hx2).1, Set.mem_iUnion] at hmem
  obtain ⟨i, u, hu, hu'⟩ := hmem
  set r : Kˣ := Units.mk0 (x 2)⁻¹ (inv_ne_zero hx2) with hr
  set T := pairedTorusHom m (f4i 1) (f4i 2) r with hT
  have hTmem := torusTwo_mem (m := m) hK r
  refine ⟨T * u⁻¹, mul_mem (reeFixedTorus_le_reeGamma' hTmem)
    (inv_mem (reeFixedPosUnipotent_le_reeGamma' hu)), normalizesU_torus_mul_inv hTmem hu, i, ?_⟩
  calc T * u⁻¹ * sylowVec m K x * (T * u⁻¹)⁻¹ = T * (u⁻¹ * sylowVec m K x * u) * T⁻¹ := by group
    _ = (T * sylowB m K 0 (x 2) * T⁻¹) * (T * sylowH m K 0 i * T⁻¹) := by rw [← hu']; group
    _ = sylowB m K 0 1 * sylowH m K 0 i := by
      rw [hT, torusTwo_conj_sylowB, torusTwo_conj_sylowH hK, hr, Units.val_mk0,
        inv_mul_cancel₀ hx2]

end Borel

end CFSG.Quasithin.B42F4
