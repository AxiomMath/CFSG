module

public import CFSG.Quasithin.Background.SmithB42F4Rank

public section

namespace CFSG.Quasithin.B42F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution


variable {m : ℕ}
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem not_isTConj_of_pure (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hpure : ∀ g ∈ E, g ≠ 1 → IsZConj m K g) {y : ModGL F4.tag K}
    (hy : y ∈ E) : ¬ IsTConj m K y := fun ht =>
  not_isZConj_of_isTConj hm hK ht (hpure y hy (ht.ne_one hK))

theorem coord_zero_of_pure (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) (hpure : ∀ g ∈ E, g ≠ 1 → IsZConj m K g) {y : ModGL F4.tag K}
    (hy : y ∈ E) : sylowCoord m K y 0 = 0 := by
  by_contra h0
  apply not_isTConj_of_pure hm hK hpure hy
  have h := isTConj_of_coord_zero_ne hK (by rw [sylowVec_sylowCoord hK (hEU hy)]; exact hsq y hy)
    h0
  rwa [sylowVec_sylowCoord hK (hEU hy)] at h

theorem sylowV_mul_sylowH (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (g i l i' : K) :
    sylowV m K 0 0 0 0 0 0 g 0 i 0 0 l * sylowH m K 0 i' =
      sylowV m K 0 0 0 0 0 0 g 0 (i + i') 0 0 l := by
  have hL : sylowL m K l ∈ F4.reeFixedPosUnipotent K m :=
    complement_le_U _ (blocks_mem (m := m) hK 0 0 0 0 0 0 l).2.2.2.2.2.2.1
  rw [sylowV_eq_blocks_of_e, sylowV_eq_blocks_of_e, sylowJ_zero, sylowK_zero, mul_one, mul_one,
    mul_one, mul_one, mul_assoc, commute_sylowH hm hK hL i', ← mul_assoc,
    mul_assoc _ (sylowH m K 0 i), sylowH_mul hK]

theorem card_lt_of_pureZ_of_coord_two (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1)
    (hpure : ∀ g ∈ E, g ≠ 1 → IsZConj m K g) {g : ModGL F4.tag K} (hgE : g ∈ E)
    (hg2 : sylowCoord m K g 2 ≠ 0) : Nat.card E < (2 ^ (2 * m + 1)) ^ 3 := by
  have := finite_modGL (τ := F4.tag) (K := K)
  set q := 2 ^ (2 * m + 1) with hqdef
  have hcrd : ∀ y ∈ E, sylowVec m K (sylowCoord m K y) = y :=
    fun y hy => sylowVec_sylowCoord hK (hEU hy)
  obtain ⟨b, hbΓ, hbU, i, hbg⟩ := exists_conj_sylowB_one hm hK
    (by rw [hcrd g hgE]; exact hsq g hgE) (coord_zero_of_pure hm hK hEU hsq hpure hgE) hg2
  rw [hcrd g hgE] at hbg
  set E' := E.map (MulAut.conj b).toMonoidHom with hE'
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj b).injective
  have hE'U : E' ≤ F4.reeFixedPosUnipotent K m := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    exact hbU e (hEU he)
  have hE'sq : ∀ y ∈ E', y ^ 2 = 1 := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    exact conj_sq_eq_one (hsq e he)
  have hE'comm : ∀ y ∈ E', ∀ y' ∈ E', y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    obtain ⟨e', he', rfl⟩ := mem_map_conj.1 hy'
    calc b * e * b⁻¹ * (b * e' * b⁻¹) = b * (e * e') * b⁻¹ := by group
      _ = b * (e' * e) * b⁻¹ := by rw [hcomm e he e' he']
      _ = b * e' * b⁻¹ * (b * e * b⁻¹) := by group
  have hE'pure : ∀ y ∈ E', y ≠ 1 → IsZConj m K y := by
    intro y hy hy1
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    refine (hpure e he fun h1 => hy1 ?_).conj hbΓ
    rw [h1]
    group
  have hgE' : b * g * b⁻¹ ∈ E' := mem_map_conj.2 ⟨g, hgE, rfl⟩
  have hi : i = 0 := by
    by_contra hi
    have ht := isTConj_sylowB_mul_sylowH hK one_ne_zero hi
    rw [← hbg] at ht
    exact not_isTConj_of_pure hm hK hE'pure hgE' ht
  rw [hi, sylowH_zero_zero, mul_one] at hbg
  have hBE' : sylowB m K 0 1 ∈ E' := hbg ▸ hgE'
  have hco : ∀ y ∈ E', sylowCoord m K y 0 = 0 ∧ sylowCoord m K y 1 = 0 ∧
      sylowCoord m K y 3 = 0 ∧ sylowCoord m K y 4 = 0 ∧ sylowCoord m K y 10 = 0 :=
    fun y hy => coords_of_commute_sylowB hK (hE'U hy) (hE'comm y hy _ hBE') (hE'sq y hy)
  have hb : ∀ y ∈ E', sylowCoord m K y 1 = 0 := fun y hy => (hco y hy).2.1
  set φ := coordTwoHom hK hE'U hb with hφ
  have hker : ∀ y : E', y ∈ φ.ker → ∃ g' i' l' : K,
      (y : ModGL F4.tag K) = sylowV m K 0 0 0 0 0 0 g' 0 i' 0 0 l' := by
    intro y hy
    have hy2 := (mem_ker_coordTwoHom hK hE'U hb).1 hy
    obtain ⟨h0, -, h3, h4, h10⟩ := hco _ y.2
    obtain ⟨h1', -, h5, h7, -⟩ := coords_of_sq_of_zero_two hK (hE'U y.2) (hE'sq _ y.2) h0 hy2
    set x := sylowCoord m K (y : ModGL F4.tag K) with hx
    have hyx : (y : ModGL F4.tag K) = sylowV m K 0 0 0 0 0 0 (x 6) 0 (x 8) (x 9) 0 (x 11) := by
      rw [← sylowVec_sylowCoord hK (hE'U y.2), ← hx]
      simp only [sylowVec, h0, h1', hy2, h3, h4, h5, h7, h10]
    have h9 : x 9 = 0 := by
      by_contra h9
      have hsq' : sylowV m K 0 0 0 0 0 0 (x 6) 0 (x 8) (x 9) 0 (x 11) ^ 2 = 1 := by
        rw [← hyx]
        exact hE'sq _ y.2
      have ht := isTConj_of_coord_nine_ne hK hsq' h9
      rw [← hyx] at ht
      exact not_isTConj_of_pure hm hK hE'pure y.2 ht
    exact ⟨x 6, x 8, x 11, by rw [hyx, h9]⟩
  set Y := sylowVec m K '' {x | ∀ j ∈ ({0, 1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 12)),
    x j = 0} with hY
  have hLY : sylowL m K 1 ∈ Y := by
    refine ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], fun j hj => ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    simp [sylowVec, sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
      sylowH_zero_zero, sylowJ_zero, sylowK_zero]
  have hVY : ∀ g' i' l' : K, sylowV m K 0 0 0 0 0 0 g' 0 i' 0 0 l' ∈ Y := by
    intro g' i' l'
    refine ⟨![0, 0, 0, 0, 0, 0, g', 0, i', 0, 0, l'], ?_, rfl⟩
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hYcard : (Y \ {sylowL m K 1}).ncard = q ^ 3 - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hLY, ← Nat.card_coe_set_eq, hY,
      card_image_sylowVec hK]
    rfl
  have hmap : ∀ (y : φ.ker) (c : K),
      ((y : E') : ModGL F4.tag K) * sylowH m K 0 c ∈ Y \ {sylowL m K 1} := by
    intro y c
    obtain ⟨g', i', l', hy⟩ := hker y y.2
    refine ⟨by rw [hy, sylowV_mul_sylowH hm hK]; exact hVY _ _ _, fun hL => ?_⟩
    have hy' : ((y : E') : ModGL F4.tag K) = sylowH m K 0 c * sylowL m K 1 := by
      have h1 : ((y : E') : ModGL F4.tag K) = sylowL m K 1 * (sylowH m K 0 c)⁻¹ := by
        rw [← (Set.mem_singleton_iff.1 hL), mul_inv_cancel_right]
      have hcc : (sylowH m K 0 c)⁻¹ = sylowH m K 0 c := by
        rw [inv_eq_iff_mul_eq_one, sylowH_mul hK, CharTwo.add_self_eq_zero, sylowH_zero_zero]
      rw [h1, hcc, commute_sylowH hm hK (complement_le_U _
        (blocks_mem (m := m) hK 0 0 0 0 0 0 1).2.2.2.2.2.2.1) c]
    have ht := isTConj_sylowH_mul_sylowL (m := m) hK (i := c) one_ne_zero
    rw [← hy'] at ht
    exact not_isTConj_of_pure hm hK hE'pure (y : E').2 ht
  have hinj : Function.Injective (fun p : φ.ker × K =>
      (⟨((p.1 : E') : ModGL F4.tag K) * sylowH m K 0 p.2, hmap p.1 p.2⟩ :
        ↥(Y \ {sylowL m K 1}))) := by
    rintro ⟨y₁, c₁⟩ ⟨y₂, c₂⟩ h
    have h' : ((y₁ : E') : ModGL F4.tag K) * sylowH m K 0 c₁ =
        ((y₂ : E') : ModGL F4.tag K) * sylowH m K 0 c₂ := by
      have h1 := Subtype.ext_iff.1 h
      exact h1
    have hz : ((y₂ : E') : ModGL F4.tag K)⁻¹ * ((y₁ : E') : ModGL F4.tag K) =
        sylowH m K 0 (c₁ + c₂) := by
      have hcc : (sylowH m K 0 c₁)⁻¹ = sylowH m K 0 c₁ := by
        rw [inv_eq_iff_mul_eq_one, sylowH_mul hK, CharTwo.add_self_eq_zero, sylowH_zero_zero]
      calc ((y₂ : E') : ModGL F4.tag K)⁻¹ * ((y₁ : E') : ModGL F4.tag K) =
          ((y₂ : E') : ModGL F4.tag K)⁻¹ * (((y₁ : E') : ModGL F4.tag K) * sylowH m K 0 c₁) *
            (sylowH m K 0 c₁)⁻¹ := by group
        _ = sylowH m K 0 c₂ * sylowH m K 0 c₁ := by rw [h', hcc]; group
        _ = sylowH m K 0 (c₁ + c₂) := by rw [sylowH_mul hK, add_comm]
    have hzE' : sylowH m K 0 (c₁ + c₂) ∈ E' := by
      rw [← hz]
      exact mul_mem (inv_mem (y₂ : E').2) (y₁ : E').2
    have hc : c₁ + c₂ = 0 := by
      by_contra hc
      have ht := isTConj_sylowB_mul_sylowH hK one_ne_zero hc
      exact not_isTConj_of_pure hm hK hE'pure (mul_mem hBE' hzE') ht
    have hcc : c₁ = c₂ := by
      have : c₁ = -c₂ := eq_neg_of_add_eq_zero_left hc
      rwa [CharTwo.neg_eq] at this
    subst hcc
    have hy : ((y₁ : E') : ModGL F4.tag K) = ((y₂ : E') : ModGL F4.tag K) := mul_right_cancel h'
    exact Prod.ext (Subtype.ext (Subtype.ext hy)) rfl
  have hkercard : Nat.card φ.ker * q ≤ q ^ 3 - 1 := by
    have h := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_coe_set_eq, hYcard, hK] at h
    exact h
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  calc Nat.card E = Nat.card E' := hcard.symm
    _ ≤ q * Nat.card φ.ker := card_le_mul_card_ker_coordTwoHom hK hE'U hb
    _ ≤ q ^ 3 - 1 := by rw [mul_comm]; exact hkercard
    _ < q ^ 3 := Nat.sub_lt (by positivity) one_pos

theorem weylOne_conj_stratum (hK : Nat.card K = 2 ^ (2 * m + 1)) (e g i j k l : K) :
    weylOne K * sylowV m K 0 0 0 0 e 0 g 0 i j k l * (weylOne K)⁻¹ =
        sylowB m K 0 e * (sylowH m K 0 g * sylowF m K 0 i * sylowK m K j * sylowJ m K k *
          sylowL m K l) ∧
      sylowH m K 0 g * sylowF m K 0 i * sylowK m K j * sylowJ m K k * sylowL m K l ∈
        F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
  refine ⟨?_, ?_⟩
  · rw [sylowV_blocks, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul,
      weylOne_conj_sylowD, weylOne_conj_sylowF, weylOne_conj_sylowH, weylOne_conj_sylowJ,
      weylOne_conj_sylowK, weylOne_conj_sylowL]
    group
  · obtain ⟨-, -, ⟨-, hF⟩, ⟨-, hH⟩, ⟨-, hJ⟩, ⟨-, hKk⟩, ⟨-, hL⟩⟩ :=
      blocks_mem (m := m) hK 0 0 i g k j l
    exact mul_mem (mul_mem (mul_mem (mul_mem hH hF) hKk) hJ) hL

theorem weylOneTwo_conj_stratum (hK : Nat.card K = 2 ^ (2 * m + 1)) (g i k l : K) :
    (weylOne K * weylTwo K) * sylowV m K 0 0 0 0 0 0 g 0 i 0 k l * (weylOne K * weylTwo K)⁻¹ =
        sylowB m K 0 g * (sylowF m K 0 i * sylowL m K k * sylowJ m K l) ∧
      sylowF m K 0 i * sylowL m K k * sylowJ m K l ∈
        F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
  refine ⟨?_, ?_⟩
  · rw [sylowV_eq_blocks_of_e, sylowJ_zero, mul_one]
    calc weylOne K * weylTwo K *
          (sylowF m K 0 g * sylowH m K 0 i * sylowK m K k * sylowL m K l) *
            (weylOne K * weylTwo K)⁻¹ =
        (weylOne K * (weylTwo K * sylowF m K 0 g * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
          (weylOne K * (weylTwo K * sylowH m K 0 i * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
            (weylOne K * (weylTwo K * sylowK m K k * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
              (weylOne K * (weylTwo K * sylowL m K l * (weylTwo K)⁻¹) * (weylOne K)⁻¹) := by
          group
      _ = _ := by
        rw [weylTwo_conj_sylowF, weylOne_conj_sylowD, weylTwo_conj_sylowH, weylOne_conj_sylowH,
          weylTwo_conj_sylowK, weylOne_conj_sylowL, weylTwo_conj_sylowL, weylOne_conj_sylowK]
        group
  · obtain ⟨-, -, ⟨-, hF⟩, -, ⟨-, hJ⟩, -, ⟨-, hL⟩⟩ := blocks_mem (m := m) hK 0 0 i 0 l 0 k
    exact mul_mem (mul_mem hF hL) hJ

theorem pureZ_map_conj {E : Subgroup (ModGL F4.tag K)} {b : ModGL F4.tag K}
    (hb : b ∈ F4.reeGamma K m) (hcomm : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) (hpure : ∀ g ∈ E, g ≠ 1 → IsZConj m K g) :
    Nat.card (E.map (MulAut.conj b).toMonoidHom) = Nat.card E ∧
    (∀ a ∈ E.map (MulAut.conj b).toMonoidHom, ∀ c ∈ E.map (MulAut.conj b).toMonoidHom,
      a * c = c * a) ∧
    (∀ a ∈ E.map (MulAut.conj b).toMonoidHom, a ^ 2 = 1) ∧
    (∀ g ∈ E.map (MulAut.conj b).toMonoidHom, g ≠ 1 → IsZConj m K g) := by
  refine ⟨Subgroup.card_map_of_injective (MulAut.conj b).injective, ?_, ?_, ?_⟩
  · intro y hy y' hy'
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    obtain ⟨e', he', rfl⟩ := mem_map_conj.1 hy'
    calc b * e * b⁻¹ * (b * e' * b⁻¹) = b * (e * e') * b⁻¹ := by group
      _ = b * (e' * e) * b⁻¹ := by rw [hcomm e he e' he']
      _ = b * e' * b⁻¹ * (b * e * b⁻¹) := by group
  · intro y hy
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    exact conj_sq_eq_one (hsq e he)
  · intro y hy hy1
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    refine (hpure e he fun h1 => hy1 ?_).conj hb
    rw [h1]
    group

theorem card_lt_of_pureZ_le_U (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1)
    (hpure : ∀ g ∈ E, g ≠ 1 → IsZConj m K g) : Nat.card E < (2 ^ (2 * m + 1)) ^ 3 := by
  have := finite_modGL (τ := F4.tag) (K := K)
  set q := 2 ^ (2 * m + 1) with hqdef
  by_cases h2 : ∃ g ∈ E, sylowCoord m K g 2 ≠ 0
  · obtain ⟨g, hg, hg2⟩ := h2
    exact card_lt_of_pureZ_of_coord_two hm hK hEU hcomm hsq hpure hg hg2
  push Not at h2
  have h0 : ∀ y ∈ E, sylowCoord m K y 0 = 0 := fun y hy =>
    coord_zero_of_pure hm hK hEU hsq hpure hy
  have hform : ∀ y ∈ E, y = sylowV m K 0 0 0 0 (sylowCoord m K y 4) 0 (sylowCoord m K y 6) 0
      (sylowCoord m K y 8) (sylowCoord m K y 9) (sylowCoord m K y 10) (sylowCoord m K y 11) := by
    intro y hy
    obtain ⟨h1, h3, h5, h7, -⟩ := coords_of_sq_of_zero_two hK (hEU hy) (hsq y hy) (h0 y hy)
      (h2 y hy)
    conv_lhs => rw [← sylowVec_sylowCoord hK (hEU hy)]
    simp only [sylowVec, h0 y hy, h1, h2 y hy, h3, h5, h7]
  by_cases h4 : ∃ g ∈ E, sylowCoord m K g 4 ≠ 0
  ·
    obtain ⟨g, hg, hg4⟩ := h4
    obtain ⟨hcard, hcomm', hsq', hpure'⟩ := pureZ_map_conj weylOne_mem hcomm hsq hpure
    have hconj : ∀ y ∈ E, weylOne K * y * (weylOne K)⁻¹ ∈ F4.reeFixedPosUnipotent K m ∧
        sylowCoord m K (weylOne K * y * (weylOne K)⁻¹) 2 = sylowCoord m K y 4 := by
      intro y hy
      obtain ⟨he, hn⟩ := weylOne_conj_stratum (m := m) hK (sylowCoord m K y 4)
        (sylowCoord m K y 6) (sylowCoord m K y 8) (sylowCoord m K y 9) (sylowCoord m K y 10)
        (sylowCoord m K y 11)
      rw [← hform y hy] at he
      have hmem : weylOne K * y * (weylOne K)⁻¹ ∈ F4.reeFixedPosUnipotent K m := by
        rw [he]
        exact mul_mem (reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK _ _))
          (complement_le_U _ hn)
      refine ⟨hmem, (coord_one_two_eq (b := 0) hK hn ?_).2⟩
      rw [sylowVec_sylowCoord hK hmem, he]
    have hE₁U : E.map (MulAut.conj (weylOne K)).toMonoidHom ≤ F4.reeFixedPosUnipotent K m := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
      exact (hconj e he).1
    rw [← hcard]
    exact card_lt_of_pureZ_of_coord_two hm hK hE₁U hcomm' hsq' hpure'
      (mem_map_conj.2 ⟨g, hg, rfl⟩) (by rw [(hconj g hg).2]; exact hg4)
  push Not at h4
  have h9 : ∀ y ∈ E, sylowCoord m K y 9 = 0 := by
    intro y hy
    by_contra h9
    have hy' := hform y hy
    rw [h4 y hy] at hy'
    have ht := isTConj_of_coord_nine_ne hK (by rw [← hy']; exact hsq y hy) h9
    rw [← hy'] at ht
    exact not_isTConj_of_pure hm hK hpure hy ht
  have hform' : ∀ y ∈ E, y = sylowV m K 0 0 0 0 0 0 (sylowCoord m K y 6) 0 (sylowCoord m K y 8) 0
      (sylowCoord m K y 10) (sylowCoord m K y 11) := by
    intro y hy
    have hy' := hform y hy
    rwa [h4 y hy, h9 y hy] at hy'
  by_cases h6 : ∃ g ∈ E, sylowCoord m K g 6 ≠ 0
  ·
    obtain ⟨g, hg, hg6⟩ := h6
    have hw : weylOne K * weylTwo K ∈ F4.reeGamma K m := mul_mem weylOne_mem weylTwo_mem
    obtain ⟨hcard, hcomm', hsq', hpure'⟩ := pureZ_map_conj hw hcomm hsq hpure
    have hconj : ∀ y ∈ E, (weylOne K * weylTwo K) * y * (weylOne K * weylTwo K)⁻¹ ∈
          F4.reeFixedPosUnipotent K m ∧
        sylowCoord m K ((weylOne K * weylTwo K) * y * (weylOne K * weylTwo K)⁻¹) 2 =
          sylowCoord m K y 6 := by
      intro y hy
      obtain ⟨he, hn⟩ := weylOneTwo_conj_stratum (m := m) hK (sylowCoord m K y 6)
        (sylowCoord m K y 8) (sylowCoord m K y 10) (sylowCoord m K y 11)
      rw [← hform' y hy] at he
      have hmem : (weylOne K * weylTwo K) * y * (weylOne K * weylTwo K)⁻¹ ∈
          F4.reeFixedPosUnipotent K m := by
        rw [he]
        exact mul_mem (reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK _ _))
          (complement_le_U _ hn)
      refine ⟨hmem, (coord_one_two_eq (b := 0) hK hn ?_).2⟩
      rw [sylowVec_sylowCoord hK hmem, he]
    have hE₁U : E.map (MulAut.conj (weylOne K * weylTwo K)).toMonoidHom ≤
        F4.reeFixedPosUnipotent K m := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
      exact (hconj e he).1
    rw [← hcard]
    exact card_lt_of_pureZ_of_coord_two hm hK hE₁U hcomm' hsq' hpure'
      (mem_map_conj.2 ⟨g, hg, rfl⟩) (by rw [(hconj g hg).2]; exact hg6)
  push Not at h6
  set Y := sylowVec m K '' {x | ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 9} : Finset (Fin 12)),
    x j = 0} with hY
  have hLY : sylowL m K 1 ∈ Y := by
    refine ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], fun j hj => ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    simp [sylowVec, sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
      sylowH_zero_zero, sylowJ_zero, sylowK_zero]
  have hsub : (E : Set (ModGL F4.tag K)) ⊆ Y \ {sylowL m K 1} := by
    intro y hy
    refine ⟨⟨![0, 0, 0, 0, 0, 0, 0, 0, sylowCoord m K y 8, 0, sylowCoord m K y 10,
      sylowCoord m K y 11], fun j hj => ?_, ?_⟩, fun hL => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have hy' := hform' y hy
      rw [h6 y hy] at hy'
      exact hy'.symm
    · exact not_isTConj_of_pure hm hK hpure hy ((Set.mem_singleton_iff.1 hL) ▸ isTConj_tOne)
  calc Nat.card E = (E : Set (ModGL F4.tag K)).ncard := Nat.card_coe_set_eq _
    _ ≤ (Y \ {sylowL m K 1}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = q ^ 3 - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem hLY, ← Nat.card_coe_set_eq, hY,
        card_image_sylowVec hK]
      rfl
    _ < q ^ 3 := Nat.sub_lt (by positivity) one_pos

theorem card_lt_of_pureZ (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (F4.reeGamma K m)} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) (hpure : ∀ g ∈ E, g ≠ 1 → IsZConj m K (g : ModGL F4.tag K)) :
    Nat.card E < (2 ^ (2 * m + 1)) ^ 3 := by
  have hp : IsPGroup 2 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hsq _ g.2)⟩
  obtain ⟨y, hy⟩ := exists_conj_le_U hm hK hp
  set E' := (E.map (MulAut.conj y).toMonoidHom).map (F4.reeGamma K m).subtype with hE'
  have hcard : Nat.card E' = Nat.card E := by
    rw [hE', Subgroup.card_map_of_injective (F4.reeGamma K m).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hmem : ∀ z ∈ E', ∃ e ∈ E, ((y * e * y⁻¹ : F4.reeGamma K m) : ModGL F4.tag K) = z := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hw
    exact ⟨e, he, rfl⟩
  rw [← hcard]
  refine card_lt_of_pureZ_le_U hm hK ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨e, he, rfl⟩ := hmem z hz
    exact hy e he
  · intro a ha b hb
    obtain ⟨e, he, rfl⟩ := hmem a ha
    obtain ⟨e', he', rfl⟩ := hmem b hb
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    calc y * e * y⁻¹ * (y * e' * y⁻¹) = y * (e * e') * y⁻¹ := by group
      _ = y * (e' * e) * y⁻¹ := by rw [hcomm e he e' he']
      _ = y * e' * y⁻¹ * (y * e * y⁻¹) := by group
  · intro a ha
    obtain ⟨e, he, rfl⟩ := hmem a ha
    rw [← Subgroup.coe_pow, conj_sq_eq_one (hsq e he), Subgroup.coe_one]
  · intro z hz hz1
    obtain ⟨e, he, rfl⟩ := hmem z hz
    have he1 : e ≠ 1 := by
      rintro rfl
      apply hz1
      simp
    have h' := (hpure e he he1).conj y.2
    simpa using h'

end CFSG.Quasithin.B42F4
