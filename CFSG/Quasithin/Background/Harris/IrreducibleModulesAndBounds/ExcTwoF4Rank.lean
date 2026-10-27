module

public import CFSG.Quasithin.Background.SmithB42F4Rank

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.B42F4


section Coord

variable {m : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K F4.prime]

theorem coord_zero_mul' (hK : Nat.card K = 2 ^ (2 * m + 1)) {g h : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedPosUnipotent K m) (hh : h ∈ F4.reeFixedPosUnipotent K m) :
    sylowCoord m K (g * h) 0 = sylowCoord m K g 0 + sylowCoord m K h 0 := by
  set x := sylowCoord m K g with hx
  set y := sylowCoord m K h with hy
  have hgx : g = sylowA m K (x 0) *
      sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) := by
    rw [← sylowVec_eq_sylowA_mul, hx, sylowVec_sylowCoord hK hg]
  have hhy : h = sylowA m K (y 0) *
      sylowV m K 0 (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) := by
    rw [← sylowVec_eq_sylowA_mul, hy, sylowVec_sylowCoord hK hh]
  have hw1 := sylowV_zero_mem_complement hK (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    (x 9) (x 10) (x 11)
  have hw2 := sylowV_zero_mem_complement hK (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
    (y 9) (y 10) (y 11)
  set w1 := sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11)
  set w2 := sylowV m K 0 (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9) (y 10) (y 11)
  have hAU : ∀ s : K, sylowA m K s ∈ F4.reeFixedPosUnipotent K m := fun s =>
    reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK s)
  have hconj : (sylowA m K (y 0))⁻¹ * w1 * sylowA m K (y 0) ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ := by
    have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer ⟨0, by decide⟩
      (inv_mem (hAU (y 0)))) _).1 hw1
    rwa [inv_inv] at this
  have hgh : sylowVec m K (sylowCoord m K (g * h)) = sylowA m K (x 0 + y 0) *
      ((sylowA m K (y 0))⁻¹ * w1 * sylowA m K (y 0) * w2) := by
    rw [sylowVec_sylowCoord hK (mul_mem hg hh), ← sylowA_mul hK]
    calc g * h = sylowA m K (x 0) * w1 * (sylowA m K (y 0) * w2) := by rw [← hgx, ← hhy]
      _ = _ := by group
  exact coord_zero_eq hK (mul_mem hconj hw2) hgh

noncomputable def coordZeroHom (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m) :
    E →* Multiplicative K :=
  MonoidHom.mk' (fun y => Multiplicative.ofAdd (sylowCoord m K (y : ModGL F4.tag K) 0))
    (fun y₁ y₂ => by
      rw [Subgroup.coe_mul, coord_zero_mul' hK (hEU y₁.2) (hEU y₂.2), ofAdd_add])

theorem mem_ker_coordZeroHom (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m) {y : E} :
    y ∈ (coordZeroHom hK hEU).ker ↔ sylowCoord m K (y : ModGL F4.tag K) 0 = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one]

theorem card_le_mul_card_ker_coordZeroHom (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m) :
    Nat.card E ≤ 2 ^ (2 * m + 1) * Nat.card (coordZeroHom hK hEU).ker := by
  have := finite_modGL (τ := F4.tag) (K := K)
  refine card_le_mul_card_ker _ ?_
  calc Nat.card (coordZeroHom hK hEU).range ≤ Nat.card (Multiplicative K) :=
        Subgroup.card_le_card_group _
    _ = 2 ^ (2 * m + 1) := by rw [← hK]; rfl


theorem four_mul_card_le_of_le_U (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1) :
    4 * Nat.card E ≤ (2 ^ (2 * m + 1)) ^ 6 := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have hq := eight_le_q hm
  set q := 2 ^ (2 * m + 1) with hqdef
  have hq5 : 4 * q ^ 5 ≤ q ^ 6 := by
    have : q ^ 6 = q * q ^ 5 := by ring
    rw [this]
    have : 0 < q ^ 5 := by positivity
    nlinarith
  have hq5' : 4 * (q ^ 5 + q ^ 5) ≤ q ^ 6 := by
    have : q ^ 6 = q * q ^ 5 := by ring
    rw [this]
    have : 0 < q ^ 5 := by positivity
    nlinarith
  have hcrd : ∀ g ∈ E, sylowVec m K (sylowCoord m K g) = g :=
    fun g hg => sylowVec_sylowCoord hK (hEU hg)
  have hsqc : ∀ g ∈ E, sylowVec m K (sylowCoord m K g) ^ 2 = 1 := fun g hg => by
    rw [hcrd g hg]
    exact hsq g hg
  by_cases h1 : ∃ g ∈ E, sylowCoord m K g 0 ≠ 0
  ·
    obtain ⟨g, hgE, hg0⟩ := h1
    obtain ⟨b, -, hbU, hbg⟩ := exists_conj_sylowA_one hK (hsqc g hgE) hg0
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
    have hE'C : ∀ y ∈ E', y ∈ ((F4.reeFixedPosUnipotent K m ⊓
        Subgroup.centralizer {sylowA m K 1} : Subgroup (ModGL F4.tag K)) :
          Set (ModGL F4.tag K)) := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
      refine Subgroup.mem_inf.2 ⟨hbU e (hEU he), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hbg]
      calc b * e * b⁻¹ * (b * g * b⁻¹) = b * (e * g) * b⁻¹ := by group
        _ = b * (g * e) * b⁻¹ := by rw [hcomm e he g hgE]
        _ = b * g * b⁻¹ * (b * e * b⁻¹) := by group
    have hco : ∀ y ∈ E', sylowCoord m K y 1 = 0 ∧ sylowCoord m K y 2 = 0 ∧
        sylowCoord m K y 5 = 0 ∧ sylowCoord m K y 6 = 0 ∧ sylowCoord m K y 7 = 0 ∧
          sylowCoord m K y 9 = 0 := by
      intro y hy
      have hyC := hE'C y hy
      rw [centralizer_sylowA_one hK] at hyC
      obtain ⟨x, ⟨h1, h2, h5, h6, h7, h9⟩, hxy⟩ := hyC
      rw [sylowCoord_eq_of_sylowVec_eq hK hxy]
      exact ⟨h1, h2, h5, h6, h7, h9⟩
    have hker : Nat.card (coordZeroHom hK hE'U).ker ≤ q ^ 4 := by
      rw [← Subgroup.card_map_of_injective (f := E'.subtype) E'.subtype_injective]
      have hle : (coordZeroHom hK hE'U).ker.map E'.subtype ≤ F4.reeFixedPosUnipotent K m := by
        rintro _ ⟨y, -, rfl⟩
        exact hE'U y.2
      refine (card_le_of_coord_eq_zero hK hle {0, 1, 2, 3, 5, 6, 7, 9} ?_).trans (le_of_eq ?_)
      · rintro _ ⟨y, hy, rfl⟩
        have hy0 := (mem_ker_coordZeroHom hK hE'U).1 hy
        obtain ⟨h1, h2, h5, h6, h7, h9⟩ := hco _ y.2
        have hy2 := hE'sq _ y.2
        have hd : sylowCoord m K (y : ModGL F4.tag K) 3 = 0 := by
          have hv := hy2
          rw [← sylowVec_sylowCoord hK (hE'U y.2),
            sylowVec_eq_of_zero_two hy0 h2] at hv
          rw [← sylowVec_sylowCoord hK (hE'U y.2)] at hy2
          exact sq_eq_one_d (by simpa [h1, h2, hy0] using hv)
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      · rw [hqdef]
        rfl
    calc 4 * Nat.card E = 4 * Nat.card E' := by rw [hcard]
      _ ≤ 4 * (q * Nat.card (coordZeroHom hK hE'U).ker) :=
        Nat.mul_le_mul_left _ (card_le_mul_card_ker_coordZeroHom hK hE'U)
      _ ≤ 4 * (q * q ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hker)
      _ = 4 * q ^ 5 := by ring
      _ ≤ q ^ 6 := hq5
  push Not at h1
  by_cases h2 : ∃ g ∈ E, sylowCoord m K g 2 ≠ 0
  ·
    obtain ⟨g, hgE, hg2⟩ := h2
    obtain ⟨b, -, hbU, i, hbg⟩ := exists_conj_sylowB_one hm hK (hsqc g hgE) (h1 g hgE) hg2
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
    have hE'C : ∀ y ∈ E', y * sylowB m K 0 1 = sylowB m K 0 1 * y := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
      have hc : b * e * b⁻¹ * (sylowB m K 0 1 * sylowH m K 0 i) =
          sylowB m K 0 1 * sylowH m K 0 i * (b * e * b⁻¹) := by
        rw [← hbg]
        calc b * e * b⁻¹ * (b * g * b⁻¹) = b * (e * g) * b⁻¹ := by group
          _ = b * (g * e) * b⁻¹ := by rw [hcomm e he g hgE]
          _ = b * g * b⁻¹ * (b * e * b⁻¹) := by group
      have hz := commute_sylowH hm hK (hbU e (hEU he)) i
      set y := b * e * b⁻¹
      calc y * sylowB m K 0 1 = y * (sylowB m K 0 1 * sylowH m K 0 i) * (sylowH m K 0 i)⁻¹ := by
            group
        _ = sylowB m K 0 1 * (sylowH m K 0 i * y) * (sylowH m K 0 i)⁻¹ := by rw [hc]; group
        _ = sylowB m K 0 1 * (y * sylowH m K 0 i) * (sylowH m K 0 i)⁻¹ := by rw [hz]
        _ = sylowB m K 0 1 * y := by group
    have hco : ∀ y ∈ E', sylowCoord m K y 0 = 0 ∧ sylowCoord m K y 1 = 0 ∧
        sylowCoord m K y 3 = 0 ∧ sylowCoord m K y 4 = 0 ∧ sylowCoord m K y 10 = 0 :=
      fun y hy => coords_of_commute_sylowB hK (hE'U hy) (hE'C y hy) (hE'sq y hy)
    have hb : ∀ y ∈ E', sylowCoord m K y 1 = 0 := fun y hy => (hco y hy).2.1
    have hker : Nat.card (coordTwoHom hK hE'U hb).ker ≤ q ^ 4 := by
      rw [← Subgroup.card_map_of_injective (f := E'.subtype) E'.subtype_injective]
      have hle : (coordTwoHom hK hE'U hb).ker.map E'.subtype ≤ F4.reeFixedPosUnipotent K m := by
        rintro _ ⟨y, -, rfl⟩
        exact hE'U y.2
      refine (card_le_of_coord_eq_zero hK hle {0, 1, 2, 3, 4, 5, 7, 10} ?_).trans (le_of_eq ?_)
      · rintro _ ⟨y, hy, rfl⟩
        have hy2 := (mem_ker_coordTwoHom hK hE'U hb).1 hy
        obtain ⟨h0, h1', h3, h4, h10⟩ := hco _ y.2
        obtain ⟨-, -, h5, h7, -⟩ := coords_of_sq_of_zero_two hK (hE'U y.2) (hE'sq _ y.2) h0 hy2
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      · rw [hqdef]
        rfl
    calc 4 * Nat.card E = 4 * Nat.card E' := by rw [hcard]
      _ ≤ 4 * (q * Nat.card (coordTwoHom hK hE'U hb).ker) :=
        Nat.mul_le_mul_left _ (card_le_mul_card_ker_coordTwoHom hK hE'U hb)
      _ ≤ 4 * (q * q ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hker)
      _ = 4 * q ^ 5 := by ring
      _ ≤ q ^ 6 := hq5
  ·
    push Not at h2
    have hsub : (E : Set (ModGL F4.tag K)) ⊆
        sylowVec m K '' {x | ∀ i ∈ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 12)), x i = 0} ∪
          sylowVec m K '' {x | ∀ i ∈ ({0, 1, 2, 3, 5, 7, 9} : Finset (Fin 12)), x i = 0} := by
      intro g hg
      obtain ⟨hb, hd, hf, hh, hej⟩ :=
        coords_of_sq_of_zero_two hK (hEU hg) (hsq g hg) (h1 g hg) (h2 g hg)
      rcases mul_eq_zero.1 hej with he | hj
      · refine Or.inl ⟨sylowCoord m K g, ?_, hcrd g hg⟩
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h1 g hg, hb, h2 g hg, hd, he, hf, hh]
      · refine Or.inr ⟨sylowCoord m K g, ?_, hcrd g hg⟩
        intro j hj'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
        rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h1 g hg, hb, h2 g hg, hd, hf, hh, hj]
    have hEn : Nat.card E = (E : Set (ModGL F4.tag K)).ncard := Nat.card_coe_set_eq _
    calc 4 * Nat.card E = 4 * (E : Set (ModGL F4.tag K)).ncard := by rw [hEn]
      _ ≤ 4 * (sylowVec m K '' {x | ∀ i ∈ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 12)), x i = 0} ∪
          sylowVec m K '' {x | ∀ i ∈ ({0, 1, 2, 3, 5, 7, 9} : Finset (Fin 12)), x i = 0}).ncard :=
        Nat.mul_le_mul_left _ (Set.ncard_le_ncard hsub (Set.toFinite _))
      _ ≤ 4 * (_ + _) := Nat.mul_le_mul_left _ (Set.ncard_union_le _ _)
      _ = 4 * (q ^ 5 + q ^ 5) := by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_image_sylowVec hK,
          card_image_sylowVec hK]
        rfl
      _ ≤ q ^ 6 := hq5'

theorem four_mul_card_le_of_isElem2 (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (F4.reeGamma K m)} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) : 4 * Nat.card E ≤ (2 ^ (2 * m + 1)) ^ 6 := by
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
  refine four_mul_card_le_of_le_U hm hK ?_ ?_ ?_
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

theorem card_le_two_pow_of_isElem2 (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (F4.reeGamma K m)} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) : Nat.card E ≤ 2 ^ (6 * (2 * m + 1) - 2) := by
  have h4 := four_mul_card_le_of_isElem2 hm hK hcomm hsq
  have hp : IsPGroup 2 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hsq _ g.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk]
  rw [hk, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, mul_comm (2 * m + 1) 6] at h4
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Coord

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
