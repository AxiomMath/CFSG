module

public import CFSG.Quasithin.Background.SmithB42F4Base

public section

namespace CFSG.Quasithin.B42F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution


variable {m : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K F4.prime]

omit [Finite K] [CharP K F4.prime] in
theorem eight_le_q (hm : 1 ≤ m) : 8 ≤ 2 ^ (2 * m + 1) :=
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Finite K] [CharP K F4.prime] in
theorem mem_map_conj {E : Subgroup (ModGL F4.tag K)} {b y : ModGL F4.tag K} :
    y ∈ E.map (MulAut.conj b).toMonoidHom ↔ ∃ e ∈ E, b * e * b⁻¹ = y := by
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem card_lt_of_le_U (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (ModGL F4.tag K)} (hEU : E ≤ F4.reeFixedPosUnipotent K m)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1) :
    Nat.card E < (2 ^ (2 * m + 1)) ^ 6 := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have hq := eight_le_q hm
  set q := 2 ^ (2 * m + 1) with hqdef
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
    have hE'C : E' ≤ F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowA m K 1} := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
      refine Subgroup.mem_inf.2 ⟨hbU e (hEU he), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hbg]
      calc b * e * b⁻¹ * (b * g * b⁻¹) = b * (e * g) * b⁻¹ := by group
        _ = b * (g * e) * b⁻¹ := by rw [hcomm e he g hgE]
        _ = b * g * b⁻¹ * (b * e * b⁻¹) := by group
    have hdC : sylowVec m K ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] ∈
        F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowA m K 1} := by
      rw [← SetLike.mem_coe, centralizer_sylowA_one hK]
      exact ⟨_, by simp, rfl⟩
    have hdE : sylowVec m K ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] ∉ E' := by
      intro hd
      obtain ⟨e, he, he'⟩ := mem_map_conj.1 hd
      have h2 : sylowV m K 0 0 0 1 0 0 0 0 0 0 0 0 ^ 2 = 1 := by
        change sylowVec m K ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] ^ 2 = 1
        rw [← he']
        exact conj_sq_eq_one (hsq e he)
      exact one_ne_zero (sq_eq_one_d h2)
    have hlt : E' < F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowA m K 1} :=
      lt_of_le_of_ne hE'C (fun h => hdE (h ▸ hdC))
    calc Nat.card E = Nat.card E' := hcard.symm
      _ < Nat.card (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowA m K 1} :
          Subgroup (ModGL F4.tag K)) := Subgroup.card_lt_of_lt hlt
      _ = q ^ 6 := card_centralizer_of_eq hK (centralizer_sylowA_one hK) {1, 2, 5, 6, 7, 9}
          (by ext x; simp)
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
    have hq5 : q * q ^ 4 < q ^ 6 := by
      have : q * q ^ 4 = q ^ 5 := by ring
      rw [this]
      exact Nat.pow_lt_pow_right (by omega) (by norm_num)
    calc Nat.card E = Nat.card E' := hcard.symm
      _ ≤ q * Nat.card (coordTwoHom hK hE'U hb).ker := card_le_mul_card_ker_coordTwoHom hK hE'U hb
      _ ≤ q * q ^ 4 := Nat.mul_le_mul_left _ hker
      _ < q ^ 6 := hq5
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
    have h5 : q ^ 5 + q ^ 5 < q ^ 6 := by
      have : q ^ 6 = q * q ^ 5 := by ring
      rw [this]
      have : 0 < q ^ 5 := by positivity
      nlinarith
    calc Nat.card E = (E : Set (ModGL F4.tag K)).ncard := (Nat.card_coe_set_eq _)
      _ ≤ (sylowVec m K '' {x | ∀ i ∈ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 12)), x i = 0} ∪
          sylowVec m K '' {x | ∀ i ∈ ({0, 1, 2, 3, 5, 7, 9} : Finset (Fin 12)), x i = 0}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ _ := Set.ncard_union_le _ _
      _ = q ^ 5 + q ^ 5 := by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_image_sylowVec hK,
          card_image_sylowVec hK]
        rfl
      _ < q ^ 6 := h5

theorem card_lt_of_isElem2 (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : Subgroup (F4.reeGamma K m)} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) : Nat.card E < (2 ^ (2 * m + 1)) ^ 6 := by
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
  refine card_lt_of_le_U hm hK ?_ ?_ ?_
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

end CFSG.Quasithin.B42F4
