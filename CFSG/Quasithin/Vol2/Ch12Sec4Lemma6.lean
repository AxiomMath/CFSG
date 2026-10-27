module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative Pointwise

@[expose] def NormalizerR1Le1246 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G)

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf [Finite G] {g x : G} (hg : orderOf g = 2)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hg] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  interval_cases k <;> simp

section L3

variable [Finite G] {T L V : Subgroup G} {z : G} [IsMulCommutative ↥V]

theorem cx_four_subgroup (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (hV16 : Nat.card V = 2 ^ 4) (hnat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1)
    {E : Subgroup G} (hEV : E ≤ V) (hE4 : Nat.card E = 4)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) {v : G} (hvE : v ∈ E)
    (hvL : v ∉ Subgroup.centralizer (L : Set G)) :
    z ∈ E ∧ E = Subgroup.zpowers v ⊔ Subgroup.zpowers z ∧
      ∀ t ∈ T, t * v * t⁻¹ = v ∨ t * v * t⁻¹ = v * z := by
  have hyp := hcx.hyp
  have hTp : IsPGroup 2 T := hyp.sylow.1
  have hET : E ≤ T := hEV.trans hf.le_T
  have hE1 : E ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hE4
    norm_num at hE4
  obtain ⟨⟨e, heE, heT⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (inf_centralizer_ne_bot_of_isPGroup hTp hET hTE hE1)
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heL := cx_inf_centralizer_T_le hcx hf hV16 hnat ⟨hEV heE, heT⟩
  have hez := hf.eq_of_mem_zV ⟨hEV heE, heL⟩ he1'
  have hzE : z ∈ E := hez ▸ heE
  have hv1 : v ≠ 1 := fun h => hvL (h ▸ Subgroup.one_mem _)
  have hvz : v ≠ z := fun h => hvL (h ▸ hf.mem_zV.2)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (hf.sq v (hEV hvE)) hv1
  have hcomm : ∀ a ∈ Subgroup.zpowers v, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    have hVV := hf.le_centralizer
    have haV : a ∈ V := (Subgroup.zpowers_le.2 (hEV hvE)) ha
    have hbV : b ∈ V := (Subgroup.zpowers_le.2 hf.mem_zV.1) hb
    exact (Subgroup.mem_centralizer_iff.1 (hVV haV) b hbV).symm
  have hinf : Subgroup.zpowers v ⊓ Subgroup.zpowers z = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf hv2 hx.1 with h | h
    · exact h ▸ Subgroup.one_mem _
    · rcases eq_one_or_eq_of_mem_zpowers_of_orderOf hf.order hx.2 with h' | h'
      · exact h' ▸ Subgroup.one_mem _
      · exact absurd (h.symm.trans h') hvz
  have hK4 : Nat.card ↥(Subgroup.zpowers v ⊔ Subgroup.zpowers z) = 4 := by
    have h1 := B2F.card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hv2, hf.order] at h1
    exact h1
  have hKE : Subgroup.zpowers v ⊔ Subgroup.zpowers z ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hvE) (Subgroup.zpowers_le.2 hzE)
  have hEK : E = Subgroup.zpowers v ⊔ Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge hKE (by rw [hE4, hK4])).symm
  refine ⟨hzE, hEK, fun t ht => ?_⟩
  have htv : t * v * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hTE ht) v).1 hvE
  have hzN : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have h1 : t * v * t⁻¹ ∈ (Subgroup.zpowers v : Set G) * (Subgroup.zpowers z : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzN, ← hEK]
    exact htv
  obtain ⟨a, ha, b, hb, hab⟩ := h1
  simp only at hab
  have htz : t * z * t⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (hf.T_le_centralizer hyp.normalizes ht),
      mul_inv_cancel_right]
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf hv2 ha with ha1 | hav <;>
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf hf.order hb with hb1 | hbz
  · exfalso
    apply hv1
    have : t * v * t⁻¹ = 1 := by rw [← hab, ha1, hb1, one_mul]
    calc v = t⁻¹ * (t * v * t⁻¹) * t := by group
      _ = 1 := by rw [this]; group
  · exfalso
    apply hvz
    have : t * v * t⁻¹ = t * z * t⁻¹ := by rw [← hab, ha1, hbz, one_mul, htz]
    calc v = t⁻¹ * (t * v * t⁻¹) * t := by group
      _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [this]
      _ = z := by group
  · left
    rw [← hab, hav, hb1, mul_one]
  · right
    rw [← hab, hav, hbz]

theorem cx_relIndex_eq_two (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (hV16 : Nat.card V = 2 ^ 4) (hnat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1)
    {E : Subgroup G} (hEV : E ≤ V) (hE4 : Nat.card E = 4)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) {v : G} (hvE : v ∈ E)
    (hvL : v ∉ Subgroup.centralizer (L : Set G)) :
    T ⊓ Subgroup.centralizer (E : Set G) = T ⊓ Subgroup.centralizer ({v} : Set G) ∧
      (T ⊓ Subgroup.centralizer (E : Set G)).relIndex T = 2 := by
  have hyp := hcx.hyp
  obtain ⟨hzE, hEK, hact⟩ := cx_four_subgroup hcx hf hV16 hnat hEV hE4 hTE hvE hvL
  have hTz := hf.T_le_centralizer hyp.normalizes
  have hR : T ⊓ Subgroup.centralizer (E : Set G) = T ⊓ Subgroup.centralizer ({v} : Set G) := by
    ext t
    simp only [Subgroup.mem_inf]
    refine and_congr_right fun ht => ⟨fun h => ?_, fun h => ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 h v hvE).symm
    · have hle : E ≤ Subgroup.centralizer ({t} : Set G) := by
        rw [hEK]
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 (hTz ht)).symm
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  refine ⟨hR, ?_⟩
  rw [hR]
  obtain ⟨t₀, ht₀, ht₀v⟩ : ∃ t₀ ∈ T, t₀ * v * t₀⁻¹ ≠ v := by
    by_contra h
    push Not at h
    apply hvL
    apply cx_inf_centralizer_T_le hcx hf hV16 hnat
    refine ⟨hEV hvE, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    calc t * v = t * v * t⁻¹ * t := by group
      _ = v * t := by rw [h t ht]
  have ht₀z : t₀ * v * t₀⁻¹ = v * z := (hact t₀ ht₀).resolve_left ht₀v
  have hz2 : z * z = 1 := by rw [← pow_two, ← hf.order, pow_orderOf_eq_one]
  have hvz' : v * z ≠ v := fun h => hf.ne_one (by
    calc z = v⁻¹ * (v * z) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have hmem : ∀ b ∈ T, b ∈ Subgroup.centralizer ({v} : Set G) ↔ b * v * b⁻¹ = v := by
    intro b _
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [h, mul_inv_cancel_right]
    · intro h
      calc b * v = b * v * b⁻¹ * b := by group
        _ = v * b := by rw [h]
  show ((T ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf T).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t₀, ht₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  have hbt : (b : G) * t₀ ∈ T := T.mul_mem b.2 ht₀
  rw [hmem _ hbt, hmem _ b.2]
  have e1 : (b : G) * t₀ * v * ((b : G) * t₀)⁻¹ = (b : G) * v * (b : G)⁻¹ * z := by
    have htz : (b : G) * z * (b : G)⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 (hTz b.2), mul_inv_cancel_right]
    calc (b : G) * t₀ * v * ((b : G) * t₀)⁻¹ = (b : G) * (t₀ * v * t₀⁻¹) * (b : G)⁻¹ := by group
      _ = (b : G) * (v * z) * (b : G)⁻¹ := by rw [ht₀z]
      _ = (b : G) * v * (b : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) := by group
      _ = (b : G) * v * (b : G)⁻¹ * z := by rw [htz]
  rw [e1]
  rcases hact b b.2 with h | h
  · rw [h]
    exact Or.inr ⟨⟨b.2, rfl⟩, fun h' => hvz' h'.2⟩
  · rw [h, mul_assoc, hz2, mul_one]
    exact Or.inl ⟨⟨hbt, rfl⟩, fun h' => hvz' h'.2⟩

theorem cx_two_mul_card_le (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (hV16 : Nat.card V = 2 ^ 4) (hnat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1)
    {v : G} (hvV : v ∈ V) (hvL : v ∉ Subgroup.centralizer (L : Set G)) {P : Subgroup G}
    (hPM : P ≤ Subgroup.normalizer (L : Set G)) (hPv : P ≤ Subgroup.centralizer ({v} : Set G))
    (hP : IsPGroup 2 P) : 2 * Nat.card P ≤ Nat.card T := by
  have hyp := hcx.hyp
  have hTM : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hyp.normalizes
  obtain ⟨S, hPS, hS⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hPM hP
  obtain ⟨m, hm, hSm⟩ := hTM.exists_conj hS
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hf.MN ▸ hm
  have hSv : ¬ S ≤ Subgroup.centralizer ({v} : Set G) := by
    intro h
    have hw : m⁻¹ * v * m ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hmV) v).1 hvV
      rwa [inv_inv] at h1
    have hwL : m⁻¹ * v * m ∉ Subgroup.centralizer (L : Set G) := by
      intro hw'
      apply hvL
      have h1 := (Subgroup.mem_normalizer_iff.1
        (F7.normalizer_le_normalizer_centralizer L hm) _).1 hw'
      rwa [show m * (m⁻¹ * v * m) * m⁻¹ = v by group] at h1
    apply hwL
    apply cx_inf_centralizer_T_le hcx hf hV16 hnat
    refine ⟨hw, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    have h1 : m * t * m⁻¹ ∈ S := by
      rw [hSm]
      exact ⟨t, ht, rfl⟩
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 (h h1)
    calc t * (m⁻¹ * v * m) = m⁻¹ * ((m * t * m⁻¹) * v) * m := by group
      _ = m⁻¹ * (v * (m * t * m⁻¹)) * m := by rw [h2]
      _ = m⁻¹ * v * m * t := by group
  have hne : S ⊓ Subgroup.centralizer ({v} : Set G) ≠ S := fun h => hSv (h ▸ inf_le_right)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : S ⊓ Subgroup.centralizer
    ({v} : Set G) ≤ S)
  have hk1 : k ≠ 1 := fun h1 => hne (Subgroup.eq_of_le_of_card_ge inf_le_left
    (by rw [hk, h1, mul_one]))
  have hk0 : k ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hk
    exact Nat.card_pos.ne' hk
  have hST : Nat.card S = Nat.card T := by rw [hS.card_eq, hTM.card_eq]
  have hPle : Nat.card P ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({v} : Set G)) :=
    Subgroup.card_le_of_le (le_inf hPS hPv)
  have h2 : Nat.card ↥(S ⊓ Subgroup.centralizer ({v} : Set G)) * 2 ≤ Nat.card S := by
    rw [hk]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

end L3

theorem lemma12_4_6_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (hN : NormalizerR1Le1246) : Lemma12_4_6 := by
  intro G _ _ T L V hcx h3' E hEV hE4 hTE v hvE hvL
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hcx (Or.inl h3')
  have := hf.comm
  obtain ⟨hV16, -, -, hnat⟩ := cx_l3_module h1222 hcx hf h3'
  obtain ⟨hR, hidx⟩ := cx_relIndex_eq_two hcx hf hV16 hnat hEV hE4 hTE hvE hvL
  refine ⟨?_, hidx⟩
  have hR₁v : T ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({v} : Set G) :=
    hR ▸ inf_le_right
  have hR₁p : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (E : Set G)) := hyp.sylow.1.to_le inf_le_left
  have hcardR : Nat.card T = 2 * Nat.card ↥(T ⊓ Subgroup.centralizer (E : Set G)) := by
    have h1 := Subgroup.relIndex_mul_card (T ⊓ Subgroup.centralizer (E : Set G)) T
    rw [show T ⊓ Subgroup.centralizer (E : Set G) ⊓ T =
      T ⊓ Subgroup.centralizer (E : Set G) from inf_eq_left.2 inf_le_left, hidx] at h1
    exact h1.symm
  obtain ⟨S, hRS, hS⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hR₁v hR₁p
  suffices hSR : S = T ⊓ Subgroup.centralizer (E : Set G) by
    rw [← hSR]
    exact hS
  by_contra hne
  have hlt : T ⊓ Subgroup.centralizer (E : Set G) < S := lt_of_le_of_ne hRS (Ne.symm hne)
  have : Group.IsNilpotent ↥S := hS.isPGroup.isNilpotent
  have hRS' : (T ⊓ Subgroup.centralizer (E : Set G)).subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne (le_antisymm (fun x hx => ?_) hRS)
    have h1 : (⟨x, hx⟩ : ↥S) ∈ (T ⊓ Subgroup.centralizer (E : Set G)).subgroupOf S :=
      h ▸ Subgroup.mem_top _
    exact h1
  obtain ⟨s, hsN, hsR⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hRS')
  have hsN' : (s : G) ∈ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ S
    · have h1 := (Subgroup.mem_normalizer_iff.1 hsN) ⟨y, hy⟩
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h1
    · constructor
      · intro h
        exact absurd (hRS h) hy
      · intro h
        exfalso
        apply hy
        have h2 := S.mul_mem (S.mul_mem (S.inv_mem s.2) (hRS h)) s.2
        rwa [show (s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * s = y by group] at h2
  set N := S ⊓ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G)
  have hNM : N ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_right.trans (hN G T L V hcx h3' E hEV hE4 hTE)
  have hNv : N ≤ Subgroup.centralizer ({v} : Set G) := inf_le_left.trans hS.le
  have hNp : IsPGroup 2 N := hS.isPGroup.to_le inf_le_left
  have h2N := cx_two_mul_card_le hcx hf hV16 hnat (hEV hvE) hvL hNM hNv hNp
  have hRN : T ⊓ Subgroup.centralizer (E : Set G) < N := by
    refine lt_of_le_of_ne (le_inf hRS Subgroup.le_normalizer) fun h => hsR ?_
    have h1 : (s : G) ∈ N := ⟨s.2, hsN'⟩
    rw [← h] at h1
    exact h1
  have := Subgroup.card_lt_of_lt hRN
  omega

end CFSG.Quasithin.H13
