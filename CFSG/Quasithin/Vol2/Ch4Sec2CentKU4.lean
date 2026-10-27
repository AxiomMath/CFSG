module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoreA
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKU1

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {n : ℕ}

private theorem psl2_card_strictMono_centKU4 {a b : ℕ} (hab : a < b) :
    2 ^ a * (4 ^ a - 1) < 2 ^ b * (4 ^ b - 1) := by
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : 4 ^ a < 4 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h3 : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have h4 : 4 ^ a - 1 < 4 ^ b - 1 := by omega
  exact Nat.mul_lt_mul'' h1 h4

private theorem psl2_card_injective_centKU4 {a b : ℕ}
    (h : 2 ^ a * (4 ^ a - 1) = 2 ^ b * (4 ^ b - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact absurd h (psl2_card_strictMono_centKU4 hab).ne
  · rfl
  · exact absurd h (psl2_card_strictMono_centKU4 hab).ne'

private theorem conjClosure_eq_self_centKU4 {X Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (X : Set G)) : conjClosure X Y = X :=
  le_antisymm (conjClosure_le fun _ hk z hz => (Subgroup.mem_normalizer_iff.mp (hY hk) z).mp hz)
    (le_conjClosure X Y)

private theorem isPSL_modO2_of_eq_centKU4 {X Y : Subgroup G} {m : ℕ} (h : X = Y)
    (hP : IsPSL 2 2 m (ModO2 X)) : IsPSL 2 2 m (ModO2 Y) := by
  subst h
  exact hP

private theorem pCoreOf_subgroupOf_centKU4 (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  unfold pCoreOf
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

private theorem relIndex_ne_zero_centKU4 (A B : Subgroup G) : A.relIndex B ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

private theorem card_modO2_eq_relIndex_centKU4 (L : Subgroup G) :
    Nat.card (ModO2 L) = (pCoreOf 2 L).relIndex L := by
  rw [Subgroup.relIndex, pCoreOf_subgroupOf_centKU4, Subgroup.index_eq_card]

theorem card_field_eq (s : Setting28 T M L Mm I H K n) {F₂ : Type} [Field F₂] [Fintype F₂]
    {α : ↥K →* ↥(StatedSL 3 F₂)} (hαm : IsModO2Surj K α) : Fintype.card F₂ = 2 ^ n := by
  obtain ⟨n₁, F₁, _, _, -, hF₁, ⟨e₁⟩, -, -, -, hPSL₁, -⟩ :=
    (s.c.c41Case3_of_isC134Case2 s.h2).2
  have hPSL₁' := isPSL_modO2_of_eq_centKU4 (conjClosure_eq_self_centKU4 s.c.LH_normal) hPSL₁
  have hn₁n : n₁ = n :=
    psl2_card_injective_centKU4 ((F420.card_of_statedPSL_two_two hPSL₁').symm.trans
      (F420.card_of_statedPSL_two_two s.hn))
  have hFeq : Fintype.card F₁ = Fintype.card F₂ :=
    card_eq_of_card_statedSL_eq ((Nat.card_congr e₁.toEquiv).symm.trans
      (card_modO2_of_surjective α hαm.1 hαm.2))
  rw [← hFeq, hF₁, hn₁n]

theorem card_modO2_eq (s : Setting28 T M L Mm I H K n) {H₁ K₁ : Subgroup G}
    (c₁ : Conf4212 G T M L I H₁ K₁) (hL₁ : perfectCore (L ⊓ H₁) = perfectCore (L ⊓ H))
    (h2₁ : IsC134Case 2 (K₁ ⊔ pCoreOf 2 I) (pCoreOf 2 I) K₁) :
    Nat.card (ModO2 K₁) = Nat.card (ModO2 K) := by
  obtain ⟨n₁, F₁, _, _, -, hF₁, ⟨e₁⟩, -, -, -, hPSL₁, -⟩ :=
    (s.c.c41Case3_of_isC134Case2 s.h2).2
  obtain ⟨n₂, F₂, _, _, -, hF₂, ⟨e₂⟩, -, -, -, hPSL₂, -⟩ :=
    (c₁.c41Case3_of_isC134Case2 h2₁).2
  have hcc₁ : conjClosure (perfectCore (L ⊓ H₁)) (H₁ ⊓ M) = perfectCore (L ⊓ H₁) :=
    conjClosure_eq_self_centKU4 c₁.LH_normal
  have hPSL₁' := isPSL_modO2_of_eq_centKU4 (conjClosure_eq_self_centKU4 s.c.LH_normal) hPSL₁
  have hPSL₂' := isPSL_modO2_of_eq_centKU4 (hcc₁.trans hL₁) hPSL₂
  have hn₁n : n₁ = n :=
    psl2_card_injective_centKU4 ((F420.card_of_statedPSL_two_two hPSL₁').symm.trans
      (F420.card_of_statedPSL_two_two s.hn))
  have hn₂n : n₂ = n :=
    psl2_card_injective_centKU4 ((F420.card_of_statedPSL_two_two hPSL₂').symm.trans
      (F420.card_of_statedPSL_two_two s.hn))
  rw [Nat.card_congr e₂.toEquiv, Nat.card_congr e₁.toEquiv, card_statedSL_three,
    card_statedSL_three, hF₂, hF₁, hn₂n, hn₁n]

theorem K₁_le_K (s : Setting28 T M L Mm I H K n) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {H₁ K₁ : Subgroup G} (c₁ : Conf4212 G T M L I H₁ K₁)
    (hKK₁ : K ≤ K₁) (hH₁K₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G))
    (hcard : Nat.card (ModO2 K₁) = Nat.card (ModO2 K)) : K₁ ≤ K := by
  have hK₁H₁ : K₁ ≤ H₁ := le_of_mem_cComp c₁.K_mem
  have hU₁H₁ : pCoreOf 2 K₁ ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K₁).trans hK₁H₁)
      (hH₁K₁.trans (normalizer_le_normalizer_pCoreOf 2 K₁)) (pCoreOf_isPGroup 2 K₁)
  have h5 := lemma_4_1_4_five (s.hy.hyp4_1_1 h37 h38 h39) s.hy.sigma s.hy.gammaStar
    c₁.inH c₁.not_le
  have hU₁I : pCoreOf 2 K₁ ≤ pCoreOf 2 I := hU₁H₁.trans (h5.2.2.1.trans h5.2.2.2)
  have hU₁N : pCoreOf 2 K₁ ≤ Subgroup.normalizer (K : Set G) :=
    hU₁I.trans ((pCoreOf_le 2 I).trans (s.c.inH.1.trans s.hKH))
  have hK₁N : K₁ ≤ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) := le_normalizer_pCoreOf 2 K₁
  have hKN : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 K₁ : Subgroup G) : Set G) := by
    intro k hk
    have hk₁ := Subgroup.mem_normalizer_iff.mp (hK₁N (hKK₁ hk))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), (hk₁ x).mp hxU⟩
    · intro hx
      obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, (hk₁ x).mpr hxU⟩
      have e : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      have h := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      rwa [e] at h
  have hPG : IsPGroup 2 ↥(K ⊓ pCoreOf 2 K₁) := (pCoreOf_isPGroup 2 K₁).to_le inf_le_right
  have hKUU : K ⊓ pCoreOf 2 K₁ ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hKN hPG
  obtain ⟨Ku, hKu⟩ : ∃ X : Subgroup K₁, X = K.subgroupOf K₁ := ⟨_, rfl⟩
  obtain ⟨Uu, hUu⟩ : ∃ X : Subgroup K₁, X = (pCoreOf 2 K₁).subgroupOf K₁ := ⟨_, rfl⟩
  obtain ⟨Uo, hUo⟩ : ∃ X : Subgroup K₁, X = (pCoreOf 2 K).subgroupOf K₁ := ⟨_, rfl⟩
  have hUuN : Uu.Normal := by
    rw [hUu]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 K₁)).mpr
      (le_normalizer_pCoreOf 2 K₁)
  have hidx₁ : Uu.index = Nat.card (ModO2 K₁) := by
    rw [hUu, pCoreOf_subgroupOf_centKU4, Subgroup.index_eq_card]
  have hidxK : Uo.relIndex Ku = Nat.card (ModO2 K) := by
    rw [hUo, hKu, Subgroup.relIndex_subgroupOf hKK₁, card_modO2_eq_relIndex_centKU4]
  have hYX : Uu ⊓ Ku ≤ Uo ⊓ Ku := by
    intro x hx
    obtain ⟨hxU, hxK⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, hxK⟩
    rw [hUu, Subgroup.mem_subgroupOf] at hxU
    rw [hKu, Subgroup.mem_subgroupOf] at hxK
    rw [hUo, Subgroup.mem_subgroupOf]
    exact hKUU (Subgroup.mem_inf.mpr ⟨hxK, hxU⟩)
  have hle : Uo.relIndex Ku ≤ Uu.relIndex Ku := by
    have h1 : Uu.relIndex Ku = (Uu ⊓ Ku).relIndex Ku :=
      (Subgroup.inf_relIndex_right Uu Ku).symm
    have h2 : (Uu ⊓ Ku).relIndex Ku = (Uu ⊓ Ku).relIndex (Uo ⊓ Ku) * (Uo ⊓ Ku).relIndex Ku :=
      (Subgroup.relIndex_mul_relIndex (Uu ⊓ Ku) (Uo ⊓ Ku) Ku hYX inf_le_right).symm
    have h3 : (Uo ⊓ Ku).relIndex Ku = Uo.relIndex Ku := Subgroup.inf_relIndex_right Uo Ku
    rw [h1, h2, h3]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (relIndex_ne_zero_centKU4 _ _))
  have hsup : Uu.relIndex (Ku ⊔ Uu) = Uu.relIndex Ku := by
    haveI := hUuN
    exact Subgroup.relIndex_sup_right Ku Uu
  have hmul : Uu.relIndex (Ku ⊔ Uu) * (Ku ⊔ Uu).index = Uu.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have hUuidx : Uu.index = Uo.relIndex Ku := by rw [hidx₁, hcard, hidxK]
  have hPidx : (Ku ⊔ Uu).index = 1 := by
    have hpos : Uu.relIndex (Ku ⊔ Uu) ≠ 0 := relIndex_ne_zero_centKU4 _ _
    have hp0 : (Ku ⊔ Uu).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hcle : Uu.relIndex (Ku ⊔ Uu) * (Ku ⊔ Uu).index ≤ Uu.relIndex (Ku ⊔ Uu) * 1 := by
      rw [hmul, hUuidx, mul_one, hsup]
      exact hle
    have hp1 := Nat.le_of_mul_le_mul_left hcle (Nat.pos_of_ne_zero hpos)
    omega
  have hPtop : Ku ⊔ Uu = ⊤ := Subgroup.index_eq_one.mp hPidx
  have hK₁le : K₁ ≤ K ⊔ pCoreOf 2 K₁ := by
    intro x hx
    have hxP : (⟨x, hx⟩ : ↥K₁) ∈ Ku ⊔ Uu := by
      rw [hPtop]
      exact Subgroup.mem_top _
    have hPQ : Ku ⊔ Uu ≤ (K ⊔ pCoreOf 2 K₁ : Subgroup G).subgroupOf K₁ := by
      refine sup_le ?_ ?_
      · intro y hy
        rw [hKu, Subgroup.mem_subgroupOf] at hy
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hy)
      · intro y hy
        rw [hUu, Subgroup.mem_subgroupOf] at hy
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hy)
    exact Subgroup.mem_subgroupOf.mp (hPQ hxP)
  have hK₁le' : K₁ ≤ pCoreOf 2 K₁ ⊔ K := by
    rw [sup_comm]
    exact hK₁le
  exact le_of_perfect_of_le_sup_coreA (perfect_of_mem_cComp c₁.K_mem) hU₁N
    (CFSG.Quasithin.isSolvable_pCoreOf_two K₁) hK₁le'

end CFSG.Quasithin.H13.Ch4.CentK
