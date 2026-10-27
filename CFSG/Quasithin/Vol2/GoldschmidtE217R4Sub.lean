module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE217Wire
public import CFSG.Quasithin.Background.B5NonB
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E217R4

variable {G : Type} [Group G] [Finite G]

theorem e217ConclOne_of_isSolvable_le {H T M V : Subgroup G} (h : E2.Hyp28 H T M V)
    (hchar : CharTwo H) (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI h.elem H))
    (hres : twoResidual M ≤ Subgroup.centralizer (V : Set G)) (hV16 : Nat.card V = 2 ^ 4)
    (hsolv : Group.IsSolvable H) : E2.E217ConclOne H V := by
  obtain ⟨U, x, z₀, d₀⟩ := E2.DihedralPair.exists_of_isSolvable h.minParabolic hsolv hchar h.le_T
    h.normal_T h.elem h.not_le_pCoreOf
  obtain ⟨z, -, hp, d⟩ := d₀.exists_prime_orderOf
  obtain ⟨hz3, hZ2, hCA, hext, hIP, φ, hφs, hφk⟩ := d.stage_one hp hV16 hq
  have hUQ := d.le_pCoreOf hz3 hV16 hZ2 hCA
  have s : E2.Setting17 H T M V U x z :=
    ⟨d, h.minParabolic, hsolv, hres, hV16, hq, hz3, hZ2, hCA, hUQ⟩
  have hY := s.conjClosure_eq
  unfold E2.E217ConclOne
  rw [hY]
  exact ⟨E2.dpP H V U z, d.PR.trans inf_le_left, hIP, hext, φ, hφs, hφk⟩

theorem charTwo_of_le {H H₀ : Subgroup G} (hchar : CharTwo H) (hQ : pCoreOf 2 H ≤ H₀)
    (hH₀ : H₀ ≤ H) : CharTwo H₀ := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hchar hH₀ hQ

omit [Finite G] in
theorem twoResidual_eq_bot {X : Subgroup G} (hX : IsPGroup 2 X) : twoResidual X = ⊥ := by
  rw [eq_bot_iff]
  refine iInf₂_le ⊥ ⟨bot_le, ?_, fun x hx => ?_⟩
  · rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top
  · obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem nine_dvd_card {H₀ Y B Q : Subgroup G} (hQn : (Q.subgroupOf H₀).Normal) (hBH : B ≤ H₀)
    (hY : Y ≤ H₀) (hidx : Q.relIndex B = 9) (hB9 : ∀ b ∈ B, b ^ 9 ∈ Q)
    (hsq : ∀ b ∈ B, ∃ q ∈ Q, b * q * b ∈ Y) : 9 ∣ Nat.card Y := by
  classical
  set N : Subgroup ↥H₀ := Q.subgroupOf H₀ with hN
  set π : ↥H₀ →* ↥H₀ ⧸ N := QuotientGroup.mk' N with hπ
  set B' : Subgroup ↥H₀ := B.subgroupOf H₀ with hB'
  set Y' : Subgroup ↥H₀ := Y.subgroupOf H₀ with hY'
  have hY'card : Nat.card Y' = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hBcard : Nat.card (B'.map π) = 9 := by
    have hker : ((QuotientGroup.mk' N).domRestrict B').ker = N.subgroupOf B' := by
      rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    have h := Subgroup.index_ker ((QuotientGroup.mk' N).domRestrict B')
    rw [hker, MonoidHom.domRestrict_range] at h
    rw [← h]
    exact (Subgroup.relIndex_subgroupOf hBH).trans hidx
  have hle : B'.map π ≤ Y'.map π := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨q, hq, hbq⟩ := hsq b.1 hb
    have hqH : q ∈ H₀ := by
      have h1 : (b : G)⁻¹ * (b * q * b) * (b : G)⁻¹ ∈ H₀ :=
        H₀.mul_mem (H₀.mul_mem (H₀.inv_mem b.2) (hY hbq)) (H₀.inv_mem b.2)
      simpa [mul_assoc] using h1
    have hπq : π ⟨q, hqH⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hq
    have hbY : (⟨b * q * b, hY hbq⟩ : ↥H₀) ∈ Y' := hbq
    have hb' : (⟨b * q * b, hY hbq⟩ : ↥H₀) = b * ⟨q, hqH⟩ * b := rfl
    have hπb : π ⟨b * q * b, hY hbq⟩ = π b ^ 2 := by
      rw [hb', map_mul, map_mul, hπq, mul_one, sq]
    have h9 : π b ^ 9 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 (hB9 b.1 hb)
    have h5 : π b = (π ⟨b * q * b, hY hbq⟩) ^ 5 := by
      rw [hπb, ← pow_mul]
      calc π b = π b ^ 9 * π b := by rw [h9, one_mul]
        _ = π b ^ (2 * 5) := by rw [← pow_succ]
    rw [h5]
    exact Subgroup.pow_mem _ (Subgroup.mem_map_of_mem _ hbY) 5
  have h1 : Nat.card (B'.map π) ∣ Nat.card (Y'.map π) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card (Y'.map π) ∣ Nat.card Y' := Subgroup.card_map_dvd Y' π
  rw [hBcard] at h1
  rw [hY'card] at h2
  exact h1.trans h2

theorem false_of_subparabolic {H T M V H₀ B : Subgroup G} (h : E2.Hyp28 H T M V)
    (hchar : CharTwo H) (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI h.elem H))
    (hV16 : Nat.card V = 2 ^ 4)
    (hQ : pCoreOf 2 H ≤ H₀) (hH₀ : H₀ ≤ H) (hVH₀ : V ≤ H₀)
    (hsyl : IsSylowTwoOf (T ⊓ H₀) H₀)
    (hnn : ¬ H₀ ≤ Subgroup.normalizer ((T ⊓ H₀ : Subgroup G) : Set G))
    (hmax : ∀ Y : Subgroup G, T ⊓ H₀ ≤ Y → Y < H₀ → Y ≤ T ⊓ H₀)
    (hker : ¬ V ≤ kerIn (T ⊓ H₀) H₀) (hsolv : Group.IsSolvable H₀) (hBH₀ : B ≤ H₀)
    (hidx : (pCoreOf 2 H).relIndex B = 9) (hB9 : ∀ b ∈ B, b ^ 9 ∈ pCoreOf 2 H) {v : G}
    (hv : v ∈ V) (hinv : ∀ b ∈ B, v * b * v⁻¹ * b ∈ pCoreOf 2 H) : False := by
  set T₀ := T ⊓ H₀ with hT₀
  have hVT₀ : V ≤ T₀ := le_inf h.le_T hVH₀
  have hT₀V : T₀ ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans h.normal_T
  have hlt : T₀ < H₀ := lt_of_le_of_ne inf_le_right fun heq => hnn (heq ▸ Subgroup.le_normalizer)
  have hmp : MinParabolic H₀ T₀ T₀ := by
    refine ⟨hsyl, hnn, ?_⟩
    rw [isUniqueMaxOver_iff]
    refine ⟨⟨hlt, fun K hK hKH => ?_⟩, le_rfl, fun N hN hTN => ?_⟩
    · by_contra hne
      exact absurd (hmax K hK.le (lt_of_le_of_ne hKH hne)) (not_le_of_gt hK)
    · exact le_antisymm (hmax N hTN hN.1) hTN
  have hVpc : V ≤ pCoreOf 2 T₀ :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V T₀ hVT₀
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVT₀).2 hT₀V)
      (B6.isPGroup_of_isElemAbelian h.elem)
  have hyp : E2.Hyp28 H₀ T₀ T₀ V :=
    ⟨hmp, B5.sqtk_of_le h.sqtk hH₀, hVT₀, hT₀V, h.elem, hVpc, hker⟩
  have hmono : autI h.elem H₀ ≤ autI h.elem H :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hH₀)
  have hq₀ : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hyp.elem H₀) :=
    hq.trans (kq_le_kq_of_le216 hmono 3)
  have hres₀ : twoResidual T₀ ≤ Subgroup.centralizer (V : Set G) := by
    rw [twoResidual_eq_bot hsyl.2.1]
    exact bot_le
  obtain ⟨D, hDY, -, hD, φ, hφs, hφk⟩ := e217ConclOne_of_isSolvable_le hyp
    (charTwo_of_le hchar hQ hH₀) hq₀ hres₀ hV16 hsolv
  have hYH : conjClosure V H₀ ≤ H₀ := by
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, w, hw, rfl⟩
    exact H₀.mul_mem (H₀.mul_mem hg (hVH₀ hw)) (H₀.inv_mem hg)
  have hYcard : Nat.card (conjClosure V H₀) = 192 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range = 6 := by
      rw [MonoidHom.range_eq_top.2 hφs, Subgroup.card_top, Nat.card_perm]
      simp [Nat.factorial]
    have h3 : Nat.card φ.ker = 32 := by
      rw [hφk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv, hD.2.1]
      norm_num
    rw [h2, h3] at h1
    omega
  have hQn : ((pCoreOf 2 H).subgroupOf H₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ).2 (hH₀.trans (le_normalizer_pCoreOf 2 H))
  have hsq : ∀ b ∈ B, ∃ q ∈ pCoreOf 2 H, b * q * b ∈ conjClosure V H₀ := by
    intro b hb
    refine ⟨v * b⁻¹ * v⁻¹ * b⁻¹, hinv b⁻¹ (B.inv_mem hb), ?_⟩
    have h1 : b * v * b⁻¹ ∈ conjClosure V H₀ := mem_conjClosure (hBH₀ hb) hv
    have h2 : v⁻¹ ∈ conjClosure V H₀ := by
      have := mem_conjClosure (Z := V) (H := H₀) H₀.one_mem (V.inv_mem hv)
      simpa using this
    have h3 : b * (v * b⁻¹ * v⁻¹ * b⁻¹) * b = (b * v * b⁻¹) * v⁻¹ := by group
    rw [h3]
    exact Subgroup.mul_mem _ h1 h2
  have hdvd := nine_dvd_card hQn hBH₀ hYH hidx hB9 hsq
  rw [hYcard] at hdvd
  omega

end E217R4

end CFSG.Quasithin
