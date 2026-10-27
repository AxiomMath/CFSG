module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Side
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Model
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.F6.GoldAmN
  CFSG.Quasithin.M12Amal

variable {D : Type*} [Group D]

theorem isCentralProduct_QQ_pow_four {R : Type*} [Group R]
    (h : IsCentralProduct₂ R (QuaternionGroup 2) (QuaternionGroup 2)) (r : R) : r ^ 4 = 1 := by
  obtain ⟨A', B', hsup, hcomm, ⟨eA⟩, ⟨eB⟩, -⟩ := h
  have hr : r ∈ A' ⊔ B' := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm r hr
  have hab : Commute a b := hcomm a ha b hb
  have hQ4 : ∀ z : QuaternionGroup 2, z ^ 4 = 1 := by decide
  have ha4 : a ^ 4 = 1 := by
    have : (⟨a, ha⟩ : ↥A') ^ 4 = 1 := eA.injective (by rw [map_pow, hQ4, map_one])
    simpa using congrArg Subtype.val this
  have hb4 : b ^ 4 = 1 := by
    have : (⟨b, hb⟩ : ↥B') ^ 4 = 1 := eB.injective (by rw [map_pow, hQ4, map_one])
    simpa using congrArg Subtype.val this
  rw [hab.mul_pow, ha4, hb4, one_mul]

variable [Finite D] {G₁ G₂ : Subgroup D}

theorem isGoldCaseM12_of_tuple (h : GoldHyp G₁ G₂) {a b s x ρ : D} (hA : ARel a b s x)
    (hAρ : ARho a b s x ρ) (hTeq : Subgroup.closure ({a, b, s, ρ} : Set D) = G₁ ⊓ G₂)
    (hcard : Nat.card ↥(Subgroup.closure ({a, b, s, ρ} : Set D)) = 64)
    (hG₁ : Subgroup.closure ({a, b, s, ρ, x} : Set D) = G₁)
    (hQ₁ : pCoreOf 2 G₁ = Q1r.map (embR hA.toTRel hAρ.toRhoRel))
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂) (QuaternionGroup 2) (QuaternionGroup 2))
    (hfpf : ∀ y ∈ G₂, y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ pCoreOf 2 G₂, y * q * y⁻¹ = q →
      ∀ v ∈ pCoreOf 2 G₂, q * v = v * q) :
    IsGoldCaseM12 G₂ G₁ := by
  have hT := hA.toTRel
  have hR := hAρ.toRhoRel
  have hinj := embR_injective hT hR hcard
  set φ := embR hT hR with hφ
  have hrange : φ.range = G₁ ⊓ G₂ := by rw [embR_range hT hR, hTeq]
  have hv₁ := h.vertex_left
  have hv₂ := h.vertex_right
  have hcardT : Nat.card ↥(G₁ ⊓ G₂) = 64 := by rw [← hTeq]; exact hcard
  have hQ₂card : Nat.card ↥(pCoreOf 2 G₂) = 32 := by
    have := card_eq_of_relIndex_two h.pCoreOf_right_le h.relIndex_pCoreOf_T_right
    omega
  have hQ₁card : Nat.card ↥(pCoreOf 2 G₁) = 32 := by
    have := card_eq_of_relIndex_two h.pCoreOf_left_le h.relIndex_pCoreOf_T_left
    omega
  have hQ₂T : pCoreOf 2 G₂ ≤ φ.range := by rw [hrange]; exact h.pCoreOf_right_le
  have hmapN : ((pCoreOf 2 G₂).comap φ).map φ = pCoreOf 2 G₂ := Subgroup.map_comap_eq_self hQ₂T
  have hcardN : Nat.card ↥((pCoreOf 2 G₂).comap φ) = 32 := by
    have := Nat.card_congr
      (Subgroup.equivMapOfInjective ((pCoreOf 2 G₂).comap φ) φ hinj).toEquiv
    rw [this, hmapN]
    exact hQ₂card
  have hidx : ((pCoreOf 2 G₂).comap φ).index = 2 := by
    have h1 := Subgroup.card_mul_index ((pCoreOf 2 G₂).comap φ)
    rw [hcardN, card_Tr] at h1
    omega
  have hexp : ∀ w ∈ (pCoreOf 2 G₂).comap φ, w ^ 4 = 1 := by
    intro w hw
    have hw' : φ w ∈ pCoreOf 2 G₂ := hw
    have h4 := isCentralProduct_QQ_pow_four h₂ (⟨φ w, hw'⟩ : ↥(pCoreOf 2 G₂))
    have h5 : (φ w) ^ 4 = 1 := by simpa using congrArg Subtype.val h4
    apply hinj
    rw [map_pow, h5, map_one]
  have hQ₂ : pCoreOf 2 G₂ = Q2r.map φ := by
    rcases eq_Q_of_index_two _ hidx hexp with hN1 | hN2
    · exfalso
      apply h.pCoreOf_ne (by rw [hcardT]; norm_num)
      rw [hQ₁, ← hmapN, hN1]
    · rw [← hmapN, hN2]
  have hGQ : ∀ g ∈ G₂, ∀ q ∈ Q2r.map φ, g * q * g⁻¹ ∈ Q2r.map φ := by
    rw [← hQ₂]
    intro g hg q hq
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hg) q).mp hq
  have hC : ∀ g ∈ G₂, (∀ q ∈ Q2r.map φ, g * q = q * g) → g ∈ Q2r.map φ := by
    rw [← hQ₂]
    intro g hg hc
    apply hv₂.charTwo
    exact ⟨hg, Subgroup.mem_centralizer_iff.mpr fun q hq => (hc q hq).symm⟩
  have hfpf' : ∀ g ∈ G₂, g ≠ 1 → g ^ 3 = 1 → ∀ q ∈ Q2r.map φ, g * q * g⁻¹ = q →
      ∀ v ∈ Q2r.map φ, q * v = v * q := by
    rw [← hQ₂]
    exact hfpf
  have hv₂' : Vertex G₂ (Subgroup.closure ({a, b, s, ρ} : Set D)) := by rw [hTeq]; exact hv₂
  have hN : ¬ G₂ ≤ Subgroup.normalizer ((Nr.map φ : Subgroup D) : Set D) := by
    intro hG₂N
    have hTN := range_le_normalizer_N hT hR
    have hG₁N : G₁ ≤ Subgroup.normalizer ((Nr.map φ : Subgroup D) : Set D) := by
      rw [← hG₁, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hmem : ∀ w : Tr, φ w ∈ Subgroup.normalizer ((Nr.map φ : Subgroup D) : Set D) :=
        fun w => hTN ⟨w, rfl⟩
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · have := hmem rA; rwa [embR_rA hT hR] at this
      · have := hmem rB; rwa [embR_rB hT hR] at this
      · have := hmem rS; rwa [embR_rS hT hR] at this
      · have := hmem rR; rwa [embR_rR hT hR] at this
      · exact aRho_normalizes_N hA hAρ
    have hNT : Nr.map φ ≤ G₁ ⊓ G₂ := by
      rw [← hrange]
      exact Subgroup.map_le_range φ Nr
    have hbot := eq_bot_of_normalizes_vAmalgam h.amalgam hNT hG₁N hG₂N
    have hmem : φ (rA * rA) ∈ Nr.map φ := Subgroup.mem_map_of_mem _ inN_rA_sq
    rw [hbot, Subgroup.mem_bot] at hmem
    exact rA_sq_ne_one (hinj (by rw [hmem, map_one]))
  obtain ⟨y', hy'G, hy'o⟩ := hv₂.exists_order_three
  have hy'3 : y' ^ 3 = 1 := hy'o ▸ pow_orderOf_eq_one y'
  have hy'1 : y' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy'o
    omega
  obtain ⟨y, hyG, hB⟩ := exists_B_elem5 hT hR hcard hv₂' hGQ hC hfpf' hN hy'G hy'3 hy'1
  have hyT : y ∉ Subgroup.closure ({a, b, s, ρ} : Set D) := by
    rw [hTeq]
    exact hv₂.not_mem_of_orderOf (orderOf_eq_prime hB.hy (hB.toMConj.ne_one hT hR hinj))
  have hTG₂ : Subgroup.closure ({a, b, s, ρ} : Set D) ≤ G₂ := by rw [hTeq]; exact inf_le_right
  have hTC : Subgroup.closure ({a, b, s, ρ} : Set D) ≤ Subgroup.closure ({a, b, s, ρ, y} : Set D) :=
    Subgroup.closure_mono (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      tauto)
  have hCG : Subgroup.closure ({a, b, s, ρ, y} : Set D) ≤ G₂ := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hmem : ∀ z ∈ ({a, b, s, ρ} : Set D), z ∈ G₂ := fun z hz =>
      hTG₂ (Subgroup.subset_closure hz)
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hyG
  have hy₂ : Subgroup.closure ({a, b, s, ρ, y} : Set D) = G₂ :=
    le_antisymm hCG (hv₂'.le_of_not_mem hTC hCG (Subgroup.subset_closure (by simp)) hyT)
  have hinf : Subgroup.closure ({a, b, s, ρ, y} : Set D) ⊓
      Subgroup.closure ({a, b, s, ρ, x} : Set D) = Subgroup.closure ({a, b, s, ρ} : Set D) := by
    rw [hy₂, hG₁, hTeq, inf_comm]
  have hiso := isAmalgamIso_of_tuples5 hA hAρ hB model_ARel model_ARho model_MRelB hcard
    model_card_T hinf model_inf
  rw [hy₂, hG₁] at hiso
  refine ⟨isYAmalgam_M12_of_iso hiso, ?_, h.amalgam.quotient₂, h.amalgam.quotient₁, h₂, ?_⟩
  ·
    intro hc
    rcases hc with hc | hc
    · exact hc
    · exfalso
      have hz : φ zR ∈ centerOf (G₂ ⊓ G₁) := by
        rw [inf_comm, ← hrange]
        refine ⟨⟨zR, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
        obtain ⟨w, rfl⟩ := ht
        rw [← map_mul, ← map_mul, zR_central]
      have hx : x ∈ G₁ := by
        rw [← hG₁]; exact Subgroup.subset_closure (by simp)
      have h1 : x * φ zR = φ zR * x := Subgroup.mem_centralizer_iff.mp (hc hz) x hx
      have h2 : x⁻¹ * φ zR * x = φ zR := by
        calc x⁻¹ * φ zR * x = x⁻¹ * (φ zR * x) := by group
          _ = x⁻¹ * (x * φ zR) := by rw [h1]
          _ = φ zR := by group
      have h3 := aRho_conj_embR hA hAρ zR zR_mem_Q1
      rw [h2] at h3
      exact actA_zR (hinj h3.symm)
  · rw [hQ₁card]
    norm_num

end CFSG.Quasithin.F6.GoldAmL5
