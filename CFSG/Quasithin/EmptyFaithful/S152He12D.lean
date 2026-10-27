module

public import CFSG.Quasithin.EmptyFaithful.S152He12C
public import CFSG.Quasithin.EmptyFaithful.S152UTail

public section

namespace CFSG.Quasithin

namespace He12

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf (Mc : Subgroup G) (y : ↥Mc) :
    y ∈ CFSG.pCore 2 ↥Mc ↔ (y : G) ∈ CFSG.Open.pCoreOf 2 Mc := by
  unfold CFSG.Open.pCoreOf
  constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    exact this ▸ hz

theorem exists_threeComplement_caseI_amb {Mc K : Subgroup G} (hKMc : K ≤ Mc)
    (hKn : Mc ≤ Subgroup.normalizer (K : Set G)) (hFa : ∀ x ∈ Mc, orderOf x = 3 → x ∈ K) :
    ∃ (Ct W : Subgroup G) (k : ℕ), Ct ≤ Mc ∧ W ≤ Mc ∧ Mc ≤ Subgroup.normalizer (W : Set G) ∧
      ¬ 3 ∣ Nat.card W ∧
      (∀ y ∈ Mc, (∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 Mc) → y ∈ Ct) ∧
      ∀ y ∈ Ct, y ^ 3 ^ k ∈ W := by
  have hKn' : (K.subgroupOf Mc).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKMc).mpr hKn
  obtain ⟨Ct', W', k, hW'n, hW'3, hCt', hpow⟩ :=
    exists_threeComplement_caseI (Y := ↥Mc) (K := K.subgroupOf Mc) hKn'
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hFa x x.2 ((Subgroup.orderOf_coe x).trans hx)))
  refine ⟨Ct'.map Mc.subtype, W'.map Mc.subtype, k, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ Mc, ∀ w ∈ W'.map Mc.subtype, g * w * g⁻¹ ∈ W'.map Mc.subtype := by
      rintro g hg _ ⟨w, hw, rfl⟩
      exact ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, hW'n.conj_mem w hw ⟨g, hg⟩, by simp⟩
    intro w
    refine ⟨key g hg w, fun hw => ?_⟩
    have := key g⁻¹ (Mc.inv_mem hg) _ hw
    simpa [mul_assoc] using this
  · rw [Subgroup.card_map_of_injective Mc.subtype_injective]
    exact hW'3
  · intro y hy hcomm
    refine ⟨⟨y, hy⟩, (hCt' ⟨y, hy⟩).mpr fun z hz => ?_, rfl⟩
    exact (mem_pCore_iff_mem_pCoreOf Mc _).mpr
      (hcomm z (Subgroup.mem_subgroupOf.mp hz))
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y ^ 3 ^ k, hpow y hy, by simp⟩

theorem le_pCoreOf_of_commutes_caseI {Mc K N V : Subgroup G} (hKMc : K ≤ Mc)
    (hKn : Mc ≤ Subgroup.normalizer (K : Set G)) (hFa : ∀ x ∈ Mc, orderOf x = 3 → x ∈ K)
    (hO3 : ∀ W : Subgroup G, W ≤ Mc → Mc ≤ Subgroup.normalizer (W : Set G) → ¬ 3 ∣ Nat.card W →
      W ≤ N)
    (hVMc : V ≤ Mc) (hV2 : IsPGroup 2 V) (hVN : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V)
    (hcomm : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ CFSG.Open.pCoreOf 2 Mc) :
    V ≤ CFSG.Open.pCoreOf 2 Mc := by
  obtain ⟨Ct, W, k, hCtMc, hWMc, hWn, hW3, hCt, hpow⟩ :=
    exists_threeComplement_caseI_amb hKMc hKn hFa
  have hWN : W ≤ N := hO3 W hWMc hWn hW3
  have hVW : V ≤ W := by
    intro v hv
    have hvCt : v ∈ Ct := hCt v (hVMc hv) fun z hz => by
      have h := hcomm z hz v hv
      have e : v * z * v⁻¹ * z⁻¹ = (z * v * z⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact (CFSG.Open.pCoreOf 2 Mc).inv_mem h
    have hvk := hpow v hvCt
    obtain ⟨a, ha⟩ := hV2 ⟨v, hv⟩
    have hv2 : v ^ 2 ^ a = 1 := by
      have := congrArg (fun z : V => (z : G)) ha
      simpa using this
    have hcop : Nat.Coprime (3 ^ k) (orderOf v) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hv2)
        (Nat.Coprime.pow k a (by norm_num : Nat.Coprime 3 2))
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hj]
    exact W.pow_mem hvk j
  have hVn : W ≤ Subgroup.normalizer (V : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hVN w (hWN hw) v hv, fun hw' => ?_⟩
    have := hVN w⁻¹ (hWN (W.inv_mem hw)) _ hw'
    simpa [mul_assoc] using this
  have hVO : V ≤ CFSG.Open.pCoreOf 2 W :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVW hVn hV2
  have hOMc : CFSG.Open.pCoreOf 2 W ≤ CFSG.Open.pCoreOf 2 Mc :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 W).trans hWMc)
      (hWn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W)
  exact hVO.trans hOMc

@[expose] def ThreeComplement152 (Mc : Subgroup G) : Prop :=
  ∃ (Ct W : Subgroup G) (k : ℕ), Ct ≤ Mc ∧ W ≤ Mc ∧ Mc ≤ Subgroup.normalizer (W : Set G) ∧
    ¬ 3 ∣ Nat.card W ∧ (∀ x ∈ Mc, (∃ a : ℕ, orderOf x = 3 ^ a) → x ∈ Ct) ∧
    ∀ y ∈ Ct, y ^ 3 ^ k ∈ W

theorem threeComplement152_of_caseI {Mc K : Subgroup G} (hKMc : K ≤ Mc)
    (hKn : Mc ≤ Subgroup.normalizer (K : Set G)) (hFa : ∀ x ∈ Mc, orderOf x = 3 → x ∈ K)
    (h3c : ∀ x ∈ Mc, (∃ a : ℕ, orderOf x = 3 ^ a) → ∀ z ∈ K,
      x * z * x⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 Mc) : ThreeComplement152 Mc := by
  obtain ⟨Ct, W, k, hCtMc, hWMc, hWn, hW3, hCt, hpow⟩ :=
    exists_threeComplement_caseI_amb hKMc hKn hFa
  exact ⟨Ct, W, k, hCtMc, hWMc, hWn, hW3, fun x hx h3 => hCt x hx (h3c x hx h3), hpow⟩

omit [Finite G] in
theorem not_hasSectionIso_of_threeComplement {Mc Y₀ : Subgroup G} (h : ThreeComplement152 Mc)
    (hY₀ : Y₀ ≤ Mc) {S : Type} [Group S] [IsSimpleGroup S] (h3 : 3 ∣ Nat.card S)
    (hSn : ¬ IsPGroup 3 S) : ¬ S152U.HasSectionIso (oPrimeResidualOf 3 Y₀) S := by
  rintro ⟨A, N, hN, hAX, ⟨e⟩⟩
  obtain ⟨Ct, W, k, hCtMc, hWMc, hWn, hW3, hCt, hpow⟩ := h
  have hXCt : oPrimeResidualOf 3 Y₀ ≤ Ct := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact hCt x (hY₀ hx.1) hx.2
  have hACt : A ≤ Ct := hAX.trans hXCt
  let ρ : ↥A →* S := (e : (↥A ⧸ N) →* S).comp (QuotientGroup.mk' N)
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  set Aw : Subgroup ↥A := W.comap A.subtype with hAwdef
  have hAwn : Aw.Normal := by
    refine ⟨fun w hw a => ?_⟩
    show ((a * w * a⁻¹ : ↥A) : G) ∈ W
    have hw' : (w : G) ∈ W := hw
    have haMc : (a : G) ∈ Mc := hCtMc (hACt a.2)
    have := (Subgroup.mem_normalizer_iff.mp (hWn haMc) (w : G)).mp hw'
    simpa using this
  have hAwcard : Nat.card Aw ∣ Nat.card W := by
    have h1 : Aw.map A.subtype = A ⊓ W := by
      rw [hAwdef, Subgroup.map_comap_eq, Subgroup.range_subtype]
    have h2 : Nat.card Aw = Nat.card (A ⊓ W : Subgroup G) := by
      rw [← h1, Subgroup.card_map_of_injective A.subtype_injective]
    rw [h2]
    exact Subgroup.card_dvd_of_le inf_le_right
  have : (Aw.map ρ).Normal := hAwn.map ρ hρ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Aw.map ρ) with hbot | htop
  ·
    apply hSn
    intro s
    obtain ⟨a, rfl⟩ := hρ s
    refine ⟨k, ?_⟩
    have hmem : (a ^ 3 ^ k : ↥A) ∈ Aw := by
      show (((a ^ 3 ^ k : ↥A)) : G) ∈ W
      rw [Subgroup.coe_pow]
      exact hpow _ (hACt a.2)
    have : ρ (a ^ 3 ^ k) ∈ Aw.map ρ := ⟨_, hmem, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    rw [← map_pow]
    exact this
  ·
    have h1 : Nat.card S ∣ Nat.card Aw := by
      have := Subgroup.card_map_dvd Aw ρ
      rwa [htop, Subgroup.card_top] at this
    exact hW3 (h3.trans (h1.trans hAwcard))

end He12

end CFSG.Quasithin
