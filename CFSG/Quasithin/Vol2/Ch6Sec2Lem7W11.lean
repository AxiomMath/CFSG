module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W10
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11B
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem three_dvd_card_of_nat627 {Q : Type} [CommGroup Q] [Finite Q] {L : Subgroup (MulAut Q)}
    {U Z : Subgroup Q}
    (h : (∃ n, BinaryNaturalSL L U Z 2 n) ∨ (∃ n, BinaryNaturalSL L U Z 3 n) ∨
      AlternatingNatural L U Z 5) : 3 ∣ Nat.card L := by
  have h4 : ∀ a : ℕ, 3 ∣ 4 ^ a - 1 := fun a => by
    have := Nat.sub_dvd_pow_sub_pow 4 1 a
    simpa using this
  rcases card_of_pair_types627 h with ⟨a, -, hc⟩ | ⟨a, -, hc⟩ | hc
  · rw [hc]
    exact Dvd.dvd.mul_left (h4 a) _
  · rw [hc]
    have e : ((2 : ℕ) ^ a) ^ 2 = 4 ^ a := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (h4 a) _) _
  · rw [hc]
    norm_num

section Claim

variable {G : Type} [Group G] [Finite G] {U UH H D K A : Subgroup G}
  [(U.subgroupOf UH).Normal] [CommModCh611 UH U]

omit [Finite G] in
theorem false_of_centralize627 (hHUH : H ≤ Subgroup.normalizer (UH : Set G))
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hHDUH : H ⊔ D ≤ Subgroup.normalizer (UH : Set G))
    (hHDU : H ⊔ D ≤ Subgroup.normalizer (U : Set G)) (hKH : K ≤ H) (hAK : A ≤ K)
    (a34 : ∀ K : Subgroup G, K ≤ H → A ≤ K →
      (∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈
        centralizerMod U (Subgroup.normalizer (U : Set G)) UH) →
      ¬ ⁅⁅UH, K⁆, D⁆ ≤ U)
    (hδ : ∀ (d : G) (hd : d ∈ D),
      (∀ q ∈ commV ((K.subgroupOf H).map (actQuot UH U H hHUH hHU)),
        actQuot UH U (H ⊔ D) hHDUH hHDU ⟨d, (le_sup_right : D ≤ H ⊔ D) hd⟩ q = q) ∧
      ∀ x ∈ (K.subgroupOf H).map (actQuot UH U H hHUH hHU),
        actQuot UH U (H ⊔ D) hHDUH hHDU ⟨d, (le_sup_right : D ≤ H ⊔ D) hd⟩ * x =
          x * actQuot UH U (H ⊔ D) hHDUH hHDU ⟨d, (le_sup_right : D ≤ H ⊔ D) hd⟩) :
    False := by
  classical
  set HD := H ⊔ D with hHDdef
  set ρ := actQuot UH U H hHUH hHU with hρ
  set ρ' := actQuot UH U HD hHDUH hHDU with hρ'
  set Ks := (K.subgroupOf H).map ρ with hKs
  have hρρ' : ∀ (x : G) (hx : x ∈ H), ρ ⟨x, hx⟩ = ρ' ⟨x, (le_sup_left : H ≤ HD) hx⟩ :=
    fun x hx => rfl
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈
      centralizerMod U (Subgroup.normalizer (U : Set G)) UH := by
    intro k hk d hd
    have hkH := hKH hk
    have hkHD : k ∈ HD := (le_sup_left : H ≤ HD) hkH
    have hdHD : d ∈ HD := (le_sup_right : D ≤ HD) hd
    have hcHD : k * d * k⁻¹ * d⁻¹ ∈ HD :=
      HD.mul_mem (HD.mul_mem (HD.mul_mem hkHD hdHD) (HD.inv_mem hkHD)) (HD.inv_mem hdHD)
    have hcN : k * d * k⁻¹ * d⁻¹ ∈ Subgroup.normalizer (U : Set G) := hHDU hcHD
    refine ⟨hcN, hcN, ?_⟩
    have hkKs : ρ ⟨k, hkH⟩ ∈ Ks := ⟨⟨k, hkH⟩, hk, rfl⟩
    have hρc : ρ' ⟨k * d * k⁻¹ * d⁻¹, hcHD⟩ = 1 := by
      have e : ρ' ⟨k * d * k⁻¹ * d⁻¹, hcHD⟩ =
          ρ ⟨k, hkH⟩ * ρ' ⟨d, hdHD⟩ * (ρ ⟨k, hkH⟩)⁻¹ * (ρ' ⟨d, hdHD⟩)⁻¹ := by
        rw [hρρ' k hkH, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [e, ← (hδ d hd).2 _ hkKs]
      group
    exact (actQuot_eq_one_iff (U := UH) (Z := U) _).mp hρc
  set W : Subgroup G :=
    ((commV Ks).comap (QuotientGroup.mk' (U.subgroupOf UH))).map UH.subtype with hWdef
  have hUHK : ⁅UH, K⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have hkH := hKH hk
    have hku : k * u⁻¹ * k⁻¹ ∈ UH :=
      (Subgroup.mem_normalizer_iff.mp (hHUH hkH) _).mp (UH.inv_mem hu)
    have hcUH : ⁅u, k⁆ ∈ UH := by
      rw [commutatorElement_def]
      have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
      rw [e]
      exact UH.mul_mem hu hku
    refine ⟨⟨_, hcUH⟩, ?_, rfl⟩
    show (QuotientGroup.mk' (U.subgroupOf UH)) ⟨⁅u, k⁆, hcUH⟩ ∈ commV Ks
    have hgen : ρ ⟨k, hkH⟩ ((⟨u, hu⟩ : ↥UH) : ↥UH ⧸ U.subgroupOf UH) *
        ((⟨u, hu⟩ : ↥UH) : ↥UH ⧸ U.subgroupOf UH)⁻¹ ∈ commV Ks :=
      Subgroup.subset_closure ⟨_, ⟨⟨k, hkH⟩, hk, rfl⟩, _, rfl⟩
    have e : (QuotientGroup.mk' (U.subgroupOf UH)) ⟨⁅u, k⁆, hcUH⟩ =
        (ρ ⟨k, hkH⟩ ((⟨u, hu⟩ : ↥UH) : ↥UH ⧸ U.subgroupOf UH) *
          ((⟨u, hu⟩ : ↥UH) : ↥UH ⧸ U.subgroupOf UH)⁻¹)⁻¹ := by
      rw [hρ, actQuot_mk, mul_inv_rev, inv_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.mk'_apply]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact (commV Ks).inv_mem hgen
  have hWD : ⁅W, D⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨⟨w, hwUH⟩, hwV, rfl⟩ d hd
    have hwV' : ((⟨w, hwUH⟩ : ↥UH) : ↥UH ⧸ U.subgroupOf UH) ∈ commV Ks := hwV
    have h1 := (hδ d hd).1 _ hwV'
    have h2 := (actQuot_mk_eq_iff (U := UH) (Z := U) (K := HD) (hKU := hHDUH) (hKZ := hHDU)
      ⟨d, (le_sup_right : D ≤ HD) hd⟩ ⟨w, hwUH⟩).mp h1
    have h3 := U.inv_mem h2
    rw [commutatorElement_def]
    simp only [Subgroup.coe_subtype]
    convert h3 using 1
    group
  exact a34 K hKH hAK hKD ((Subgroup.commutator_mono hUHK le_rfl).trans hWD)

end Claim

section SL34G

variable {G : Type} [Group G] [Finite G] {U UH H D : Subgroup G}
  [(U.subgroupOf UH).Normal] [CommModCh611 UH U]

theorem false_of_sl34G627 (hHUH : H ≤ Subgroup.normalizer (UH : Set G))
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hHDUH : H ⊔ D ≤ Subgroup.normalizer (UH : Set G))
    (hHDU : H ⊔ D ≤ Subgroup.normalizer (U : Set G))
    (hH : H = Subgroup.centralizer (U : Set G)) (hO : centralizerMod U H UH = pCoreOf 2 H)
    (hrank : ∀ E : Subgroup G, E ≤ H ⊔ D → CFSG.Open.IsElemAbelian 3 E → ∀ r,
      Nat.card E = 3 ^ r → r ≤ 2)
    {Ls : Subgroup (MulAut (↥UH ⧸ U.subgroupOf UH))}
    (hLsX : Ls ≤ (actQuot UH U H hHUH hHU).range)
    (hnat : BinaryNaturalSL Ls (commV Ls) (fixV Ls ⊓ commV Ls) 3 2) {d : G} (hdD : d ∈ D)
    (hdH : d ∉ H) (hd3 : d ^ 3 = 1)
    (hδL : actQuot UH U (H ⊔ D) hHDUH hHDU ⟨d, (le_sup_right : D ≤ H ⊔ D) hdD⟩ ∈
      Subgroup.normalizer (Ls : Set (MulAut (↥UH ⧸ U.subgroupOf UH)))) : False := by
  classical
  set HD := H ⊔ D with hHDdef
  set ρ := actQuot UH U H hHUH hHU with hρ
  set ρ' := actQuot UH U HD hHDUH hHDU with hρ'
  set dd : ↥HD := ⟨d, (le_sup_right : D ≤ HD) hdD⟩ with hdd
  have hdd3 : dd ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hδ3 : ρ' dd ^ 3 = 1 := by rw [← map_pow, hdd3, map_one]
  obtain ⟨t₁, ht₁, t₂, ht₂, ℓ, hℓ, ho₁, ho₂, hc₁₂, hc₁, hc₂, hP3, hind⟩ :=
    exists_E9_sl34_627 hnat hδL hδ3
  obtain ⟨e₁, he₁⟩ := hLsX ht₁
  obtain ⟨e₂, he₂⟩ := hLsX ht₂
  obtain ⟨k₃, hk₃⟩ := hLsX hℓ
  have : ((⊥ : Subgroup G).subgroupOf U).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hHDbot : HD ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun x _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  set σ := actQuot U ⊥ HD hHDU hHDbot with hσ
  have hσ1 : ∀ y : ↥HD, σ y = 1 ↔ (y : G) ∈ H := by
    intro y
    rw [actQuot_eq_one_iff, hH]
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h3 : (y : G) * u * (y : G)⁻¹ = u := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (h1 u hu))
      calc u * (y : G) = (y : G) * u * (y : G)⁻¹ * (y : G) := by rw [h3]
        _ = (y : G) * u := by group
    · intro h1 u hu
      rw [Subgroup.mem_bot]
      have h2 := Subgroup.mem_centralizer_iff.mp h1 u hu
      rw [← h2]
      group
  have hker : ∀ y : ↥HD, ρ' y = 1 → σ y = 1 → ∃ i : ℕ, y ^ 2 ^ i = 1 := by
    intro y h1 h2
    have hyH := (hσ1 y).mp h2
    have h3 : ρ ⟨y, hyH⟩ = 1 := h1
    have h4 : (y : G) ∈ pCoreOf 2 H := by
      rw [← hO]
      exact (mem_centralizerMod_iff_actQuot (hKU := hHUH) (hKZ := hHU) hyH).mpr h3
    obtain ⟨i, hi⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨y, h4⟩
    exact ⟨i, Subtype.ext (by simpa using congrArg Subtype.val hi)⟩
  set x₁ : ↥HD := ⟨e₁, (le_sup_left : H ≤ HD) e₁.2⟩ with hx₁
  set x₂ : ↥HD := ⟨e₂, (le_sup_left : H ≤ HD) e₂.2⟩ with hx₂
  set y₃ : ↥HD := ⟨k₃, (le_sup_left : H ≤ HD) k₃.2⟩ with hy₃
  have hθ₁ : ρ' x₁ = t₁ := he₁
  have hθ₂ : ρ' x₂ = t₂ := he₂
  have hθ₃ : ρ' (dd * y₃) = ρ' dd * ℓ := by
    rw [map_mul]
    congr 1
  have hσ₃ : σ y₃ = 1 := (hσ1 y₃).mpr k₃.2
  have hσd : orderOf (σ (dd * y₃)) = 3 := by
    rw [map_mul, hσ₃, mul_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hdd3, map_one]
    · exact fun h1 => hdH ((hσ1 dd).mp h1)
  refine false_of_E27_627 hrank ρ' σ hker ((hσ1 x₁).mpr e₁.2) ((hσ1 x₂).mpr e₂.2) hσd
    (by rw [hθ₁]; exact ho₁) (by rw [hθ₂]; exact ho₂) (by rw [hθ₁, hθ₂]; exact hc₁₂)
    (by rw [hθ₁, hθ₃]; exact hc₁) (by rw [hθ₂, hθ₃]; exact hc₂) (by rw [hθ₃]; exact hP3)
    (by rw [hθ₁, hθ₂]; exact hind)

end SL34G

end CFSG.Quasithin.H13
