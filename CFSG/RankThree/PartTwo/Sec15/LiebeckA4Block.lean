module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4
public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.Quasithin.Background.C1PackA4

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckA4

open CFSG.Quasithin.S14110 (A4Data)
open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_of_a4Data {X W : Subgroup G} {c : G} (h : A4Data X W c) :
    CFSG.Open.pCoreOf 2 X = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWQ : W ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.le h.le_normalizer
      (IsPGroup.of_card (n := 2) (by rw [h.card_W]; norm_num))
  refine le_antisymm (fun x hx => ?_) hWQ
  obtain ⟨w, hw, k, rfl⟩ := h.mem_decomp (CFSG.LieType.BorelTits.pCoreOf_le 2 X hx)
  have hck : c ^ k ∈ CFSG.Open.pCoreOf 2 X := by
    have := (CFSG.Open.pCoreOf 2 X).mul_mem ((CFSG.Open.pCoreOf 2 X).inv_mem (hWQ hw)) hx
    simpa using this
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨c ^ k, hck⟩
  have hn' : (c ^ k) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have h3 : (c ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast (c ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.c_pow_three,
      one_zpow]
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hord : orderOf (c ^ k) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3) hcop)
      (orderOf_dvd_of_pow_eq_one hn')
  rw [orderOf_eq_one_iff.1 hord, mul_one]
  exact hw

theorem card_quotient_pCore_of_a4Data {X W : Subgroup G} {c : G} (h : A4Data X W c) :
    Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 3 := by
  have h1 : Nat.card (CFSG.pCore 2 ↥X) = 4 := by
    rw [← Subgroup.card_map_of_injective (f := X.subtype) X.subtype_injective]
    change Nat.card (CFSG.Open.pCoreOf 2 X) = 4
    rw [pCoreOf_eq_of_a4Data h, h.card_W]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  rw [h.card_X, h1] at h2
  omega

private theorem blockU_eq {X W : Subgroup G} {c : G} (h : A4Data X W c) : blockU X = W := by
  have hQ : blockQ X = W := pCoreOf_eq_of_a4Data h
  rw [blockU, hQ]
  refine le_antisymm (Subgroup.commutator_le.2 fun w hw x hx => ?_) fun w₁ hw₁ => ?_
  · have hx' : x * w⁻¹ * x⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (h.le_normalizer hx) w⁻¹).1 (W.inv_mem hw)
    have : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact W.mul_mem hw hx'
  · obtain ⟨w₀, hw₀, hw₀c⟩ := h.exists_mul_conj_inv_eq hw₁
    have : ⁅w₀, c⁆ = w₁ := by rw [← hw₀c, commutatorElement_def]; group
    rw [← this]
    exact Subgroup.commutator_mem_commutator hw₀ h.mem_X

private theorem blockZ_eq_bot {X W : Subgroup G} {c : G} (h : A4Data X W c) :
    blockZ X = ⊥ := by
  rw [blockZ, blockU_eq h, eq_bot_iff]
  rintro w ⟨hwW, hwC⟩
  rw [Subgroup.mem_bot]
  exact h.center w (h.le hwW) fun l hl => (Subgroup.mem_centralizer_iff.1 hwC l hl).symm

private theorem eq_bot_or_eq_of_le {X W : Subgroup G} {c : G} (h : A4Data X W c) {V : Subgroup G}
    (hVW : V ≤ W) (hn : X ≤ Subgroup.normalizer (V : Set G)) : V = ⊥ ∨ V = W := by
  by_cases hbot : V = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
  have hw' : c * w * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hn h.mem_X) w).1 hw
  have h3 : 3 ≤ Nat.card V := by
    have hsub : ({1, w, c * w * c⁻¹} : Set G) ⊆ (V : Set G) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact V.one_mem
      · exact hw
      · exact hw'
    have hc3 : ({1, w, c * w * c⁻¹} : Set G).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨1, w, c * w * c⁻¹, fun e => hw1' e.symm,
        fun e => hw1' (conj_eq_one_iff.1 e.symm), fun e => h.fpf w (hVW hw) hw1' e.symm, rfl⟩
    calc 3 = ({1, w, c * w * c⁻¹} : Set G).ncard := hc3.symm
      _ ≤ (V : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card V := (Nat.card_coe_set_eq (V : Set G)).symm
  have hdvd : Nat.card V ∣ 4 := h.card_W ▸ Subgroup.card_dvd_of_le hVW
  have h4 : Nat.card W ≤ Nat.card V := by
    rw [h.card_W]
    have hle : Nat.card V ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases Nat.card V
    · omega
    · exact le_rfl
  haveI := h.finite_W
  exact Subgroup.eq_of_le_of_card_ge hVW h4

omit [Finite G] in
private theorem eq_top_of_isPGroup_quotient {X W : Subgroup G} {c : G} (h : A4Data X W c)
    (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 (X ⧸ N)) : N = ⊤ := by
  set c' : X := ⟨c, h.mem_X⟩ with hc'
  have hc3 : c' ^ 3 = 1 := Subtype.ext h.c_pow_three
  have hcN : c' ∈ N := by
    obtain ⟨n, hn⟩ := hN (QuotientGroup.mk c')
    have h3 : (QuotientGroup.mk c' : X ⧸ N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have hord : orderOf (QuotientGroup.mk c' : X ⧸ N) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3) hcop)
        (orderOf_dvd_of_pow_eq_one hn)
    exact (QuotientGroup.eq_one_iff c').1 (orderOf_eq_one_iff.1 hord)
  have hWN : ∀ (w : G) (hw : w ∈ W), (⟨w, h.le hw⟩ : X) ∈ N := by
    intro w hw
    obtain ⟨w₀, hw₀, hw₀c⟩ := h.exists_mul_conj_inv_eq hw
    have hmem : (⟨w₀, h.le hw₀⟩ : X) * c' * (⟨w₀, h.le hw₀⟩ : X)⁻¹ * c'⁻¹ ∈ N :=
      N.mul_mem ((inferInstance : N.Normal).conj_mem c' hcN _) (N.inv_mem hcN)
    have hG : w = w₀ * c * w₀⁻¹ * c⁻¹ := by rw [← hw₀c]; group
    have : (⟨w, h.le hw⟩ : X) = (⟨w₀, h.le hw₀⟩ : X) * c' * (⟨w₀, h.le hw₀⟩ : X)⁻¹ * c'⁻¹ :=
      Subtype.ext hG
    rw [this]
    exact hmem
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hw, k, hx⟩ := h.mem_decomp x.2
  have : x = ⟨w, h.le hw⟩ * c' ^ k := by
    apply Subtype.ext
    simp only [hc', Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hx
  rw [this]
  exact N.mul_mem (hWN w hw) (N.zpow_mem hcN k)

private theorem charTwo_of_a4Data {X W : Subgroup G} {c : G} (h : A4Data X W c) : CharTwo X := by
  rintro x ⟨hxX, hxC⟩
  rw [pCoreOf_eq_of_a4Data h] at hxC ⊢
  obtain ⟨w, hw, k, rfl⟩ := h.mem_decomp hxX
  have key : ∀ u ∈ W, c ^ k * u * (c ^ k)⁻¹ = u := by
    intro u hu
    have h1 := Subgroup.mem_centralizer_iff.1 hxC u hu
    have h2 := h.comm u hu w hw
    have h3 : w * (c ^ k * u * (c ^ k)⁻¹) * c ^ k = w * u * c ^ k := by
      calc w * (c ^ k * u * (c ^ k)⁻¹) * c ^ k = w * c ^ k * u := by group
        _ = u * (w * c ^ k) := h1.symm
        _ = u * w * c ^ k := by rw [mul_assoc]
        _ = w * u * c ^ k := by rw [h2]
    exact mul_left_cancel (mul_right_cancel h3)
  rw [h.zpow_c_eq_one_of_centralizes key, mul_one]
  exact hw

theorem isShort2_of_a4Data {X W : Subgroup G} {c : G} (h : A4Data X W c) :
    CFSG.QuasithinUnique.IsShort2 X := by
  have hQ : blockQ X = W := pCoreOf_eq_of_a4Data h
  have hU : blockU X = W := blockU_eq h
  have hZ : blockZ X = ⊥ := blockZ_eq_bot h
  have hWbot : W ≠ ⊥ := by
    obtain ⟨u, hu, hu1⟩ := h.exists_ne_one_mem_W
    exact fun hb => hu1 (by simpa [hb] using hu)
  refine ⟨fun N _ hN => eq_top_of_isPGroup_quotient h N hN, charTwo_of_a4Data h, ⟨?_, ?_⟩,
    Or.inr (card_quotient_pCore_of_a4Data h), ?_, ?_⟩
  · rw [hU, hQ]
    exact le_inf le_rfl fun u hu => Subgroup.mem_centralizer_iff.2 fun v hv => h.comm v hv u hu
  · intro x hx
    rw [hU] at hx
    exact h.sq_eq_one x hx
  · rw [hZ, hU]
    exact bot_lt_iff_ne_bot.2 hWbot
  · intro V _ hVU hXV
    rw [hU] at hVU
    rw [hZ, hU]
    exact eq_bot_or_eq_of_le h hVU hXV

private theorem evenWeightOnes_three : CFSG.RankThree.PartTwo.evenWeightOnes 3 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [CFSG.RankThree.PartTwo.evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_zmultiples_iff] at hx
  obtain ⟨k, hk⟩ := hx
  have hsum := x.2
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at hsum
  rw [← hk] at hsum
  simp only [CFSG.RankThree.PartTwo.allOnes, Pi.smul_apply, zsmul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h31 : ((3 : ℕ) : ZMod 2) = 1 := by decide
  rw [h31, one_mul] at hsum
  rw [AddSubgroup.mem_bot]
  apply Subtype.ext
  rw [← hk]
  funext i
  simp [CFSG.RankThree.PartTwo.allOnes, zsmul_eq_mul, hsum]

omit [Finite G] in
private theorem isAltNaturalType_three {L : Subgroup G} (h : IsAltType L 3) :
    CFSG.RankThree.PartTwo.IsAltNaturalType L 3 := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hR⟩ := h
  set q := QuotientAddGroup.mk' (CFSG.RankThree.PartTwo.evenWeightOnes 3)
  have hqinj : Function.Injective q := by
    rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_mk', evenWeightOnes_three]
  refine ⟨α, hαs, hαk, (AddMonoidHom.toMultiplicative q).comp β,
    (QuotientAddGroup.mk'_surjective _).comp hβs, ?_, fun ℓ u v huv x hx => ?_⟩
  · rw [← hβk]
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hu
      have h1 : q (Multiplicative.toAdd (β u)) = q 0 := by
        rw [map_zero]
        exact congrArg Multiplicative.toAdd hu
      exact congrArg Multiplicative.ofAdd (hqinj h1)
    · intro hu
      rw [hu]
      rfl
  · change q (Multiplicative.toAdd (β v)) =
      q (CFSG.RankThree.PartTwo.evenWeightPerm (α ℓ : Equiv.Perm (Fin 3)) x)
    have hux : Multiplicative.toAdd (β u) = x := hqinj hx
    congr 1
    apply Subtype.ext
    funext i
    rw [hR ℓ u v huv i, hux]
    rfl

theorem isScriptLBlock_of_a4Data {M X W : Subgroup G} {c : G} (h : A4Data X W c)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) :
    CFSG.RankThree.PartTwo.IsScriptLBlock M X :=
  ⟨⟨IsShort2.isShort (isShort2_of_a4Data h), hXM, hsub⟩,
    Or.inr (Or.inl ⟨3, isAltNaturalType_three
      (CFSG.Quasithin.C1Pack.isAltType_three_of_card_three (isShort2_of_a4Data h)
        (card_quotient_pCore_of_a4Data h))⟩)⟩

theorem isScriptLBlock_of_a4Data_of_le_normalizer {M X W : Subgroup G} {c : G}
    (h : A4Data X W c) (hXM : X ≤ M) (hMX : M ≤ Subgroup.normalizer (X : Set G)) :
    CFSG.RankThree.PartTwo.IsScriptLBlock M X :=
  isScriptLBlock_of_a4Data h hXM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX).isSubnormal

end CFSG.RankThree.PartTwo.Sec15.LiebeckA4
