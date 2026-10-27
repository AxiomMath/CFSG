module

public import CFSG.RankThree.PartOne.S12.Sec1511Y2

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

variable {G : Type} [Group G]

theorem exists_invariant_sylow [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {O B : Subgroup G}
    (hBp : IsPGroup p ↥B) (hBO : B ≤ Subgroup.normalizer (O : Set G)) (hOp : ¬ p ∣ Nat.card ↥O) :
    ∃ T : Subgroup G, IsSylowOf q T O ∧ B ≤ Subgroup.normalizer (T : Set G) := by
  classical
  let φ : ↥B →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hBO)
  let _ : MulDistribMulAction ↥B ↥O := MulDistribMulAction.compHom ↥O φ
  let _ : MulAction ↥B (Sylow q ↥O) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow q ↥O) := by
    intro h
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q ↥O))
    exact hOp (h.trans (Q.card_dvd_index.trans (Subgroup.index_dvd_card _)))
  obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q ↥O) hcard
  refine ⟨(Q₀ : Subgroup ↥O).map O.subtype, ⟨Subgroup.map_subtype_le _, Q₀.isPGroup'.map _, ?_⟩, ?_⟩
  · have hsub : ((Q₀ : Subgroup ↥O).map O.subtype).subgroupOf O = (Q₀ : Subgroup ↥O) :=
      Subgroup.comap_map_eq_self_of_injective O.subtype_injective _
    have : ((Q₀ : Subgroup ↥O).map O.subtype).relIndex O = (Q₀ : Subgroup ↥O).index := by
      rw [Subgroup.relIndex, hsub]
    rw [this]
    exact Q₀.not_dvd_index
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : ↥B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : ↥B) • y ∈ (Q₀ : Subgroup ↥O) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : ↥B) (Q₀ : Subgroup ↥O) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((O.normalizerMonoidHom) (Subgroup.inclusion hBO ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

theorem mem_normalizer_inf_normalizer {R R₁ : Subgroup G} {b : G}
    (hbR : b ∈ Subgroup.normalizer (R : Set G)) (hbR₁ : b ∈ Subgroup.normalizer (R₁ : Set G)) :
    b ∈ Subgroup.normalizer ((R₁ ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (R : Set G) ↔
      b * x * b⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
    intro x
    constructor
    · intro hx
      exact (Subgroup.normalizer (R : Set G)).mul_mem
        ((Subgroup.normalizer (R : Set G)).mul_mem hbR hx)
        ((Subgroup.normalizer (R : Set G)).inv_mem hbR)
    · intro hx
      have := (Subgroup.normalizer (R : Set G)).mul_mem
        ((Subgroup.normalizer (R : Set G)).mul_mem ((Subgroup.normalizer (R : Set G)).inv_mem hbR) hx)
        hbR
      simpa [mul_assoc] using this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 hbR₁ x, key x]

structure Y3Out (N R B O : Subgroup G) : Prop where
  sylow : IsSylowOf 2 R O
  maximal : ∀ R₁ : Subgroup G, IsPGroup 2 ↥R₁ → R ≤ R₁ → B ≤ Subgroup.normalizer (R₁ : Set G) →
    R₁ = R
  RN : R ≤ N

theorem lemmaY3 [Finite G] {p : ℕ} {E N Y' P R O : Subgroup G} (hp : p.Prime)
    (hY1 : Y1Out p E N Y' P) (hYN : ¬ Y' ≤ N) (hY2 : Y2Out p N Y' P (P ⊓ E) O)
    (hR2 : IsPGroup 2 ↥R) (hRY : R ≤ Y') (hRn : ∀ y ∈ Y', ∀ r ∈ R, y * r * y⁻¹ ∈ R)
    (hNR : Subgroup.normalizer (R : Set G) ≤ Y')
    (hmax : ∀ T : Subgroup G, IsPGroup 2 ↥T → Nat.card ↥R < Nat.card ↥T →
      P ⊓ E ≤ Subgroup.normalizer (T : Set G) → Subgroup.normalizer (T : Set G) ≤ N) :
    Y3Out N R (P ⊓ E) O := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBP : P ⊓ E ≤ P := inf_le_left
  have hPY : P ≤ Y' := hY1.syl.1
  have hBY : P ⊓ E ≤ Y' := hBP.trans hPY
  have hBp : IsPGroup p ↥(P ⊓ E) := hY1.syl.2.1.to_le hBP
  have hNormR : ∀ y ∈ Y', y ∈ Subgroup.normalizer (R : Set G) := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hRn y hy x hx, fun hx => by
      have := hRn y⁻¹ (Y'.inv_mem hy) _ hx
      simpa [mul_assoc] using this⟩
  have hNormO : ∀ y ∈ Y', y ∈ Subgroup.normalizer (O : Set G) := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hY2.O_norm y hy x hx, fun hx => by
      have := hY2.O_norm y⁻¹ (Y'.inv_mem hy) _ hx
      simpa [mul_assoc] using this⟩
  have hBR : P ⊓ E ≤ Subgroup.normalizer (R : Set G) := fun b hb => hNormR b (hBY hb)
  have hBO : P ⊓ E ≤ Subgroup.normalizer (O : Set G) := fun b hb => hNormO b (hBY hb)
  have hRO : R ≤ O := hY2.two R hRY hR2 hBR
  have hsylow : IsSylowOf 2 R O := by
    obtain ⟨T, hT, hBT⟩ := exists_invariant_sylow (p := p) (q := 2) hBp hBO hY2.O_cop
    have hRT : R ≤ T := by
      obtain ⟨T', hT', hRT'⟩ := Sec12Fus.exists_isSylowOf_ge (p := 2) hRO hR2
      obtain ⟨g, hgO, hg⟩ := Sec15FA.exists_conj_of_isSylowOf Nat.prime_two hT' hT
      intro r hr
      refine (hg r).2 (hRT' ?_)
      have hgY : g ∈ Y' := hY2.O_le hgO
      have := hRn g⁻¹ (Y'.inv_mem hgY) r hr
      simpa using this
    have hT2 : IsPGroup 2 ↥T := hT.2.1
    by_cases hTR : T = R
    · exact hTR ▸ hT
    · exfalso
      have hlt : Nat.card ↥R < Nat.card ↥T :=
        Subgroup.card_lt_of_lt (lt_of_le_of_ne hRT (Ne.symm hTR))
      have hNT : Subgroup.normalizer (T : Set G) ≤ N := hmax T hT2 hlt hBT
      apply hYN
      intro y hy
      have hcO : conjSub y O = O := by
        apply le_antisymm
        · intro x hx
          have h1 := (mem_conjSub_iff).1 hx
          have := hY2.O_norm y hy _ h1
          simpa [mul_assoc] using this
        · intro x hx
          rw [mem_conjSub_iff]
          have := hY2.O_norm y⁻¹ (Y'.inv_mem hy) x hx
          simpa [mul_assoc] using this
      have hTy : IsSylowOf 2 (conjSub y T) O := hcO ▸ isSylowOf_conjSub hT y
      obtain ⟨g, hgO, hg⟩ := Sec15FA.exists_conj_of_isSylowOf Nat.prime_two hT hTy
      have hm : g⁻¹ * y ∈ Subgroup.normalizer (T : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro t
        have h1 := hg (y * t * y⁻¹)
        rw [mem_conjSub_iff] at h1
        have e1 : y⁻¹ * (y * t * y⁻¹) * y = t := by group
        have e2 : g⁻¹ * y * t * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * t * y⁻¹) * g := by group
        rw [e1] at h1
        rw [e2]
        exact h1
      have hy' : y = g * (g⁻¹ * y) := by group
      rw [hy']
      exact N.mul_mem (hY2.O_N hgO) (hNT hm)
  have hmaximal : ∀ R₁ : Subgroup G, IsPGroup 2 ↥R₁ → R ≤ R₁ →
      P ⊓ E ≤ Subgroup.normalizer (R₁ : Set G) → R₁ = R := by
    intro R₁ hR₁ hRR₁ hBR₁
    by_contra hne
    obtain ⟨y, hyR₁, hyR, hyN⟩ := Sec12Fus.exists_mem_normalizer_sdiff (p := 2) hRR₁ hR₁
      (Ne.symm hne)
    set V : Subgroup G := R₁ ⊓ Subgroup.normalizer (R : Set G) with hV
    have hVY : V ≤ Y' := inf_le_right.trans hNR
    have hV2 : IsPGroup 2 ↥V := hR₁.to_le inf_le_left
    have hBV : P ⊓ E ≤ Subgroup.normalizer (V : Set G) := fun b hb =>
      mem_normalizer_inf_normalizer (hBR hb) (hBR₁ hb)
    have hVO : V ≤ O := hY2.two V hVY hV2 hBV
    have hRV : R ≤ V := le_inf hRR₁ Subgroup.le_normalizer
    have hVR : V ≤ R := Sec15FA.le_of_isSylowOf_of_isPGroup hsylow hV2 hRV hVO
    exact hyR (hVR ⟨hyR₁, hyN⟩)
  have hpR : ¬ p ∣ Nat.card ↥R := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    intro hdvd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    have := hY2.p5
    omega
  exact ⟨hsylow, hmaximal, hY1.coprime R hRY hRn hpR⟩

end Sec1511

end CFSG.RankThree.PartOne
