module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313Pre
public import CFSG.Quasithin.Vol2.Ch10SecB4

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13

theorem yo2_cover {G : Type} [Group G] [Finite G] {Y R P : Subgroup G} (hPY : P ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (R : Set G)) (hPR : P ⊓ R = ⊥)
    (hcard : R.relIndex Y = Nat.card P) {y : G} (hy : y ∈ Y) :
    ∃ r ∈ R, ∃ p ∈ P, y = r * p := by
  let f : ↥P → ↥Y ⧸ R.subgroupOf Y := fun p => QuotientGroup.mk (⟨(p : G), hPY p.2⟩ : ↥Y)
  have hf : Function.Injective f := by
    intro p₁ p₂ h
    have h' : (QuotientGroup.mk (⟨(p₁ : G), hPY p₁.2⟩ : ↥Y) : ↥Y ⧸ R.subgroupOf Y) =
        QuotientGroup.mk (⟨(p₂ : G), hPY p₂.2⟩ : ↥Y) := h
    have h1 : (p₁ : G)⁻¹ * (p₂ : G) ∈ R := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h')
    have h2 : (p₁ : G)⁻¹ * (p₂ : G) ∈ P ⊓ R := ⟨P.mul_mem (P.inv_mem p₁.2) p₂.2, h1⟩
    rw [hPR, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2
  have hcard' : Nat.card ↥P = Nat.card (↥Y ⧸ R.subgroupOf Y) := hcard.symm
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard'⟩
  obtain ⟨p, hp⟩ := hbij.2 (QuotientGroup.mk (⟨y, hy⟩ : ↥Y))
  have hp' : (QuotientGroup.mk (⟨(p : G), hPY p.2⟩ : ↥Y) : ↥Y ⧸ R.subgroupOf Y) =
      QuotientGroup.mk (⟨y, hy⟩ : ↥Y) := hp
  have h3 : (p : G)⁻¹ * y ∈ R := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hp')
  refine ⟨(p : G) * ((p : G)⁻¹ * y) * (p : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hYN (hPY p.2)) ((p : G)⁻¹ * y)).mp h3, (p : G), p.2, ?_⟩
  group

theorem yo2_Y_split {G : Type} [Group G] [Finite G] {T H : Subgroup G}
    (hTsyl : IsSylowTwoOf T H) (hTop : pCoreOf 2 H ≠ ⊥)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) :
    ∃ P3 : Subgroup G, P3 ≤ oTwoUpper H ∧ Nat.card P3 = 9 ∧ (∀ y ∈ P3, y ^ 3 = 1) ∧
      (∀ y ∈ oTwoUpper H, ∃ r ∈ pCoreOf 2 (oTwoUpper H), ∃ p ∈ P3, y = r * p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hXi := CFSG.Quasithin.Der6D.xi_of_iso hTsyl hTop (oTwoQuotEquiv e)
  have hrel := CFSG.Quasithin.C1Pack12.relIndex_pCoreOf_oTwoUpper (oTwoQuotEquiv e)
  have hOHT : pCoreOf 2 H ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTsyl
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ T := fun x hx =>
    hOHT (CFSG.Quasithin.C1Pack12.pow_three_mem_pCoreOf (oTwoQuotEquiv e) hx)
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [CFSG.Quasithin.card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := CFSG.Quasithin.Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  have hP3card : Nat.card P3 = 9 := by
    rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  refine ⟨P3, hP3.1, hP3card, ?_, ?_⟩
  ·
    intro y hy
    have h1 : y ^ 3 ∈ P3 ⊓ T := ⟨P3.pow_mem hy 3, hpow3 y (hP3.1 hy)⟩
    rw [(IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 T hP3.2.1 hT2).eq_bot,
      Subgroup.mem_bot] at h1
    exact h1
  ·
    have hPR : P3 ⊓ pCoreOf 2 (oTwoUpper H) = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 (pCoreOf 2 (oTwoUpper H)) hP3.2.1
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oTwoUpper H))).eq_bot
    exact fun y hy => yo2_cover hP3.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (oTwoUpper H)) hPR
      (hrel.trans hP3card.symm) hy

theorem yo2_img_card {G : Type} [Group G] [Finite G] {H₀ X : Subgroup G} (hXH : X ≤ H₀)
    (hX : X ⊓ pCoreOf 2 H₀ = ⊥) : Nat.card (modO2Image H₀ X) = Nat.card X := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥H₀)).comp (X.subgroupOf H₀).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : x.1 ∈ CFSG.pCore 2 ↥H₀ := (QuotientGroup.eq_one_iff x.1).mp hx
    have h2 : ((x.1 : ↥H₀) : G) ∈ X ⊓ pCoreOf 2 H₀ := ⟨x.2, ⟨x.1, h1, rfl⟩⟩
    rw [hX, Subgroup.mem_bot] at h2
    exact Subtype.ext (Subtype.ext h2)
  have hrange : modO2Image H₀ X =
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥H₀)).comp (X.subgroupOf H₀).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    try rfl
  rw [hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv

end CFSG.Quasithin.H13.NF314pt
