module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row6Alt7
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row6Hat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Transport
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AStep2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.BarSplit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem row6_orderOf_mk {H : Subgroup G} {g : G} (hg : g ∈ H) (h3 : orderOf g = 3) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hg⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : (⟨g, hg⟩ : ↥H) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one g
    rw [h3] at this
    simpa using this
  have hord : orderOf (⟨g, hg⟩ : ↥H) = 3 := by
    rw [Subgroup.orderOf_mk, h3]
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hg⟩ ≠ 1 := by
    intro h
    have hmem : (⟨g, hg⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h
    have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hp ⟨_, hmem⟩
    rw [Subgroup.orderOf_mk, hord] at hk
    rcases k with _ | k
    · simp at hk
    · rw [pow_succ] at hk
      omega
  refine orderOf_eq_prime ?_ h1
  rw [← map_pow, hpow, map_one]

theorem row6_false_gen {H S L L₁ : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L) (hLH : L ≤ H)
    (hLL₁ : L ≤ L₁) (hN : (L₁.subgroupOf H).Normal) (hrk : CFSG.Open.pRank 3 H ≤ 2)
    (hsplit : ∀ s ∈ S, ∃ p ∈ S ⊓ L, ∃ c ∈ S,
      (∀ x ∈ L, ∃ m ∈ pCoreOf 2 L, c * x * c⁻¹ = x * m) ∧ s = p * c)
    (hrow : IsPSL 3 2 1 ↥(modO2Image H L) ∧
      (IsAlt 7 ↥(modO2Image H L₁) ∨ IsHat ↥(modO2Image H L₁) (alternatingGroup (Fin 7))))
    (h6b : ∀ (X : Type) [Group X], IsAlt 7 X → ∀ E : Subgroup X, Nat.card E = 9 →
      ∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ∉ Subgroup.zpowers a →
        ∀ n : X, n * a * n⁻¹ = a⁻¹ → n * b * n⁻¹ = b → False)
    (h6c : ∀ (X : Type) [Group X] [Finite X], IsHat X (alternatingGroup (Fin 7)) →
      ∀ E : Subgroup X, Nat.card E = 9 → E ⊓ Subgroup.center X ≠ ⊥)
    {e x s : G} (he : e ∈ L) (he3 : orderOf e = 3) (hxH : x ∈ H) (hx3 : orderOf x = 3)
    (hex : e * x = x * e) (hxL : x ∉ Subgroup.normalizer (L : Set G)) (hsS : s ∈ S)
    (hse : s * e * s⁻¹ = e⁻¹) (hsx : s * x * s⁻¹ = x) : False := by
  classical
  obtain ⟨hpsl, hrow⟩ := hrow
  have hNn : (modO2Image H L₁).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLbN : modO2Image H L ≤ modO2Image H L₁ := Subgroup.map_mono fun _ hx => hLL₁ hx
  have hrank := le_nine_modO2_of_pRank_le H hrk
  have hsimple : IsSimpleGroup ↥(modO2Image H L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hpsl).2
  have hcard : Nat.card ↥(modO2Image H L) = 168 := by
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hpsl
    rw [Nat.card_congr φ.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
    decide
  have hn : ¬ IsPGroup 2 ↥(modO2Image H L) := by
    intro hp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hcard] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hLbZ : ∀ z ∈ modO2Image H L, (∀ a ∈ modO2Image H L, z * a = a * z) → z = 1 := by
    intro z hz hzc
    have := eq_one_of_central_isPSL hpsl (z := ⟨z, hz⟩) (fun a => Subtype.ext (hzc a a.2))
    exact congrArg Subtype.val this
  have hbe : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨e, hLH he⟩ ∈ modO2Image H L :=
    ⟨⟨e, hLH he⟩, he, rfl⟩
  have hbe3 := row6_orderOf_mk (hLH he) he3
  have hbx3 := row6_orderOf_mk hxH hx3
  have hbex : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨e, hLH he⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨e, hLH he⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hex
  have hbxL : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∉
      Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := fun hnn =>
    hxL (mem_normalizer_of_mk_mem hS hSL hperf hLH hxH hnn)
  obtain ⟨p, hp, c, -, hcent, hsp⟩ := Stellmacher.CD.L3YC.split_bar hS.1 hLH hsplit hsimple hn
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hS.1 hsS⟩) ⟨⟨s, hS.1 hsS⟩, hsS, rfl⟩
  have hbse : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hS.1 hsS⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨e, hLH he⟩ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hS.1 hsS⟩)⁻¹ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨e, hLH he⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hse
  have hbsx : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hS.1 hsS⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hS.1 hsS⟩)⁻¹ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hsx
  rw [hsp] at hbse hbsx
  rcases hrow with hA | hHat
  · exact row6_alt7_false hLbN hrank hA hcard h6b hbe hbe3 hbx3 hbex hbxL hp.2 hcent hbse hbsx
  · exact row6_hat_false hLbN hrank hHat hLbZ h6c hbe hbe3 hbx3 hbex hbxL

end Bar

section Main

variable {G : Type} [Group G] [Finite G]

theorem row6_false_of (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G}
    (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hc₀2 : c₀ * c₀ = 1) (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1)
    (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s) (hsw : t' * c₀ * t'⁻¹ = u₀)
    (hS : IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)))
    (hev : evenRank G ≤ 2) {L₁ : Subgroup G}
    (_hL₁ : L₁ ∈ cComp (Subgroup.centralizer ({c₀} : Set G))) (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal)
    (hrow : IsPSL 3 2 1 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L) ∧
      (IsAlt 7 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁) ∨
        IsHat ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)
          (alternatingGroup (Fin 7))))
    (h6b : ∀ (X : Type) [Group X], IsAlt 7 X → ∀ E : Subgroup X, Nat.card E = 9 →
      ∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ∉ Subgroup.zpowers a →
        ∀ n : X, n * a * n⁻¹ = a⁻¹ → n * b * n⁻¹ = b → False)
    (h6c : ∀ (X : Type) [Group X] [Finite X], IsHat X (alternatingGroup (Fin 7)) →
      ∀ E : Subgroup X, Nat.card E = 9 → E ⊓ Subgroup.center X ≠ ⊥) : False := by
  classical
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ Subgroup.centralizer ({c₀} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  have hloc : IsTwoLocal (Subgroup.centralizer ({c₀} : Set G)) :=
    CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one (by rw [pow_two]; exact hc₀2)
      hc₀1
  have hrk := (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc).trans hev
  obtain ⟨y, x, s₁, s₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hyL, hoe, hox, hcomm, hxc,
      hxN, hs1S, -, hs1e, hs1x, -, -⟩ :=
    exists_e_x2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc hc₀1 hu₀ hu₀1
      hu₀S hsw
  have hxH : t'⁻¹ * x * t' ∈ Subgroup.centralizer ({c₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hxc
  exact row6_false_gen hS hSL hperf hLH hLL₁ hN hrk (Stellmacher.PU.L3YC.pu_S_split c hq hSL h4)
    hrow h6b h6c hyL hoe hxH hox hcomm hxN hs1S hs1e hs1x

end Main

end Stellmacher.L3YC

end CFSG.Quasithin
