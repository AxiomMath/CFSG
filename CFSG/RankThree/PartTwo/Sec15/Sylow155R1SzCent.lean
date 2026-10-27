module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1SzLayer
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree.S4Free CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

private theorem isPGroup_three_of_pow_three {A : Subgroup G} (hA3 : ∀ a ∈ A, a ^ 3 = 1) :
    IsPGroup 3 ↥A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsPGroup.iff_orderOf]
  intro a
  have h3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA3 a a.2)
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

private theorem isSylowOf_map_hom {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private def conjAut (H : Subgroup G) {a : G} (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    MulAut ↥H where
  toFun h := ⟨a * h * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha h).mp h.2⟩
  invFun h := ⟨a⁻¹ * h * a, (Subgroup.mem_normalizer_iff''.mp ha h).mp h.2⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private theorem conjAut_pow (H : Subgroup G) {a : G} (ha : a ∈ Subgroup.normalizer (H : Set G))
    (n : ℕ) (h : ↥H) : (((conjAut H ha) ^ n) h : G) = a ^ n * h * (a ^ n)⁻¹ := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    change a ^ n * (a * (h : G) * a⁻¹) * (a ^ n)⁻¹ = a ^ (n + 1) * h * (a ^ (n + 1))⁻¹
    rw [pow_succ]
    group

private noncomputable def pPrimeQuotAut (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ pPrimeCore 2 X) where
  toFun σ := QuotientGroup.congr _ _ σ (pPrimeCore_map_iso 2 σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

private theorem exists_quotAut {H : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (H : Set G)) (ha3 : a ^ 3 = 1) :
    ∃ σ : MulAut (↥H ⧸ pPrimeCore 2 ↥H), σ ^ 3 = 1 ∧
      ∀ h h' : ↥H, (h' : G) = a * h * a⁻¹ →
        σ (QuotientGroup.mk h) = QuotientGroup.mk h' := by
  refine ⟨pPrimeQuotAut ↥H (conjAut H ha), ?_, fun h h' hh' => ?_⟩
  · have hc : conjAut H ha ^ 3 = 1 := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [conjAut_pow, ha3]
      simp
    rw [← map_pow, hc, map_one]
  · have : conjAut H ha h = h' := Subtype.ext hh'.symm
    rw [← this]
    rfl

theorem layerOddPreimage_le_centralizer_of_szSections {H A : Subgroup G}
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAO : A ≤ Subgroup.normalizer (CFSG.GH74.GLS.pPrimeCoreOf 2 H : Set G))
    (hAE : A ≤ Subgroup.normalizer (layerOddPreimage H : Set G))
    (hH3 : ¬ 3 ∣ Nat.card H) (hSz : SzSections ↥H)
    (hSz3 : CFSG.LocalAnalysis.UniquenessCase.UCK.SzOrder3Aut)
    (hC0 : ∀ S : Subgroup G, S ≤ layerOddPreimage H → Odd (Nat.card S) →
      A ≤ Subgroup.normalizer (S : Set G) → S ≤ Subgroup.centralizer (A : Set G)) :
    layerOddPreimage H ≤ Subgroup.centralizer (A : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  let π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hE0H : layerOddPreimage H ≤ H := Subgroup.map_subtype_le _
  have hE0sub : (layerOddPreimage H).subgroupOf H = (layer (↥H ⧸ O)).comap π := by
    unfold layerOddPreimage Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hMem : ∀ e ∈ layerOddPreimage H, ∃ e' : ↥H, (e' : G) = e ∧ π e' ∈ layer (↥H ⧸ O) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
    exact ⟨e', rfl, he'⟩
  have hOH : CFSG.GH74.GLS.pPrimeCoreOf 2 H ≤ H := Subgroup.map_subtype_le _
  have hOle : CFSG.GH74.GLS.pPrimeCoreOf 2 H ≤ layerOddPreimage H := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    show π o ∈ layer (↥H ⧸ O)
    rw [show π o = 1 from (QuotientGroup.eq_one_iff o).mpr ho]
    exact one_mem _
  have hOodd : Odd (Nat.card (CFSG.GH74.GLS.pPrimeCoreOf 2 H)) := by
    change Odd (Nat.card ((pPrimeCore 2 ↥H).map H.subtype))
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOC : CFSG.GH74.GLS.pPrimeCoreOf 2 H ≤ Subgroup.centralizer (A : Set G) :=
    hC0 _ hOle hOodd hAO
  have hsyl : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∃ R : Subgroup G,
      IsSylowOf ℓ R (layerOddPreimage H) ∧ R ≤ Subgroup.centralizer (A : Set G) := by
    intro ℓ hℓ hℓ2
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hK3 : ¬ 3 ∣ Nat.card (layerOddPreimage H) :=
      fun h => hH3 (h.trans (Subgroup.card_dvd_of_le hE0H))
    obtain ⟨R, hR, -, hAR⟩ := exists_invariant_isSylowOf_ge_of_coprime Nat.prime_three hℓ
      (isPGroup_three_of_pow_three hA3) hAE hK3 (bot_le : (⊥ : Subgroup G) ≤ _)
      (IsPGroup.of_card (n := 0) (by simp)) Subgroup.le_normalizer_of_normal
    refine ⟨R, hR, hC0 R hR.le ?_ hAR⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hR.isPGroup)
    rw [hn]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have himg : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∃ R : Subgroup G,
      IsSylowOf ℓ ((R.subgroupOf H).map π) (layer (↥H ⧸ O)) ∧
        R ≤ Subgroup.centralizer (A : Set G) ∧ R ≤ H := by
    intro ℓ hℓ hℓ2
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨R, hR, hRC⟩ := hsyl ℓ hℓ hℓ2
    have h1 : IsSylowOf ℓ (R.subgroupOf H) ((layerOddPreimage H).subgroupOf H) := by
      rw [← isSylowOf_map_subtype_iff H, Subgroup.map_subgroupOf_eq_of_le (hR.le.trans hE0H),
        Subgroup.map_subgroupOf_eq_of_le hE0H]
      exact hR
    rw [hE0sub] at h1
    have h2 := isSylowOf_map_hom h1 π
    rw [Subgroup.map_comap_eq_self_of_surjective hπ] at h2
    exact ⟨R, h2, hRC, hR.le.trans hE0H⟩
  have hmodO : ∀ a ∈ A, ∀ e ∈ layerOddPreimage H,
      e⁻¹ * (a * e * a⁻¹) ∈ CFSG.GH74.GLS.pPrimeCoreOf 2 H := by
    intro a ha e he
    have haN : a ∈ Subgroup.normalizer (H : Set G) := hAH ha
    obtain ⟨σ, hσ3, hσ⟩ := exists_quotAut haN (hA3 a ha)
    have hfix : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
        ∃ P : Subgroup (↥H ⧸ O), IsSylowOf ℓ P (layer (↥H ⧸ O)) ∧ ∀ x ∈ P, σ x = x := by
      intro ℓ hℓ hℓ2
      obtain ⟨R, hR, hRC, hRH⟩ := himg ℓ hℓ hℓ2
      refine ⟨_, hR, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have hrR : (r : G) ∈ R := hr
      have hcomm : a * (r : G) = (r : G) * a := Subgroup.mem_centralizer_iff.mp (hRC hrR) a ha
      exact hσ r r (by rw [hcomm]; group)
    have hlayer := mulAut_fixes_layer_of_szSections (hSz.quotient O) hSz3 hσ3 hfix
    obtain ⟨e', rfl, he'⟩ := hMem e he
    have hmem : a * (e' : G) * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp haN e').mp e'.2
    have h1 := hσ e' ⟨a * (e' : G) * a⁻¹, hmem⟩ rfl
    have h3 : σ (QuotientGroup.mk e') = QuotientGroup.mk e' := hlayer _ he'
    rw [h3] at h1
    have h2 : (e'⁻¹ * ⟨a * (e' : G) * a⁻¹, hmem⟩ : ↥H) ∈ O :=
      QuotientGroup.eq.mp h1
    exact ⟨_, h2, rfl⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hn := hmodO a ha x hx
  have hnC : a * (x⁻¹ * (a * x * a⁻¹)) = (x⁻¹ * (a * x * a⁻¹)) * a :=
    Subgroup.mem_centralizer_iff.mp (hOC hn) a ha
  set n : G := x⁻¹ * (a * x * a⁻¹) with hn_def
  have hxn : a * x * a⁻¹ = x * n := by rw [hn_def]; group
  have hpow : ∀ k : ℕ, a ^ k * x * (a ^ k)⁻¹ = x * n ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : a * n ^ k = n ^ k * a := (Commute.pow_right (show Commute a n from hnC) k).eq
      calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹
          = a * (a ^ k * x * (a ^ k)⁻¹) * a⁻¹ := by rw [pow_succ']; group
        _ = a * (x * n ^ k) * a⁻¹ := by rw [ih]
        _ = (a * x * a⁻¹) * (a * n ^ k * a⁻¹) := by group
        _ = (x * n) * n ^ k := by rw [hxn, hc]; group
        _ = x * n ^ (k + 1) := by rw [pow_succ']; group
  have hn3 : n ^ 3 = 1 := by
    have h := hpow 3
    rw [hA3 a ha] at h
    simpa using h.symm
  have hnH : n ∈ H := hOH hn
  have hord : orderOf n = 1 :=
    Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hH3)
      (orderOf_dvd_of_pow_eq_one hn3) (Subgroup.orderOf_dvd_natCard H hnH)
  have hn1 : n = 1 := orderOf_eq_one_iff.mp hord
  rw [hn1, mul_one] at hxn
  exact mul_inv_eq_iff_eq_mul.mp hxn

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
