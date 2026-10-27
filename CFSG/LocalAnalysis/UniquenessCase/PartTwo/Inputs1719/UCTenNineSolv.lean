module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.LocalAnalysis.UniquenessCase.UCKUnfaithful
public import CFSG.GroupTheory.CommutatorLeSubgroupOf
public import TauCeti.RepresentationTheory.Unipotent.PowerOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_isChiefFactorUnder_of_minimal {H X Y : Subgroup G} (hYX : Y < X) (hXH : X ≤ H)
    (hYn : H ≤ normalizer (Y : Set G)) (hXn : H ≤ normalizer (X : Set G))
    (hmin : ∀ W : Subgroup G, Y ≤ W → W ≤ X → H ≤ normalizer (W : Set G) → W = Y ∨ W = X)
    (hab : ⁅X, X⁆ ≤ Y) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ CFSG.ABGLocalTools.IsChiefFactorUnder ℓ H X Y := by
  classical
  have hN : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX.le).2 (hXH.trans hYn)
  let Q := X ⧸ Y.subgroupOf X
  have hQcomm : IsMulCommutative Q :=
    CFSG.GroupTheory.isMulCommutative_quotient_subgroupOf_of_commutator_le hab
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  have hQnontriv : Nontrivial Q := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hYX.ne (le_antisymm hYX.le (Subgroup.subgroupOf_eq_top.mp htop))
  have hQcard : Nat.card Q ≠ 1 := by
    intro h1
    have hsub : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp h1).1
    exact not_subsingleton_iff_nontrivial.mpr hQnontriv hsub
  obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd hQcard
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let π : X →* Q := QuotientGroup.mk' (Y.subgroupOf X)
  let K : Subgroup Q := (powMonoidHom ℓ : Q →* Q).ker
  let W : Subgroup G := (K.comap π).map X.subtype
  have hmemW : ∀ g : G, g ∈ W ↔ g ∈ X ∧ g ^ ℓ ∈ Y := by
    intro g
    constructor
    · rintro ⟨x, hxK, rfl⟩
      refine ⟨x.2, ?_⟩
      have h2 : QuotientGroup.mk (x ^ ℓ) = (1 : Q) := by
        have h2' : (QuotientGroup.mk' (Y.subgroupOf X)) (x ^ ℓ) = 1 := by
          have h := MonoidHom.mem_ker.1 hxK
          rw [powMonoidHom_apply, ← map_pow] at h
          exact h
        rw [QuotientGroup.mk'_apply] at h2'
        exact h2'
      rw [QuotientGroup.eq_one_iff] at h2
      simpa using Subgroup.mem_subgroupOf.1 h2
    · rintro ⟨hxX, hxY⟩
      refine ⟨⟨g, hxX⟩, ?_, rfl⟩
      change (powMonoidHom ℓ) (π ⟨g, hxX⟩) = 1
      rw [powMonoidHom_apply]
      have h2 : (QuotientGroup.mk' (Y.subgroupOf X)) (⟨g, hxX⟩ ^ ℓ) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        simpa using Subgroup.mem_subgroupOf.2 hxY
      change ((QuotientGroup.mk' (Y.subgroupOf X)) ⟨g, hxX⟩) ^ ℓ = 1
      simpa only [map_pow] using h2
  have hHnW : H ≤ normalizer (W : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [hmemW g, hmemW (h * g * h⁻¹)]
    constructor
    · rintro ⟨hgX, hgY⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hXn hh) g).1 hgX, ?_⟩
      rw [conj_pow]
      exact (Subgroup.mem_normalizer_iff.1 (hYn hh) (g ^ ℓ)).1 hgY
    · rintro ⟨hgX, hgY⟩
      have hgX' : g ∈ X := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (hXn (H.inv_mem hh)) (h * g * h⁻¹)).1 hgX
        simpa [mul_assoc] using h1
      have h2 : h * g ^ ℓ * h⁻¹ ∈ Y := by
        simpa only [conj_pow] using hgY
      refine ⟨hgX', ?_⟩
      have h3 := (Subgroup.mem_normalizer_iff.1 (hYn (H.inv_mem hh)) (h * g ^ ℓ * h⁻¹)).1 h2
      simpa [mul_assoc] using h3
  have hWne : W ≠ Y := by
    intro hWY
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) ℓ hℓdvd
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf X) q
    have hq1 : q ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hq
      exact hℓ.ne_one hq.symm
    have hxY : (x : G) ∉ Y := by
      intro hxY
      apply hq1
      rw [← hx, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      simpa using Subgroup.mem_subgroupOf.2 hxY
    have hxpow : (x : G) ^ ℓ ∈ Y := by
      have hqpow : q ^ ℓ = 1 := by
        rw [← hq]
        exact pow_orderOf_eq_one q
      have h1 : QuotientGroup.mk (x ^ ℓ) = (1 : Q) := by
        have h1' : (QuotientGroup.mk' (Y.subgroupOf X)) (x ^ ℓ) = 1 := by
          rw [map_pow, hx, hqpow]
        rw [QuotientGroup.mk'_apply] at h1'
        exact h1'
      rw [QuotientGroup.eq_one_iff] at h1
      simpa using Subgroup.mem_subgroupOf.1 h1
    have hxW : (x : G) ∈ W := (hmemW x).2 ⟨x.2, hxpow⟩
    exact hxY (hWY ▸ hxW)
  have hYW : Y ≤ W := by
    intro y hy
    rw [hmemW]
    exact ⟨hYX.le hy, Y.pow_mem hy ℓ⟩
  have hWX : W ≤ X := Subgroup.map_subtype_le _
  have hWXeq : W = X := by
    rcases hmin W hYW hWX hHnW with h | h
    · exact absurd h hWne
    · exact h
  have hpowX : ∀ x ∈ X, x ^ ℓ ∈ Y := by
    intro x hx
    exact ((hmemW x).1 (hWXeq ▸ hx)).2
  refine ⟨ℓ, hℓ, hYX, hXn, hYn, ?_, ?_, hpowX, hmin⟩
  · intro x hx y hy
    exact (Subgroup.mem_normalizer_iff.1 (hYn (hXH hx)) y).1 hy
  · intro x hx y hy
    exact hab (Subgroup.commutator_mem_commutator hx hy)

theorem le_sup_of_isSylowOf_of_pow_mem {ℓ : ℕ} [Fact ℓ.Prime] {X Y S : Subgroup G}
    (hYX : Y ≤ X) (hXY : X ≤ normalizer (Y : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf ℓ S X) (hpow : ∀ x ∈ X, x ^ ℓ ∈ Y) : X ≤ S ⊔ Y := by
  classical
  have hN : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY
  let Q := X ⧸ Y.subgroupOf X
  let π : X →* Q := QuotientGroup.mk' (Y.subgroupOf X)
  let Sbar : Subgroup Q := (S.subgroupOf X).map π
  have hQp : IsPGroup ℓ Q := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf X) q
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hqpow : q ^ ℓ = 1 := by
      rw [← hx, ← map_pow]
      change QuotientGroup.mk (x ^ ℓ) = (1 : Q)
      rw [QuotientGroup.eq_one_iff]
      simpa using Subgroup.mem_subgroupOf.2 (hpow x x.2)
    exact orderOf_dvd_of_pow_eq_one hqpow
  have hSbarTop : Sbar = ⊤ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQp
    have hdvdpow : Sbar.index ∣ ℓ ^ n := by
      rw [← hn]
      exact Subgroup.index_dvd_card Sbar
    have hdvd : Sbar.index ∣ (S.subgroupOf X).index := by
      exact Subgroup.index_map_dvd (S.subgroupOf X)
        (QuotientGroup.mk'_surjective (Y.subgroupOf X))
    have hnot : ¬ ℓ ∣ (S.subgroupOf X).index := by
      obtain ⟨Q₀, hQ₀⟩ := hS.exists_sylow_eq_subgroupOf
      rw [← hQ₀]
      exact Q₀.not_dvd_index
    have hind : Sbar.index = 1 := by
      by_contra hne
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).1 hdvdpow
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hne (by rw [hk, pow_zero])
      refine hnot (dvd_trans ?_ hdvd)
      rw [hk]
      exact dvd_pow_self ℓ hk0
    exact Subgroup.index_eq_one.1 hind
  intro x hx
  have hxbar : π ⟨x, hx⟩ ∈ Sbar := by
    rw [hSbarTop]
    exact Subgroup.mem_top _
  change π ⟨x, hx⟩ ∈ (S.subgroupOf X).map π at hxbar
  rw [Subgroup.mem_map] at hxbar
  obtain ⟨s, hs, hsp⟩ := hxbar
  have hys : ((s : G)⁻¹ * x) ∈ Y := by
    have h1 : QuotientGroup.mk (s⁻¹ * ⟨x, hx⟩) = (1 : Q) := by
      have h1' : π (s⁻¹ * ⟨x, hx⟩) = 1 := by
        rw [map_mul, map_inv, hsp, inv_mul_cancel]
      change (QuotientGroup.mk' (Y.subgroupOf X)) (s⁻¹ * ⟨x, hx⟩) = 1 at h1'
      rw [QuotientGroup.mk'_apply] at h1'
      exact h1'
    rw [QuotientGroup.eq_one_iff] at h1
    simpa using Subgroup.mem_subgroupOf.1 h1
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
  rw [show x = (s : G) * ((s : G)⁻¹ * x) by group]
  exact (S ⊔ Y).mul_mem (Subgroup.mem_sup_left hsS) (Subgroup.mem_sup_right hys)

theorem commutator_mem_of_isChiefFactorUnder {ℓ p : ℕ} [Fact ℓ.Prime] (hp : p.Prime)
    (hp2 : p ≠ 2) (hℓ2 : ℓ ≠ 2) (hd : ¬ ∃ k : ℕ, orderOf (2 : ZMod p) = 2 ^ k)
    {H T B X Y : Subgroup G} (hchief : CFSG.ABGLocalTools.IsChiefFactorUnder ℓ H X Y)
    (hT : IsPGroup 2 T) (hTH : T ≤ H) (hBH : B ≤ H) (hBT : B ≤ normalizer (T : Set G))
    (hBp : Nat.card B = p) (hfix : ∀ x ∈ X, (∀ b ∈ B, ⁅x, b⁆ ∈ Y) → x ∈ Y) :
    ∀ c ∈ ⁅T, B⁆, ∀ x ∈ X, ⁅x, c⁆ ∈ Y := by
  classical
  have := hchief.normal
  have := hchief.isElementaryAbelian
  let V := Additive (X ⧸ Y.subgroupOf X)
  let ρ : Representation (ZMod ℓ) H V :=
    (Units.coeHom _).comp (CFSG.ABGLocalTools.chiefRep (p := ℓ) hchief.2.1 hchief.2.2.1)
  have hTBH : ⁅T, B⁆ ≤ H := (Subgroup.le_normalizer_iff_commutator_le_left.1 hBT).trans hTH
  have hDcard : Nat.card (B.subgroupOf H) = p := by
    rw [← hBp]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hVnt : Nontrivial V := by
    have htop : Y.subgroupOf X ≠ ⊤ := by
      intro htop
      exact hchief.1.ne (le_antisymm hchief.1.le (Subgroup.subgroupOf_eq_top.mp htop))
    have hnt : Nontrivial (X ⧸ Y.subgroupOf X) := QuotientGroup.nontrivial_iff.mpr htop
    exact hnt
  have hρeval : ∀ (n : H) (w : X), ρ n (Additive.ofMul (w : X ⧸ Y.subgroupOf X)) =
      Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hchief.2.1 n w : X) :
        X ⧸ Y.subgroupOf X) := by
    intro n w
    exact CFSG.ABGLocalTools.chiefRep_apply_mk hchief.2.1 hchief.2.2.1 n w
  have hfixV : CFSG.LocalAnalysis.UniquenessCase.UCK.fixV ρ (B.subgroupOf H) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨w, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk (W₁ := X) (W₂ := Y) v
    have hwY : (w : G) ∈ Y := by
      apply hfix (w : G) w.2
      intro b hb
      let n : B.subgroupOf H := ⟨⟨b, hBH hb⟩, hb⟩
      have hfixn := hv n n.2
      rw [hρeval (n : H) w] at hfixn
      have heq : ((CFSG.ABGLocalTools.chiefConj hchief.2.1 (n : H) w : X) :
          X ⧸ Y.subgroupOf X) = (w : X ⧸ Y.subgroupOf X) := by
        simpa using hfixn
      have hmem : ((CFSG.ABGLocalTools.chiefConj hchief.2.1 (n : H) w)⁻¹ * w :
          X) ∈ Y.subgroupOf X := QuotientGroup.eq.1 heq
      have hmemY : (((CFSG.ABGLocalTools.chiefConj hchief.2.1 (n : H) w)⁻¹ * w :
          X) : G) ∈ Y := Subgroup.mem_subgroupOf.1 hmem
      have hconj : (w : G) * (((CFSG.ABGLocalTools.chiefConj hchief.2.1 (n : H) w)⁻¹ *
          w : X) : G) * (w : G)⁻¹ ∈ Y := hchief.2.2.2.1 (w : G) w.2 _ hmemY
      have hcomm : ⁅(w : G), b⁆ =
          (w : G) * (((CFSG.ABGLocalTools.chiefConj hchief.2.1 (n : H) w)⁻¹ * w :
            X) : G) * (w : G)⁻¹ := by
        have hc : ((CFSG.ABGLocalTools.chiefConj hchief.2.1 (n : H) w : X) : G) =
            ((n : H) : G) * (w : G) * (((n : H) : G))⁻¹ := by
          simpa using CFSG.ABGLocalTools.chiefConj_apply_coe hchief.2.1 (n : H) w
        have hnb : ((n : H) : G) = b := rfl
        rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hc, hnb]
        group
      rw [hcomm]
      exact hconj
    have hwQ : (w : X ⧸ Y.subgroupOf X) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hwY)
    rw [hwQ]
    rfl
  have hℓp : ℓ ≠ p := by
    intro hlp
    have : Nontrivial V := hVnt
    have : Finite V := inferInstanceAs (Finite (X ⧸ Y.subgroupOf X))
    have : FiniteDimensional (ZMod ℓ) V := Module.Finite.of_finite
    have hPp : IsPGroup ℓ (B.subgroupOf H) :=
      IsPGroup.of_card (n := 1) (by rw [hDcard, ← hlp, pow_one])
    obtain ⟨v, hv0, hvfix⟩ :=
      Representation.exists_common_fixed_vector_of_isPGroup (p := ℓ) hPp
        (ρ.comp (B.subgroupOf H).subtype)
    have hvmem : v ∈ CFSG.LocalAnalysis.UniquenessCase.UCK.fixV ρ (B.subgroupOf H) := by
      intro g hg
      exact hvfix ⟨g, hg⟩
    rw [hfixV] at hvmem
    exact hv0 (by simpa using hvmem)
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc, x, hx, hcx⟩ := hcon
  have hQ : IsPGroup 2 ((⁅T, B⁆ : Subgroup G).subgroupOf H) := by
    have hle : ⁅T, B⁆ ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.1 hBT
    exact (hT.comap_subtype (K := H)).to_le (Subgroup.subgroupOf_mono H hle)
  let t : (⁅T, B⁆ : Subgroup G).subgroupOf H := ⟨⟨c, hTBH hc⟩, hc⟩
  have hQρ : ∃ t ∈ (⁅T, B⁆ : Subgroup G).subgroupOf H, ρ t ≠ 1 := by
    refine ⟨t, t.2, ?_⟩
    intro hρ1
    have hrep : CFSG.ABGLocalTools.chiefRep (p := ℓ) hchief.2.1 hchief.2.2.1 t = 1 := by
      apply Units.ext
      simpa [ρ] using hρ1
    have hxY := (CFSG.ABGLocalTools.chiefRep_eq_one_iff hchief.2.1 hchief.2.2.1 t).1 hrep x hx
    exact hcx (by simpa [t] using hxY)
  have hDQ : B.subgroupOf H ≤ normalizer (((⁅T, B⁆ : Subgroup G).subgroupOf H :
      Subgroup H) : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTBH]
    intro b hb
    exact Subgroup.normalizer_commutator_ge_right (H₁ := T) (H₂ := B)
      (Subgroup.mem_subgroupOf.1 hb)
  have hBpgroup : IsPGroup p B := IsPGroup.of_card (n := 1) (by rw [hBp, pow_one])
  have hTcop : ¬ p ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hDQc : ⁅B.subgroupOf H, (⁅T, B⁆ : Subgroup G).subgroupOf H⁆ =
      (⁅T, B⁆ : Subgroup G).subgroupOf H := by
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hBH hTBH, commutator_comm,
      CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp B T
        hBpgroup hTcop hBT]
  obtain ⟨-, k, hk⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.k42_unfaithful ρ (q := 2) (r := p)
    Nat.prime_two hp (Ne.symm hℓ2) (Ne.symm hℓp) (Ne.symm hp2) hDcard hfixV hQ hQρ hDQ hDQc
  exact hd ⟨k, hk⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
