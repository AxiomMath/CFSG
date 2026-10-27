module

public import CFSG.Walter.ReeOrder.JT.Section7P
public import CFSG.Walter.ReeOrder.JT.Section7N

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem conj_mem_normalizer_map {H : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (H : Set X)) (g : X) :
    g * x * g⁻¹ ∈ Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_map]
  have : (MulAut.conj (g * x * g⁻¹)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
    ext y
    simp [mul_assoc]
  rw [this, ← Subgroup.map_map, map_conj_eq_of_mem_normalizer hx]

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem not_nine_dvd_card
    {N : Subgroup G} (hN : Group.IsSolvable N) (h4 : 4 ∣ Nat.card N) :
    ¬ 9 ∣ Nat.card N := by
  classical
  set π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩}
  obtain ⟨H, hH⟩ := SolvableHall.solvable_hall_existence hN π
  have hcop : ∀ {r : ℕ} (hr : r.Prime), r = 2 ∨ r = 3 → ¬ r ∣ H.index := by
    intro r hr hr23 hd
    have := hH.p_in_pi_of_p_dvd_index ⟨r, hr⟩ hd
    rcases hr23 with rfl | rfl
    · exact this (Or.inl rfl)
    · exact this (Or.inr rfl)
  have hcard := H.card_mul_index
  have h4H : 4 ∣ Nat.card H := by
    have h2 : Nat.Coprime 4 H.index := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (hcop Nat.prime_two (Or.inl rfl)))
    exact h2.dvd_of_dvd_mul_right (hcard ▸ h4)
  set HG := H.map N.subtype
  have hHG : Nat.card HG = Nat.card H := Subgroup.card_map_of_injective N.subtype_injective
  have h72 := h.lemma_7_2 hp3 (H := HG) (fun r hr hrd => by
    rw [hHG] at hrd
    rcases hH.p_in_pi_of_p_dvd_card ⟨r, hr⟩ hrd with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1) (hHG ▸ h4H)
  intro h9
  apply h72.2
  rw [hHG]
  have h3 : Nat.Coprime 9 H.index := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (hcop Nat.prime_three (Or.inr rfl)))
  exact h3.dvd_of_dvd_mul_right (hcard ▸ h9)

theorem inf_centralizer_t_eq
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) {P : Subgroup G} (hP : IsPGroup p P) (hCpP : c.Cp p ≤ P) :
    P ⊓ Subgroup.centralizer ({h.t} : Set G) = c.Cp p := by
  have hCpt : c.Cp p ≤ Subgroup.centralizer ({h.t} : Set G) := fun x hx =>
    h.le_centralizer (c.torus.le (c.Cp_le_C p hx))
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hCpP hCpt) ?_).symm
  rw [c.card_Cp, ← h.factorization_card_centralizer_t hp3 c hpq]
  set Ct := Subgroup.centralizer ({h.t} : Set G)
  obtain ⟨S, hS⟩ := ((hP.to_le (inf_le_left : P ⊓ Ct ≤ P)).comap_subtype (K := Ct)).exists_le_sylow
  have h1 := Subgroup.card_le_of_le hS
  rw [Sylow.card_eq_multiplicity] at h1
  calc Nat.card (P ⊓ Ct : Subgroup G) = Nat.card ((P ⊓ Ct).comap Ct.subtype) := by
        rw [← Subgroup.card_map_of_injective Ct.subtype_injective,
          Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact inf_le_right)]
    _ ≤ _ := h1

theorem not_isCyclic_of_ne
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P : Sylow p G) (hCpP : c.Cp p ≤ P)
    (hT₀P : c.T₀ ≤ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hne : c.Cp p ≠ (P : Subgroup G)) : ¬ IsCyclic (P : Subgroup G) := by
  intro hc
  have hPp := P.isPGroup'
  have hpC : p ∣ Nat.card c.C := by
    have := c.card_C
    have hq : (h.q - 1) / 2 = Nat.card c.C := by omega
    rwa [hq] at hpq
  have hdisj : ∀ {u v : G}, u ∈ c.T₀ → v ∈ c.T₀ → u ≠ 1 → v ≠ 1 → u ≠ v →
      (P : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) ⊓
        ((P : Subgroup G) ⊓ Subgroup.centralizer ({v} : Set G)) = ⊥ := by
    intro u v hu hv hu1 hv1 huv
    rw [eq_bot_iff]
    rintro x ⟨⟨hxP, hxu⟩, -, hxv⟩
    rw [Subgroup.mem_bot]
    have hxu' := Subgroup.mem_centralizer_singleton_iff.mp hxu
    have hxv' := Subgroup.mem_centralizer_singleton_iff.mp hxv
    have hxV : x ∈ Subgroup.centralizer (c.T₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1, one_mul, mul_one]
      by_cases hyu : y = u
      · rw [hyu]; exact hxu'.symm
      by_cases hyv : y = v
      · rw [hyv]; exact hxv'.symm
      rw [eq_mul_of_mem_kleinFour c.isKleinFour_T₀ hu hv hy hu1 hv1 huv hy1 hyu hyv]
      calc u * v * x = u * (v * x) := by group
        _ = u * (x * v) := by rw [hxv']
        _ = (u * x) * v := by group
        _ = (x * u) * v := by rw [hxu']
        _ = x * (u * v) := by group
    have h1 : orderOf x ∣ Nat.card (Subgroup.centralizer (c.T₀ : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hxV
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    have h2 : orderOf x ∣ p ^ n := hn ▸ Subgroup.orderOf_dvd_natCard _ hxP
    have hcop : Nat.Coprime (p ^ n) (Nat.card (Subgroup.centralizer (c.T₀ : Set G))) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
        (h.not_dvd_card_centralizer_of_isKleinFour hp3 hpq c.isKleinFour_T₀))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  have hBW := h.card_eq_mul_of_le_normalizer hp3 c hpq hPp hT₀P
  have hle : ∀ v : G, (P : Subgroup G) ⊓ Subgroup.centralizer ({v} : Set G) ≤ P :=
    fun v => inf_le_left
  have htne : (P : Subgroup G) ⊓ Subgroup.centralizer ({h.t} : Set G) ≠ ⊥ := by
    rw [h.inf_centralizer_t_eq hp3 c hpq hPp hCpP]
    exact c.Cp_ne_bot p hpC
  have hw : (P : Subgroup G) ⊓ Subgroup.centralizer ({c.w} : Set G) = ⊥ := by
    by_contra hw
    exact inf_ne_bot_of_isCyclic hc hPp (hle _) (hle _) htne hw
      (hdisj c.t_mem_T₀ c.w_mem_T₀ h.t_ne_one c.w_ne_one c.t_ne_w)
  have htw : (P : Subgroup G) ⊓ Subgroup.centralizer ({h.t * c.w} : Set G) = ⊥ := by
    by_contra htw
    exact inf_ne_bot_of_isCyclic hc hPp (hle _) (hle _) htne htw
      (hdisj c.t_mem_T₀ c.tw_mem_T₀ h.t_ne_one c.tw_ne_one c.t_ne_tw)
  rw [hw, htw, Subgroup.card_bot, mul_one, mul_one,
    h.inf_centralizer_t_eq hp3 c hpq hPp hCpP] at hBW
  exact hne (Subgroup.eq_of_le_of_card_ge hCpP hBW.le)

theorem lemma_7_8
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    (P : Sylow p G) (hnc : ¬ IsCyclic (P : Subgroup G)) :
    (∃ V : Subgroup G, IsKleinFour V ∧ V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
      ∃ s : G, s ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
        s ∈ Subgroup.normalizer (V : Set G) ∧ orderOf s = 3) ∧
    Nat.card (omegaZ (P : Subgroup G) p) = p ^ 3 ∧
    omegaOne (P : Subgroup G) p = omegaZ (P : Subgroup G) p := by
  obtain ⟨P₀, -, hT₀P₀⟩ := h.exists_sylow_invariant hp3 c hpq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  have hPmap : (P : Subgroup G) = (P₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hnc₀ : ¬ IsCyclic (P₀ : Subgroup G) := by
    intro hc
    apply hnc
    rw [hPmap]
    have e := (P₀ : Subgroup G).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hW₀ : ¬ IsCyclic (omegaZ (P₀ : Subgroup G) p) :=
    fun hc => h.false_of_isCyclic_omegaZ hp3 c hpq P₀ hT₀P₀ hnc₀ hc
  obtain ⟨s, hsP, hsT, hs3⟩ := h.exists_orderOf_three hp3 c hpq P₀ hT₀P₀ hW₀
  obtain ⟨hcard, hΩ⟩ := h.omegaOne_eq_omegaZ hp3 c hpq P₀ hT₀P₀ hsP hsT hs3
  refine ⟨⟨c.T₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, g * s * g⁻¹, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine isKleinFour_of_card_four ?_ ?_
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, c.isKleinFour_T₀.card_four]
    · rintro ⟨_, x, hx, rfl⟩
      apply Subtype.ext
      have hxx : x * x = 1 := mul_self_of_isKleinFour' c.isKleinFour_T₀ hx
      simp only [Subgroup.coe_mul, Subgroup.coe_one, ← map_mul, hxx, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [hPmap]
    exact conj_mem_normalizer_map (hT₀P₀ hx) g
  · rw [hPmap]
    exact conj_mem_normalizer_map hsP g
  · exact conj_mem_normalizer_map hsT g
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs3]
  · rw [hPmap, ← map_omegaZ (MulAut.conj g), Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hcard]
  · rw [hPmap, ← map_omegaZ (MulAut.conj g), ← map_omegaOne (MulAut.conj g), hΩ]

theorem lemma_7_8_card
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    (P : Sylow p G) (hnc : ¬ IsCyclic (P : Subgroup G)) :
    4 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      ¬ 9 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  obtain ⟨⟨V, hV, hVP, -⟩, -⟩ := h.lemma_7_8 hp3 c hpq P hnc
  have h4 : 4 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    have := Subgroup.card_dvd_of_le hVP
    rwa [hV.card_four] at this
  have hP1 : (P : Subgroup G) ≠ ⊥ := fun h0 => hnc (by rw [h0]; infer_instance)
  exact ⟨h4, h.not_nine_dvd_card hp3 (h.isSolvable_normalizer_of_isPGroup_pi hp3 hpq
    P.isPGroup' hP1) h4⟩

end JTHyp

end CFSG.Walter.JT
