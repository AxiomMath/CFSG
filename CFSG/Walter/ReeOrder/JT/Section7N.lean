module

public import CFSG.Walter.ReeOrder.JT.Section7L

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups commutatorElement
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X]

@[expose] def omegaOne (H : Subgroup X) (p : ℕ) : Subgroup X :=
  Subgroup.closure {x | x ∈ H ∧ x ^ p = 1}

theorem mem_normalizer_bot (x : X) : x ∈ Subgroup.normalizer ((⊥ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl
    group
  · intro hy
    have := congrArg (fun z => x⁻¹ * z * x) hy
    simpa [mul_assoc] using this

theorem omegaOne_le (H : Subgroup X) (p : ℕ) : omegaOne H p ≤ H := by
  rw [omegaOne, Subgroup.closure_le]
  exact fun _ hx => hx.1

theorem mem_omegaOne {H : Subgroup X} {p : ℕ} {x : X} (hx : x ∈ H) (hxp : x ^ p = 1) :
    x ∈ omegaOne H p :=
  Subgroup.subset_closure ⟨hx, hxp⟩

theorem omegaZ_le_omegaOne (H : Subgroup X) (p : ℕ) : omegaZ H p ≤ omegaOne H p :=
  fun _ hx => mem_omegaOne hx.1 hx.2.2

theorem map_omegaOne {Y : Type*} [Group Y] (e : X ≃* Y) (H : Subgroup X) (p : ℕ) :
    (omegaOne H p).map e.toMonoidHom = omegaOne (H.map e.toMonoidHom) p := by
  rw [omegaOne, omegaOne, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxH, hxp⟩, rfl⟩
    exact ⟨⟨x, hxH, rfl⟩, by rw [← map_pow, hxp, map_one]⟩
  · rintro ⟨⟨x, hxH, rfl⟩, hxp⟩
    refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
    apply e.injective
    simpa using hxp

theorem map_conj_eq_of_mem_normalizer {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hg _).mpr (by simpa [mul_assoc] using hx),
      by simp [mul_assoc]⟩

theorem mem_normalizer_of_map_conj_eq [Finite X] {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set X) :=
  mem_normalizer_of_conj_mem fun x hx => by
    rw [← h]
    exact ⟨x, hx, rfl⟩

theorem normalizer_le_normalizer_omegaOne [Finite X] (H : Subgroup X) (p : ℕ) :
    Subgroup.normalizer (H : Set X) ≤ Subgroup.normalizer ((omegaOne H p : Subgroup X) : Set X) :=
  fun g hg => mem_normalizer_of_map_conj_eq (by
    rw [map_omegaOne (MulAut.conj g) H p, map_conj_eq_of_mem_normalizer hg])

theorem normalizer_le_normalizer_lowerCentralSeries [Finite X] (H : Subgroup X) (n : ℕ) :
    Subgroup.normalizer (H : Set X) ≤
      Subgroup.normalizer ((H.lowerCentralSeries n : Subgroup X) : Set X) :=
  fun g hg => mem_normalizer_of_map_conj_eq (by
    rw [Subgroup.map_lowerCentralSeries, map_conj_eq_of_mem_normalizer hg])

theorem lowerCentralSeries_one_eq_bot [Finite X] {H : Subgroup X} (hH : Group.IsNilpotent H)
    (h21 : H.lowerCentralSeries 2 = H.lowerCentralSeries 1) : H.lowerCentralSeries 1 = ⊥ := by
  have hall : ∀ n, H.lowerCentralSeries (n + 1) = H.lowerCentralSeries 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ, ih, ← Subgroup.lowerCentralSeries_succ, h21]
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries H).mp hH
  have := Subgroup.lowerCentralSeries_antitone H (Nat.le_succ n)
  rw [hn, le_bot_iff, hall] at this
  exact this

theorem pow_mem_lowerCentralSeries_two [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Subgroup X) {z : X} (hz : z ∈ omegaOne H p) :
    z ^ p ∈ (omegaOne H p).lowerCentralSeries 2 := by
  rw [omegaOne] at hz ⊢
  set k : Set X := {x | x ∈ H ∧ x ^ p = 1}
  set P₀ := Subgroup.closure k
  set L : Subgroup P₀ := (⊤ : Subgroup P₀).lowerCentralSeries 2
  have : L.Normal := inferInstance
  set π := QuotientGroup.mk' L
  have hcent : ∀ a b : P₀ ⧸ L, ⁅a, b⁆ ∈ Subgroup.center (P₀ ⧸ L) := by
    have hbot : (⊤ : Subgroup (P₀ ⧸ L)).lowerCentralSeries 2 = ⊥ := by
      have h1 := Subgroup.map_lowerCentralSeries (⊤ : Subgroup P₀) π 2
      rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective L)] at h1
      rw [← h1, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    intro a b
    have hab : ⁅a, b⁆ ∈ (⊤ : Subgroup (P₀ ⧸ L)).lowerCentralSeries 1 :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    have := hbot hab
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp this g (Set.mem_univ g))
  have key : ∀ y : P₀, (π y) ^ p = 1 := by
    intro y
    have hy : y ∈ Subgroup.closure (((↑) : P₀ → X) ⁻¹' k) := by
      rw [Subgroup.closure_closure_coe_preimage]
      exact Subgroup.mem_top y
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (by simpa using hx.2)
      rw [this, map_one]
    | one => rw [map_one, one_pow]
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact pth_mul_eq_one_of_class2 (p := p) hp2 (π a) (π b) (hcent _ _) ha hb
    | inv a _ ha => rw [map_inv, inv_pow, ha, inv_one]
  have hz' := key ⟨z, hz⟩
  rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hz'
  rw [← Subgroup.top_subtype_lowerCentralSeries]
  exact ⟨_, hz', rfl⟩

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem card_inf_centralizer_eq
    (c : TorusConf h) {s : G}
    (hsT : s ∈ Subgroup.normalizer (c.T₀ : Set G)) (hs3 : orderOf s = 3) {K : Subgroup G}
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) {u v : G} (hu : u ∈ c.T₀) (hv : v ∈ c.T₀)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    Nat.card (K ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
      Nat.card (K ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) := by
  have hsC : s ∉ Subgroup.centralizer (c.T₀ : Set G) := fun hC =>
    h.three_not_dvd_card_centralizer hp3 c.isKleinFour_T₀
      (hs3 ▸ Subgroup.orderOf_dvd_natCard _ hC)
  have hs3C : s ^ 3 ∈ Subgroup.centralizer (c.T₀ : Set G) := by
    rw [← hs3, pow_orderOf_eq_one]
    exact Subgroup.one_mem _
  obtain ⟨k, hk⟩ := exists_pow_conj_of_pow_three_mem c.isKleinFour_T₀ hsT hs3C hsC hu hu1 hv hv1
  have hmap : (K ⊓ Subgroup.centralizer ({u} : Set G)).map (MulAut.conj (s ^ k)).toMonoidHom =
      K ⊓ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (s ^ k)).injective]
    have hK : K.map (MulAut.conj (s ^ k)).toMonoidHom = K := by
      have := (conj_smul_eq_iff (g := s ^ k) (K := K)).mpr (Subgroup.pow_mem _ hsK k)
      rwa [Subgroup.pointwise_smul_def] at this
    have hC := centralizer_singleton_map (MulAut.conj (s ^ k)) u
    rw [MulAut.conj_apply, hk] at hC
    rw [hK, hC]
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj (s ^ k)).injective]

theorem relIndex_eq_one_or_eq_pow_three
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) {s : G} (hsT : s ∈ Subgroup.normalizer (c.T₀ : Set G))
    (hs3 : orderOf s = 3) {K₁ K₂ : Subgroup G} (hK₁ : IsPGroup p K₁) (hK₂₁ : K₂ ≤ K₁)
    (hT₁ : c.T₀ ≤ Subgroup.normalizer (K₁ : Set G))
    (hT₂ : c.T₀ ≤ Subgroup.normalizer (K₂ : Set G))
    (hs₁ : s ∈ Subgroup.normalizer (K₁ : Set G)) (hs₂ : s ∈ Subgroup.normalizer (K₂ : Set G))
    (hpow : ∀ z ∈ K₁, z ^ p ∈ K₂) :
    K₂.relIndex K₁ = 1 ∨ K₂.relIndex K₁ = p ^ 3 := by
  have hrel := h.relIndex_eq_mul hp3 c hpq hK₁ hK₂₁ hT₁ hT₂
  have hfac : ∀ {u v : G}, u ∈ c.T₀ → v ∈ c.T₀ → u ≠ 1 → v ≠ 1 →
      (K₂ ⊓ Subgroup.centralizer ({u} : Set G)).relIndex
          (K₁ ⊓ Subgroup.centralizer ({u} : Set G)) =
        (K₂ ⊓ Subgroup.centralizer ({v} : Set G)).relIndex
          (K₁ ⊓ Subgroup.centralizer ({v} : Set G)) := by
    intro u v hu hv hu1 hv1
    have e₁ := card_mul_relIndex (inf_le_inf_right (Subgroup.centralizer ({u} : Set G)) hK₂₁)
    have e₂ := card_mul_relIndex (inf_le_inf_right (Subgroup.centralizer ({v} : Set G)) hK₂₁)
    rw [h.card_inf_centralizer_eq hp3 c hsT hs3 hs₁ hu hv hu1 hv1,
      h.card_inf_centralizer_eq hp3 c hsT hs3 hs₂ hu hv hu1 hv1, ← e₂] at e₁
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos e₁
  rw [hfac c.w_mem_T₀ c.t_mem_T₀ c.w_ne_one h.t_ne_one,
    hfac c.tw_mem_T₀ c.t_mem_T₀ c.tw_ne_one h.t_ne_one] at hrel
  have hcyc := h.isCyclic_of_le_centralizer_pi hp3 hpq (hK₁.to_le inf_le_left) h.orderOf_t
    (inf_le_right :
      K₁ ⊓ Subgroup.centralizer ({h.t} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G))
  have hdvd := relIndex_dvd_of_pow_mem hp.out.ne_zero hcyc (inf_le_inf_right _ hK₂₁)
    fun z hz => ⟨hpow z hz.1, Subgroup.pow_mem _ hz.2 p⟩
  rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
  · left
    rw [hrel, h1]
  · right
    rw [hrel, h1]
    ring

theorem omegaOne_eq_omegaZ
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P : Sylow p G)
    (hT₀P : c.T₀ ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) {s : G}
    (hsP : s ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hsT : s ∈ Subgroup.normalizer (c.T₀ : Set G)) (hs3 : orderOf s = 3) :
    Nat.card (omegaZ (P : Subgroup G) p) = p ^ 3 ∧
      omegaOne (P : Subgroup G) p = omegaZ (P : Subgroup G) p := by
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hp2 : p ≠ 2 := by omega
  set W := omegaZ (P : Subgroup G) p
  set P₀ := omegaOne (P : Subgroup G) p
  have hPp := P.isPGroup'
  have hNW := normalizer_le_normalizer_omegaZ (H := (P : Subgroup G)) (r := p)
  have hNP₀ := normalizer_le_normalizer_omegaOne (P : Subgroup G) p
  have hP₀p : IsPGroup p P₀ := hPp.to_le (omegaOne_le _ _)
  have hP1 : (P : Subgroup G) ≠ ⊥ := by
    have hpC : p ∣ Nat.card c.C := by
      have := c.card_C
      have hq : (h.q - 1) / 2 = Nat.card c.C := by omega
      rwa [hq] at hpq
    exact P.ne_bot_of_dvd_card (hpC.trans (Subgroup.card_subgroup_dvd_card _))
  have hW1 : W ≠ ⊥ := omegaZ_ne_bot hPp hP1
  have hWcard : Nat.card W = p ^ 3 := by
    have := h.relIndex_eq_one_or_eq_pow_three hp3 c hpq hsT hs3 (hPp.to_le omegaZ_le)
      bot_le (hT₀P.trans hNW) (fun x _ => mem_normalizer_bot x) (hNW hsP) (mem_normalizer_bot s)
      (fun z hz => by rw [pow_eq_one_of_mem_omegaZ hz]; exact Subgroup.one_mem _)
    rw [Subgroup.relIndex_bot_left] at this
    rcases this with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hW1
    · exact h1
  set P₁ := P₀.lowerCentralSeries 1
  set P₂ := P₀.lowerCentralSeries 2
  have hP₁₀ : P₁ ≤ P₀ := Subgroup.lowerCentralSeries_le_self P₀ 1
  have hP₂₁ : P₂ ≤ P₁ := Subgroup.lowerCentralSeries_antitone P₀ (by norm_num : 1 ≤ 2)
  have hT₀ : c.T₀ ≤ Subgroup.normalizer ((P₀ : Subgroup G) : Set G) := hT₀P.trans hNP₀
  have hs₀ : s ∈ Subgroup.normalizer ((P₀ : Subgroup G) : Set G) := hNP₀ hsP
  have hN₁ := normalizer_le_normalizer_lowerCentralSeries P₀ 1
  have hN₂ := normalizer_le_normalizer_lowerCentralSeries P₀ 2
  have hpow2 : ∀ z ∈ P₀, z ^ p ∈ P₂ := fun z hz => pow_mem_lowerCentralSeries_two hp2 _ hz
  have hW₀ : W ≤ P₀ := omegaZ_le_omegaOne _ _
  have hP₀1 : P₀ ≠ ⊥ := fun h0 => hW1 (le_bot_iff.mp (h0 ▸ hW₀))
  have hnil : Group.IsNilpotent P₀ := hP₀p.isNilpotent
  have hP₁ne : P₁ ≠ P₀ := by
    have : Nontrivial P₀ := (Subgroup.nontrivial_iff_ne_bot P₀).mpr hP₀1
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := P₀)
    intro heq
    apply hlt.ne
    apply Subgroup.map_injective P₀.subtype_injective
    rw [← Subgroup.top_lowerCentralSeries_one, Subgroup.top_subtype_lowerCentralSeries,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact heq
  have hcube := h.relIndex_eq_one_or_eq_pow_three hp3 c hpq hsT hs3 hP₀p hP₁₀ hT₀ (hT₀.trans hN₁)
    hs₀ (hN₁ hs₀) (fun z hz => hP₂₁ (hpow2 z hz))
  have hcube' : P₁.relIndex P₀ = p ^ 3 := by
    rcases hcube with h1 | h1
    · exact absurd (le_antisymm hP₁₀ (Subgroup.relIndex_eq_one.mp h1)) hP₁ne
    · exact h1
  have hbound := h.relIndex_dvd_pow_three hp3 c hpq hP₀p (hP₂₁.trans hP₁₀) hT₀ (hT₀.trans hN₂)
    hpow2
  rw [← Subgroup.relIndex_mul_relIndex P₂ P₁ P₀ hP₂₁ hP₁₀, hcube'] at hbound
  have h21 : P₂.relIndex P₁ = 1 := by
    have hpos : 0 < p ^ 3 := by positivity
    obtain ⟨k, hk⟩ := hbound
    have : P₂.relIndex P₁ * k = 1 := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [one_mul]
      nth_rewrite 2 [hk]
      ring
    exact Nat.eq_one_of_mul_eq_one_right this
  have hP₂₁' : P₂ = P₁ := le_antisymm hP₂₁ (Subgroup.relIndex_eq_one.mp h21)
  have hP₁1 : P₁ = ⊥ := lowerCentralSeries_one_eq_bot hnil hP₂₁'
  have hpow0 : ∀ z ∈ P₀, z ^ p ∈ (⊥ : Subgroup G) := fun z hz => by
    have := hpow2 z hz
    rwa [hP₂₁', hP₁1] at this
  have hbound0 := h.relIndex_dvd_pow_three hp3 c hpq hP₀p bot_le hT₀
    (fun x _ => mem_normalizer_bot x) hpow0
  rw [Subgroup.relIndex_bot_left] at hbound0
  refine ⟨hWcard, (Subgroup.eq_of_le_of_card_ge hW₀ ?_).symm⟩
  rw [hWcard]
  exact Nat.le_of_dvd (by positivity) hbound0

end JTHyp

end CFSG.Walter.JT
