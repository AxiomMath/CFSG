module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B11
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588

theorem conj_mem_of_map_eq_uc6b {G : Type*} [Group G] {X Y : Subgroup G} {w : G}
    (h : X.map (MulAut.conj w).toMonoidHom = Y) {x : G} (hx : x ∈ X) : w * x * w⁻¹ ∈ Y := by
  rw [← h]
  exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem conj_inv_mem_of_map_eq_uc6b {G : Type*} [Group G] {X Y : Subgroup G} {w : G}
    (h : X.map (MulAut.conj w).toMonoidHom = Y) {y : G} (hy : y ∈ Y) : w⁻¹ * y * w ∈ X := by
  rw [← h] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa [MulAut.conj_apply, mul_assoc] using hx

theorem conj_inv_pow_uc6b {G : Type*} [Group G] (k e : G) (n : ℕ) :
    (k⁻¹ * e * k) ^ n = k⁻¹ * e ^ n * k := by
  have h := conj_pow (a := k⁻¹) (b := e) (i := n)
  rwa [inv_inv] at h

theorem isPGroup_zpowers_uc6b {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x : G} {n : ℕ}
    (h : x ^ p ^ n = 1) : IsPGroup p (zpowers x) := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

namespace Mz614

namespace A10Setup

variable {G : Type} [Group G] [Finite G] {m : Mz614 G} (D : A10Setup m)

theorem conj_Z_le_L {w : G} (hw₁ : m.Z.map (MulAut.conj w).toMonoidHom = line₁.map D.ι)
    (hw₂ : (line₁.map D.ι).map (MulAut.conj w).toMonoidHom = m.Z) :
    (∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L) ∧ (∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) :=
  ⟨fun _ hz => D.map_ι_le_L _ (conj_mem_of_map_eq_uc6b hw₁ hz),
    fun _ hz => D.map_ι_le_L _ (conj_inv_mem_of_map_eq_uc6b hw₂ hz)⟩

include D in
theorem mem_Z_of_pow_five (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (hr : m.r = 5) {e : G} (heL : e ∈ centralizer (m.L : Set G)) (heH : e ∈ m.H)
    (he : e ^ 5 = 1) : e ∈ m.Z := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hsix := m.hZ.sixteen h69
  have heA : e ∈ centralizer (m.A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨z, hz, b, hb, rfl⟩ := m.exists_mul_of_mem_A h620 ha
    have h1 : z * e = e * z := mem_centralizer_iff.1 heH z hz
    have h2 : b * e = e * b := mem_centralizer_iff.1 heL b hb.2
    calc z * b * e = z * (b * e) := mul_assoc _ _ _
      _ = z * e * b := by rw [h2, mul_assoc]
      _ = e * (z * b) := by rw [h1, mul_assoc]
  have hRsyl : IsSylowOf m.r m.R (centralizer (m.A : Set G)) :=
    m.R_isSylowOf_top.of_le (m.R_le_centralizer_A h69) le_top
  have hep : IsPGroup m.r (zpowers e) := isPGroup_zpowers_uc6b m.hr (n := 1) (by rw [pow_one, hr, he])
  obtain ⟨k, hkC, hk⟩ := exists_conj_le_of_isSylowOf hRsyl ((zpowers_le).2 heA) hep
  have hkA : k⁻¹ * e * k ∈ m.A :=
    hsix.2 _ (hk e (mem_zpowers e)) (by rw [conj_inv_pow_uc6b, hr, he]; group)
  have heA' : e ∈ m.A := by
    have hc := mem_centralizer_iff.1 hkC _ hkA
    have he' : e = k⁻¹ * e * k := by
      calc e = k * (k⁻¹ * e * k) * k⁻¹ := by group
        _ = (k⁻¹ * e * k) * k * k⁻¹ := by rw [← hc]
        _ = k⁻¹ * e * k := by group
    rw [he']
    exact hkA
  obtain ⟨z, hz, b, hb, hzb⟩ := m.exists_mul_of_mem_A h620 heA'
  have hbC : b ∈ centralizer (m.L : Set G) := by
    have hb' : b = z⁻¹ * e := by rw [hzb]; group
    rw [hb']
    refine mul_mem (inv_mem (mem_centralizer_iff.2 fun l hl => ?_)) heL
    exact (m.Z_comm_L hz hl).symm
  rw [hzb, D.eq_one_of_mem_centralizer hb.2 hbC, mul_one]
  exact hz

include D in
theorem pow_five_of_pow_twentyfive_CHL (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    (h620 : m.C620) (hr : m.r = 5) {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L)
    (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) {e : G} (heL : e ∈ centralizer (m.L : Set G))
    (heH : e ∈ m.H) (he : e ^ 25 = 1) : e ^ 5 = 1 := by
  have he5 : e ^ 5 ∈ m.Z := D.mem_Z_of_pow_five h69 h620 hr (pow_mem heL 5) (pow_mem heH 5)
    (by rw [← pow_mul]; exact he)
  set d := w⁻¹ * e * w with hd
  have hdH : d ∈ m.H := by
    refine mem_centralizer_iff.2 fun z hz => ?_
    have h1 := mem_centralizer_iff.1 heL _ (hw₁ z hz)
    calc z * d = w⁻¹ * ((w * z * w⁻¹) * e) * w := by rw [hd]; group
      _ = w⁻¹ * (e * (w * z * w⁻¹)) * w := by rw [h1]
      _ = d * z := by rw [hd]; group
  have hdpow : ∀ n : ℕ, d ^ n = w⁻¹ * e ^ n * w := fun n => conj_inv_pow_uc6b w e n
  have hd25 : d ^ 25 = 1 := by rw [hdpow, he]; group
  have hd5L : d ^ 5 ∈ m.L := by rw [hdpow]; exact hw₂ _ he5
  obtain ⟨ℓ, hℓL, hc⟩ := D.exists_mem_centralizer_of_chi_eq_one
    (D.chi_eq_one_of_pow (n := ⟨d, m.H_le_normalizer_L hdH⟩) (k := 25) (by decide) hd25)
  set c := ℓ⁻¹ * d with hcdef
  have hdc : d = ℓ * c := by rw [hcdef]; group
  have hcomm : Commute ℓ c := mem_centralizer_iff.1 hc ℓ hℓL
  have hd5 : d ^ 5 = ℓ ^ 5 * c ^ 5 := by rw [hdc, hcomm.mul_pow]
  have hc5L : c ^ 5 ∈ m.L := by
    have hc5 : c ^ 5 = (ℓ ^ 5)⁻¹ * d ^ 5 := by rw [hd5]; group
    rw [hc5]
    exact mul_mem (inv_mem (pow_mem hℓL 5)) hd5L
  have hc5 : c ^ 5 = 1 := D.eq_one_of_mem_centralizer hc5L (pow_mem hc 5)
  have hℓ5 : ℓ ^ 5 = d ^ 5 := by rw [hd5, hc5, mul_one]
  have hℓ25 : ℓ ^ 25 = 1 := by
    rw [show (25 : ℕ) = 5 * 5 from rfl, pow_mul, hℓ5, ← pow_mul]
    exact hd25
  have hd5' : d ^ 5 = 1 := by rw [← hℓ5]; exact D.pow_five_of_mem_L hℓL hℓ25
  rw [hdpow] at hd5'
  have he' : e ^ 5 = w * (w⁻¹ * e ^ 5 * w) * w⁻¹ := by group
  rw [he', hd5']
  group

include D in
theorem pow_five_of_pow_prime_pow_CHL (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    (h620 : m.C620) (hr : m.r = 5) {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L)
    (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) (k : ℕ) :
    ∀ e ∈ centralizer (m.L : Set G) ⊓ m.H, e ^ 5 ^ k = 1 → e ^ 5 = 1 := by
  induction k with
  | zero =>
    intro e _ h
    rw [pow_zero, pow_one] at h
    rw [h, one_pow]
  | succ k ih =>
    intro e he h
    have h25 : (e ^ 5) ^ 5 = 1 :=
      ih (e ^ 5) (pow_mem he 5) (by rw [← pow_mul, ← pow_succ']; exact h)
    rw [← pow_mul] at h25
    exact D.pow_five_of_pow_twentyfive_CHL h69 h620 hr hw₁ hw₂ he.1 he.2 h25

include D in
theorem mem_Z_of_pow_prime_pow (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (hr : m.r = 5) {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L)
    (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) {e : G} (he : e ∈ centralizer (m.L : Set G) ⊓ m.H)
    {k : ℕ} (hk : e ^ 5 ^ k = 1) : e ∈ m.Z :=
  D.mem_Z_of_pow_five h69 h620 hr he.1 he.2
    (D.pow_five_of_pow_prime_pow_CHL h69 h620 hr hw₁ hw₂ k e he hk)

theorem card_le_of_le_Ka (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (hr : m.r = 5) {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L)
    (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) {P : Subgroup G} (hPK : P ≤ D.Ka)
    (hP : IsPGroup 5 P) (hZP : m.Z ≤ P) : Nat.card P ≤ 25 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsix := m.hZ.sixteen h69
  have hPH : P ≤ m.H := by
    intro x hx
    obtain ⟨k, -, hk⟩ :=
      exists_conj_le_of_isSylowOf m.R_isSylowOf_top le_top (by rw [hr]; exact hP)
    refine mem_centralizer_iff.2 fun z hz => ?_
    have hzA : k⁻¹ * z * k ∈ m.A := hsix.2 _ (hk z (hZP hz)) (by
      rw [conj_inv_pow_uc6b, (isElemAbelian_of_card_prime m.hr m.card_Z).2 z hz]
      group)
    have h1 := hsix.1 _ hzA _ (hk x hx)
    calc z * x = k * ((k⁻¹ * z * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * x * k) * (k⁻¹ * z * k)) * k⁻¹ := by rw [h1]
      _ = x * z := by group
  have hPN : P ≤ normalizer (m.L : Set G) := hPH.trans m.H_le_normalizer_L
  let f : ↥P →* Equiv.Perm (Fin 10) := D.permOf.comp (Subgroup.inclusion hPN)
  have hP5 : ∀ x : ↥P, ∃ k : ℕ, (x : G) ^ 5 ^ k = 1 := fun x => by
    obtain ⟨k, hk⟩ := hP x
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hker : Nat.card f.ker ≤ 5 := by
    have hle : (f.ker).map P.subtype ≤ m.Z := by
      rintro _ ⟨x, hx, rfl⟩
      have hC := D.mem_centralizer_of_permOf_eq_one (n := Subgroup.inclusion hPN x) hx
      obtain ⟨k, hk⟩ := hP5 x
      exact D.mem_Z_of_pow_prime_pow h69 h620 hr hw₁ hw₂ ⟨hC, hPH x.2⟩ hk
    have h := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective P.subtype_injective, m.card_Z, hr] at h
  have hrange : f.range ≤ (altA T6).map (alternatingGroup (Fin 10)).subtype := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := hP5 x
    have hchi : D.chi (Subgroup.inclusion hPN x) = 1 :=
      D.chi_eq_one_of_pow (k := 5 ^ k) (Odd.pow (by decide)) hk
    have hmem : D.permOf (Subgroup.inclusion hPN x) ∈ alternatingGroup (Fin 10) :=
      D.permOf_mem_of_chi hchi
    refine ⟨⟨_, hmem⟩, mem_altA_T6_iff.1 fun σ hσ => ?_, rfl⟩
    have h1 := D.conj_eq_of_permOf (n := Subgroup.inclusion hPN x) (a := ⟨_, hmem⟩) rfl
      (D.ι_mem_L σ)
    have h2 : (x : G) * D.ι σ * (x : G)⁻¹ = D.ι σ := by
      rw [← (D.mem_Ka_iff.1 (hPK x.2)) σ hσ]
      group
    have h3 : D.ι ⟨_, hmem⟩ * D.ι σ * (D.ι ⟨_, hmem⟩)⁻¹ = D.ι σ := h1.symm.trans h2
    have h4 : (⟨_, hmem⟩ : A10) * σ * (⟨_, hmem⟩ : A10)⁻¹ = σ :=
      D.ι_injective (by rw [map_mul, map_mul, map_inv]; exact h3)
    calc σ * ⟨_, hmem⟩ = ((⟨_, hmem⟩ : A10) * σ * (⟨_, hmem⟩ : A10)⁻¹) * ⟨_, hmem⟩ := by
          rw [h4]
      _ = ⟨_, hmem⟩ * σ := by group
  have hrange_card : Nat.card f.range ≤ 5 := by
    obtain ⟨k, hk⟩ := (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
    have hdvd : Nat.card f.range ∣ 360 := by
      have h := Subgroup.card_dvd_of_le hrange
      rwa [Subgroup.card_map_of_injective (alternatingGroup (Fin 10)).subtype_injective,
        card_altA_T6] at h
    rw [hk] at hdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra h
      push Not at h
      have h' := (Nat.pow_dvd_pow 5 h).trans hdvd
      norm_num at h'
    calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 5 := pow_one 5
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card P := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  calc Nat.card P = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ ≤ 5 * 5 := Nat.mul_le_mul hker hrange_card
    _ = 25 := rfl

theorem line₁_le_Ka : line₁.map D.ι ≤ D.Ka := by
  rintro _ ⟨σ, hσ, rfl⟩
  rw [D.ι_mem_Ka_iff]
  rw [line₁_eq] at hσ
  exact (zpowers_le.2 a₁_mem_T6) hσ

theorem card_Z_sup_line₁ (h620 : m.C620) (hr : m.r = 5) :
    Nat.card ↥(m.Z ⊔ line₁.map D.ι) = 25 := by
  have hZL : m.Z ⊓ m.L = ⊥ := inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2
  have hdisj : m.Z ⊓ line₁.map D.ι = ⊥ := by
    rw [eq_bot_iff, ← hZL]
    exact inf_le_inf_left _ (D.map_ι_le_L _)
  rw [card_sup_of_commute_of_disjoint (fun z hz y hy => m.Z_comm_L hz (D.map_ι_le_L _ hy)) hdisj,
    m.card_Z, D.card_map_ι, card_line₁, hr]

theorem isPGroup_Z_sup_line₁ (h620 : m.C620) (hr : m.r = 5) :
    IsPGroup 5 ↥(m.Z ⊔ line₁.map D.ι) :=
  IsPGroup.of_card (n := 2) (by rw [D.card_Z_sup_line₁ h620 hr]; norm_num)

theorem isSylowOf_Ka (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (hr : m.r = 5) {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L)
    (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) : IsSylowOf 5 (m.Z ⊔ line₁.map D.ι) D.Ka := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hle : m.Z ⊔ line₁.map D.ι ≤ D.Ka := sup_le D.Z_le_Ka D.line₁_le_Ka
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge hle (D.isPGroup_Z_sup_line₁ h620 hr)
  obtain ⟨hPK, hPp, -⟩ := isSylowOf_iff.1 hP
  have hcard := D.card_le_of_le_Ka h69 h620 hr hw₁ hw₂ hPK hPp (le_sup_left.trans hQP)
  have heq : m.Z ⊔ line₁.map D.ι = P :=
    Subgroup.eq_of_le_of_card_ge hQP (by rw [D.card_Z_sup_line₁ h620 hr]; exact hcard)
  rw [heq]
  exact hP

end A10Setup

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
