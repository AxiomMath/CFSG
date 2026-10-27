module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4F4
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
public import CFSG.Quasithin.Background.SmithB42Disp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup
open scoped commutatorElement

@[expose] def InvolutionWitness {S : Type*} [Group S] (s : S) : Prop :=
  (∃ c : S, orderOf (s * (c * s * c⁻¹)) = 13) ∨
    (∃ c g : S, orderOf (s * (c * s * c⁻¹)) = 5 ∧
      g * (s * (c * s * c⁻¹)) * g⁻¹ = (s * (c * s * c⁻¹)) ^ 2) ∨
    ∃ cs : List S, cs.length ≤ 6 ∧ Subgroup.closure {v : S | ∃ c ∈ cs, v = c * s * c⁻¹} = ⊤

private lemma m4pow_card_eq_one {L : Type*} [Group L]
    (hZ : Nat.card (Subgroup.center L) = 3) {y : L} (hy : y ∈ Subgroup.center L) :
    y ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥(Subgroup.center L)) (x := ⟨y, hy⟩)
  rw [hZ] at h
  simpa using congrArg Subtype.val h

private lemma m4pow_mul_three_eq_one {L : Type*} [Group L]
    (hZ : Nat.card (Subgroup.center L) = 3) {y : L} {n : ℕ}
    (hy : y ^ n ∈ Subgroup.center L) : y ^ (n * 3) = 1 := by
  calc y ^ (n * 3) = (y ^ n) ^ 3 := pow_mul y n 3
    _ = 1 := m4pow_card_eq_one hZ hy

private lemma m4pow_mul_three_eq_one_of_map {L S : Type*} [Group L] [Group S]
    (φ : L →* S) (hker : φ.ker = Subgroup.center L)
    (hZ : Nat.card (Subgroup.center L) = 3) {y : L} {n : ℕ}
    (hy : (φ y) ^ n = 1) : y ^ (n * 3) = 1 := by
  refine m4pow_mul_three_eq_one hZ ?_
  rw [← hker, MonoidHom.mem_ker, map_pow, hy]

private lemma m4commutator_mul_center {X : Type*} [Group X] {k₁ k₂ z₁ z₂ : X}
    (hz₁ : z₁ ∈ Subgroup.center X) (hz₂ : z₂ ∈ Subgroup.center X) :
    ⁅k₁ * z₁, k₂ * z₂⁆ = ⁅k₁, k₂⁆ := by
  have hz₁c : ∀ x, Commute z₁ x := fun x => (Subgroup.mem_center_iff.1 hz₁ x).symm
  have hz₂c : ∀ x, Commute x z₂ := fun x => Subgroup.mem_center_iff.1 hz₂ x
  calc ⁅k₁ * z₁, k₂ * z₂⁆
      = k₁ * ⁅z₁, k₂ * z₂⁆ * k₁⁻¹ * ⁅k₁, k₂ * z₂⁆ :=
        commutatorElement_mul_left_eq_conj_mul k₁ z₁ (k₂ * z₂)
    _ = k₁ * 1 * k₁⁻¹ * ⁅k₁, k₂ * z₂⁆ := by
        rw [(hz₁c (k₂ * z₂)).commutator_eq]
    _ = k₁ * 1 * k₁⁻¹ * (⁅k₁, k₂⁆ * k₂ * ⁅k₁, z₂⁆ * k₂⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj]
    _ = ⁅k₁, k₂⁆ := by
        rw [(hz₂c k₁).commutator_eq]
        group

private lemma m4eq_top_of_mul_center {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    {K : Subgroup X} (h : ∀ x : X, ∃ k ∈ K, ∃ z ∈ Subgroup.center X, x = k * z) :
    K = ⊤ := by
  rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := h a
  obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := h b
  rw [m4commutator_mul_center hz₁ hz₂]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)

private theorem m4orderOf_two_zmod_thirteen : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem two_pow_four_le_index_of_witness {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ w : U, w * w = 1) {L S : Type} [Group L] [Finite L] [Group S] (φ : L →* S)
    (hφ : Function.Surjective φ) (hker : φ.ker = Subgroup.center L)
    (hZ : Nat.card (Subgroup.center L) = 3) (hperf : Group.IsPerfect L)
    (ρ : L →* MulAut U) (hρ : Function.Injective ρ) {ζ : L} (hζ : ζ ∈ Subgroup.center L)
    (hζ1 : ζ ≠ 1) (hfix : ∀ w : U, ρ ζ w = w → w = 1) (hcard : 2 ^ 54 ≤ Nat.card U)
    {t : L} (ht2 : t * t = 1) (hw : InvolutionWitness (φ t)) :
    2 ^ 4 ≤ (fixV (zpowers (ρ t))).index := by
  set d : ℕ := (fixV (Subgroup.zpowers (ρ t))).index with hd
  have hζ3 : ζ ^ 3 = 1 := m4pow_card_eq_one hZ hζ
  rcases hw with ⟨c, hc⟩ | ⟨c, g, hc, hg⟩ | ⟨cs, hlen, hcl⟩
  ·
    obtain ⟨h, hh⟩ := hφ c
    let t' : L := h * t * h⁻¹
    let y : L := t * t'
    let x : L := y ^ 3
    have ht'2 : t' * t' = 1 := by
      change (h * t * h⁻¹) * (h * t * h⁻¹) = 1
      calc (h * t * h⁻¹) * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
        _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
    have hφy : φ y = φ t * (c * φ t * c⁻¹) := by
      change φ (t * (h * t * h⁻¹)) = φ t * (c * φ t * c⁻¹)
      simp only [map_mul, map_inv, hh]
    have hordy : orderOf (φ y) = 13 := by rw [hφy]; exact hc
    have hφy13 : (φ y) ^ 13 = 1 := by rw [← hordy]; exact pow_orderOf_eq_one _
    have hy39 : y ^ 39 = 1 := by
      have h := m4pow_mul_three_eq_one_of_map φ hker hZ hφy13
      simpa using h
    have hx13 : x ^ 13 = 1 := by
      have h : x ^ 13 = y ^ 39 := by
        change (y ^ 3) ^ 13 = y ^ 39
        rw [← pow_mul]
      rw [h, hy39]
    have hx1 : x ≠ 1 := by
      intro hx
      have hφx : φ x = 1 := by rw [hx, map_one]
      have hxeq : φ x = (φ y) ^ 3 := by
        change φ (y ^ 3) = (φ y) ^ 3
        rw [map_pow]
      have h3 : (φ y) ^ 3 = 1 := by rw [← hxeq]; exact hφx
      have hdvd : 13 ∣ 3 := by
        have := orderOf_dvd_iff_pow_eq_one.2 h3
        rwa [hordy] at this
      norm_num at hdvd
    have hxord : orderOf x = 13 := by
      haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      exact orderOf_eq_prime hx13 hx1
    have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have ht'_inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
    have hty : t * y * t⁻¹ = y⁻¹ := by
      have hL : t * y * t⁻¹ = t' * t := by
        change t * (t * t') * t⁻¹ = t' * t
        calc t * (t * t') * t⁻¹ = (t * t) * t' * t⁻¹ := by group
          _ = t' * t⁻¹ := by rw [ht2, one_mul]
          _ = t' * t := by rw [ht_inv]
      have hR : y⁻¹ = t' * t := by
        change (t * t')⁻¹ = t' * t
        rw [mul_inv_rev, ht'_inv, ht_inv]
      rw [hL, hR]
    have htx : t * x * t⁻¹ = x⁻¹ := by
      change t * y ^ 3 * t⁻¹ = (y ^ 3)⁻¹
      rw [← conj_pow, hty, inv_pow]
    have ht2A : ρ t * ρ t = 1 := by rw [← map_mul, ht2, map_one]
    have hxordA : orderOf (ρ x) = 13 := by rw [orderOf_injective ρ hρ x, hxord]
    have hx13A : (ρ x) ^ 13 = 1 := by rw [← map_pow, hx13, map_one]
    have htxA : ρ t * ρ x * (ρ t)⁻¹ = (ρ x)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, htx, map_inv]
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have h12 : 2 ^ 12 ≤ (fixV (Subgroup.zpowers (ρ x))).index := by
      have h := CFSG.QuasithinUnique.Setup.X1.two_pow_orderOf_le_index_fixV hU
        (p := 13) (by norm_num) (g := ρ x) hxordA
      rwa [m4orderOf_two_zmod_thirteen] at h
    have hsq : (fixV (Subgroup.zpowers (ρ x))).index ≤ d ^ 2 :=
      index_fixV_le_sq_of_inverts (W := U) (p := 13) (by norm_num) hx13A ht2A htxA
    have h6 : 2 ^ 6 ≤ d := by
      by_contra hcon
      have hdlt : d < 2 ^ 6 := not_le.1 hcon
      have hlt : d ^ 2 < (2 ^ 6) ^ 2 := Nat.pow_lt_pow_left hdlt (by norm_num)
      have heq : (2 ^ 6) ^ 2 = 2 ^ 12 := by rw [← pow_mul]
      rw [heq] at hlt
      exact absurd hlt (not_lt.2 (h12.trans hsq))
    exact (by norm_num : (2 : ℕ) ^ 4 ≤ 2 ^ 6).trans h6
  ·
    obtain ⟨h, hh⟩ := hφ c
    obtain ⟨g', hg'⟩ := hφ g
    let t' : L := h * t * h⁻¹
    let y : L := t * t'
    let x : L := y ^ 3
    have ht'2 : t' * t' = 1 := by
      change (h * t * h⁻¹) * (h * t * h⁻¹) = 1
      calc (h * t * h⁻¹) * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
        _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
    have hφy : φ y = φ t * (c * φ t * c⁻¹) := by
      change φ (t * (h * t * h⁻¹)) = φ t * (c * φ t * c⁻¹)
      simp only [map_mul, map_inv, hh]
    have hordy : orderOf (φ y) = 5 := by rw [hφy]; exact hc
    have hφy5 : (φ y) ^ 5 = 1 := by rw [← hordy]; exact pow_orderOf_eq_one _
    have hy15 : y ^ 15 = 1 := by
      have h := m4pow_mul_three_eq_one_of_map φ hker hZ hφy5
      simpa using h
    have hx5 : x ^ 5 = 1 := by
      have h : x ^ 5 = y ^ 15 := by
        change (y ^ 3) ^ 5 = y ^ 15
        rw [← pow_mul]
      rw [h, hy15]
    have hx1 : x ≠ 1 := by
      intro hx
      have hφx : φ x = 1 := by rw [hx, map_one]
      have hxeq : φ x = (φ y) ^ 3 := by
        change φ (y ^ 3) = (φ y) ^ 3
        rw [map_pow]
      have h3 : (φ y) ^ 3 = 1 := by rw [← hxeq]; exact hφx
      have hdvd : 5 ∣ 3 := by
        have := orderOf_dvd_iff_pow_eq_one.2 h3
        rwa [hordy] at this
      norm_num at hdvd
    have hxord : orderOf x = 5 := by
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact orderOf_eq_prime hx5 hx1
    have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have ht'_inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
    have hty : t * y * t⁻¹ = y⁻¹ := by
      have hL : t * y * t⁻¹ = t' * t := by
        change t * (t * t') * t⁻¹ = t' * t
        calc t * (t * t') * t⁻¹ = (t * t) * t' * t⁻¹ := by group
          _ = t' * t⁻¹ := by rw [ht2, one_mul]
          _ = t' * t := by rw [ht_inv]
      have hR : y⁻¹ = t' * t := by
        change (t * t')⁻¹ = t' * t
        rw [mul_inv_rev, ht'_inv, ht_inv]
      rw [hL, hR]
    have htx : t * x * t⁻¹ = x⁻¹ := by
      change t * y ^ 3 * t⁻¹ = (y ^ 3)⁻¹
      rw [← conj_pow, hty, inv_pow]
    have hconjφ : φ (g' * y * g'⁻¹) = (φ y) ^ 2 := by
      calc φ (g' * y * g'⁻¹) = φ g' * φ y * (φ g')⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = g * (φ t * (c * φ t * c⁻¹)) * g⁻¹ := by rw [hg', hφy]
        _ = (φ t * (c * φ t * c⁻¹)) ^ 2 := hg
        _ = (φ y) ^ 2 := by rw [hφy]
    let k : L := (g' * y * g'⁻¹) * (y ^ 2)⁻¹
    have hkker : k ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      change φ ((g' * y * g'⁻¹) * (y ^ 2)⁻¹) = 1
      rw [map_mul, map_inv, map_pow, hconjφ, mul_inv_cancel]
    have hkcenter : k ∈ Subgroup.center L := by rw [← hker]; exact hkker
    have hk3 : k ^ 3 = 1 := m4pow_card_eq_one hZ hkcenter
    have hgy : g' * y * g'⁻¹ = k * y ^ 2 := by
      change g' * y * g'⁻¹ = ((g' * y * g'⁻¹) * (y ^ 2)⁻¹) * y ^ 2
      group
    have hgy2 : g' * x * g'⁻¹ = x ^ 2 := by
      have h1 : g' * x * g'⁻¹ = (g' * y * g'⁻¹) ^ 3 := by
        change g' * y ^ 3 * g'⁻¹ = (g' * y * g'⁻¹) ^ 3
        rw [← conj_pow]
      rw [h1, hgy]
      have hcomm : Commute k (y ^ 2) :=
        (show Commute k y from (Subgroup.mem_center_iff.1 hkcenter y).symm).pow_right 2
      rw [hcomm.mul_pow 3, hk3, one_mul, ← pow_mul]
      change y ^ (2 * 3) = (y ^ 3) ^ 2
      rw [← pow_mul]
    have ht2A : ρ t * ρ t = 1 := by rw [← map_mul, ht2, map_one]
    have htxA : ρ t * ρ x * (ρ t)⁻¹ = (ρ x)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, htx, map_inv]
    have hxζ : x * ζ = ζ * x := Subgroup.mem_center_iff.1 hζ x
    have hg'ζ : g' * ζ = ζ * g' := Subgroup.mem_center_iff.1 hζ g'
    have hω3 : (ρ ζ) ^ 3 = 1 := by rw [← map_pow, hζ3, map_one]
    have hu5 : (ρ x) ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
    have hu1 : ρ x ≠ 1 := by
      intro h
      exact hx1 (hρ (by rw [h, map_one]))
    have huω : ρ x * ρ ζ = ρ ζ * ρ x := by rw [← map_mul, ← map_mul, hxζ]
    have hgω : ρ g' * ρ ζ = ρ ζ * ρ g' := by rw [← map_mul, ← map_mul, hg'ζ]
    have hgA : ρ g' * ρ x * (ρ g')⁻¹ = (ρ x) ^ 2 := by
      rw [← map_inv, ← map_mul, ← map_mul, hgy2, map_pow]
    have h8 := two_pow_eight_le_index_of_conj_sq hU hω3 hfix hu5 hu1 huω hgω hgA
    have hsq : (fixV (Subgroup.zpowers (ρ x))).index ≤ d ^ 2 :=
      index_fixV_le_sq_of_inverts (W := U) (p := 5) (by norm_num) hu5 ht2A htxA
    have h4 : 2 ^ 4 ≤ d := by
      by_contra hcon
      have hdlt : d < 2 ^ 4 := not_le.1 hcon
      have hlt : d ^ 2 < (2 ^ 4) ^ 2 := Nat.pow_lt_pow_left hdlt (by norm_num)
      have heq : (2 ^ 4) ^ 2 = 2 ^ 8 := by rw [← pow_mul]
      rw [heq] at hlt
      exact absurd hlt (not_lt.2 (h8.trans hsq))
    exact h4
  ·
    let gs : List L := cs.map (fun c => Classical.choose (hφ c))
    have hgs_len : gs.length = cs.length := by simp [gs]
    have himg : φ '' {v : L | ∃ g ∈ gs, v = g * t * g⁻¹}
        = {v : S | ∃ c ∈ cs, v = c * φ t * c⁻¹} := by
      ext v
      constructor
      · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
        obtain ⟨c, hc, hgc⟩ := List.mem_map.1 hg
        refine ⟨c, hc, ?_⟩
        rw [← hgc]
        simp only [map_mul, map_inv, Classical.choose_spec (hφ c)]
      · rintro ⟨c, hc, rfl⟩
        refine ⟨Classical.choose (hφ c) * t * (Classical.choose (hφ c))⁻¹,
          ⟨Classical.choose (hφ c), List.mem_map.2 ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
        simp only [map_mul, map_inv, Classical.choose_spec (hφ c)]
    let K : Subgroup L := Subgroup.closure {v : L | ∃ g ∈ gs, v = g * t * g⁻¹}
    have hKmap : K.map φ = ⊤ := by
      change (Subgroup.closure {v : L | ∃ g ∈ gs, v = g * t * g⁻¹}).map φ = ⊤
      rw [MonoidHom.map_closure, himg, hcl]
    have hKtop : K = ⊤ := by
      refine m4eq_top_of_mul_center hperf ?_
      intro a
      have ha : φ a ∈ K.map φ := by rw [hKmap]; trivial
      rw [Subgroup.mem_map] at ha
      obtain ⟨k, hk, hka⟩ := ha
      refine ⟨k, hk, k⁻¹ * a, ?_, ?_⟩
      · rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hka, inv_mul_cancel]
      · group
    have himgρ : ρ '' {v : L | ∃ g ∈ gs, v = g * t * g⁻¹}
        = {v : MulAut U | ∃ h ∈ gs.map ρ, v = h * ρ t * h⁻¹} := by
      ext v
      constructor
      · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨ρ g, List.mem_map.2 ⟨g, hg, rfl⟩, by simp only [map_mul, map_inv]⟩
      · rintro ⟨h, hh, rfl⟩
        obtain ⟨g, hg, hgh⟩ := List.mem_map.1 hh
        refine ⟨g * t * g⁻¹, ⟨g, hg, rfl⟩, ?_⟩
        rw [← hgh]
        simp only [map_mul, map_inv]
    let Kρ : Subgroup (MulAut U) :=
      Subgroup.closure {v : MulAut U | ∃ h ∈ gs.map ρ, v = h * ρ t * h⁻¹}
    have hKρ : Kρ = K.map ρ := by
      change Subgroup.closure {v : MulAut U | ∃ h ∈ gs.map ρ, v = h * ρ t * h⁻¹}
        = (Subgroup.closure {v : L | ∃ g ∈ gs, v = g * t * g⁻¹}).map ρ
      rw [MonoidHom.map_closure, himgρ]
    have hKρ_range : Kρ = ρ.range := by rw [hKρ, hKtop, Subgroup.map_top]
    have hζKρ : ρ ζ ∈ Kρ := by rw [hKρ_range]; exact ⟨ζ, rfl⟩
    have hzpow_le : Subgroup.zpowers (ρ ζ) ≤ Kρ := Subgroup.zpowers_le.mpr hζKρ
    have hfixbot : fixV (Subgroup.zpowers (ρ ζ)) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_bot]
      exact hfix w ((CFSG.Quasithin.mem_fixV_zpowers_iff_apply).1 hw)
    have hfix_le : fixV Kρ ≤ fixV (Subgroup.zpowers (ρ ζ)) :=
      fun w hw x hx => hw x (hzpow_le hx)
    have hfixKρ : fixV Kρ = ⊥ := le_antisymm (hfix_le.trans_eq hfixbot) bot_le
    have hcardU : (fixV Kρ).index = Nat.card U := by rw [hfixKρ, Subgroup.index_bot]
    have hle : (fixV Kρ).index ≤ d ^ (gs.map ρ).length := by
      change (fixV (Subgroup.closure {y | ∃ h ∈ gs.map ρ, y = h * ρ t * h⁻¹})).index
        ≤ d ^ (gs.map ρ).length
      rw [hd]
      exact CFSG.Quasithin.B42Disp.index_fixV_closure_conj_elt_le (V := U) (ρ t) (gs.map ρ)
    have hlen6 : (gs.map ρ).length ≤ 6 := by
      simpa only [gs, List.length_map] using hlen
    have hdpos : 0 < d := by
      rw [hd, Subgroup.index_eq_card]
      exact Nat.card_pos
    have hpow : d ^ (gs.map ρ).length ≤ d ^ 6 := Nat.pow_le_pow_right hdpos hlen6
    have hcardle : Nat.card U ≤ d ^ 6 := by rw [← hcardU]; exact hle.trans hpow
    by_contra hcon
    have hdlt : d < 2 ^ 4 := not_le.1 hcon
    have hlt : d ^ 6 < (2 ^ 4) ^ 6 := Nat.pow_lt_pow_left hdlt (by norm_num)
    have heq : (2 ^ 4) ^ 6 = 2 ^ 24 := by rw [← pow_mul]
    rw [heq] at hlt
    have h24 : 2 ^ 24 < 2 ^ 54 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    exact absurd (hlt.trans h24) (not_lt.2 (hcard.trans hcardle))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
