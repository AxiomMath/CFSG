module

public import CFSG.Quasithin.Recognition.SzVBEvenCtx
public import CFSG.Quasithin.Recognition.SzVBOddL24Loc
public import CFSG.Quasithin.Recognition.Kleidman.VBEven.Coord

public section

namespace CFSG.Quasithin.Kleidman.VBEven

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.SzVB
open CFSG.LieType.BorelTits CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

omit [Finite G] in
theorem eq_one_of_conj_eq_one {ρ a : G} (h : ρ * a * ρ⁻¹ = 1) : a = 1 := by
  have e : a = ρ⁻¹ * (ρ * a * ρ⁻¹) * ρ := by group
  rw [e, h]; group

section Klein

variable (hV : IsElemAbelian 2 V) (hcard : Nat.card ↥V = 4) {ρ : G}
  (hρN : ρ ∈ Subgroup.normalizer (V : Set G)) (hρ3 : ρ ^ 3 = 1)

include hV hcard hρN hρ3

omit [Finite G] in
theorem conj_eq_of_fix {a : G} (ha : a ∈ V) (ha1 : a ≠ 1) (hfix : ρ * a * ρ⁻¹ = a) :
    ∀ v ∈ V, ρ * v * ρ⁻¹ = v := by
  obtain ⟨b, hb, hb1, hba⟩ := exists_klein_ne a hcard
  have hbV : ρ * b * ρ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hρN b).mp hb
  have haa : a * a = 1 := by rw [← pow_two]; exact isElemAbelian_pow_eq_one hV ha
  have hρba : ρ * (b * a) * ρ⁻¹ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) := by group
  rcases klein_cases hV hcard ha ha1 hb hb1 hba hbV with h | h | h | h
  · exact absurd (eq_one_of_conj_eq_one h) hb1
  · rw [← hfix] at h
    exact absurd (mul_left_cancel (mul_right_cancel h)) hba
  · intro v hv
    rcases klein_cases hV hcard ha ha1 hb hb1 hba hv with rfl | rfl | rfl | rfl
    · group
    · exact hfix
    · exact h
    · rw [hρba, h, hfix]
  · exfalso
    have h2 : ρ * (ρ * b * ρ⁻¹) * ρ⁻¹ = b := by
      rw [h, hρba, h, hfix, mul_assoc b a a, haa, mul_one]
    have hρ3' : ρ * (ρ * ρ) = 1 := by rw [← pow_three]; exact hρ3
    have h3 : ρ * (ρ * ρ) * b * (ρ * (ρ * ρ))⁻¹ = ρ * (ρ * (ρ * b * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ := by
      group
    rw [h2, h, hρ3'] at h3
    apply ha1
    have h4 : b * a = b * 1 := by rw [← h3]; group
    exact mul_left_cancel h4

omit [Finite G] in
theorem conj_conj_eq (hρf : ∀ v ∈ V, ρ * v * ρ⁻¹ = v → v = 1) {a : G} (ha : a ∈ V)
    (ha1 : a ≠ 1) : ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ = ρ * a * ρ⁻¹ * a := by
  have hbV : ρ * a * ρ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hρN a).mp ha
  have hb1 : ρ * a * ρ⁻¹ ≠ 1 := fun h => ha1 (eq_one_of_conj_eq_one h)
  have hba : ρ * a * ρ⁻¹ ≠ a := fun h => ha1 (hρf a ha h)
  have hcV : ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hρN _).mp hbV
  rcases klein_cases hV hcard ha ha1 hbV hb1 hba hcV with h | h | h | h
  · exact absurd (eq_one_of_conj_eq_one h) hb1
  · exfalso
    have hρ3' : ρ * (ρ * ρ) = 1 := by rw [← pow_three]; exact hρ3
    have h3 : ρ * (ρ * ρ) * a * (ρ * (ρ * ρ))⁻¹ = ρ * (ρ * (ρ * a * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ := by
      group
    rw [h, hρ3'] at h3
    apply hba
    rw [← h3]; group
  · exact absurd (hρf _ hbV h) hb1
  · exact h

end Klein

omit [Finite G] in
theorem klein_three_cases (hV : IsElemAbelian 2 V) (hcard : Nat.card ↥V = 4) {ρ σ : G}
    (hρN : ρ ∈ Subgroup.normalizer (V : Set G)) (hσN : σ ∈ Subgroup.normalizer (V : Set G))
    (hρ3 : ρ ^ 3 = 1) (hσ3 : σ ^ 3 = 1) (hρf : ∀ v ∈ V, ρ * v * ρ⁻¹ = v → v = 1)
    (hσf : ∀ v ∈ V, σ * v * σ⁻¹ = v → v = 1) :
    (∀ v ∈ V, σ * v * σ⁻¹ = ρ * v * ρ⁻¹) ∨ (∀ v ∈ V, σ * v * σ⁻¹ = ρ⁻¹ * v * ρ) := by
  obtain ⟨a, ha, ha1, -⟩ := exists_klein_ne (1 : G) hcard
  set b := ρ * a * ρ⁻¹ with hbdef
  have hbV : b ∈ V := (Subgroup.mem_normalizer_iff.mp hρN a).mp ha
  have hb1 : b ≠ 1 := fun h => ha1 (eq_one_of_conj_eq_one h)
  have hba : b ≠ a := fun h => ha1 (hρf a ha h)
  have haa : a * a = 1 := by rw [← pow_two]; exact isElemAbelian_pow_eq_one hV ha
  have hbb : b * b = 1 := by rw [← pow_two]; exact isElemAbelian_pow_eq_one hV hbV
  have hab : a * b = b * a := isElemAbelian_comm hV ha hbV
  have hρb : ρ * b * ρ⁻¹ = b * a := conj_conj_eq hV hcard hρN hρ3 hρf ha ha1
  have hρia : ρ⁻¹ * a * ρ = b * a := by
    have e : ρ * (b * a) * ρ⁻¹ = a := by
      calc ρ * (b * a) * ρ⁻¹ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) := by group
        _ = b * a * b := by rw [hρb, ← hbdef]
        _ = a := by rw [mul_assoc, hab, ← mul_assoc, hbb, one_mul]
    calc ρ⁻¹ * a * ρ = ρ⁻¹ * (ρ * (b * a) * ρ⁻¹) * ρ := by rw [e]
      _ = b * a := by group
  have hρib : ρ⁻¹ * b * ρ = a := by rw [hbdef]; group
  have hσa : σ * a * σ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hσN a).mp ha
  have hσa1 : σ * a * σ⁻¹ ≠ 1 := fun h => ha1 (eq_one_of_conj_eq_one h)
  have hσaa : σ * a * σ⁻¹ ≠ a := fun h => ha1 (hσf a ha h)
  have hσ2 := conj_conj_eq hV hcard hσN hσ3 hσf ha ha1
  have hext : ∀ c d : G, c * a * c⁻¹ = d * a * d⁻¹ → c * b * c⁻¹ = d * b * d⁻¹ →
      ∀ v ∈ V, c * v * c⁻¹ = d * v * d⁻¹ := by
    intro c d hca hcb v hv
    rcases klein_cases hV hcard ha ha1 hbV hb1 hba hv with rfl | rfl | rfl | rfl
    · group
    · exact hca
    · exact hcb
    · calc c * (b * a) * c⁻¹ = c * b * c⁻¹ * (c * a * c⁻¹) := by group
        _ = d * b * d⁻¹ * (d * a * d⁻¹) := by rw [hca, hcb]
        _ = d * (b * a) * d⁻¹ := by group
  rcases klein_cases hV hcard ha ha1 hbV hb1 hba hσa with h | h | h | h
  · exact absurd h hσa1
  · exact absurd h hσaa
  ·
    left
    refine hext σ ρ (h.trans hbdef) ?_
    rw [hρb]
    rw [h] at hσ2
    exact hσ2
  ·
    right
    have hσba : σ * (b * a) * σ⁻¹ = b := by
      have := hσ2
      rw [h, mul_assoc b a a, haa, mul_one] at this
      exact this
    have hfb : σ * b * σ⁻¹ = ρ⁻¹ * b * ρ⁻¹⁻¹ := by
      rw [inv_inv, hρib]
      calc σ * b * σ⁻¹ = σ * (b * a) * σ⁻¹ * (σ * a * σ⁻¹) := by
            rw [show σ * (b * a) * σ⁻¹ * (σ * a * σ⁻¹) = σ * (b * a * a) * σ⁻¹ by group,
              mul_assoc b a a, haa, mul_one]
        _ = b * (b * a) := by rw [hσba, h]
        _ = a := by rw [← mul_assoc, hbb, one_mul]
    have hfa : σ * a * σ⁻¹ = ρ⁻¹ * a * ρ⁻¹⁻¹ := by rw [inv_inv, h, hρia]
    intro v hv
    have := hext σ ρ⁻¹ hfa hfb v hv
    rwa [inv_inv] at this

theorem exists_fpf_three (hC : GeoCtx G₀ G₁ G₂ T V z) :
    ∃ ρ ∈ G₁, ρ ^ 3 = 1 ∧ ∀ v ∈ V, ρ * v * ρ⁻¹ = v → v = 1 := by
  have hyp := hC.hyp
  have h3' : (T.subgroupOf G₁).index = 3 := hC.index3
  have h3 : 3 ∣ Nat.card ↥G₁ := h3' ▸ Subgroup.index_dvd_card _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3 : (x : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  refine ⟨x, x.2, hx3, fun v hv hfix => ?_⟩
  by_contra hv1
  have hcent := conj_eq_of_fix hyp.elemAbelian hC.natS3.card_eq (hyp.normalizes x.2) hx3 hv hv1
    hfix
  have hxC : (x : G) ∈ G₁ ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := hcent w hw
    calc w * x = (x : G) * w * (x : G)⁻¹ * x := by rw [this]
      _ = x * w := by group
  have hxQ : (x : G) ∈ pCoreOf 2 G₁ := by
    rw [pCoreOf_eq_inf_centralizer hyp]
    exact ⟨inf_centralizer_le_T hyp hC.natS3 hC.index3 hxC, hxC.2⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 G₁ ⟨x, hxQ⟩
  have hk' : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h1 : (x : G) ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hk', hx3⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  exact hx1 h1

theorem exists_central_of_index_two (hC : GeoCtx G₀ G₁ G₂ T V z) {U : Subgroup G}
    (hUN : G₁ ≤ Subgroup.normalizer (U : Set G)) (_hVU : V ≤ U)
    (hQ : pCoreOf 2 G₁ ≤ Subgroup.centralizer (U : Set G)) (hU2 : IsElemAbelian 2 U)
    {s₀ : G} (hs₀ : s₀ ∈ U) (hs₀V : s₀ ∉ V) (hU : ∀ a ∈ U, a ∈ V ∨ a * s₀⁻¹ ∈ V) :
    ∃ s ∈ U, s ∉ V ∧ ∀ x ∈ G₁, x * s = s * x := by
  have hyp := hC.hyp
  have hN := hyp.normalizes
  have hVab := hyp.elemAbelian
  have hcard := hC.natS3.card_eq
  have hCQ : G₁ ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 G₁ := by
    rw [pCoreOf_eq_inf_centralizer hyp]
    exact le_inf (inf_centralizer_le_T hyp hC.natS3 hC.index3) inf_le_right
  obtain ⟨ρ, hρ, hρ3, hρf⟩ := exists_fpf_three hC
  have hρ3' : ρ * (ρ * ρ) = 1 := by rw [← pow_three]; exact hρ3
  have hconjU : ∀ x ∈ G₁, ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.mp (hUN hx) u).mp hu
  have hconjV : ∀ x ∈ G₁, ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (hN hx) v).mp hv
  have hout : ∀ x ∈ G₁, ∀ u : G, u ∉ V → x * u * x⁻¹ ∉ V := by
    intro x hx u huV h
    apply huV
    have h1 := hconjV x⁻¹ (G₁.inv_mem hx) _ h
    have e : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
    rwa [e] at h1
  have hcoset : ∀ u ∈ U, u ∉ V → u * s₀⁻¹ ∈ V := fun u hu huV =>
    (hU u hu).resolve_left huV
  have hdiff : ∀ u ∈ U, u ∉ V → ∀ u' ∈ U, u' ∉ V → u * u'⁻¹ ∈ V := by
    intro u hu huV u' hu' hu'V
    have e : u * u'⁻¹ = u * s₀⁻¹ * (u' * s₀⁻¹)⁻¹ := by group
    rw [e]
    exact V.mul_mem (hcoset u hu huV) (V.inv_mem (hcoset u' hu' hu'V))
  have huniq : ∀ u ∈ U, u ∉ V → ρ * u * ρ⁻¹ = u → ∀ u' ∈ U, u' ∉ V → ρ * u' * ρ⁻¹ = u' →
      u = u' := by
    intro u hu huV hfu u' hu' hu'V hfu'
    have h1 := hρf _ (hdiff u hu huV u' hu' hu'V) (by
      calc ρ * (u * u'⁻¹) * ρ⁻¹ = ρ * u * ρ⁻¹ * (ρ * u' * ρ⁻¹)⁻¹ := by group
        _ = u * u'⁻¹ := by rw [hfu, hfu'])
    exact mul_inv_eq_one.mp h1
  set s₁ := ρ * s₀ * ρ⁻¹ with hs₁
  set s₂ := ρ * s₁ * ρ⁻¹ with hs₂
  have hs₁U : s₁ ∈ U := hconjU ρ hρ s₀ hs₀
  have hs₂U : s₂ ∈ U := hconjU ρ hρ s₁ hs₁U
  have hs₁V : s₁ ∉ V := hout ρ hρ s₀ hs₀V
  have hs₂V : s₂ ∉ V := hout ρ hρ s₁ hs₁V
  have hρs₂ : ρ * s₂ * ρ⁻¹ = s₀ := by
    have e : ρ * s₂ * ρ⁻¹ = ρ * (ρ * ρ) * s₀ * (ρ * (ρ * ρ))⁻¹ := by rw [hs₂, hs₁]; group
    rw [e, hρ3']; group
  have hs₀s₀ : s₀ * s₀ = 1 := by rw [← pow_two]; exact isElemAbelian_pow_eq_one hU2 hs₀
  have hs₀inv : s₀⁻¹ = s₀ := inv_eq_of_mul_eq_one_right hs₀s₀
  have c1 : s₀ * s₁ = s₁ * s₀ := isElemAbelian_comm hU2 hs₀ hs₁U
  set s := s₀ * s₁ * s₂ with hsdef
  have hsU : s ∈ U := U.mul_mem (U.mul_mem hs₀ hs₁U) hs₂U
  have hss₀ : s * s₀⁻¹ ∈ V := by
    have e : s * s₀⁻¹ = s₁ * s₀⁻¹ * (s₂ * s₀⁻¹) := by
      rw [hsdef, hs₀inv, c1, mul_assoc (s₁ * s₀)]
    rw [e]
    exact V.mul_mem (hcoset s₁ hs₁U hs₁V) (hcoset s₂ hs₂U hs₂V)
  have hsV : s ∉ V := by
    intro h
    apply hs₀V
    have e : s₀ = (s * s₀⁻¹)⁻¹ * s := by group
    rw [e]
    exact V.mul_mem (V.inv_mem hss₀) h
  have hρs : ρ * s * ρ⁻¹ = s := by
    have e : ρ * s * ρ⁻¹ = s₁ * s₂ * (ρ * s₂ * ρ⁻¹) := by rw [hsdef, hs₂, hs₁]; group
    rw [e, hρs₂, hsdef, mul_assoc s₀, isElemAbelian_comm hU2 hs₀ (U.mul_mem hs₁U hs₂U)]
  refine ⟨s, hsU, hsV, fun x hx => ?_⟩
  set σ := x⁻¹ * ρ * x with hσdef
  have hσG : σ ∈ G₁ := G₁.mul_mem (G₁.mul_mem (G₁.inv_mem hx) hρ) hx
  have hσ3 : σ ^ 3 = 1 := by
    have e : σ * (σ * σ) = x⁻¹ * (ρ * (ρ * ρ)) * x := by rw [hσdef]; group
    rw [pow_three, e, hρ3']; group
  have hσf : ∀ v ∈ V, σ * v * σ⁻¹ = v → v = 1 := by
    intro v hv hfix
    have h1 : ρ * (x * v * x⁻¹) * ρ⁻¹ = x * v * x⁻¹ := by
      calc ρ * (x * v * x⁻¹) * ρ⁻¹ = x * (σ * v * σ⁻¹) * x⁻¹ := by rw [hσdef]; group
        _ = x * v * x⁻¹ := by rw [hfix]
    exact eq_one_of_conj_eq_one (hρf _ (hconjV x hx v hv) h1)
  have hcU : ∀ c ∈ G₁, (∀ v ∈ V, c * v * c⁻¹ = v) → c * s * c⁻¹ = s := by
    intro c hc hcv
    have hcC : c ∈ G₁ ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨hc, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have := hcv w hw
      calc w * c = c * w * c⁻¹ * c := by rw [this]
        _ = c * w := by group
    have h1 := Subgroup.mem_centralizer_iff.mp (hQ (hCQ hcC)) s hsU
    rw [← h1]; group
  have hσs : σ * s * σ⁻¹ = s := by
    rcases klein_three_cases hVab hcard (hN hρ) (hN hσG) hρ3 hσ3 hρf hσf with h | h
    ·
      have h1 := hcU (ρ⁻¹ * σ) (G₁.mul_mem (G₁.inv_mem hρ) hσG) fun v hv => by
        calc ρ⁻¹ * σ * v * (ρ⁻¹ * σ)⁻¹ = ρ⁻¹ * (σ * v * σ⁻¹) * ρ := by group
          _ = v := by rw [h v hv]; group
      calc σ * s * σ⁻¹ = ρ * (ρ⁻¹ * σ * s * (ρ⁻¹ * σ)⁻¹) * ρ⁻¹ := by group
        _ = s := by rw [h1, hρs]
    ·
      have h1 := hcU (ρ * σ) (G₁.mul_mem hρ hσG) fun v hv => by
        calc ρ * σ * v * (ρ * σ)⁻¹ = ρ * (σ * v * σ⁻¹) * ρ⁻¹ := by group
          _ = v := by rw [h v hv]; group
      have hρis : ρ⁻¹ * s * ρ = s := by
        calc ρ⁻¹ * s * ρ = ρ⁻¹ * (ρ * s * ρ⁻¹) * ρ := by rw [hρs]
          _ = s := by group
      calc σ * s * σ⁻¹ = ρ⁻¹ * (ρ * σ * s * (ρ * σ)⁻¹) * ρ := by group
        _ = s := by rw [h1, hρis]
  have hxs : ρ * (x * s * x⁻¹) * ρ⁻¹ = x * s * x⁻¹ := by
    calc ρ * (x * s * x⁻¹) * ρ⁻¹ = x * (σ * s * σ⁻¹) * x⁻¹ := by rw [hσdef]; group
      _ = x * s * x⁻¹ := by rw [hσs]
  have := huniq _ (hconjU x hx s hsU) (hout x hx s hsV) hxs s hsU hsV hρs
  calc x * s = x * s * x⁻¹ * x := by group
    _ = s * x := by rw [this]

section FalseOfCentral

open scoped Classical commutatorElement Pointwise symmDiff

omit [Finite G] in
theorem conj_of_mem_zpowers {g c : G} (hgz : g * z = z * g) (hc : c ∈ Subgroup.zpowers z) :
    g * c * g⁻¹ = c := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have : g * z * g⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hgz
  rw [← conj_zpow, this]

omit [Finite G] in
theorem commutator_le_centralizer {P : Subgroup G} {z s : G} (hcent : ∀ x ∈ P, x * z = z * x)
    (hcomm : ∀ g ∈ P, g * s * g⁻¹ * s⁻¹ ∈ Subgroup.zpowers z) :
    ⁅P, P⁆ ≤ Subgroup.centralizer {s} := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  let ε : ↥P →* ↥(Subgroup.zpowers z) :=
    { toFun := fun g => ⟨(g : G) * s * (g : G)⁻¹ * s⁻¹, hcomm g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ((a * b : ↥P) : G) * s * ((a * b : ↥P) : G)⁻¹ * s⁻¹ =
          ((a : G) * s * (a : G)⁻¹ * s⁻¹) * ((b : G) * s * (b : G)⁻¹ * s⁻¹)
        have hb := hcomm b b.2
        have ha := hcomm a a.2
        have hconj := conj_of_mem_zpowers (hcent a a.2) hb
        have hcm : ((a : G) * s * (a : G)⁻¹ * s⁻¹) * ((b : G) * s * (b : G)⁻¹ * s⁻¹) =
            ((b : G) * s * (b : G)⁻¹ * s⁻¹) * ((a : G) * s * (a : G)⁻¹ * s⁻¹) :=
          setLike_mul_comm ha hb
        have e1 : (b : G) * s * (b : G)⁻¹ = ((b : G) * s * (b : G)⁻¹ * s⁻¹) * s := by group
        calc ((a * b : ↥P) : G) * s * ((a * b : ↥P) : G)⁻¹ * s⁻¹
            = (a : G) * ((b : G) * s * (b : G)⁻¹) * (a : G)⁻¹ * s⁻¹ := by
              simp only [Subgroup.coe_mul, mul_inv_rev]; group
          _ = (a : G) * (((b : G) * s * (b : G)⁻¹ * s⁻¹) * s) * (a : G)⁻¹ * s⁻¹ := by rw [← e1]
          _ = ((a : G) * ((b : G) * s * (b : G)⁻¹ * s⁻¹) * (a : G)⁻¹) *
                ((a : G) * s * (a : G)⁻¹ * s⁻¹) := by group
          _ = ((b : G) * s * (b : G)⁻¹ * s⁻¹) * ((a : G) * s * (a : G)⁻¹ * s⁻¹) := by rw [hconj]
          _ = ((a : G) * s * (a : G)⁻¹ * s⁻¹) * ((b : G) * s * (b : G)⁻¹ * s⁻¹) :=
              hcm.symm) }
  have key : ε ⁅(⟨g, hg⟩ : ↥P), (⟨h, hh⟩ : ↥P)⁆ = 1 :=
    by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (IsMulCommutative.is_comm.comm _ _)
  have h1 := congrArg Subtype.val key
  simp only [ε, MonoidHom.coe_mk, OneHom.coe_mk, commutatorElement_def, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_one] at h1
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have h2 : ⁅g, h⁆ * y * ⁅g, h⁆⁻¹ = y := by
    have := mul_inv_eq_one.mp h1
    exact this
  calc y * ⁅g, h⁆ = ⁅g, h⁆ * y * ⁅g, h⁆⁻¹ * ⁅g, h⁆ := by
        rw [h2]
    _ = ⁅g, h⁆ * y := by group

theorem false_of_central (hC : GeoCtx G₀ G₁ G₂ T V z) (F : A5Facts G₂ T V z) {s : G}
    (hs : s ∈ conjClosure V G₂) (hsV : s ∉ V) (hs1 : ∀ x ∈ G₁, x * s = s * x)
    (hq : ∃ q ∈ pCoreOf 2 G₂, ∃ k ∈ G₂, conjSub k V ≠ V ∧
      q ∈ Subgroup.centralizer (conjSub k V : Set G) ∧ q ∉ Subgroup.centralizer (V : Set G)) :
    False := by
  obtain ⟨E⟩ := exists_frame F
  have hTG1 : T ≤ G₁ := hC.hyp.sylow₁.1
  have hQT : pCoreOf 2 G₂ ≤ T := F7.isSylowTwoOf_pCoreOf_le hC.hyp.sylow₂
  have hzV : z ∈ V := F.klein.z_mem
  have hWG2 : conjClosure V G₂ ≤ G₂ :=
    conjClosure_le fun h hh v hv => G₂.mul_mem (G₂.mul_mem hh (F.klein.V_le hv)) (G₂.inv_mem hh)
  have hzW : z ∈ conjClosure V G₂ := E.tdata.z_mem
  obtain ⟨I, c, hc, hsI⟩ : ∃ (I : Finset (ConjSet G₂ V)) (c : G), (c = 1 ∨ c = z) ∧
      s = E.prod I * c := by
    obtain ⟨I, hI⟩ := E.exists_of_mem hs
    rcases hI with h | h
    · exact ⟨I, 1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨I, z, Or.inr rfl, h⟩
  have hcc : c * c = 1 := by
    rcases hc with h | h
    · rw [h, mul_one]
    · rw [h]; exact E.tdata.z_sq
  have hcW : c ∈ conjClosure V G₂ := by
    rcases hc with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hzW
  have hcg : ∀ g ∈ G₂, g * c * g⁻¹ = c := by
    intro g hg
    rcases hc with h | h
    · rw [h]; group
    · rw [h]; exact mul_inv_eq_iff_eq_mul.mpr (F.klein.z_cent g hg)
  have hprod : E.prod I = s * c := by
    rw [hsI, mul_assoc, hcc, mul_one]
  have hinv : ∀ g : ↥G₂, (g : G) ∈ T → g • I = I := by
    intro g hg
    refine E.smul_eq_of_conj F g (Or.inl ?_)
    have hgs : (g : G) * s * (g : G)⁻¹ = s := mul_inv_eq_iff_eq_mul.mpr (hs1 g (hTG1 hg))
    calc (g : G) * E.prod I * (g : G)⁻¹ = ((g : G) * s * (g : G)⁻¹) * ((g : G) * c * (g : G)⁻¹) := by
          rw [hprod]; group
      _ = E.prod I := by rw [hgs, hcg g g.2, hprod]
  rcases T_invariant_cases F hinv with h | h | h | h
  ·
    apply hsV
    rw [hsI, h, E.prod_empty, one_mul]
    rcases hc with h' | h'
    · rw [h']; exact V.one_mem
    · rw [h']; exact hzV
  ·
    apply hsV
    rw [hsI, h, E.prod_singleton]
    refine V.mul_mem (E.mem (ConjSet.base G₂ V)) ?_
    rcases hc with h' | h'
    · rw [h']; exact V.one_mem
    · rw [h']; exact hzV
  ·
    have : Fintype (ConjSet G₂ V) := Fintype.ofFinite _
    obtain ⟨q, hqO, k, hk, hkV, hqk, hqV⟩ := hq
    have hq2 : q ∈ G₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hqO
    have hqs : q * s = s * q := hs1 q (hTG1 (hQT hqO))
    have hqs' : q * (k * s * k⁻¹) = (k * s * k⁻¹) * q := by
      have h1 : k⁻¹ * q * k⁻¹⁻¹ ∈ pCoreOf 2 G₂ :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ (G₂.inv_mem hk)) q).mp hqO
      have h2 := hs1 _ (hTG1 (hQT h1))
      calc q * (k * s * k⁻¹) = k * ((k⁻¹ * q * k⁻¹⁻¹) * s) * k⁻¹ := by group
        _ = k * (s * (k⁻¹ * q * k⁻¹⁻¹)) * k⁻¹ := by rw [h2]
        _ = (k * s * k⁻¹) * q := by group
    let kk : ↥G₂ := ⟨k, hk⟩
    set o := ConjSet.base G₂ V with ho
    let lam : ConjSet G₂ V := kk • o
    have hlam : lam ≠ o := fun hh => hkV (congrArg Subtype.val hh)
    have hIe : I = Finset.univ.erase o := by
      ext a
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact h a
    have hJe : kk • I = Finset.univ.erase lam := by
      rw [hIe]
      ext x
      simp only [Finset.mem_smul_finset, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨a, hao, rfl⟩ hh
        exact hao (MulAction.injective kk hh)
      · intro hx
        refine ⟨kk⁻¹ • x, fun hh => hx ?_, by simp [smul_smul]⟩
        show x = kk • o
        calc x = kk • (kk⁻¹ • x) := by simp [smul_smul]
          _ = kk • o := by rw [hh]
    obtain ⟨ε, hε, hke⟩ := E.conj_prod kk I
    rw [hJe] at hke
    have hεW : ε ∈ conjClosure V G₂ := by
      rcases hε with h' | h'
      · rw [h']; exact one_mem _
      · rw [h']; exact hzW
    have hεz : q * ε = ε * q := by
      rcases hε with h' | h'
      · rw [h']; simp
      · rw [h']; exact F.klein.z_cent q hq2
    have hs' : k * s * k⁻¹ = E.prod (Finset.univ.erase lam) * ε * c := by
      calc k * s * k⁻¹ = (k * E.prod I * k⁻¹) * (k * c * k⁻¹) := by rw [hsI]; group
        _ = E.prod (Finset.univ.erase lam) * ε * c := by rw [hke, hcg k hk]
    have hsym : I ∆ (Finset.univ.erase lam) = {o} ∆ {lam} := by
      rw [hIe]
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_singleton]
      by_cases hx : x = o <;> by_cases hy : x = lam <;> simp [hx, hy, hlam, hlam.symm]
    have hprod' : E.prod {o} * E.prod {lam} = E.prod I * E.prod (Finset.univ.erase lam) := by
      rw [E.prod_mul, E.prod_mul, hsym]
    have hBε : E.prod (Finset.univ.erase lam) * ε ∈ conjClosure V G₂ :=
      Subgroup.mul_mem _ (E.prod_mem _) hεW
    have hss' : s * (k * s * k⁻¹) = (E.t o * E.t lam) * ε := by
      rw [hs', hsI, ← E.prod_singleton o, ← E.prod_singleton lam, hprod']
      calc E.prod I * c * (E.prod (Finset.univ.erase lam) * ε * c)
          = E.prod I * (c * (E.prod (Finset.univ.erase lam) * ε)) * c := by group
        _ = E.prod I * ((E.prod (Finset.univ.erase lam) * ε) * c) * c := by
            rw [E.comm hcW hBε]
        _ = E.prod I * E.prod (Finset.univ.erase lam) * ε * (c * c) := by group
        _ = E.prod I * E.prod (Finset.univ.erase lam) * ε := by rw [hcc, mul_one]
    have hqtot : Commute q (s * (k * s * k⁻¹)) :=
      (show Commute q s from hqs).mul_right (show Commute q (k * s * k⁻¹) from hqs')
    rw [hss'] at hqtot
    have hqm : Commute q (E.t o * E.t lam) := by
      have h3 := hqtot.mul_right (show Commute q ε from hεz).inv_right
      rwa [mul_inv_cancel_right] at h3
    have hqtl : Commute q (E.t lam) := by
      have : E.t lam * q = q * E.t lam := hqk (E.t lam) (E.mem lam)
      exact this.symm
    have hqto : Commute q (E.t o) := by
      have := hqm.mul_right hqtl.inv_right
      simpa using this
    apply hqV
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases E.V_cases F.klein hv with rfl | rfl | rfl | rfl
    · simp
    · exact (F.klein.z_cent q hq2).symm
    · exact hqto.eq.symm
    · calc E.t o * z * q = E.t o * (z * q) := mul_assoc _ _ _
        _ = E.t o * (q * z) := by rw [F.klein.z_cent q hq2]
        _ = (E.t o * q) * z := (mul_assoc _ _ _).symm
        _ = (q * E.t o) * z := by rw [hqto.eq]
        _ = q * (E.t o * z) := mul_assoc _ _ _
  ·
    have : Fintype (ConjSet G₂ V) := Fintype.ofFinite _
    have hIu : I = Finset.univ := Finset.eq_univ_of_forall h
    have hcomm : ∀ g ∈ G₂, g * s * g⁻¹ * s⁻¹ ∈ Subgroup.zpowers z := by
      intro g hg
      obtain ⟨ε, hε, he⟩ := E.conj_prod ⟨g, hg⟩ I
      have hgI : (⟨g, hg⟩ : ↥G₂) • I = I := by
        rw [hIu]
        ext x
        simp only [Finset.mem_smul_finset, Finset.mem_univ, true_and, iff_true]
        exact ⟨(⟨g, hg⟩ : ↥G₂)⁻¹ • x, by simp [smul_smul]⟩
      rw [hgI] at he
      have hεW : ε ∈ conjClosure V G₂ := by
        rcases hε with h' | h'
        · rw [h']; exact one_mem _
        · rw [h']; exact hzW
      have hgs : g * s * g⁻¹ = ε * s := by
        calc g * s * g⁻¹ = (g * E.prod I * g⁻¹) * (g * c * g⁻¹) := by rw [hsI]; group
          _ = E.prod I * ε * c := by rw [he, hcg g hg]
          _ = ε * E.prod I * c := by rw [E.comm (E.prod_mem I) hεW]
          _ = ε * (E.prod I * c) := mul_assoc _ _ _
          _ = ε * s := by rw [hsI]
      rw [hgs, mul_assoc, mul_inv_cancel, mul_one]
      rcases hε with h' | h'
      · rw [h']; exact Subgroup.one_mem _
      · rw [h']; exact Subgroup.mem_zpowers z
    have hcl := commutator_le_centralizer F.klein.z_cent hcomm
    have hcentr : ∀ x ∈ G₁, x ∈ Subgroup.centralizer {s} := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hs1 x hx).symm
    have hG2 : G₂ ≤ Subgroup.centralizer {s} :=
      F.perfect.trans (sup_le hcl fun x hx => hcentr x (hTG1 (hQT hx)))
    have hG0 : G₀ ≤ Subgroup.centralizer {s} := by
      rw [hC.hyp.gen]
      exact sup_le (fun x hx => hcentr x hx) hG2
    have hG2G0 : G₂ ≤ G₀ := by rw [hC.hyp.gen]; exact le_sup_right
    have hcomm' : ∀ x ∈ G₀, x * s = s * x := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hG0 hx) s (Set.mem_singleton s)).symm
    have hp : IsPGroup 2 ↥(Subgroup.zpowers s) :=
      (isPGroup_of_isElemAbelian F.abel).to_le (Subgroup.zpowers_le.mpr hs)
    have hle : Subgroup.zpowers s ≤ pCoreOf 2 G₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (Subgroup.zpowers_le.mpr (hG2G0 (hWG2 hs))) (fun x hx => by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hy
            rw [conj_of_mem_zpowers (hcomm' x hx) hy]
            exact hy
          · intro hy
            have := conj_of_mem_zpowers (hcomm' x⁻¹ (G₀.inv_mem hx)) hy
            have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
            rw [e] at this
            rw [this]
            exact hy) hp
    have hs0 : s ∈ pCoreOf 2 G₀ := hle (Subgroup.mem_zpowers s)
    rw [hC.hyp.o2_trivial, Subgroup.mem_bot] at hs0
    apply hsV
    rw [hs0]
    exact V.one_mem

end FalseOfCentral

end CFSG.Quasithin.Kleidman.VBEven
