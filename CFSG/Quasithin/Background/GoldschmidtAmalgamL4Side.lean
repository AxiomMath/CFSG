module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Rel

public section

namespace CFSG.Quasithin.F6.GoldAmL4

variable {D : Type*} [Group D]

theorem exists_B_elem {a b s : D} (hT : TRel a b s)
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32) {G : Subgroup D}
    (hTG : Subgroup.closure ({a, b, s} : Set D) ≤ G)
    (hGQ : ∀ g ∈ G, ∀ q ∈ m2Sub.map hT.emb, g * q * g⁻¹ ∈ m2Sub.map hT.emb)
    (hC : ∀ g ∈ G, (∀ q ∈ m2Sub.map hT.emb, g * q = q * g) → g ∈ m2Sub.map hT.emb)
    {y' : D} (hy'G : y' ∈ G) (hy'3 : y' ^ 3 = 1) (hy'1 : y' ≠ 1) :
    ∃ y ∈ G, BRel a b s y := by
  have hinj := hT.emb_injective hcard
  set Q : Subgroup D := m2Sub.map hT.emb with hQ
  have hrange : hT.emb.range = Subgroup.closure ({a, b, s} : Set D) := hT.emb_range
  have hmemT : ∀ w : Tc, hT.emb w ∈ G := fun w => hTG (hrange ▸ ⟨w, rfl⟩)
  have hQ_mem : ∀ w ∈ m2Sub, hT.emb w ∈ Q := fun w hw => Subgroup.mem_map_of_mem _ hw
  have hQ_inv : ∀ q ∈ Q, ∃ w ∈ m2Sub, hT.emb w = q := fun q hq => Subgroup.mem_map.mp hq
  have hQT : ∀ q ∈ Q, q ∈ hT.emb.range := fun q hq => by
    obtain ⟨w, _, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨w, rfl⟩
  have hcoord : ∀ w : Tc, hT.coord (hT.emb w) = w := hT.coord_emb hinj
  let f : Tc → Tc := fun w => hT.coord (y'⁻¹ * hT.emb w * y')
  have hf_emb : ∀ w ∈ m2Sub, f w ∈ m2Sub ∧ hT.emb (f w) = y'⁻¹ * hT.emb w * y' := by
    intro w hw
    have h1 : y'⁻¹ * hT.emb w * y' ∈ Q := by
      have := hGQ y'⁻¹ (G.inv_mem hy'G) (hT.emb w) (hQ_mem w hw)
      simpa using this
    obtain ⟨w₁, hw₁, hw₁e⟩ := hQ_inv _ h1
    have hfw : f w = w₁ := by
      show hT.coord (y'⁻¹ * hT.emb w * y') = w₁
      rw [← hw₁e, hcoord]
    exact ⟨hfw ▸ hw₁, by rw [hfw, hw₁e]⟩
  have hf : HomOn f := by
    refine ⟨?_, fun w hw => (hf_emb w hw).1, ?_⟩
    · show hT.coord (y'⁻¹ * hT.emb 1 * y') = 1
      rw [map_one, mul_one, inv_mul_cancel]
      have := hcoord 1
      rwa [map_one] at this
    · intro x hx y hy
      apply hinj
      rw [(hf_emb (x * y) (m2Sub.mul_mem hx hy)).2, map_mul, map_mul, (hf_emb x hx).2,
        (hf_emb y hy).2]
      group
  have h3 : ∀ x ∈ m2Sub, f (f (f x)) = x := by
    intro x hx
    apply hinj
    have e1 := hf_emb x hx
    have e2 := hf_emb (f x) e1.1
    have e3 := hf_emb (f (f x)) e2.1
    rw [e3.2, e2.2, e1.2]
    have hy3' : y' * y' * y' = 1 := by
      rw [← pow_three']; exact hy'3
    calc y'⁻¹ * (y'⁻¹ * (y'⁻¹ * hT.emb x * y') * y') * y'
        = (y' * y' * y')⁻¹ * hT.emb x * (y' * y' * y') := by group
      _ = hT.emb x := by rw [hy3', inv_one, one_mul, mul_one]
  have hne : ¬ (f tC = tC ∧ f tP = tP ∧ f tS = tS) := by
    rintro ⟨h1, h2, h3'⟩
    have hid : ∀ w ∈ m2Sub, f w = w := by
      intro w hw
      rw [hf.eq_Fu hw, h1, h2, h3']
      exact Fu_id w hw
    have hcent : ∀ q ∈ Q, y' * q = q * y' := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hQ_inv q hq
      have := (hf_emb w hw).2
      rw [hid w hw] at this
      calc y' * hT.emb w = y' * (y'⁻¹ * hT.emb w * y') := by rw [← this]
        _ = hT.emb w * y' := by group
    have hyQ : y' ∈ Q := hC y' hy'G hcent
    have hyT : y' ∈ Subgroup.closure ({a, b, s} : Set D) := by
      rw [← hrange]; exact hQT y' hyQ
    exact hy'1 (hT.eq_one_of_pow_three hy'3 hyT)
  obtain ⟨t, ht1, ht2, ht3⟩ := classify_B hf h3 hne
  obtain ⟨y, hy⟩ : ∃ y : D, y = hT.emb t * y' * (hT.emb t)⁻¹ := ⟨_, rfl⟩
  have hyG : y ∈ G := by
    rw [hy]; exact G.mul_mem (G.mul_mem (hmemT t) hy'G) (G.inv_mem (hmemT t))
  have hy3 : y ^ 3 = 1 := by
    have e : y ^ 3 = hT.emb t * y' ^ 3 * (hT.emb t)⁻¹ := by
      rw [hy]; simp only [pow_three']; group
    rw [e, hy'3]; group
  have hconj : ∀ g ∈ m2Sub, y⁻¹ * hT.emb g * y = hT.emb (t * f (t⁻¹ * g * t) * t⁻¹) := by
    intro g hg
    have hg' : t⁻¹ * g * t ∈ m2Sub := by simpa using m2_normal t⁻¹ g hg
    have e := (hf_emb _ hg').2
    simp only [map_mul, map_inv]
    simp only [map_mul, map_inv] at e
    rw [e, hy]
    group
  have hyc : y⁻¹ * (a * b) * y = a * b := by
    have h1 := hconj tC tC_mem
    rw [ht1, hT.emb_tC] at h1
    exact h1
  have hyp : y⁻¹ * (a * a) * y = s := by
    have h1 := hconj tP tP_mem
    rw [ht2, hT.emb_tP, hT.emb_tS] at h1
    exact h1
  have hyq : y⁻¹ * s * y = a * b⁻¹ * s := by
    have h1 := hconj tS tS_mem
    rw [ht3, hT.emb_tS, hT.emb_alpha] at h1
    exact h1
  have hBc : BConj a b s y := ⟨hT, hy3, hyc, hyp, hyq⟩
  have hcj : ∀ w ∈ m2Sub, y⁻¹ * hT.emb w * y = hT.emb (Fu alpha0 w) := hBc.conj_emb
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : D, t₀ = hT.emb tT0 := ⟨_, rfl⟩
  have ht₀G : t₀ ∈ G := by rw [ht₀]; exact hmemT tT0
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : D, y₂ = t₀ * y * t₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : D, z = y₂ * y := ⟨_, rfl⟩
  have hzG : z ∈ G := by
    rw [hz, hy₂]
    exact G.mul_mem (G.mul_mem (G.mul_mem ht₀G hyG) (G.inv_mem ht₀G)) hyG
  have hzc : ∀ w ∈ m2Sub, z⁻¹ * hT.emb w * z = hT.emb w := by
    intro w hw
    have hw' : tT0⁻¹ * w * tT0 ∈ m2Sub := by simpa using m2_normal tT0⁻¹ w hw
    have e1 : y⁻¹ * hT.emb (tT0⁻¹ * w * tT0) * y = hT.emb (Fu alpha0 (tT0⁻¹ * w * tT0)) :=
      hcj _ hw'
    have hw1 : Fu alpha0 (tT0⁻¹ * w * tT0) ∈ m2Sub := Fu_alpha0_mem _ hw'
    have hw2 : tT0 * Fu alpha0 (tT0⁻¹ * w * tT0) * tT0⁻¹ ∈ m2Sub := m2_normal tT0 _ hw1
    have e2 : y⁻¹ * hT.emb (tT0 * Fu alpha0 (tT0⁻¹ * w * tT0) * tT0⁻¹) * y = hT.emb w := by
      rw [hcj _ hw2, alpha0_inverted w hw]
    have e3 : t₀⁻¹ * hT.emb w * t₀ = hT.emb (tT0⁻¹ * w * tT0) := by
      rw [ht₀]; simp only [map_mul, map_inv]
    have e4 : t₀ * hT.emb (Fu alpha0 (tT0⁻¹ * w * tT0)) * t₀⁻¹ =
        hT.emb (tT0 * Fu alpha0 (tT0⁻¹ * w * tT0) * tT0⁻¹) := by
      rw [ht₀]; simp only [map_mul, map_inv]
    calc z⁻¹ * hT.emb w * z
        = y⁻¹ * (t₀ * (y⁻¹ * (t₀⁻¹ * hT.emb w * t₀) * y) * t₀⁻¹) * y := by
          rw [hz, hy₂]; group
      _ = hT.emb w := by rw [e3, e1, e4, e2]
  have hzcent : ∀ q ∈ Q, z * q = q * z := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := hQ_inv q hq
    calc z * hT.emb w = z * (z⁻¹ * hT.emb w * z) := by rw [hzc w hw]
      _ = hT.emb w * z := by group
  have hzQ : z ∈ Q := hC z hzG hzcent
  obtain ⟨wz, hwz, hwze⟩ := hQ_inv z hzQ
  have hwzc : ∀ v ∈ m2Sub, wz * v = v * wz := by
    intro v hv
    apply hinj
    rw [map_mul, map_mul, hwze]
    exact hzcent _ (hQ_mem v hv)
  obtain ⟨k, hk⟩ := m2_center wz hwz hwzc
  have hzk : z = (a * b) ^ k.val := by
    rw [← hwze, hk, map_pow, hT.emb_tC]
  have hyz : y⁻¹ * z * y = z := by
    rw [hzk]
    have := conj_pow (a := y⁻¹) (b := a * b) (i := k.val)
    simp only [inv_inv] at this
    rw [← this, hyc]
  have hy₂3 : y₂ ^ 3 = 1 := by
    have e : y₂ ^ 3 = t₀ * y ^ 3 * t₀⁻¹ := by
      rw [hy₂]; simp only [pow_three']; group
    rw [e, hy3]; group
  have hy₂z : y₂ = z * y⁻¹ := by rw [hz]; group
  have hzy : z * y = y * z := by
    calc z * y = y * (y⁻¹ * z * y) := by group
      _ = y * z := by rw [hyz]
  have hz3 : z ^ 3 = 1 := by
    have h1 : (z * y⁻¹) ^ 3 = 1 := by rw [← hy₂z]; exact hy₂3
    have hc : Commute z y⁻¹ := (Commute.inv_right (show Commute z y from hzy))
    rw [hc.mul_pow, inv_pow, hy3, inv_one, mul_one] at h1
    exact h1
  have hz4 : z ^ 4 = 1 := by
    rw [hzk, ← pow_mul, mul_comm, pow_mul]
    have : (a * b) ^ 4 = 1 := by
      rw [← hT.emb_tC, ← map_pow, tC_pow_four, map_one]
    rw [this, one_pow]
  have hz1 : z = 1 := by
    calc z = z ^ 4 * (z ^ 3)⁻¹ := by group
      _ = 1 := by rw [hz4, hz3]; simp
  have hy₂y : y₂ = y⁻¹ := by
    have : y₂ * y = 1 := by rw [← hz]; exact hz1
    exact eq_inv_of_mul_eq_one_left this
  have hyt : y * (s * a) * y = s * a := by
    have e : t₀ * y = y⁻¹ * t₀ := by
      calc t₀ * y = (t₀ * y * t₀⁻¹) * t₀ := by group
        _ = y⁻¹ * t₀ := by rw [← hy₂, hy₂y]
    have ht₀' : t₀ = s * a := by rw [ht₀, hT.emb_tT0]
    rw [← ht₀']
    calc y * t₀ * y = y * (t₀ * y) := by group
      _ = t₀ := by rw [e]; group
  exact ⟨y, hyG, ⟨hBc, hyt⟩⟩

end CFSG.Quasithin.F6.GoldAmL4
