module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Rel
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Label

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.F6.GoldAmL

variable {D : Type*} [Group D]

theorem mem_normalizer_of_cube {N : Subgroup D} {y : D} (hy3 : y ^ 3 = 1)
    (h : ∀ n ∈ N, y⁻¹ * n * y ∈ N) : y ∈ Subgroup.normalizer (N : Set D) := by
  have hy3' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have := h _ (h n hn)
    have e : y⁻¹ * (y⁻¹ * n * y) * y = y * n * y⁻¹ := by
      calc y⁻¹ * (y⁻¹ * n * y) * y = (y * y)⁻¹ * n * (y * y) := by group
        _ = y * n * y⁻¹ := by
          have : y * y = y⁻¹ := by
            rw [eq_inv_iff_mul_eq_one]; exact hy3'
          rw [this]; group
    rwa [e] at this
  · intro hn
    have := h _ hn
    have e : y⁻¹ * (y * n * y⁻¹) * y = n := by group
    rwa [e] at this

theorem mem_normalizer_of_both {N : Subgroup D} {g : D} (h1 : ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, g⁻¹ * n * g ∈ N) : g ∈ Subgroup.normalizer (N : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact h1 n
  · intro hn
    have := h2 _ hn
    have e : g⁻¹ * (g * n * g⁻¹) * g = n := by group
    rwa [e] at this

theorem range_le_normalizer_N {a b s ρ : D} (hT : TRel a b s) (hR : RhoRel a b s ρ) :
    (embR hT hR).range ≤ Subgroup.normalizer ((Nr.map (embR hT hR) : Subgroup D) : Set D) := by
  rintro _ ⟨w, rfl⟩
  refine mem_normalizer_of_both (fun n hn => ?_) (fun n hn => ?_)
  · obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hn
    have : embR hT hR w * embR hT hR g * (embR hT hR w)⁻¹ = embR hT hR (w * g * w⁻¹) := by
      simp only [map_mul, map_inv]
    rw [this]
    exact Subgroup.mem_map_of_mem _ (N_normal w g hg)
  · obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hn
    have : (embR hT hR w)⁻¹ * embR hT hR g * embR hT hR w = embR hT hR (w⁻¹ * g * w) := by
      simp only [map_mul, map_inv]
    rw [this]
    have := N_normal w⁻¹ g hg
    simp only [inv_inv] at this
    exact Subgroup.mem_map_of_mem _ this

theorem aRho_normalizes_N {a b s x ρ : D} (hA : ARel a b s x) (hAρ : ARho a b s x ρ) :
    x ∈ Subgroup.normalizer ((Nr.map (embR hA.toTRel hAρ.toRhoRel) : Subgroup D) : Set D) := by
  refine mem_normalizer_of_cube hA.hx ?_
  intro n hn
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hn
  rw [aRho_conj_embR hA hAρ g (N_le_Q1 g hg)]
  exact Subgroup.mem_map_of_mem _ (actA_N g hg)

theorem exists_B_elem5 {a b s ρ : D} (hT : TRel a b s) (hR : RhoRel a b s ρ)
    (hcard : Nat.card (Subgroup.closure ({a, b, s, ρ} : Set D)) = 64) {G : Subgroup D}
    (hv : Vertex G (Subgroup.closure ({a, b, s, ρ} : Set D)))
    (hGQ : ∀ g ∈ G, ∀ q ∈ Q2r.map (embR hT hR), g * q * g⁻¹ ∈ Q2r.map (embR hT hR))
    (hC : ∀ g ∈ G, (∀ q ∈ Q2r.map (embR hT hR), g * q = q * g) → g ∈ Q2r.map (embR hT hR))
    (hfpf : ∀ g ∈ G, g ≠ 1 → g ^ 3 = 1 → ∀ q ∈ Q2r.map (embR hT hR), g * q * g⁻¹ = q →
      ∀ v ∈ Q2r.map (embR hT hR), q * v = v * q)
    (hN : ¬ G ≤ Subgroup.normalizer ((Nr.map (embR hT hR) : Subgroup D) : Set D))
    {y' : D} (hy'G : y' ∈ G) (hy'3 : y' ^ 3 = 1) (hy'1 : y' ≠ 1) :
    ∃ y ∈ G, MRelB a b s ρ y := by
  have hinj := embR_injective hT hR hcard
  set φ := embR hT hR with hφ
  set Q : Subgroup D := Q2r.map φ with hQ
  have hrange : φ.range = Subgroup.closure ({a, b, s, ρ} : Set D) := embR_range hT hR
  have hTG : Subgroup.closure ({a, b, s, ρ} : Set D) ≤ G := hv.T_le
  have hmemT : ∀ w : Tr, φ w ∈ G := fun w => hTG (hrange ▸ ⟨w, rfl⟩)
  have hQ_mem : ∀ w : Tr, inQ2 w → φ w ∈ Q := fun w hw => Subgroup.mem_map_of_mem _ hw
  have hQ_inv : ∀ q ∈ Q, ∃ w : Tr, inQ2 w ∧ φ w = q := fun q hq => by
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨w, hw, rfl⟩
  have hy'3' : y' * y' * y' = 1 := by rw [← pow_three']; exact hy'3
  let κ : D →* D := (MulAut.conj y'⁻¹).toMonoidHom
  have hκ : ∀ g, κ g = y'⁻¹ * g * y' := fun g => by
    show y'⁻¹ * g * y'⁻¹⁻¹ = _
    rw [inv_inv]
  have κ3 : ∀ x, κ (κ (κ x)) = x := fun x => by
    simp only [hκ]
    calc y'⁻¹ * (y'⁻¹ * (y'⁻¹ * x * y') * y') * y' = (y' * y' * y')⁻¹ * x * (y' * y' * y') := by
          group
      _ = x := by rw [hy'3', inv_one, one_mul, mul_one]
  have hκQ : ∀ w : Tr, inQ2 w → κ (φ w) ∈ Q := fun w hw => by
    rw [hκ]
    simpa using hGQ y'⁻¹ (G.inv_mem hy'G) (φ w) (hQ_mem w hw)
  obtain ⟨u₁, hu₁q, hu₁⟩ := hQ_inv _ (hκQ cR cR_mem_Q2)
  obtain ⟨u₂, hu₂q, hu₂⟩ := hQ_inv _ (hκQ pR pR_mem_Q2)
  obtain ⟨u₃, hu₃q, hu₃⟩ := hQ_inv _ (hκQ rS rS_mem_Q2)
  obtain ⟨u₄, hu₄q, hu₄⟩ := hQ_inv _ (hκQ rR rR_mem_Q2)
  set u : Tr × Tr × Tr × Tr := (u₁, u₂, u₃, u₄) with hu
  have hF : ∀ w : Tr, inQ2 w → φ (Fq u w) = κ (φ w) := fun w hw =>
    (conj_Fq φ κ u hu₁.symm hu₂.symm hu₃.symm hu₄.symm w hw).symm
  have hFmem : ∀ w : Tr, inQ2 w → inQ2 (Fq u w) := fun w hw => by
    obtain ⟨w', hw'q, hw'⟩ := hQ_inv _ (hκQ w hw)
    have : w' = Fq u w := hinj (by rw [hw', hF w hw])
    rw [← this]; exact hw'q
  have hrels : Rels4 u₁ u₂ u₃ u₄ := by
    refine Rels4.of_injective hinj ?_
    rw [hu₁, hu₂, hu₃, hu₄]
    exact Rels4.map (κ.comp φ) gen_rels
  have hcubeAll : ∀ w : Tr, inQ2 w → Fq u (Fq u (Fq u w)) = w := fun w hw => by
    apply hinj
    rw [hF _ (hFmem _ (hFmem _ hw)), hF _ (hFmem _ hw), hF _ hw, κ3]
  have hcube : Cube4 u :=
    ⟨hcubeAll cR cR_mem_Q2, hcubeAll pR pR_mem_Q2, hcubeAll rS rS_mem_Q2, hcubeAll rR rR_mem_Q2⟩
  have hf : FPF u := by
    intro g hg hgfix
    have h1 : κ (φ g) = φ g := by rw [← hF g hg, hgfix]
    have h2 : y' * φ g * y'⁻¹ = φ g := by
      rw [hκ] at h1
      have h1' : y' * φ g = φ g * y' := by
        calc y' * φ g = y' * (y'⁻¹ * φ g * y') := by rw [h1]
          _ = φ g * y' := by group
      calc y' * φ g * y'⁻¹ = φ g * y' * y'⁻¹ := by rw [h1']
        _ = φ g := by group
    have h3 := hfpf y' hy'G hy'1 hy'3 (φ g) (hQ_mem g hg) h2
    exact Q2_center g hg (fun v hv => hinj (by
      rw [map_mul, map_mul]
      exact h3 (φ v) (hQ_mem v hv)))
  have hsq : u₁ * u₁ ≠ 1 := by
    intro h
    apply cR_sq_ne_one
    apply hinj
    rw [map_mul, map_one]
    have h1 : κ (φ cR) * κ (φ cR) = 1 := by rw [← hu₁, ← map_mul, h, map_one]
    have h2 : κ (φ cR * φ cR) = 1 := by rw [map_mul]; exact h1
    rw [hκ] at h2
    calc φ cR * φ cR = y' * (y'⁻¹ * (φ cR * φ cR) * y') * y'⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hcls := classify_B5 u hu₁q hu₂q hu₃q hu₄q hrels hcube hf hsq
  rcases hcls with ⟨t, ht⟩ | hNst
  ·
    obtain ⟨y, hy⟩ : ∃ y : D, y = φ t * y' * (φ t)⁻¹ := ⟨_, rfl⟩
    have hyG : y ∈ G := by
      rw [hy]; exact G.mul_mem (G.mul_mem (hmemT t) hy'G) (G.inv_mem (hmemT t))
    have hy3 : y ^ 3 = 1 := by
      have e : y ^ 3 = φ t * y' ^ 3 * (φ t)⁻¹ := by
        rw [hy]; simp only [pow_three']; group
      rw [e, hy'3]; group
    have hconj : ∀ g : Tr, inQ2 g →
        y⁻¹ * φ g * y = φ (t * Fq u (t⁻¹ * g * t) * t⁻¹) := by
      intro g hg
      have hg' : inQ2 (t⁻¹ * g * t) := by simpa using Q2_normal t⁻¹ g hg
      have e := hF _ hg'
      rw [hκ] at e
      simp only [map_mul, map_inv] at e ⊢
      rw [e, hy]
      group
    have ht1 : t * Fq u (t⁻¹ * cR * t) * t⁻¹ = alpha5.1 := congrArg Prod.fst ht
    have ht2 : t * Fq u (t⁻¹ * pR * t) * t⁻¹ = alpha5.2.1 := congrArg (fun p => p.2.1) ht
    have ht3 : t * Fq u (t⁻¹ * rS * t) * t⁻¹ = alpha5.2.2.1 := congrArg (fun p => p.2.2.1) ht
    have ht4 : t * Fq u (t⁻¹ * rR * t) * t⁻¹ = alpha5.2.2.2 := congrArg (fun p => p.2.2.2) ht
    have hyc : y⁻¹ * (a * b) * y = a * a * s * ρ := by
      have := hconj cR cR_mem_Q2
      rwa [ht1, embR_cR, embR_alpha1] at this
    have hyp : y⁻¹ * (a * a) * y = a * b⁻¹ * ρ := by
      have := hconj pR pR_mem_Q2
      rwa [ht2, embR_pR, embR_alpha2] at this
    have hyq : y⁻¹ * s * y = ρ := by
      have := hconj rS rS_mem_Q2
      rwa [ht3, embR_rS, embR_alpha3] at this
    have hyr : y⁻¹ * ρ * y = s * ρ := by
      have := hconj rR rR_mem_Q2
      rwa [ht4, embR_rR, embR_alpha4] at this
    have hMC : MConj a b s ρ y := ⟨hy3, hyc, hyp, hyq, hyr⟩
    have hcj : ∀ w : Tr, inQ2 w → y⁻¹ * φ w * y = φ (Fq alpha5 w) :=
      fun w hw => hMC.conj_embR hT hR w hw
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : D, t₀ = φ rT0 := ⟨_, rfl⟩
    have ht₀G : t₀ ∈ G := by rw [ht₀]; exact hmemT rT0
    obtain ⟨y₂, hy₂⟩ : ∃ y₂ : D, y₂ = t₀ * y * t₀⁻¹ := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : D, z = y₂ * y := ⟨_, rfl⟩
    have hzG : z ∈ G := by
      rw [hz, hy₂]
      exact G.mul_mem (G.mul_mem (G.mul_mem ht₀G hyG) (G.inv_mem ht₀G)) hyG
    have hzc : ∀ w : Tr, inQ2 w → z⁻¹ * φ w * z = φ w := by
      intro w hw
      have hw1 : inQ2 (rT0⁻¹ * w * rT0) := by simpa using Q2_normal rT0⁻¹ w hw
      have e1 := hcj _ hw1
      have hw2 : inQ2 (Fq alpha5 (rT0⁻¹ * w * rT0)) := alpha5_mem _ hw1
      have hw3 : inQ2 (rT0 * Fq alpha5 (rT0⁻¹ * w * rT0) * rT0⁻¹) := Q2_normal rT0 _ hw2
      have e2 := hcj _ hw3
      have e3 : t₀⁻¹ * φ w * t₀ = φ (rT0⁻¹ * w * rT0) := by rw [ht₀]; simp only [map_mul, map_inv]
      have e4 : t₀ * φ (Fq alpha5 (rT0⁻¹ * w * rT0)) * t₀⁻¹ =
          φ (rT0 * Fq alpha5 (rT0⁻¹ * w * rT0) * rT0⁻¹) := by
        rw [ht₀]; simp only [map_mul, map_inv]
      calc z⁻¹ * φ w * z
          = y⁻¹ * (t₀ * (y⁻¹ * (t₀⁻¹ * φ w * t₀) * y) * t₀⁻¹) * y := by
            rw [hz, hy₂]; group
        _ = φ w := by rw [e3, e1, e4, e2, alpha5_inverted w hw]
    have hzcent : ∀ q ∈ Q, z * q = q * z := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hQ_inv q hq
      calc z * φ w = z * (z⁻¹ * φ w * z) := by rw [hzc w hw]
        _ = φ w * z := by group
    have hzQ : z ∈ Q := hC z hzG hzcent
    obtain ⟨wz, hwz, hwze⟩ := hQ_inv z hzQ
    have hwzc : ∀ v : Tr, inQ2 v → wz * v = v * wz := fun v hv => hinj (by
      rw [map_mul, map_mul, hwze]
      exact hzcent _ (hQ_mem v hv))
    have hz1 : z = 1 := by
      rcases Q2_center wz hwz hwzc with h1 | h1
      · rw [← hwze, h1, map_one]
      · have hz2 : z * z = 1 := by
          rw [← hwze, h1, ← map_mul, zR_sq, map_one]
        have hyz : y⁻¹ * z * y = z := by
          rw [← hwze, h1, hcj zR zR_mem_Q2, alpha5_zR]
        have hzy : z * y = y * z := by
          calc z * y = y * (y⁻¹ * z * y) := by group
            _ = y * z := by rw [hyz]
        have hy₂z : y₂ = z * y⁻¹ := by rw [hz]; group
        have hy₂3 : y₂ ^ 3 = 1 := by
          have e : y₂ ^ 3 = t₀ * y ^ 3 * t₀⁻¹ := by
            rw [hy₂]; simp only [pow_three']; group
          rw [e, hy3]; group
        have hz3 : z ^ 3 = 1 := by
          have h1' : (z * y⁻¹) ^ 3 = 1 := by rw [← hy₂z]; exact hy₂3
          have hc : Commute z y⁻¹ := Commute.inv_right (show Commute z y from hzy)
          rw [hc.mul_pow, inv_pow, hy3, inv_one, mul_one] at h1'
          exact h1'
        calc z = z ^ 3 * (z * z)⁻¹ := by group
          _ = 1 := by rw [hz3, hz2]; simp
    have hy₂y : y₂ = y⁻¹ := by
      have : y₂ * y = 1 := by rw [← hz]; exact hz1
      exact eq_inv_of_mul_eq_one_left this
    have hyt : y * (a * ρ) * y = a * ρ := by
      have e : t₀ * y = y⁻¹ * t₀ := by
        calc t₀ * y = (t₀ * y * t₀⁻¹) * t₀ := by group
          _ = y⁻¹ * t₀ := by rw [← hy₂, hy₂y]
      have ht₀' : t₀ = a * ρ := by rw [ht₀, embR_rT0]
      rw [← ht₀']
      calc y * t₀ * y = y * (t₀ * y) := by group
        _ = t₀ := by rw [e]; group
    exact ⟨y, hyG, ⟨hMC, hyt⟩⟩
  ·
    exfalso
    apply hN
    set N : Subgroup D := Nr.map φ with hNdef
    have hy'N : y' ∈ Subgroup.normalizer (N : Set D) := by
      refine mem_normalizer_of_cube hy'3 ?_
      intro n hn
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hn
      have hg' : inN g := hg
      rw [← hκ, ← hF g (N_le_Q2 g hg')]
      exact Subgroup.mem_map_of_mem _ (hNst g hg')
    have hTN : Subgroup.closure ({a, b, s, ρ} : Set D) ≤ Subgroup.normalizer (N : Set D) := by
      rw [← hrange]
      exact range_le_normalizer_N hT hR
    have hy'T : y' ∉ Subgroup.closure ({a, b, s, ρ} : Set D) :=
      hv.not_mem_of_orderOf (orderOf_eq_prime hy'3 hy'1)
    have hle := hv.le_of_not_mem (C := G ⊓ Subgroup.normalizer (N : Set D))
      (le_inf hTG hTN) inf_le_left ⟨hy'G, hy'N⟩ hy'T
    exact hle.trans inf_le_right

end CFSG.Quasithin.F6.GoldAmL5
