module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bA
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Norm
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Syl

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

omit [Finite G] in
theorem AutIso.imgG_inf_cen (iso : AutIso M₁ M₂) (b : Bh) :
    iso.imgG (That ⊓ Subgroup.centralizer ({(b : Ah)} : Set Ah)) =
      iso.imgG That ⊓ cenOf (iso.toG b) := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ⟨haT, haC⟩, rfl⟩ := iso.mem_imgG.1 hg
    refine ⟨iso.mem_imgG.2 ⟨a, haT, rfl⟩, ?_⟩
    show iso.toG a ∈ Subgroup.centralizer ({iso.toG b} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : a * b = b * a := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 haC)
    have h2 := congrArg iso.toG this
    rwa [AutIso.toG_mul, AutIso.toG_mul] at h2
  · rintro ⟨hgT, hgC⟩
    obtain ⟨a, haT, rfl⟩ := iso.mem_imgG.1 hgT
    refine iso.mem_imgG.2 ⟨a, ⟨haT, ?_⟩, rfl⟩
    have hgC' := Subgroup.mem_centralizer_singleton_iff.1
      (show iso.toG a ∈ Subgroup.centralizer ({iso.toG b} : Set G) from hgC)
    show (a : Ah) ∈ Subgroup.centralizer ({(b : Ah)} : Set Ah)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : a * b = b * a := by
      apply iso.toG_injective
      rw [AutIso.toG_mul, AutIso.toG_mul]
      exact hgC'
    have h := congrArg (fun x : ↥Bh => (x : Ah)) this
    simpa only [Subgroup.coe_mul] using h

omit [Finite G] in
theorem card_T0
    (iso : AutIso M₁ M₂) : Nat.card ↥(iso.imgG That) = 128 := by
  rw [iso.card_imgG That_le_Bh, card_That]

theorem F_notConj
    (c : AutCtx G M₁ M₂ z) (h5 : U42AutFusionZ) : ¬ IsConj (c.iso.toG fhB) z :=
  h5 G M₁ M₂ z c _ ⟨fhB, isGoodInv_fhatA, rfl⟩

omit [Finite G] in
theorem F_ne_one
    (iso : AutIso M₁ M₂) : iso.toG fhB ≠ 1 := by
  intro h
  have h0 : fhB = 1 := iso.toG_injective (h.trans iso.toG_one.symm)
  have h1 : (fhB : Ah) = 1 := congrArg (fun x : Bh => (x : Ah)) h0
  rw [coe_fhB] at h1
  exact fhatA_not_mem_Yh (by rw [h1]; exact Yh.one_mem)

omit [Finite G] in
theorem F_sq (iso : AutIso M₁ M₂) :
    iso.toG fhB * iso.toG fhB = 1 := by
  rw [← AutIso.toG_mul]
  have : fhB * fhB = 1 := Subtype.ext (by
    have h := fhatA_sq
    rwa [pow_two] at h)
  rw [this]
  exact iso.toG_one

theorem Tf_ne
    (c : AutCtx G M₁ M₂ z) (h4 : NotExtremalStmt) {R : Subgroup G}
    (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB))) :
    c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≠ R := by
  intro hTR
  have hT₀ := isSylowTwoOf_imgG_That c.iso
  have hFT : c.iso.toG fhB ∈ c.iso.imgG That := c.iso.mem_imgG.2 ⟨fhB, fhatA_mem_That, rfl⟩
  have hFS : c.iso.toG fhB ∉ sOf M₁ M₂ := by
    intro h
    obtain ⟨y, hy, hyF⟩ := c.iso.mem_pCoreOf_iff.1 h
    have : y = fhB := c.iso.toG_injective hyF
    rw [this] at hy
    exact fhatA_not_mem_Yh hy.2
  have := h4 G M₁ M₂ z c _ hT₀ _ hFT hFS (by rw [pow_two]; exact F_sq c.iso)
  apply this
  rw [hTR]
  exact hR

theorem AutCtx.central_T0
    (c : AutCtx G M₁ M₂ z) {u : G} (hu : u ∈ c.iso.imgG That)
    (hc : ∀ t ∈ c.iso.imgG That, t * u = u * t) : u = 1 ∨ u = z := by
  obtain ⟨b, hbT, rfl⟩ := c.iso.mem_imgG.1 hu
  have hbcen : ∀ m ∈ That, m * (b : Ah) = (b : Ah) * m := by
    intro m hm
    have h1 := hc (c.iso.toG ⟨m, That_le_Bh hm⟩) (c.iso.mem_imgG.2 ⟨⟨m, That_le_Bh hm⟩, hm, rfl⟩)
    have h2 : (⟨m, That_le_Bh hm⟩ : Bh) * b = b * ⟨m, That_le_Bh hm⟩ := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, AutIso.toG_mul]
      exact h1
    exact congrArg (fun x : Bh => (x : Ah)) h2
  rcases center_That hbT (fun t ht => (hbcen t ht).symm) with h | h
  · left
    rw [(Subtype.ext h : b = 1)]
    exact c.iso.toG_one
  · right
    rw [(Subtype.ext h : b = xB)]
    exact c.iso.toG_xB c.z2 c.z1 c.zc

theorem card_R
    (c : AutCtx G M₁ M₂ z) (h2 : U42AutSylow) (h4 : NotExtremalStmt) (h5 : U42AutFusionZ)
    {R : Subgroup G} (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R) : Nat.card ↥R = 2 ^ 6 := by
  have hTG : IsSylowTwoOf (c.iso.imgG That) ⊤ := h2 G M₁ M₂ z c _ (isSylowTwoOf_imgG_That c.iso)
  have hne := Tf_ne c h4 hR
  have hR2 : IsPGroup 2 R := hR.2.1
  obtain ⟨j, hj⟩ := hR2.exists_card_eq
  have hlt : 32 < Nat.card R := by
    rw [← card_Tf c.iso]
    rcases (Subgroup.card_le_of_le hTR).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hTR h.symm.le) hne
  have hle : Nat.card R ≤ 128 := by
    have := card_le_twoPart (le_top : R ≤ ⊤) hR2
    rwa [← hTG.card_eq, card_T0] at this
  have hj6 : 6 ≤ j := by
    by_contra h
    have : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hj7 : j ≤ 7 := by
    by_contra h
    have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hj6' : j = 6
  · rw [hj, hj6']
  · exfalso
    have hj7' : j = 7 := by omega
    have hRS : IsSylowTwoOf R ⊤ := by
      refine isSylowTwoOf_of_card_eq le_top hR2 ?_
      rw [← hTG.card_eq, card_T0, hj, hj7']
      norm_num
    obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hTG hRS
    have hFc : ∀ b ∈ cenOf (c.iso.toG fhB), b * c.iso.toG fhB = c.iso.toG fhB * b := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.1 hb
    have hFR : c.iso.toG fhB ∈ R := mem_of_central_of_isSylowTwoOf hR
      (Subgroup.mem_centralizer_singleton_iff.2 rfl) hFc (F_sq c.iso)
    have hFT : g⁻¹ * c.iso.toG fhB * g ∈ c.iso.imgG That := B6.mem_conjSub.1 (hg ▸ hFR)
    have hcen : ∀ t ∈ c.iso.imgG That, t * (g⁻¹ * c.iso.toG fhB * g) =
        (g⁻¹ * c.iso.toG fhB * g) * t := by
      intro t ht
      have htR : g * t * g⁻¹ ∈ R := hg ▸ B6.mem_conjSub.2 (by simpa [mul_assoc] using ht)
      have := hFc _ (hR.1 htR)
      calc t * (g⁻¹ * c.iso.toG fhB * g) = g⁻¹ * (g * t * g⁻¹ * c.iso.toG fhB) * g := by group
        _ = g⁻¹ * (c.iso.toG fhB * (g * t * g⁻¹)) * g := by rw [this]
        _ = (g⁻¹ * c.iso.toG fhB * g) * t := by group
    rcases c.central_T0 hFT hcen with h | h
    · apply F_ne_one c.iso
      calc c.iso.toG fhB = g * (g⁻¹ * c.iso.toG fhB * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · exact F_notConj c h5 (isConj_iff.2 ⟨g⁻¹, by
        calc g⁻¹ * c.iso.toG fhB * g⁻¹⁻¹ = g⁻¹ * c.iso.toG fhB * g := by group
          _ = z := h⟩)

theorem exists_t
    (c : AutCtx G M₁ M₂ z) (h2 : U42AutSylow) (h5 : U42AutFusionZ)
    {R : Subgroup G} (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB))) (hcard : Nat.card ↥R = 2 ^ 6) :
    ∃ g : G, g⁻¹ * c.iso.toG fhB * g ∈ c.iso.imgG That ∧
      (g⁻¹ * c.iso.toG fhB * g) ^ 2 = 1 ∧
      Nat.card ↥(c.iso.imgG That ⊓ cenOf (g⁻¹ * c.iso.toG fhB * g)) = 2 ^ 6 := by
  have hTG : IsSylowTwoOf (c.iso.imgG That) ⊤ := h2 G M₁ M₂ z c _ (isSylowTwoOf_imgG_That c.iso)
  obtain ⟨S, hS, hRS⟩ := B6.exists_isSylowTwoOf_ge hR.2.1 (le_top : R ≤ ⊤)
  obtain ⟨g, -, hSg⟩ := B6.isSylowTwoOf_exists_conj hTG hS
  have hFc : ∀ b ∈ cenOf (c.iso.toG fhB), b * c.iso.toG fhB = c.iso.toG fhB * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 hb
  have hFR : c.iso.toG fhB ∈ R := mem_of_central_of_isSylowTwoOf hR
    (Subgroup.mem_centralizer_singleton_iff.2 rfl) hFc (F_sq c.iso)
  have hRT : ∀ x ∈ R, g⁻¹ * x * g ∈ c.iso.imgG That := fun x hx =>
    B6.mem_conjSub.1 (hSg ▸ hRS hx)
  have ht : g⁻¹ * c.iso.toG fhB * g ∈ c.iso.imgG That := hRT _ hFR
  refine ⟨g, ht, ?_, ?_⟩
  · calc (g⁻¹ * c.iso.toG fhB * g) ^ 2
        = g⁻¹ * (c.iso.toG fhB * c.iso.toG fhB) * g := by rw [pow_two]; group
      _ = 1 := by rw [F_sq c.iso]; group
  · apply le_antisymm
    · obtain ⟨t', ht'T, ht'g⟩ := c.iso.mem_imgG.1 ht
      have hFne : c.iso.toG fhB ≠ 1 := F_ne_one c.iso
      have ht'2 : t' * t' = 1 := by
        apply c.iso.toG_injective
        rw [AutIso.toG_mul, ht'g, c.iso.toG_one]
        calc g⁻¹ * c.iso.toG fhB * g * (g⁻¹ * c.iso.toG fhB * g)
            = g⁻¹ * (c.iso.toG fhB * c.iso.toG fhB) * g := by group
          _ = 1 := by rw [F_sq c.iso]; group
      have ht'1 : (t' : Ah) ≠ 1 := by
        intro h1
        apply hFne
        have : t' = 1 := Subtype.ext h1
        have h2 := congrArg c.iso.toG this
        rw [ht'g, c.iso.toG_one] at h2
        calc c.iso.toG fhB = g * (g⁻¹ * c.iso.toG fhB * g) * g⁻¹ := by group
          _ = 1 := by rw [h2]; group
      have ht'x : (t' : Ah) ≠ xA := by
        intro h1
        apply F_notConj c h5
        have : t' = xB := Subtype.ext h1
        have h2 := congrArg c.iso.toG this
        rw [ht'g, c.iso.toG_xB c.z2 c.z1 c.zc] at h2
        exact isConj_iff.2 ⟨g⁻¹, by
          calc g⁻¹ * c.iso.toG fhB * g⁻¹⁻¹ = g⁻¹ * c.iso.toG fhB * g := by group
            _ = z := h2⟩
      have hb := card_cent_le_64 ht'T (congrArg (fun x : Bh => (x : Ah)) ht'2) ht'1 ht'x
      have e := c.iso.imgG_inf_cen t'
      have hK : That ⊓ Subgroup.centralizer ({(t' : Ah)} : Set Ah) ≤ Bh :=
        inf_le_left.trans That_le_Bh
      rw [← ht'g, ← e, c.iso.card_imgG hK]
      exact hb
    · have hle : B6.conjSub g⁻¹ R ≤ c.iso.imgG That ⊓ cenOf (g⁻¹ * c.iso.toG fhB * g) := by
        intro x hx
        have hx' : g⁻¹⁻¹ * x * g⁻¹ ∈ R := B6.mem_conjSub.1 hx
        refine ⟨?_, ?_⟩
        · have := hRT _ hx'
          simpa [mul_assoc] using this
        · show x ∈ Subgroup.centralizer ({g⁻¹ * c.iso.toG fhB * g} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := hFc _ (hR.1 hx')
          calc x * (g⁻¹ * c.iso.toG fhB * g)
              = g⁻¹ * (g * x * g⁻¹ * c.iso.toG fhB) * g := by group
            _ = g⁻¹ * (c.iso.toG fhB * (g * x * g⁻¹)) * g := by
              simpa using congrArg (g⁻¹ * · * g) h1
            _ = g⁻¹ * c.iso.toG fhB * g * x := by group
      have := Subgroup.card_le_of_le hle
      rwa [conjSub_card, hcard] at this

end CFSG.Quasithin.H13.F431.U42Aut
