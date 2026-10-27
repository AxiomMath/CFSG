module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqAbs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace QA25

section Bar

variable {G : Type} [Group G]

abbrev barMap (H : Subgroup G) : ↥H →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥H)

theorem mem_modO2Image_iff {H L : Subgroup G} {y : ↥H ⧸ CFSG.pCore 2 ↥H} :
    y ∈ modO2Image H L ↔ ∃ h : ↥H, (h : G) ∈ L ∧ barMap H h = y := by
  unfold modO2Image
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

@[expose] def preimBar (H K : Subgroup G) (P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Subgroup G :=
  K ⊓ (P.comap (barMap H)).map H.subtype

theorem mem_preimBar {H K : Subgroup G} {P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} {g : G} :
    g ∈ preimBar H K P ↔
      g ∈ K ∧ ∃ h : ↥H, (h : G) = g ∧ barMap H h ∈ P := by
  unfold preimBar
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  simp only [Subgroup.mem_comap]
  constructor
  · rintro ⟨hK, h, hh, hg⟩
    exact ⟨hK, h, hg, hh⟩
  · rintro ⟨hK, h, hg, hh⟩
    exact ⟨hK, h, hh, hg⟩

theorem not_isDiagramNontrivial_of_bar {H K T : Subgroup G} (hKH : K ≤ H) (hTH : T ≤ H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hS : IsSylowTwoOf (T ⊓ K) K)
    {P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hPK : P ≤ modO2Image H K)
    (hPne : P ≠ modO2Image H K)
    (hPmax : ∀ Q : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), Q ≤ modO2Image H K → P ≤ Q →
      Q = P ∨ Q = modO2Image H K)
    (hB : modO2Image H K ⊓ Subgroup.normalizer
      ((modO2Image H (T ⊓ K) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ P)
    (hT : modO2Image H T ≤ Subgroup.normalizer
      ((P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    ¬ E2.IsDiagramNontrivial T K (T ⊓ K) := by
  have hmem : ∀ {k : G} (hk : k ∈ K), k ∈ preimBar H K P ↔ barMap H ⟨k, hKH hk⟩ ∈ P := by
    intro k hk
    rw [mem_preimBar]
    constructor
    · rintro ⟨-, h, hh, hP⟩
      have : h = ⟨k, hKH hk⟩ := Subtype.ext hh
      rwa [this] at hP
    · intro hP
      exact ⟨hk, ⟨k, hKH hk⟩, rfl, hP⟩
  refine H13.Lem1227Eq.not_isDiagramNontrivial_of_stable (P := preimBar H K P) hS
    inf_le_left ?_ ?_ ?_ ?_
  ·
    intro h
    apply hPne
    refine le_antisymm hPK fun y hy => ?_
    obtain ⟨h0, hh0, rfl⟩ := mem_modO2Image_iff.mp hy
    have : (h0 : G) ∈ preimBar H K P := by rw [h]; exact hh0
    have h1 := (hmem hh0).mp this
    simpa using h1
  ·
    intro Q hQK hPQ
    have hQ1 : modO2Image H Q ≤ modO2Image H K := Subgroup.map_mono (fun x hx => hQK hx)
    have hPQ1 : P ≤ modO2Image H Q := by
      intro y hy
      obtain ⟨h0, hh0, rfl⟩ := mem_modO2Image_iff.mp (hPK hy)
      exact mem_modO2Image_iff.mpr ⟨h0, hPQ ((hmem hh0).mpr hy), rfl⟩
    rcases hPmax _ hQ1 hPQ1 with h | h
    · left
      refine le_antisymm (fun q hq => ?_) hPQ
      have hqK : q ∈ K := hQK hq
      rw [hmem hqK]
      have : barMap H ⟨q, hKH hqK⟩ ∈ modO2Image H Q :=
        mem_modO2Image_iff.mpr ⟨⟨q, hKH hqK⟩, hq, rfl⟩
      rwa [h] at this
    · right
      refine le_antisymm hQK fun k hk => ?_
      have hk1 : barMap H ⟨k, hKH hk⟩ ∈ modO2Image H Q := by
        rw [h]
        exact mem_modO2Image_iff.mpr ⟨⟨k, hKH hk⟩, hk, rfl⟩
      obtain ⟨q, hq, hqk⟩ := mem_modO2Image_iff.mp hk1
      have hqK : (q : G) ∈ K := hQK hq
      have hker : (q : G)⁻¹ * k ∈ preimBar H K P := by
        rw [hmem (K.mul_mem (K.inv_mem hqK) hk)]
        have : barMap H ⟨(q : G)⁻¹ * k, hKH (K.mul_mem (K.inv_mem hqK) hk)⟩ = 1 := by
          have e : (⟨(q : G)⁻¹ * k, hKH (K.mul_mem (K.inv_mem hqK) hk)⟩ : ↥H) =
              q⁻¹ * ⟨k, hKH hk⟩ := rfl
          rw [e, map_mul, map_inv, hqk, inv_mul_cancel]
        rw [this]
        exact P.one_mem
      have : (q : G) * ((q : G)⁻¹ * k) ∈ Q := Q.mul_mem hq (hPQ hker)
      simpa using this
  ·
    rintro x ⟨hxK, hxN⟩
    have hxK' : x ∈ K := hxK
    have hxN' : x ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := hxN
    rw [hmem hxK']
    refine hB ⟨mem_modO2Image_iff.mpr ⟨⟨x, hKH hxK'⟩, hxK', rfl⟩, ?_⟩
    refine Subgroup.mem_normalizer_iff.mpr ?_
    have key : ∀ {z : G} (hz : z ∈ T ⊓ K) , x * z * x⁻¹ ∈ T ⊓ K := fun {z} hz =>
      (Subgroup.mem_normalizer_iff.mp hxN' z).mp hz
    have key' : ∀ {z : G}, x * z * x⁻¹ ∈ T ⊓ K → z ∈ T ⊓ K := fun {z} hz =>
      (Subgroup.mem_normalizer_iff.mp hxN' z).mpr hz
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, rfl⟩ := mem_modO2Image_iff.mp hy
      refine mem_modO2Image_iff.mpr ⟨⟨x, hKH hxK'⟩ * u * ⟨x, hKH hxK'⟩⁻¹, key hu, ?_⟩
      simp
    · intro hy
      obtain ⟨u, hu, hu'⟩ := mem_modO2Image_iff.mp hy
      refine mem_modO2Image_iff.mpr ⟨⟨x, hKH hxK'⟩⁻¹ * u * ⟨x, hKH hxK'⟩, ?_, ?_⟩
      · refine key' ?_
        have e : x * ((⟨x, hKH hxK'⟩⁻¹ * u * ⟨x, hKH hxK'⟩ : ↥H) : G) * x⁻¹ = (u : G) := by
          simp [mul_assoc]
        rw [e]
        exact hu
      · rw [map_mul, map_mul, map_inv, hu']
        group
  ·
    intro t ht
    have hT' : ∀ t ∈ T, ∀ g ∈ preimBar H K P, t * g * t⁻¹ ∈ preimBar H K P := by
      intro t ht g hg
      have hgK : g ∈ K := (mem_preimBar.mp hg).1
      have htgK : t * g * t⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hTK ht) g).mp hgK
      rw [hmem htgK]
      have hg' := (hmem hgK).mp hg
      have htT : barMap H ⟨t, hTH ht⟩ ∈ modO2Image H T :=
        mem_modO2Image_iff.mpr ⟨⟨t, hTH ht⟩, ht, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hT htT) (barMap H ⟨g, hKH hgK⟩)).mp hg'
      have e : barMap H ⟨t * g * t⁻¹, hKH htgK⟩ =
          barMap H ⟨t, hTH ht⟩ * barMap H ⟨g, hKH hgK⟩ * (barMap H ⟨t, hTH ht⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h1
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hT' t ht g hg, fun hg => ?_⟩
    have := hT' t⁻¹ (T.inv_mem ht) _ hg
    simpa [mul_assoc] using this

theorem coe_mem_pCoreOf {H : Subgroup G} (y : ↥H) (hy : y ∈ CFSG.pCore 2 ↥H) :
    (y : G) ∈ pCoreOf 2 H := by
  refine ⟨y, ?_, rfl⟩
  exact hy

theorem modO2Image_inf {H T K : Subgroup G} (hO : pCoreOf 2 H ≤ T) :
    modO2Image H (T ⊓ K) = modO2Image H T ⊓ modO2Image H K := by
  refine le_antisymm (le_inf (Subgroup.map_mono fun x hx => hx.1)
    (Subgroup.map_mono fun x hx => hx.2)) fun y hy => ?_
  obtain ⟨h1, hh1, rfl⟩ := mem_modO2Image_iff.mp hy.1
  obtain ⟨h2, hh2, h12⟩ := mem_modO2Image_iff.mp hy.2
  have h3 : h1⁻¹ * h2 ∈ CFSG.pCore 2 ↥H := by
    have := QuotientGroup.eq.mp h12.symm
    exact this
  have h4 : ((h1⁻¹ * h2 : ↥H) : G) ∈ T := hO (coe_mem_pCoreOf _ h3)
  have h5 : (h2 : G) ∈ T := by
    have := T.mul_mem hh1 h4
    simpa using this
  exact mem_modO2Image_iff.mpr ⟨h2, ⟨h5, hh2⟩, h12⟩

theorem modO2Image_le_normalizer {H T K : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    modO2Image H T ≤ Subgroup.normalizer ((modO2Image H K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := mem_modO2Image_iff.mp ht
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  constructor
  · intro hy
    obtain ⟨k, hk, rfl⟩ := mem_modO2Image_iff.mp hy
    refine mem_modO2Image_iff.mpr ⟨a * k * a⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTK ha) k).mp hk
  · intro hy
    obtain ⟨k, hk, hk'⟩ := mem_modO2Image_iff.mp hy
    refine mem_modO2Image_iff.mpr ⟨a⁻¹ * k * a, ?_, ?_⟩
    · have e : ((a : G)) * (((a⁻¹ * k * a : ↥H)) : G) * (a : G)⁻¹ = (k : G) := by
        simp [mul_assoc]
      have := (Subgroup.mem_normalizer_iff.mp (hTK ha) ((a⁻¹ * k * a : ↥H) : G))
      rw [e] at this
      exact this.mpr hk
    · rw [map_mul, map_mul, map_inv, hk']
      group

end Bar

end QA25

end CFSG.Quasithin
