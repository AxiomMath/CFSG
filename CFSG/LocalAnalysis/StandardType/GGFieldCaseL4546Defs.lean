module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45Moving
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL46J
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGL45Config (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X B₂ : Subgroup G)
    (d y : G) (K U U₁ : Subgroup G) : Prop :=
  GGFieldCase p B Bs x L D J X ∧ GGTableBModule p Bs x L B₂ ∧ GGL43 Bs x X ∧ GGL44i p Bs x X ∧
    GGL44ii Bs x X B₂ ∧ GGL44iii p B Bs x D J X d y K ∧ GGL45Setup p Bs X U ∧
    GGInnerDiagPart U K U₁ ∧ U ≤ Subgroup.normalizer (U₁ : Set G)

theorem ggL45Config_of_setup {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G}
    {d y : G} {K U U₁ : Subgroup G} (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) :
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hS
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun u hu => h9 ⟨Subgroup.le_normalizer hu, ?_⟩⟩
  exact Subgroup.centralizer_le_normalizer _ (h7.1 hu)

end Defs

@[expose] def GGRawInndiagIso : LargeEvenRawCont :=
  fun R _ I _ => ∀ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' →
    LargeEvenLabelAll lab' (LargeEvenSimpleGuard fun R' _ I' _ =>
      ∀ (σ : R ≃* R') (φ : MulAut R), φ ∈ ggInndiag R I ↔ MulAut.congr σ φ ∈ ggInndiag R' I')

@[expose] def GGRawInndiagIsoInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGRawInndiagIso)

@[expose] def GGL45CentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
        Subgroup.zpowers d

@[expose] def GGL45OmegaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
      ∀ u ∈ U, u ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
        u ∈ Bs ⊔ (U ⊓ Subgroup.centralizer (K : Set G))

@[expose] def GGL45RankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
      ∀ w ∈ U, w ∉ U₁ → ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁,
        (a₁ * w * a₁⁻¹ * w⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        (a₂ * w * a₂⁻¹ * w⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ i j : ℕ, (a₁ * w * a₁⁻¹ * w⁻¹) ^ i * (a₂ * w * a₂⁻¹ * w⁻¹) ^ j ∈
          U ⊓ Subgroup.centralizer (K : Set G) → p ∣ i ∧ p ∣ j

@[expose] def GGL45TorusInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
      ∃ s : ℕ, 2 ≤ s ∧
        (∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        (∀ u ∈ U₁, u ^ p ^ s ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        (∃ u ∈ U₁, u ^ p ^ (s - 1) ∉ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        ∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
          ∀ u ∈ U₁, (u ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * u * x') ∈
            U ⊓ Subgroup.centralizer (K : Set G)

@[expose] def GGL46CoverInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      ∀ g ∈ X, ∃ u ∈ U₁, u⁻¹ * g ∈ Subgroup.centralizer (Bs : Set G)

@[expose] def GGL45FiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
    Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (U₁ : Set G) →
    (∀ r ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G),
          r * v * r⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) → v = 1) →
    (∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), v ^ p = 1 → v ∈ Subgroup.zpowers d) →
    (∀ n ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), n * v * n⁻¹ ∈ U₁) →
    ∀ r ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        r ∈ Subgroup.normalizer (U₁ : Set G)

section Facts

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.prime (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : p.Prime :=
  h.1.1.1.2.2.2.2.2.1.1

theorem GGL45Config.odd (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : p ≠ 2 :=
  h.1.1.1.2.2.2.2.2.1.2.1

theorem GGL45Config.isElemAbelian (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    IsElemAbelian p Bs :=
  h.1.1.2.1.2.1

theorem GGL45Config.x_mem (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : x ∈ Bs :=
  h.1.1.2.1.1 h.1.1.1.2.2.2.2.2.2.1.2.1

theorem GGL45Config.x_pow (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : x ^ p = 1 :=
  h.isElemAbelian.2 x h.x_mem

theorem GGL45Config.bstar_max (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
  h.1.1.2.1.2.2.2

theorem GGL45Config.bs_le (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : Bs ≤ U :=
  h.2.2.2.2.2.2.1.2.2.2

theorem GGL45Config.le_normalizer (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    U ≤ Subgroup.normalizer (K : Set G) :=
  h.2.2.2.2.2.2.2.1.1

theorem GGL45Config.le_centralizer (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    U ≤ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
  h.2.2.2.2.2.2.1.1

theorem GGL45Config.isPGroup (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : IsPGroup p U :=
  h.2.2.2.2.2.2.1.2.1

theorem GGL45Config.part_le (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : U₁ ≤ U :=
  h.2.2.2.2.2.2.2.1.2.1

theorem GGL45Config.le_normalizer_part (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    U ≤ Subgroup.normalizer (U₁ : Set G) :=
  h.2.2.2.2.2.2.2.2

theorem GGL45Config.d_mem (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    d ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
  have : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [h.2.2.2.2.2.1.1]
    exact Subgroup.mem_zpowers d
  exact this.2

theorem GGL45Config.d_ne (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : d ≠ 1 :=
  h.2.2.2.2.2.1.2.1

theorem GGL45Config.d_pow (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) : d ^ p = 1 :=
  h.isElemAbelian.2 d h.d_mem.1

theorem GGL45Config.d_mem_V (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    d ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
  refine ⟨h.bs_le h.d_mem.1, ?_⟩
  have hK := h.2.2.2.2.2.1.2.2.1.1.2.2.2.1
  have hy : d ∈ Subgroup.zpowers y := by
    rw [h.2.2.2.2.2.1.2.2.2.1]
    exact Subgroup.mem_zpowers d
  show d ∈ Subgroup.centralizer (K : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hky : y * k = k * y := (Subgroup.mem_centralizer_iff.mp (hK hk)) y rfl
  exact (Commute.zpow_right (hky.symm : Commute k y) n).eq

theorem GGL45Config.conj_mem_V (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {u v : G}
    (hu : u ∈ U) (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) :
    u * v * u⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) :=
  ⟨U.mul_mem (U.mul_mem hu hv.1) (U.inv_mem hu),
    (Subgroup.mem_normalizer_iff.mp (ggNormalizer_le_normalizer_centralizer K
      (h.le_normalizer hu)) v).mp hv.2⟩

theorem GGL45Config.conj_mem_part (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {u a : G}
    (hu : u ∈ U) (ha : a ∈ U₁) : u * a * u⁻¹ ∈ U₁ :=
  (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_part hu) a).mp ha

theorem GGL45Config.mem_of_commute (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {e : G}
    (he : e ∈ U) (hex : e * x = x * e) (hep : e ^ p = 1) : e ∈ Bs := by
  refine h.bstar_max e ?_ hep
  have hle : Bs ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [h.2.2.1.2]
    refine sup_le (fun b hb => ?_) ((Subgroup.zpowers_le).mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact ((Subgroup.mem_centralizer_iff.mp (h.le_centralizer he)) b hb).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact hex
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact ((Subgroup.mem_centralizer_iff.mp (hle hb)) e rfl).symm

theorem GGL45Config.inf_part_le (h : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hB₁ : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ U₁) (hx : x ∉ U₁) :
    Bs ⊓ U₁ ≤ Bs ⊓ Subgroup.centralizer (X : Set G) := by
  have : Fact p.Prime := ⟨h.prime⟩
  intro e he
  have hN : Bs ⊓ Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left (mul_comm_of_isElemAbelian h.isElemAbelian h.x_mem hb.1) k).eq)
  have he' : e ∈ ((Bs ⊓ Subgroup.centralizer (X : Set G) ⊔ Subgroup.zpowers x : Subgroup G) :
      Set G) := by
    rw [← h.2.2.1.2]
    exact he.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at he'
  obtain ⟨b, hb, z, hz, rfl⟩ := he'
  have hzU : z ∈ U₁ := by
    have := U₁.mul_mem (U₁.inv_mem (hB₁ hb)) he.2
    simpa using this
  by_cases hz1 : z = 1
  · simpa [hz1] using hb
  · exfalso
    apply hx
    have heq := zpowers_eq_of_mem_of_ne_one h.x_pow hz hz1
    exact (Subgroup.zpowers_le.mpr hzU) (heq ▸ Subgroup.mem_zpowers x)

end Facts

section Marking

theorem ggLAut_congr {G : Type*} [Group G] (K : Subgroup G) {R R' : Type} [Group R] [Group R']
    (θ : K ⧸ Subgroup.center K ≃* R) (θ' : K ⧸ Subgroup.center K ≃* R')
    (g : Subgroup.normalizer (K : Set G)) :
    ggLAut K θ' g = MulAut.congr (θ.symm.trans θ') (ggLAut K θ g) := by
  ext r
  simp [ggLAut, MulAut.congr_apply]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem ggL4546_exists_marking {P' : LargeEvenRawCont}
    (hP' : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenLabelAll lab P')
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R),
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ GGRawInnField p R I F ∧ P' R I F ∧
      (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
        LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
      (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹)) ∧
      ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
        (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I) := by
  have hp := hcfg.prime
  have hp2 := hcfg.odd
  obtain ⟨-, -, -, -, -, hK, -, hpart, -⟩ := hcfg
  have hM1 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
    (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) hK.2.2.2.2
  have hM1' := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := P')
    (fun lab hl _ => hP' lab hl) (fun _ _ _ _ _ _ _ => trivial) hM1
  have hM1'' := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := GGRawInndiagIso) (fun lab hl _ => hiso lab hl) (fun _ _ _ _ _ _ _ => trivial) hM1'
  obtain ⟨-, lab, -, hraw1⟩ := hM1''
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨⟨⟨-, hB₁I, hxF⟩, hRIF⟩, hP'RIF⟩, hisoR⟩ :=
    largeEvenRawDatum_exists hraw1
  have hM2 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
    (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) hpart.2.2
  obtain ⟨-, lab', hlab', hraw2⟩ := hM2
  obtain ⟨R', _, I', F', ⟨hs', hna', θ', hU₁iff, hR'⟩, hisoRR'⟩ :=
    largeEvenRawDatum_exists (hisoR lab' hlab' _ hraw2)
  obtain ⟨hmul, hinv, hinn, -⟩ := hRIF hs hna
  obtain ⟨hmul', hinv', hinn', -⟩ := hR' hs' hna'
  refine ⟨R, inferInstance, I, F, θ, hs, hna, hRIF, hP'RIF, hB₁I, hxF, fun u hu huN => ?_⟩
  rw [hU₁iff u hu, ggL45_exists_induces_iff hinv' huN,
    ← ggL45_mem_ggInndiag_iff hmul' hinv' hinn', ← ggL45_mem_ggInndiag_iff hmul hinv hinn,
    hisoRR' hs' hna' (θ.symm.trans θ'), ← ggLAut_congr]

theorem largeEvenLabelAll_true (lab : LargeEvenLabel) :
    LargeEvenLabelAll lab fun _ _ _ _ => True := fun _ h =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq, trivial⟩) h

theorem ggL4546_basic (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    Bs ⊓ Subgroup.centralizer (X : Set G) ≤ U₁ ∧ x ∉ U₁ ∧
      U ⊓ Subgroup.centralizer (K : Set G) ≤ U₁ := by
  have hUK := hcfg.le_normalizer
  have hBsU := hcfg.bs_le
  obtain ⟨R, _, I, F, θ, hs, hna, hRIF, -, hB₁I, ⟨f, hf, u, hu, hord, hxind⟩, hiff⟩ :=
    ggL4546_exists_marking (P' := fun _ _ _ _ => True) (fun lab _ => largeEvenLabelAll_true lab)
      hraw hiso hcfg
  obtain ⟨hmul, hinv, hinn, hF⟩ := hRIF hs hna
  have hB₁N : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    fun b hb => hUK (hBsU hb.1)
  refine ⟨fun b hb => (hiff b (hBsU hb.1) (hUK (hBsU hb.1))).mpr
    (ggLAut_mem_of_induces K θ hB₁N hB₁I hb), ?_, fun v hv => ?_⟩
  · intro hx
    have hxU : x ∈ U := hBsU hcfg.x_mem
    have h1 := (hiff x hxU (hUK hxU)).mp hx
    have h2 : u * f * u⁻¹ = ggLAut K θ ⟨x⁻¹, inv_mem (hUK hxU)⟩ :=
      eq_ggLAut_of_induces K θ (hUK hxU) hxind
    have h3 : ggLAut K θ ⟨x⁻¹, inv_mem (hUK hxU)⟩ = (ggLAut K θ ⟨x, hUK hxU⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    apply hF f hf hord
    have e : f = u⁻¹ * (u * f * u⁻¹) * u := by group
    rw [e, h2, h3]
    exact hmul _ (hmul _ (hinv u hu) _ (hinv _ h1)) _ hu
  · refine (hiff v hv.1 (hUK hv.1)).mpr ?_
    have e : ggLAut K θ ⟨v, hUK hv.1⟩ = 1 := ggLAut_of_mem_centralizer_outdiag K θ hv.2
    rw [e]
    simpa using hinn 1

theorem ggL4546_comm_mem (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) (hcx : c * x * c⁻¹ ∈ U) :
    c * x * c⁻¹ * x⁻¹ ∈ U₁ := by
  have hUK := hcfg.le_normalizer
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  obtain ⟨R, _, I, F, θ, hs, hna, hRIF, hcenR, -, ⟨f, hf, u, hu, -, hxind⟩, hiff⟩ :=
    ggL4546_exists_marking (P' := GGRawFieldCentral) hcen hraw hiso hcfg
  obtain ⟨-, hinv, hinn, -⟩ := hRIF hs hna
  have hcen' := hcenR hs hna
  have h2 : u * f * u⁻¹ = ggLAut K θ ⟨x⁻¹, inv_mem (hUK hxU)⟩ :=
    eq_ggLAut_of_induces K θ (hUK hxU) hxind
  have h3 : ggLAut K θ ⟨x, hUK hxU⟩ = (u * f⁻¹ * u⁻¹ * f) * f⁻¹ := by
    have h4 : ggLAut K θ ⟨x, hUK hxU⟩ = (ggLAut K θ ⟨x⁻¹, inv_mem (hUK hxU)⟩)⁻¹ := by
      rw [← map_inv]
      congr 1
      exact Subtype.ext (inv_inv x).symm
    rw [h4, ← h2]
    group
  have h1I : (1 : MulAut R) ∈ I := by simpa using hinn 1
  have hfF : f⁻¹ ∈ Subgroup.closure F := inv_mem (Subgroup.subset_closure hf)
  have hxF : ∃ u' ∈ I, ∃ f' ∈ Subgroup.closure F, ggLAut K θ ⟨x, hUK hxU⟩ = u' * f' := by
    refine ⟨u * f⁻¹ * u⁻¹ * f, ?_, f⁻¹, hfF, h3⟩
    have := hcen' u 1 h1I f⁻¹ hfF
    simpa using this
  have hmem : c * x * c⁻¹ * x⁻¹ ∈ U := U.mul_mem hcx (U.inv_mem hxU)
  refine (hiff _ hmem (hUK hmem)).mpr ?_
  exact ggLAut_comm_mem θ hcen' hc (hUK hxU) hxF (hUK hmem)

end Marking

end CFSG.StandardType

end
