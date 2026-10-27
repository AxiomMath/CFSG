module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriForm
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriNat

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small CFSG.Open Module

section Transport

variable {K : Type*} [Field K] {S V : Type*} [AddCommGroup S] [Module K S] [AddCommGroup V]
  [Module K V]

theorem range_eq_map_symm (e : S ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (eV : V ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    {l : K} (hl : l ≠ 0) {φ : S →ₗ[K] V} {ψ : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (h : ∀ s, eV (φ s) = l • ψ (e s)) :
    LinearMap.range φ = (LinearMap.range ψ).map (eV.symm : _ →ₗ[K] V) := by
  ext v
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨ψ (l • e s), ⟨l • e s, rfl⟩, ?_⟩
    rw [map_smul, ← h s]
    exact eV.symm_apply_apply _
  · rintro ⟨w, ⟨o, rfl⟩, rfl⟩
    refine ⟨e.symm (l⁻¹ • o), ?_⟩
    apply eV.injective
    rw [h, LinearEquiv.apply_symm_apply, map_smul, smul_inv_smul₀ hl, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

theorem ker_eq_comap (e : S ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (eV : V ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    {l : K} (hl : l ≠ 0) {φ : S →ₗ[K] V} {ψ : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (h : ∀ s, eV (φ s) = l • ψ (e s)) :
    LinearMap.ker φ = (LinearMap.ker ψ).comap (e : S →ₗ[K] _) := by
  ext s
  simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearEquiv.coe_coe]
  constructor
  · intro h0
    have := h s
    rw [h0, map_zero] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hl
  · intro h0
    apply eV.injective
    rw [h s, h0, smul_zero, map_zero]

theorem finrank_range_eq (e : S ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (eV : V ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    {l : K} (hl : l ≠ 0) {φ : S →ₗ[K] V} {ψ : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (h : ∀ s, eV (φ s) = l • ψ (e s)) :
    finrank K (LinearMap.range φ) = finrank K (LinearMap.range ψ) := by
  rw [range_eq_map_symm e eV hl h]
  exact LinearEquiv.finrank_map_eq eV.symm _

theorem finrank_range_inf_eq {S' : Type*} [AddCommGroup S'] [Module K S']
    (e : S ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (e' : S' ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (eV : V ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) {l : K} (hl : l ≠ 0) {φ : S →ₗ[K] V}
    {φ' : S' →ₗ[K] V} {ψ ψ' : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (h : ∀ s, eV (φ s) = l • ψ (e s)) (h' : ∀ s, eV (φ' s) = l • ψ' (e' s)) :
    finrank K ↥(LinearMap.range φ ⊓ LinearMap.range φ') =
      finrank K ↥(LinearMap.range ψ ⊓ LinearMap.range ψ') := by
  rw [range_eq_map_symm e eV hl h, range_eq_map_symm e' eV hl h',
    ← Submodule.map_inf _ eV.symm.injective]
  exact LinearEquiv.finrank_map_eq eV.symm _

end Transport

section Ranks

variable {K : Type} [Field K] {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y]
  [Module K Y]

@[expose] def TrialityRanks (β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (qX : QuadraticForm K X)
    (qY : QuadraticForm K Y) : Prop :=
  (∀ y : Y, y ≠ 0 → qY y ≠ 0 → Module.finrank K (LinearMap.range (β.flip y)) = 8) ∧
  (∀ y : Y, y ≠ 0 → qY y = 0 → Module.finrank K (LinearMap.range (β.flip y)) = 4 ∧
    ∀ v ∈ LinearMap.range (β.flip y), StatedQuadPlus 4 K v = 0) ∧
  (∀ x : X, x ≠ 0 → qX x ≠ 0 → Module.finrank K (LinearMap.range (β x)) = 8) ∧
  (∀ x : X, x ≠ 0 → qX x = 0 → Module.finrank K (LinearMap.range (β x)) = 4 ∧
    ∀ v ∈ LinearMap.range (β x), StatedQuadPlus 4 K v = 0) ∧
  (∀ y : Y, y ≠ 0 → qY y = 0 → ∀ x ∈ LinearMap.ker (β.flip y), qX x = 0) ∧
  (∀ x : X, x ≠ 0 → qX x = 0 → ∀ y ∈ LinearMap.ker (β x), qY y = 0) ∧
  (∀ y y' : Y, y ≠ 0 → y' ≠ 0 → qY y = 0 → qY y' = 0 →
    (LinearMap.range (β.flip y) = LinearMap.range (β.flip y') ∨
      LinearMap.ker (β.flip y) = LinearMap.ker (β.flip y')) → ∃ c : K, y' = c • y) ∧
  (∀ x x' : X, x ≠ 0 → x' ≠ 0 → qX x = 0 → qX x' = 0 →
    (LinearMap.range (β x) = LinearMap.range (β x') ∨
      LinearMap.ker (β x) = LinearMap.ker (β x')) → ∃ c : K, x' = c • x) ∧
  (∀ y y' : Y, y ≠ 0 → y' ≠ 0 → qY y = 0 → qY y' = 0 →
    Even (Module.finrank K ↥(LinearMap.range (β.flip y) ⊓ LinearMap.range (β.flip y')))) ∧
  (∀ x x' : X, x ≠ 0 → x' ≠ 0 → qX x = 0 → qX x' = 0 →
    Even (Module.finrank K ↥(LinearMap.range (β x) ⊓ LinearMap.range (β x')))) ∧
  ∀ (x : X) (y : Y), x ≠ 0 → y ≠ 0 → qX x = 0 → qY y = 0 →
    Odd (Module.finrank K ↥(LinearMap.range (β x) ⊓ LinearMap.range (β.flip y)))

variable [CharP K 2]

theorem ranks_of_zorn (eX : X ≃ₗ[K] Oct K) (eY : Y ≃ₗ[K] Oct K)
    (eV : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] Oct K) (hV : ∀ v, octNorm (eV v) = StatedQuadPlus 4 K v)
    {l : K} (hl : l ≠ 0) (β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hβ : ∀ x y, eV (β x y) = l • octMul (eX x) (eY y))
    {qX : QuadraticForm K X} {qY : QuadraticForm K Y} {μX μY : K} (hμX : μX ≠ 0)
    (hμY : μY ≠ 0) (hqX : ∀ x, qX x = μX * octNorm (eX x))
    (hqY : ∀ y, qY y = μY * octNorm (eY y)) : TrialityRanks β qX qY := by
  have hβy : ∀ y x, eV ((β.flip y) x) = l • (octMulBil.flip (eY y)) (eX x) := fun y x => by
    simpa using hβ x y
  have hβx : ∀ x y, eV ((β x) y) = l • (octMulBil (eX x)) (eY y) := fun x y => by
    simpa using hβ x y
  have hqXz : ∀ x, qX x = 0 ↔ octNorm (eX x) = 0 := fun x => by
    rw [hqX, mul_eq_zero]
    exact ⟨fun h => h.resolve_left hμX, Or.inr⟩
  have hqYz : ∀ y, qY y = 0 ↔ octNorm (eY y) = 0 := fun y => by
    rw [hqY, mul_eq_zero]
    exact ⟨fun h => h.resolve_left hμY, Or.inr⟩
  have hx0 : ∀ x, x ≠ 0 → eX x ≠ 0 := fun x hx h => hx (eX.map_eq_zero_iff.1 h)
  have hy0 : ∀ y, y ≠ 0 → eY y ≠ 0 := fun y hy h => hy (eY.map_eq_zero_iff.1 h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y _ hqy
    rw [finrank_range_eq eX eV hl (hβy y)]
    exact finrank_range_mulRight_of_norm_ne_zero (fun h => hqy ((hqYz y).2 h))
  · intro y hy hqy
    have hyN := (hqYz y).1 hqy
    refine ⟨?_, ?_⟩
    · rw [finrank_range_eq eX eV hl (hβy y)]
      exact finrank_range_mulRight_of_singular (hy0 y hy) hyN
    · rintro v ⟨x, rfl⟩
      rw [← hV, hβy y x]
      simp only [LinearMap.flip_apply, octMulBil_apply]
      rw [octNorm_smul, octNorm_mul, hyN, mul_zero, mul_zero]
  · intro x _ hqx
    rw [finrank_range_eq eY eV hl (hβx x)]
    exact finrank_range_mulLeft_of_norm_ne_zero (fun h => hqx ((hqXz x).2 h))
  · intro x hx hqx
    have hxN := (hqXz x).1 hqx
    refine ⟨?_, ?_⟩
    · rw [finrank_range_eq eY eV hl (hβx x)]
      exact finrank_range_mulLeft_of_singular (hx0 x hx) hxN
    · rintro v ⟨y, rfl⟩
      rw [← hV, hβx x y]
      simp only [octMulBil_apply]
      rw [octNorm_smul, octNorm_mul, hxN, zero_mul, mul_zero]
  · intro y hy hqy x hx
    have hmem : eX x ∈ LinearMap.ker (octMulBil.flip (eY y)) := by
      rw [ker_eq_comap eX eV hl (hβy y)] at hx
      exact hx
    exact (hqXz x).2 (octNorm_eq_zero_of_mem_ker_mulRight (hy0 y hy) ((hqYz y).1 hqy) hmem)
  · intro x hx hqx y hy
    have hmem : eY y ∈ LinearMap.ker (octMulBil (eX x)) := by
      rw [ker_eq_comap eY eV hl (hβx x)] at hy
      exact hy
    exact (hqYz y).2 (octNorm_eq_zero_of_mem_ker_mulLeft (hx0 x hx) ((hqXz x).1 hqx) hmem)
  · intro y y' hy hy' hqy hqy' h
    have h' : LinearMap.range (octMulBil.flip (eY y)) = LinearMap.range (octMulBil.flip (eY y')) ∨
        LinearMap.ker (octMulBil.flip (eY y)) = LinearMap.ker (octMulBil.flip (eY y')) := by
      rcases h with h | h
      · left
        rw [range_eq_map_symm eX eV hl (hβy y), range_eq_map_symm eX eV hl (hβy y')] at h
        exact Submodule.map_injective_of_injective eV.symm.injective h
      · right
        rw [ker_eq_comap eX eV hl (hβy y), ker_eq_comap eX eV hl (hβy y')] at h
        exact Submodule.comap_injective_of_surjective eX.surjective h
    obtain ⟨c, hc⟩ := exists_smul_eq_of_mulRight_eq (hy0 y hy) ((hqYz y).1 hqy) (hy0 y' hy')
      ((hqYz y').1 hqy') h'
    exact ⟨c, eY.injective (by rw [map_smul]; exact hc)⟩
  · intro x x' hx hx' hqx hqx' h
    have h' : LinearMap.range (octMulBil (eX x)) = LinearMap.range (octMulBil (eX x')) ∨
        LinearMap.ker (octMulBil (eX x)) = LinearMap.ker (octMulBil (eX x')) := by
      rcases h with h | h
      · left
        rw [range_eq_map_symm eY eV hl (hβx x), range_eq_map_symm eY eV hl (hβx x')] at h
        exact Submodule.map_injective_of_injective eV.symm.injective h
      · right
        rw [ker_eq_comap eY eV hl (hβx x), ker_eq_comap eY eV hl (hβx x')] at h
        exact Submodule.comap_injective_of_surjective eY.surjective h
    obtain ⟨c, hc⟩ := exists_smul_eq_of_mulLeft_eq (hx0 x hx) ((hqXz x).1 hqx) (hx0 x' hx')
      ((hqXz x').1 hqx') h'
    exact ⟨c, eX.injective (by rw [map_smul]; exact hc)⟩
  · intro y y' hy hy' hqy hqy'
    rw [finrank_range_inf_eq eX eX eV hl (hβy y) (hβy y')]
    exact even_finrank_range_mulRight_inf (hy0 y hy) ((hqYz y).1 hqy) (hy0 y' hy')
      ((hqYz y').1 hqy')
  · intro x x' hx hx' hqx hqx'
    rw [finrank_range_inf_eq eY eY eV hl (hβx x) (hβx x')]
    exact even_finrank_range_mulLeft_inf (hx0 x hx) ((hqXz x).1 hqx) (hx0 x' hx')
      ((hqXz x').1 hqx')
  · intro x y hx hy hqx hqy
    rw [finrank_range_inf_eq eY eX eV hl (hβx x) (hβy y)]
    exact odd_finrank_range_mulLeft_inf_mulRight (hx0 x hx) ((hqXz x).1 hqx) (hy0 y hy)
      ((hqYz y).1 hqy)

theorem polar_octQuad_comp {S : Type*} [AddCommGroup S] [Module K S] (e : S ≃ₗ[K] Oct K)
    (x y : S) : QuadraticMap.polar ((octQuad K).comp (e : S →ₗ[K] Oct K)) x y =
      octPolar (e x) (e y) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add,
    octQuad_apply, octPolar]

theorem eq_zero_of_polar_octQuad_comp {S : Type*} [AddCommGroup S] [Module K S]
    (e : S ≃ₗ[K] Oct K) {x : S}
    (hx : ∀ x' : S, QuadraticMap.polar ((octQuad K).comp (e : S →ₗ[K] Oct K)) x x' = 0) :
    x = 0 := by
  have h : ∀ y : Oct K, octPolar (e x) y = 0 := by
    intro y
    have := hx (e.symm y)
    rwa [polar_octQuad_comp, LinearEquiv.apply_symm_apply] at this
  have h0 : e x = 0 := octPolarBil_nondegenerate.1 (e x) (fun y => h y)
  exact e.injective (by rw [h0, map_zero])

theorem clauses_of_zorn (eX : X ≃ₗ[K] Oct K) (eY : Y ≃ₗ[K] Oct K)
    (eV : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] Oct K) (hV : ∀ v, octNorm (eV v) = StatedQuadPlus 4 K v)
    {l : K} (hl : l ≠ 0) (β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hβ : ∀ x y, eV (β x y) = l • octMul (eX x) (eY y))
    (PX : QuadraticForm K X → Prop) (PY : QuadraticForm K Y → Prop)
    (hPX0 : PX ((octQuad K).comp (eX : X →ₗ[K] Oct K)))
    (hPY0 : PY ((octQuad K).comp (eY : Y →ₗ[K] Oct K)))
    (hPX : ∀ q, PX q → ∃ μ : K, ∀ x, q x = μ * octNorm (eX x))
    (hPY : ∀ q, PY q → ∃ μ : K, ∀ y, q y = μ * octNorm (eY y)) :
    (∃ qX : QuadraticForm K X, PX qX ∧
      ∀ x : X, (∀ x' : X, QuadraticMap.polar qX x x' = 0) → x = 0) ∧
    (∃ qY : QuadraticForm K Y, PY qY ∧
      ∀ y : Y, (∀ y' : Y, QuadraticMap.polar qY y y' = 0) → y = 0) ∧
    ∀ (qX : QuadraticForm K X) (qY : QuadraticForm K Y), PX qX → PY qY → qX ≠ 0 → qY ≠ 0 →
      TrialityRanks β qX qY := by
  refine ⟨⟨_, hPX0, fun x hx => eq_zero_of_polar_octQuad_comp eX hx⟩,
    ⟨_, hPY0, fun y hy => eq_zero_of_polar_octQuad_comp eY hy⟩, ?_⟩
  intro qX qY hqX hqY hX0 hY0
  obtain ⟨μX, hμX⟩ := hPX qX hqX
  obtain ⟨μY, hμY⟩ := hPY qY hqY
  have hμX0 : μX ≠ 0 := by
    rintro rfl
    exact hX0 (QuadraticMap.ext fun x => by rw [hμX x, zero_mul]; rfl)
  have hμY0 : μY ≠ 0 := by
    rintro rfl
    exact hY0 (QuadraticMap.ext fun y => by rw [hμY y, zero_mul]; rfl)
  exact ranks_of_zorn eX eY eV hV hl β hβ hμX0 hμY0 hμX hμY

end Ranks

section Coord

variable {G : Type*} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem octNorm_funCongrLeft {e : ℕ} (P : ZLabPair e) (v : Fin 4 ⊕ Fin 4 → K) :
    octNorm (LinearEquiv.funCongrLeft K K P.σ v) = StatedQuadPlus 4 K v := by
  rw [octNorm_eq_statedQuadPlus]
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases P.σ_pair i with ⟨h1 | h1, h2⟩
  · rw [h2, h1]
    rfl
  · rw [h2, h1]
    exact mul_comm _ _

theorem ZLabPair.σ_σ {e : ℕ} (P : ZLabPair e) (m : Fin 4 ⊕ Fin 4) : P.σ (P.σ m) = m := by
  rcases m with i | i
  · rcases P.σ_pair i with ⟨h1 | h1, h2⟩
    · rw [h1, h1]
    · have h3 : P.σ (.inr i) = .inl i := by rw [h2, h1]; rfl
      rw [h1, h3]
  · rcases P.σ_pair i with ⟨h1 | h1, h2⟩
    · have h3 : P.σ (.inr i) = .inr i := by rw [h2, h1]; rfl
      rw [h3, h3]
    · have h3 : P.σ (.inr i) = .inl i := by rw [h2, h1]; rfl
      rw [h3, h1]

theorem ZLabPair.σ_apply_eq_iff {e : ℕ} (P : ZLabPair e) (j x : Fin 4 ⊕ Fin 4) :
    P.σ j = x ↔ j = P.σ x :=
  ⟨fun h => by rw [← h, P.σ_σ], fun h => by rw [h, P.σ_σ]⟩

theorem funCongrLeft_single {e : ℕ} (P : ZLabPair e) (x : Fin 4 ⊕ Fin 4) :
    LinearEquiv.funCongrLeft K K P.σ (Pi.single x 1 : Fin 4 ⊕ Fin 4 → K) =
      Pi.single (P.σ x) 1 := by
  funext j
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply,
    Pi.single_apply]
  exact if_congr (P.σ_apply_eq_iff _ _) rfl rfl

theorem natBasis_zSgn (hN : 3 ≤ Nat.card Kˣ) (k : Fin 4) (r : Bool) :
    natBasis (Pi.single k (zSgn (ZMod (Nat.card Kˣ)) r) : Fin 4 → ZMod (Nat.card Kˣ)) =
      (Pi.single (natIdx k r) 1 : Fin 4 ⊕ Fin 4 → K) := by
  cases r
  · exact natBasis_single_neg_one hN k
  · exact natBasis_single_one hN k

variable {D : D4Datum G K} {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y]
  [Module K Y] {ρX : Representation K G X} {ρY : Representation K G Y}
  {CX CY : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
  {bX : (Fin 4 → ZMod (Nat.card Kˣ)) → X} {bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y}
  {b₀ : ZMod (Nat.card Kˣ)} {e : ℕ}

theorem relabel_beta_basis (P : ZLabPair e) (hNX : SpinNF D ρX e b₀ CX bX)
    (hNY : SpinNF D ρY (1 - e) b₀ CY bY) (hN3 : 3 ≤ Nat.card Kˣ) {l : K}
    (β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hβ : ∀ a ∈ CX, ∀ b ∈ CY,
      β (bX a) (bY b) = if a + b ∈ natWts (K := K) then l • natBasis (a + b) else 0)
    (m n : Fin 4 ⊕ Fin 4) :
    LinearEquiv.funCongrLeft K K P.σ (β (hNX.basis P.X m) (hNY.basis P.Y n)) =
      l • octMul (Pi.single m 1 : Oct K) (Pi.single n 1) := by
  haveI := hNX.nontrivial
  rw [hNX.basis_apply, hNY.basis_apply, hβ _ (hNX.hsWeight_mem _ m) _ (hNY.hsWeight_mem _ n),
    octMul_single_single]
  by_cases hadm : ∃ k, ∀ i, P.X.lab m i = P.Y.lab n i ↔ i = k
  · obtain ⟨k, hk⟩ := hadm
    have hsum := hsWeight_add_hsWeight_of_agree hNX.two_mul hk
    have hmem : (Pi.single k (zSgn (ZMod (Nat.card Kˣ)) (P.X.lab m k)) :
        Fin 4 → ZMod (Nat.card Kˣ)) ∈ natWts (K := K) := by
      rw [mem_natWts]
      refine ⟨k, ?_⟩
      cases P.X.lab m k
      · exact Or.inr rfl
      · exact Or.inl rfl
    rw [hsum, if_pos hmem, natBasis_zSgn hN3, P.mul_some m n k hk]
    simp only [Option.elim_some, map_smul, funCongrLeft_single]
  · have hnot : ¬ (hsWeight b₀ (P.X.lab m) + hsWeight b₀ (P.Y.lab n) ∈ natWts (K := K)) := by
      intro hmem
      obtain ⟨k, hk⟩ := mem_natWts.1 hmem
      apply hadm
      rcases hk with hk | hk
      · exact ⟨k, agree_of_hsWeight_add hNX.two_mul (r := true) hk⟩
      · exact ⟨k, agree_of_hsWeight_add hNX.two_mul (r := false) hk⟩
    rw [if_neg hnot, P.mul_none m n hadm]
    simp

end Coord

theorem clauses_of_coord {G : Type*} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (D : D4Datum G K)
    {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    {ρX : Representation K G X} {ρY : Representation K G Y}
    {CX CY : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
    {bX : (Fin 4 → ZMod (Nat.card Kˣ)) → X} {bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y}
    (hX : NF D ρX 0 CX bX) (hY : NF D ρY 0 CY bY)
    {b₀ : ZMod (Nat.card Kˣ)} {e : ℕ} (hb₀ : 2 * b₀ = 1) (he : e < 2)
    (hCX : ∀ a, a ∈ CX ↔ IsSpinWt b₀ e a) (hCY : ∀ a, a ∈ CY ↔ IsSpinWt b₀ (1 - e) a)
    (β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) {l : K} (hl : l ≠ 0)
    (hβ : ∀ a ∈ CX, ∀ b ∈ CY,
      β (bX a) (bY b) = if a + b ∈ natWts (K := K) then l • natBasis (a + b) else 0) :
    (∃ qX : QuadraticForm K X, (∀ (g : G) (x : X), qX (ρX g x) = qX x) ∧
      ∀ x : X, (∀ x' : X, QuadraticMap.polar qX x x' = 0) → x = 0) ∧
    (∃ qY : QuadraticForm K Y, (∀ (g : G) (y : Y), qY (ρY g y) = qY y) ∧
      ∀ y : Y, (∀ y' : Y, QuadraticMap.polar qY y y' = 0) → y = 0) ∧
    ∀ (qX : QuadraticForm K X) (qY : QuadraticForm K Y),
      (∀ (g : G) (x : X), qX (ρX g x) = qX x) → (∀ (g : G) (y : Y), qY (ρY g y) = qY y) →
      qX ≠ 0 → qY ≠ 0 →
      (∀ y : Y, y ≠ 0 → qY y ≠ 0 → Module.finrank K (LinearMap.range (β.flip y)) = 8) ∧
      (∀ y : Y, y ≠ 0 → qY y = 0 → Module.finrank K (LinearMap.range (β.flip y)) = 4 ∧
        ∀ v ∈ LinearMap.range (β.flip y), StatedQuadPlus 4 K v = 0) ∧
      (∀ x : X, x ≠ 0 → qX x ≠ 0 → Module.finrank K (LinearMap.range (β x)) = 8) ∧
      (∀ x : X, x ≠ 0 → qX x = 0 → Module.finrank K (LinearMap.range (β x)) = 4 ∧
        ∀ v ∈ LinearMap.range (β x), StatedQuadPlus 4 K v = 0) ∧
      (∀ y : Y, y ≠ 0 → qY y = 0 → ∀ x ∈ LinearMap.ker (β.flip y), qX x = 0) ∧
      (∀ x : X, x ≠ 0 → qX x = 0 → ∀ y ∈ LinearMap.ker (β x), qY y = 0) ∧
      (∀ y y' : Y, y ≠ 0 → y' ≠ 0 → qY y = 0 → qY y' = 0 →
        (LinearMap.range (β.flip y) = LinearMap.range (β.flip y') ∨
          LinearMap.ker (β.flip y) = LinearMap.ker (β.flip y')) → ∃ c : K, y' = c • y) ∧
      (∀ x x' : X, x ≠ 0 → x' ≠ 0 → qX x = 0 → qX x' = 0 →
        (LinearMap.range (β x) = LinearMap.range (β x') ∨
          LinearMap.ker (β x) = LinearMap.ker (β x')) → ∃ c : K, x' = c • x) ∧
      (∀ y y' : Y, y ≠ 0 → y' ≠ 0 → qY y = 0 → qY y' = 0 →
        Even (Module.finrank K ↥(LinearMap.range (β.flip y) ⊓ LinearMap.range (β.flip y')))) ∧
      (∀ x x' : X, x ≠ 0 → x' ≠ 0 → qX x = 0 → qX x' = 0 →
        Even (Module.finrank K ↥(LinearMap.range (β x) ⊓ LinearMap.range (β x')))) ∧
      ∀ (x : X) (y : Y), x ≠ 0 → y ≠ 0 → qX x = 0 → qY y = 0 →
        Odd (Module.finrank K ↥(LinearMap.range (β x) ⊓ LinearMap.range (β.flip y))) := by
  have hN3 : 3 ≤ Nat.card Kˣ := by rw [Nat.card_units]; omega
  have hNX : SpinNF D ρX e b₀ CX bX := ⟨hb₀, by omega, hCX, hX⟩
  have hNY : SpinNF D ρY (1 - e) b₀ CY bY := ⟨hb₀, by omega, hCY, hY⟩
  let P := zlabPair e he
  have hβ' : ∀ x y, LinearEquiv.funCongrLeft K K P.σ (β x y) =
      l • octMul (hNX.equiv P.X x) (hNY.equiv P.Y y) := by
    have hB : β.compr₂ (LinearEquiv.funCongrLeft K K P.σ).toLinearMap =
        l • (octMulBil.compl₁₂ (hNX.equiv P.X).toLinearMap (hNY.equiv P.Y).toLinearMap) :=
      LinearMap.ext_basis (hNX.basis P.X) (hNY.basis P.Y) fun m n => by
        simp only [LinearMap.compr₂_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
          LinearMap.compl₁₂_apply, octMulBil_apply, hNX.equiv_basis P.X, hNY.equiv_basis P.Y]
        exact relabel_beta_basis P hNX hNY hN3 β hβ m n
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simpa using this
  exact clauses_of_zorn (hNX.equiv P.X) (hNY.equiv P.Y) (LinearEquiv.funCongrLeft K K P.σ)
    (octNorm_funCongrLeft P) hl β hβ' (fun q => ∀ (g : G) (x : X), q (ρX g x) = q x)
    (fun q => ∀ (g : G) (y : Y), q (ρY g y) = q y) (hNX.quad_invariant P.X)
    (hNY.quad_invariant P.Y) (fun q hq => hNX.exists_eq_mul_octNorm P.X hq)
    (fun q hq => hNY.exists_eq_mul_octNorm P.Y hq)

end CFSG.RankThree.GF2n.Stroth80.Tri

end
