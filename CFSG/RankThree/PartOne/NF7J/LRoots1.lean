module

public import CFSG.RankThree.PartOne.NF7J.LFrame
public import CFSG.RankThree.PartOne.SP4C.GAL
public import CFSG.RankThree.PartOne.NF7J.Sp4Oct

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.SP4C
open scoped commutatorElement

structure RFrame (G : Type) [Group G] [Finite G] (p : ℕ) (c : G) (L E : Subgroup G) (f : ℕ)
    (K : Type) [Field K] [Finite K] [CharP K 2] where
  ε : ↥L →* StatedProj (StatedSp 2 K)
  hε : IsCentralPQuot p ε
  hZ : Subgroup.center L = ⊥
  card : Nat.card K = 2 ^ f
  ζ : Kˣ
  hζ : IsPrimitiveRoot ζ p
  hcL : ∀ y ∈ L, c * y = y * c
  hEA : E ≤ Subgroup.zpowers c ⊔ (E ⊓ L)
  tor : ((E ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K)
  r₀ : MulAut E
  r₁ : MulAut E
  r₀_ref : r₀ ∈ reflectionSet p E
  r₀_L : r₀ ∈ torusImage E L
  r₁_ref : r₁ ∈ reflectionSet p E
  r₁_L : r₁ ∈ torusImage E L
  ord : orderOf (r₀ * r₁) = 4
  kfat₀ : KFAt p E f r₀
  kfat₁ : KFAt p E f r₁
  le₀ : kZero p E r₀ ≤ L
  le₁ : kZero p E r₁ ≤ L
  map₀ : ((kZero p E r₀).subgroupOf L).map ε = (spBlock (K := K)).range.map (spQ K)
  map₁ : ((kZero p E r₁).subgroupOf L).map ε = (spBlock' (K := K)).range.map (spQ K)

section Exists

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem exists_rframe (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nonempty (RFrame G p c L E f K) := by
  classical
  obtain ⟨hZL, K, hKf, hKfin, hchar, hK, ε, hε, ζ, hζ, hAT, r₀, r₁, h0, h0L, h1, h1L, hord, hk0, hk1,
    hle0, hle1, hmap0, hmap1⟩ := nf7j_frame hGA h hF hF13 hEA hf1 hpq hmod
  have hG : Sec12TwoGeneric p c L E := KF132.sec12TwoGeneric_of_center_bot hF hZL
  subst hEA
  refine ⟨K, hKf, hKfin, hchar, ⟨?_⟩⟩
  exact
    { ε := ε
      hε := hε
      hZ := hZL
      card := hK
      ζ := ζ
      hζ := hζ
      hcL := fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (h.L_le_centralizer hy)).symm
      hEA := by
        have := hG.E_eq
        rw [sup_comm] at this
        exact this.le
      tor := hAT
      r₀ := r₀
      r₁ := r₁
      r₀_ref := h0
      r₀_L := h0L
      r₁_ref := h1
      r₁_L := h1L
      ord := hord
      kfat₀ := hk0
      kfat₁ := hk1
      le₀ := hle0
      le₁ := hle1
      map₀ := hmap0
      map₁ := hmap1 }

end Exists

theorem spQ_injective' (K : Type) [Field K] [Finite K] [CharP K 2] : Function.Injective (spQ K) :=
  fun _ _ h => (spQe K).injective h

namespace RFrame

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K)

theorem ε_injective : Function.Injective F.ε := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_eq_center F.hε, F.hZ]

@[expose] noncomputable def lam : ↥L ≃* ↥(spRev K) :=
  (MulEquiv.ofBijective F.ε ⟨F.ε_injective, F.hε.surjective⟩).trans (spQe K).symm

theorem spQ_lam (x : ↥L) : spQ K (F.lam x) = F.ε x := by
  show spQe K ((spQe K).symm (F.ε x)) = F.ε x
  exact (spQe K).apply_symm_apply _

theorem ε_mem_map_iff (S : Subgroup ↥(spRev K)) (x : ↥L) : F.ε x ∈ S.map (spQ K) ↔ F.lam x ∈ S := by
  rw [← F.spQ_lam x]
  exact Subgroup.mem_map_iff_mem (spQ_injective' K)

@[expose] noncomputable def rgHom : ↥(spRev K) →* G := L.subtype.comp F.lam.symm.toMonoidHom

theorem rgHom_apply (t : ↥(spRev K)) : F.rgHom t = ((F.lam.symm t : ↥L) : G) := rfl

theorem rgHom_injective : Function.Injective F.rgHom := fun _ _ h =>
  F.lam.symm.injective (Subtype.ext h)

theorem rgHom_mem (t : ↥(spRev K)) : F.rgHom t ∈ L := (F.lam.symm t).2

theorem rgHom_lam (x : ↥L) : F.rgHom (F.lam x) = (x : G) := by
  rw [rgHom_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def rg (j : Fin 8) : Subgroup G := (octSub K j).map F.rgHom

theorem mem_rg {j : Fin 8} {g : G} : g ∈ F.rg j ↔ ∃ s : K, g = F.rgHom (octEl j s) := by
  unfold rg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, rfl⟩ := mem_octSub_iff.1 ht
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨octEl j s, octEl_mem j s, rfl⟩

theorem rg_le_L (j : Fin 8) : F.rg j ≤ L := by
  intro g hg
  obtain ⟨s, rfl⟩ := F.mem_rg.1 hg
  exact F.rgHom_mem _

theorem rg_sq {j : Fin 8} {g : G} (hg : g ∈ F.rg j) : g * g = 1 := by
  obtain ⟨s, rfl⟩ := F.mem_rg.1 hg
  rw [← map_mul, octEl_sq, map_one]

theorem card_rg (j : Fin 8) : Nat.card (F.rg j) = 2 ^ f := by
  unfold rg
  rw [Subgroup.card_map_of_injective F.rgHom_injective, octSub_card, F.card]

theorem rg_comm {i j : Fin 8} (h : ¬ OctNC i j) :
    ∀ x ∈ F.rg i, ∀ y ∈ F.rg j, x * y = y * x := by
  intro x hx y hy
  obtain ⟨s, rfl⟩ := F.mem_rg.1 hx
  obtain ⟨t, rfl⟩ := F.mem_rg.1 hy
  rw [← map_mul, ← map_mul, octEl_comm h]

theorem rg_ncomm {i j : Fin 8} (h : OctNC i j) : ∃ x ∈ F.rg i, ∃ y ∈ F.rg j, x * y ≠ y * x := by
  obtain ⟨x, hx, y, hy, hxy⟩ := octSub_ncomm (K := K) h
  refine ⟨F.rgHom x, ⟨x, hx, rfl⟩, F.rgHom y, ⟨y, hy, rfl⟩, fun h' => hxy ?_⟩
  apply F.rgHom_injective
  rw [map_mul, map_mul]
  exact h'

theorem rg_gen (j : Fin 8) {t₀ : K} (h0 : t₀ ≠ 0) (h1 : t₀ ≠ 1) :
    F.rg (j + 1) ≤ ⁅F.rg j, F.rg (j + 3)⁆ ∧ F.rg (j + 2) ≤ ⁅F.rg j, F.rg (j + 3)⁆ := by
  obtain ⟨hA, hB⟩ := octSub_gen (K := K) j h0 h1
  unfold rg
  rw [← Subgroup.map_commutator]
  exact ⟨Subgroup.map_mono hA, Subgroup.map_mono hB⟩

theorem mem_normalizer_rg_of {j : Fin 8} {x : ↥L}
    (hx : F.lam x ∈ Subgroup.normalizer (octSub K j : Set ↥(spRev K))) :
    (x : G) ∈ Subgroup.normalizer (F.rg j : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨s, rfl⟩ := F.mem_rg.1 hg
    obtain ⟨s', hs'⟩ := mem_octSub_iff.1 ((Subgroup.mem_normalizer_iff.1 hx (octEl j s)).1 (octEl_mem j s))
    refine F.mem_rg.2 ⟨s', ?_⟩
    rw [← hs', ← F.rgHom_lam x, ← map_inv, ← map_mul, ← map_mul]
  · intro hg
    obtain ⟨s, hs⟩ := F.mem_rg.1 hg
    have hx' := Subgroup.mem_normalizer_iff.1 hx
    have h1 : (F.lam x)⁻¹ * octEl j s * F.lam x ∈ octSub K j := by
      have := (hx' ((F.lam x)⁻¹ * octEl j s * F.lam x)).2
      have e : F.lam x * ((F.lam x)⁻¹ * octEl j s * F.lam x) * (F.lam x)⁻¹ = octEl j s := by group
      rw [e] at this
      exact this (octEl_mem j s)
    have hg' : g = F.rgHom ((F.lam x)⁻¹ * octEl j s * F.lam x) := by
      rw [map_mul, map_mul, map_inv, F.rgHom_lam x, ← hs]
      group
    rw [hg']
    exact ⟨_, h1, rfl⟩

theorem inf_le_normalizer_rg (j : Fin 8) :
    E ⊓ L ≤ Subgroup.normalizer (F.rg j : Set G) := by
  intro g hg
  have hgL : g ∈ L := hg.2
  set x : ↥L := ⟨g, hgL⟩ with hx
  have h1 : x ∈ (E ⊓ L).subgroupOf L := hg
  have h2 : F.ε x ∈ (torus7 p K).map (spQ K) := by
    rw [← F.tor]
    exact ⟨x, h1, rfl⟩
  have h3 : F.lam x ∈ torus7 p K := (F.ε_mem_map_iff _ x).1 h2
  obtain ⟨a, b, -, -, hab⟩ := mem_torus7_iff.1 h3
  have h4 : F.lam x = spDiag K (a, b) := Subtype.ext hab
  exact F.mem_normalizer_rg_of (by rw [h4]; exact spDiag_mem_normalizer_octSub j a b)

theorem E_le_normalizer_rg (j : Fin 8) : E ≤ Subgroup.normalizer (F.rg j : Set G) := by
  refine F.hEA.trans (sup_le ?_ (F.inf_le_normalizer_rg j))
  rw [Subgroup.zpowers_le]
  have hc : c ∈ Subgroup.centralizer (F.rg j : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (F.hcL s (F.rg_le_L j hs)).symm
  exact Subgroup.centralizer_le_normalizer (F.rg j : Set G) hc

theorem rg_conj_E {j : Fin 8} {a : G} (ha : a ∈ E) {s : G} (hs : s ∈ F.rg j) : a * s * a⁻¹ ∈ F.rg j :=
  (Subgroup.mem_normalizer_iff.1 (F.E_le_normalizer_rg j ha) s).1 hs

theorem rgHom_mem_E {t : ↥(spRev K)} (ht : t ∈ torus7 p K) : F.rgHom t ∈ E := by
  set x : ↥L := F.lam.symm t with hx
  have h1 : F.ε x ∈ ((E ⊓ L).subgroupOf L).map F.ε := by
    rw [F.tor]
    refine ⟨t, ht, ?_⟩
    rw [← F.spQ_lam x, hx, MulEquiv.apply_symm_apply]
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = x := F.ε_injective hyx
  rw [this] at hy
  have : F.rgHom t = (x : G) := by rw [hx, rgHom_apply]
  rw [this]
  exact (Subgroup.mem_inf.1 hy).1

theorem kZero_r₀_eq : kZero p E F.r₀ = (spBlock (K := K)).range.map F.rgHom := by
  ext g
  constructor
  · intro hg
    have hgL : g ∈ L := F.le₀ hg
    set x : ↥L := ⟨g, hgL⟩ with hx
    have h1 : F.ε x ∈ ((kZero p E F.r₀).subgroupOf L).map F.ε := ⟨x, hg, rfl⟩
    rw [F.map₀, F.ε_mem_map_iff] at h1
    exact ⟨F.lam x, h1, F.rgHom_lam x⟩
  · rintro ⟨t, ht, rfl⟩
    set x : ↥L := F.lam.symm t with hx
    have h1 : F.ε x ∈ (spBlock (K := K)).range.map (spQ K) := by
      rw [F.ε_mem_map_iff, hx, MulEquiv.apply_symm_apply]
      exact ht
    rw [← F.map₀] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := F.ε_injective hyx
    rw [this] at hy
    exact hy

theorem kZero_r₁_eq : kZero p E F.r₁ = (spBlock' (K := K)).range.map F.rgHom := by
  ext g
  constructor
  · intro hg
    have hgL : g ∈ L := F.le₁ hg
    set x : ↥L := ⟨g, hgL⟩ with hx
    have h1 : F.ε x ∈ ((kZero p E F.r₁).subgroupOf L).map F.ε := ⟨x, hg, rfl⟩
    rw [F.map₁, F.ε_mem_map_iff] at h1
    exact ⟨F.lam x, h1, F.rgHom_lam x⟩
  · rintro ⟨t, ht, rfl⟩
    set x : ↥L := F.lam.symm t with hx
    have h1 : F.ε x ∈ (spBlock' (K := K)).range.map (spQ K) := by
      rw [F.ε_mem_map_iff, hx, MulEquiv.apply_symm_apply]
      exact ht
    rw [← F.map₁] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := F.ε_injective hyx
    rw [this] at hy
    exact hy

@[expose] noncomputable def phi₀ : Matrix.SpecialLinearGroup (Fin 2) K →* G :=
  F.rgHom.comp (spBlock (K := K))

@[expose] noncomputable def phi₁ : Matrix.SpecialLinearGroup (Fin 2) K →* G :=
  F.rgHom.comp (spBlock' (K := K))

theorem phi₀_injective : Function.Injective F.phi₀ :=
  F.rgHom_injective.comp spBlock_injective

theorem phi₁_injective : Function.Injective F.phi₁ :=
  F.rgHom_injective.comp spBlock'_injective

theorem phi₀_range : F.phi₀.range = kZero p E F.r₀ := by
  rw [F.kZero_r₀_eq, phi₀, MonoidHom.range_comp, MonoidHom.range_eq_map]

theorem phi₁_range : F.phi₁.range = kZero p E F.r₁ := by
  rw [F.kZero_r₁_eq, phi₁, MonoidHom.range_comp, MonoidHom.range_eq_map]

theorem rg_zero_eq : F.rg 0 = (Uplus K).map F.phi₀ := by
  rw [rg, octSub_zero_eq, Subgroup.map_map]
  rfl

theorem rg_four_eq : F.rg 4 = (Uminus K).map F.phi₀ := by
  rw [rg, octSub_four_eq, Subgroup.map_map]
  rfl

theorem rg_seven_eq : F.rg 7 = (Uplus K).map F.phi₁ := by
  rw [rg, octSub_seven_eq, Subgroup.map_map]
  rfl

theorem rg_three_eq : F.rg 3 = (Uminus K).map F.phi₁ := by
  rw [rg, octSub_three_eq, Subgroup.map_map]
  rfl

omit [Finite K] [CharP K 2] in
theorem hmat_eq_diag2 (ζ : Kˣ) :
    (hmat ζ : Matrix.SpecialLinearGroup (Fin 2) K) = diag2 ζ := by
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diag2, e2, e2_hmat_00 ζ, e2_hmat_01 ζ, e2_hmat_10 ζ, e2_hmat_11 ζ]

theorem phi₀_hmat_mem_E : F.phi₀ (hmat F.ζ) ∈ E := by
  have hζp : F.ζ ^ p = 1 := F.hζ.pow_eq_one
  have : F.phi₀ (hmat F.ζ) = F.rgHom (rho7 F.ζ) := by
    rw [phi₀, MonoidHom.comp_apply, hmat_eq_diag2, spBlock_diag2]
  rw [this]
  exact F.rgHom_mem_E (rho7_mem_torus7 hζp)

theorem phi₁_hmat_mem_E : F.phi₁ (hmat F.ζ) ∈ E := by
  have hζp : F.ζ ^ p = 1 := F.hζ.pow_eq_one
  have h1 : spBlock' (hmat F.ζ : Matrix.SpecialLinearGroup (Fin 2) K) = spDiag K (F.ζ, F.ζ⁻¹) := by
    apply Subtype.ext
    apply Units.ext
    simp only [coe_spBlock', coe_spDiag, diagU_val]
    ext i j
    have h00 : ((hmat F.ζ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = F.ζ :=
      e2_hmat_00 F.ζ
    have h01 : ((hmat F.ζ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 :=
      e2_hmat_01 F.ζ
    have h10 : ((hmat F.ζ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
      e2_hmat_10 F.ζ
    have h11 : ((hmat F.ζ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (F.ζ : K)⁻¹ := e2_hmat_11 F.ζ
    fin_cases i <;> fin_cases j <;> simp [blk4, dvec4, h00, h01, h10, h11]
  have hmem : spDiag K (F.ζ, F.ζ⁻¹) ∈ torus7 p K :=
    mem_torus7_iff.2 ⟨F.ζ, F.ζ⁻¹, hζp, by rw [inv_pow, hζp, inv_one], rfl⟩
  have : F.phi₁ (hmat F.ζ) = F.rgHom (spDiag K (F.ζ, F.ζ⁻¹)) := by
    rw [phi₁, MonoidHom.comp_apply, h1]
  rw [this]
  exact F.rgHom_mem_E hmem

end RFrame

end CFSG.RankThree.PartOne.NF7J
