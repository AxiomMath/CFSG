module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneRestSeven

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggLe_sup_inf_of_noCentral {K R Y : Subgroup G} (hRK : R ≤ K) (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Y)
    (hNY : K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hY : Y ≤ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) ⊔
      Subgroup.centralizer (K : Set G))
    (hnc : ∀ A B' : Subgroup G, R ≤ A → A ≤ B' →
      B' ≤ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) →
      K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (A : Set G) →
      K ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (B' : Set G) →
      ⁅B', K ⊓ Subgroup.normalizer (R : Set G)⁆ ≤ A → B' ≤ A) :
    Y ≤ (Y ⊓ K) ⊔ (Y ⊓ Subgroup.centralizer (K : Set G)) := by
  set N := K ⊓ Subgroup.normalizer (R : Set G) with hN
  set Q₁ := pCoreOf 2 N with hQ₁
  set C := Subgroup.centralizer (K : Set G) with hC
  have hQ₁N : Q₁ ≤ N := Subgroup.map_subtype_le _
  have hQ₁K : Q₁ ≤ K := hQ₁N.trans inf_le_left
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := fun k hk =>
    mem_normalizer_centralizer (Subgroup.le_normalizer hk)
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) :=
    hY.trans (sup_le (hQ₁K.trans hKC) Subgroup.le_normalizer)
  have hNQ₁ : N ≤ Subgroup.normalizer (Q₁ : Set G) := fun n hn => mem_normalizer_pCoreOf hn
  have hRN : R ≤ N := le_inf hRK Subgroup.le_normalizer
  have hRQ₁ : R ≤ Q₁ := ggLe_pCoreOf_two hRN (fun n hn => (Subgroup.mem_inf.mp hn).2) hR2
  have hBA : Q₁ ⊓ (Y ⊔ C) ≤ Y ⊓ Q₁ := by
    refine hnc (Y ⊓ Q₁) (Q₁ ⊓ (Y ⊔ C)) (le_inf hRY hRQ₁) (fun a ha => Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp ha).2, Subgroup.mem_sup_left (Subgroup.mem_inf.mp ha).1⟩)
      inf_le_left ?_ ?_ ?_
    · intro n hn
      exact mem_normalizer_inf (hNY hn) (hNQ₁ hn)
    · intro n hn
      exact mem_normalizer_inf (hNQ₁ hn)
        (ggMem_normalizer_sup (hNY hn) (hKC (Subgroup.mem_inf.mp hn).1))
    · refine Subgroup.commutator_le.mpr fun b hb n hn => ?_
      obtain ⟨hbQ, hbYC⟩ := Subgroup.mem_inf.mp hb
      have hbYC' : b ∈ ((Y ⊔ C : Subgroup G) : Set G) := hbYC
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Y C hYC] at hbYC'
      obtain ⟨y, hy, c, hc, rfl⟩ := hbYC'
      have hnK : n ∈ K := (Subgroup.mem_inf.mp hn).1
      have hcn : c * n = n * c := (Subgroup.mem_centralizer_iff.mp hc n hnK).symm
      have heq : ⁅y * c, n⁆ = y * (n * y⁻¹ * n⁻¹) := by
        rw [commutatorElement_def]
        calc y * c * n * (y * c)⁻¹ * n⁻¹ = y * (c * n) * c⁻¹ * y⁻¹ * n⁻¹ := by group
          _ = y * (n * c) * c⁻¹ * y⁻¹ * n⁻¹ := by rw [hcn]
          _ = y * (n * y⁻¹ * n⁻¹) := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ggCommutatorElement_mem_left hbQ (hNQ₁ hn)⟩
      rw [heq]
      exact Y.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hNY hn) _).mp (Y.inv_mem hy))
  intro y hy
  have hy' : y ∈ ((Q₁ ⊔ C : Subgroup G) : Set G) := hY hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q₁ C (hQ₁K.trans hKC)] at hy'
  obtain ⟨k, hk, c, hc, rfl⟩ := hy'
  have hkB : k ∈ Q₁ ⊓ (Y ⊔ C) := by
    refine Subgroup.mem_inf.mpr ⟨hk, ?_⟩
    have hk' : k = (k * c) * c⁻¹ := by group
    rw [hk']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (C.inv_mem hc))
  have hkY : k ∈ Y := (Subgroup.mem_inf.mp (hBA hkB)).1
  have hcY : c ∈ Y := by
    have hc' : c = k⁻¹ * (k * c) := by group
    rw [hc']
    exact Y.mul_mem (Y.inv_mem hkY) hy
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hkY, hQ₁K hk⟩)
    (Subgroup.mem_inf.mpr ⟨hcY, hc⟩)

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.perD_of_inner (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {R : Subgroup G}
    (hRJ : R ≤ J) (hR2 : IsPGroup 2 R) {d : G} (hd : d ∈ D)
    (hP1 : ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      pCoreOf 2 (ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G)) ⊔
        Subgroup.centralizer (ggKd p B x L D J d : Set G))
    (hP2 : ∀ A B' : Subgroup G, R ≤ A → A ≤ B' →
      B' ≤ pCoreOf 2 (ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G)) →
      ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (A : Set G) →
      ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (B' : Set G) →
      ⁅B', ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G)⁆ ≤ A → B' ≤ A) :
    ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      (ggSR p B x L D J R ⊓ ggKd p B x L D J d) ⊔
        (ggSR p B x L D J R ⊓ Subgroup.centralizer (ggKd p B x L D J d : Set G)) := by
  have hRK : R ≤ ggKd p B x L D J d := hRJ.trans (le_ggKd p B x L D J d)
  have hRP : R ≤ ggPR R := ggLe_pCoreOf_two Subgroup.le_normalizer le_rfl hR2
  have hRN₀ : R ≤ ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) :=
    le_inf (hRJ.trans h.le_ggG0) Subgroup.le_normalizer
  have hRS : R ≤ ggSR p B x L D J R :=
    le_inf hRP fun r hr => mem_normalizer_pCoreOf (hRN₀ hr)
  have hRd : R ≤ Subgroup.centralizer {d} := (hRJ.trans (h.le_ggG0_inf hd)).trans inf_le_right
  have hNY : ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((ggSR p B x L D J R ⊓ Subgroup.centralizer {d} : Subgroup G) :
        Set G) := by
    intro m hm
    obtain ⟨hmK, hmR⟩ := Subgroup.mem_inf.mp hm
    have hmP : m ∈ Subgroup.normalizer (ggPR R : Set G) := mem_normalizer_pCoreOf hmR
    have hmN₀ : m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) :=
      Subgroup.mem_inf.mpr ⟨h.ggKd_le_ggG0 hd hmK, hmR⟩
    have hmQ : m ∈ Subgroup.normalizer (ggQR p B x L D J R : Set G) :=
      mem_normalizer_pCoreOf hmN₀
    have hmS : m ∈ Subgroup.normalizer (ggSR p B x L D J R : Set G) :=
      mem_normalizer_inf hmP (Subgroup.le_normalizer hmQ)
    exact mem_normalizer_inf hmS (Subgroup.le_normalizer (h.ggKd_le_centralizer hd hmK))
  exact (ggLe_sup_inf_of_noCentral hRK hR2 (le_inf hRS hRd) hNY hP1 hP2).trans
    (sup_le_sup (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_left))

end Ctx

end CFSG.StandardType
