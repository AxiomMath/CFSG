module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Out
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimQuad
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCForms
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.RankThree.GF2n.Stroth80

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private theorem s16g_isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ} {f : G →* H}
    (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  have := hE.1
  exact ⟨Subgroup.comap_injective_isMulCommutative E hf, fun x hx =>
    hf (by rw [map_pow, map_one]; exact hE.2 (f x) hx)⟩

theorem s16g_exists_matrix_elem_of_lin {Γ : Subgroup (GL ι K)} {p : ℕ}
    {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hEL : E ≤ s16gLin ι K) (hE : IsElemAbelian p E) :
    ∃ F : Subgroup (GL ι K), F ≤ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      IsElemAbelian p F ∧ Nat.card F = Nat.card E := by
  obtain ⟨F, hFN, hFE⟩ := s16g_exists_matrix_subgroup hEN hEL
  refine ⟨F, hFN, ?_, ?_⟩
  · refine (s16g_isElemAbelian_comap s16gNatHom_injective hE).mono fun x hx => ?_
    rw [Subgroup.mem_comap, ← hFE]
    exact Subgroup.mem_map_of_mem _ hx
  · rw [← hFE, Subgroup.card_map_of_injective s16gNatHom_injective]

theorem s16g_exists_ker_subgroup {Γ : Subgroup (GL ι K)} {C : Type*} [Group C] [Finite C]
    (μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* C) {F : Subgroup (GL ι K)}
    (hFN : F ≤ Subgroup.normalizer (Γ : Set (GL ι K))) :
    ∃ F₀ : Subgroup (GL ι K), F₀ ≤ F ∧ Nat.card F ≤ Nat.card C * Nat.card F₀ ∧
      ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), (x : GL ι K) ∈ F₀ → μ x = 1 := by
  let φ : ↥F →* C := μ.comp (Subgroup.inclusion hFN)
  refine ⟨φ.ker.map F.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.card_map_of_injective F.subtype_injective]
    exact s16g_card_le_mul_card_ker φ
  · rintro x ⟨y, hy, hyx⟩
    have hx : x = Subgroup.inclusion hFN y := Subtype.ext hyx.symm
    rw [hx]
    exact MonoidHom.mem_ker.1 hy

theorem s16g_mu_eq_one_of_coprime {Γ : Subgroup (GL ι K)} {C : Type*} [Group C] [Finite C]
    (μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* C) {F : Subgroup (GL ι K)}
    (hFN : F ≤ Subgroup.normalizer (Γ : Set (GL ι K))) {p : ℕ} (hp : p.Prime)
    (hF : IsPGroup p F) (hpC : ¬ p ∣ Nat.card C) :
    ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), (x : GL ι K) ∈ F → μ x = 1 := by
  intro x hx
  have h := DFunLike.congr_fun (s16g_hom_eq_one_of_coprime hp hF hpC
    (μ.comp (Subgroup.inclusion hFN))) ⟨x, hx⟩
  exact h

private theorem s16g_card_units_eight [Finite K] (hK : Nat.card K = 8) : Nat.card Kˣ = 7 := by
  rw [Nat.card_units, hK]

theorem s16g_exists_iso_elem_of_lin [Finite K] {Γ : Subgroup (GL ι K)} (hK : Nat.card K = 8)
    (μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* Kˣ) {p : ℕ} (hp : p.Prime) (hp7 : p ≠ 7)
    {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hEL : E ≤ s16gLin ι K) (hE : IsElemAbelian p E) :
    ∃ F : Subgroup (GL ι K), F ≤ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      IsElemAbelian p F ∧ Nat.card F = Nat.card E ∧
      ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), (x : GL ι K) ∈ F → μ x = 1 := by
  obtain ⟨F, hFN, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hE
  refine ⟨F, hFN, hF, hcard, s16g_mu_eq_one_of_coprime μ hFN hp hF.isPGroup ?_⟩
  rw [s16g_card_units_eight hK]
  exact fun h => hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem s16g_exists_iso_elem_three [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) (hK : Nat.card K = 8)
    (μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* Kˣ)
    {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hE : IsElemAbelian 3 E) :
    ∃ F : Subgroup (GL ι K), F ≤ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      IsElemAbelian 3 F ∧ Nat.card E ≤ 3 * Nat.card F ∧
      ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), (x : GL ι K) ∈ F → μ x = 1 := by
  have h1 := s16g_card_le_of_norm hΓ hEN
  rw [s16g_card_ringAut_eight hK] at h1
  obtain ⟨F, hFN, hF, hcard, hμ⟩ := s16g_exists_iso_elem_of_lin hK μ Nat.prime_three
    (by norm_num) (E := E ⊓ s16gLin ι K) (inf_le_left.trans hEN) inf_le_right
    (hE.mono inf_le_left)
  exact ⟨F, hFN, hF, hcard ▸ h1, hμ⟩

theorem s16g_exists_iso_elem_seven [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) (hK : Nat.card K = 8)
    (μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* Kˣ)
    {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hE : IsElemAbelian 7 E) :
    ∃ F : Subgroup (GL ι K), F ≤ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      IsElemAbelian 7 F ∧ Nat.card E ≤ 7 * Nat.card F ∧
      ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), (x : GL ι K) ∈ F → μ x = 1 := by
  have hp7 : (7 : ℕ).Prime := by norm_num
  have hEL : E ≤ s16gLin ι K := s16g_le_lin_of_coprime hΓ hp7
    (by rw [s16g_card_ringAut_eight hK]; norm_num) hEN hE.isPGroup
  obtain ⟨F, hFN, hF, hcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hE
  obtain ⟨F₀, hF₀F, hF₀card, hF₀μ⟩ := s16g_exists_ker_subgroup μ hFN
  refine ⟨F₀, hF₀F.trans hFN, hF.mono hF₀F, ?_, hF₀μ⟩
  rw [← hcard]
  have h := hF₀card
  rwa [s16g_card_units_eight hK] at h

theorem s16g_exists_iso_elem_generic [Finite K] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    (hΓ : AddCommutantScalar Γ) (hK : Nat.card K = 8)
    (μ : ↥(Subgroup.normalizer (Γ : Set (GL ι K))) →* Kˣ) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hp7 : p ≠ 7) {E : Subgroup (MulAut (Multiplicative (ι → K)))} (hEN : E ≤ s16gNorm Γ)
    (hE : IsElemAbelian p E) :
    ∃ F : Subgroup (GL ι K), F ≤ Subgroup.normalizer (Γ : Set (GL ι K)) ∧
      IsElemAbelian p F ∧ Nat.card F = Nat.card E ∧
      ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL ι K))), (x : GL ι K) ∈ F → μ x = 1 :=
  s16g_exists_iso_elem_of_lin hK μ hp hp7 hEN
    (s16g_le_lin_of_coprime hΓ hp (by
      rw [s16g_card_ringAut_eight hK]
      exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)) hEN hE.isPGroup) hE

theorem s16g_exists_mult_omegaPlus {m : ℕ} (hm : 3 ≤ m) [Finite K] [CharP K 2] :
    ∃ μ : ↥(Subgroup.normalizer (StatedOmega (StatedQuadPlus m K) :
        Set (GL (Fin m ⊕ Fin m) K))) →* Kˣ,
      ∀ x : ↥(Subgroup.normalizer (StatedOmega (StatedQuadPlus m K) :
        Set (GL (Fin m ⊕ Fin m) K))), μ x = 1 → ∀ v : Fin m ⊕ Fin m → K,
          StatedQuadPlus m K (((x : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v) =
            StatedQuadPlus m K v := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_quadratic (CFSG.LieType.Universal.Spin.quadPlus m K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K)
    (addCommutantScalar_statedOmegaPlus hm)
    (fun A hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
  refine ⟨μ, fun x hx v => ?_⟩
  have h := (hμ x).1 hx v
  rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at h

theorem s16g_exists_mult_omegaMinus {m : ℕ} (hm : 2 ≤ m) [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ μ : ↥(Subgroup.normalizer (StatedOmega (StatedQuadMinus m K b c) :
        Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K))) →* Kˣ,
      ∀ x : ↥(Subgroup.normalizer (StatedOmega (StatedQuadMinus m K b c) :
        Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K))), μ x = 1 →
        ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
          StatedQuadMinus m K b c
              (((x : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ v) =
            StatedQuadMinus m K b c v := by
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_quadratic (CFSG.LieType.Universal.Spin.quadMinus m K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
    (addCommutantScalar_statedOmegaMinus hm hirr)
    (fun A hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
  refine ⟨μ, fun x hx v => ?_⟩
  have h := (hμ x).1 hx v
  rwa [CFSG.LieType.Universal.Spin.coe_quadMinus] at h

theorem s16g_range_le_norm {G : Type*} [Group G] {A : Subgroup G} {Γ : Subgroup (GL ι K)}
    {ρ : ↥A →* MulAut (Multiplicative (ι → K))} (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm Γ) :
    ρ.range ≤ s16gNorm Γ := by
  rintro _ ⟨a, rfl⟩
  exact hρN a

theorem s16g_pRank_le_of_embedding {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (ρ : ↥A →* MulAut (Multiplicative (ι → K))) (hρ : Function.Injective ρ) {p : ℕ}
    (hp : p.Prime) {r : ℕ}
    (h : ∀ E : Subgroup (MulAut (Multiplicative (ι → K))), E ≤ ρ.range → IsElemAbelian p E →
      Nat.card E ≤ p ^ r) : CFSG.Open.pRank p A ≤ r := by
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEA hE => ?_
  have h1 : (E.subgroupOf A).map ρ ≤ ρ.range := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact ⟨y, rfl⟩
  have h2 := h ((E.subgroupOf A).map ρ) h1 ((hE.subgroupOf A).map ρ)
  rwa [Subgroup.card_map_of_injective hρ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv] at h2

theorem s16g_exists_elem_of_le_pRank {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (ρ : ↥A →* MulAut (Multiplicative (ι → K))) (hρ : Function.Injective ρ) {p : ℕ}
    (hp : p.Prime) {k : ℕ} (hk : k ≤ CFSG.Open.pRank p A) :
    ∃ E : Subgroup (MulAut (Multiplicative (ι → K))), E ≤ ρ.range ∧ IsElemAbelian p E ∧
      p ^ k ≤ Nat.card E := by
  obtain ⟨E₀, hE₀A, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  refine ⟨(E₀.subgroupOf A).map ρ, fun x hx => ?_, (hE₀.subgroupOf A).map ρ, ?_⟩
  · obtain ⟨y, -, rfl⟩ := hx
    exact ⟨y, rfl⟩
  · rw [Subgroup.card_map_of_injective hρ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀A).toEquiv, hcard]
    exact Nat.pow_le_pow_right hp.pos hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
