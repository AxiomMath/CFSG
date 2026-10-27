module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenAbstract
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenMatrix
public import CFSG.GH74.Uniqueness.Section14Primary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open Matrix
open CFSG.RankThree.PartTwo.Sec15.KSL3Two (IsMonomialWith)

namespace SL3G

section FieldCase

variable {K : Type} [Field K]

private theorem eigen_three {B : GL (Fin 3) K} {σ : K ≃+* K} {ζ : Kˣ}
    (h : (B : Matrix (Fin 3) (Fin 3) K) *
        (diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1]).map σ =
      diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1] * (B : Matrix (Fin 3) (Fin 3) K)) :
    σ (ζ : K) = ζ ∨ σ (ζ : K) = ((ζ⁻¹ : Kˣ) : K) ∨ σ (ζ : K) = 1 := by
  set x : K := σ (ζ : K) with hx
  have hmap : (diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1]).map σ = diagonal ![x, x⁻¹, 1] := by
    rw [Matrix.diagonal_map (map_zero σ)]
    congr 1
    ext i
    fin_cases i <;> simp [hx, map_inv₀]
  rw [hmap] at h
  have hsub : ∀ d : Fin 3 → K, diagonal d - x • (1 : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => d i - x) := by
    intro d
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  have h2 : (B : Matrix (Fin 3) (Fin 3) K) * (diagonal ![x, x⁻¹, 1] - x • 1) =
      (diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1] - x • 1) * (B : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, h]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [hsub, hsub] at h2
  have hdet := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Fin.prod_univ_three, Fin.prod_univ_three] at hdet
  have hB : (B : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (B.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  simp at hdet
  rcases hdet with ((h1 | h1) | h1) | h1
  · exact Or.inl (sub_eq_zero.mp h1).symm
  · refine Or.inr (Or.inl ?_)
    rw [Units.val_inv_eq_inv_val]
    exact (sub_eq_zero.mp h1).symm
  · exact Or.inr (Or.inr (sub_eq_zero.mp h1).symm)
  · exact absurd h1 hB

private theorem diag_mem_of_maximal {G : Type*} [Group G] [Finite G] (ι : G →* GL (Fin 3) K)
    (hι : Function.Injective ι) {T : Subgroup G} (hT3 : IsPGroup 3 T)
    (hTmax : ∀ S : Subgroup G, IsPGroup 3 S → T ≤ S → S = T)
    (hmono : ∀ s ∈ T, ∃ τ : Fin 3 → Fin 3,
      IsMonomialWith ((ι s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ)
    {d : G} (hd : ((ι d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hd3 : ∃ n : ℕ, d ^ (3 ^ n) = 1) : d ∈ T := by
  have hcomm : ∀ a ∈ diagSub ι, ∀ b ∈ diagSub ι, a * b = b * a :=
    fun a ha b hb => diagSub_comm hι ha hb
  let M := CFSG.GH74.Uniqueness.primaryComponent (diagSub ι) hcomm 3
  have hdM : d ∈ M := ⟨hd, hd3⟩
  have hM3 : IsPGroup 3 M := CFSG.GH74.Uniqueness.isPGroup_primaryComponent Nat.prime_three
  have hnorm : ∀ s ∈ T, ∀ b ∈ diagSub ι, s * b * s⁻¹ ∈ diagSub ι := by
    intro s hs b hb
    obtain ⟨τ, hτ⟩ := hmono s hs
    have hτ3 := monomial_perm_cube ι hT3 hs hτ
    rw [mem_diagSub, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    exact isDiag_conj_of_monomial hτ hτ3 (mem_diagSub.mp hb)
  have hTM : T ≤ Subgroup.normalizer (M : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact CFSG.GH74.Uniqueness.primaryComponent_conj (hnorm s hs) hx
    · intro hx
      have := CFSG.GH74.Uniqueness.primaryComponent_conj (hnorm s⁻¹ (inv_mem hs)) hx
      simpa [mul_assoc] using this
  have hsup : IsPGroup 3 ↥(T ⊔ M) := IsPGroup.to_sup_of_normal_right' hT3 hM3 hTM
  have heq : T ⊔ M = T := hTmax _ hsup le_sup_left
  have hMT : M ≤ T := heq ▸ le_sup_right
  exact hMT hdM

private theorem field_d_mem_diag {G : Type} [Group G] [Finite G] {ι : G →* GL (Fin 3) K}
    (hι : Function.Injective ι) {T : Subgroup G} (hT3 : IsPGroup 3 T)
    (hTmax : ∀ S : Subgroup G, IsPGroup 3 S → T ≤ S → S = T)
    (hmono : ∀ s ∈ T, ∃ τ : Fin 3 → Fin 3,
      IsMonomialWith ((ι s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ)
    {ζ : Kˣ} (hζ : ∃ n : ℕ, ζ ^ (3 ^ n) = 1) {d : G}
    (hd : ((ι d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1]) :
    d ∈ T ⊓ diagSub ι := by
  obtain ⟨n, hn⟩ := hζ
  have hddiag : d ∈ diagSub ι := by
    rw [mem_diagSub, hd]
    exact isDiag_diagonal _
  have hd3 : ∃ m : ℕ, d ^ (3 ^ m) = 1 := by
    refine ⟨n, hι ?_⟩
    rw [map_pow, map_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hd, Matrix.diagonal_pow, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [← Units.val_pow_eq_pow_val, inv_pow, hn]
  exact ⟨diag_mem_of_maximal ι hι hT3 hTmax hmono (mem_diagSub.mp hddiag) hd3, hddiag⟩

private theorem field_fix_eq_diag {G : Type} [Group G] [Finite G] {ι : G →* GL (Fin 3) K}
    (hι : Function.Injective ι) {α : MulAut G} {T : Subgroup G} (hH : ModelHyp α T)
    (hFD : T ⊓ fixSub α ≤ T ⊓ diagSub ι) :
    T ⊓ diagSub ι = T ⊓ fixSub α := by
  have hDT : T ⊓ diagSub ι ≤ T := inf_le_left
  have hidx : (T ⊓ fixSub α).relIndex T = 3 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact hH.index
  have hchain := Subgroup.relIndex_mul_relIndex (T ⊓ fixSub α) (T ⊓ diagSub ι) T hFD hDT
  rw [hidx] at hchain
  have hdvd : (T ⊓ diagSub ι).relIndex T ∣ 3 := Dvd.intro_left _ hchain
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    have hTD : T ≤ T ⊓ diagSub ι := Subgroup.relIndex_eq_one.mp h
    apply hH.nonabelian
    exact ⟨⟨fun a b => Subtype.ext (diagSub_comm hι (hTD a.2).2 (hTD b.2).2)⟩⟩
  · have h1' : (T ⊓ fixSub α).relIndex (T ⊓ diagSub ι) = 1 := by
      rw [h] at hchain
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1') hFD

private theorem field_commute {B : GL (Fin 3) K} {M N : Matrix (Fin 3) (Fin 3) K}
    (h : (B : Matrix (Fin 3) (Fin 3) K) * M *
      ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = N) :
    (B : Matrix (Fin 3) (Fin 3) K) * M = N * (B : Matrix (Fin 3) (Fin 3) K) := by
  have hBinv : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (B : Matrix (Fin 3) (Fin 3) K) * M
      = (B : Matrix (Fin 3) (Fin 3) K) * M *
        (((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (B : Matrix (Fin 3) (Fin 3) K)) := by rw [hBinv, Matrix.mul_one]
    _ = ((B : Matrix (Fin 3) (Fin 3) K) * M *
          ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (B : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.mul_assoc _ ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)]
    _ = N * (B : Matrix (Fin 3) (Fin 3) K) := by rw [h]

theorem field_false {G : Type} [Group G] [Finite G] {ι : G →* GL (Fin 3) K}
    (hι : Function.Injective ι) {α : MulAut G} {T : Subgroup G} (hH : ModelHyp α T)
    {σ : K ≃+* K} {B : GL (Fin 3) K} (hα : ActsAs ι α σ B)
    (hmono : ∀ s ∈ T, ∃ τ : Fin 3 → Fin 3,
      IsMonomialWith ((ι s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) τ)
    (hdiag : ∀ x ∈ T ⊓ fixSub α, ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    {ζ : Kˣ} (hζ : ∃ n : ℕ, ζ ^ (3 ^ n) = 1)
    (hd : ∃ d : G, ((ι d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1])
    (h1 : σ (ζ : K) ≠ ζ) (h2 : σ (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K)) (h3 : σ (ζ : K) ≠ 1) : False := by
  obtain ⟨d, hd⟩ := hd
  have hdD := field_d_mem_diag hι hH.pgroup hH.maximal hmono hζ hd
  have hFD : T ⊓ fixSub α ≤ T ⊓ diagSub ι := fun x hx => ⟨hx.1, hdiag x hx⟩
  have hDF := field_fix_eq_diag hι hH hFD
  have hdF : d ∈ T ⊓ fixSub α := hDF ▸ hdD
  have hfix : α d = d := hdF.2
  have hact := hα d
  rw [hfix, hd] at hact
  have hcomm := field_commute hact.symm
  rcases eigen_three hcomm with e | e | e
  · exact h1 e
  · exact h2 e
  · exact h3 e

end FieldCase

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
