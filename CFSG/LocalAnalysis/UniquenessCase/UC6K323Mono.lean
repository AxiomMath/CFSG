module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K322Lin
public import CFSG.LocalAnalysis.UniquenessCase.UC6K323Fr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K323Mono

open Matrix CFSG.RepresentationTheory
open CFSG.RankThree.SubgroupLists (translate IsTransitiveMonomial)

variable {p : ℕ} [Fact p.Prime]

theorem pow_pred_eq_one_of_diag {L : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p)}
    (hL : DirectSum.IsInternal L) (hL1 : ∀ i, Module.finrank (ZMod p) (L i) = 1)
    {A : GL (Fin 3) (ZMod p)}
    (hA : ∀ i, ∀ w ∈ L i, (A : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ L i) :
    A ^ (p - 1) = 1 := by
  classical
  have hline : ∀ i, ∀ w ∈ L i, (((A ^ (p - 1) : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w = w) := by
    intro i w hw
    by_cases hw0 : w = 0
    · rw [hw0, Matrix.mulVec_zero]
    have hspan := (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : L i)
      (fun h0 => hw0 (congrArg Subtype.val h0))).1 (hL1 i)
    obtain ⟨c, hc⟩ := hspan ⟨(A : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w, hA i w hw⟩
    have hcw : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w = c • w := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hcw
      apply hw0
      have h2 := congrArg (fun v => ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v)
        hcw
      simpa [Matrix.mulVec_mulVec] using h2
    have hpow : ∀ k : ℕ, ((A ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w =
        c ^ k • w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [K323Fr.mulVec_pow_succ, ih, Matrix.mulVec_smul, hcw, smul_smul, pow_succ, mul_comm]
    rw [hpow, ZMod.pow_card_sub_one_eq_one hc0, one_smul]
  have hall : ∀ v : Fin 3 → ZMod p, (((A ^ (p - 1) : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v) := by
    intro v
    have hv : v ∈ ⨆ i, L i := hL.submodule_iSup_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem i w hw => exact hline i w hw
    | zero => rw [Matrix.mulVec_zero]
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, ha, hb]
  refine Units.ext ?_
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hall w, Units.val_one, Matrix.one_mulVec]

theorem iterate_two_of_fix : ∀ σ : Fin 3 → Fin 3, Function.Injective σ → ∀ i₀, σ i₀ = i₀ →
    ∀ i, σ (σ i) = i := by decide

theorem translate_sq_eq {G : Subgroup (GL (Fin 3) (ZMod p))}
    {L : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p)} (hL : DirectSum.IsInternal L)
    (hL1 : ∀ i, Module.finrank (ZMod p) (L i) = 1)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) {g : GL (Fin 3) (ZMod p)} (hgG : g ∈ G)
    {i₀ : Fin 3} (hfix : translate g (L i₀) = L i₀) : ∀ i, translate (g ^ 2) (L i) = L i := by
  classical
  have hinjL : Function.Injective L := K322Lin.injective_of_isInternal hL hL1
  choose σ hσ using hperm g hgG
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply hinjL
    rw [← CFSG.RankThree.SubgroupLists.translate_inv_translate g (L i), hσ i, hij, ← hσ j,
      CFSG.RankThree.SubgroupLists.translate_inv_translate]
  have hσi₀ : σ i₀ = i₀ := by
    apply hinjL
    rw [← hσ i₀, hfix]
  intro i
  rw [pow_two, CFSG.RankThree.SubgroupLists.translate_mul, hσ, hσ, iterate_two_of_fix σ hσinj i₀ hσi₀]

theorem false_of_monomial (hp5 : 5 ≤ p) {G X : Subgroup (GL (Fin 3) (ZMod p))} (hXG : X ≤ G)
    (hmono : IsTransitiveMonomial G) {g x : GL (Fin 3) (ZMod p)} (hgX : g ∈ X) {n : ℕ}
    (horder : orderOf g = n) (hn : n = (p ^ 2 - 1) / 2) (hx4 : x ^ 4 = 1) (hxG : x ∈ G)
    {Z : Submodule (ZMod p) (Fin 3 → ZMod p)} (hZ : Module.finrank (ZMod p) Z = 1)
    (hfix : {v : Fin 3 → ZMod p | ((x ^ 2 : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v} = (Z : Set (Fin 3 → ZMod p)))
    (hXZ : ∀ y ∈ X, ∀ w ∈ Z, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w = w) : False := by
  classical
  obtain ⟨L, hL, hL1, hperm, -⟩ := hmono
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨i₀, hZi⟩ := K322Lin.eq_line_of_monomial h2 hL hL1 hperm hxG hx4 hZ hfix
  have hgfix : translate g (L i₀) = L i₀ := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Matrix.toLin'_apply, hXZ g hgX u (hZi ▸ hu)]
      exact hu
    · intro hw
      exact ⟨w, hw, by rw [Matrix.toLin'_apply]; exact hXZ g hgX w (hZi ▸ hw)⟩
  have hsq := translate_sq_eq hL hL1 hperm (hXG hgX) hgfix
  have hA : ∀ i, ∀ w ∈ L i, ((g ^ 2 : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ L i := by
    intro i w hw
    have := (K322Lin.mulVec_mem_translate_iff (g := g ^ 2) (W := L i)).2 hw
    rwa [hsq i] at this
  have h1 : (g ^ 2) ^ (p - 1) = 1 := pow_pred_eq_one_of_diag hL hL1 hA
  have hdvd : n ∣ 2 * (p - 1) := by
    rw [← horder]
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul] at h1
    exact h1
  have hp2 : 2 ≤ p := by omega
  have hle := Nat.le_of_dvd (by omega) hdvd
  rw [hn] at hle
  have : p ^ 2 ≤ 4 * p - 2 := by omega
  have h5 : 5 * p ≤ p ^ 2 := by nlinarith
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC6.K323Mono
