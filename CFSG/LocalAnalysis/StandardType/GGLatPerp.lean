module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
public import CFSG.LocalAnalysis.StandardType.GGLatPerpComp
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.StandardType.LatPerpChecks

namespace LatPerp

section Scale

variable {N : ℕ}

theorem latGram_intSmul (k : ℤ) (B : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram (k • B) α β = k * latGram B α β := by
  simp only [latGram, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem corootCoord_intSmul (p : ℕ) (k : ℤ) (hk : 0 < k) (B : Matrix (Fin N) (Fin N) ℤ)
    (α : Fin N → ℤ) : corootCoord p (k • B) α = corootCoord p B α := by
  funext i
  simp only [corootCoord, latGram_intSmul]
  rw [show 2 * (k * latGram B (Pi.single i 1) α) = k * (2 * latGram B (Pi.single i 1) α) by ring,
    Int.mul_ediv_mul_of_pos _ _ hk]

theorem perp_intSmul (R : Set (Fin N → ℤ)) (k : ℤ) (hk : k ≠ 0) (B : Matrix (Fin N) (Fin N) ℤ)
    (α : Fin N → ℤ) : perp R (k • B) α = perp R B α := by
  ext β
  simp only [perp, Set.mem_setOf_eq, latGram_intSmul, mul_eq_zero, hk, false_or]

theorem latLinked_intSmul (k : ℤ) (hk : k ≠ 0) (B : Matrix (Fin N) (Fin N) ℤ)
    (Φ : Set (Fin N → ℤ)) : latLinked (k • B) Φ = latLinked B Φ := by
  have h : (fun α β : Fin N → ℤ => α ∈ Φ ∧ β ∈ Φ ∧ latGram (k • B) α β ≠ 0) =
      fun α β => α ∈ Φ ∧ β ∈ Φ ∧ latGram B α β ≠ 0 := by
    funext α β
    simp only [latGram_intSmul, ne_eq, mul_eq_zero, hk, false_or]
  unfold latLinked
  rw [h]

end Scale

section Cart

@[expose] def ggCartOK (τ : Tag) (α : Fin τ.rank → ℤ) : Prop :=
  DivInv (Tag.symmetrizedCartan τ) α ∧ ∀ β, IsRoot τ β →
    -2 ≤ cartInt (Tag.symmetrizedCartan τ) α β ∧ cartInt (Tag.symmetrizedCartan τ) α β ≤ 2 ∧
      (cartInt (Tag.symmetrizedCartan τ) α β = 0 ↔
        latGram (Tag.symmetrizedCartan τ) α β = 0)

theorem ggDiv_base (τ : Tag) (i j : Fin τ.rank) :
    Tag.symmetrizedCartan τ j j ∣ 2 * Tag.symmetrizedCartan τ i j := by
  cases τ <;> fin_cases i <;> fin_cases j <;> decide +kernel

theorem ggCartOK_basis {τ : Tag} (hcart : ggCartCheck τ = true) (j : Fin τ.rank) :
    ggCartOK τ (Pi.single j 1) := by
  refine ⟨⟨?_, fun i => ?_⟩, fun β hβ => ggCartCheck_sound hcart j hβ⟩
  · rw [latGram_single_single]
    exact ggSymmCartan_diag_ne_zero τ j
  · rw [latGram_single_single, latGram_single_single]
    exact ggDiv_base τ i j

theorem ggCartOK_reflect (τ : Tag) (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (h : ggCartOK τ α) :
    ggCartOK τ (reflect τ i α) := by
  have hdiv' : DivInv (Tag.symmetrizedCartan τ) (reflect τ i α) :=
    divInv_transport _ (reflect τ i) (reflect_invol τ i) (latGram_reflect τ i) i
      (fun l => ⟨τ.cartan i l, reflect_single τ i l⟩) h.1
  refine ⟨hdiv', fun β hβ => ?_⟩
  have hc : cartInt (Tag.symmetrizedCartan τ) (reflect τ i α) β =
      cartInt (Tag.symmetrizedCartan τ) α (reflect τ i β) :=
    cartInt_transport _ (reflect τ i) (reflect_invol τ i) (latGram_reflect τ i) h.1 hdiv' β
  have hg : latGram (Tag.symmetrizedCartan τ) (reflect τ i α) β =
      latGram (Tag.symmetrizedCartan τ) α (reflect τ i β) := by
    have h1 := latGram_reflect τ i α (reflect τ i β)
    rwa [reflect_invol] at h1
  rw [hc, hg]
  exact h.2 _ (IsRoot.reflect i hβ)

theorem ggCartOK_of_isRoot {τ : Tag} (hcart : ggCartCheck τ = true) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : ggCartOK τ α := by
  induction hα with
  | basis j => exact ggCartOK_basis hcart j
  | reflect i _ ih => exact ggCartOK_reflect τ i ih

theorem ggPhi_eq_perp {τ : Tag} {α : Fin τ.rank → ℤ} (h : ggCartOK τ α) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    latPhi {v | IsRoot τ v} p (corootCoord p (Tag.symmetrizedCartan τ) α) = ggPerp τ α := by
  ext β
  constructor
  · rintro ⟨hβ, hchar⟩
    obtain ⟨h1, h2, h3⟩ := h.2 β hβ
    rw [latChar_corootCoord] at hchar
    exact ⟨hβ, h3.mp ((intCast_zmod_eq_zero_iff_of_abs_le_two hp hp2 h1 h2).mp hchar)⟩
  · rintro ⟨hβ, hg⟩
    obtain ⟨h1, h2, h3⟩ := h.2 β hβ
    refine ⟨hβ, ?_⟩
    rw [latChar_corootCoord]
    exact (intCast_zmod_eq_zero_iff_of_abs_le_two hp hp2 h1 h2).mpr (h3.mpr hg)

theorem perp_clauses_of_checks {τ : Tag} (hcart : ggCartCheck τ = true)
    (hbasis : ggBasisCheck τ = true) (k : ℕ) (hk : 0 < k) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    latPhi {v | IsRoot τ v} p
        (corootCoord p ((k : ℤ) • Tag.symmetrizedCartan τ) α) =
      perp {v | IsRoot τ v} ((k : ℤ) • Tag.symmetrizedCartan τ) α ∧
    (∀ β ∈ perp {v | IsRoot τ v} ((k : ℤ) • Tag.symmetrizedCartan τ) α,
      ∀ γ ∈ perp {v | IsRoot τ v} ((k : ℤ) • Tag.symmetrizedCartan τ) α,
        latLinked ((k : ℤ) • Tag.symmetrizedCartan τ)
          (perp {v | IsRoot τ v} ((k : ℤ) • Tag.symmetrizedCartan τ) α) β γ) ∧
    Nat.card {f : Fin τ.rank → ZMod p //
      ∀ β ∈ perp {v | IsRoot τ v} ((k : ℤ) • Tag.symmetrizedCartan τ) α,
        latChar p f β = 0} = p ∧
    7 ≤ (perp {v | IsRoot τ v} ((k : ℤ) • Tag.symmetrizedCartan τ) α).ncard := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hk0 : (k : ℤ) ≠ 0 := hk'.ne'
  have hphi := ggPhi_eq_perp (ggCartOK_of_isRoot hcart hα) p hp hp2
  obtain ⟨hconn, hcard, hcount⟩ := ggPerpComp_of_checks hcart hbasis p hp hp2 hα
  rw [corootCoord_intSmul p k hk', perp_intSmul _ k hk0, latLinked_intSmul k hk0]
  exact ⟨hphi, hconn, hcard, hcount⟩

end Cart

end LatPerp

open LatPerp

section Perp

theorem latPerp_F4 (n f : ℕ) : LatPerp (ggU .F4 n f).D := by
  intro S hS α hα p hp hp2
  obtain ⟨k, hk, rfl⟩ := isRootGram_F4 n f S hS
  have hR : (ggU .F4 n f).D.roots = {v : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 v} := by
    ext v
    exact (mem_roots_F4 n f v).trans mem_rootFinset
  rw [hR] at hα ⊢
  exact perp_clauses_of_checks ggCartCheck_F4 ggBasisCheck_F4 k hk hα p hp hp2

theorem latPerp_E6 (n f : ℕ) : LatPerp (ggU .E6 n f).D := by
  intro S hS α hα p hp hp2
  obtain ⟨k, hk, rfl⟩ := isRootGram_E6 n f S hS
  have hR : (ggU .E6 n f).D.roots = {v : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 v} := by
    ext v
    exact (mem_roots_E6 n f v).trans mem_rootFinset
  rw [hR] at hα ⊢
  exact perp_clauses_of_checks ggCartCheck_E6 ggBasisCheck_E6 k hk hα p hp hp2

theorem latPerp_E7 (n f : ℕ) : LatPerp (ggU .E7 n f).D := by
  intro S hS α hα p hp hp2
  obtain ⟨k, hk, rfl⟩ := isRootGram_E7 n f S hS
  have hR : (ggU .E7 n f).D.roots = {v : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 v} := by
    ext v
    exact (mem_roots_E7 n f v).trans mem_rootFinset
  rw [hR] at hα ⊢
  exact perp_clauses_of_checks ggCartCheck_E7 ggBasisCheck_E7 k hk hα p hp hp2

theorem latPerp_E8 (n f : ℕ) : LatPerp (ggU .E8 n f).D := by
  intro S hS α hα p hp hp2
  obtain ⟨k, hk, rfl⟩ := isRootGram_E8 n f S hS
  have hR : (ggU .E8 n f).D.roots = {v : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 v} := by
    ext v
    exact (mem_roots_E8 n f v).trans mem_rootFinset
  rw [hR] at hα ⊢
  exact perp_clauses_of_checks ggCartCheck_E8 ggBasisCheck_E8 k hk hα p hp hp2

theorem ggLatPerpExc_holds : ∀ (τ : StatedLieTag) (f : ℕ), GGExcFive τ → LatPerp (ggU (absTag τ) 6 f).D := by
  intro τ f hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact latPerp_F4 6 f
  · exact latPerp_E6 6 f
  · exact latPerp_E7 6 f
  · exact latPerp_E8 6 f
  · exact latPerp_E6 6 f

end Perp

end CFSG.StandardType
