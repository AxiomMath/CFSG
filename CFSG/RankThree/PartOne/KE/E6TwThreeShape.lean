module

public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2
public import CFSG.RankThree.PartOne.KE.E6FourGraph
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public noncomputable section

namespace CFSG.RankThree.PartOne.KETw3

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.E6
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section Dichotomy

theorem chainRoot13_orientation_aux : ∀ a b c d e f : Fin 3, a ≠ b → c ≠ d → e ≠ f →
    chainRoot chain13 a b + chainRoot chain13 c d = chainRoot chain13 e f →
    (b = c ∧ a ≠ d) ∨ (a = d ∧ b ≠ c) := by
  decide +kernel

theorem chainRoot13_add : ∀ a b c : Fin 3,
    chainRoot chain13 a b + chainRoot chain13 b c = chainRoot chain13 a c := by
  decide +kernel

theorem chainRoot56_add : ∀ a b c : Fin 3,
    chainRoot chain56 a b + chainRoot chain56 b c = chainRoot chain56 a c := by
  decide +kernel

variable {T : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ}

theorem map_zero_of_add (hadd : ∀ x y, T (x + y) = T x + T y) : T 0 = 0 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem map_neg_of_add (hadd : ∀ x y, T (x + y) = T x + T y) (x : Fin Tag.E6.rank → ℤ) :
    T (-x) = -T x := by
  have := hadd x (-x)
  rw [add_neg_cancel, map_zero_of_add hadd] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem transition_pos_of_simple (hadd : ∀ x y, T (x + y) = T x + T y) (π : Equiv.Perm (Fin 3))
    (h01 : T (chainRoot chain56 0 1) = chainRoot chain13 (π 0) (π 1))
    (h12 : T (chainRoot chain56 1 2) = chainRoot chain13 (π 1) (π 2)) :
    ∀ i j : Fin 3, T (chainRoot chain56 i j) = chainRoot chain13 (π i) (π j) := by
  have h0 := map_zero_of_add hadd
  intro i j
  fin_cases i <;> fin_cases j
  · show T (chainRoot chain56 0 0) = chainRoot chain13 (π 0) (π 0)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h01
  · show T (chainRoot chain56 0 2) = chainRoot chain13 (π 0) (π 2)
    rw [← chainRoot56_add 0 1 2, hadd, h01, h12, chainRoot13_add]
  · show T (chainRoot chain56 1 0) = chainRoot chain13 (π 1) (π 0)
    rw [chainRoot_swap chain56 0 1, chainRoot_swap chain13 (π 0) (π 1), map_neg_of_add hadd, h01]
  · show T (chainRoot chain56 1 1) = chainRoot chain13 (π 1) (π 1)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h12
  · show T (chainRoot chain56 2 0) = chainRoot chain13 (π 2) (π 0)
    rw [chainRoot_swap chain56 0 2, chainRoot_swap chain13 (π 0) (π 2), ← chainRoot56_add 0 1 2,
      map_neg_of_add hadd, hadd, h01, h12, chainRoot13_add]
  · show T (chainRoot chain56 2 1) = chainRoot chain13 (π 2) (π 1)
    rw [chainRoot_swap chain56 1 2, chainRoot_swap chain13 (π 1) (π 2), map_neg_of_add hadd, h12]
  · show T (chainRoot chain56 2 2) = chainRoot chain13 (π 2) (π 2)
    rw [chainRoot_self, chainRoot_self, h0]

theorem transition_neg_of_simple (hadd : ∀ x y, T (x + y) = T x + T y) (π : Equiv.Perm (Fin 3))
    (h01 : T (chainRoot chain56 0 1) = chainRoot chain13 (π 1) (π 0))
    (h12 : T (chainRoot chain56 1 2) = chainRoot chain13 (π 2) (π 1)) :
    ∀ i j : Fin 3, T (chainRoot chain56 i j) = chainRoot chain13 (π j) (π i) := by
  have h0 := map_zero_of_add hadd
  intro i j
  fin_cases i <;> fin_cases j
  · show T (chainRoot chain56 0 0) = chainRoot chain13 (π 0) (π 0)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h01
  · show T (chainRoot chain56 0 2) = chainRoot chain13 (π 2) (π 0)
    rw [← chainRoot56_add 0 1 2, hadd, h01, h12, add_comm, chainRoot13_add]
  · show T (chainRoot chain56 1 0) = chainRoot chain13 (π 0) (π 1)
    rw [chainRoot_swap chain56 0 1, map_neg_of_add hadd, h01, chainRoot_swap chain13 (π 1) (π 0)]
  · show T (chainRoot chain56 1 1) = chainRoot chain13 (π 1) (π 1)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h12
  · show T (chainRoot chain56 2 0) = chainRoot chain13 (π 0) (π 2)
    rw [chainRoot_swap chain56 0 2, ← chainRoot56_add 0 1 2, map_neg_of_add hadd, hadd, h01, h12,
      add_comm, chainRoot13_add, chainRoot_swap chain13 (π 2) (π 0)]
  · show T (chainRoot chain56 2 1) = chainRoot chain13 (π 1) (π 2)
    rw [chainRoot_swap chain56 1 2, map_neg_of_add hadd, h12, chainRoot_swap chain13 (π 2) (π 1)]
  · show T (chainRoot chain56 2 2) = chainRoot chain13 (π 2) (π 2)
    rw [chainRoot_self, chainRoot_self, h0]

theorem a2_transition_cases (hadd : ∀ x y, T (x + y) = T x + T y)
    (hroots : ∀ i j : Fin 3, i ≠ j → ∃ a b : Fin 3, a ≠ b ∧
      T (chainRoot chain56 i j) = chainRoot chain13 a b) :
    IsPositiveTransition T chain56 chain13 ∨ IsNegativeTransition T chain56 chain13 := by
  obtain ⟨a, b, hab, h01⟩ := hroots 0 1 (by decide)
  obtain ⟨c, d, hcd, h12⟩ := hroots 1 2 (by decide)
  obtain ⟨e, f, hef, h02⟩ := hroots 0 2 (by decide)
  have hs : chainRoot chain13 a b + chainRoot chain13 c d = chainRoot chain13 e f := by
    rw [← h01, ← h12, ← h02, ← hadd, chainRoot56_add]
  rcases chainRoot13_orientation_aux a b c d e f hab hcd hef hs with ⟨hbc, had⟩ | ⟨had, hbc⟩
  · subst hbc
    have hinj : Function.Injective ![a, b, d] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    let π : Equiv.Perm (Fin 3) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    left
    exact ⟨π, transition_pos_of_simple hadd π h01 h12⟩
  · subst had
    have hinj : Function.Injective ![b, a, c] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    let π : Equiv.Perm (Fin 3) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    right
    exact ⟨π, transition_neg_of_simple hadd π h01 h12⟩

end Dichotomy

section Exchange

variable {Ω : Type} [Field Ω]

theorem exists_sl3_exchange_21 (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (τ₁ τ₂ : Fin 3 → Fin 3 → Fin 3) (hne : ∀ i j : Fin 3, i ≠ j → τ₁ i j ≠ τ₂ i j)
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ μ : Ωˣ, ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (τ₁ i j) (τ₂ i j)) ((μ : Ω) * c)) :
    ∃ hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56, θ' g ∈ subsystemGroup Tag.E6 Ω support13,
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((a2Equiv₁ Ω ⟨θ' ((a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t)),
          hQ _ ((a2Equiv₂ Ω).symm _).2⟩ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single (τ₁ i j) (τ₂ i j) ((b i j : Ω) * t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot56_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun i j hij c => by
      obtain ⟨μ, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot13_mem (hne i j hij) _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      θ' g ∈ subsystemGroup Tag.E6 Ω support13 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, c, rfl | rfl⟩ := hx
      · rcases (mem_support56 i).1 hi with rfl | rfl
        · rw [← pinnedX_single, ← h01]
          exact hmemθ 0 1 (by decide) c
        · rw [← pinnedX_single, ← h12]
          exact hmemθ 1 2 (by decide) c
      · rcases (mem_support56 i).1 hi with rfl | rfl
        · rw [← pinnedX_neg_single, ← h10]
          exact hmemθ 1 0 (by decide) c
        · rw [← pinnedX_neg_single, ← h21]
          exact hmemθ 2 1 (by decide) c
    | one =>
      rw [map_one]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact inv_mem hx
  choose s hs hρ using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₂_pinnedX_chainRoot56 (Ω := Ω) hij
  choose s' hs' hρ' using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₁_pinnedX_chainRoot13 (Ω := Ω) hij
  choose μ hμ using hθ
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain56 i j) (s i j hij * t),
          pinnedX_chainRoot56_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₂_apply, coe_a2Rep₂, hρ i j hij, ← mul_assoc, hs i j hij, one_mul]
    rfl
  refine ⟨hQ, fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne (((s' (τ₁ i j) (τ₂ i j) (hne i j hij) : ℤ) : Ω)) ((s' (τ₁ i j) (τ₂ i j) (hne i j hij) : ℤ) : Ω) (sign_mul_self (hs' (τ₁ i j) (τ₂ i j) (hne i j hij))) * μ i j hij *
      Units.mkOfMulEqOne (s i j hij) (s i j hij) (hs i j hij) else 1, fun i j hij t => ?_⟩
  simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mul, Units.val_mkOfMulEqOne]
  rw [a2Equiv₁_apply, coe_a2Rep₁]
  change a2Mat₁ (θ' ((a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t))) = _
  rw [hsymm i j hij t]
  change a2Mat₁ (θ' (pinnedX Tag.E6 Ω (chainRoot chain56 i j) (s i j hij * t))) = _
  rw [hμ i j hij, hρ' (τ₁ i j) (τ₂ i j) (hne i j hij)]
  congr 2
  ring

end Exchange

section Conj

variable {L : Type} [Field L]

theorem conj_t0nwP_pinnedX {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (w : WeylGroup Tag.E6)
    {t₀ : ModGL Tag.E6 L} (ht₀ : t₀ ∈ torusGroup Tag.E6 L) :
    ∃ μ : Lˣ, ∀ c : L,
      (t₀ * canonicalRep (coxeterSystem Tag.E6) L w * KE.diagE6 L) * pinnedX Tag.E6 L β c *
        (t₀ * canonicalRep (coxeterSystem Tag.E6) L w * KE.diagE6 L)⁻¹ =
          pinnedX Tag.E6 L (w • permLattice e6Rho β) ((μ : L) * c) := by
  classical
  set nw : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hnwm : nw ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup L w
  have hπ : weylQuotientHom Tag.E6 L ⟨nw, hnwm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  obtain ⟨b₀, hb₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀
  set Q : ModGL Tag.E6 L := KE.diagE6 L with hQ
  have hργ : IsRoot Tag.E6 (permLattice e6Rho β) := hβ.permLattice TwistTag.E6.cartan_perm
  have hγ : IsRoot Tag.E6 (w • permLattice e6Rho β) := IsRoot.smul hργ w
  obtain ⟨e, hee, he⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hβ
  have he' : ∀ c : L, Q * pinnedX Tag.E6 L β c * Q⁻¹ =
      pinnedX Tag.E6 L (permLattice e6Rho β) (e * c) := he
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnwm hργ
  rw [hπ] at hμ
  refine ⟨rootChar b₀ (w • permLattice e6Rho β) * μ * ⟨e, e, hee, hee⟩, fun c => ?_⟩
  have e1 : (t₀ * nw * Q) * pinnedX Tag.E6 L β c * (t₀ * nw * Q)⁻¹ =
      t₀ * (nw * (Q * pinnedX Tag.E6 L β c * Q⁻¹) * nw⁻¹) * t₀⁻¹ := by
    group
  rw [e1, he' c, hμ, hb₀, rootDiagUnit_conj_pinnedX b₀ hγ]
  congr 1
  simp only [Units.val_mul]
  ring

theorem conj_conj_t0nwP_pinnedX {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (w₁ w₂ : WeylGroup Tag.E6) {t₀ : ModGL Tag.E6 L} (ht₀ : t₀ ∈ torusGroup Tag.E6 L) :
    ∃ μ : Lˣ, ∀ c : L,
      (canonicalRep (coxeterSystem Tag.E6) L w₁ *
          (t₀ * canonicalRep (coxeterSystem Tag.E6) L w₂ * KE.diagE6 L) *
            (canonicalRep (coxeterSystem Tag.E6) L w₁)⁻¹) * pinnedX Tag.E6 L β c *
        (canonicalRep (coxeterSystem Tag.E6) L w₁ *
          (t₀ * canonicalRep (coxeterSystem Tag.E6) L w₂ * KE.diagE6 L) *
            (canonicalRep (coxeterSystem Tag.E6) L w₁)⁻¹)⁻¹ =
          pinnedX Tag.E6 L (w₁ • (w₂ • permLattice e6Rho (w₁⁻¹ • β))) ((μ : L) * c) := by
  classical
  set n₁ : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w₁ with hn₁
  set nh : ModGL Tag.E6 L := t₀ * canonicalRep (coxeterSystem Tag.E6) L w₂ * KE.diagE6 L with hnh
  have hn₁m : n₁ ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup L w₁
  have hπ₁ : weylQuotientHom Tag.E6 L ⟨n₁, hn₁m⟩ = w₁ :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w₁)
  have hπ₁' : weylQuotientHom Tag.E6 L ⟨n₁⁻¹, inv_mem hn₁m⟩ = w₁⁻¹ := by
    have := map_inv (weylQuotientHom Tag.E6 L) ⟨n₁, hn₁m⟩
    rw [hπ₁] at this
    exact this
  have hβ' : IsRoot Tag.E6 (w₁⁻¹ • β) := IsRoot.smul hβ w₁⁻¹
  obtain ⟨μA, hμA⟩ := monomial_conj_pinnedX (inv_mem hn₁m) hβ
  rw [hπ₁'] at hμA
  obtain ⟨μB, hμB⟩ := conj_t0nwP_pinnedX hβ' w₂ ht₀
  have hγ : IsRoot Tag.E6 (w₂ • permLattice e6Rho (w₁⁻¹ • β)) :=
    IsRoot.smul (hβ'.permLattice TwistTag.E6.cartan_perm) w₂
  obtain ⟨μC, hμC⟩ := monomial_conj_pinnedX hn₁m hγ
  rw [hπ₁] at hμC
  refine ⟨μC * μB * μA, fun c => ?_⟩
  have e1 : (n₁ * nh * n₁⁻¹) * pinnedX Tag.E6 L β c * (n₁ * nh * n₁⁻¹)⁻¹ =
      n₁ * (nh * (n₁⁻¹ * pinnedX Tag.E6 L β c * n₁⁻¹⁻¹) * nh⁻¹) * n₁⁻¹ := by
    group
  rw [e1, hμA c, hμB, hμC]
  congr 1
  simp only [Units.val_mul]
  ring

theorem conj_rootSpan_le {E : ModGL Tag.E6 L} {S S' : Set (Fin Tag.E6.rank → ℤ)}
    (T : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ)
    (hE : ∀ α ∈ S, ∃ μ : Lˣ, ∀ c : L,
      E * pinnedX Tag.E6 L α c * E⁻¹ = pinnedX Tag.E6 L (T α) ((μ : L) * c))
    (hST : ∀ α ∈ S, T α ∈ S') :
    ∀ g ∈ rootSpan Tag.E6 L S, E * g * E⁻¹ ∈ rootSpan Tag.E6 L S' := by
  intro g hg
  have hle : rootSpan Tag.E6 L S ≤ (rootSpan Tag.E6 L S').comap (MulAut.conj E).toMonoidHom := by
    refine iSup₂_le fun α hα => ?_
    intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨μ, hμ⟩ := hE α hα
    show E * pinnedX Tag.E6 L α c * E⁻¹ ∈ rootSpan Tag.E6 L S'
    rw [hμ c]
    exact rootSubgroup_le_rootSpan (hST α hα) (mem_rootSubgroup.2 ⟨_, rfl⟩)
  exact hle hg

end Conj

end CFSG.RankThree.PartOne.KETw3
