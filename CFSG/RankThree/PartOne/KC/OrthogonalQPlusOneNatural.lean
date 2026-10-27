module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneSector
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneData
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePair

public section

open Polynomial Module QuadraticMap CFSG CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical

namespace CFSG.RankThree.PartOne

section Chars

variable {G : Type*} [Group G] {p : ℕ}

theorem chars_independent [Fact p.Prime] {M N : Subgroup G} (hM : Nat.card M = p)
    (hN : Nat.card N = p) (hMN : M ≠ N) (χ χ' : G →* Multiplicative (ZMod p))
    (hχ : ∀ y, χ y = 1 ↔ y ∈ M) (hχ' : ∀ y, χ' y = 1 ↔ y ∈ N) :
    ∀ m n : ZMod p, (∀ y : G, m * (χ y).toAdd + n * (χ' y).toAdd = 0) → m = 0 ∧ n = 0 := by
  intro m n h
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hMfin : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hp0)
  have hNfin : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; exact hp0)
  obtain ⟨y, hyM, hyN⟩ : ∃ y ∈ M, y ∉ N := by
    by_contra hcon
    push Not at hcon
    exact hMN (Subgroup.eq_of_le_of_card_ge (fun y hy => hcon y hy) (by rw [hM, hN]))
  obtain ⟨y', hyN', hyM'⟩ : ∃ y ∈ N, y ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hMN (Subgroup.eq_of_le_of_card_ge (fun y hy => hcon y hy) (by rw [hM, hN])).symm
  have h1 := h y
  have h2 := h y'
  have e1 : (χ y).toAdd = 0 := toAdd_eq_zero.mpr ((hχ y).mpr hyM)
  have e2 : (χ' y').toAdd = 0 := toAdd_eq_zero.mpr ((hχ' y').mpr hyN')
  have n1 : (χ' y).toAdd ≠ 0 := fun h0 => hyN ((hχ' y).mp (toAdd_eq_zero.mp h0))
  have n2 : (χ y').toAdd ≠ 0 := fun h0 => hyM' ((hχ y').mp (toAdd_eq_zero.mp h0))
  rw [e1, mul_zero, zero_add] at h1
  rw [e2, mul_zero, add_zero] at h2
  exact ⟨(mul_eq_zero.mp h2).resolve_right n2, (mul_eq_zero.mp h1).resolve_right n1⟩

end Chars

section Planes

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

structure SectorPlanes (Q : QuadraticForm K V) (p : ℕ) (Ã : Subgroup (orthDerived Q))
    (E : Type) [Field E] [Algebra K E] (ζ : E) (M : Subgroup Ã) where
  ι : Type
  fin : Fintype ι
  φ : ι → E →ₗ[K] V
  χ : ι → Ã →* Multiplicative (ZMod p)
  plane : ∀ i, IsNormPlane Ã ζ (φ i) (χ i)
  mem : ∀ i z, φ i z ∈ lineSpace M
  orth : ∀ i j, i ≠ j → ∀ z w, polar Q (φ i z) (φ j w) = 0
  span : (⨆ i, LinearMap.range (φ i)) = lineSpace M
  ker : ∀ i (y : Ã), χ i y = 1 ↔ y ∈ M

theorem nonempty_sectorPlanes (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hpq : p ∣ Nat.card K + 1) {A : Subgroup (ProjOrthDerived Q)} {Ã : Subgroup (orthDerived Q)}
    (hdata : QPlusData Q p A Ã) {E : Type} [Field E] [Algebra K E] (hE : finrank K E = 2)
    {ζ : E} (hζ : orderOf ζ = p) (M : Subgroup Ã) (hM : Nat.card M = p) :
    Nonempty (SectorPlanes Q p Ã E ζ M) := by
  have : IsMulCommutative Ã := hdata.elem.1
  obtain ⟨ι, hι, φ, χ, hinj, hnorm, hmem, horth, hreg, hspan, hact, hker⟩ :=
    exists_sector_planes hp hp3 hpl hpq Ã hdata.card hdata.elem.2 M hM (lineSpace M)
      (hdata.reg M hM) (hdata.fixM M hM) (hdata.inv M hM) (hdata.noFix M hM) hE hζ
  exact ⟨⟨ι, hι, φ, χ, fun i => ⟨hinj i, hnorm i, hreg i, hact i⟩, hmem, horth, hspan, hker⟩⟩

end Planes

section Natural

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
theorem qplus_card_ge (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) :
    4 ≤ Nat.card K := by
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have := Nat.le_of_dvd (Nat.succ_pos _) hpq
  omega

theorem qplus_scalar_of_planeFix_ne_bot (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (Ã : Subgroup (orthDerived Q)) (hdata : QPlusData Q p A Ã)
    (hV0 : planeFixSpace Ã ≠ ⊥)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    σ = RingEquiv.refl K ∧ ∃ c : Kˣ, ∀ v, F v = (c : K) • v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq4 := qplus_card_ge hp hp3 hpq
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁₂, hM₁a, hM₂a⟩ := hdata.two
  have hline : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      ∃ c : Kˣ, ∀ v ∈ lineFixSpace M, F v = (c : K) • v := by
    intro M hM hMa
    have h3 : 3 ≤ finrank K (lineFixSpace M) := by
      have hdim2 := hdata.dim2 M hM hMa
      rw [hdata.decomp M hM]
      have := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace Ã) (lineSpace M)
      rw [disjoint_iff.mp (hdata.disj M hM), finrank_bot] at this
      have hpos : 1 ≤ finrank K (planeFixSpace Ã) := Submodule.one_le_finrank_iff.mpr hV0
      omega
    exact natural_line_scalar hQ hT hp hp3 hpl D hD A hA hAc Ã hdata.inA hdata.elem.2 hdata.inj σ F
      hFσ μ hμ hFQ κ hκF hcent M hM (hdata.ker M hM) h3 (fun h => absurd h (by omega))
      (fun h => absurd h (by omega))
  choose! c hc using hline
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  have hV0W : ∀ M : Subgroup Ã, Nat.card M = p → ∀ v ∈ planeFixSpace Ã, v ∈ lineFixSpace M :=
    fun M hM v hv => by
      rw [hdata.decomp M hM]
      exact Submodule.mem_sup_left hv
  have hVMW : ∀ M : Subgroup Ã, Nat.card M = p → ∀ v ∈ lineSpace M, v ∈ lineFixSpace M :=
    fun M hM v hv => by
      rw [hdata.decomp M hM]
      exact Submodule.mem_sup_right hv
  have hcc : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      ((c M : Kˣ) : K) = ((c M₁ : Kˣ) : K) := fun M hM hMa => by
    have h1 := hc M hM hMa v₀ (hV0W M hM v₀ hv₀)
    have h2 := hc M₁ hM₁ hM₁a v₀ (hV0W M₁ hM₁ v₀ hv₀)
    rw [h1] at h2
    exact smul_left_injective K hv₀0 h2
  have hall : ∀ v, F v = ((c M₁ : Kˣ) : K) • v := by
    refine hdata.glue F _ (fun v hv => hc M₁ hM₁ hM₁a v (hV0W M₁ hM₁ v hv)) fun M hM v hv => ?_
    by_cases hMa : lineSpace M = ⊥
    · have : v = 0 := (Submodule.mem_bot K).mp (hMa ▸ hv)
      rw [this, map_zero, smul_zero]
    · rw [← hcc M hM hMa]
      exact hc M hM hMa v (hVMW M hM v hv)
  exact ⟨eq_refl_of_scalar_line hFσ (c M₁).ne_zero hv₀0 fun t => hall (t • v₀), c M₁, hall⟩

end Natural

section Zero

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem qplus_scalar_of_planeFix_eq_bot (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (Ã : Subgroup (orthDerived Q))
    (hdata : QPlusData Q p A Ã) (hV0 : planeFixSpace Ã = ⊥)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    σ = RingEquiv.refl K ∧ ∃ c : Kˣ, ∀ v, F v = (c : K) • v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, _, _, hE, ζ, hζ⟩ := exists_quadratic_extension hp hp3 hpl hpq
  have hsp : ∀ M : Subgroup Ã, Nat.card M = p → SectorPlanes Q p Ã E ζ M := fun M hM =>
    (nonempty_sectorPlanes hp hp3 hpl hpq hdata hE hζ M hM).some
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁₂, hM₁a, hM₂a⟩ := hdata.two
  have hpair : ∀ (M N : Subgroup Ã) (hM : Nat.card M = p) (hN : Nat.card N = p), M ≠ N →
      ∀ (i : (hsp M hM).ι) (j : (hsp N hN).ι), σ = RingEquiv.refl K ∧ ∃ c : Kˣ,
        (∀ z, F ((hsp M hM).φ i z) = (c : K) • (hsp M hM).φ i z) ∧
        ∀ w, F ((hsp N hN).φ j w) = (c : K) • (hsp N hN).φ j w := by
    intro M N hM hN hMN i j
    refine pair_scalar hQ hT hp hp3 hpl hpq D hD A Ã hdata.elem hdata.card hdata.inA hdata.inj hE
      hζ ((hsp M hM).plane i) ((hsp N hN).plane j) (fun z w => ?_) ?_ σ F hFσ μ hμ hFQ κ hκF hcent
    · exact hdata.orth M N hM hN hMN _ ((hsp M hM).mem i z) _ ((hsp N hN).mem j w)
    · exact chars_independent hM hN hMN _ _ ((hsp M hM).ker i) ((hsp N hN).ker j)
  have hne : ∀ (M : Subgroup Ã) (hM : Nat.card M = p), lineSpace M ≠ ⊥ →
      Nonempty (hsp M hM).ι := by
    intro M hM hMa
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    apply hMa
    rw [← (hsp M hM).span]
    simp
  have hφ1 : ∀ (M : Subgroup Ã) (hM : Nat.card M = p) (i : (hsp M hM).ι),
      (hsp M hM).φ i 1 ≠ 0 := fun M hM i h =>
    one_ne_zero (((hsp M hM).plane i).1 (h.trans (map_zero _).symm))
  obtain ⟨i₁⟩ := hne M₁ hM₁ hM₁a
  obtain ⟨i₂⟩ := hne M₂ hM₂ hM₂a
  obtain ⟨hσ, c₀, hc₁, hc₂⟩ := hpair M₁ M₂ hM₁ hM₂ hM₁₂ i₁ i₂
  have hplane : ∀ (M : Subgroup Ã) (hM : Nat.card M = p) (i : (hsp M hM).ι) (z : E),
      F ((hsp M hM).φ i z) = (c₀ : K) • (hsp M hM).φ i z := by
    intro M hM i z
    by_cases hM1 : M = M₁
    · subst hM1
      obtain ⟨-, c', hc'1, hc'2⟩ := hpair M M₂ hM hM₂ hM₁₂ i i₂
      have hcc : (c' : K) = c₀ := smul_left_injective K (hφ1 M₂ hM₂ i₂)
        ((hc'2 1).symm.trans (hc₂ 1))
      rw [hc'1 z, hcc]
    · obtain ⟨-, c', hc'1, hc'2⟩ := hpair M₁ M hM₁ hM (Ne.symm hM1) i₁ i
      have hcc : (c' : K) = c₀ := smul_left_injective K (hφ1 M₁ hM₁ i₁)
        ((hc'1 1).symm.trans (hc₁ 1))
      rw [hc'2 z, hcc]
  have hall : ∀ v, F v = (c₀ : K) • v := by
    refine hdata.glue F _ (fun v hv => ?_) fun M hM v hv => ?_
    · rw [hV0, Submodule.mem_bot] at hv
      rw [hv, map_zero, smul_zero]
    · refine eq_smul_of_mem_iSup (S := fun i => LinearMap.range ((hsp M hM).φ i))
        (fun i v hv => ?_) ((hsp M hM).span ▸ hv)
      obtain ⟨z, rfl⟩ := hv
      exact hplane M hM i z
  exact ⟨hσ, c₀, hall⟩

end Zero

section Final

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem qplus_natural (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ v, F v = (c : K) • v) ∧ κ = 1 := by
  classical
  have hV3 : 3 ≤ finrank K V := by
    obtain ⟨U, hU3, -⟩ := hT
    exact hU3 ▸ Submodule.finrank_le U
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨Ã, hdata⟩ := qplus_data Q hQ hp hp3 hpl A hA hAc
  obtain ⟨hσ, c, hc⟩ : σ = RingEquiv.refl K ∧ ∃ c : Kˣ, ∀ v, F v = (c : K) • v := by
    by_cases hV0 : planeFixSpace Ã = ⊥
    · exact qplus_scalar_of_planeFix_eq_bot hQ hT hp hp3 hpl hpq D hD A Ã hdata hV0 σ F hFσ μ hμ
        hFQ κ hκF hcent
    · exact qplus_scalar_of_planeFix_ne_bot hQ hT hp hp3 hpl hpq D hD A hA hAc Ã hdata hV0 σ F hFσ
        μ hμ hFQ κ hκF hcent
  refine ⟨hσ, ⟨c, hc⟩, MulEquiv.ext fun t => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  refine (hκF g g fun v => ?_).trans (MulAut.one_apply _ _).symm
  rw [hc, ← map_smul, ← hc, AddEquiv.apply_symm_apply]

end Final

section Involution

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem qplus_exists_pair (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) :
    ∃ (Ã : Subgroup (orthDerived Q)) (_ : QPlusData Q p A Ã) (E : Type) (_ : Field E)
      (_ : Algebra K E) (ζ : E), finrank K E = 2 ∧ orderOf ζ = p ∧
      ∃ (φ₁ φ₂ : E →ₗ[K] V) (χ₁ χ₂ : Ã →* Multiplicative (ZMod p)),
        IsNormPlane Ã ζ φ₁ χ₁ ∧ IsNormPlane Ã ζ φ₂ χ₂ ∧
        (∀ z w, polar Q (φ₁ z) (φ₂ w) = 0) ∧
        (∀ s t : K, s • φ₁ 1 + t • φ₂ 1 = 0 → s = 0 ∧ t = 0) ∧
        (∀ m n : ZMod p, (∀ y : Ã, m * (χ₁ y).toAdd + n * (χ₂ y).toAdd = 0) → m = 0 ∧ n = 0) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hV3 : 3 ≤ finrank K V := by
    obtain ⟨U, hU3, -⟩ := hT
    exact hU3 ▸ Submodule.finrank_le U
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨Ã, hdata⟩ := qplus_data Q hQ hp hp3 hpl A hA hAc
  obtain ⟨E, _, _, hE, ζ, hζ⟩ := exists_quadratic_extension hp hp3 hpl hpq
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁₂, hM₁a, hM₂a⟩ := hdata.two
  obtain ⟨sp₁⟩ := nonempty_sectorPlanes hp hp3 hpl hpq hdata hE hζ M₁ hM₁
  obtain ⟨sp₂⟩ := nonempty_sectorPlanes hp hp3 hpl hpq hdata hE hζ M₂ hM₂
  have hne : ∀ (M : Subgroup Ã) (sp : SectorPlanes Q p Ã E ζ M), lineSpace M ≠ ⊥ →
      Nonempty sp.ι := by
    intro M sp hMa
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    apply hMa
    rw [← sp.span]
    simp
  obtain ⟨i₁⟩ := hne M₁ sp₁ hM₁a
  obtain ⟨i₂⟩ := hne M₂ sp₂ hM₂a
  refine ⟨Ã, hdata, E, inferInstance, inferInstance, ζ, hE, hζ, sp₁.φ i₁, sp₂.φ i₂, sp₁.χ i₁,
    sp₂.χ i₂, sp₁.plane i₁, sp₂.plane i₂, fun z w => ?_, ?_, ?_⟩
  · exact hdata.orth M₁ M₂ hM₁ hM₂ hM₁₂ _ (sp₁.mem i₁ z) _ (sp₂.mem i₂ w)
  ·
    have hsep : ∀ (M N : Subgroup Ã) (hM : Nat.card M = p) (hN : Nat.card N = p), M ≠ N →
        ∀ w : V, w ∈ lineSpace M → w ∈ lineSpace N → w = 0 := by
      intro M N hM hN hMN w hwM hwN
      have h0 : (⟨w, hwM⟩ : lineSpace M) = 0 := by
        refine (hdata.reg M hM).1 _ fun x => ?_
        show polarBilin (Q.comp (lineSpace M).subtype) ⟨w, hwM⟩ x = 0
        rw [polarBilin_apply_apply, polar_comp_subtype_eq]
        exact hdata.orth N M hN hM (Ne.symm hMN) w hwN x x.2
      exact congrArg Subtype.val h0
    intro s t hst
    have h1 : s • sp₁.φ i₁ 1 ∈ lineSpace M₁ := Submodule.smul_mem _ s (sp₁.mem i₁ 1)
    have h2 : s • sp₁.φ i₁ 1 ∈ lineSpace M₂ := by
      have : s • sp₁.φ i₁ 1 = -(t • sp₂.φ i₂ 1) := eq_neg_of_add_eq_zero_left hst
      rw [this]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ t (sp₂.mem i₂ 1))
    have hs0 : s • sp₁.φ i₁ 1 = 0 := hsep M₁ M₂ hM₁ hM₂ hM₁₂ _ h1 h2
    have h3 : t • sp₂.φ i₂ 1 ∈ lineSpace M₂ := Submodule.smul_mem _ t (sp₂.mem i₂ 1)
    have ht0 : t • sp₂.φ i₂ 1 = 0 := by
      have : t • sp₂.φ i₂ 1 = -(s • sp₁.φ i₁ 1) := eq_neg_of_add_eq_zero_right hst
      rw [this, hs0, neg_zero]
    have hφ₁ : sp₁.φ i₁ 1 ≠ 0 := fun h =>
      one_ne_zero ((sp₁.plane i₁).1 (h.trans (map_zero _).symm))
    have hφ₂ : sp₂.φ i₂ 1 ≠ 0 := fun h =>
      one_ne_zero ((sp₂.plane i₂).1 (h.trans (map_zero _).symm))
    exact ⟨(smul_eq_zero.mp hs0).resolve_right hφ₁, (smul_eq_zero.mp ht0).resolve_right hφ₂⟩
  · exact chars_independent hM₁ hM₂ hM₁₂ _ _ (sp₁.ker i₁) (sp₂.ker i₂)

theorem qplus_pair_involution (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hpq : p ∣ Nat.card K + 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (κ : MulAut (ProjOrthDerived Q))
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    ∃ (u v : V) (hg : reflect Q u * reflect Q v ∈ orthDerived Q), Q u = 1 ∧ Q v = 1 ∧
      polar Q u v = 0 ∧ (∀ s t : K, s • u + t • v = 0 → s = 0 ∧ t = 0) ∧
      orderOf (QuotientGroup.mk (⟨reflect Q u * reflect Q v, hg⟩ : orthDerived Q) :
        ProjOrthDerived Q) = 2 ∧
      ((2 : K) = 0 → reflect Q u * reflect Q v = eichler Q (u + v) u) ∧
      κ (QuotientGroup.mk (⟨reflect Q u * reflect Q v, hg⟩ : orthDerived Q)) =
        QuotientGroup.mk (⟨reflect Q u * reflect Q v, hg⟩ : orthDerived Q) := by
  obtain ⟨Ã, hdata, E, _, _, ζ, hE, hζ, φ₁, φ₂, χ₁, χ₂, h₁, h₂, horth, hind, hχ⟩ :=
    qplus_exists_pair hQ hT hp hp3 hpl hpq A hA hAc
  obtain ⟨-, hu1, hv1, huv, hg, hgord, heich, hfix⟩ := pair_fix hQ hT hp hp3 hpl hpq D hD A Ã
    hdata.elem hdata.card hdata.inA hdata.inj hE hζ h₁ h₂ horth hχ κ hcent
  exact ⟨φ₁ 1, φ₂ 1, hg, hu1, hv1, huv, hind, hgord, heich, hfix⟩

end Involution

end CFSG.RankThree.PartOne
