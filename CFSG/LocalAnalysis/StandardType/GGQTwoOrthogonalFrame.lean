module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoBasic
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public noncomputable section

namespace CFSG.StandardType.QTwoOrthogonalCav

open Module CFSG.Assembly CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

theorem mem_of_full_three_card
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {n : ℕ} (hdim : finrank K V = 2 * n)
    {E : Subgroup (V ≃ₗ[K] V)} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ n) {g : V ≃ₗ[K] V}
    (hg3 : g ^ 3 = 1) (hgE : ∀ e ∈ E, g * e = e * g) : g ∈ E := by
  classical
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun x : V ≃ₗ[K] V => (x : V → V)) DFunLike.coe_injective
  let C := Subgroup.zpowers g
  let S := E ⊔ C
  letI : CFSG.IsElementaryAbelian 3 E := hE.isElementaryAbelian
  letI : CFSG.IsElementaryAbelian 3 C :=
    (CFSG.Open.isElemAbelian_zpowers hg3).isElementaryAbelian
  have hCE : C ≤ Subgroup.centralizer (E : Set (V ≃ₗ[K] V)) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun e he => (hgE e he).symm)
  letI : CFSG.IsElementaryAbelian 3 S := CFSG.IsElementaryAbelian.sup_of_le_centralizer hCE
  have hS : CFSG.Open.IsElemAbelian 3 S := CFSG.Open.isElemAbelian_of_isElementaryAbelian
  let f := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm
  let X := S.map f.toMonoidHom
  have hX := hS.map f.toMonoidHom
  have hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hX.1.is_comm.comm (⟨x, hx⟩ : X) ⟨y, hy⟩)
  have hsq := TwoThree.card_sq_le_top hK X hc hX.2
  have hcardX : Nat.card X = Nat.card S := Subgroup.card_map_of_injective f.injective
  have hp : (3 : ℕ) ^ (2 * n) = (3 ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, pow_mul]
  rw [hcardX, hdim, hp] at hsq
  have hle : Nat.card S ≤ 3 ^ n := by nlinarith
  have hEq : E = S := Subgroup.eq_of_le_of_card_ge le_sup_left
    (by simpa only [hcard] using hle)
  rw [hEq]
  have hCS : C ≤ S := le_sup_right
  exact hCS (Subgroup.mem_zpowers g)

theorem exists_full_torus_data
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) (hn : 4 ≤ n)
    {E : Subgroup (V ≃ₗ[K] V)} (hEΩ : E ≤ orthDerived Q)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ n) :
    Nonempty (OrthTorus.TBJOmData Q 3 E n) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.exists_threeSingular hQ hdim (by
      by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · exact Or.inl ⟨hplus, by omega⟩
      · exact Or.inr ⟨hplus, hn⟩)
  have hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E :=
    fun g _ hg3 hcomm => mem_of_full_three_card hK hdim hE hcard hg3 hcomm
  have hne : ∃ b ∈ E, b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [hbot, Subgroup.card_bot] at hcard
    have hp : 1 < 3 ^ n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
    intro e he e' he'
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨e, he⟩ : E) ⟨e', he'⟩)
  obtain ⟨r, τ, F, D, i₁, i₂, i₃, c, θ, hτF, hinj, hrange, hdimD, hcp, hfix, hT', hroots,
    hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsign, hnoFix, hexFix⟩ :=
    OrthTorus.exists_torus_blocks (by decide : (3 : ℕ) ≠ 2)
      (Or.inr (by norm_num [hK])) hQ hT hEΩ hE.2 hc hmax hne
  let Δ : OrthTorus.TBJOmData Q 3 E r :=
    { τ := τ, F := F, D := D, c := c, θ := θ, τ_eq := hτF, τ_inj := hinj, τ_range := hrange,
      finrank_D := hdimD, c_pow := hcp, c_fix := hfix, c_twist := hT', c_roots := hroots,
      θ_inj := hθinj, θ_range := hθrange, θ_act := hθact, normalizer := hnorm,
      swapMove := hswap, dinvMove := hdinv, signMove := hsign, noFixed := hnoFix,
      exFixed := hexFix }
  have hcardRange := Subgroup.card_map_of_injective (K := (⊤ : Subgroup
    (Fin r → Multiplicative (ZMod 3)))) (f := τ) hinj
  rw [Subgroup.map_top, hrange, Subgroup.card_top] at hcardRange
  have hcoord : Nat.card (Fin r → Multiplicative (ZMod 3)) = 3 ^ r := by
    rw [Nat.card_eq_fintype_card]
    simp
  rw [hcoord, hcard] at hcardRange
  have hr : r = n := Nat.le_antisymm
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp (Nat.le_of_eq hcardRange.symm))
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp (Nat.le_of_eq hcardRange))
  subst r
  exact ⟨Δ⟩

theorem full_data_fixed_free
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) {E : Subgroup (V ≃ₗ[K] V)}
    (Δ : OrthTorus.TBJOmData Q 3 E n) :
    ∀ v : V, Δ.F.ι (Multiplicative.ofAdd (fun _ : Fin n => (1 : ZMod 3))) v = v → v = 0 := by
  classical
  have hU : ∀ j, finrank K (Δ.F.U j) = 2 := by
    intro j
    rw [← Δ.θ_range j, LinearMap.finrank_range_of_inj (Δ.θ_inj j), Δ.finrank_D]
  let s : Multiplicative (Fin n → ZMod 3) := Multiplicative.ofAdd fun _ => 1
  have hdfix : finrank K (fixedSpace (Δ.F.ι s)) = 0 := by
    rw [CFSG.StandardType.OrthTorusGen.fixedSpace_eq_suppPerp_frame Δ.F s,
      suppPerp,
      LinearMap.BilinForm.finrank_orthogonal (B := QuadraticMap.polarBilin Q) hQ,
      CFSG.StandardType.OrthTorusGen.finrank_iSup_frame_pieces Δ.F hU]
    change finrank K V - 2 * Fintype.card {j : Fin n // (1 : ZMod 3) ≠ 0} = 0
    have hc : Fintype.card {j : Fin n // (1 : ZMod 3) ≠ 0} = n := by simp
    rw [hc, hdim]
    omega
  have hbot : fixedSpace (Δ.F.ι s) = ⊥ :=
    Submodule.finrank_eq_zero.mp hdfix
  intro v hv
  have hmem : v ∈ fixedSpace (Δ.F.ι s) := mem_fixedSpace.mpr hv
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

theorem full_data_type
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) {E : Subgroup (V ≃ₗ[K] V)}
    (hEΩ : E ≤ orthDerived Q) (Δ : OrthTorus.TBJOmData Q 3 E n) :
    CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even n := by
  let s : Multiplicative (Fin n → ZMod 3) := Multiplicative.ofAdd fun _ => 1
  have hx : OddOrderIsometry Q 3 (Δ.F.ι s) :=
    Δ.F.oddOrderIsometry hQ (by decide) Nat.prime_three hEΩ s
  have hreg : CFSG.RankThree.PartOne.K159.RegOn Q (⊤ : Submodule K V) := by
    intro u _ hu
    exact hx.regular u (fun w => hu w (Submodule.mem_top))
  have htype := CFSG.RankThree.PartOne.K159.isPlusType_iff_even_of_fixedFree hx
    Nat.prime_three (by decide) (by norm_num [hK]) n (⊤ : Submodule K V)
    (fun _ _ => Submodule.mem_top) hreg
    (fun v _ hv => full_data_fixed_free hQ hdim Δ v hv)
    (by simpa only [finrank_top] using hdim)
  exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.isPlusType_comp_top_iff
    (Q := Q)).symm.trans htype

theorem full_data_fixed_four_plus
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) {E : Subgroup (V ≃ₗ[K] V)}
    (hEΩ : E ≤ orthDerived Q) (Δ : OrthTorus.TBJOmData Q 3 E n)
    (f : Fin n → Multiplicative (ZMod 3))
    (hfix : finrank K (fixedSpace (Δ.τ f)) = 4) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (Δ.τ f)).subtype) := by
  have hx : OddOrderIsometry Q 3 (Δ.τ f) := by
    rw [Δ.τ_eq]
    exact Δ.F.oddOrderIsometry hQ (by decide) Nat.prime_three hEΩ _
  have hpar : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even (finrank K V / 2) := by
    rw [hdim, Nat.mul_div_right n (by decide : 0 < 2)]
    exact full_data_type hK hQ hdim hEΩ Δ
  have htype := CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.isPlusType_fixedSpace_iff hK hx hpar
  exact htype.mpr (by rw [hfix]; decide)

theorem full_data_finrank_fixed
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) {E : Subgroup (V ≃ₗ[K] V)}
    (Δ : OrthTorus.TBJOmData Q 3 E n) (f : Fin n → Multiplicative (ZMod 3)) :
    finrank K (fixedSpace (Δ.τ f)) =
      2 * Fintype.card {j : Fin n // Multiplicative.toAdd (f j) = 0} := by
  classical
  rw [Δ.τ_eq, CFSG.StandardType.OrthTorusGen.fixedSpace_eq_suppPerp_frame,
    suppPerp, LinearMap.BilinForm.finrank_orthogonal (B := QuadraticMap.polarBilin Q) hQ,
    CFSG.StandardType.OrthTorusGen.finrank_iSup_frame_pieces Δ.F Δ.finrank_piece, hdim]
  change 2 * n - 2 * Fintype.card {j : Fin n // Multiplicative.toAdd (f j) ≠ 0} =
    2 * Fintype.card {j : Fin n // Multiplicative.toAdd (f j) = 0}
  have hc := Fintype.card_subtype_compl (fun j : Fin n => Multiplicative.toAdd (f j) ≠ 0)
  simp only [not_not, Fintype.card_fin] at hc
  omega

theorem full_data_exists_three_zero
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) {E : Subgroup (V ≃ₗ[K] V)}
    (Δ : OrthTorus.TBJOmData Q 3 E n) (f : Fin n → Multiplicative (ZMod 3))
    (h6 : 6 ≤ finrank K (fixedSpace (Δ.τ f))) :
    ∃ i k l : Fin n, Multiplicative.toAdd (f i) = 0 ∧
      Multiplicative.toAdd (f k) = 0 ∧ Multiplicative.toAdd (f l) = 0 ∧
      i ≠ k ∧ i ≠ l ∧ k ≠ l := by
  classical
  rw [full_data_finrank_fixed hQ hdim Δ f] at h6
  have hc : 2 < Fintype.card {j : Fin n // Multiplicative.toAdd (f j) = 0} := by omega
  obtain ⟨i, k, l, hik, hil, hkl⟩ := Fintype.two_lt_card_iff.mp hc
  exact ⟨i.1, k.1, l.1, i.2, k.2, l.2,
    fun h => hik (Subtype.ext h), fun h => hil (Subtype.ext h), fun h => hkl (Subtype.ext h)⟩

end CFSG.StandardType.QTwoOrthogonalCav

end
