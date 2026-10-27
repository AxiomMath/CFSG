module

public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlock
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthSymmetry
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups

public noncomputable section

namespace CFSG.OddTranspositions.PartFour

open Matrix Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem linearIndependent_pair_of_map_eq_one [CharP K 2] {v w : V} (hv : Q v = 1) (hw : Q w = 1)
    (hvw : v ≠ w) : LinearIndependent K ![v, w] := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  rw [LinearIndependent.pair_iff' hv0]
  rintro a rfl
  rw [QuadraticMap.map_smul, hv, smul_eq_mul, mul_one] at hw
  have ha : a = 1 := CharTwo.sq_inj.mp (by rw [_root_.sq, one_pow, hw])
  exact hvw (by rw [ha, one_smul])

theorem linearIndependent_pair_of_polar_ne_zero [CharP K 2] {x y : V} (hx : x ≠ 0)
    (hxy : polar Q x y ≠ 0) : LinearIndependent K ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hxx : polar Q x x = 0 := by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have h := congrArg (fun u => polar Q x u) hab
  simp only [polar_add_right, polar_smul_right, hxx, smul_eq_mul, mul_zero, zero_add,
    polar_zero_right] at h
  have hb : b = 0 := (mul_eq_zero.mp h).resolve_right hxy
  rw [hb, zero_smul, add_zero] at hab
  exact ⟨(smul_eq_zero.mp hab).resolve_right hx, hb⟩

theorem exists_mem_map_eq_of_polar_ne_zero [Finite K] [CharP K 2] {W : Submodule K V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (hxy : polar Q x y ≠ 0) (t : K) : ∃ p ∈ W, Q p = t := by
  by_cases ht : t = 0
  · exact ⟨0, W.zero_mem, by rw [ht, QuadraticMap.map_zero]⟩
  obtain ⟨u, huW, hu⟩ : ∃ u ∈ W, Q u ≠ 0 := by
    by_contra! h
    refine hxy ?_
    rw [polar, h x hx, h y hy, h (x + y) (W.add_mem hx hy)]
    ring
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (t / Q u)
  refine ⟨μ • u, W.smul_mem μ huW, ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, ← hμ, div_mul_cancel₀ _ hu]

theorem exists_add_mem_map_eq [Finite K] [CharP K 2] {W : Submodule K V} {x y : V} (hx : x ∈ W)
    (hy : y ∈ W) (hxy : polar Q x y ≠ 0) (u₀ : V) (t : K) : ∃ w ∈ W, Q (u₀ + w) = t := by
  have hxx : polar Q x x = 0 := by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hyy : polar Q y y = 0 := by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hyx : polar Q y x = polar Q x y := polar_comm Q y x
  set α : K := -(polar Q u₀ x / polar Q x y) with hα
  set β : K := -(polar Q u₀ y / polar Q x y) with hβ
  set u₁ : V := u₀ + β • x + α • y with hu₁
  have hαπ : α * polar Q x y = -polar Q u₀ x := by
    rw [hα, neg_mul, div_mul_cancel₀ _ hxy]
  have hβπ : β * polar Q x y = -polar Q u₀ y := by
    rw [hβ, neg_mul, div_mul_cancel₀ _ hxy]
  have h1 : polar Q u₁ x = 0 := by
    rw [hu₁, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hxx, hyx,
      smul_eq_mul, smul_eq_mul, hαπ]
    ring
  have h2 : polar Q u₁ y = 0 := by
    rw [hu₁, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hyy, smul_eq_mul,
      smul_eq_mul, hβπ]
    ring
  obtain ⟨p, hpU, hp⟩ := exists_mem_map_eq_of_polar_ne_zero (Q := Q)
    (W := Submodule.span K {x, y}) (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp)) hxy (t - Q u₁)
  have hpW : p ∈ W := (Submodule.span_le.mpr (Set.pair_subset hx hy)) hpU
  have hp0 : polar Q u₁ p = 0 := by
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hpU
    rw [polar_add_right, polar_smul_right, polar_smul_right, h1, h2]
    simp
  refine ⟨β • x + α • y + p, W.add_mem (W.add_mem (W.smul_mem β hx) (W.smul_mem α hy)) hpW, ?_⟩
  have hsum : u₀ + (β • x + α • y + p) = u₁ + p := by
    rw [hu₁]
    abel
  rw [hsum, QuadraticMap.map_add Q u₁ p, hp, hp0]
  ring

private abbrev orthOfPair (Q : QuadraticForm K V) (a b : V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span K (Set.range ![a, b]))

private theorem mem_orthOfPair_iff {a b : V} (u : V) :
    u ∈ orthOfPair Q a b ↔ polar Q u a = 0 ∧ polar Q u b = 0 := by
  rw [orthOfPair, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [polar_comm]
      exact h a (Submodule.subset_span ⟨0, rfl⟩)
    · rw [polar_comm]
      exact h b (Submodule.subset_span ⟨1, rfl⟩)
  · rintro ⟨ha, hb⟩ n hn
    induction hn using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · simpa [polar_comm Q a u] using ha
      · simpa [polar_comm Q b u] using hb
    | zero => simp
    | add z z' _ _ h h' => rw [map_add, LinearMap.add_apply, h, h', add_zero]
    | smul r z _ h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]

private theorem finrank_orthOfPair [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {a b : V} (hab : LinearIndependent K ![a, b]) :
    finrank K (orthOfPair Q a b) = finrank K V - 2 := by
  have hUrank : finrank K (Submodule.span K (Set.range ![a, b])) = 2 := by
    rw [finrank_span_eq_card hab]
    simp
  rw [orthOfPair, LinearMap.BilinForm.finrank_orthogonal hQ, hUrank]

theorem exists_polar_eq_pair_of_linearIndependent [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) {a b : V} (hab : LinearIndependent K ![a, b])
    (c₁ c₂ : K) : ∃ u, polar Q u a = c₁ ∧ polar Q u b = c₂ := by
  let M : V →ₗ[K] K × K := (Q.polarBilin.flip a).prod (Q.polarBilin.flip b)
  have hker : LinearMap.ker M = orthOfPair Q a b := by
    ext u
    rw [LinearMap.mem_ker, mem_orthOfPair_iff, Prod.ext_iff]
    simp [M]
  have hV : 2 ≤ finrank K V := by simpa using hab.fintype_card_le_finrank
  have hMrange : LinearMap.range M = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := LinearMap.finrank_range_add_finrank_ker M
    rw [hker, finrank_orthOfPair hQ hab] at h
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, M u₀ = (c₁, c₂) := by
    have : ((c₁, c₂) : K × K) ∈ LinearMap.range M := by rw [hMrange]; trivial
    exact this
  exact ⟨u₀, congrArg Prod.fst hu₀, congrArg Prod.snd hu₀⟩

private theorem exists_polar_eq_map_eq_of_exists_polar_ne_zero [Finite K] [CharP K 2]
    [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate) {a b : V}
    (hab : LinearIndependent K ![a, b])
    (hiso : ∃ x ∈ orthOfPair Q a b, ∃ y ∈ orthOfPair Q a b, polar Q x y ≠ 0)
    (c₁ c₂ t : K) : ∃ u, polar Q u a = c₁ ∧ polar Q u b = c₂ ∧ Q u = t := by
  obtain ⟨u₀, hu₀a, hu₀b⟩ := exists_polar_eq_pair_of_linearIndependent hQ hab c₁ c₂
  obtain ⟨x, hxW, y, hyW, hxy⟩ := hiso
  obtain ⟨w, hwW, hw⟩ := exists_add_mem_map_eq hxW hyW hxy u₀ t
  obtain ⟨hwa, hwb⟩ := (mem_orthOfPair_iff w).mp hwW
  refine ⟨u₀ + w, ?_, ?_, hw⟩
  · rw [polar_add_left, hu₀a, hwa, add_zero]
  · rw [polar_add_left, hu₀b, hwb, add_zero]

theorem exists_polar_eq_map_eq [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) (hV : 5 ≤ finrank K V) {a b : V}
    (hab : LinearIndependent K ![a, b]) (c₁ c₂ t : K) :
    ∃ u, polar Q u a = c₁ ∧ polar Q u b = c₂ ∧ Q u = t := by
  refine exists_polar_eq_map_eq_of_exists_polar_ne_zero hQ hab ?_ c₁ c₂ t
  by_contra! h
  set W : Submodule K V := orthOfPair Q a b with hW
  have hWrank : finrank K W = finrank K V - 2 := finrank_orthOfPair hQ hab
  have hle : W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := fun x hx y hy => h y hy x hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ W, hWrank] at h1
  omega

theorem exists_polar_eq_map_eq_of_polar_ne_zero [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) (hV : 3 ≤ finrank K V) {a b : V} (hab : polar Q a b ≠ 0)
    (c₁ c₂ t : K) : ∃ u, polar Q u a = c₁ ∧ polar Q u b = c₂ ∧ Q u = t := by
  have haa : polar Q a a = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hbb : polar Q b b = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hba : polar Q b a ≠ 0 := by rwa [polar_comm]
  have ha : a ≠ 0 := fun h => hab (by rw [h, polar_zero_left])
  have hind : LinearIndependent K ![a, b] := linearIndependent_pair_of_polar_ne_zero ha hab
  refine exists_polar_eq_map_eq_of_exists_polar_ne_zero hQ hind ?_ c₁ c₂ t
  by_contra! h
  set U : Submodule K V := Submodule.span K (Set.range ![a, b]) with hU
  set W : Submodule K V := orthOfPair Q a b with hW
  have hrefl : Q.polarBilin.IsRefl := fun x y hxy => by
    rw [QuadraticMap.polarBilin_apply_apply] at hxy ⊢
    rwa [polar_comm]
  have hle : W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := fun x hx y hy => h y hy x hx
  have hWW : LinearMap.BilinForm.orthogonal Q.polarBilin W = U :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl U
  rw [hWW] at hle
  have hW0 : W = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwa, hwb⟩ := (mem_orthOfPair_iff w).mp hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hle hw)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      polar_add_left, polar_smul_left, smul_eq_mul, haa, hbb, mul_zero, zero_add,
      add_zero] at hwa hwb
    have hc1 : c 1 = 0 := (mul_eq_zero.mp hwa).resolve_right hba
    have hc0 : c 0 = 0 := (mul_eq_zero.mp hwb).resolve_right hab
    simp [Fin.sum_univ_two, hc0, hc1]
  have hrank : finrank K W = finrank K V - 2 := finrank_orthOfPair hQ hind
  rw [hW0, finrank_bot] at hrank
  omega

theorem exists_polar_eq_map_eq_of_polar_eq_zero [CharP K 2] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) {a b : V} (hab : LinearIndependent K ![a, b])
    (hpol : polar Q a b = 0) (hQab : Q a = Q b) {c₁ c₂ : K} (hc : c₁ ≠ c₂) (t : K) :
    ∃ u, polar Q u a = c₁ ∧ polar Q u b = c₂ ∧ Q u = t := by
  obtain ⟨u₀, hu₀a, hu₀b⟩ := exists_polar_eq_pair_of_linearIndependent hQ hab c₁ c₂
  have haa : polar Q a a = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hbb : polar Q b b = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hpol' : polar Q b a = 0 := by rw [polar_comm, hpol]
  have hra : polar Q (a + b) a = 0 := by rw [polar_add_left, haa, hpol', add_zero]
  have hrb : polar Q (a + b) b = 0 := by rw [polar_add_left, hpol, hbb, add_zero]
  have hQr : Q (a + b) = 0 := by
    rw [QuadraticMap.map_add Q a b, hpol, hQab, add_zero, CharTwo.add_self_eq_zero]
  have hur : polar Q u₀ (a + b) = c₁ + c₂ := by rw [polar_add_right, hu₀a, hu₀b]
  have hc' : c₁ + c₂ ≠ 0 := fun h => hc (CharTwo.add_eq_zero.mp h)
  refine ⟨u₀ + ((t - Q u₀) / (c₁ + c₂)) • (a + b), ?_, ?_, ?_⟩
  · rw [polar_add_left, polar_smul_left, hra, smul_zero, add_zero, hu₀a]
  · rw [polar_add_left, polar_smul_left, hrb, smul_zero, add_zero, hu₀b]
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQr, polar_smul_right, hur, smul_eq_mul,
      smul_eq_mul, mul_zero, add_zero, div_mul_cancel₀ _ hc']
    ring

theorem exists_eq_smul_add_smul_of_forall_polar_eq_zero [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) {a b x : V}
    (h : ∀ w, polar Q w a = 0 → polar Q w b = 0 → polar Q x w = 0) :
    ∃ α β : K, x = α • a + β • b := by
  have hrefl : Q.polarBilin.IsRefl := fun y z hyz => by
    rw [QuadraticMap.polarBilin_apply_apply] at hyz ⊢
    rwa [polar_comm]
  have hx : x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (orthOfPair Q a b) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨hwa, hwb⟩ := (mem_orthOfPair_iff w).mp hw
    rw [QuadraticMap.polarBilin_apply_apply, polar_comm]
    exact h w hwa hwb
  have hxU : x ∈ Submodule.span K (Set.range ![a, b]) := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl
      (Submodule.span K (Set.range ![a, b]))]
    exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxU
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  rfl

end LinearAlgebra

section SymmetryModel

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
private theorem exists_mem_matrixIsometries_mulVec_eq (hQ : Q.polarBilin.Nondegenerate) {k : ℕ}
    (u u' : Fin k → Fin d → K) (hu : LinearIndependent K u) (hu' : LinearIndependent K u')
    (hQu : ∀ i, Q (u' i) = Q (u i))
    (hpol : ∀ i j, polar Q (u' i) (u' j) = polar Q (u i) (u j)) :
    ∃ A ∈ matrixIsometries Q, ∀ i, (A : Matrix (Fin d) (Fin d) K) *ᵥ u i = u' i := by
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ u u' hu hu' hQu hpol
  refine ⟨matrixLinearIso.symm g, ?_, fun i => ?_⟩
  · change matrixLinearIso (matrixLinearIso.symm g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [MulEquiv.apply_symm_apply]
    exact hg
  · change matrixLinearIso (matrixLinearIso.symm g) (u i) = u' i
    rw [MulEquiv.apply_symm_apply]
    exact hgu i

omit [Finite K] in
private theorem exists_isConj_symmetry {X : Type} [Group X] (hQ : Q.polarBilin.Nondegenerate)
    (ψ : X →* GL (Fin d) K) (hrange : ψ.range = matrixIsometries Q) {s : X} {v : Fin d → K}
    (hv : Q v = 1) (hψs : ψ s = symmetryGL Q v) {x : Fin d → K} (hx : Q x = 1) :
    ∃ t, IsConj s t ∧ ψ t = symmetryGL Q x := by
  have hψmem : ∀ g, ψ g ∈ matrixIsometries Q := fun g => hrange ▸ ⟨g, rfl⟩
  have hpolar_self : ∀ y : Fin d → K, polar Q y y = 0 := fun y => by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hv0 : v ≠ 0 := fun h0 => by
    rw [h0, QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hx0 : x ≠ 0 := fun h0 => by
    rw [h0, QuadraticMap.map_zero] at hx
    exact zero_ne_one hx
  obtain ⟨A, hA, hAv⟩ := exists_mem_matrixIsometries_mulVec_eq hQ (k := 1) ![v] ![x]
    (linearIndependent_unique_iff.2 (by simpa using hv0))
    (linearIndependent_unique_iff.2 (by simpa using hx0))
    (fun i => by simpa using hx.trans hv.symm)
    (fun i j => by simp only [Matrix.cons_val_fin_one, hpolar_self])
  obtain ⟨g, rfl⟩ : ∃ g, ψ g = A := by
    rw [← hrange] at hA
    exact hA
  have hAv' : (ψ g : Matrix (Fin d) (Fin d) K) *ᵥ v = x := by simpa using hAv 0
  refine ⟨g * s * g⁻¹, isConj_iff.mpr ⟨g, rfl⟩, ?_⟩
  rw [map_mul, map_mul, map_inv, hψs, conj_symmetryGL (hψmem g), hAv']

private theorem subsingleton_and_ne_of_symmetry_model {X : Type} [Group X] {E : Set X}
    (hQ : Q.polarBilin.Nondegenerate) (hd : 4 ≤ d) (hK : 5 ≤ d ∨ ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1)
    (ψ : X →* GL (Fin d) K) (hψ : Function.Injective ψ)
    (hrange : ψ.range = matrixIsometries Q) (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) {s : X}
    (hs : s ∈ E) {v : Fin d → K} (hv : Q v = 1) (hψs : ψ s = symmetryGL Q v) :
    (∀ β, IsBlock E β → β.Subsingleton) ∧ rootBlock E s ≠ E := by
  classical
  have hdim : 3 ≤ finrank K (Fin d → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have hψmem : ∀ g, ψ g ∈ matrixIsometries Q := fun g => hrange ▸ ⟨g, rfl⟩
  have hψsurj : ∀ A ∈ matrixIsometries Q, ∃ g, ψ g = A := fun A hA => by
    rw [← hrange] at hA
    exact hA
  have hnorm : ∀ (g : X) (x : Fin d → K), Q ((ψ g : Matrix (Fin d) (Fin d) K) *ᵥ x) = Q x :=
    fun g x => (mem_matrixIsometries_iff Q _).mp (hψmem g) x
  have hS : ∀ x y : Fin d → K, Q x = 1 →
      (symmetryGL Q x : Matrix (Fin d) (Fin d) K) *ᵥ y = y + polar Q x y • x :=
    fun x y hx => symmetryGL_mulVec_of_charTwo hx y
  have hpolar_self : ∀ x : Fin d → K, polar Q x x = 0 := fun x => by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hne0 : ∀ x : Fin d → K, Q x = 1 → x ≠ 0 := fun x hx h0 => by
    rw [h0, QuadraticMap.map_zero] at hx
    exact zero_ne_one hx
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hconjE : ∀ g x, x ∈ E → g * x * g⁻¹ ∈ E := fun g x hx =>
    (hEs _).mpr (((hEs x).mp hx).trans (isConj_iff.mpr ⟨g, rfl⟩))
  have hEref : ∀ u ∈ E, ∃ x, Q x = 1 ∧ ψ u = symmetryGL Q x := by
    intro u hu
    obtain ⟨c, rfl⟩ := isConj_iff.mp ((hEs u).mp hu)
    refine ⟨(ψ c : Matrix (Fin d) (Fin d) K) *ᵥ v, by rw [hnorm, hv], ?_⟩
    rw [map_mul, map_mul, map_inv, hψs, conj_symmetryGL (hψmem c)]
  have hne : rootBlock E s ≠ E := by
    intro hEq
    have hv0 := hne0 v hv
    obtain ⟨b, hvb⟩ : ∃ b, polar Q v b ≠ 0 := by
      by_contra! h0
      exact hv0 (hQ.1 v fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
    obtain ⟨x, hxv, -, hx⟩ := exists_polar_eq_map_eq_of_polar_ne_zero hQ hdim hvb 1 0 1
    have hx0 := hne0 x hx
    obtain ⟨A, hA, hAv⟩ := exists_mem_matrixIsometries_mulVec_eq hQ (k := 1) ![v] ![x]
      (linearIndependent_unique_iff.2 (by simpa using hv0))
      (linearIndependent_unique_iff.2 (by simpa using hx0))
      (fun i => by simpa using hx.trans hv.symm)
      (fun i j => by simp only [Matrix.cons_val_fin_one, hpolar_self])
    obtain ⟨g, rfl⟩ := hψsurj A hA
    have hAv' : (ψ g : Matrix (Fin d) (Fin d) K) *ᵥ v = x := by simpa using hAv 0
    have htE : g * s * g⁻¹ ∈ E := hconjE g s hs
    have ht : ψ (g * s * g⁻¹) = symmetryGL Q x := by
      rw [map_mul, map_mul, map_inv, hψs, conj_symmetryGL (hψmem g), hAv']
    rw [← hEq] at htE
    have h1 : Commute s (g * s * g⁻¹) := (htE.2 s hs).mpr (Commute.refl s)
    have h2 : symmetryGL Q x ∈ Subgroup.centralizer {symmetryGL Q v} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 := (h1.map ψ).eq
      rw [hψs, ht] at h3
      exact h3.symm
    have h4 := (mem_centralizer_symmetryGL_iff hQ hv (symmetryGL_mem Q x)).mp h2
    rw [hS x v hx, hxv, one_smul] at h4
    exact hx0 (add_eq_left.mp h4)
  refine ⟨fun β hβ a ha b hb => ?_, hne⟩
  by_contra hab
  obtain ⟨va, hva, hψa⟩ := hEref a (hβ.1 ha)
  obtain ⟨vb, hvb, hψb⟩ := hEref b (hβ.1 hb)
  have hvab : va ≠ vb := fun h => hab (hψ (by rw [hψa, hψb, h]))
  have hCN : ∀ x ∈ β, ∀ g : X, Commute g x → g ∈ Subgroup.normalizer β := by
    intro x hx g hg
    by_contra hgN
    refine Set.disjoint_left.mp (hβ.2.2.2 g hgN) hx ⟨x, hx, ?_⟩
    change g * x * g⁻¹ = x
    rw [hg.eq, mul_inv_cancel_right]
  have hNmem : ∀ g ∈ Subgroup.normalizer β, ∀ x ∈ β, g * x * g⁻¹ ∈ β := by
    intro g hg x hx
    have h1 := Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  set T : Set (Fin d → K) := {x | Q x = 1 ∧ ∃ t' ∈ β, ψ t' = symmetryGL Q x} with hT
  have hvaT : va ∈ T := ⟨hva, a, ha, hψa⟩
  have hvbT : vb ∈ T := ⟨hvb, b, hb, hψb⟩
  have hT1 : ∀ x ∈ T, ∀ g : X, (ψ g : Matrix (Fin d) (Fin d) K) *ᵥ x = x →
      g ∈ Subgroup.normalizer β := by
    rintro x ⟨hx, t', ht'β, ht'⟩ g hg
    refine hCN t' ht'β g ?_
    have h1 : ψ (g * t' * g⁻¹) = ψ t' := by
      rw [map_mul, map_mul, map_inv, ht', conj_symmetryGL (hψmem g), hg]
    have h2 : g * t' * g⁻¹ = t' := hψ h1
    change g * t' = t' * g
    calc g * t' = g * t' * g⁻¹ * g := by group
      _ = t' * g := by rw [h2]
  have hT3 : ∀ x ∈ T, ∀ g ∈ Subgroup.normalizer β,
      (ψ g : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ T := by
    rintro x ⟨hx, t', ht'β, ht'⟩ g hg
    refine ⟨by rw [hnorm, hx], g * t' * g⁻¹, hNmem g hg t' ht'β, ?_⟩
    rw [map_mul, map_mul, map_inv, ht', conj_symmetryGL (hψmem g)]
  have hT5 : ∀ x ∈ T, ∀ y ∈ T, polar Q x y ≠ 0 → ∀ z, Q z = 1 → polar Q z x = polar Q y x →
      z ∈ T := by
    intro x hxT y hyT hxy z hz hzx
    have hx1 := hxT.1
    have hy1 := hyT.1
    have hxz : polar Q x z = polar Q x y := by
      rw [polar_comm Q x z, hzx, polar_comm Q y x]
    obtain ⟨A, hA, hAu⟩ := exists_mem_matrixIsometries_mulVec_eq hQ (k := 2) ![x, y] ![x, z]
      (linearIndependent_pair_of_polar_ne_zero (hne0 x hx1) hxy)
      (linearIndependent_pair_of_polar_ne_zero (hne0 x hx1) (by rw [hxz]; exact hxy))
      (fun i => by fin_cases i <;> simp [hz, hy1])
      (fun i j => by
        fin_cases i <;> fin_cases j
        · rfl
        · exact hxz
        · exact hzx
        · exact (hpolar_self z).trans (hpolar_self y).symm)
    obtain ⟨g, rfl⟩ := hψsurj A hA
    have hgx : (ψ g : Matrix (Fin d) (Fin d) K) *ᵥ x = x := by simpa using hAu 0
    have hgy : (ψ g : Matrix (Fin d) (Fin d) K) *ᵥ y = z := by simpa using hAu 1
    have h := hT3 y hyT g (hT1 x hxT g hgx)
    rwa [hgy] at h
  obtain ⟨y, hyb, hya, hy1⟩ : ∃ y, polar Q y vb = 0 ∧ polar Q y va = 1 ∧ Q y = 1 := by
    by_cases hpab : polar Q vb va = 0
    · exact exists_polar_eq_map_eq_of_polar_eq_zero hQ
        (linearIndependent_pair_of_map_eq_one hvb hva (Ne.symm hvab)) hpab (hvb.trans hva.symm)
        zero_ne_one 1
    · exact exists_polar_eq_map_eq_of_polar_ne_zero hQ hdim hpab 0 1 1
  obtain ⟨gy, hgy⟩ := hψsurj (symmetryGL Q y) (symmetryGL_mem Q y)
  have hgyN : gy ∈ Subgroup.normalizer β :=
    hT1 vb hvbT gy (by rw [hgy, hS y vb hy1, hyb, zero_smul, add_zero])
  have hva₁ : va + y ∈ T := by
    have h := hT3 va hvaT gy hgyN
    rwa [hgy, hS y va hy1, hya, one_smul] at h
  have hva₁a : polar Q (va + y) va = 1 := by
    rw [polar_add_left, hpolar_self, hya, zero_add]
  have hstep2 : ∀ x ∈ T, ∀ x₁ ∈ T, polar Q x x₁ ≠ 0 → ∀ z, Q z = 1 → polar Q x z ≠ 0 →
      z ∈ T := by
    intro x hxT x₁ hx₁T hxx₁ z hz hxz
    have hxx₁' : polar Q x₁ x ≠ 0 := by rwa [polar_comm]
    obtain ⟨y', hy'x, hy'z, hy'1⟩ := exists_polar_eq_map_eq_of_polar_ne_zero hQ hdim hxz
      (polar Q x₁ x) (polar Q x₁ x) 1
    have hy'T : y' ∈ T := hT5 x hxT x₁ hx₁T hxx₁ y' hy'1 hy'x
    refine hT5 y' hy'T x hxT (by rw [hy'x]; exact hxx₁') z hz ?_
    rw [polar_comm Q z y', hy'z, polar_comm Q x y', hy'x]
  have hv1 : ∀ z, Q z = 1 → polar Q va z ≠ 0 → z ∈ T := by
    intro z hz hvz
    refine hstep2 va hvaT (va + y) hva₁ ?_ z hz hvz
    rw [polar_comm, hva₁a]
    exact one_ne_zero
  have hall : ∀ z, Q z = 1 → z ∈ T := by
    intro z hz
    by_cases hvz : polar Q va z = 0
    · by_cases hzv : z = va
      · rw [hzv]
        exact hvaT
      obtain ⟨u, hu1, huv, huz⟩ : ∃ u, Q u = 1 ∧ polar Q u va ≠ 0 ∧ polar Q u z ≠ 0 := by
        rcases hK with h5 | ⟨ω, hω0, hω1⟩
        · obtain ⟨u, huv, huz, hu1⟩ := exists_polar_eq_map_eq hQ (by rwa [Module.finrank_fin_fun])
            (linearIndependent_pair_of_map_eq_one hva hz (Ne.symm hzv)) 1 1 1
          exact ⟨u, hu1, by rw [huv]; exact one_ne_zero, by rw [huz]; exact one_ne_zero⟩
        · obtain ⟨u, huv, huz, hu1⟩ := exists_polar_eq_map_eq_of_polar_eq_zero hQ
            (linearIndependent_pair_of_map_eq_one hva hz (Ne.symm hzv)) hvz (hva.trans hz.symm)
            (c₁ := 1) (c₂ := ω) (Ne.symm hω1) 1
          exact ⟨u, hu1, by rw [huv]; exact one_ne_zero, by rw [huz]; exact hω0⟩
      have huT : u ∈ T := hv1 u hu1 (by rw [polar_comm]; exact huv)
      exact hstep2 u huT va hvaT huv z hz huz
    · exact hv1 z hz hvz
  have hEβ : E ⊆ β := by
    intro u hu
    obtain ⟨x, hx, hux⟩ := hEref u hu
    obtain ⟨-, t', ht'β, ht'⟩ := hall x hx
    have h : t' = u := hψ (ht'.trans hux.symm)
    rwa [← h]
  exact hβ.2.2.1 (hβ.1.antisymm hEβ)

end SymmetryModel

section Transport

private theorem mul_self_eq_one_of_isometry_rank_eq_one {K : Type} [Field K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate) {s : GL (Fin d) K}
    (hs : s ∈ matrixIsometries Q) (hr : ((s : Matrix (Fin d) (Fin d) K) - 1).rank = 1) :
    s * s = 1 := by
  set S : Matrix (Fin d) (Fin d) K := (s : Matrix (Fin d) (Fin d) K) with hSdef
  have hiso : ∀ x, Q (S *ᵥ x) = Q x := (mem_matrixIsometries_iff Q s).mp hs
  have hpol : ∀ x y, polar Q (S *ᵥ x) (S *ᵥ y) = polar Q x y := fun x y => by
    rw [polar, polar, ← Matrix.mulVec_add, hiso, hiso, hiso]
  rw [Matrix.rank] at hr
  obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp hr
  set w' : Fin d → K := (w : Fin d → K) with hw'def
  have hw'0 : w' ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hc : ∀ x, ∃ a : K, S *ᵥ x = x + a • w' := by
    intro x
    obtain ⟨a, ha⟩ := hw ⟨_, LinearMap.mem_range_self (S - 1).mulVecLin x⟩
    refine ⟨a, ?_⟩
    have h : a • w' = (S - 1) *ᵥ x := congrArg Subtype.val ha
    rw [h, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hww : polar Q w' w' = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  obtain ⟨μ, hμ⟩ := hc w'
  have hkey : ∀ y, μ * polar Q y w' = 0 := by
    intro y
    obtain ⟨a, ha⟩ := hc y
    have h := hpol y w'
    rw [ha, hμ] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hww,
      smul_eq_mul] at h
    linear_combination h
  have hSw : S *ᵥ w' = w' := by
    by_cases hμ0 : μ = 0
    · rw [hμ, hμ0, zero_smul, add_zero]
    · exfalso
      apply hw'0
      apply hQ.1
      intro y
      rw [polarBilin_apply_apply, polar_comm]
      exact (mul_eq_zero.mp (hkey y)).resolve_left hμ0
  have hSS : ∀ x, S *ᵥ (S *ᵥ x) = x := by
    intro x
    obtain ⟨a, ha⟩ := hc x
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, ha, hSw, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  exact hSS x

private theorem nondegenerate_reindex_of_nondegenerate {ι K : Type} [Field K] {d : ℕ}
    (e : ι ≃ Fin d) {Q₀ : QuadraticForm K (ι → K)} (hQ₀ : Q₀.polarBilin.Nondegenerate) :
    (reindexQuadraticForm e Q₀).polarBilin.Nondegenerate := by
  have hpol : ∀ y z, polar (reindexQuadraticForm e Q₀) y z =
      polar Q₀ ((reindexVectorEquiv (K := K) e).symm y)
        ((reindexVectorEquiv (K := K) e).symm z) := by
    intro y z
    simp only [polar, reindexQuadraticForm, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      map_add]
  have hsep : ∀ x : Fin d → K, (∀ y, polar (reindexQuadraticForm e Q₀) x y = 0) → x = 0 := by
    intro x hx
    have h0 : (reindexVectorEquiv (K := K) e).symm x = 0 := by
      apply hQ₀.1
      intro y
      have h := hx (reindexVectorEquiv e y)
      rwa [hpol, LinearEquiv.symm_apply_apply, ← polarBilin_apply_apply] at h
    exact ((reindexVectorEquiv (K := K) e).symm.map_eq_zero_iff).mp h0
  refine ⟨fun x hx => hsep x fun y => ?_, fun x hx => hsep x fun y => ?_⟩
  · rw [← polarBilin_apply_apply]
    exact hx y
  · rw [polar_comm, ← polarBilin_apply_apply]
    exact hx y

private theorem exists_symmetry_model_of_rankOne_model {G ι F : Type} [Group G] [Fintype ι]
    [DecidableEq ι] [Field F] [Finite F] [CharP F 2] (hZ : Subgroup.center G = ⊥) {s : G}
    {Q₀ : QuadraticForm F (ι → F)} (hQ₀ : Q₀.polarBilin.Nondegenerate) {d : ℕ}
    (hd : Fintype.card ι = d) {O : Subgroup (GL ι F)}
    (hO : O = (TauCeti.QuadraticMap.orthogonalGroup Q₀).comap (toLinEquiv ι F).toMonoidHom)
    (e : G ⧸ Subgroup.center G ≃* O)
    (hr : CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
      ((e (QuotientGroup.mk s) : O) : GL ι F)) :
    ∃ (Q : QuadraticForm F (Fin d → F)) (φ : G →* GL (Fin d) F) (v : Fin d → F),
      Q.polarBilin.Nondegenerate ∧ Function.Injective φ ∧ φ.range = matrixIsometries Q ∧
        Q v = 1 ∧ φ s = symmetryGL Q v ∧
        ∀ x : Fin d → F, Q x = 1 → ∃ t, IsConj s t ∧ φ t = symmetryGL Q x := by
  let σ : ι ≃ Fin d := Fintype.equivFinOfCardEq hd
  set Q := reindexQuadraticForm σ Q₀ with hQdef
  have hQ : Q.polarBilin.Nondegenerate := nondegenerate_reindex_of_nondegenerate σ hQ₀
  let φ : G →* GL (Fin d) F := (reindexMatrixEquiv σ).toMonoidHom.comp
    (O.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))))
  have hmk : Function.Injective (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hφ : Function.Injective φ :=
    (reindexMatrixEquiv σ).injective.comp (O.subtype_injective.comp (e.injective.comp hmk))
  have hmem : ∀ A : GL ι F, reindexMatrixEquiv σ A ∈ matrixIsometries Q ↔ A ∈ O := by
    intro A
    rw [hO]
    exact reindexMatrixEquiv_mem_isometries σ Q₀ A
  have hrange : φ.range = matrixIsometries Q := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      exact (hmem _).mpr (e _).2
    · intro hA
      obtain ⟨B, rfl⟩ := (reindexMatrixEquiv σ).surjective A
      obtain ⟨q, hq⟩ := e.surjective ⟨B, (hmem B).mp hA⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) q
      refine ⟨g, ?_⟩
      show reindexMatrixEquiv σ ((e (QuotientGroup.mk' (Subgroup.center G) g) : O) : GL ι F) = _
      rw [hq]
  have hφmem : ∀ g, φ g ∈ matrixIsometries Q := fun g => by
    rw [← hrange]
    exact ⟨g, rfl⟩
  have hrs : (((φ s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) - 1).rank = 1 := by
    have h : ((φ s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) - 1 =
        Matrix.reindex σ σ ((((e (QuotientGroup.mk s) : O) : GL ι F) : Matrix ι ι F) - 1) := by
      show Matrix.reindex σ σ ((((e (QuotientGroup.mk s) : O) : GL ι F) : Matrix ι ι F)) - 1 = _
      simp only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
        Matrix.submatrix_one_equiv]
    rw [h, Matrix.rank_reindex]
    exact hr
  have hs2 : φ s * φ s = 1 := mul_self_eq_one_of_isometry_rank_eq_one hQ (hφmem s) hrs
  have hs1 : φ s ≠ 1 := by
    intro h
    rw [h, Units.val_one, sub_self, Matrix.rank_zero] at hrs
    exact zero_ne_one hrs
  obtain ⟨w, hw, hsw⟩ := OmegaRadical.exists_symmetry_of_rank_le_one hQ (hφmem s) hs2 hs1 hrs.le
  exact ⟨Q, φ, w, hQ, hφ, hrange, hw, hsw, fun x hx => exists_isConj_symmetry hQ φ hrange hw hsw hx⟩

private theorem exists_ne_zero_ne_one_of_two_le {F : Type} [Field F] [Finite F] {f : ℕ}
    (hf : 2 ≤ f) (hcard : Nat.card F = 2 ^ f) : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  by_contra! h
  have hsurj : Function.Surjective (![0, 1] : Fin 2 → F) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [h x hx]⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

end Transport

theorem exists_symmetry_model_of_isOrthReflection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ}
    (h : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (Q : QuadraticForm K (Fin m → K))
      (ψ : X →* GL (Fin m) K) (v : Fin m → K),
      Fintype.card K = 2 ^ f ∧ Q.polarBilin.Nondegenerate ∧ Function.Injective ψ ∧
        ψ.range = matrixIsometries Q ∧ Q v = 1 ∧ ψ s = symmetryGL Q v ∧
        ∀ x : Fin m → K, Q x = 1 → ∃ t, IsConj s t ∧ ψ t = symmetryGL Q x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨k, hk, hmk, F, hF, hFin, hcard, e, hr⟩ |
    ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc, e, hr⟩
  · let _ : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [Nat.card_eq_fintype_card] at hcard)
    have hcoeq : ⇑(CFSG.LieType.Universal.Spin.quadPlus k F) =
        CFSG.PGLModel.plusQuadForm k (K := F) := by
      funext v
      rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
      rfl
    have hO : CFSG.PGLModel.orthogonalPlus k F =
        (TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus k F)).comap
          (toLinEquiv (Fin k ⊕ Fin k) F).toMonoidHom := by
      have h := closure_isometries_eq_comap (ι := Fin k ⊕ Fin k) (K := F) hcoeq
      simpa [CFSG.PGLModel.orthogonalPlus, CFSG.PGLModel.orthogonalGroup,
        CFSG.MatrixModel.isometryCore] using h
    obtain ⟨Q, φ, w, hQ, hφ, hrange, hw, hsw, hrefl⟩ := exists_symmetry_model_of_rankOne_model hZ
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus k F) (d := m)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hO e hr
    exact ⟨F, hF, inferInstance, this, Q, φ, w, by rw [← Nat.card_eq_fintype_card]; exact hcard,
      hQ, hφ, hrange, hw, hsw, hrefl⟩
  · let _ : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [Nat.card_eq_fintype_card] at hcard)
    have hcoeq : ⇑(CFSG.LieType.Universal.Spin.quadMinus (k + 1) F b c) =
        CFSG.PGLModel.minusQuadForm k (K := F) b c := by
      funext v
      rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
      rfl
    have hO : CFSG.PGLModel.orthogonalMinus k F b c =
        (TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (k + 1) F b c)).comap
          (toLinEquiv (Fin k ⊕ Fin k ⊕ Fin 2) F).toMonoidHom := by
      have h := closure_isometries_eq_comap (ι := Fin k ⊕ Fin k ⊕ Fin 2) (K := F) hcoeq
      simpa [CFSG.PGLModel.orthogonalMinus, CFSG.PGLModel.orthogonalGroup,
        CFSG.MatrixModel.isometryCore] using h
    obtain ⟨Q, φ, w, hQ, hφ, hrange, hw, hsw, hrefl⟩ := exists_symmetry_model_of_rankOne_model hZ
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n := k + 1)
        (K := F) hbc) (d := m) (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hO e hr
    exact ⟨F, hF, inferInstance, this, Q, φ, w, by rw [← Nat.card_eq_fintype_card]; exact hcard,
      hQ, hφ, hrange, hw, hsw, hrefl⟩

theorem four_le_of_isOrthReflection {X : Type} [Group X] {s : X} {m f : ℕ}
    (h : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) : 4 ≤ m := by
  rcases h with ⟨k, hk, hmk, -⟩ | ⟨k, hk, hmk, -⟩ <;> omega

private theorem subsingleton_and_ne_of_isOrthReflection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (hmf : 6 ≤ m ∨ 2 ≤ f)
    (h : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    (∀ β, IsBlock E β → β.Subsingleton) ∧ rootBlock E s ≠ E := by
  obtain ⟨K, _, _, _, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψs, -⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ h
  refine subsingleton_and_ne_of_symmetry_model hQ hm ?_ ψ hψ hrange hcls hs hv hψs
  rcases hmf with h6 | h2
  · exact Or.inl (by omega)
  · refine Or.inr (exists_ne_zero_ne_one_of_two_le h2 ?_)
    rw [Nat.card_eq_fintype_card]
    exact hcard

theorem subset_rootBlock_and_ne_of_isOrthReflection_of_four_le {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (hmf : 6 ≤ m ∨ 2 ≤ f)
    (h : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    (∀ β, IsBlock E β → s ∈ β → β ⊆ rootBlock E s) ∧ rootBlock E s ≠ E := by
  obtain ⟨hsub, hne⟩ := subsingleton_and_ne_of_isOrthReflection hcls hZ hs hm hmf h
  refine ⟨fun β hβ hsβ t htβ => ?_, hne⟩
  rw [hsub β hβ htβ hsβ]
  exact mem_rootBlock_self hs

theorem eq_singleton_of_isBlock_of_isOrthReflection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (hmf : 6 ≤ m ∨ 2 ≤ f)
    (h : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    ∀ β, IsBlock E β → s ∈ β → β = {s} := fun β hβ hsβ =>
  ((subsingleton_and_ne_of_isOrthReflection hcls hZ hs hm hmf h).1 β hβ).eq_singleton_of_mem hsβ

theorem rootBlock_eq_singleton_of_isOrthReflection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (hmf : 6 ≤ m ∨ 2 ≤ f)
    (h : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) : rootBlock E s = {s} := by
  obtain ⟨-, hne⟩ := subset_rootBlock_and_ne_of_isOrthReflection_of_four_le hcls hZ hs hm hmf h
  have hE : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    obtain ⟨d₀, rfl⟩ := hcls
    exact fun g x hx => (show IsConj d₀ x from hx).trans (isConj_iff.mpr ⟨g, rfl⟩)
  exact eq_singleton_of_isBlock_of_isOrthReflection hcls hZ hs hm hmf h (rootBlock E s)
    (isBlock_rootBlock hE hs hne) (mem_rootBlock_self hs)

theorem subsingleton_or_eq_of_isOrthReflection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (hmf : 6 ≤ m ∨ 2 ≤ f)
    (h : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    ∀ B : Set X, B ⊆ E → B.Nonempty →
      (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨ Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = E := by
  intro B hBE hBne hB
  by_cases hBeq : B = E
  · exact Or.inr hBeq
  refine Or.inl ((subsingleton_and_ne_of_isOrthReflection hcls hZ hs hm hmf h).1 B
    ⟨hBE, hBne, hBeq, fun g hg => ?_⟩)
  rcases hB g with himg | hdisj
  · exact absurd (Subgroup.mem_normalizer_iff_conj_image_eq.mpr himg) hg
  · exact hdisj.symm

end CFSG.OddTranspositions.PartFour

end
