module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniBlock
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameMap
public import CFSG.Blueprint.Catalog
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3Inputs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Cop
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125W
import CFSG.GH74.KGroups.L3EpsUni
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartTwo.Sec15.Sylow155R1 CFSG.RankThree.PartTwo.Sec15.Sylow155R3

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

local notation "𝟙" => ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem statedModel (h5 : 5 ≤ p ^ f) :
    CFSG.Open.StatedClassicalModel (primeFormP h 𝟙) .PSU 3 p f := by
  obtain ⟨e₀⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 3) (K := F))
  refine ⟨⟨h.prime, h.one_le, by norm_num, ?_⟩, F, inferInstance, h.finite, h.card_eq_sq,
    ⟨e₀.trans (unitaryPSUEquiv h (by norm_num))⟩⟩
  intro he
  have heq := congrArg Prod.snd he
  omega

theorem exists_model {X : Type} [Group X] {p : ℕ} (hX : CFSG.Blueprint.LieModel X .PSU 3 p 1) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData p 1 F), Nonempty (X ≃* primeFormP h
      ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨⟨hp, hf, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let h : UnitaryFieldData p 1 F := ⟨hp, hf, by simpa using hF⟩
  obtain ⟨e₁⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 3) (K := F))
  exact ⟨F, inferInstance, h, ⟨e₀.trans ((unitaryPSUEquiv h (by norm_num)).symm.trans e₁.symm)⟩⟩

theorem isCyclic_cent (hq : Odd (p ^ f)) :
    IsCyclic ↥(I h ⊓ centralizer ({e h, r h} : Set (MulAut (primeFormP h 𝟙)))) := by
  have : Finite F := h.finite
  let H : Subgroup (MulAut (primeFormP h 𝟙)) :=
    ((psiUni h).range).map (MulAut.conj : primeFormP h 𝟙 →* MulAut (primeFormP h 𝟙))
  have hcyc : IsCyclic ↥H := by
    have hpsi : IsCyclic ↥(psiUni h).range :=
      isCyclic_of_surjective (psiUni h).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    let Φ : ↥(psiUni h).range →* ↥H :=
      ((MulAut.conj : primeFormP h 𝟙 →* MulAut (primeFormP h 𝟙)).comp
        (psiUni h).range.subtype).codRestrict H (fun x => ⟨x, x.2, rfl⟩)
    exact isCyclic_of_surjective Φ (by
      rintro ⟨x, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩)
  have hle : I h ⊓ centralizer ({e h, r h} : Set (MulAut (primeFormP h 𝟙))) ≤ H := by
    rintro _ hx
    obtain ⟨⟨x, rfl⟩, hx⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have he : MulAut.conj (g : primeFormP h 𝟙) * e h = e h * MulAut.conj (g : primeFormP h 𝟙) :=
      ((Subgroup.mem_centralizer_iff.1 hx) _ (Set.mem_insert _ _)).symm
    have hr : MulAut.conj (g : primeFormP h 𝟙) * r h = r h * MulAut.conj (g : primeFormP h 𝟙) :=
      ((Subgroup.mem_centralizer_iff.1 hx) _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))).symm
    let gU : primeFormUnitary h 𝟙 := ⟨g, g.2.1⟩
    let eU' : primeFormUnitary h 𝟙 := ⟨eU h, (eU h).2.1⟩
    let rU' : primeFormUnitary h 𝟙 := ⟨rU h, (rU h).2.1⟩
    have htrE : (((eU' : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace ≠ 0 := by
      change (eMat : Matrix (Fin 3) (Fin 3) F).trace ≠ 0
      simp [eMat, Matrix.trace_fin_three]
    have htrR : (((rU' : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace ≠ 0 := by
      change (rMat : Matrix (Fin 3) (Fin 3) F).trace ≠ 0
      simp [rMat, Matrix.trace_fin_three]
    have hgE : gU * eU' = eU' * gU := L3Uni.commute_of_conjHom h htrE (by
      simpa only [gU, eU', primeFormConjHom_eq_conj, e] using he)
    have hgR : gU * rU' = rU' * gU := L3Uni.commute_of_conjHom h htrR (by
      simpa only [gU, rU', primeFormConjHom_eq_conj, r] using hr)
    let M := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    have hME : M * eMat = eMat * M := congrArg (fun A : primeFormUnitary h 𝟙 =>
      ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hgE
    have hMR : M * rMat = rMat * M := congrArg (fun A : primeFormUnitary h 𝟙 =>
      ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hgR
    have hdiag := commute_diag (Uni.two_ne_zero_of_odd_pow h hq) hME hMR
    let a := M 0 0
    let b := M 2 2
    have hdet : a * a * b = 1 := by
      have he := g.2.2
      change M.det = 1 at he
      rw [hdiag, Matrix.det_diagonal] at he
      simpa [Fin.prod_univ_three, a, b] using he
    have ha0 : a ≠ 0 := by intro he; rw [he] at hdet; simp at hdet
    have hn : h.bar a * a = 1 := by
      have he := g.2.1
      have he' : (M.map h.bar)ᵀ * M = 1 := by simpa only [Units.val_one, Matrix.mul_one] using he
      rw [hdiag] at he'
      have he00 := congrFun (congrFun he' 0) 0
      simpa [a, Matrix.mul_apply, Fin.sum_univ_three] using he00
    have hb : b = (a * a)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      exact hdet
    let u : normOneUnits (p := p) (f := f) (K := F) :=
      ⟨Units.mk0 a ha0, by
        rw [mem_normOneUnits]
        apply Units.ext
        simpa [h.bar_apply, pow_succ', mul_comm] using hn⟩
    have hg : g = diagUHom h u := by
      apply Subtype.ext
      apply Units.ext
      change M = _
      rw [coe_diagUHom, hdiag]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u, a, b, hb]
    refine ⟨(g : primeFormP h 𝟙), ?_, rfl⟩
    exact ⟨u, congrArg (fun g : gramSU h 𝟙 => (g : primeFormP h 𝟙)) hg.symm⟩
  have := hcyc
  exact Subgroup.isCyclic_of_le hle

theorem comm_of_coprime_six (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {y : MulAut (primeFormP h 𝟙)} (hy : Nat.Coprime (orderOf y) 6)
    {R : Subgroup (MulAut (primeFormP h 𝟙))} (hR : IsPGroup 2 R)
    (hn : y ∈ normalizer (R : Set (MulAut (primeFormP h 𝟙)))) :
    ∀ x ∈ R, y * x = x * y := by
  have := h.finite
  have hX : CFSG.Open.StatedClassicalModel (primeFormP h 𝟙) .PSL 3 p f ∨
      CFSG.Open.StatedClassicalModel (primeFormP h 𝟙) .PSU 3 p f := Or.inr (statedModel h h5)
  exact res3L125_centralizes_of_normalizes (center_primeFormP_three_eq_bot h h5)
    (res1OddL3_odd_commutator_outer hX) (res1OddL3_abelian_index_le_two hp2 hX)
    (res1OddL3_card_elemAbelian_le_four hp2 hX)
    (fun _ _ _ hR _ hA hidx hE _ hβ => res3L125_eq_one_of_coprime_six hR hA hidx hE hβ)
    hR hn hy

theorem exists_frame_of_model {X : Type} [Group X] [Finite X] {p : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F p] {Y : Type} [Group Y] (e₀ : X ≃* Y)
    (Fr : L3Frame (MulAut Y) p F) (hI : Fr.I = (MulAut.conj : Y →* MulAut Y).range)
    {K : Subgroup Y} (hK : ⁅K, K⁆ = K) (hc : Nat.card K = p * (p ^ 2 - 1))
    (hKb : Fr.Kb = K.map (MulAut.conj : Y →* MulAut Y)) :
    ∃ Fr' : L3Frame (MulAut X) p F,
      Fr'.I = (MulAut.conj : X →* MulAut X).range ∧
        ∃ K' : Subgroup X, ⁅K', K'⁆ = K' ∧ Nat.card K' = p * (p ^ 2 - 1) ∧
          Fr'.Kb = K'.map (MulAut.conj : X →* MulAut X) := by
  let Ψ := MulAut.congr e₀
  let K' := K.map e₀.symm.toMonoidHom
  refine ⟨L3Frame.comap Ψ Fr, ?_, K', ?_, ?_, ?_⟩
  · rw [L3Frame.comap_I, hI]
    ext a
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨e₀.symm y, Ψ.injective ?_⟩
      rw [congr_conj, e₀.apply_symm_apply]
      exact hy
    · rintro ⟨x, rfl⟩
      exact ⟨e₀ x, (congr_conj e₀ x).symm⟩
  · rw [← Subgroup.map_commutator, hK]
  · rw [Subgroup.card_map_of_injective e₀.symm.injective, hc]
  · rw [L3Frame.comap_Kb, hKb]
    ext a
    constructor
    · rintro ⟨y, hy, hya⟩
      refine ⟨e₀.symm y, ⟨y, hy, rfl⟩, Ψ.injective ?_⟩
      rw [congr_conj, e₀.apply_symm_apply]
      exact hya
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      change MulAut.conj y = MulAut.congr e₀ (MulAut.conj (e₀.symm y))
      rw [congr_conj, e₀.apply_symm_apply]

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni
