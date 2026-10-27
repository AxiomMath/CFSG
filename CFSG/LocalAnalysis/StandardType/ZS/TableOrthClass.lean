module

public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.LocalAnalysis.StandardType.ZS.TableOrth
import CFSG.LocalAnalysis.StandardType.ZS.TableOrthClassBasis
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGen
import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.ClassicalGroups.Orthogonal.Restrict
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Sporadic.Ly.KeySpec
import CFSG.Sporadic.Schreier.J4SSylowBase
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem classRefl_ker_eq_orthogonal {Q : QuadraticForm (ZMod p) U} {z : U} :
    LinearMap.ker (QuadraticMap.polarBilin Q z) =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (Submodule.span (ZMod p) {z}) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hv y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, LinearMap.smul_apply, hv, smul_zero]
  · intro hv
    exact hv z (Submodule.mem_span_singleton_self z)

private theorem classRefl_ker_isCompl_span (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {z : U} (hz : Q z ≠ 0) :
    IsCompl (LinearMap.ker (QuadraticMap.polarBilin Q z))
        (Submodule.span (ZMod p) {z}) ∧
      Module.finrank (ZMod p) (LinearMap.ker (QuadraticMap.polarBilin Q z)) =
        Module.finrank (ZMod p) U - 1 := by
  have hzz : QuadraticMap.polarBilin Q z z ≠ 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul]
    exact mul_ne_zero (ZMod.prime_ne_zero p 2 hp) hz
  have hcompl := LinearMap.BilinForm.isCompl_span_singleton_orthogonal
    (B := QuadraticMap.polarBilin Q) hzz
  refine ⟨?_, ?_⟩
  · rw [classRefl_ker_eq_orthogonal]
    exact hcompl.symm
  · rw [classRefl_ker_eq_orthogonal,
      LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span (ZMod p) {z}),
      finrank_span_singleton (fun h => hz (by rw [h, QuadraticMap.map_zero]))]

private theorem exists_norm_eq_of_nondegenerate_two_le (hp : p ≠ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    {Q : QuadraticForm (ZMod p) W} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod p) W) (c : ZMod p) :
    ∃ w : W, Q w = c := by
  have htop : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (⊤ : Submodule (ZMod p) W) := CFSG.ClassicalGroups.Orthogonal.polarNondegOn_top hQ
  have hdim : 2 ≤ Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) W) := by
    simpa using h2
  obtain ⟨w, -, hw⟩ := htop.exists_map_eq (ZMod.prime_ne_zero p 2 hp) hdim c
  exact ⟨w, hw⟩

private theorem classRefl_polar_mem_of_mem_ker {Q : QuadraticForm (ZMod p) U} {z b s : U}
    (hs : QuadraticMap.polarBilin Q z s = 0)
    (hb : QuadraticMap.polarBilin Q z b = 0) :
    QuadraticMap.polarBilin Q z (CFSG.ClassicalGroups.Orthogonal.reflect Q b s) = 0 := by
  have hbz : QuadraticMap.polar Q b z = 0 := by
    rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact hb
  have hz : QuadraticMap.polar Q z s = 0 := by
    simpa [QuadraticMap.polarBilin_apply_apply] using hs
  have hO := CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q b
  have hp := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hO z s
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero hbz] at hp
  rw [QuadraticMap.polarBilin_apply_apply, hp, hz]

private theorem classRefl_norm_span_ne_bot (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {z : U} (hz : Q z ≠ 0) {c : ZMod p} (hc : c ≠ 0)
    (hVdim : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker (QuadraticMap.polarBilin Q z))) :
    Submodule.span (ZMod p) {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} ≠ ⊥ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hVeq := classRefl_ker_eq_orthogonal (Q := Q) (z := z)
  have hVpolar : (QuadraticMap.polarBilin (Q.comp
      (LinearMap.ker (QuadraticMap.polarBilin Q z)).subtype)).Nondegenerate := by
    rw [hVeq]
    exact owCr_restrict_nondegenerate Q hQ h2 z hz
  obtain ⟨s0, hs0⟩ := exists_norm_eq_of_nondegenerate_two_le hp hVpolar hVdim c
  intro hbot
  have hmem : (s0 : U) ∈ Submodule.span (ZMod p)
      {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} :=
    Submodule.subset_span ⟨s0.2, hs0⟩
  rw [hbot] at hmem
  have hzero : (s0 : U) = 0 := by simpa using hmem
  have hQ0 : Q (s0 : U) = 0 := by rw [hzero, QuadraticMap.map_zero]
  change Q (s0 : U) = c at hs0
  rw [hs0] at hQ0
  exact hc hQ0

private def classReflBfull (Q : QuadraticForm (ZMod p) U) (z : U) :
    Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure {t : U ≃ₗ[ZMod p] U | ∃ b ∈ LinearMap.ker (QuadraticMap.polarBilin Q z),
    Q b ≠ 0 ∧ t = CFSG.ClassicalGroups.Orthogonal.reflect Q b}

private def classReflInvariantSubgroup (W : Submodule (ZMod p) U) :
    Subgroup (U ≃ₗ[ZMod p] U) :=
  { carrier := {t | (∀ w ∈ W, t w ∈ W) ∧ (∀ w ∈ W, t⁻¹ w ∈ W)}
    one_mem' := by
      refine ⟨?_, ?_⟩ <;> intro w hw <;> simpa using hw
    mul_mem' := by
      rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      refine ⟨?_, ?_⟩
      · intro w hw
        exact ha1 (b w) (hb1 w hw)
      · intro w hw
        rw [mul_inv_rev]
        exact hb2 (a⁻¹ w) (ha2 w hw)
    inv_mem' := by
      rintro a ⟨ha1, ha2⟩
      refine ⟨?_, ?_⟩
      · intro w hw
        exact ha2 w hw
      · intro w hw
        simpa using ha1 w hw }

private theorem classRefl_span_norm_invariant
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} {W : Submodule (ZMod p) U}
    (hW : W = Submodule.span (ZMod p)
      {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c}) :
    ∀ t ∈ classReflBfull Q z, ∀ w ∈ W, t w ∈ W := by
  let S : Set U := {b | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c}
  let V : Submodule (ZMod p) U := LinearMap.ker (QuadraticMap.polarBilin Q z)
  have hBfull : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ classReflBfull Q z := by
    intro b hb hbQ
    exact Subgroup.subset_closure ⟨b, show b ∈ V from hb, hbQ, rfl⟩
  let P : Subgroup (U ≃ₗ[ZMod p] U) := classReflInvariantSubgroup W
  have hBfullP : classReflBfull Q z ≤ P := by
    rw [classReflBfull, Subgroup.closure_le]
    rintro t ⟨b, hbV, hbQ, rfl⟩
    have hmapS : ∀ s ∈ S, CFSG.ClassicalGroups.Orthogonal.reflect Q b s ∈ S := by
      intro s hs
      exact ⟨classRefl_polar_mem_of_mem_ker hs.1 hbV,
        by rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem
              (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q b) s]
           exact hs.2⟩
    have hmapW : Submodule.map
        (CFSG.ClassicalGroups.Orthogonal.reflect Q b).toLinearMap W ≤ W := by
      rw [hW, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.subset_span (hmapS s hs)
    refine ⟨?_, ?_⟩
    · intro w hw
      exact hmapW (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)
    · intro w hw
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_inv]
      exact hmapW (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)
  exact fun t ht => (hBfullP ht).1

private theorem classRefl_span_norm_eq_top (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {z : U} (hz : Q z ≠ 0) {c : ZMod p} (hc : c ≠ 0)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0)
    (hVdim : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker (QuadraticMap.polarBilin Q z))) :
    Submodule.span (ZMod p) {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} =
      LinearMap.ker (QuadraticMap.polarBilin Q z) := by
  let S : Set U := {b | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c}
  let W : Submodule (ZMod p) U := Submodule.span (ZMod p) S
  let V : Submodule (ZMod p) U := LinearMap.ker (QuadraticMap.polarBilin Q z)
  have hWV : W ≤ V := by
    rw [Submodule.span_le]
    rintro b ⟨hb, -⟩
    exact hb
  have hWne : W ≠ ⊥ := by
    simpa only [W, S] using classRefl_norm_span_ne_bot hp hQ hz hc hVdim
  have hBfull : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ classReflBfull Q z := by
    intro b hb hbQ
    exact Subgroup.subset_closure ⟨b, show b ∈ V from hb, hbQ, rfl⟩
  have hirr := irredOnSection_of_reflect_mem hp hQ hz hBfull hdim
  have hWinv : ∀ t ∈ classReflBfull Q z, ∀ w ∈ W, t w ∈ W :=
    classRefl_span_norm_invariant rfl
  have hEq : W = V := (hirr W bot_le hWV hWinv).resolve_left hWne
  simpa only [W, V, S] using hEq

private theorem classRefl_mem_orthogonal_of_not_mem [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U}
    (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    {s : U} (hsV : QuadraticMap.polarBilin Q z s = 0) (hsQ : Q s = c) (hsX : s ∉ X) :
    s ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  have hQs : Q s ≠ 0 := by rw [hsQ]; exact hc
  have hrx : CFSG.ClassicalGroups.Orthogonal.reflect Q s x ∈ X :=
    hXinv _ (hB s hsV hsQ) x hx
  have hcoefmem : (QuadraticMap.polar Q s x / Q s) • s ∈ X := by
    have h := X.sub_mem hx hrx
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQs x, sub_sub_cancel] at h
    exact h
  by_contra hne
  have hcoef : QuadraticMap.polar Q s x / Q s ≠ 0 := by
    intro h0
    apply hne
    have ht : QuadraticMap.polar Q s x = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact h
      · exact absurd h hQs
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using ht
  have hsX' : s ∈ X := by
    have := X.smul_mem ((QuadraticMap.polar Q s x / Q s)⁻¹) hcoefmem
    rw [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at this
    exact this
  exact hsX hsX'

private theorem classRefl_polar_eq_zero_on_ker {Q : QuadraticForm (ZMod p) U} {z : U}
    {c : ZMod p} {x : U}
    (hspan : Submodule.span (ZMod p)
        {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} =
      LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hx : ∀ s ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c},
      QuadraticMap.polar Q x s = 0)
    {v : U} (hv : v ∈ LinearMap.ker (QuadraticMap.polarBilin Q z)) :
    QuadraticMap.polar Q x v = 0 := by
  rw [← hspan] at hv
  refine Submodule.span_induction (p := fun w _ => QuadraticMap.polar Q x w = 0)
    ?_ ?_ ?_ ?_ hv
  · intro s hs
    exact hx s hs
  · simp
  · intro a b ha hb iha ihb
    rw [QuadraticMap.polar_add_right, iha, ihb, add_zero]
  · intro a b hb ihb
    rw [QuadraticMap.polar_smul_right, ihb, smul_zero]

private theorem classRefl_inv_submodule_norm_and_nondegenerate [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hspan : Submodule.span (ZMod p)
        {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} =
      LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hVnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.ker (QuadraticMap.polarBilin Q z))) (hXne : X ≠ ⊥) :
    (∃ s : U, s ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} ∧ s ∈ X) ∧
      CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q X := by
  have hSmem : ∀ s ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c},
      s ∉ X → s ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X :=
    fun s hs hsX => classRefl_mem_orthogonal_of_not_mem hc hB hXinv hs.1 hs.2 hsX
  constructor
  · obtain ⟨x, hxX, hxne⟩ := Submodule.ne_bot_iff X |>.mp hXne
    by_contra hnone
    push Not at hnone
    have hxzero : ∀ s ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c},
        QuadraticMap.polar Q x s = 0 := by
      intro s hs
      have hmem := hSmem s hs (hnone s hs)
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) x hxX
      simpa [QuadraticMap.polarBilin_apply_apply] using h
    exact hxne (hVnd x (hXV hxX)
      (fun y hy => classRefl_polar_eq_zero_on_ker hspan hxzero hy))
  · intro y hyX hyorth
    have hyzero : ∀ s ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c},
        QuadraticMap.polar Q y s = 0 := by
      intro s hs
      by_cases hsX : s ∈ X
      · exact hyorth s hsX
      · have hmem := hSmem s hs hsX
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) y hyX
        simpa [QuadraticMap.polarBilin_apply_apply] using h
    exact hVnd y (hXV hyX)
      (fun w hw => classRefl_polar_eq_zero_on_ker hspan hyzero hw)

private theorem classRefl_inv_compl_sup [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X Y : Submodule (ZMod p) U} (hYdef : Y =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓
        LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hspan : Submodule.span (ZMod p)
        {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} =
      LinearMap.ker (QuadraticMap.polarBilin Q z)) :
    LinearMap.ker (QuadraticMap.polarBilin Q z) = X ⊔ Y := by
  have hYV : Y ≤ LinearMap.ker (QuadraticMap.polarBilin Q z) := by
    rw [hYdef]
    exact inf_le_right
  have hSsub : ∀ s ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c},
      s ∈ X ∨ s ∈ Y := by
    intro s hs
    by_cases hsX : s ∈ X
    · exact Or.inl hsX
    · refine Or.inr ?_
      rw [hYdef]
      exact ⟨classRefl_mem_orthogonal_of_not_mem hc hB hXinv hs.1 hs.2 hsX, hs.1⟩
  apply le_antisymm
  · rw [← hspan, Submodule.span_le]
    intro s hs
    rcases hSsub s hs with h | h
    · exact Submodule.mem_sup_left h
    · exact Submodule.mem_sup_right h
  · exact sup_le hXV hYV

private theorem classRefl_inv_compl_nondegenerate [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U}
    {X Y : Submodule (ZMod p) U} (hYdef : Y =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓
        LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hsup : LinearMap.ker (QuadraticMap.polarBilin Q z) = X ⊔ Y)
    (hVnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.ker (QuadraticMap.polarBilin Q z))) :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q Y := by
  intro y hy hyorth
  rw [hYdef] at hy
  by_contra hyne
  obtain ⟨v, hvV, hpol⟩ := hVnd.exists_polar_ne_zero hy.2 hyne
  obtain ⟨a, haX, b, hbY, hab⟩ := Submodule.mem_sup.mp (hsup ▸ hvV)
  have hya : QuadraticMap.polar Q y a = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy.1) a haX
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h
  have hyb : QuadraticMap.polar Q y b ≠ 0 := by
    have hsum : QuadraticMap.polar Q y v =
        QuadraticMap.polar Q y a + QuadraticMap.polar Q y b := by
      rw [← hab, QuadraticMap.polar_add_right]
    rw [hsum, hya, zero_add] at hpol
    exact hpol
  exact hyb (hyorth b hbY)

private theorem classRefl_inv_compl_data [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X Y : Submodule (ZMod p) U} (hYdef : Y =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓
        LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hspan : Submodule.span (ZMod p)
        {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} =
      LinearMap.ker (QuadraticMap.polarBilin Q z))
    (hVnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.ker (QuadraticMap.polarBilin Q z))) :
    LinearMap.ker (QuadraticMap.polarBilin Q z) = X ⊔ Y ∧
      CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q Y :=
  ⟨classRefl_inv_compl_sup hc hB hYdef hXinv hXV hspan,
    classRefl_inv_compl_nondegenerate hYdef
      (classRefl_inv_compl_sup hc hB hYdef hXinv hXV hspan) hVnd⟩

private structure ClassReflIrredBase (Q : QuadraticForm (ZMod p) U) (z : U) (c : ZMod p) where
  V : Submodule (ZMod p) U
  hVeq : V = LinearMap.ker (QuadraticMap.polarBilin Q z)
  hVdim : 2 ≤ Module.finrank (ZMod p) V
  hVnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q V
  hspan : Submodule.span (ZMod p)
    {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} = V

private noncomputable def classRefl_irred_base (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : U} (hz : Q z ≠ 0)
    {c : ZMod p} (hc : c ≠ 0)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0)
    (hVdim : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker (QuadraticMap.polarBilin Q z))) :
    ClassReflIrredBase Q z c := by
  let V : Submodule (ZMod p) U := LinearMap.ker (QuadraticMap.polarBilin Q z)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hVeq := classRefl_ker_eq_orthogonal (Q := Q) (z := z)
  have hVpolar : (QuadraticMap.polarBilin (Q.comp V.subtype)).Nondegenerate := by
    change (QuadraticMap.polarBilin (Q.comp
      (LinearMap.ker (QuadraticMap.polarBilin Q z)).subtype)).Nondegenerate
    rw [hVeq]
    exact owCr_restrict_nondegenerate Q hQ h2 z hz
  have hVnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q V := by
    intro y hy hyorth
    have hy' : (⟨y, hy⟩ : V) = 0 := hVpolar.1 ⟨y, hy⟩ (fun w => by
      have h := hyorth w.1 w.2
      simpa [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
        QuadraticMap.polarBilin_apply_apply] using h)
    exact Subtype.ext_iff.mp hy'
  have hspan := classRefl_span_norm_eq_top hp hQ hz hc hdim hVdim
  exact ⟨V, rfl, hVdim, hVnd, hspan⟩

private structure ClassReflIrredX (Q : QuadraticForm (ZMod p) U) (z : U) (c : ZMod p)
    (B : Subgroup (U ≃ₗ[ZMod p] U)) (X : Submodule (ZMod p) U) where
  base : ClassReflIrredBase Q z c
  x : U
  hxX : x ∈ X
  hxQ : Q x = c
  hxne : x ≠ 0
  hXnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q X

private noncomputable def classRefl_irred_X (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {z : U} (hz : Q z ≠ 0) {c : ZMod p} (hc : c ≠ 0)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0)
    (hVdim : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker (QuadraticMap.polarBilin Q z)))
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z)) (hX0 : X ≠ ⊥) :
    ClassReflIrredX Q z c B X := by
  let base := classRefl_irred_base hp hQ hz hc hdim hVdim
  have hdata := classRefl_inv_submodule_norm_and_nondegenerate hc hB hXinv hXV base.hspan
    base.hVnd hX0
  let x := Classical.choose hdata.1
  have hxS : x ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} :=
    (Classical.choose_spec hdata.1).1
  have hxX : x ∈ X := (Classical.choose_spec hdata.1).2
  have hxQ : Q x = c := hxS.2
  have hxne : x ≠ 0 := by
    intro hx0
    rw [hx0, QuadraticMap.map_zero] at hxQ
    exact hc hxQ.symm
  exact ⟨base, x, hxX, hxQ, hxne, hdata.2⟩

private structure ClassReflIrredY (Q : QuadraticForm (ZMod p) U) (z : U) (c : ZMod p)
    (B : Subgroup (U ≃ₗ[ZMod p] U)) (X : Submodule (ZMod p) U) where
  xdata : ClassReflIrredX Q z c B X
  Y : Submodule (ZMod p) U
  hYdef : Y = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ xdata.base.V
  hsup : xdata.base.V = X ⊔ Y
  hYnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q Y
  y : U
  hyY : y ∈ Y
  hyQ : Q y = c
  hyne : y ≠ 0
  hpolxy : QuadraticMap.polar Q xdata.x y = 0
  hXinf : X ⊓ Y = ⊥
  hdimsum : Module.finrank (ZMod p) xdata.base.V =
    Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y

private structure ClassReflIrredYW (Q : QuadraticForm (ZMod p) U) (z : U) (c : ZMod p)
    (B : Subgroup (U ≃ₗ[ZMod p] U)) (X : Submodule (ZMod p) U)
    (xdata : ClassReflIrredX Q z c B X) (Y : Submodule (ZMod p) U) where
  y : U
  hyY : y ∈ Y
  hyQ : Q y = c
  hyne : y ≠ 0
  hpolxy : QuadraticMap.polar Q xdata.x y = 0
  hXinf : X ⊓ Y = ⊥
  hdimsum : Module.finrank (ZMod p) xdata.base.V =
    Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y

private noncomputable def classRefl_irred_YW [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (xdata : ClassReflIrredX Q z c B X) (hXproper : X ≠ xdata.base.V)
    {Y : Submodule (ZMod p) U} (hYdef : Y = LinearMap.BilinForm.orthogonal
      (QuadraticMap.polarBilin Q) X ⊓ xdata.base.V) (hsup : xdata.base.V = X ⊔ Y) :
    ClassReflIrredYW Q z c B X xdata Y := by
  have hy_exists : ∃ s : U, s ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} ∧
      s ∉ X := by
    by_contra h
    push Not at h
    apply hXproper
    apply le_antisymm
    · rw [xdata.base.hVeq]; exact hXV
    · rw [← xdata.base.hspan]
      exact Submodule.span_le.mpr fun s hs => h s hs
  let y := Classical.choose hy_exists
  have hyS : y ∈ {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} :=
    (Classical.choose_spec hy_exists).1
  have hyX : y ∉ X := (Classical.choose_spec hy_exists).2
  have hyQ : Q y = c := hyS.2
  have hyY : y ∈ Y := by
    rw [hYdef]
    exact ⟨classRefl_mem_orthogonal_of_not_mem hc hB hXinv hyS.1 hyS.2 hyX,
      by rw [xdata.base.hVeq]; exact hyS.1⟩
  have hyY' : y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓
      xdata.base.V := by rw [← hYdef]; exact hyY
  have hpolxy : QuadraticMap.polar Q xdata.x y = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hyY'.1) xdata.x xdata.hxX
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h
  have hXinf : X ⊓ Y = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro u ⟨huX, huY⟩
    apply xdata.hXnd u huX
    intro v hvX
    have huY' : u ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓
        xdata.base.V := by rw [← hYdef]; exact huY
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp huY'.1) v hvX
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h
  have hdimsum : Module.finrank (ZMod p) xdata.base.V =
      Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
    rw [← hsup, hXinf, finrank_bot, add_zero] at h
    simpa using h
  have hyne : y ≠ 0 := fun hy0 => hc (by rw [hy0, QuadraticMap.map_zero] at hyQ; exact hyQ.symm)
  exact ⟨y, hyY, hyQ, hyne, hpolxy, hXinf, hdimsum⟩

private noncomputable def classRefl_irred_Y [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (xdata : ClassReflIrredX Q z c B X) (hXproper : X ≠ xdata.base.V) :
    ClassReflIrredY Q z c B X := by
  set Y : Submodule (ZMod p) U :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ xdata.base.V with hYdef
  have hYdef' : Y = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓
      LinearMap.ker (QuadraticMap.polarBilin Q z) := by rw [hYdef, xdata.base.hVeq]
  have hspan' : Submodule.span (ZMod p)
      {b : U | QuadraticMap.polarBilin Q z b = 0 ∧ Q b = c} =
      LinearMap.ker (QuadraticMap.polarBilin Q z) := by
    simpa [xdata.base.hVeq] using xdata.base.hspan
  have hVnd' : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.ker (QuadraticMap.polarBilin Q z)) := by
    simpa [xdata.base.hVeq] using xdata.base.hVnd
  obtain ⟨hsupKer, hYnd⟩ :=
    classRefl_inv_compl_data hc hB (Y := Y) hYdef' hXinv hXV hspan' hVnd'
  have hsup : xdata.base.V = X ⊔ Y := by rw [xdata.base.hVeq]; exact hsupKer
  let yw := classRefl_irred_YW hc hB hXinv hXV xdata hXproper hYdef hsup
  exact ⟨xdata, Y, hYdef, hsup, hYnd, yw.y, yw.hyY, yw.hyQ, yw.hyne, yw.hpolxy,
    yw.hXinf, yw.hdimsum⟩

private structure ClassReflIrredData (Q : QuadraticForm (ZMod p) U) (z : U) (c : ZMod p)
    (B : Subgroup (U ≃ₗ[ZMod p] U)) (X : Submodule (ZMod p) U) where
  xdata : ClassReflIrredX Q z c B X
  Y : Submodule (ZMod p) U
  hYdef : Y = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ xdata.base.V
  hsup : xdata.base.V = X ⊔ Y
  hYnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q Y
  y : U
  hyY : y ∈ Y
  hyQ : Q y = c
  hyne : y ≠ 0
  hpolxy : QuadraticMap.polar Q xdata.x y = 0
  hXinf : X ⊓ Y = ⊥
  hdimsum : Module.finrank (ZMod p) xdata.base.V =
    Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y

private noncomputable def classRefl_irred_data [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (xdata : ClassReflIrredX Q z c B X) (hXproper : X ≠ xdata.base.V) :
    ClassReflIrredData Q z c B X := by
  let yd := classRefl_irred_Y hc hB hXinv hXV xdata hXproper
  exact ⟨yd.xdata, yd.Y, yd.hYdef, yd.hsup, yd.hYnd, yd.y, yd.hyY, yd.hyQ, yd.hyne,
    yd.hpolxy, yd.hXinf, yd.hdimsum⟩

private theorem classRefl_smul_add_not_mem_left {X Y : Submodule (ZMod p) U}
    (hXinf : X ⊓ Y = ⊥) {u v : U} (huX : u ∈ X) (hvY : v ∈ Y) (hvne : v ≠ 0)
    {α β : ZMod p} (hβ : β ≠ 0) {w : U} (hw : w = α • u + β • v) : w ∉ X := by
  intro hwX
  have hvX : v ∈ X := by
    have hmem' : β • v ∈ X := by
      have : β • v = w - α • u := by rw [hw]; abel
      rw [this]; exact X.sub_mem hwX (X.smul_mem _ huX)
    have hmem := X.smul_mem β⁻¹ hmem'
    rwa [smul_smul, inv_mul_cancel₀ hβ, one_smul] at hmem
  have : v ∈ X ⊓ Y := ⟨hvX, hvY⟩
  rw [hXinf] at this
  exact hvne (by simpa using this)

private theorem classRefl_smul_add_not_mem_orth {Q : QuadraticForm (ZMod p) U}
    {X Y V : Submodule (ZMod p) U}
    (hXinf : X ⊓ Y = ⊥) (hYdef : Y = LinearMap.BilinForm.orthogonal
      (QuadraticMap.polarBilin Q) X ⊓ V) {u v : U} (huX : u ∈ X) (hvY : v ∈ Y)
    (huV : u ∈ V) (hune : u ≠ 0) {α β : ZMod p} (hα : α ≠ 0) {w : U}
    (hw : w = α • u + β • v) :
    w ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
  intro hwO
  have huO : u ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
    have hmem' : α • u ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
      have : α • u = w - β • v := by rw [hw]; abel
      rw [this]
      exact (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X).sub_mem hwO
        ((LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X).smul_mem _
          (by rw [hYdef] at hvY; exact hvY.1))
    have hmem := (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X).smul_mem
      α⁻¹ hmem'
    rwa [smul_smul, inv_mul_cancel₀ hα, one_smul] at hmem
  have huY : u ∈ Y := by rw [hYdef]; exact ⟨huO, huV⟩
  have : u ∈ X ⊓ Y := ⟨huX, huY⟩
  rw [hXinf] at this
  exact hune (by simpa using this)

private theorem classRefl_irred_pne5 (hp : p ≠ 2) (hp3 : p ≠ 3)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (D : ClassReflIrredData Q z c B X) (hp5 : p ≠ 5) : False := by
  rcases D with ⟨⟨base, x, hxX, hxQ, hxne, hXnd⟩, Y, hYdef, hsup, hYnd, y, hyY, hyQ,
    hyne, hpolxy, hXinf, hdimsum⟩
  let V := base.V
  have hxV : x ∈ V := by change x ∈ base.V; rw [base.hVeq]; exact hXV hxX
  have hYV : Y ≤ V := by change Y ≤ base.V; rw [hYdef]; exact inf_le_right
  have hyY' : y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V := by
    change y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ base.V
    rw [← hYdef]; exact hyY
  have h5 : (5 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 5 hp5
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h22 : (2 : ZMod p) * 2 ≠ 0 :=
      mul_ne_zero (ZMod.prime_ne_zero p 2 hp) (ZMod.prime_ne_zero p 2 hp)
    simpa [show (4 : ZMod p) = 2 * 2 by norm_num] using h22
  have hα : (3 * (5 : ZMod p)⁻¹) ≠ 0 := mul_ne_zero h3 (inv_ne_zero h5)
  have hβ : (4 * (5 : ZMod p)⁻¹) ≠ 0 := mul_ne_zero h4 (inv_ne_zero h5)
  let w : U := (3 * (5 : ZMod p)⁻¹) • x + (4 * (5 : ZMod p)⁻¹) • y
  have hwQ : Q w = c := by
    dsimp [w]
    rw [QuadraticMap.map_add Q, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_left, hxQ, hyQ, hpolxy]
    field_simp [h5]
    ring
  have hwV : w ∈ V := V.add_mem (V.smul_mem _ hxV) (V.smul_mem _ (hYV hyY))
  have hwK : w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z) := by
    rw [← base.hVeq]; exact hwV
  have hwX : w ∉ X := by
    apply classRefl_smul_add_not_mem_left hXinf hxX hyY hyne hβ
    dsimp [w]
  have hwOrth : w ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
    apply classRefl_smul_add_not_mem_orth hXinf hYdef hxX hyY hxV hxne hα
    dsimp [w]
  exact hwOrth (classRefl_mem_orthogonal_of_not_mem hc hB hXinv hwK hwQ hwX)

private theorem classRefl_irred_p5_left (hp : p ≠ 2) (hp3 : p ≠ 3)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (D : ClassReflIrredData Q z c B X) (hX2 : 2 ≤ Module.finrank (ZMod p) X) : False := by
  rcases D with ⟨⟨base, x, hxX, hxQ, hxne, hXnd⟩, Y, hYdef, hsup, hYnd, y, hyY, hyQ,
    hyne, hpolxy, hXinf, hdimsum⟩
  let V := base.V
  have hxV : x ∈ V := by change x ∈ base.V; rw [base.hVeq]; exact hXV hxX
  have hYV : Y ≤ V := by change Y ≤ base.V; rw [hYdef]; exact inf_le_right
  have hyY' : y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V := by
    change y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ base.V
    rw [← hYdef]; exact hyY
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  have hXpolar : (QuadraticMap.polarBilin (Q.comp X.subtype)).Nondegenerate :=
    CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hXnd
  obtain ⟨x', hx'Q⟩ := exists_norm_eq_of_nondegenerate_two_le hp hXpolar hX2 (3 * c)
  have hx'X : (x' : U) ∈ X := x'.2
  change Q (x' : U) = 3 * c at hx'Q
  have hx'y : QuadraticMap.polar Q (x' : U) y = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hyY'.1) x' hx'X
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h
  let w : U := (2 : ZMod p)⁻¹ • ((x' : U) + y)
  have hwQ : Q w = c := by
    dsimp [w]
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, QuadraticMap.map_add Q,
      hx'Q, hyQ, hx'y]
    field_simp [h2]
    ring
  have hx'V : (x' : U) ∈ V := by
    change (x' : U) ∈ base.V
    rw [base.hVeq]; exact hXV hx'X
  have hwV : w ∈ V := V.smul_mem _ (V.add_mem hx'V (hYV hyY))
  have hwK : w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z) := by
    rw [← base.hVeq]; exact hwV
  have hwX : w ∉ X := by
    apply classRefl_smul_add_not_mem_left hXinf hx'X hyY hyne (inv_ne_zero h2)
    dsimp [w]; rw [smul_add]
  have hwOrth : w ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
    apply classRefl_smul_add_not_mem_orth hXinf hYdef hx'X hyY hx'V
      (fun h => (mul_ne_zero h3 hc) (by
        rw [h, QuadraticMap.map_zero] at hx'Q; exact hx'Q.symm)) (inv_ne_zero h2)
    dsimp [w]; rw [smul_add]
  exact hwOrth (classRefl_mem_orthogonal_of_not_mem hc hB hXinv hwK hwQ hwX)

private theorem classRefl_irred_p5_right (hp : p ≠ 2) (hp3 : p ≠ 3)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    {z : U} {c : ZMod p} (hc : c ≠ 0)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ t ∈ B, ∀ x ∈ X, t x ∈ X)
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z))
    (D : ClassReflIrredData Q z c B X) (hY2 : 2 ≤ Module.finrank (ZMod p) D.Y) : False := by
  rcases D with ⟨⟨base, x, hxX, hxQ, hxne, hXnd⟩, Y, hYdef, hsup, hYnd, y, hyY, hyQ,
    hyne, hpolxy, hXinf, hdimsum⟩
  let V := base.V
  have hxV : x ∈ V := by change x ∈ base.V; rw [base.hVeq]; exact hXV hxX
  have hYV : Y ≤ V := by change Y ≤ base.V; rw [hYdef]; exact inf_le_right
  have hyY' : y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ V := by
    change y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓ base.V
    rw [← hYdef]; exact hyY
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  have hYpolar : (QuadraticMap.polarBilin (Q.comp Y.subtype)).Nondegenerate :=
    CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hYnd
  obtain ⟨y', hy'Q⟩ := exists_norm_eq_of_nondegenerate_two_le hp hYpolar hY2 (3 * c)
  have hy'Y : (y' : U) ∈ Y := y'.2
  change Q (y' : U) = 3 * c at hy'Q
  have hy'Y' : (y' : U) ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X ⊓
      base.V := by rw [← hYdef]; exact hy'Y
  have hxy' : QuadraticMap.polar Q x (y' : U) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy'Y'.1) x hxX
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h
  let w : U := (2 : ZMod p)⁻¹ • (x + (y' : U))
  have hwQ : Q w = c := by
    dsimp [w]
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, QuadraticMap.map_add Q,
      hxQ, hy'Q, hxy']
    field_simp [h2]
    ring
  have hwV : w ∈ V := V.smul_mem _ (V.add_mem hxV (hYV hy'Y))
  have hwK : w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z) := by
    rw [← base.hVeq]; exact hwV
  have hwX : w ∉ X := by
    apply classRefl_smul_add_not_mem_left hXinf hxX hy'Y
      (fun h => (mul_ne_zero h3 hc) (by
        rw [h, QuadraticMap.map_zero] at hy'Q; exact hy'Q.symm)) (inv_ne_zero h2)
    dsimp [w]; rw [smul_add]
  have hwOrth : w ∉ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) X := by
    apply classRefl_smul_add_not_mem_orth hXinf hYdef hxX hy'Y hxV hxne (inv_ne_zero h2)
    dsimp [w]; rw [smul_add]
  exact hwOrth (classRefl_mem_orthogonal_of_not_mem hc hB hXinv hwK hwQ hwX)

private theorem classRefl_aniso_final {X Y : Submodule (ZMod p) U} (hXinf : X ⊓ Y = ⊥)
    {x y : U} (hxX : x ∈ X) (hxne : x ≠ 0) (hyY : y ∈ Y)
    (hzero : x + (2 : ZMod p) • y = 0) : False := by
  have hxY : x ∈ Y := by
    have heq : x = -((2 : ZMod p) • y) := by rw [eq_neg_iff_add_eq_zero]; exact hzero
    rw [heq]; exact Y.neg_mem (Y.smul_mem _ hyY)
  have : x ∈ X ⊓ Y := ⟨hxX, hxY⟩
  rw [hXinf] at this
  exact hxne (by simpa using this)

private theorem classRefl_irred_aniso (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : U} {c : ZMod p}
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    {X : Submodule (ZMod p) U}
    (hXV : X ≤ LinearMap.ker (QuadraticMap.polarBilin Q z)) (hz : Q z ≠ 0)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0)
    (D : ClassReflIrredData Q z c B X) (hp5eq : p = 5)
    (hX1 : Module.finrank (ZMod p) X = 1) (hY1 : Module.finrank (ZMod p) D.Y = 1) : False := by
  rcases D with ⟨⟨base, x, hxX, hxQ, hxne, hXnd⟩, Y, hYdef, hsup, hYnd, y, hyY, hyQ,
    hyne, hpolxy, hXinf, hdimsum⟩
  let V := base.V
  have hxV : x ∈ V := by change x ∈ base.V; rw [base.hVeq]; exact hXV hxX
  have hYV : Y ≤ V := by change Y ≤ base.V; rw [hYdef]; exact inf_le_right
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hdimsum' : Module.finrank (ZMod p) V =
      Module.finrank (ZMod p) X + Module.finrank (ZMod p) Y := hdimsum
  have hV2 : Module.finrank (ZMod p) V = 2 := by
    rw [hdimsum', hX1, hY1]
  have hV2' : Module.finrank (ZMod p) (LinearMap.ker (QuadraticMap.polarBilin Q z)) = 2 := by
    rw [← base.hVeq]; exact hV2
  have hU3 : Module.finrank (ZMod p) U = 3 := by
    have := (classRefl_ker_isCompl_span (Q := Q) (z := z) hp hQ hz).2
    omega
  have hVanz : ∀ v : U, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0 := by
    rcases hdim with h4 | hanz <;> [omega; exact hanz]
  have hsumQ : Q (x + (2 : ZMod p) • y) = 0 := by
    rw [QuadraticMap.map_add Q, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      QuadraticMap.polar_smul_right, hxQ, hyQ, hpolxy]
    have h5zero : (5 : ZMod p) = 0 := by simpa [hp5eq] using ZMod.natCast_self p
    linear_combination c * h5zero
  have hsumV : x + (2 : ZMod p) • y ∈ V := V.add_mem hxV (V.smul_mem _ (hYV hyY))
  have hzero := hVanz _ (by
    show x + (2 : ZMod p) • y ∈ LinearMap.ker (QuadraticMap.polarBilin Q z)
    rw [← base.hVeq]; exact hsumV) hsumQ
  exact classRefl_aniso_final hXinf hxX hxne hyY hzero

theorem irredOnSection_of_classReflect_mem (hp : p ≠ 2) (hp3 : p ≠ 3) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {z : U}
    (hz : Q z ≠ 0) {c : ZMod p} (hc : c ≠ 0) {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ B)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0) :
    IrredOnSection B ⊥ (LinearMap.ker (QuadraticMap.polarBilin Q z)) := by
  intro X hbot hXV hXinv
  by_cases hX0 : X = ⊥
  · exact Or.inl hX0
  by_cases hXVeq : X = LinearMap.ker (QuadraticMap.polarBilin Q z)
  · exact Or.inr hXVeq
  apply Or.inr
  by_contra hXVne
  by_cases hVsmall : Module.finrank (ZMod p)
      (LinearMap.ker (QuadraticMap.polarBilin Q z)) ≤ 1
  · have hXpos : 0 < Module.finrank (ZMod p) X := by
      rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) X) with h0 | hpos
      · exact absurd (Submodule.finrank_eq_zero.mp h0) hX0
      · exact hpos
    exact hXVne (Submodule.eq_of_le_of_finrank_eq hXV (by
      have hle := Submodule.finrank_mono hXV
      omega))
  have hVdim : 2 ≤ Module.finrank (ZMod p)
      (LinearMap.ker (QuadraticMap.polarBilin Q z)) := by omega
  let xdata := classRefl_irred_X hp hQ hz hc hdim hVdim hB hXinv hXV hX0
  have hXproper : X ≠ xdata.base.V := fun h => hXVne (by rw [h]; exact xdata.base.hVeq)
  let D := classRefl_irred_data hc hB hXinv hXV xdata hXproper
  by_cases hp5 : p ≠ 5
  · exact classRefl_irred_pne5 hp hp3 hc hB hXinv hXV D hp5
  · have hp5eq : p = 5 := by omega
    by_cases hX2 : 2 ≤ Module.finrank (ZMod p) X
    · exact classRefl_irred_p5_left hp hp3 hc hB hXinv hXV D hX2
    · have hXpos : 0 < Module.finrank (ZMod p) X := by
        rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) X) with h0 | hpos
        · exact absurd (Submodule.finrank_eq_zero.mp h0) hX0
        · exact hpos
      have hX1 : Module.finrank (ZMod p) X = 1 := by omega
      by_cases hY2 : 2 ≤ Module.finrank (ZMod p) D.Y
      · exact classRefl_irred_p5_right hp hp3 hc hB hXinv hXV D hY2
      · have hYle : Module.finrank (ZMod p) D.Y ≤ 1 := by omega
        have hY1 : Module.finrank (ZMod p) D.Y = 1 := by
          have hdimsumK := D.hdimsum
          rw [D.xdata.base.hVeq] at hdimsumK
          omega
        exact classRefl_irred_aniso hp hQ hXV hz hdim D hp5eq hX1 hY1

private theorem throughReflClass_fixRefl_inv [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hJ : J = Subgroup.closure (ClassRefl p Q c)) {z : U} :
    ∀ h ∈ fixReflSubgroup p J z, ∀ w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z),
      h w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z) := by
  intro h hh w hw
  have hhJ : h ∈ J := fixReflSubgroup_le J z hh
  have hisom : IsIsom p Q h :=
    isIsom_of_mem_closure_classRefl (by rwa [hJ] at hhJ)
  have hzfix : h z = z := fixReflSubgroup_apply_eq hh
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hisom
  have hpol := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hO z w
  rw [hzfix] at hpol
  rw [LinearMap.mem_ker] at hw ⊢
  rw [QuadraticMap.polarBilin_apply_apply] at hw ⊢
  rwa [hpol]

private theorem throughReflClass_fixRefl_hne (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} {J : Subgroup (U ≃ₗ[ZMod p] U)}
    {z a : U} (ha : Q a ≠ 0) (hQa : Q a = c)
    (hza : QuadraticMap.polarBilin Q z a = 0)
    (hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ fixReflSubgroup p J z) :
    ∃ h ∈ fixReflSubgroup p J z,
      ∃ w ∈ LinearMap.ker (QuadraticMap.polarBilin Q z), h w ≠ w := by
  have hra : CFSG.ClassicalGroups.Orthogonal.reflect Q a a = -a := by
    let _ : Invertible (Q a) := invertibleOfNonzero ha
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
      TauCeti.QuadraticMap.reflection_apply_self]
  refine ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a, hB a hza hQa, a, hza, ?_⟩
  intro heq
  have haeq : a = -a := by rw [← hra, heq]
  have h2a : (2 : ZMod p) • a = 0 := by
    rw [two_smul]
    nth_rewrite 1 [haeq]
    exact neg_add_cancel a
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hane : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  exact hane ((smul_eq_zero.mp h2a).resolve_left h2)

private theorem throughReflClass_splitSupport (hp : p ≠ 2) (hp3 : p ≠ 3)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : J = Subgroup.closure (ClassRefl p Q c))
    {z a : U} (hz : Q z ≠ 0) (ha : Q a ≠ 0) (hQa : Q a = c)
    (hza : QuadraticMap.polarBilin Q z a = 0)
    (hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0) :
    SplitSupport (fixReflSubgroup p J z) (Module.finrank (ZMod p) U - 1) := by
  have hB : ∀ b, QuadraticMap.polarBilin Q z b = 0 → Q b = c →
      CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ fixReflSubgroup p J z := by
    intro b hzb hbQ
    have hclass : CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ ClassRefl p Q c :=
      (mem_classRefl_iff hp hQ hc _).mpr ⟨b, hbQ, rfl⟩
    have hbJ : CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ J := by
      rw [hJ]
      exact Subgroup.subset_closure hclass
    have hfix : CFSG.ClassicalGroups.Orthogonal.reflect Q b z = z := by
      apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
      exact hzb
    exact mem_fixReflSubgroup hbJ hclass.1 hfix
  have hirr := irredOnSection_of_classReflect_mem hp hp3 hQ hz hc hB hdim
  obtain ⟨hcompl, hWfin⟩ := classRefl_ker_isCompl_span hp hQ hz
  have hfix : ∀ h ∈ fixReflSubgroup p J z, ∀ w ∈ Submodule.span (ZMod p) {z},
      h w = w := by
    intro h hh w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨d, rfl⟩ := hw
    rw [map_smul, fixReflSubgroup_apply_eq hh]
  have hinv := throughReflClass_fixRefl_inv (c := c) hJ (z := z)
  have hne := throughReflClass_fixRefl_hne hp ha hQa hza hB
  have hsp := splitSupport_of_isCompl hcompl hfix hinv hirr hne
  rw [hWfin] at hsp
  exact hsp

theorem throughRefl_orthClass (hp : p ≠ 2) (hp3 : p ≠ 3) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : J = Subgroup.closure (ClassRefl p Q c)) :
    ThroughRefl p (Module.finrank (ZMod p) U - 1) J := by
  intro r hr hrrefl
  have hrClass : r ∈ ClassRefl p Q c :=
    mem_classRefl_of_isRefl_mem_closure hp hQ hc (by rwa [hJ] at hr) hrrefl
  obtain ⟨a, hQa, hr_eq⟩ := (mem_classRefl_iff hp hQ hc r).mp hrClass
  have ha : Q a ≠ 0 := by rw [hQa]; exact hc
  obtain ⟨z, hz, hza, hzaniso⟩ := exists_hyperplane_of_root hp hQ h3 ha
  have hbz : QuadraticMap.polar Q a z = 0 := by
    rw [QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]
    exact hza
  have hdim : 4 ≤ Module.finrank (ZMod p) U ∨
      ∀ v, QuadraticMap.polarBilin Q z v = 0 → Q v = 0 → v = 0 := by
    by_cases hm : Module.finrank (ZMod p) U = 3
    · exact Or.inr (hzaniso hm)
    · exact Or.inl (by omega)
  have hsp := throughReflClass_splitSupport hp hp3 hQ hc hJ hz ha hQa hza hdim
  refine ⟨fixReflSubgroup p J z, fixReflSubgroup_le J z, ?_,
    reflGen_fixReflSubgroup J z, hsp⟩
  rw [hr_eq] at hr hrrefl ⊢
  exact mem_fixReflSubgroup hr hrrefl (by
    apply CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
    exact hbz)

theorem exists_gen_closure_classRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : J = Subgroup.closure (ClassRefl p Q c))
    (hT : TableHyp p J) (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∉ J) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ J ∧ IsRefl p x) ∧ J = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) := by
  subst hJ
  obtain ⟨s, hs, hsR, hcl⟩ := exists_classRefl_gen hp h3 hQ hc hneg hT.dLarge
  exact ⟨s, hs, fun x hx => ⟨Subgroup.subset_closure (hsR x hx), (hsR x hx).1⟩, hcl⟩

theorem negOrGen_orthClass (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : J = Subgroup.closure (ClassRefl p Q c))
    (hT : TableHyp p J) : NegOrGen p (Module.finrank (ZMod p) U) J := by
  by_cases hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J
  · exact Or.inl hneg
  · exact Or.inr (exists_gen_closure_classRefl hp h3 hQ hc hJ hT hneg)

theorem tableConclusions_orthClass (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hJ : J = Subgroup.closure (ClassRefl p Q c))
    (hT : TableHyp p J) : TableConclusions p (Module.finrank (ZMod p) U) J := by
  by_cases hp3 : p = 3
  · exfalso
    obtain ⟨x, hxJ, y, hyJ, hxr, hyr, hxy⟩ := hT.dLarge
    have hx : x ∈ Subgroup.closure (ClassRefl p Q c) := by rwa [hJ] at hxJ
    have hy : y ∈ Subgroup.closure (ClassRefl p Q c) := by rwa [hJ] at hyJ
    have hle := orderOf_mul_le_three_of_classRefl_three hp3 hQ hc hx hy hxr hyr
    omega
  · refine ⟨negOrGen_orthClass hp h3 hQ hc hJ hT, ?_⟩
    exact ⟨coprimeWitness_orthClass hp h3 hQ hc hJ,
      throughRefl_orthClass hp hp3 h3 hQ hc hJ⟩

end CFSG.StandardType.ZS
