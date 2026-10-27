module

public import CFSG.Quasithin.Background.JonesParshallG2H1
public import CFSG.Quasithin.Background.JonesParshallSp4Two
public import CFSG.Quasithin.Background.JonesParshallG2TwoInputs
public import Certificates.Certificate17028
public import CFSG.Quasithin.Background.JonesParshallG2TwoCertificate8952Inputs
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43


public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open
open scoped commutatorElement

section Mat

variable {F : Type} [Field F]

theorem zornCoord_apply (x : quasithinZorn F) :
    zornCoord x = ![x.1, x.2.1 0, x.2.1 1, x.2.1 2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2, x.2.2.2] :=
  rfl

theorem zornCoord_map (g : quasithinZorn F →ₗ[F] quasithinZorn F) (x : quasithinZorn F) :
    zornCoord (g x) = zmat g *ᵥ zornCoord x := by
  rw [zmat, LinearMap.toMatrix'_mulVec]
  simp

theorem zmat_eq_of_mulVec {g : quasithinZorn F →ₗ[F] quasithinZorn F}
    {M : Matrix (Fin 8) (Fin 8) F} (h : ∀ x, zornCoord (g x) = M *ᵥ zornCoord x) : zmat g = M := by
  rw [zmat, ← LinearMap.toMatrix'_toLin' M]
  congr 1
  refine LinearMap.ext fun c => ?_
  simp [h]

theorem zmat_injective {g h : quasithinZorn F →ₗ[F] quasithinZorn F} (hgh : zmat g = zmat h) :
    g = h :=
  LinearMap.ext fun x => zornCoord.injective (by rw [zornCoord_map, zornCoord_map, hgh])

theorem cmat_injective {g h : ↥(cayleyGroup F)} (hgh : cmat g = cmat h) : g = h :=
  Subtype.ext (LinearEquiv.toLinearMap_injective (zmat_injective hgh))

theorem zornCoord_cg (g : ↥(cayleyGroup F)) (x : quasithinZorn F) :
    zornCoord (cgE g x) = cmat g *ᵥ zornCoord x :=
  zornCoord_map _ x

theorem cmat_wordEval {k : ℕ} (gens : Fin k → ↥(cayleyGroup F))
    (mats : Fin k → Matrix (Fin 8) (Fin 8) F) (h : ∀ i, cmat (gens i) = mats i)
    (w : List (Fin k)) : cmat (wordEval gens w) = wordEvalM mats w := by
  induction w with
  | nil => exact map_one cmat
  | cons i w ih =>
    change cmat (gens i * wordEval gens w) = mats i * wordEvalM mats w
    rw [map_mul, h, ih]

theorem inv_eq_of_cmat {g : ↥(cayleyGroup F)} {M : Matrix (Fin 8) (Fin 8) F} (hg : cmat g = M)
    (hM : M * M = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (cmat_injective (by rw [map_mul, map_one, hg, hM]))

theorem cmat_g2A (A : SL3 F) :
    cmat (g2A A) = zornBlockMat (A : Matrix (Fin 3) (Fin 3) F)
      (adjugate (A : Matrix (Fin 3) (Fin 3) F))ᵀ := by
  refine zmat_eq_of_mulVec fun x => ?_
  funext i
  fin_cases i <;>
    simp [zornCoord_apply, zornBlockMat, g2A_apply, gAFun, mulVec, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_eight]

@[expose] def embQ : Ix3 → Fin 8 := Sum.elim ![1, 2, 3] ![4, 5, 6]

theorem g2Act_eq_mulVec [CharP F 2] (g : ↥(cayleyGroup F)) (w : Ix3 → F) :
    g2Act g w = (cmat g).submatrix embQ embQ *ᵥ w := by
  have h := zornCoord_cg g (zI w)
  have hz : ∀ i, zP (cgE g (zI w)) i = zornCoord (cgE g (zI w)) (embQ i) := by
    intro i
    rcases i with i | i <;> fin_cases i <;> rfl
  funext i
  rw [g2Act_apply, hz, h]
  rcases i with i | i <;> fin_cases i <;>
    simp [mulVec, dotProduct, Fin.sum_univ_eight, Fintype.sum_sum_type, Fin.sum_univ_three, embQ,
      zornCoord_apply, zI, zmk] <;> ring

theorem ellG_eq_of_cmat [CharP F 2] {g : ↥(cayleyGroup F)} {M : Matrix (Fin 8) (Fin 8) F}
    (hM : cmat g⁻¹ = M) (w : Ix3 → F) : ellG g w = (M *ᵥ zornCoord (zI w)) 0 := by
  rw [ellG, ← hM, ← zornCoord_cg]
  rfl

end Mat

theorem forall_vec3 {α : Type*} {P : α → Prop} {a b c : α} (ha : P a) (hb : P b) (hc : P c) :
    ∀ i, P (![a, b, c] i) := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

theorem coe_wordEval_sub {G : Type*} [Group G] {H : Subgroup G} {k : ℕ} (gens : Fin k → ↥H)
    (w : List (Fin k)) : ((wordEval gens w : ↥H) : G) = wordEval (fun i => (gens i : G)) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change ((gens i : G) * ((wordEval gens w : ↥H) : G)) = _
    rw [ih]
    rfl

section Two

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

theorem cmat_g2X_e0 :
    cmat (g2X (![1, 0, 0] : Fin 3 → ZMod 2)) = matX2 :=
  Certificates.certificate17028.1

theorem cmat_g2Y_e1 :
    cmat (g2Y (![0, 1, 0] : Fin 3 → ZMod 2)) = matY2 :=
  Certificates.certificate17028.2

theorem adj_transvection_two {i j : Fin 3} (hij : i ≠ j) :
    (adjugate (Matrix.transvection i j (1 : ZMod 2)))ᵀ = Matrix.transvection j i 1 :=
  Certificates.certificate8953 hij

@[expose] def g2t (i j : Fin 3) (hij : i ≠ j) : ↥(cayleyGroup (ZMod 2)) :=
  g2A (transvection hij 1)

theorem cmat_g2t {i j : Fin 3} (hij : i ≠ j) :
    cmat (g2t i j hij) =
      zornBlockMat (Matrix.transvection i j 1) (Matrix.transvection j i 1) := by
  rw [g2t, cmat_g2A]
  exact congrArg _ (adj_transvection_two hij)

@[expose] def gens8 : Fin 8 → ↥(cayleyGroup (ZMod 2)) :=
  ![g2X ![1, 0, 0], g2Y ![0, 1, 0], g2t 0 1 (by decide), g2t 0 2 (by decide),
    g2t 1 0 (by decide), g2t 1 2 (by decide), g2t 2 0 (by decide), g2t 2 1 (by decide)]

theorem cmat_gens8 (i : Fin 8) :
    cmat (gens8 i) = mats8 i := by
  fin_cases i
  · exact cmat_g2X_e0
  · exact cmat_g2Y_e1
  all_goals exact cmat_g2t _

@[expose] def g2a : ↥(cayleyGroup (ZMod 2)) := wordEval gens8 [6, 1, 5, 1, 6, 5]

@[expose] def g2b : ↥(cayleyGroup (ZMod 2)) := wordEval gens8 [7, 5, 3, 7, 3, 5]

theorem cmat_g2a :
    cmat g2a = matA2 := by
  rw [g2a, cmat_wordEval gens8 mats8 cmat_gens8]
  exact Certificates.certificate8952.1

theorem cmat_g2b :
    cmat g2b = matB2 := by
  rw [g2b, cmat_wordEval gens8 mats8 cmat_gens8]
  exact Certificates.certificate8952.2.1

theorem gens8_inv
    (i : Fin 8) :
    (gens8 i)⁻¹ = gens8 i :=
  inv_eq_of_cmat (cmat_gens8 i) (Certificates.certificate8952.2.2.1 i)

theorem g2a_eq :
    g2a = ⁅gens8 6 * gens8 1, gens8 5⁆ := by
  rw [commutatorElement_def, _root_.mul_inv_rev, gens8_inv, gens8_inv, gens8_inv]
  simp only [g2a, wordEval, mul_one, mul_assoc]

theorem g2b_eq :
    g2b = ⁅gens8 7, gens8 5 * gens8 3⁆ := by
  rw [commutatorElement_def, _root_.mul_inv_rev, gens8_inv, gens8_inv, gens8_inv]
  simp only [g2b, wordEval, mul_one, mul_assoc]

theorem coe_mem_commutator (g h : ↥(cayleyGroup (ZMod 2))) :
    ((⁅g, h⁆ : ↥(cayleyGroup (ZMod 2))) : Amb) ∈
      ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ := by
  rw [show ((⁅g, h⁆ : ↥(cayleyGroup (ZMod 2))) : Amb) = ⁅(g : Amb), (h : Amb)⁆ from
    map_commutatorElement (cayleyGroup (ZMod 2)).subtype g h]
  exact Subgroup.commutator_mem_commutator g.2 h.2

theorem g2a_mem
    : (g2a : Amb) ∈ ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ := by
  rw [g2a_eq]
  exact coe_mem_commutator _ _

theorem g2b_mem
    : (g2b : Amb) ∈ ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ := by
  rw [g2b_eq]
  exact coe_mem_commutator _ _

theorem cmat_ab
    (i : Fin 2) : cmat (![g2a, g2b] i) = ![matA2, matB2] i := by
  fin_cases i
  · exact cmat_g2a
  · exact cmat_g2b

theorem cmat_tab
    (i : Fin 3) : cmat (![gens8 0, g2a, g2b] i) = ![matX2, matA2, matB2] i := by
  fin_cases i
  · exact cmat_gens8 0
  · exact cmat_g2a
  · exact cmat_g2b

@[expose] def subG2 : Subgroup Amb := Subgroup.closure {(g2a : Amb), (g2b : Amb)}

theorem conj_g2a :
    gens8 0 * g2a * gens8 0 =
      wordEval ![g2a, g2b] [1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0] := by
  apply cmat_injective
  rw [map_mul, map_mul, cmat_gens8, cmat_g2a, cmat_wordEval _ _ cmat_ab]
  exact Certificates.certificate8952.2.2.2.1

theorem conj_g2b :
    gens8 0 * g2b * gens8 0 = g2b := by
  apply cmat_injective
  rw [map_mul, map_mul, cmat_gens8, cmat_g2b]
  exact Certificates.certificate8952.2.2.2.2.1

theorem gens8_eq
    (i : Fin 8) : gens8 i = wordEval ![gens8 0, g2a, g2b] (wordsG i) := by
  apply cmat_injective
  rw [cmat_gens8, cmat_wordEval _ _ cmat_tab]
  exact Certificates.certificate8952.2.2.2.2.2 i

theorem ab_mem_subG2 : ∀ i, (![(g2a : Amb), (g2b : Amb)] : Fin 2 → Amb) i ∈ subG2 := by
  intro i
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem coe_wordEval_ab (w : List (Fin 2)) :
    ((wordEval ![g2a, g2b] w : ↥(cayleyGroup (ZMod 2))) : Amb) =
      wordEval (![(g2a : Amb), (g2b : Amb)] : Fin 2 → Amb) w := by
  rw [coe_wordEval_sub]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem gens8_zero_sq :
    gens8 0 * gens8 0 = 1 := by
  have h := gens8_inv 0
  rwa [inv_eq_iff_mul_eq_one] at h

theorem tau_sq :
    (gens8 0 : Amb) * gens8 0 = 1 := by
  rw [← Subgroup.coe_mul, gens8_zero_sq]
  rfl

theorem tau_inv :
    ((gens8 0 : Amb))⁻¹ = gens8 0 :=
  inv_eq_of_mul_eq_one_right tau_sq

theorem tau_conj_mem
    : ∀ k ∈ subG2, (gens8 0 : Amb) * k * (gens8 0 : Amb)⁻¹ ∈ subG2 := by
  intro k hk
  rw [tau_inv]
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, conj_g2a, coe_wordEval_ab]
      exact wordEval_mem ab_mem_subG2 _
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, conj_g2b]
      exact ab_mem_subG2 1
  | one =>
    rw [mul_one, tau_sq]
    exact subG2.one_mem
  | mul x y _ _ hx hy =>
    have e : (gens8 0 : Amb) * (x * y) * gens8 0 =
        ((gens8 0 : Amb) * x * gens8 0) * ((gens8 0 : Amb) * y * gens8 0) := by
      calc (gens8 0 : Amb) * (x * y) * gens8 0 =
          (gens8 0 : Amb) * x * 1 * y * gens8 0 := by group
        _ = (gens8 0 : Amb) * x * ((gens8 0 : Amb) * gens8 0) * y * gens8 0 := by rw [tau_sq]
        _ = _ := by group
    rw [e]
    exact subG2.mul_mem hx hy
  | inv x _ hx =>
    have e : (gens8 0 : Amb) * x⁻¹ * gens8 0 = ((gens8 0 : Amb) * x * gens8 0)⁻¹ := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, tau_inv]
      group
    rw [e]
    exact subG2.inv_mem hx

theorem tau_conj_mem'
    : ∀ k ∈ subG2, (gens8 0 : Amb)⁻¹ * k * (gens8 0 : Amb) ∈ subG2 := by
  intro k hk
  have h := tau_conj_mem k hk
  rw [tau_inv] at h ⊢
  exact h

theorem g2A_mem_of_closure {C : Subgroup Amb}
    (h : ∀ i, (gens8 i : Amb) ∈ C) (A : SL3 (ZMod 2)) : (g2A A : Amb) ∈ C := by
  let P : Subgroup (SL3 (ZMod 2)) := C.comap ((cayleyGroup (ZMod 2)).subtype.comp g2A)
  have hP : Subgroup.closure (P : Set (SL3 (ZMod 2))) = ⊤ := by
    refine closure_eq_top_of_transvection fun t => ?_
    rw [Subgroup.closure_eq]
    obtain ⟨i, j, hij, c⟩ := t
    have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hc c with rfl | rfl
    · have e : (TransvectionStruct.mk i j hij (0 : ZMod 2)).toSpecialLinearGroup = 1 :=
        Subtype.ext (Matrix.transvection_zero i j)
      rw [e]
      exact P.one_mem
    · change (g2A (transvection hij (1 : ZMod 2)) : Amb) ∈ C
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact h 2 | exact h 3 | exact h 4 | exact h 5 | exact h 6 | exact h 7
  rw [Subgroup.closure_eq] at hP
  have hA : A ∈ P := by
    rw [hP]
    exact Subgroup.mem_top A
  exact hA

theorem gensG2_two_subset :
    gensG2 (ZMod 2) ⊆ Subgroup.closure (insert (gens8 0 : Amb) (subG2 : Set Amb)) := by
  set C := Subgroup.closure (insert (gens8 0 : Amb) (subG2 : Set Amb))
  have h0 : (gens8 0 : Amb) ∈ C := Subgroup.subset_closure (Set.mem_insert _ _)
  have ha : (g2a : Amb) ∈ C := Subgroup.subset_closure
    (Set.mem_insert_of_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)))
  have hb : (g2b : Amb) ∈ C := Subgroup.subset_closure
    (Set.mem_insert_of_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  have hg := forall_vec3 (P := fun g : ↥(cayleyGroup (ZMod 2)) => (g : Amb) ∈ C) h0 ha hb
  have hgens : ∀ i, (gens8 i : Amb) ∈ C := fun i => by
    rw [gens8_eq i, coe_wordEval_sub]
    exact wordEval_mem hg _
  have hA := g2A_mem_of_closure hgens
  rintro g (⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨A, rfl⟩)
  · by_cases hb : b = 0
    · subst hb
      rw [g2X_zero]
      exact C.one_mem
    obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit b hb)
    have e : g2X b = g2A B * g2X ![1, 0, 0] * (g2A B)⁻¹ := by
      rw [g2A_mul_g2X, mul_inv_cancel_right]
      congr 1
      exact hB.symm
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact C.mul_mem (C.mul_mem (hA B) (hgens 0)) (C.inv_mem (hA B))
  · by_cases hb : b = 0
    · subst hb
      rw [g2Y_zero]
      exact C.one_mem
    obtain ⟨B, e⟩ := g2Y_conj_e1 hb
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact C.mul_mem (C.mul_mem (hA B) (hgens 1)) (C.inv_mem (hA B))
  · exact hA A

theorem g2Two_commutator_eq
    : ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ = subG2 := by
  refine le_antisymm (commutator_le_of_normalizes tau_conj_mem tau_conj_mem' ?_) ?_
  · exact (cayleyGroup_eq_closure (F := ZMod 2)).le.trans
      ((Subgroup.closure_le _).mpr gensG2_two_subset)
  · rw [subG2, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact g2a_mem
    · exact g2b_mem

end Two

end CFSG.Quasithin.JonesParshall
