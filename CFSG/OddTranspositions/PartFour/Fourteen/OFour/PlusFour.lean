module

public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.PlusModel
public import CFSG.OddTranspositions.PartThree.Eleven.PlusWreath
import CFSG.GroupTheory.ConjClassGeneration
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot
public import CFSG.OddTranspositions.PartThree.Eleven.PlusModel

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open CFSG.Timmesfeld.Bridge.Asc72
open Matrix

section Generic

variable {F : Type} [Field F]

abbrev plusO (F : Type) [Field F] : Type := ↥(CFSG.PGLModel.orthogonalPlus 2 F)

@[expose] noncomputable def plusA : Subgroup (plusO F) :=
  (j1 (F := F)).range.subgroupOf (CFSG.PGLModel.orthogonalPlus 2 F)

@[expose] noncomputable def plusB : Subgroup (plusO F) :=
  (j2 (F := F)).range.subgroupOf (CFSG.PGLModel.orthogonalPlus 2 F)

noncomputable def j1O (a : Matrix.SpecialLinearGroup (Fin 2) F) : plusO F :=
  ⟨j1 a, j1_mem_orthGroup a⟩

noncomputable def j2O (b : Matrix.SpecialLinearGroup (Fin 2) F) : plusO F :=
  ⟨j2 b, j2_mem_orthGroup b⟩

theorem mem_plusA_iff {g : plusO F} :
    g ∈ plusA ↔ ∃ a : Matrix.SpecialLinearGroup (Fin 2) F,
      j1 a = (g : GL (Fin 2 ⊕ Fin 2) F) := by
  rw [plusA, Subgroup.mem_subgroupOf, MonoidHom.mem_range]

theorem mem_plusB_iff {g : plusO F} :
    g ∈ plusB ↔ ∃ b : Matrix.SpecialLinearGroup (Fin 2) F,
      j2 b = (g : GL (Fin 2 ⊕ Fin 2) F) := by
  rw [plusB, Subgroup.mem_subgroupOf, MonoidHom.mem_range]

theorem j1_mem_plusA (a : Matrix.SpecialLinearGroup (Fin 2) F) :
    j1O a ∈ plusA (F := F) :=
  mem_plusA_iff.2 ⟨a, rfl⟩

theorem j2_mem_plusB (b : Matrix.SpecialLinearGroup (Fin 2) F) :
    j2O b ∈ plusB (F := F) :=
  mem_plusB_iff.2 ⟨b, rfl⟩

theorem plusA_inf_plusB [CharP F 2] :
    plusA (F := F) ⊓ plusB (F := F) = (⊥ : Subgroup (plusO F)) := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨a, ha⟩ := mem_plusA_iff.1 hx.1
  obtain ⟨b, hb⟩ := mem_plusB_iff.1 hx.2
  obtain ⟨rfl, rfl⟩ := eq_one_of_j1_eq_j2 (ha.trans hb.symm)
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by simpa using ha.symm)

theorem plusA_sup_plusB : plusA (F := F) ⊔ plusB (F := F) = plusN (F := F) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨a, ha⟩ := mem_plusA_iff.1 hx
      exact mem_plusN_iff.2 ⟨a, 1, by rw [map_one, mul_one]; exact ha⟩
    · intro x hx
      obtain ⟨b, hb⟩ := mem_plusB_iff.1 hx
      exact mem_plusN_iff.2 ⟨1, b, by rw [map_one, one_mul]; exact hb⟩
  · intro x hx
    obtain ⟨a, b, hab⟩ := mem_plusN_iff.1 hx
    have hx' : x = j1O a * j2O b :=
      Subtype.ext (by rw [Subgroup.coe_mul]; exact hab.symm)
    rw [hx']
    exact Subgroup.mul_mem_sup (j1_mem_plusA a) (j2_mem_plusB b)

theorem plusA_commute_plusB {a b : plusO F} (ha : a ∈ plusA (F := F))
    (hb : b ∈ plusB (F := F)) :
    Commute a b := by
  obtain ⟨x, hx⟩ := mem_plusA_iff.1 ha
  obtain ⟨y, hy⟩ := mem_plusB_iff.1 hb
  rw [show a = j1O x from Subtype.ext hx.symm,
    show b = j2O y from Subtype.ext hy.symm]
  exact Subtype.ext (j1_j2_commute x y).eq

theorem index_sup_plusA_plusB [Finite F] [CharP F 2] :
    (plusA (F := F) ⊔ plusB (F := F)).index = 2 := by
  rw [plusA_sup_plusB]
  exact index_plusN (F := F)

theorem not_mem_plusN_of_closure_isConj [Finite F] [CharP F 2] {r : plusO F}
    (hgen : Subgroup.closure {y : plusO F | IsConj r y} = ⊤) : r ∉ plusN (F := F) := by
  intro hr
  have htop : plusN (F := F) = ⊤ :=
    CFSG.GroupTheory.eq_top_of_mem_of_closure_isConj_eq_top
      (plusN_normal (F := F)) hr hgen
  have hidx := index_plusN (F := F)
  rw [htop, Subgroup.index_top] at hidx
  omega

theorem j1_range_le_orthogonalPlus :
    (j1 (F := F)).range ≤ CFSG.PGLModel.orthogonalPlus 2 F := by
  rintro _ ⟨a, rfl⟩
  exact j1_mem_orthGroup a

noncomputable def plusAEquivPSL2 [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    CFSG.Theory.Comparator.PSL2Model 2 ≃* plusA (F := F) :=
  (Classical.choice (CFSG.ComponentClassification.GMS78.nonempty_SL2_equiv_galois F
    (f := 2) (by norm_num) (by rw [hF]; norm_num))).symm.trans
    ((MonoidHom.ofInjective (j1_injective (F := F))).trans
      (Subgroup.subgroupOfEquivOfLe (j1_range_le_orthogonalPlus (F := F))).symm)

theorem conj_j1_eq_j2 {r : plusO F} {a : Matrix.SpecialLinearGroup (Fin 2) F}
    (hr : (r : GL (Fin 2 ⊕ Fin 2) F) = j1 a * tauMat * (j1 a)⁻¹)
    (b : Matrix.SpecialLinearGroup (Fin 2) F) :
    r * j1O b * r⁻¹ = j2O (a⁻¹ * b * a) := by
  refine Subtype.ext ?_
  show (r : GL (Fin 2 ⊕ Fin 2) F) * j1 b * (r : GL (Fin 2 ⊕ Fin 2) F)⁻¹ =
    j2 (a⁻¹ * b * a)
  rw [hr]
  have hinv : (j1 a * tauMat * (j1 a)⁻¹)⁻¹ = j1 a * tauMat * (j1 a)⁻¹ := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, tauMat_inv, inv_inv]
    group
  rw [hinv]
  have hmid : (j1 a)⁻¹ * j1 b * j1 a = j1 (a⁻¹ * b * a) := by
    rw [← map_inv, ← map_mul, ← map_mul]
  calc (j1 a * tauMat * (j1 a)⁻¹) * j1 b * (j1 a * tauMat * (j1 a)⁻¹)
      = j1 a * tauMat * ((j1 a)⁻¹ * j1 b * j1 a) * tauMat * (j1 a)⁻¹ := by group
    _ = j1 a * tauMat * j1 (a⁻¹ * b * a) * tauMat * (j1 a)⁻¹ := by rw [hmid]
    _ = j1 a * (tauMat * j1 (a⁻¹ * b * a) * tauMat) * (j1 a)⁻¹ := by group
    _ = j1 a * j2 (a⁻¹ * b * a) * (j1 a)⁻¹ := by rw [tau_conj_j1]
    _ = j2 (a⁻¹ * b * a) * j1 a * (j1 a)⁻¹ := by
          rw [(j1_j2_commute a (a⁻¹ * b * a)).eq]
    _ = j2 (a⁻¹ * b * a) := by group

theorem map_conj_plusA [Finite F] [CharP F 2] {r : plusO F}
    (hr : r * r = 1) (hrN : r ∉ plusN (F := F)) :
    plusA (F := F).map (MulAut.conj r).toMonoidHom = plusB (F := F) := by
  obtain ⟨a, ha⟩ := exists_j1_conj_tauMat_of_mul_self_eq_one (F := F) hr hrN
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := mem_plusA_iff.1 hx
    rw [show x = j1O b from Subtype.ext hb.symm]
    change r * j1O b * r⁻¹ ∈ plusB (F := F)
    rw [conj_j1_eq_j2 ha b]
    exact j2_mem_plusB _
  · intro y hy
    obtain ⟨b, hb⟩ := mem_plusB_iff.1 hy
    rw [show y = j2O b from Subtype.ext hb.symm]
    refine ⟨j1O (a * b * a⁻¹), j1_mem_plusA _, ?_⟩
    change r * j1O (a * b * a⁻¹) * r⁻¹ = j2O b
    rw [conj_j1_eq_j2 ha (a * b * a⁻¹)]
    congr 1
    group

end Generic


theorem exists_isFiveReflectionModel_of_mulEquiv_orthogonalPlus_four
    {X : Type} [Group X] {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : X ≃* ↥(CFSG.PGLModel.orthogonalPlus 2 F)) {s : X} (hs : s * s = 1)
    (hgen : Subgroup.closure {x | IsConj s x} = ⊤) :
    ∃ π, CFSG.OddTranspositions.PartThree.IsFiveReflectionModel 3 true π {x | IsConj s x} := by
  let r : ↥(CFSG.PGLModel.orthogonalPlus 2 F) := e s
  have hr : r * r = 1 := by
    change e s * e s = 1
    rw [← map_mul, hs, map_one]
  have hgenr : Subgroup.closure {y : ↥(CFSG.PGLModel.orthogonalPlus 2 F) | IsConj r y} = ⊤ :=
    CFSG.GroupTheory.closure_isConj_mulEquiv_eq_top e hgen
  have hrN : r ∉ plusN (F := F) := not_mem_plusN_of_closure_isConj hgenr
  obtain ⟨Ψ, hΨ⟩ := CFSG.OddTranspositions.PartThree.exists_mulEquiv_wreathTwo (plusAEquivPSL2 hF)
    (plusA_inf_plusB (F := F)) (fun a ha b hb => plusA_commute_plusB ha hb)
    (index_sup_plusA_plusB (F := F)) hr (by rwa [plusA_sup_plusB]) (map_conj_plusA hr hrN)
  have hes : (e.trans Ψ.symm) s = SemidirectProduct.inr (Equiv.swap 0 1) := by
    have h1 : (e.trans Ψ.symm) s = Ψ.symm r := rfl
    rw [h1, ← hΨ, MulEquiv.symm_apply_apply]
  exact CFSG.OddTranspositions.PartThree.isFiveReflectionModel_of_l2Wreath_two_two
    (e := e.trans Ψ.symm)
    (by simpa [hes] using IsConj.refl (SemidirectProduct.inr (Equiv.swap 0 1)))

end CFSG.OddTranspositions.PartFour
