module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofU54
public import CFSG.RankThree.PartTwo.Sec21.U4FourGroupLines
public import CFSG.RankThree.PartOne.K1320X.U4Emb
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne.KFU (dvec5 diagU torus6 d8Vec d8Vec_mem_SU d8Comb_four d8Vec_four
  dvec4 card_center_mulEquiv)
open CFSG.RankThree.PartOne.K1320X (su4Emb su4Emb_injective gu5_su4Emb embMat45 eSum45)

variable {G : Type} [Group G]

theorem card_U44 : Nat.card (projSU 4 2 2) = 1018368000 :=
  CFSG.PGLModel.card_projSU_four_four

theorem center_SU44 : Subgroup.center (↥(SU σ16 4)) = ⊥ := by
  obtain ⟨θ⟩ := U4Lines.nonempty_projSU_mulEquiv_SU 2 (by norm_num)
  have : IsSimpleGroup (projSU 4 2 2) := isSimpleGroup_projSU le_rfl (by norm_num)
  have hZ : Subgroup.center (projSU 4 2 2) = ⊥ :=
    Sec4.Item434Spor.center_eq_bot_of_simple (by rw [card_U44]; norm_num)
  have h := card_center_mulEquiv θ
  rw [hZ, Subgroup.card_bot] at h
  exact Subgroup.eq_bot_of_card_eq _ h.symm

theorem qU_su4Emb_injective : Function.Injective (qU.comp (su4Emb σ16)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hc : su4Emb σ16 y ∈ Subgroup.center SU54 := isCentralPQuot_qU.central hy
  have hyc : y ∈ Subgroup.center (↥(SU σ16 4)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply su4Emb_injective σ16
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hc (su4Emb σ16 z)
  rw [center_SU44] at hyc
  exact hyc

@[expose] noncomputable def tt4 (a b : rootsOfUnity 3 K16) : ↥(SU σ16 4) :=
  ⟨diagU (d8Vec 4 ((a, b) : rootsOfUnity 3 K16 × rootsOfUnity 3 K16)),
    d8Vec_mem_SU (Or.inl rfl) d8Comb_four σ16 σ16_mu3 _⟩

theorem tt_eq_su4Emb (a b : rootsOfUnity 3 K16) : tt a b = su4Emb σ16 (tt4 a b) := by
  apply Subtype.ext
  apply Units.ext
  change ((diagU (dvec5 (a : K16ˣ) (b : K16ˣ)) : GL (Fin 5) K16) : Matrix (Fin 5) (Fin 5) K16) =
    embMat45 ((diagU (d8Vec 4 ((a, b) : rootsOfUnity 3 K16 × rootsOfUnity 3 K16)) :
      GL (Fin 4) K16) : Matrix (Fin 4) (Fin 4) K16)
  rw [d8Vec_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embMat45, eSum45, CFSG.RankThree.PartOne.KFU.diagU_val, dvec4, dvec5]

theorem exists_U44_of_model [Finite G] {A Z : Subgroup G} (ε : Z ≃* U54)
    (hT2 : ∀ f (hf : f ∈ A ⊓ Z), ∃ t ∈ torus6 σ16 3, ε ⟨f, (Subgroup.mem_inf.mp hf).2⟩ = qU t) :
    ∃ Y : Subgroup G, Y ≤ Z ∧ A ⊓ Z ≤ Y ∧ Nonempty (Y ≃* projSU 4 2 2) := by
  set θ : ↥(SU σ16 4) →* G :=
    Z.subtype.comp (ε.symm.toMonoidHom.comp (qU.comp (su4Emb σ16))) with hθ
  have hθinj : Function.Injective θ :=
    Z.subtype_injective.comp (ε.symm.injective.comp qU_su4Emb_injective)
  refine ⟨θ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (ε.symm (qU (su4Emb σ16 y))).2
  · intro f hf
    obtain ⟨t, ht, h⟩ := hT2 f hf
    obtain ⟨a, b, rfl⟩ := exists_tt ht
    refine ⟨tt4 a b, ?_⟩
    have h1 : ε.symm (qU (tt a b)) = ⟨f, (Subgroup.mem_inf.mp hf).2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact h.symm
    change ((ε.symm (qU (su4Emb σ16 (tt4 a b))) : Z) : G) = f
    rw [← tt_eq_su4Emb, h1]
  · obtain ⟨e₄⟩ := U4Lines.nonempty_projSU_mulEquiv_SU 2 (by norm_num)
    exact ⟨(MonoidHom.ofInjective hθinj).symm.trans e₄.symm⟩

theorem lines_U54 [Finite G] {A Z : Subgroup G} (hAe : IsElemAbelian 3 A) (ε : Z ≃* U54)
    (hT2 : ∀ f (hf : f ∈ A ⊓ Z), ∃ t ∈ torus6 σ16 3, ε ⟨f, (Subgroup.mem_inf.mp hf).2⟩ = qU t) :
    ∀ ℓ : Subgroup G, ℓ ≤ A ⊓ Z → Nat.card ℓ = 3 → ∃ V : Subgroup G, V ≤ Z ∧
      IsElemAbelian 2 V ∧ Nat.card V = 4 ∧ A ⊓ Z ≤ Subgroup.normalizer (V : Set G) ∧
      (A ⊓ Z) ⊓ Subgroup.centralizer (V : Set G) = ℓ := by
  intro ℓ hℓ hℓ3
  obtain ⟨Y, hYZ, hFY, hY⟩ := exists_U44_of_model ε hT2
  have hFe : IsElemAbelian 3 (A ⊓ Z) := isElemAbelian_of_le hAe inf_le_left
  obtain ⟨V, hVY, hVe, hV4, hVN, hVC⟩ :=
    U4FourLines.u4FourGroupLines (by norm_num) even_two G Y hY (A ⊓ Z) ℓ hFY hFe hℓ hℓ3
  exact ⟨V, hVY.trans hYZ, hVe, hV4, hVN, hVC⟩

end CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof
