module

public import CFSG.Quasithin.H13.StatementsL5C
public import CFSG.Quasithin.Background.SmithB45MatM12
public import CFSG.Quasithin.Background.SmithB45MatIndM24
public import CFSG.Quasithin.Background.SmithB45HM22Holds
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch7Prop711Grp

public section

namespace CFSG.Quasithin.H13.Prop711

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open HatM22 CFSG.CharacterTheory.SteinbergBY
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}


omit [Finite G] in
theorem mul_self_eq_one_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) (v : ↥V) :
    v * v = 1 := by
  apply Subtype.ext
  have h1 := hV.2 (v : G) v.2
  rw [Subgroup.coe_mul, ← sq, h1]
  rfl

omit [Finite G] in
theorem nonempty_autOn_mulEquiv_m12
    {V : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hperf : Group.IsPerfect ↥(autOn L V))
    (hnt : autOn L V ≠ ⊥) (e : ↥(autOn (L ⊔ T) V) ≃* MulAut NativeSporadic.M12) :
    Nonempty (↥(autOn L V) ≃* NativeSporadic.M12) := by
  have hle : autOn L V ≤ autOn (L ⊔ T) V := InternalSec.autOn_le_autOn_of_le le_sup_left
  set N := (autOn L V).subgroupOf (autOn (L ⊔ T) V) with hN
  have eN : ↥N ≃* ↥(autOn L V) := Subgroup.subgroupOfEquivOfLe hle
  have hNn : N.Normal := by
    refine ⟨fun k hk x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact InternalSec.autOn_normal_of (sup_le Subgroup.le_normalizer hTL) _ x.2 _ hk
  have hNperf : Group.IsPerfect ↥N := Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom)
    eN.symm.surjective
  have hNne : N ≠ ⊥ := by
    intro h
    apply hnt
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(autOn (L ⊔ T) V)) ∈ N := hx
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨e'⟩ := nonempty_mulEquiv_m12 hNn hNperf hNne e
  exact ⟨eN.symm.trans e'⟩

theorem isQuasisimple_of_hatM22 {X : Type} [Group X]
    (hP : Group.IsPerfect X) (e : X ⧸ Subgroup.center X ≃* NativeSporadic.M22) :
    CFSG.IsQuasisimple X := by
  obtain ⟨-, hnt, hsimp⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  have : Nontrivial NativeSporadic.M22 := hnt
  have hS : IsSimpleGroup (X ⧸ Subgroup.center X) := e.isSimpleGroup
  refine ⟨hP, hS, ?_⟩
  by_contra h
  push Not at h
  have hPQ : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hcomm : commutator (X ⧸ Subgroup.center X) = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, h a b, mul_inv_cancel_right, mul_inv_cancel]
  rw [hPQ.commutator_eq_top] at hcomm
  have : Nontrivial (X ⧸ Subgroup.center X) := e.toEquiv.nontrivial
  exact top_ne_bot hcomm

theorem rows_of_irr
    (h329 : Stmt3_2_9C) (hyp : Hyp7_0_2 G T L I) (hL0 : L = fsuL0 T L)
    (hIV : I = conjClosure I T) [hab : IsMulCommutative ↥(fsuV T I)]
    (hV : IsElemAbelian 2 (fsuV T I)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hperf : Group.IsPerfect ↥(autOn L (fsuV T I))) (hnt : autOn L (fsuV T I) ≠ ⊥)
    (hirr : ∀ U : Subgroup ↥(fsuV T I), (∀ g ∈ autOn L (fsuV T I), ∀ u ∈ U, g u ∈ U) →
      U = ⊥ ∨ U = ⊤) : Rows7_1_1 T L I := by
  have hL0' : fsuL0 T L = L := hL0.symm
  have hfsu' : FSU G T L (fsuV T I) := by
    show FSU G T L (conjClosure I T)
    rw [← hIV]
    exact hyp.fsu
  have hVV : fsuV T I = conjClosure (fsuV T I) T := by
    show conjClosure I T = conjClosure (conjClosure I T) T
    rw [← hIV]
    exact hIV
  have hnotFF : ¬ IsFFModule (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I)))) := by
    intro hFF
    apply hyp.notFF hab
    show ∃ A : Subgroup (MulAut ↥(fsuV T I)), IsFFStarOffender (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn (fsuL0 T L) (fsuV T I) : Set (MulAut ↥(fsuV T I)))) A
    rw [hL0']
    exact B6.exists_isFFStarOffender hFF
  have hV2 := mul_self_eq_one_of_isElemAbelian hV
  have hVsq : ∀ v : ↥(fsuV T I), v ^ 2 = 1 := fun v => by rw [sq]; exact hV2 v
  have hirrX : XMod.IsIrrSec ↥(autOn L (fsuV T I)) (⊥ : Subgroup ↥(fsuV T I)) ⊤ := by
    refine ⟨?_, fun J hJ _ _ => hirr J fun g hg u hu => hJ ⟨g, hg⟩ u hu⟩
    rw [bot_lt_iff_ne_bot]
    intro h
    apply hnt
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext v
    have : v ∈ (⊥ : Subgroup ↥(fsuV T I)) := by rw [← h]; exact Subgroup.mem_top v
    rw [Subgroup.mem_bot] at this
    rw [this, map_one]
    rfl
  obtain ⟨_, hcases⟩ := h329 G T L (fsuV T I) hfsu' hL0 hVV ⟨hab, hnotFF⟩
  unfold Rows7_1_1
  rcases hcases with ⟨n, hn1, -, hO4, -⟩ | ⟨n, hSU, -⟩ | ⟨f, hSz, -⟩ |
      ⟨n, K, _, _, _, hn1, hK, -, -, -, -, π, hπ, -⟩ | ⟨⟨eA⟩, hcard, -, -⟩ |
      ⟨hP, hZ3, ⟨eQ⟩, hcard, -⟩ | ⟨⟨eM⟩, hcard, -⟩ | ⟨⟨eM⟩, hcard, -⟩ | ⟨⟨eM⟩, hcard, -⟩
  ·
    exact (hyp.notOrth hab ⟨n, hn1, by rw [hL0']; exact hO4⟩).elim
  ·
    left
    refine ⟨n, ?_, by rw [hL0']; exact hSU⟩
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSU3.exists_equiv hSU
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exfalso
      interval_cases n
      · have := Finite.one_lt_card (α := K)
        rw [hK] at this
        norm_num at this
      · exact not_isPerfect_statedSU_three_two hK
          (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · exact hn
  ·
    right; left
    exact ⟨f, by rw [hL0']; exact hSz⟩
  ·
    right; right; left
    exact ⟨n, hn1, by rw [hL0']; exact ⟨K, inferInstance, inferInstance, inferInstance, hK, π, hπ⟩⟩
  ·
    right; right; right; left
    obtain ⟨eL⟩ := nonempty_autOn_mulEquiv_m12 hTL hperf hnt eA
    refine ⟨?_, ?_⟩
    · rw [hL0']
      exact mathieuSmallIrr12_holds _ hV2 _ ⟨eL⟩ hirr (by rw [hcard]; norm_num)
    · rw [hL0']
      exact ⟨eA⟩
  ·
    right; right; right; right; left
    unfold Row711M22Hat
    rw [hL0']
    have hHat : IsHat ↥(autOn L (fsuV T I)) (NativeSporadic.Carrier .M22) :=
      ⟨isQuasisimple_of_hatM22 hP eQ, hZ3, ⟨eQ⟩⟩
    have hR := hatM22SmallModules_holds _ hVsq _ hHat hirrX (by rw [hcard]; norm_num)
    exact ⟨FieldFour, inferInstance, inferInstance, hatM22Γ₀, FieldFour.natCard_eq,
      isHat_hatM22Γ₀, ⟨hatM22Form, hatM22Form_det_ne_zero, hatM22Form_hermitian,
        hatM22Form_invariant⟩, hR⟩
  ·
    rcases mathieuSmallIrr22_holds _ hV2 _ ⟨eM⟩ hirr (by rw [hcard]; norm_num) with h | h
    · right; right; right; right; right; left
      unfold Row711M22Code
      rw [hL0']
      exact h
    · right; right; right; right; right; right; left
      unfold Row711M22Cocode
      rw [hL0']
      exact h
  ·
    rcases mathieuSmallIrr23_holds _ hV2 _ ⟨eM⟩ hirr (by rw [hcard]; norm_num) with h | h
    · iterate 7 right
      left
      unfold Row711M23Code
      rw [hL0']
      exact h
    · iterate 8 right
      left
      unfold Row711M23Cocode
      rw [hL0']
      exact h
  ·
    rcases mathieuSmallIrr24_holds _ hV2 _ ⟨eM⟩ hirr (by rw [hcard]; norm_num) with h | h
    · iterate 9 right
      left
      unfold Row711M24Code
      rw [hL0']
      exact h
    · iterate 10 right
      left
      unfold Row711M24Cocode
      rw [hL0']
      exact h

end CFSG.Quasithin.H13.Prop711
