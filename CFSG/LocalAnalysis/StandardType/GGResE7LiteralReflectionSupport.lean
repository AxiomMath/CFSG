module

public import CFSG.LocalAnalysis.StandardType.GGResE6ActualSevenRootSupport
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGResE7LiteralModel
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGResE6Coordinates
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.Blueprint.Chevalley
public import CFSG.Assembly.E6FourCentMask
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Mathlib.Decide.Nodup
import CFSG.Mathlib.Decide.F3Rep
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Tactic
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13604
public import Certificates.Certificate13657
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate830101
public import CFSG.LocalAnalysis.StandardType.GGResE6ActualInsideSupport
public import CFSG.Quasithin.Vol2.KGFactC31RuRef


public section

namespace CFSG.StandardType.E7F3

local instance : Module F3 V7 := Pi.Function.module (Fin 7) F3 F3

private def linearMapOfPerm (g : Equiv.Perm V7) (hg : IsLinearPerm g) : V7 →ₗ[F3] V7 := by
  have hzero : g 0 = 0 := by
    have hz := hg 1 0 0
    simp only [one_smul, zero_add] at hz
    have hz' : g 0 + g 0 = g 0 + 0 := by simpa only [add_zero] using hz.symm
    exact add_left_cancel hz'
  exact {
    toFun := g
    map_add' := fun u v => by simpa only [one_smul] using hg 1 u v
    map_smul' := fun a v => by simpa only [zero_add, hzero, RingHom.id_apply] using hg a 0 v
  }

private theorem linearPerm_ext_basis {g f : Equiv.Perm V7}
    (hg : IsLinearPerm g) (hf : IsLinearPerm f)
    (he : ∀ i : Fin 7, g (e i) = f (e i)) : g = f := by
  have hmaps : linearMapOfPerm g hg = linearMapOfPerm f hf := by
    apply (Pi.basisFun F3 (Fin 7)).ext
    intro i
    rw [Pi.basisFun_apply]
    change g (Pi.single i 1) = f (Pi.single i 1)
    exact he i
  apply Equiv.ext
  intro v
  exact congrArg (fun T : V7 →ₗ[F3] V7 => T v) hmaps

@[expose] def badWitnessAxis : V7 := ![2, 1, 1, 2, 0, 0, 0]

theorem norm_badWitnessAxis : norm badWitnessAxis = 2 := by decide +kernel

theorem badWitness_as_inside_reflection :
    badWitness = reflPerm badWitnessAxis norm_badWitnessAxis := by
  have hbad : genBad ∈ linearPerms := by
    intro a u v
    change reflFun badBase (u + a • v) = reflFun badBase u + a • reflFun badBase v
    rw [reflFun_add, reflFun_smul]
  have hword : IsLinearPerm badWitness :=
    wordW_mem L_le_linear hbad badWitnessWord
  have hreflection : IsLinearPerm (reflPerm badWitnessAxis norm_badWitnessAxis) := by
    intro a u v
    change reflFun badWitnessAxis (u + a • v) =
      reflFun badWitnessAxis u + a • reflFun badWitnessAxis v
    rw [reflFun_add, reflFun_smul]
  apply linearPerm_ext_basis hword hreflection
  intro i
  rw [badWitness, wordW_apply, reflPerm_apply]
  fin_cases i <;> decide +kernel

private theorem literalL_preserves_rootList {g : Equiv.Perm V7} (hg : g ∈ L) :
    ∀ v, v ∈ rootList ↔ g v ∈ rootList := by
  have hmem : g ∈ Subgroup.closure (s7 '' firstSixSet) := hg
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ v, v ∈ rootList ↔ g v ∈ rootList)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨i, hi, rfl⟩ v
    exact s7_root_iff i hi v
  · intro v
    rfl
  · intro a b ha hb hpa hpb v
    rw [Equiv.Perm.mul_apply]
    exact (hpb v).trans (hpa (b v))
  · intro a ha hpa v
    have h := hpa (a⁻¹ v)
    simpa using h.symm

theorem bad_reflection_not_mem_of_inside_reflections
    (A : Subgroup (Equiv.Perm V7)) (hL : L ≤ A)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ A → reflPerm v hn ∈ L)
    {h : V7} (hn : norm h = 2) (hl : h 6 = 1)
    (hbad : key6 h ∈ badKeys) (hRA : reflPerm h hn ∈ A) : False := by
  obtain ⟨w, rfl⟩ := bad_word_of_key hl hbad
  let g : Equiv.Perm V7 := wordL w
  have hgL : g ∈ L := wordL_mem (le_refl L) w
  have hgA : g ∈ A := hL hgL
  have hglin : IsLinearPerm g := L_le_linear hgL
  have hgpair : PreservesPair g := L_le_pairPres hgL
  have hconj : g * genBad * g⁻¹ =
      reflPerm (g badBase) (by
        change pair (g badBase) (g badBase) = 2
        rw [hgpair badBase badBase]
        simpa [norm] using norm_badBase) := by
    simpa only [genBad] using conj_reflPerm hglin hgpair (h := badBase) norm_badBase
  have hRg : g * genBad * g⁻¹ ∈ A := by
    rw [hconj]
    simpa using hRA
  have hgen : genBad ∈ A := by
    have h1 : g⁻¹ * (g * genBad * g⁻¹) * g ∈ A :=
      mul_mem (mul_mem (inv_mem hgA) hRg) hgA
    have hEq : g⁻¹ * (g * genBad * g⁻¹) * g = genBad := by group
    rwa [hEq] at h1
  have hbW : badWitness ∈ A := wordW_mem hL hgen badWitnessWord
  have hbR : reflPerm badWitnessAxis norm_badWitnessAxis ∈ A := by
    rwa [badWitness_as_inside_reflection] at hbW
  have hbL : badWitness ∈ L := by
    rw [badWitness_as_inside_reflection]
    exact hInside badWitnessAxis norm_badWitnessAxis rfl hbR
  have hroot : badWitness (e 2) ∈ rootList :=
    (literalL_preserves_rootList hbL (e 2)).mp e2_mem_rootList
  rw [badWitness_image] at hroot
  exact badImage_not_mem_rootList hroot

end CFSG.StandardType.E7F3

end

public section

namespace CFSG.StandardType.E7F3

local instance : Module F3 V7 := Pi.Function.module (Fin 7) F3 F3

theorem classify_last1_of_inside_reflections (A : Subgroup (Equiv.Perm V7))
    (hL : L ≤ A) (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ A → reflPerm v hn ∈ L)
    {h : V7} (hn : norm h = 2) (hl : h 6 = 1)
    (hRA : reflPerm h hn ∈ A) : (∃ g ∈ L, h = g goodBase) ∨ (∃ g ∈ L, h = -(g goodBase)) := by
  have hk : key6 h ∈ List.range 729 := by
    rw [List.mem_range]
    exact key6_lt h
  have hnorm : norm (vOfKey (key6 h)) = 2 := by
    rw [vOfKey_key6 h hl]
    exact hn
  rcases key_coverage (key6 h) hk hnorm with hgood | hbad
  · obtain ⟨w, hw⟩ := good_word_of_key hl hgood
    left
    refine ⟨wordL w, wordL_mem (le_refl L) w, ?_⟩
    rw [hw, goodBase_eq_e6]
  · exact False.elim (bad_reflection_not_mem_of_inside_reflections A hL hInside hn hl hbad hRA)

theorem classify_all_of_inside_reflections (A : Subgroup (Equiv.Perm V7))
    (hL : L ≤ A) (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ A → reflPerm v hn ∈ L)
    {h : V7} (hn : norm h = 2) (hl : h 6 ≠ 0)
    (hRA : reflPerm h hn ∈ A) : (∃ g ∈ L, h = g goodBase) ∨ (∃ g ∈ L, h = -(g goodBase)) := by
  by_cases h1 : h 6 = 1
  · exact classify_last1_of_inside_reflections A hL hInside hn h1 hRA
  · have h2 : h 6 = 2 := by
      have hv0 : (h 6).val ≠ 0 := by
        intro hv
        apply hl
        have hv1' : (1 : F3).val = 1 := by decide +kernel
        apply (ZMod.val_injective 3)
        simpa [hv1'] using hv
      have hv1 : (h 6).val ≠ 1 := by
        intro hv
        apply h1
        have hv1' : (1 : F3).val = 1 := by decide +kernel
        apply (ZMod.val_injective 3)
        simpa [hv1'] using hv
      have hv2 : (h 6).val = 2 := by
        have := ZMod.val_lt (h 6)
        omega
      have hv2' : (2 : F3).val = 2 := by decide +kernel
      exact (ZMod.val_injective 3) (by simpa [hv2'] using hv2)
    have hn' : norm (-h) = 2 := norm_neg_two h hn
    have hl' : (-h) 6 = 1 := by
      change -(h 6) = 1
      rw [h2]
      decide +kernel
    have hRA' : reflPerm (-h) hn' ∈ A := by
      rw [reflPerm_neg h hn]
      exact hRA
    have hclass := classify_last1_of_inside_reflections A hL hInside hn' hl' hRA'
    rcases hclass with ⟨g, hgL, hg⟩ | ⟨g, hgL, hg⟩
    · right
      refine ⟨g, hgL, ?_⟩
      calc
        h = -(-h) := by exact (neg_neg h).symm
        _ = -(g goodBase) := by rw [hg]
    · left
      refine ⟨g, hgL, ?_⟩
      calc
        h = -(-h) := by exact (neg_neg h).symm
        _ = -(-(g goodBase)) := by rw [hg]
        _ = g goodBase := by exact neg_neg _

theorem outside_refl_eq_conj_of_inside_reflections
    (A : Subgroup (Equiv.Perm V7)) (hL : L ≤ A)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ A → reflPerm v hn ∈ L)
    {h : V7} (hn : norm h = 2) (hl : h 6 ≠ 0)
    (hRA : reflPerm h hn ∈ A) :
    ∃ g ∈ L, reflPerm h hn = g * s7 6 * g⁻¹ := by
  rcases classify_all_of_inside_reflections A hL hInside hn hl hRA with
    ⟨g, hgL, hg⟩ | ⟨g, hgL, hg⟩
  · exact ⟨g, hgL, good_refl_eq_conj hn hgL hg⟩
  · exact ⟨g, hgL, neg_good_refl_eq_conj hn hgL hg⟩

theorem outside_refl_mem_G7_of_inside_reflections
    (A : Subgroup (Equiv.Perm V7)) (hL : L ≤ A)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ A → reflPerm v hn ∈ L)
    {h : V7} (hn : norm h = 2) (hl : h 6 ≠ 0)
    (hRA : reflPerm h hn ∈ A) : reflPerm h hn ∈ G7 := by
  obtain ⟨g, hgL, heq⟩ := outside_refl_eq_conj_of_inside_reflections A hL hInside hn hl hRA
  rw [heq]
  exact mul_mem (mul_mem (L_le_G7 hgL) (Subgroup.subset_closure ⟨6, rfl⟩))
    (inv_mem (L_le_G7 hgL))

theorem closure_outside_refl_eq_G7_of_inside_reflections
    (A : Subgroup (Equiv.Perm V7)) (hL : L ≤ A)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ A → reflPerm v hn ∈ L)
    {h : V7} (hn : norm h = 2) (hl : h 6 ≠ 0)
    (hRA : reflPerm h hn ∈ A) :
    Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ {reflPerm h hn}) = G7 := by
  let T : Subgroup (Equiv.Perm V7) :=
    Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ {reflPerm h hn})
  have hLT : L ≤ T := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hRT : reflPerm h hn ∈ T := Subgroup.subset_closure (Or.inr (by simp))
  apply le_antisymm
  · apply (Subgroup.closure_le G7).mpr
    intro g hg
    rcases hg with hgL | hgR
    · exact L_le_G7 hgL
    · rw [Set.mem_singleton_iff] at hgR
      rw [hgR]
      exact outside_refl_mem_G7_of_inside_reflections A hL hInside hn hl hRA
  · obtain ⟨g, hgL, heq⟩ := outside_refl_eq_conj_of_inside_reflections A hL hInside hn hl hRA
    have hgT : g ∈ T := hLT hgL
    have hs6T : s7 6 ∈ T := by
      have h1 : g⁻¹ * reflPerm h hn * g ∈ T :=
        mul_mem (mul_mem (inv_mem hgT) hRT) hgT
      have hEq : g⁻¹ * reflPerm h hn * g = s7 6 := by
        rw [heq]
        group
      rwa [hEq] at h1
    apply (Subgroup.closure_le T).mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 6
    · simpa [hi] using hs6T
    · have hlt : i.val < 6 := by
        have := i.isLt
        omega
      exact hLT (Subgroup.subset_closure ⟨i, by simpa [firstSixSet] using hlt, rfl⟩)

end CFSG.StandardType.E7F3

end

public section

namespace CFSG.StandardType.E7F3

local instance : Module F3 V7 := Pi.Function.module (Fin 7) F3 F3

theorem generated_mixed_reflections_le_G7_of_inside_reflections
    (S : Set (Equiv.Perm V7))
    (hS : ∀ g ∈ S, ∃ (v : V7) (hn : norm v = 2), reflPerm v hn = g)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) →
      reflPerm v hn ∈ L) :
    Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) ≤ G7 := by
  let A : Subgroup (Equiv.Perm V7) :=
    Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S)
  have hL : L ≤ A := fun g hg => Subgroup.subset_closure (Or.inl hg)
  apply (Subgroup.closure_le G7).mpr
  intro g hg
  rcases hg with hgL | hgS
  · exact L_le_G7 hgL
  · obtain ⟨v, hn, rfl⟩ := hS g hgS
    have hvA : reflPerm v hn ∈ A := Subgroup.subset_closure (Or.inr hgS)
    by_cases hv : v 6 = 0
    · exact L_le_G7 (hInside v hn hv hvA)
    · exact outside_refl_mem_G7_of_inside_reflections A hL hInside hn hv hvA

theorem generated_mixed_reflections_eq_G7_of_inside_reflections
    (S : Set (Equiv.Perm V7))
    (hS : ∀ g ∈ S, ∃ (v : V7) (hn : norm v = 2), reflPerm v hn = g)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) →
      reflPerm v hn ∈ L)
    (hOutside : ∃ (v : V7) (hn : norm v = 2), v 6 ≠ 0 ∧
      reflPerm v hn ∈ Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S)) :
    Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) = G7 := by
  let A : Subgroup (Equiv.Perm V7) :=
    Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S)
  have hL : L ≤ A := fun g hg => Subgroup.subset_closure (Or.inl hg)
  apply le_antisymm
  · exact generated_mixed_reflections_le_G7_of_inside_reflections S hS hInside
  · obtain ⟨v, hn, hv, hvA⟩ := hOutside
    rw [← closure_outside_refl_eq_G7_of_inside_reflections A hL hInside hn hv hvA]
    apply (Subgroup.closure_le A).mpr
    intro g hg
    rcases hg with hgL | hgR
    · exact hL hgL
    · rw [Set.mem_singleton_iff] at hgR
      rwa [hgR]

end CFSG.StandardType.E7F3

end

public section

namespace CFSG.StandardType.E7F3

open Matrix
open CFSG.StandardType

local instance : Module F3 V7 := Pi.Function.module (Fin 7) F3 F3
local instance : Module (ZMod 3) V7 := Pi.Function.module (Fin 7) F3 F3

@[expose] def e7NodeFun : Fin 7 → Fin 7 := ![5, 1, 4, 3, 2, 0, 6]

lemma e7NodeFun_involutive : Function.Involutive e7NodeFun := by
  intro x
  fin_cases x <;> rfl

@[expose] noncomputable def e7Node : Equiv.Perm (Fin 7) :=
  e7NodeFun_involutive.toPerm e7NodeFun

@[simp] lemma e7Node_apply (i : Fin 7) : e7Node i = e7NodeFun i := rfl

@[simp] lemma e7Node_involutive_apply (i : Fin 7) : e7Node (e7Node i) = i :=
  e7NodeFun_involutive i

theorem C7_e7Node (i j : Fin 7) :
    C7 (e7Node i) (e7Node j) = ((CartanMatrix.E 7 i j : ℤ) : F3) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

lemma pair_e_e (a b : Fin 7) : pair (e a) (e b) = C7 a b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

@[expose] noncomputable def e7Root (i : Fin 7) : Module.Dual F3 V7 where
  toFun v := pair v (e (e7Node i))
  map_add' u w := by
    simpa using pair_add_left u w (e (e7Node i))
  map_smul' a v := by
    simpa [smul_eq_mul] using pair_smul_left a v (e (e7Node i))

@[simp] lemma e7Root_apply (i : Fin 7) (v : V7) :
    e7Root i v = pair v (e (e7Node i)) := rfl

lemma e7Root_self (i : Fin 7) : e7Root i (e (e7Node i)) = 2 := by
  rw [e7Root_apply]
  simpa [norm] using norm_e_all (e7Node i)

lemma e7Root_pairing (i j : Fin 7) :
    e7Root i (e (e7Node j)) = ((CartanMatrix.E 7 i j : ℤ) : F3) := by
  rw [e7Root_apply, pair_e_e]
  rw [← C7_isSymm.apply (e7Node j) (e7Node i)]
  exact C7_e7Node i j

@[expose] noncomputable def e7Refl (i : Fin 7) : V7 ≃ₗ[F3] V7 :=
  @Module.reflection F3 V7 (ZMod.commRing 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 7) F3 F3) (x := e (e7Node i)) (f := e7Root i) (e7Root_self i)

lemma e7Refl_apply (i : Fin 7) (v : V7) :
    e7Refl i v = v - pair v (e (e7Node i)) • e (e7Node i) := by
  rfl

lemma s7_e7Node_eq_e7Refl (i : Fin 7) (v : V7) :
    s7 (e7Node i) v = e7Refl i v := by
  rw [s7, reflPerm_apply, reflFun, e7Refl_apply]

lemma e7Refl_toEquiv_eq_s7 (i : Fin 7) :
    (e7Refl i).toEquiv = s7 (e7Node i) := by
  apply Equiv.ext
  intro v
  exact (s7_e7Node_eq_e7Refl i v).symm

@[expose] noncomputable def e7PermHom : (V7 ≃ₗ[F3] V7) →* Equiv.Perm V7 where
  toFun e := e.toEquiv
  map_one' := rfl
  map_mul' e f := rfl

@[simp] lemma e7PermHom_apply (e : V7 ≃ₗ[F3] V7) :
    e7PermHom e = e.toEquiv := rfl

lemma e7PermHom_injective : Function.Injective e7PermHom := by
  intro e f h
  exact LinearEquiv.toEquiv_injective h

@[expose] noncomputable def e7LinHom {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ V7) : MulAut ↥Bs →* (V7 ≃ₗ[F3] V7) :=
  @CFSG.StandardType.ggLin 3 (Fact.mk (by norm_num)) ↥Bs (inferInstance : Group ↥Bs) V7
    (Pi.addCommGroup) (Pi.Function.module (Fin 7) F3 F3) ι

lemma e7LinHom_apply_ofMul {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ V7) (φ : MulAut ↥Bs) (b : ↥Bs) :
    e7LinHom ι φ (ι (Additive.ofMul b)) = ι (Additive.ofMul (φ b)) := by
  rw [e7LinHom]
  exact @CFSG.StandardType.ggLin_apply_ofMul 3 (Fact.mk (by norm_num)) ↥Bs
    (inferInstance : Group ↥Bs) V7 (Pi.addCommGroup) (Pi.Function.module (Fin 7) F3 F3)
    ι φ b

lemma e7LinHom_injective {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ V7) : Function.Injective (e7LinHom ι) := by
  intro φ ψ h
  refine MulEquiv.ext fun b => ?_
  have hb := congrArg (fun T : V7 ≃ₗ[F3] V7 => T (ι (Additive.ofMul b))) h
  rw [e7LinHom_apply_ofMul, e7LinHom_apply_ofMul] at hb
  exact Additive.ofMul.injective (ι.injective hb)

@[expose] noncomputable def e7Liftable : CoxeterMatrix.E₇.IsLiftable e7Refl :=
  @CFSG.StandardType.isLiftable_reflection_of_intCartan F3 V7 (ZMod.commRing 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 7) F3 F3) (Γ := Fin 7) (M := CoxeterMatrix.E₇)
    (C := CartanMatrix.E 7) CFSG.StandardType.ggIntCartan_E₇
    (fun i => e (e7Node i)) e7Root e7Root_self e7Root_pairing

@[expose] noncomputable def e7LinLift : CoxeterMatrix.E₇.Group →* (V7 ≃ₗ[F3] V7) :=
  CoxeterMatrix.E₇.toCoxeterSystem.lift ⟨e7Refl, e7Liftable⟩

@[simp] lemma e7LinLift_apply_simple (i : Fin 7) :
    e7LinLift (CoxeterMatrix.E₇.simple i) = e7Refl i := by
  rw [e7LinLift]
  exact CoxeterSystem.lift_apply_simple (M := CoxeterMatrix.E₇) (cs := CoxeterMatrix.E₇.toCoxeterSystem)
    (f := e7Refl) e7Liftable i

lemma e7Node_independent : LinearIndependent F3 (fun i : Fin 7 => e (e7Node i)) := by
  have h := (Pi.linearIndependent_single_one (Fin 7) F3).comp e7Node e7Node.injective
  change LinearIndependent F3 ((fun i => Pi.single i 1) ∘ (e7Node : Fin 7 → Fin 7))
  exact h

lemma e7FaithfulInput {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 7 → V) (α : Fin 7 → Module.Dual (ZMod 3) V)
    (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h) :
    Function.Injective
      (CoxeterMatrix.E₇.toCoxeterSystem.lift
        ⟨fun i => Module.reflection (hα i),
          CFSG.StandardType.isLiftable_reflection_of_intCartan
            CFSG.StandardType.ggIntCartan_E₇ h α hα hP⟩) :=
  ggCartanFaithfulInputFixed_holds 3 (by norm_num) (by norm_num)
    (Fin 7) CoxeterMatrix.E₇ (CartanMatrix.E 7)
    (CFSG.StandardType.GGIsWeylMatrixE.isWeylMatrix
      (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), rfl⟩)))
    CFSG.StandardType.ggIntCartan_E₇ V h α hα hP hind

lemma e7LinLift_injective : Function.Injective e7LinLift := by
  let hL :=
    @CFSG.StandardType.isLiftable_reflection_of_intCartan F3 V7 (ZMod.commRing 3)
      (Pi.addCommGroup) (Pi.Function.module (Fin 7) F3 F3) (Γ := Fin 7)
      (M := CoxeterMatrix.E₇) (C := CartanMatrix.E 7) CFSG.StandardType.ggIntCartan_E₇
      (fun i => e (e7Node i)) e7Root e7Root_self e7Root_pairing
  let L :=
    CoxeterMatrix.E₇.toCoxeterSystem.lift ⟨fun i => e7Refl i, hL⟩
  have hfaith : Function.Injective L := by
    have h := @e7FaithfulInput V7 (Pi.addCommGroup)
      (Pi.Function.module (Fin 7) F3 F3) (fun i => e (e7Node i)) e7Root
      e7Root_self e7Root_pairing e7Node_independent
    convert h using 1
    · rfl
  have hL_eq : e7LinLift = L := by
    apply CoxeterMatrix.E₇.toCoxeterSystem.ext_simple
    intro i
    simp only [CoxeterMatrix.toCoxeterSystem_simple]
    rw [e7LinLift_apply_simple]
    rfl
  rwa [hL_eq]

@[expose] noncomputable def e7Gen (i : Fin 7) : ↥G7 :=
  ⟨s7 (e7Node i), Subgroup.subset_closure ⟨e7Node i, rfl⟩⟩

@[simp] lemma e7Gen_coe (i : Fin 7) :
    (e7Gen i : Equiv.Perm V7) = e7PermHom (e7Refl i) := by
  change s7 (e7Node i) = (e7Refl i).toEquiv
  exact (e7Refl_toEquiv_eq_s7 i).symm

lemma e7Gen_liftable : CoxeterMatrix.E₇.IsLiftable e7Gen := by
  intro i j
  apply Subtype.ext
  have h := congrArg e7PermHom (e7Liftable i j)
  simpa [e7Gen_coe, e7PermHom, map_mul, map_pow] using h

@[expose] noncomputable def e7GenLift : CoxeterMatrix.E₇.Group →* ↥G7 :=
  CoxeterMatrix.E₇.toCoxeterSystem.lift ⟨e7Gen, e7Gen_liftable⟩

@[simp] lemma e7GenLift_apply_simple (i : Fin 7) :
    e7GenLift (CoxeterMatrix.E₇.simple i) = e7Gen i := by
  rw [e7GenLift]
  exact CoxeterSystem.lift_apply_simple (M := CoxeterMatrix.E₇) (cs := CoxeterMatrix.E₇.toCoxeterSystem)
    (f := e7Gen) e7Gen_liftable i

lemma e7GenLift_range_eq_top : e7GenLift.range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  let P : (g : Equiv.Perm V7) → g ∈ G7 → Prop :=
    fun g hg => (⟨g, hg⟩ : ↥G7) ∈ e7GenLift.range
  have hP : P x.val x.2 := by
    refine Subgroup.closure_induction (p := P) ?mem ?one ?mul ?inv x.2
    · intro g hg
      obtain ⟨i, rfl⟩ := hg
      have hgen : (⟨s7 i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : ↥G7) ∈ e7GenLift.range := by
        refine ⟨CoxeterMatrix.E₇.simple (e7Node i), ?_⟩
        rw [e7GenLift_apply_simple]
        exact Subtype.ext (by
          change s7 (e7Node (e7Node i)) = s7 i
          rw [e7Node_involutive_apply])
      simpa [P] using hgen
    · exact ⟨1, map_one e7GenLift⟩
    · intro a b ha hb haP hbP
      exact Subgroup.mul_mem _ haP hbP
    · intro a ha haP
      exact Subgroup.inv_mem _ haP
  simpa [P] using hP

lemma e7GenLift_injective : Function.Injective e7GenLift := by
  have hcomp : e7PermHom.comp e7LinLift =
      (Subgroup.subtype G7).comp e7GenLift := by
    apply CoxeterMatrix.E₇.toCoxeterSystem.ext_simple
    intro i
    simp only [CoxeterMatrix.toCoxeterSystem_simple]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e7LinLift_apply_simple,
      e7GenLift_apply_simple]
    exact (e7Gen_coe i).symm
  intro w1 w2 h
  apply e7LinLift_injective
  apply e7PermHom_injective
  have hcomp_apply : ∀ w : CoxeterMatrix.E₇.Group,
      e7PermHom (e7LinLift w) = (e7GenLift w : Equiv.Perm V7) := by
    intro w
    have hw := congrArg (fun f : CoxeterMatrix.E₇.Group →* Equiv.Perm V7 => f w) hcomp
    simpa using hw
  rw [hcomp_apply w1, hcomp_apply w2]
  exact congrArg (fun x : ↥G7 => (x : Equiv.Perm V7)) h

@[expose] noncomputable def e7GroupEquivG7 : CoxeterMatrix.E₇.Group ≃* ↥G7 :=
  MulEquiv.ofBijective e7GenLift ⟨e7GenLift_injective, by
    intro x
    have hx : x ∈ e7GenLift.range := by
      rw [e7GenLift_range_eq_top]
      exact Subgroup.mem_top x
    simpa [MonoidHom.mem_range] using hx⟩

@[simp] lemma e7GroupEquivG7_apply_simple (i : Fin 7) :
    e7GroupEquivG7 (CoxeterMatrix.E₇.simple i) = e7Gen i := by
  change e7GenLift (CoxeterMatrix.E₇.simple i) = e7Gen i
  exact e7GenLift_apply_simple i

lemma e7IsReflection_of_e7LinHom {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ V7) {φ : MulAut ↥Bs} (i : Fin 7)
    (h : e7LinHom ι φ = e7Refl i) :
    CFSG.StandardType.GGIsReflection 3 φ := by
  refine @CFSG.StandardType.ggIsReflection_of_eq_reflection G (inferInstance : Group G) 3
    (Fact.mk (by norm_num)) Bs V7 (Pi.addCommGroup)
    (Pi.Function.module (Fin 7) F3 F3) (by norm_num) ι φ (e (e7Node i)) (e7Root i)
    (e7Root_self i) ?_
  change (e7LinHom ι φ) = e7Refl i
  exact h

theorem GGWeylReflectionGroup_of_e7_chart {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ V7) (φ : Fin 7 → MulAut ↥Bs)
    (hlin : ∀ i, e7LinHom ι (φ i) = e7Refl i)
    (A : Subgroup (MulAut ↥Bs)) (hA : Subgroup.closure (Set.range φ) = A) :
    CFSG.StandardType.GGWeylReflectionGroup 3 A := by
  have hLift : CoxeterMatrix.E₇.IsLiftable φ := by
    intro i j
    apply e7LinHom_injective ι
    rw [map_pow, map_mul, hlin i, hlin j, map_one]
    exact e7Liftable i j
  have hrefl : ∀ i, CFSG.StandardType.GGIsReflection 3 (φ i) := by
    intro i
    exact e7IsReflection_of_e7LinHom ι i (hlin i)
  have hcomp : (e7LinHom ι).comp
      (CoxeterMatrix.E₇.toCoxeterSystem.lift ⟨φ, hLift⟩) = e7LinLift := by
    apply CoxeterMatrix.E₇.toCoxeterSystem.ext_simple
    intro i
    simp only [CoxeterMatrix.toCoxeterSystem_simple]
    rw [MonoidHom.comp_apply, e7LinLift_apply_simple]
    exact hlin i
  have hinj : Function.Injective
      (CoxeterMatrix.E₇.toCoxeterSystem.lift ⟨φ, hLift⟩) := by
    intro w1 w2 h
    apply e7LinLift_injective
    have hcomp_apply : ∀ w : CoxeterMatrix.E₇.Group,
        e7LinHom ι (CoxeterMatrix.E₇.toCoxeterSystem.lift ⟨φ, hLift⟩ w) = e7LinLift w := by
      intro w
      have hw := congrArg (fun f : CoxeterMatrix.E₇.Group →* (V7 ≃ₗ[F3] V7) => f w) hcomp
      simpa using hw
    rw [← hcomp_apply w1, ← hcomp_apply w2]
    exact congrArg (e7LinHom ι) h
  have hW := CFSG.StandardType.ggWeylReflectionGroup_of_lift
    (hM := CFSG.StandardType.GGIsWeylMatrixE.isWeylMatrix
      (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), rfl⟩))) φ hLift hrefl hinj
  rwa [hA] at hW

lemma closure_range_e7Gen : Subgroup.closure (Set.range e7Gen) = ⊤ := by
  have hrange : e7GenLift.range = Subgroup.closure (Set.range e7Gen) := by
    rw [MonoidHom.range_eq_map,
      ← CoxeterSystem.subgroup_closure_range_simple (cs := CoxeterMatrix.E₇.toCoxeterSystem),
      MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, rfl⟩ := hi
      exact ⟨j, by
        simpa [CoxeterMatrix.toCoxeterSystem_simple] using (e7GenLift_apply_simple j).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨CoxeterMatrix.E₇.simple i, ⟨i, rfl⟩,
        by simpa [CoxeterMatrix.toCoxeterSystem_simple] using e7GenLift_apply_simple i⟩
  rw [← hrange, e7GenLift_range_eq_top]

theorem GGWeylReflectionGroup_of_e7_chart_equiv {G : Type} [Group G] {Bs : Subgroup G}
    (A : Subgroup (MulAut ↥Bs)) (ι : Additive ↥Bs ≃+ V7) (e : A ≃* ↥G7)
    (hchart : ∀ (a : A) (b : ↥Bs),
      ι (Additive.ofMul ((a : MulAut ↥Bs) b)) =
        ((e a : ↥G7) : Equiv.Perm V7) (ι (Additive.ofMul b))) :
    CFSG.StandardType.GGWeylReflectionGroup 3 A := by
  let ψ : Fin 7 → A := fun i => e.symm (e7Gen i)
  let φ : Fin 7 → MulAut ↥Bs := fun i => (ψ i : MulAut ↥Bs)
  have hlin : ∀ i, e7LinHom ι (φ i) = e7Refl i := by
    intro i
    apply LinearEquiv.ext
    intro v
    let b : ↥Bs := Additive.toMul (ι.symm v)
    have hb : ι (Additive.ofMul b) = v := by simp [b]
    rw [← hb]
    rw [e7LinHom_apply_ofMul]
    change ι (Additive.ofMul (((ψ i : A) : MulAut ↥Bs) b)) =
      e7Refl i (ι (Additive.ofMul b))
    rw [hchart (ψ i) b, MulEquiv.apply_symm_apply]
    change s7 (e7Node i) (ι (Additive.ofMul b)) = e7Refl i (ι (Additive.ofMul b))
    exact s7_e7Node_eq_e7Refl i _
  have hmap : (Subgroup.closure (Set.range ψ)).map (e : A →* ↥G7) =
      Subgroup.closure (Set.range e7Gen) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨i, rfl⟩ := ha
      exact ⟨i, by simp [ψ]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ψ i, ⟨i, rfl⟩, by simp [ψ]⟩
  have hclosureA : Subgroup.closure (Set.range ψ) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have hg : e a ∈ Subgroup.closure (Set.range e7Gen) := by
      rw [closure_range_e7Gen]
      exact Subgroup.mem_top (e a)
    rw [← hmap] at hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨a', ha', heq⟩ := hg
    have haneq : a' = a := e.injective heq
    simpa [haneq] using ha' 
  have hclosure : Subgroup.closure (Set.range φ) = A := by
    change Subgroup.closure (Set.range (fun i => (ψ i : MulAut ↥Bs))) = A
    have hcl : Subgroup.closure (Set.range (fun i => (ψ i : MulAut ↥Bs))) =
        (Subgroup.closure (Set.range ψ)).map (Subgroup.subtype A) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨ψ i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hcl, hclosureA, Subgroup.map_top, Subgroup.range_subtype]
  exact GGWeylReflectionGroup_of_e7_chart ι φ hlin A hclosure

end CFSG.StandardType.E7F3

end

section
namespace CFSG.StandardType.E6Seven

open CFSG.StandardType.E7F3
open CFSG.Assembly Module
open scoped Matrix

local instance joinModuleF3V7 : Module F3 V7 :=
  Pi.Function.module (Fin 7) F3 F3

theorem chartConjHom_injective_generated
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V) :
    Function.Injective (chartConjHom chi ι) := by
  intro F H hFH
  apply ggLin_injective (p := 3) ι
  apply LinearEquiv.ext
  intro v
  have hv := congrArg (fun e : Equiv.Perm V7 => e (chi v)) hFH
  change chartConj chi ι F (chi v) = chartConj chi ι H (chi v) at hv
  rw [chartConj_apply, chartConj_apply] at hv
  apply chi.injective
  simpa using hv

theorem e6_actual_seven_join_compose_with_mixed_generation
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    (AL AK : Subgroup (MulAut ↥Bs)) (Aadd : Set (MulAut ↥Bs))
    (hAL : Subgroup.map (chartConjHom chi ι) AL = L)
    (hAaddAK : Aadd ⊆ AK)
    (hAK_le : AK ≤ AL ⊔ Subgroup.closure Aadd)
    (hS : ∀ a ∈ Aadd, ∃ (v : V7) (hn : norm v = 2),
      chartConj chi ι a = reflPerm v hn)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ Subgroup.closure
        ((L : Set (Equiv.Perm V7)) ∪ (chartConjHom chi ι '' Aadd)) →
      reflPerm v hn ∈ L)
    (hOutside : ∃ a ∈ Aadd, ∃ (v : V7) (hn : norm v = 2),
      chartConj chi ι a = reflPerm v hn ∧ v 6 ≠ 0)
    :
    CFSG.StandardType.GGWeylReflectionGroup 3 (AL ⊔ AK) := by
  let f : MulAut ↥Bs →* Equiv.Perm V7 := chartConjHom chi ι
  let S : Set (Equiv.Perm V7) := f '' Aadd
  have hS' : ∀ g ∈ S, ∃ (v : V7) (hn : norm v = 2), reflPerm v hn = g := by
    rintro g ⟨a, ha, rfl⟩
    obtain ⟨v, hn, hv⟩ := hS a ha
    exact ⟨v, hn, hv.symm⟩
  have hOutside' : ∃ (v : V7) (hn : norm v = 2), v 6 ≠ 0 ∧
      reflPerm v hn ∈ Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) := by
    obtain ⟨a, ha, v, hn, hv, hvlast⟩ := hOutside
    have hmem : f a ∈ S := ⟨a, ha, rfl⟩
    have hEq : f a = reflPerm v hn := by
      show chartConj chi ι a = reflPerm v hn
      exact hv
    exact ⟨v, hn, hvlast, by
      rw [← hEq]
      exact Subgroup.subset_closure (Or.inr hmem)⟩
  have hclosure : Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) = G7 :=
    generated_mixed_reflections_eq_G7_of_inside_reflections S hS' (by simpa [S, f] using hInside) hOutside'
  have hmap_le : Subgroup.map f (AL ⊔ AK) ≤
      Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rw [hAL]
      intro x hx
      exact Subgroup.subset_closure (Or.inl hx)
    · calc
        Subgroup.map f AK ≤ Subgroup.map f (AL ⊔ Subgroup.closure Aadd) :=
          Subgroup.map_mono hAK_le
        _ = Subgroup.map f AL ⊔ Subgroup.map f (Subgroup.closure Aadd) := by
          rw [Subgroup.map_sup]
        _ = L ⊔ Subgroup.closure S := by
          rw [hAL, MonoidHom.map_closure]
        _ ≤ Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) := by
          apply sup_le
          · intro x hx
            exact Subgroup.subset_closure (Or.inl hx)
          · rw [Subgroup.closure_le]
            intro x hx
            exact Subgroup.subset_closure (Or.inr hx)
  have hclosure_le_map : Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) ≤
      Subgroup.map f (AL ⊔ AK) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hxL | hxS
    · have hxL' : x ∈ Subgroup.map f AL := by
        rw [hAL]
        exact hxL
      exact Subgroup.map_mono (show AL ≤ AL ⊔ AK from le_sup_left) hxL' 
    · rcases hxS with ⟨a, ha, rfl⟩
      have hmem : f a ∈ Subgroup.map f AK :=
        Subgroup.mem_map.mpr ⟨a, hAaddAK ha, rfl⟩
      exact Subgroup.map_mono (show AK ≤ AL ⊔ AK from le_sup_right) hmem
  have himage : Subgroup.map f (AL ⊔ AK) =
      Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ S) :=
    le_antisymm hmap_le hclosure_le_map
  have himageG7 : Subgroup.map f (AL ⊔ AK) = G7 := himage.trans hclosure
  have hInj : Function.Injective f := chartConjHom_injective_generated chi ι
  let e0 : ↥(AL ⊔ AK) ≃* ↥(Subgroup.map f (AL ⊔ AK)) :=
    Subgroup.equivMapOfInjective (AL ⊔ AK) f hInj
  let e : ↥(AL ⊔ AK) ≃* ↥G7 := e0.trans (MulEquiv.subgroupCongr himageG7)
  have he_apply : ∀ a : ↥(AL ⊔ AK),
      ((e a : ↥G7) : Equiv.Perm V7) = chartConj chi ι (a : MulAut ↥Bs) := by
    intro a
    rfl
  let iota7 : Additive ↥Bs ≃+ V7 := ι.trans chi.toAddEquiv
  have hchart : ∀ (a : ↥(AL ⊔ AK)) (b : ↥Bs),
      iota7 (Additive.ofMul ((a : MulAut ↥Bs) b)) =
        ((e a : ↥G7) : Equiv.Perm V7) (iota7 (Additive.ofMul b)) := by
    intro a b
    rw [he_apply]
    change chi (ι (Additive.ofMul ((a : MulAut ↥Bs) b))) =
      chi (ggLin (p := 3) ι (a : MulAut ↥Bs)
        (chi.symm (chi (ι (Additive.ofMul b)))))
    simp only [LinearEquiv.symm_apply_apply]
    rw [ggLin_apply_ofMul]
  exact GGWeylReflectionGroup_of_e7_chart_equiv
    (AL ⊔ AK) iota7 e hchart

theorem e6_actual_seven_join_of_sources_with_mixed_generation
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    {Lgrp K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (S : Finset Λ)
    {Λa : Type} [Fintype Λa]
    (e : Fin 6 ≃ Λ)
    (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hclosL : ggAutomizer Lgrp Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hgenAction : ∀ i : Fin 6,
      chartConj chi ι (φ (Sum.inl (e i))) = s7 i.castSucc)
    (hS : ∀ a : Λa, ∃ (v : V7) (hn : norm v = 2),
      chartConj chi ι (φ (Sum.inr a)) = reflPerm v hn)
    (hInside : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ Subgroup.closure
        ((L : Set (Equiv.Perm V7)) ∪
          (chartConjHom chi ι '' Set.range fun a : Λa => φ (Sum.inr a))) →
      reflPerm v hn ∈ L)
    (hOutside : ∃ a : Λa, ∃ (v : V7) (hn : norm v = 2),
      chartConj chi ι (φ (Sum.inr a)) = reflPerm v hn ∧ v 6 ≠ 0)
    :
    CFSG.StandardType.GGWeylReflectionGroup 3
      (ggAutomizer Lgrp Bs ⊔ ggAutomizer K Bs) := by
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e i))
  let Aadd : Set (MulAut ↥Bs) := Set.range fun a : Λa => φ (Sum.inr a)
  have hclosL' : ggAutomizer Lgrp Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [φL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
  have hAL : Subgroup.map (chartConjHom chi ι) (ggAutomizer Lgrp Bs) = L := by
    simpa [L, firstSixSet] using
      chartConj_map_closure_eq_literalL chi ι φL Lgrp
        (by simpa [φL] using hgenAction) hclosL'
  have hAaddAK : Aadd ⊆ ggAutomizer K Bs := by
    rintro x ⟨a, rfl⟩
    rw [hclosK]
    exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  have hAK_le : ggAutomizer K Bs ≤
      ggAutomizer Lgrp Bs ⊔ Subgroup.closure Aadd := by
    rw [hclosK]
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rcases hx with ⟨j, rfl⟩
      apply Subgroup.mem_sup_left
      rw [hclosL]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    · rcases hx with ⟨a, rfl⟩
      apply Subgroup.mem_sup_right
      exact Subgroup.subset_closure ⟨a, rfl⟩
  exact e6_actual_seven_join_compose_with_mixed_generation chi ι
    (ggAutomizer Lgrp Bs) (ggAutomizer K Bs) Aadd hAL hAaddAK hAK_le
    (by
      rintro x ⟨a, rfl⟩
      exact hS a)
    (by simpa [Aadd] using hInside)
    (by
      obtain ⟨a, v, hn, hv, hvlast⟩ := hOutside
      exact ⟨φ (Sum.inr a), ⟨a, rfl⟩, v, hn, hv, hvlast⟩)

end CFSG.StandardType.E6Seven
end

public section

namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E7F3
open scoped Matrix

local instance : Module F3 V7 := Pi.Function.module (Fin 7) F3 F3

theorem normalized_chart_H_castSucc
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (h : Fin 6 → V)
    (hchi : ∀ i, chi (h i) = e i.castSucc)
    (u : Fin 6 → ZMod 3) (j : Fin 6) :
    chi (Fintype.linearCombination (ZMod 3) h u) j.castSucc = u j := by
  rw [Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul, hchi]
  simp [e, Finset.sum_apply, Pi.single_apply]

theorem normalized_chart_H_last
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (h : Fin 6 → V)
    (hchi : ∀ i, chi (h i) = e i.castSucc)
    (u : Fin 6 → ZMod 3) :
    chi (Fintype.linearCombination (ZMod 3) h u) (Fin.last 6) = 0 := by
  have hne (i : Fin 6) : (6 : Fin 7) ≠ i.castSucc := by
    intro heq
    have := congrArg Fin.val heq
    change (6 : ℕ) = i.val at this
    omega
  rw [Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul, hchi]
  simp [e, Finset.sum_apply, Pi.single_apply, hne]

theorem normalized_inside_reflection_lift_mem_actualL
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (φL : Fin 6 → MulAut ↥Bs)
    (hLI : LinearIndependent (ZMod 3) h)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v, Bform (ggLin (p := 3) ι (φL i) u)
      (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (chi : V ≃ₗ[ZMod 3] V7)
    (hchi : ∀ i, chi (h i) = e i.castSucc)
    (hform : ∀ u v, Bform u v = pair (chi u) (chi v))
    (lam : ZMod 3)
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r)
    {F : MulAut ↥Bs} (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (v : V7) (hn : norm v = 2) (hv : v 6 = 0)
    (hFchart : chartConj chi ι F = reflPerm v hn) :
    F ∈ ggAutomizer L Bs := by
  let s : Fin 6 → ZMod 3 := fun i => v i.castSucc
  let ha : V := Fintype.linearCombination (ZMod 3) h s
  let aa : Module.Dual (ZMod 3) V := Bform ha
  have hha : chi ha = v := by
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [ha, hv] using normalized_chart_H_last chi h hchi s
    · exact normalized_chart_H_castSucc chi h hchi s i
  have hFlin : ∀ w, ggLin (p := 3) ι F w = w - aa w • ha := by
    intro w
    apply chi.injective
    have hc := congrArg (fun P : Equiv.Perm V7 => P (chi w)) hFchart
    rw [chartConj_apply, LinearEquiv.symm_apply_apply, reflPerm_apply, reflFun] at hc
    rw [map_sub, map_smul, hha]
    change chi (ggLin (p := 3) ι F w) = chi w - Bform ha w • v
    rw [hform, hha, pair_comm]
    exact hc
  have hself : aa ha = 2 := by
    change Bform ha ha = 2
    rw [hform, hha]
    exact hn
  have hres : ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) =
        (1 : ZMod 3) * e6dot (Cmul s) u := by
    intro u
    change Bform ha (Fintype.linearCombination (ZMod 3) h u) = _
    rw [one_mul]
    calc
      Bform ha (Fintype.linearCombination (ZMod 3) h u) =
          Bform (Fintype.linearCombination (ZMod 3) h u) ha := by
            rw [hform, hform, pair_comm]
      _ = e6dot (Cmul s) u := e6_Bform_H_H_eq_e6dot hpair hB u s
  exact e6_actual_insideU_membership_original hH hx hLNoncyclic hLI hpair hB hlin
    hgenB hinv hgenL hclosL hF hFlin hself rfl hxvec hres

theorem normalized_chart_inside_reflections_mem_literalL
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    (hLNoncyclic : GGLNoncyclicInput)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (φL : Fin 6 → MulAut ↥Bs)
    (hLI : LinearIndependent (ZMod 3) h)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i u v, Bform (ggLin (p := 3) ι (φL i) u)
      (ggLin (p := 3) ι (φL i) v) = Bform u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (chi : V ≃ₗ[ZMod 3] V7)
    (hchi : ∀ i, chi (h i) = e i.castSucc)
    (hform : ∀ u v, Bform u v = pair (chi u) (chi v))
    (lam : ZMod 3)
    (hxvec : ι (Additive.ofMul ⟨x, hx⟩) =
      lam • Fintype.linearCombination (ZMod 3) h r) :
    ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (chartConjHom chi ι) →
      reflPerm v hn ∈ CFSG.StandardType.E7F3.L := by
  intro v hn hv hmem
  obtain ⟨F, hF, hFchart⟩ := Subgroup.mem_map.mp hmem
  have hFL := normalized_inside_reflection_lift_mem_actualL hH hx hLNoncyclic ι
    Bform h α φL hLI hpair hB hlin hgenB hinv hgenL hclosL chi hchi hform
    lam hxvec hF v hn hv hFchart
  have hgenAction : ∀ i, chartConj chi ι (φL i) = s7 i.castSucc :=
    chartConj_phiL_eq_s7 chi ι φL h α Bform hchi hform hB hlin
  have hmap : (ggAutomizer L Bs).map (chartConjHom chi ι) =
      CFSG.StandardType.E7F3.L := by
    simpa only [CFSG.StandardType.E7F3.L, firstSixSet] using
      chartConj_map_closure_eq_literalL chi ι φL L hgenAction hclosL
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨F, hFL, hFchart⟩

end CFSG.StandardType.E6Seven

end

public section
namespace CFSG.StandardType.E6Seven

open CFSG.StandardType.E7F3
open Module

local instance lastCoordModule : Module F3 V7 := Pi.Function.module (Fin 7) F3 F3

theorem last_zero_mem_firstSix_span (x : V7) (hx : x (Fin.last 6) = 0) :
    x ∈ Submodule.span F3 (Set.range fun i : Fin 6 => e i.castSucc) := by
  have hsingle : ∀ c : Fin 6, e c.castSucc (Fin.last 6) = 0 := by
    intro c
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last c).symm 1
  have hdecomp : x = ∑ i : Fin 6, x i.castSucc • e i.castSucc := by
    funext j
    rw [Finset.sum_apply]
    by_cases hj : j = Fin.last 6
    · rw [hj]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hsum : (∑ c : Fin 6, x c.castSucc * e c.castSucc (Fin.last 6)) = 0 := by
        apply Finset.sum_eq_zero
        intro c _
        rw [hsingle c, mul_zero]
      rw [hx, hsum]
    · have hlt : j.val < 6 := by
        have hlt7 := j.isLt
        have hne : j.val ≠ 6 := by
          intro hv
          apply hj
          ext
          simpa using hv
        omega
      let i : Fin 6 := ⟨j.val, hlt⟩
      have hji : j = i.castSucc := by
        ext
        simp [i]
      rw [hji]
      rw [Finset.sum_eq_single i]
      · simp [e]
      · intro b _ hb
        simp [e, hb]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
  rw [hdecomp]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem chi_last_ne_zero_of_not_mem_span
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (h : Fin 6 → V)
    (hchi : ∀ i : Fin 6, chi (h i) = e i.castSucc)
    {w : V} (hw : w ∉ Submodule.span (ZMod 3) (Set.range h)) :
    chi w (Fin.last 6) ≠ 0 := by
  intro hlast
  have hmem : chi w ∈ Submodule.span F3 (Set.range fun i : Fin 6 => e i.castSucc) :=
    last_zero_mem_firstSix_span (chi w) hlast
  have hspan : Submodule.span F3 (Set.range fun i : Fin 6 => e i.castSucc) =
      Submodule.map (chi : V →ₗ[ZMod 3] V7) (Submodule.span F3 (Set.range h)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨h i, ⟨i, rfl⟩, hchi i⟩
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hchi i).symm⟩
  rw [hspan, Submodule.mem_map] at hmem
  obtain ⟨v, hv, hvw⟩ := hmem
  have hv' : v = w := chi.injective hvw
  exact hw (hv' ▸ hv)

end CFSG.StandardType.E6Seven
end

public section
namespace CFSG.StandardType.E6Seven

open CFSG.StandardType.E7F3
open CFSG.Assembly Module
open scoped Matrix

local instance witnessChartModule : Module F3 V7 := Pi.Function.module (Fin 7) F3 F3

theorem witnessChart_conj_eq_reflPerm
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    (F : MulAut ↥Bs) (w : V)
    (hact : ∀ v, ggLin (p := 3) ι F v = v - pair (chi w) (chi v) • w)
    (hn : norm (chi w) = 2) :
    chartConj chi ι F = reflPerm (chi w) hn := by
  apply Equiv.ext
  intro v
  rw [chartConj_apply, hact (chi.symm v), map_sub, map_smul,
    LinearEquiv.apply_symm_apply, reflPerm_apply, reflFun, pair_comm]

theorem e6_actual_seven_join_of_witness_chart
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    {Lgrp K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (S : Finset Λ)
    {Λa : Type} [Fintype Λa]
    (ee : Fin 6 ≃ Λ)
    (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hV : Λ ⊕ Λa → V)
    (αV : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hlin : ∀ o v, ggLin (p := 3) ι (φ o) v = v - αV o v • hV o)
    (hclosL : ggAutomizer Lgrp Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (Bb : LinearMap.BilinForm (ZMod 3) V)
    (hB : ∀ i : Fin 6, Bb (hV (Sum.inl (ee i))) = αV (Sum.inl (ee i)))
    (hpair_form : ∀ u v, Bb u v = pair (chi u) (chi v))
    (hchi_h : ∀ i : Fin 6, chi (hV (Sum.inl (ee i))) = e i.castSucc)
    (a0 : Λa)
    (ha_out : hV (Sum.inr a0) ∉ Submodule.span (ZMod 3)
      (Set.range fun i : Fin 6 => hV (Sum.inl (ee i))))
    (haction0 : ∀ v, ggLin (p := 3) ι (φ (Sum.inr a0)) v =
      v - pair (chi (hV (Sum.inr a0))) (chi v) • hV (Sum.inr a0))
    (hww0 : norm (chi (hV (Sum.inr a0))) = 2)
    (hInsideMap : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈
        (ggAutomizer Lgrp Bs ⊔ ggAutomizer K Bs).map (chartConjHom chi ι) →
      reflPerm v hn ∈ L)
    (hSadd : ∀ a : Λa, ∃ (v : V7) (hn : norm v = 2),
      chartConj chi ι (φ (Sum.inr a)) = reflPerm v hn) :
    CFSG.StandardType.GGWeylReflectionGroup 3
      (ggAutomizer Lgrp Bs ⊔ ggAutomizer K Bs) := by
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (ee i))
  let h' : Fin 6 → V := fun i => hV (Sum.inl (ee i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => αV (Sum.inl (ee i))
  let Aadd : Set (MulAut ↥Bs) := Set.range fun a : Λa => φ (Sum.inr a)
  let f : MulAut ↥Bs →* Equiv.Perm V7 := chartConjHom chi ι
  have hclosL' : ggAutomizer Lgrp Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ee.symm i, by simp [φL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ee i, rfl⟩
  have hlinL : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α' i v • h' i := by
    intro i v
    exact hlin (Sum.inl (ee i)) v
  have hgenAction : ∀ i : Fin 6, chartConj chi ι (φL i) = s7 i.castSucc :=
    chartConj_phiL_eq_s7 chi ι φL h' α' Bb hchi_h hpair_form hB hlinL
  have hAL : Subgroup.map f (ggAutomizer Lgrp Bs) = L := by
    simpa [L, firstSixSet] using
      chartConj_map_closure_eq_literalL chi ι φL Lgrp hgenAction hclosL'
  have hAaddAK : Aadd ⊆ ggAutomizer K Bs := by
    rintro x ⟨a, rfl⟩
    rw [hclosK]
    exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  have hAK_le : ggAutomizer K Bs ≤
      ggAutomizer Lgrp Bs ⊔ Subgroup.closure Aadd := by
    rw [hclosK]
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rcases hx with ⟨j, rfl⟩
      apply Subgroup.mem_sup_left
      rw [hclosL]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    · rcases hx with ⟨a, rfl⟩
      apply Subgroup.mem_sup_right
      exact Subgroup.subset_closure ⟨a, rfl⟩
  have himage : Subgroup.map f (ggAutomizer Lgrp Bs ⊔ ggAutomizer K Bs) =
      Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ (f '' Aadd)) := by
    apply le_antisymm
    · rw [Subgroup.map_sup]
      apply sup_le
      · rw [hAL]
        intro x hx
        exact Subgroup.subset_closure (Or.inl hx)
      · calc
          Subgroup.map f (ggAutomizer K Bs) ≤
              Subgroup.map f (ggAutomizer Lgrp Bs ⊔ Subgroup.closure Aadd) :=
            Subgroup.map_mono hAK_le
          _ = Subgroup.map f (ggAutomizer Lgrp Bs) ⊔
              Subgroup.map f (Subgroup.closure Aadd) := by
            rw [Subgroup.map_sup]
          _ = L ⊔ Subgroup.closure (f '' Aadd) := by
            rw [hAL, MonoidHom.map_closure]
          _ ≤ Subgroup.closure ((L : Set (Equiv.Perm V7)) ∪ (f '' Aadd)) := by
            apply sup_le
            · intro x hx
              exact Subgroup.subset_closure (Or.inl hx)
            · rw [Subgroup.closure_le]
              intro x hx
              exact Subgroup.subset_closure (Or.inr hx)
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hxL | hxS
      · have hxL' : x ∈ Subgroup.map f (ggAutomizer Lgrp Bs) := by
          rw [hAL]
          exact hxL
        exact Subgroup.map_mono (show ggAutomizer Lgrp Bs ≤
          ggAutomizer Lgrp Bs ⊔ ggAutomizer K Bs from le_sup_left) hxL'
      · rcases hxS with ⟨a, ha, rfl⟩
        have hmem : f a ∈ Subgroup.map f (ggAutomizer K Bs) :=
          Subgroup.mem_map.mpr ⟨a, hAaddAK ha, rfl⟩
        exact Subgroup.map_mono (show ggAutomizer K Bs ≤
          ggAutomizer Lgrp Bs ⊔ ggAutomizer K Bs from le_sup_right) hmem
  have hInsideClosure : ∀ (v : V7) (hn : norm v = 2), v 6 = 0 →
      reflPerm v hn ∈ Subgroup.closure
        ((L : Set (Equiv.Perm V7)) ∪ (f '' Aadd)) →
      reflPerm v hn ∈ L := by
    intro v hn hv hmem
    apply hInsideMap v hn hv
    rw [himage]
    exact hmem
  have hlast0 : chi (hV (Sum.inr a0)) (Fin.last 6) ≠ 0 :=
    chi_last_ne_zero_of_not_mem_span chi h' hchi_h ha_out
  have hS0 : chartConj chi ι (φ (Sum.inr a0)) =
      reflPerm (chi (hV (Sum.inr a0))) hww0 :=
    witnessChart_conj_eq_reflPerm chi ι (φ (Sum.inr a0)) (hV (Sum.inr a0)) haction0 hww0
  have hOutside : ∃ a : Λa, ∃ (v : V7) (hn : norm v = 2),
      chartConj chi ι (φ (Sum.inr a)) = reflPerm v hn ∧ v 6 ≠ 0 :=
    ⟨a0, chi (hV (Sum.inr a0)), hww0, hS0, hlast0⟩
  exact e6_actual_seven_join_of_sources_with_mixed_generation chi ι S ee φ
    hclosL hclosK hgenAction (by simpa [f] using hSadd) hInsideClosure hOutside

end CFSG.StandardType.E6Seven
end
