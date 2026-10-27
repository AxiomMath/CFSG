module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOrbitE7
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOrbitE8
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxWielandt
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxStruct
import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.FrameRoute

open Multiplicative CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem tmOrb_bounds_of_frame {G : Type} [Group G] {E : Subgroup G} {r N0 : ℕ}
    (φ : E ≃* Multiplicative (Fin r → ZMod 3))
    (refl dual : Fin r → (Fin r → ZMod 3) → Fin r → ZMod 3)
    (hpair : ∀ i c x, ∑ k, c k * refl i x k = ∑ k, dual i c k * x k)
    (hrefl2 : ∀ i x, refl i (refl i x) = x) (hdual2 : ∀ i c, dual i (dual i c) = c)
    (hdual0 : ∀ i, dual i 0 = 0)
    (hreflB : ∀ X : Set (Fin r → ZMod 3), (∀ i, ∀ x ∈ X, refl i x ∈ X) →
      ∀ {x}, x ∈ X → x ≠ 0 → N0 ≤ X.ncard)
    (hdualB : ∀ T : Set (Fin r → ZMod 3), (∀ i, ∀ c ∈ T, dual i c ∈ T) →
      ∀ {c}, c ∈ T → c ≠ 0 → N0 ≤ T.ncard)
    (hgen : ∀ i, ∃ g : Subgroup.normalizer (E : Set G), ∀ e : E,
      toAdd (φ (E.normalizerMonoidHom g e)) = refl i (toAdd (φ e))) :
    (∀ X : Set E, (∀ g : Subgroup.normalizer (E : Set G), ∀ x ∈ X, E.normalizerMonoidHom g x ∈ X) →
        ∀ x ∈ X, x ≠ 1 → N0 ≤ X.ncard) ∧
    (∀ P : Subgroup E → Prop, (∀ g : Subgroup.normalizer (E : Set G), ∀ K, P K →
        P (K.map (E.normalizerMonoidHom g).toMonoidHom)) →
      ∀ c, c ≠ 0 → P (tmKer φ c) → N0 ≤ {c | c ≠ 0 ∧ P (tmKer φ c)}.ncard) := by
  choose g hg using hgen
  have hinj : Function.Injective fun e : E => toAdd (φ e) :=
    toAdd.injective.comp φ.injective
  refine ⟨fun X hX x hx hx1 => ?_, fun P hP c hc0 hPc => ?_⟩
  · rw [← Set.ncard_image_of_injective X hinj]
    refine hreflB _ (fun i y hy => ?_) (Set.mem_image_of_mem _ hx) fun h => hx1 ?_
    · obtain ⟨x', hx', rfl⟩ := hy
      exact ⟨_, hX (g i) x' hx', hg i x'⟩
    · exact φ.injective (by rw [map_one]; exact toAdd_eq_zero.mp h)
  · refine hdualB _ (fun i c' hc' => ⟨fun h => hc'.1 ?_, ?_⟩) ⟨hc0, hPc⟩ hc0
    · rw [← hdual2 i c', h, hdual0]
    · have hK : tmKer φ (dual i c') =
          (tmKer φ c').map (E.normalizerMonoidHom (g i)).toMonoidHom := by
        ext e
        rw [Subgroup.mem_map_equiv, mem_tmKer, mem_tmKer]
        set e' := (E.normalizerMonoidHom (g i)).symm e
        have he : e = E.normalizerMonoidHom (g i) e' := by simp [e']
        rw [he, hg i e', ← hpair, hrefl2]
      rw [hK]
      exact hP (g i) _ hc'.2

theorem tmOrb_refl7_refl7 (i : Fin 7) (x : Fin 7 → ZMod 3) :
    tmOrb_refl7 i (tmOrb_refl7 i x) = x := by
  have hii : tmOrb_negCart7 i i = 1 := by fin_cases i <;> rfl
  have h3 : (3 : ZMod 3) = 0 := rfl
  funext k
  simp only [tmOrb_refl7, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hii]
  split_ifs with hk
  · subst hk
    linear_combination (∑ j, tmOrb_negCart7 j k * x j) * h3
  · ring

theorem tmOrb_pair7 (i : Fin 7) (c x : Fin 7 → ZMod 3) :
    ∑ k, c k * tmOrb_refl7 i x k = ∑ k, tmOrb_dual7 i c k * x k := by
  simp only [tmOrb_refl7, tmOrb_dual7, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul,
    Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tmOrb_negCart7_symm j i]
  ring

theorem tmOrb_negCart7_eq (i j : Fin 7) :
    tmOrb_negCart7 j i = -((Tag.cartan .E7 j i : ℤ) : ZMod 3) := by
  revert i j
  decide

theorem tmOrb_refl7_eq (i : Fin Tag.E7.rank) (x : Fin Tag.E7.rank → ZMod 3) :
    TableBExc.torusAct .E7 3 (simple .E7 i) x = tmOrb_refl7 i x := by
  rw [← TableBExc.torusRefl_eq_torusAct TableBExc.Three.cartan_symm_E7]
  simp only [TableBExc.torusRefl, tmOrb_refl7, sub_eq_add_neg]
  rw [← neg_smul, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tmOrb_negCart7_eq i j, neg_mul]

theorem tmOrb_bounds_E7
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 7) :
    ∃ φ : E ≃* Multiplicative (Fin 7 → ZMod 3),
      (∀ X : Set E,
        (∀ g : Subgroup.normalizer (E : Set G), ∀ x ∈ X, E.normalizerMonoidHom g x ∈ X) →
          ∀ x ∈ X, x ≠ 1 → 56 ≤ X.ncard) ∧
      (∀ P : Subgroup E → Prop, (∀ g : Subgroup.normalizer (E : Set G), ∀ K, P K →
          P (K.map (E.normalizerMonoidHom g).toMonoidHom)) →
        ∀ c, c ≠ 0 → P (tmKer φ c) → 56 ≤ {c | c ≠ 0 ∧ P (tmKer φ c)}.ncard) := by
  obtain ⟨π, φ, hπs, -, hπi⟩ := tmStruct_E7 G hEm hsimple E hE hcard
  refine ⟨φ, tmOrb_bounds_of_frame φ tmOrb_refl7 tmOrb_dual7 tmOrb_pair7 tmOrb_refl7_refl7
    tmOrb_dual7_dual7 tmOrb_dual7_zero (fun X hX _ hx hx0 => tmOrb_refl7_card X hX hx hx0)
    (fun T hT _ hc hc0 => tmOrb_dual7_card T hT hc hc0) fun i => ?_⟩
  obtain ⟨g, hg⟩ := hπs (simple .E7 i)
  refine ⟨g, fun e => ?_⟩
  have h := hπi g e
  rw [hg, ← ofAdd_toAdd (φ e), ExcWeylOuter.torusMulAut_apply] at h
  rw [h, toAdd_ofAdd]
  exact tmOrb_refl7_eq i _

theorem tmOrb_refl8_refl8 (i : Fin 8) (x : Fin 8 → ZMod 3) :
    tmOrb_refl8 i (tmOrb_refl8 i x) = x := by
  have hii : tmOrb_negCart8 i i = 1 := by fin_cases i <;> rfl
  have h3 : (3 : ZMod 3) = 0 := rfl
  funext k
  simp only [tmOrb_refl8, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hii]
  split_ifs with hk
  · subst hk
    linear_combination (∑ j, tmOrb_negCart8 j k * x j) * h3
  · ring

theorem tmOrb_pair8 (i : Fin 8) (c x : Fin 8 → ZMod 3) :
    ∑ k, c k * tmOrb_refl8 i x k = ∑ k, tmOrb_dual8 i c k * x k := by
  simp only [tmOrb_refl8, tmOrb_dual8, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul,
    Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tmOrb_negCart8_symm j i]
  ring

theorem tmOrb_negCart8_eq (i j : Fin 8) :
    tmOrb_negCart8 j i = -((Tag.cartan .E8 j i : ℤ) : ZMod 3) := by
  revert i j
  decide

theorem tmOrb_refl8_eq (i : Fin Tag.E8.rank) (x : Fin Tag.E8.rank → ZMod 3) :
    TableBExc.torusAct .E8 3 (simple .E8 i) x = tmOrb_refl8 i x := by
  rw [← TableBExc.torusRefl_eq_torusAct TableBExc.Three.cartan_symm_E8]
  simp only [TableBExc.torusRefl, tmOrb_refl8, sub_eq_add_neg]
  rw [← neg_smul, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tmOrb_negCart8_eq i j, neg_mul]

theorem tmOrb_bounds_E8
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 8) :
    ∃ φ : E ≃* Multiplicative (Fin 8 → ZMod 3),
      (∀ X : Set E,
        (∀ g : Subgroup.normalizer (E : Set G), ∀ x ∈ X, E.normalizerMonoidHom g x ∈ X) →
          ∀ x ∈ X, x ≠ 1 → 240 ≤ X.ncard) ∧
      (∀ P : Subgroup E → Prop, (∀ g : Subgroup.normalizer (E : Set G), ∀ K, P K →
          P (K.map (E.normalizerMonoidHom g).toMonoidHom)) →
        ∀ c, c ≠ 0 → P (tmKer φ c) → 240 ≤ {c | c ≠ 0 ∧ P (tmKer φ c)}.ncard) := by
  obtain ⟨π, φ, hπs, -, hπi⟩ := tmStruct_E8 G hEm hsimple E hE hcard
  refine ⟨φ, tmOrb_bounds_of_frame φ tmOrb_refl8 tmOrb_dual8 tmOrb_pair8 tmOrb_refl8_refl8
    tmOrb_dual8_dual8 tmOrb_dual8_zero (fun X hX _ hx hx0 => tmOrb_refl8_card X hX hx hx0)
    (fun T hT _ hc hc0 => tmOrb_dual8_card T hT hc hc0) fun i => ?_⟩
  obtain ⟨g, hg⟩ := hπs (simple .E8 i)
  refine ⟨g, fun e => ?_⟩
  have h := hπi g e
  rw [hg, ← ofAdd_toAdd (φ e), ExcWeylOuter.torusMulAut_apply] at h
  rw [h, toAdd_ofAdd]
  exact tmOrb_refl8_eq i _

end CFSG.StandardType.FrameRoute

end
