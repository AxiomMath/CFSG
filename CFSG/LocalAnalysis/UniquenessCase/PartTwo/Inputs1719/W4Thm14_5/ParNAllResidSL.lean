module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ProdPCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.LeviBlock

section TwoBlocks

variable {ι : Type} {M : ι → Type} [∀ i, Group (M i)]

private def piProdHom (B : ∀ i, Subgroup (M i)) (j₀ j₁ : ι) :
    ↥(Subgroup.pi Set.univ B) →* ↥(B j₀) × ↥(B j₁) where
  toFun x := (⟨(x : ∀ i, M i) j₀, (Subgroup.mem_pi _).mp x.2 j₀ (Set.mem_univ _)⟩,
    ⟨(x : ∀ i, M i) j₁, (Subgroup.mem_pi _).mp x.2 j₁ (Set.mem_univ _)⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem piProdHom_bijective {B : ∀ i, Subgroup (M i)} {j₀ j₁ : ι} (hj : j₀ ≠ j₁)
    (hB : ∀ j, j ≠ j₀ → j ≠ j₁ → B j = ⊥) : Function.Bijective (piProdHom B j₀ j₁) := by
  classical
  refine ⟨fun x y hxy => Subtype.ext (funext fun j => ?_), fun p => ?_⟩
  · by_cases h0 : j = j₀
    · subst h0
      exact congrArg (fun q => (q.1 : M j)) hxy
    by_cases h1 : j = j₁
    · subst h1
      exact congrArg (fun q => (q.2 : M j)) hxy
    have hx := (Subgroup.mem_pi _).mp x.2 j (Set.mem_univ _)
    have hy := (Subgroup.mem_pi _).mp y.2 j (Set.mem_univ _)
    rw [hB j h0 h1, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · refine ⟨⟨Pi.mulSingle j₀ (p.1 : M j₀) * Pi.mulSingle j₁ (p.2 : M j₁),
      mul_mem ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => p.1.2)
        ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => p.2.2)⟩, ?_⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change Pi.mulSingle j₀ (p.1 : M j₀) j₀ * Pi.mulSingle j₁ (p.2 : M j₁) j₀ = p.1
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hj, mul_one]
    · change Pi.mulSingle j₀ (p.1 : M j₀) j₁ * Pi.mulSingle j₁ (p.2 : M j₁) j₁ = p.2
      rw [Pi.mulSingle_eq_of_ne hj.symm, Pi.mulSingle_eq_same, one_mul]

theorem nonempty_bar2_hinf_equiv_of_leviHom_mulSingle_two {G : Type} [Group G] [Finite G]
    (P : Subgroup G) (β : ↥P →* ∀ i, M i) (hker : IsPGroup 2 ↥β.ker) {j₀ j₁ : ι}
    (hj : j₀ ≠ j₁) (B : ∀ i, Subgroup (M i)) (hB : ∀ j, j ≠ j₀ → j ≠ j₁ → B j = ⊥)
    (hSR : Subgroup.pi Set.univ B ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ B) {T₀ T₁ : Type} [Group T₀] [Group T₁]
    (e₀ : ↥(B j₀) ≃* T₀) (e₁ : ↥(B j₁) ≃* T₁) (hperf₀ : Group.IsPerfect T₀)
    (hperf₁ : Group.IsPerfect T₁) (hT₀ : CFSG.pCore 2 T₀ = ⊥) (hT₁ : CFSG.pCore 2 T₁ = ⊥) :
    Nonempty (Bar2 (Hinf P) ≃* T₀ × T₁) :=
  KTabD.nonempty_bar2_hinf_equiv_of_leviHom_of_equiv P β hker _ hSR hcomm
    ((MulEquiv.ofBijective _ (piProdHom_bijective hj hB)).trans (e₀.prodCongr e₁))
    (KTabD.isPerfect_prod hperf₀ hperf₁) (KTabD.pCore_prod_eq_bot hT₀ hT₁)

end TwoBlocks

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pCore_specialLinearGroup_eq_bot (m : ℕ) :
    CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin m) K) = ⊥ := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m K
  have h := CFSG.pCore_map_iso 2 e
  rw [KOrdNat.pCore_statedSL_eq_bot 2 m] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

omit [Finite K] [CharP K 2] in
private theorem linBlockSL_eq_bot {n : ℕ} {I : Set ℕ} {a : Fin n} (h : linBlockLen n I a < 2) :
    linBlockSL K n I a = ⊥ := by
  have := subsingleton_specialLinear_of_lt_two (K := K) h
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨A, rfl⟩
  rw [Subsingleton.elim A 1, map_one]

omit [Finite K] [CharP K 2] in
private theorem linBlockSL_eq_bot_of_not_start {n : ℕ} {I : Set ℕ} {a : Fin n}
    (ha : ¬ ((a : ℕ) = 0 ∨ (a : ℕ) ∈ I)) : linBlockSL K n I a = ⊥ :=
  linBlockSL_eq_bot (by rw [linBlockLen_of_not_start ha]; omega)

private theorem linBlockLen_eq {n : ℕ} {I : Set ℕ} {a : Fin n} {m : ℕ} (h : (a : ℕ) + m ≤ n)
    (ha : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I) (hb : (a : ℕ) + m = n ∨ (a : ℕ) + m ∈ I)
    (hno : ∀ c ∈ I, ¬ ((a : ℕ) < c ∧ c < a + m)) (hm : 1 ≤ m) : linBlockLen n I a = m :=
  (linBlockLen_eq_of_maxBlock a.isLt h ha hb hno hm).symm

private noncomputable def linBlockSLEquiv {n : ℕ} {I : Set ℕ} {a : Fin n} {k : ℕ}
    (h : linBlockLen n I a = k) :
    ↥(linBlockSL K n I a) ≃* Matrix.SpecialLinearGroup (Fin k) K :=
  (slEquivToGLRange (linBlockLen n I a)).symm.trans
    (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) h)

theorem nonempty_bar2_hinf_slFlagStab_four_two (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K {2})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  have h0 : linBlockLen 4 {2} 0 = 2 :=
    linBlockLen_eq (by simp) (Or.inl rfl) (Or.inr (by simp))
      (fun c hc => by rw [Set.mem_singleton_iff] at hc; simp [hc]) (by norm_num)
  have h2 : linBlockLen 4 {2} 2 = 2 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inl (by simp))
      (fun c hc => by rw [Set.mem_singleton_iff] at hc; simp [hc]) (by norm_num)
  have hB : ∀ j, j ≠ 0 → j ≠ 2 → linBlockSL K 4 {2} j = ⊥ := by
    intro j hj0 hj2
    refine linBlockSL_eq_bot_of_not_start ?_
    rintro (h | h)
    · exact hj0 (Fin.ext h)
    · exact hj2 (Fin.ext (by simpa using h))
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  exact nonempty_bar2_hinf_equiv_of_leviHom_mulSingle_two _ (linLeviHom K 4 {2})
    (isPGroup_ker_linLeviHom (by norm_num)) (by decide) (linBlockSL K 4 {2}) hB
    pi_le_range_linLeviHom commutator_range_linLeviHom_le (linBlockSLEquiv h0)
    (linBlockSLEquiv h2) hperf hperf (pCore_specialLinearGroup_eq_bot 2)
    (pCore_specialLinearGroup_eq_bot 2)

theorem nonempty_bar2_hinf_slFlagStab_four_three :
    Nonempty (Bar2 (Hinf (LinearFlag.flagStabilizer 4 K {3})) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) := by
  have h0 : linBlockLen 4 {3} 0 = 3 :=
    linBlockLen_eq (by simp) (Or.inl rfl) (Or.inr (by simp))
      (fun c hc => by rw [Set.mem_singleton_iff] at hc; simp [hc]) (by norm_num)
  have h3 : linBlockLen 4 {3} 3 = 1 :=
    linBlockLen_eq (by simp) (Or.inr (by simp)) (Or.inl (by simp))
      (fun c hc => by rw [Set.mem_singleton_iff] at hc; simp [hc]) le_rfl
  have hB : ∀ j, j ≠ 0 → linBlockSL K 4 {3} j = ⊥ := by
    intro j hj0
    by_cases hj3 : j = 3
    · subst hj3
      exact linBlockSL_eq_bot (by rw [h3]; norm_num)
    refine linBlockSL_eq_bot_of_not_start ?_
    rintro (h | h)
    · exact hj0 (Fin.ext h)
    · exact hj3 (Fin.ext (by simpa using h))
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (linLeviHom K 4 {3})
    (isPGroup_ker_linLeviHom (by norm_num)) 0 (linBlockSL K 4 {3}) hB (fun y hy => ?_)
    commutator_range_linLeviHom_le (linBlockSLEquiv h0)
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl)
    (pCore_specialLinearGroup_eq_bot 3)
  exact pi_le_range_linLeviHom ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
