module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Nodes
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LieType.Chevalley.SimplyLacedCommutation
public import CFSG.RankThree.PartOne.S11c.G2Torus

public section

namespace CFSG.StandardType.SmallExc.E6Node

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.StandardType.TableBExc.E6Three CFSG.SeitzReduction

theorem le_normalizer_inf {G : Type} [Group G] {H N : Subgroup G}
    (hN : H ≤ Subgroup.normalizer (N : Set G)) :
    H ≤ Subgroup.normalizer ((N ⊓ H : Subgroup G) : Set G) := fun g hg => by
  have h1 := Subgroup.mem_normalizer_iff.mp (hN hg)
  have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
  exact and_congr (h1 x) (h2 x)

section Char

variable {L : Type} [Field L]

theorem iform_eq_sum_single_right (x v : Fin Tag.E6.rank → ℤ) :
    iform x v = ∑ j, v j * iform x (Pi.single j 1) := by
  have h : ∀ j, iform x (Pi.single j 1) = ∑ i, x i * Tag.E6.symmetrizedCartan i j := fun j => by
    simp [iform, Pi.single_apply]
  calc iform x v = ∑ i, ∑ j, x i * Tag.E6.symmetrizedCartan i j * v j := rfl
    _ = ∑ j, ∑ i, x i * Tag.E6.symmetrizedCartan i j * v j := Finset.sum_comm
    _ = ∑ j, v j * iform x (Pi.single j 1) := Finset.sum_congr rfl fun j _ => by
        rw [h j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

@[expose] def hChar (x : Fin Tag.E6.rank → ℤ) (l : Lˣ) : Fin Tag.E6.rank → Lˣ :=
  fun j => l ^ iform x (Pi.single j 1)

theorem rootChar_hChar (x v : Fin Tag.E6.rank → ℤ) (l : Lˣ) :
    rootChar (hChar x l) v = l ^ iform x v := by
  rw [iform_eq_sum_single_right x v, ← CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [hChar]
  rw [← zpow_mul, mul_comm]

theorem rootChar_mul_left (a b : Fin Tag.E6.rank → Lˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

end Char

section Certs

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def liftConj (n : ModGL .E6 (FiniteField.Extension K 2 2)) :
    adjointGroup .E6 K →* ModGL .E6 (FiniteField.Extension K 2 2) :=
  (MulAut.conj n⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))).comp (adjointGroup .E6 K).subtype)

theorem liftConj_apply (n : ModGL .E6 (FiniteField.Extension K 2 2)) (c : adjointGroup .E6 K) :
    liftConj n c = n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) c * n := by
  simp [liftConj, MulAut.conj_apply]

theorem liftConj_injective (n : ModGL .E6 (FiniteField.Extension K 2 2)) :
    Function.Injective (liftConj (K := K) n) := fun c c' h => by
  rw [liftConj_apply, liftConj_apply] at h
  exact Subtype.ext (baseChangeGL_injective _ (by simpa using h))

theorem centralizer_le_normalizer_comap {n : ModGL .E6 (FiniteField.Extension K 2 2)}
    (hn : n ∈ adjointGroup .E6 (FiniteField.Extension K 2 2)) {a : adjointGroup .E6 K}
    {χ : Fin Tag.E6.rank → (FiniteField.Extension K 2 2)ˣ} (ha : liftConj n a = rootDiagUnit .E6 χ)
    {R : Subgroup (ModGL .E6 (FiniteField.Extension K 2 2))}
    (hR : toralCentralizer .E6 (FiniteField.Extension K 2 2) χ ≤ Subgroup.normalizer (R : Set _)) :
    Subgroup.centralizer ({a} : Set (adjointGroup .E6 K)) ≤
      Subgroup.normalizer ((R.comap (liftConj n) : Subgroup (adjointGroup .E6 K)) : Set _) := by
  intro c hc
  refine Subgroup.le_normalizer_comap (liftConj n) (Subgroup.mem_comap.2 (hR ?_))
  have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine mem_toralCentralizer.2 ⟨?_, ?_⟩
  · rw [liftConj_apply]
    exact mul_mem (mul_mem (inv_mem hn) (baseChangeGL_mem_adjointGroup _ c.2)) hn
  · rw [← ha, ← map_inv, ← map_mul, ← map_mul, ← hca, mul_inv_cancel_right]

end Lift

section Roots

section RootSL2

variable {L : Type} [Field L]

theorem rootSL2_HSL_eq {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (l : Lˣ) :
    rootSL2 .E6 L β (HSL l) = rootDiagUnit .E6 (hChar β l) := by
  have h2 : iform β β = 2 := (dotProduct_mulVec_symmetrizedCartan_eq_sum β β).symm.trans
    (rootForm_self (Or.inr (Or.inl rfl)) hβ)
  refine rootSL2_HSL_eq_rootDiagUnit hβ (fun j => iform β (Pi.single j 1)) (fun δ _ => ?_) l
  rw [h2, Int.mul_ediv_cancel_left _ (by norm_num), iform_eq_sum_single_right]

theorem rootSL2_mem_rootSpan {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    {S : Set (Fin Tag.E6.rank → ℤ)} (h1 : β ∈ S) (h2 : -β ∈ S) (A : SL2 L) :
    rootSL2 .E6 L β A ∈ rootSpan .E6 L S := by
  have h : rootSL2 .E6 L β A ∈ rootRankOneGroup .E6 L β := ⟨A, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport .E6 L hβ).1] at h
  exact sup_le (le_iSup₂_of_le β h1 le_rfl : rootSubgroup .E6 L β ≤ rootSpan .E6 L S)
    (le_iSup₂_of_le (-β) h2 le_rfl : rootSubgroup .E6 L (-β) ≤ rootSpan .E6 L S) h

theorem rootSL2_mem_adjointGroup {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (A : SL2 L) :
    rootSL2 .E6 L β A ∈ adjointGroup .E6 L := by
  have h : rootSL2 .E6 L β A ∈ rootRankOneGroup .E6 L β := ⟨A, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport .E6 L hβ).1] at h
  exact sup_le (rootSubgroup_le_adjointGroup β) (rootSubgroup_le_adjointGroup (-β)) h

theorem conj_rootSL2_self (β : Fin Tag.E6.rank → ℤ) (P X : SL2 L) :
    (rootSL2 .E6 L β P)⁻¹ * rootSL2 .E6 L β X * rootSL2 .E6 L β P =
      rootSL2 .E6 L β (P⁻¹ * X * P) := by
  rw [map_mul, map_mul, map_inv]

end RootSL2

theorem baseChangeGL_uE6Two {K : Type} [Field K] [Finite K]
    [CharP K 2] (i : Fin 4) :
    baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
        ((uE6Two i : adjointGroup .E6 K) : ModGL .E6 K) =
      rootSL2 .E6 (FiniteField.Extension K 2 2) (bE6 i)
        (Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL 1 * vSL 1)) := by
  rw [coe_uE6Two_eq CharTwo.two_eq_zero i, baseChangeGL_rootSL2_of_charTwo _ (isRoot_bE6 i)]

section Commute

variable
  {L : Type} [Field L]

theorem rootSL2_bE6_commute {i j : Fin 4} (hij : i ≠ j) (A B : SL2 L) :
    Commute (rootSL2 .E6 L (bE6 i) A) (rootSL2 .E6 L (bE6 j) B) :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .E6 L (isRoot_bE6 i)
    (isRoot_bE6 j) (iform_bE6 i j hij).1 (not_isRoot_of_isRootB (isRootB_add_bE6 i j hij).1)
    (by rw [sub_eq_add_neg]; exact not_isRoot_of_isRootB (isRootB_add_bE6 i j hij).2.1)
    _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

theorem conj_rootSL2_bE6_of_ne {i j : Fin 4} (h : i ≠ j) (P X : SL2 L) :
    (rootSL2 .E6 L (bE6 j) P)⁻¹ * rootSL2 .E6 L (bE6 i) X * rootSL2 .E6 L (bE6 j) P =
      rootSL2 .E6 L (bE6 i) X := by
  rw [mul_assoc, (rootSL2_bE6_commute h X P).eq, inv_mul_cancel_left]

end Commute

end Roots

end Certs

theorem exists_inv_mul_map_uvSL_mul_eq_HSL {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) :
    ∃ (P : SL2 (FiniteField.Extension K 2 2)) (l : (FiniteField.Extension K 2 2)ˣ),
      orderOf l = 3 ∧
        P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL (1 : K) * vSL 1) * P = HSL l := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have := Fact.mk Nat.prime_three
  have hA1 : uSL (1 : K) * vSL 1 ≠ 1 := fun h => by
    have h00 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) h
    have huv : ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] :=
      coe_uvSL h2
    rw [huv] at h00
    simp at h00
  have hA : orderOf (uSL (1 : K) * vSL 1) = Nat.card K + 1 := by
    rw [hK]
    exact orderOf_eq_prime (uvSL_pow_three h2) hA1
  obtain ⟨l, P, -, hl1, hl3, hP⟩ := F4Pilot.exists_inv_mul_map_mul_eq_HSL hA
  have hl3' : l ^ 3 = 1 := by
    rw [hK] at hl3
    exact hl3
  exact ⟨P, l, orderOf_eq_prime hl3' hl1, hP⟩

end CFSG.StandardType.SmallExc.E6Node

end
