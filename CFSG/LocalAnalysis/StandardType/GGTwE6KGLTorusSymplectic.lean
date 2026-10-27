module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly CFSG.LieType.SteinbergBR.EvenSp

section Lift

variable {K : Type} [Field K]

private lemma det_swapGL [CharP K 2] :
    ((TwoThree.swapGL : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [Matrix.det_fin_two_of, mul_zero, one_mul, zero_sub, CharTwo.neg_eq]

private lemma det_mulSingle {m : ℕ} {i : Fin m} {g : GL (Fin 2) K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K).det = 1) (j : Fin m) :
    (((Pi.mulSingle i g : Fin m → GL (Fin 2) K) j : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same, hg]
  · rw [Pi.mulSingle_eq_of_ne hj, Units.val_one, Matrix.det_one]

private lemma det_extTorus [CharP K 2] {k : ℕ} (f : Fin k → Multiplicative (ZMod 3))
    (j : Fin (k + 1)) :
    ((TwoThree.extTorus f j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  simp only [TwoThree.extTorus, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · rw [TwoThree.tPow, TableBSymp.zmodPowHom_apply]
    exact det_of_mem_zpowers (Subgroup.npow_mem_zpowers _ _)
  · rw [Units.val_one, Matrix.det_one]

private lemma eq_one_of_mem_sp_scalars [CharP K 2] {m : ℕ} (hm : 1 ≤ m)
    {g : GL (Fin m ⊕ Fin m) K} (hg : g ∈ LargeEvenSpGroup K m)
    (hs : g ∈ LargeEvenScalars (Fin m ⊕ Fin m) K) : g = 1 := by
  have h : (⟨g, hg⟩ : CFSG.Open.StatedSp m K) ∈
      (CFSG.Open.StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (CFSG.Open.StatedSp m K) :=
    Subgroup.mem_subgroupOf.mpr hs
  rw [statedScalars_subgroupOf_statedSp hm, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

private lemma extTorus_mul_mulSingle_last [CharP K 2] {k : ℕ}
    (f : Fin k → Multiplicative (ZMod 3)) (v : GL (Fin 2) K) :
    TwoThree.extTorus f * Pi.mulSingle (Fin.last k) v =
      Pi.mulSingle (Fin.last k) v * TwoThree.extTorus f := by
  funext j
  simp only [Pi.mul_apply]
  by_cases hj : j = Fin.last k
  · subst hj
    have h : ¬ ((Fin.last k : Fin (k + 1)) : ℕ) < k := by simp
    simp only [TwoThree.extTorus, MonoidHom.coe_mk, OneHom.coe_mk, h, dite_false, one_mul,
      mul_one]
  · rw [Pi.mulSingle_eq_of_ne hj, one_mul, mul_one]

theorem ggTorusLift_three_symplectic [CharP K 2] (k : ℕ) :
    GGTorusLift 3 k (LargeEvenProj (LargeEvenSpGroup K (k + 1))) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hτH : ∀ f, planeHom (TwoThree.extTorus (K := K) (k := k) f) ∈
      LargeEvenSpGroup K (k + 1) := fun f => planeHom_mem_statedSp _ (det_extTorus f)
  have hXH : ∀ c : Multiplicative K, planeHom (Pi.mulSingle (Fin.last k)
      (TauCeti.transvectionHom h01 c)) ∈ LargeEvenSpGroup K (k + 1) := fun c =>
    planeHom_mem_statedSp _ (det_mulSingle (by rw [TauCeti.transvectionHom_apply,
      TauCeti.coe_transvectionUnit, Matrix.det_transvection_of_ne _ _ h01]))
  have hbasis : ∀ i, TableBSymp.torusBasis
      (planeHom.comp (TwoThree.extTorus (K := K) (k := k))) i =
        planeHom (Pi.mulSingle i.castSucc tGL) := fun i => by
    rw [TableBSymp.torusBasis, MonoidHom.comp_apply, TwoThree.extTorus_mulSingle]
  refine TableBSymp.ggTorusLift_of_matrixTorus Nat.prime_three (by norm_num)
    (planeHom.comp TwoThree.extTorus) hτH (fun f hf => ?_) (fun i j => ?_)
    (planeHom.comp ((MonoidHom.mulSingle (fun _ => GL (Fin 2) K) (Fin.last k)).comp
      (TauCeti.transvectionHom h01))) hXH (fun hs => ?_) (fun c => ?_) (fun f c => ⟨c, ?_⟩)
  · have h1 := eq_one_of_mem_sp_scalars (Nat.succ_pos k) (hτH f) hf
    exact TwoThree.extTorus_injective
      ((planeHom_injective (h1.trans (map_one _).symm)).trans (map_one _).symm)
  · refine ⟨planeHom (Pi.mulSingle i.castSucc TwoThree.swapGL),
      planeHom_mem_statedSp _ (det_mulSingle det_swapGL), ?_, fun hji => ?_⟩
    · rw [hbasis, ← map_inv, ← map_mul, ← map_mul, ← Pi.mulSingle_inv, ← Pi.mulSingle_mul,
        ← Pi.mulSingle_mul, TwoThree.swapGL_conj_tGL, Pi.mulSingle_inv, map_inv]
    · have hne : i.castSucc ≠ j.castSucc := fun h => hji (Fin.castSucc_injective _ h).symm
      rw [hbasis, ← map_inv, ← map_mul, ← map_mul,
        (Pi.mulSingle_commute (f := fun _ => GL (Fin 2) K) hne TwoThree.swapGL tGL).eq,
        mul_inv_cancel_right]
  · have h1 := eq_one_of_mem_sp_scalars (Nat.succ_pos k) (hXH _) hs
    have h2 := congrFun (planeHom_injective (h1.trans (map_one _).symm)) (Fin.last k)
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h2
    have h3 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h2
    simp [TauCeti.transvectionHom_apply, TauCeti.coe_transvectionUnit, Matrix.transvection] at h3
  · rw [← map_pow]
    have hc2 : c ^ 2 = 1 := by
      rw [← ofAdd_toAdd c, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [hc2, map_one]
  · simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
    rw [← map_inv, ← map_mul, ← map_mul, extTorus_mul_mulSingle_last, mul_inv_cancel_right]

end Lift

theorem largeEvenLabelAll_torusLift_symplectic_threeFive {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (h6 : 6 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h6
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  intro Q hQ
  rcases htag with rfl | rfl <;>
  · dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusLift_mono Nat.prime_three (ggTorusLift_three_symplectic (K := K) k) (by omega)⟩

end CFSG.StandardType.SCFourCover

end
