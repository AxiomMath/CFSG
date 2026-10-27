module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypEigen
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical2

theorem card_le_pow_statedProj_statedSU_of_dvd_sub_one {n r p : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 n F) (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) (E : Subgroup (StatedProj (StatedSU (2 * r) (2 ^ n) F)))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ r := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite F := h.finite
  let N : Subgroup (StatedSU (2 * r) (2 ^ n) F) :=
    (StatedScalars (Fin (2 * r)) F).subgroupOf (StatedSU (2 * r) (2 ^ n) F)
  haveI hNn : N.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : (StatedScalars (Fin (2 * r)) F).Normal)
      (StatedSU (2 * r) (2 ^ n) F)
  have hNcard : Nat.card N ∣ 2 ^ n + 1 :=
    card_scalars_statedSU_dvd h.card_eq_sq (by omega)
  have hN : ¬ p ∣ Nat.card N := by
    intro hdiv
    have hpadd : p ∣ 2 ^ n + 1 := hdiv.trans hNcard
    have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpadd hpq
    have h3 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h3] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  obtain ⟨S, -, hS, hScard⟩ := exists_elemAbelian_lift N hN hE
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 0) h
  let e : StatedSU (2 * r) (2 ^ n) F ≃* hypSU h r 0 := (hypTransport h hR).symm
  let S' : Subgroup (hypSU h r 0) := S.map e.toMonoidHom
  have hS'card : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective e.injective
  have hS' : IsElemAbelian p S' := hS.map e.toMonoidHom
  have hbound : Nat.card S' ≤ p ^ r := card_le_pow_hypSU h hp hp2 hpq S' hS'
  calc Nat.card E = Nat.card S := hScard.symm
    _ = Nat.card S' := hS'card.symm
    _ ≤ p ^ r := hbound

private theorem conj_injective_of_center_eq_bot {G : Type*} [Group G]
    (h : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro x y hxy
  have hz : x * y⁻¹ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : MulAut.conj (x * y⁻¹) g = g := by rw [h1]; rfl
    rw [MulAut.conj_apply] at h2
    have h3 : (x * y⁻¹) * g = g * (x * y⁻¹) := by
      calc (x * y⁻¹) * g = (x * y⁻¹) * g * (x * y⁻¹)⁻¹ * (x * y⁻¹) := by group
        _ = g * (x * y⁻¹) := by rw [h2]
    exact h3.symm
  rw [h, Subgroup.mem_bot] at hz
  exact mul_inv_eq_one.mp hz

theorem card_le_sq_of_subset_matConj_GU_four {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))))}
    (hE : IsElemAbelian p E)
    (hEI : (E : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenGUSet (Fin 4) K (2 ^ n))) :
    Nat.card E ≤ p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hK
  have hInn : E ≤ LargeEvenInnSet (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) := by
    intro a ha
    exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_matConj_SU_sub_inn (E := K) (q := 2 ^ n)
      (f := n) rfl hn hK (hEI ha)
  have hcenter : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) = ⊥ :=
    center_statedProj_statedSU_eq_bot hK (le_refl 4)
  have hinj : Function.Injective (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))) :=
    conj_injective_of_center_eq_bot hcenter
  let Esub : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) :=
    E.comap (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))))
  have hEmap : Esub.map (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))) = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hInn
  have hEcard : Nat.card Esub = Nat.card E := by
    rw [← hEmap, Subgroup.card_map_of_injective hinj]
  have hEsub : IsElemAbelian p Esub := hE.comap hinj
  have hbound : Nat.card Esub ≤ p ^ 2 :=
    card_le_pow_statedProj_statedSU_of_dvd_sub_one (r := 2)
      (h := TableBU.unitaryFieldData_of_card hK hn) (by norm_num) hp hp2 hpq Esub hEsub
  calc Nat.card E = Nat.card Esub := hEcard.symm
    _ ≤ p ^ 2 := hbound

end CFSG.StandardType

end
