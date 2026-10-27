module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdRefl
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

theorem unitDvd_automizer_le_closure {K : Type} [Field K] [Finite K] {n d p : ℕ} {L' : Type}
    [Group L'] [Finite L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hd : 5 ≤ d) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      Subgroup.closure (ggTorusReflSet p A) := by
  classical
  have hN : ∀ σ, MulAut.conj (φ (permSU hM.field σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    unitDvd_conj_perm_mem_normalizer hM hp hpq (by omega) hA.2 hsc hdiag
  have hmul : ∀ σ τ : Equiv.Perm (Fin d),
      ggConjAut A (hN (σ * τ)) = ggConjAut A (hN σ) * ggConjAut A (hN τ) := by
    intro σ τ
    refine MulEquiv.ext fun b => Subtype.ext ?_
    simp only [ggConjAut_apply, MulAut.mul_apply, UnitAct.permSU_mul, map_mul]
    group
  have hone : ggConjAut A (hN 1) = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    simp [ggConjAut_apply, UnitAct.permSU_one]
  have hperm : ∀ π : Equiv.Perm (Fin d),
      ggConjAut A (hN π) ∈ Subgroup.closure (ggTorusReflSet p A) := by
    intro π
    refine Equiv.Perm.swap_induction_on π ?_ ?_
    · rw [hone]
      exact Subgroup.one_mem _
    · intro f x y hxy ih
      rw [hmul]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure
        (unitDvd_swap_mem_reflSet hM hp hp2 hpq (by omega) hA hsc hdiag hN hxy)) ih
  intro v hv
  obtain ⟨c, ⟨m, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
  obtain ⟨w, ⟨π, rfl⟩, hfix⟩ := UnitAct.exists_weyl_fix hM hK hp hp2 hpq (by omega) hA hsc hdiag hcN
  obtain ⟨u, hu⟩ : ∃ u : L', u = m * (φ (permSU hM.field π))⁻¹ := ⟨_, rfl⟩
  have hfixu : ∀ a ∈ A, a u = u := fun a ha => by
    rw [hu]
    exact hfix a ha
  have hm : m = u * φ (permSU hM.field π) := by rw [hu]; group
  have hcomm : ∀ b' ∈ A, MulAut.conj u * b' = b' * MulAut.conj u := by
    intro b' hb'
    ext x
    have h := hfixu b' hb'
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]
  have hv' : v = ggConjAut A (hN π) := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hvc b, ggConjAut_apply, hm, map_mul]
    have hb' : MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
        (MulAut.conj (φ (permSU hM.field π)))⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hN π) b).mp b.2
    calc MulAut.conj u * MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
          (MulAut.conj u * MulAut.conj (φ (permSU hM.field π)))⁻¹
        = MulAut.conj u * (MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
            (MulAut.conj (φ (permSU hM.field π)))⁻¹) * (MulAut.conj u)⁻¹ := by group
      _ = (MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
            (MulAut.conj (φ (permSU hM.field π)))⁻¹) * MulAut.conj u * (MulAut.conj u)⁻¹ := by
          rw [hcomm _ hb']
      _ = _ := mul_inv_cancel_right _ _
  rw [hv']
  exact hperm π

theorem ggTorusReflGenW_unitary_dvd
    {n d p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGTorusReflGenW p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAab, hAI, hr, h3, hsc⟩ := hA
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hrank : ggUnitaryTorusRank p d = d - 3 := by simp [ggUnitaryTorusRank, hpd]
  rw [hrank] at hr
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn hd hp hpq hpd
    (unitaryUniversalCover_holds n d K hK hd hdnd) hψ hker hperf hAab hAI hcard
  exact unitDvd_automizer_le_closure ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩ hK hp
    hp2 hpq hd hAab hsc hdiag

theorem recipeUnitary_dvd_reflGenW
    {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ GGTorusLift p (ggUnitaryTorusRank p d) R ∧
        GGTorusReflGenW p (ggUnitaryTorusRank p d) R I := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq,
    ggTorusReflGenW_unitary_dvd hK hn hd hp hpq hpd hnd⟩

end CFSG.StandardType
