module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTypeDet
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces


private theorem l02qu5_isDiag_mul_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A B : Matrix ι ι F} (hA : A.IsDiag) (hB : B.IsDiag) : A * B = B * A := by
  rw [← (Matrix.isDiag_iff_diagonal_diag A).mp hA, ← (Matrix.isDiag_iff_diagonal_diag B).mp hB,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private theorem l02qu5_conj_diag_comm {d : ℕ} {K : Type} [Field K] {P M N : GL (Fin d) K}
    (hM : ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag)
    (hN : ((P⁻¹ * N * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag) :
    M * N = N * M := by
  have hconj : (P⁻¹ * M * P : GL (Fin d) K) * (P⁻¹ * N * P) =
      (P⁻¹ * N * P) * (P⁻¹ * M * P) := by
    apply Units.ext
    simp only [Units.val_mul]
    exact l02qu5_isDiag_mul_comm hM hN
  calc M * N = P * ((P⁻¹ * M * P) * (P⁻¹ * N * P)) * P⁻¹ := by group
    _ = P * ((P⁻¹ * N * P) * (P⁻¹ * M * P)) * P⁻¹ := by rw [hconj]
    _ = N * M := by group

theorem toralUni_of_card {d m p : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (hdq : ¬(d = 3 ∧ 2 ^ m = 2))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))))}
    (hE : IsElemAbelian p E)
    (hEI : ∀ a ∈ E, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))) (LargeEvenGUSet (Fin d) K (2 ^ m)))
    (hcard : p ^ (d / p + 2) ≤ Nat.card E) : ToralUni _ E := by
  classical
  unfold ToralUni
  intro d' m' K' _ _ hK' θ
  have hm' : 1 ≤ m' := by
    by_contra h
    have h0 : m' = 0 := by omega
    subst h0
    have h2 : 2 ≤ Nat.card K' := by
      have := Finite.one_lt_card (α := K')
      omega
    rw [hK'] at h2
    norm_num at h2
  have hUF' : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m' K' :=
    unitaryFieldData_of_card hm' hK'
  obtain ⟨hd', hm'eq⟩ := kgLangS1A_psu_typeDet (d := d) (d₁ := d') (m₀ := m) (m := m')
    (F₀ := K) (E := K') hd hm hK hdq hUF' θ
  subst d'
  subst m'
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K :=
    unitaryFieldData_of_card hm hK
  have hdq' : (d, 2 ^ m) ≠ (3, 2) := by
    intro h
    exact hdq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  obtain ⟨P, hP, hframe⟩ :=
    TableBUD.exists_unitary_frame hUF hK hd hdq' hp hpq hE hEI hcard
  rw [isMulCommutative_iff]
  intro g' h'
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp g'.2)
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp h'.2)
  obtain ⟨Ma, hMa, hdiag_a, hproj_a⟩ := hframe a ha
  obtain ⟨Mb, hMb, hdiag_b, hproj_b⟩ := hframe b hb
  let MaN : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    ⟨Ma, TableBUE.gu_subset_normalizer hUF hMa⟩
  let MbN : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    ⟨Mb, TableBUE.gu_subset_normalizer hUF hMb⟩
  have hproj_a' : a = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) MaN := hproj_a
  have hproj_b' : b = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) MbN := hproj_b
  have hMaMb : Ma * Mb = Mb * Ma := l02qu5_conj_diag_comm hdiag_a hdiag_b
  have hgh : (MaN : GL (Fin d) K) * MbN = MbN * MaN := by
    simpa using hMaMb
  have hM : ∀ x, θ.symm (TableB.projConj (LargeEvenSUGroup (Fin d) K' (2 ^ m)) g'.1 x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) MaN (θ.symm x) := by
    intro x
    rw [haeq.symm]
    show θ.symm (θ (a (θ.symm x))) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) MaN (θ.symm x)
    rw [MulEquiv.symm_apply_apply, hproj_a']
  have hN : ∀ x, θ.symm (TableB.projConj (LargeEvenSUGroup (Fin d) K' (2 ^ m)) h'.1 x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) MbN (θ.symm x) := by
    intro x
    rw [hbeq.symm]
    show θ.symm (θ (b (θ.symm x))) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) MbN (θ.symm x)
    rw [MulEquiv.symm_apply_apply, hproj_b']
  have htransfer := kgLangS1A_uni_commute_transfer (d := d) (m := m) (F₀ := K') (E := K)
    hd hm hK' hK hdq θ.symm hM hN hgh
  exact Subtype.ext (Subtype.ext htransfer)

theorem toralUni_of_rank {d m p : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (hdq : ¬(d = 3 ∧ 2 ^ m = 2))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1) (hd63 : ¬(d = 6 ∧ p = 3))
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))))}
    (hE : IsElemAbelian p E)
    (hEI : ∀ a ∈ E, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))) (LargeEvenGUSet (Fin d) K (2 ^ m)))
    (hr : p ^ (d - 3) ≤ Nat.card E) (h3 : p ^ 3 ≤ Nat.card E) : ToralUni _ E := by
  apply toralUni_of_card hd hm hdq hK hp hpq hE hEI
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    have h2dvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have hmod : (2 ^ m + 1) % 2 = 1 := by
      rw [Nat.add_mod]
      simp [Nat.dvd_iff_mod_eq_zero.mp h2dvd]
    have h0 : (2 ^ m + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hpq
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hk : d / p + 2 ≤ d - 3 ∨ d / p + 2 ≤ 3 := by
    by_cases hp3' : p = 3
    · subst hp3'
      have : d ≠ 6 := fun h6 => hd63 ⟨h6, rfl⟩
      omega
    · have h4 : d / p ≤ d / 4 := Nat.div_le_div_left (by omega) (by norm_num)
      omega
  rcases hk with hk | hk
  · exact (Nat.pow_le_pow_right hp.pos hk).trans hr
  · exact (Nat.pow_le_pow_right hp.pos hk).trans h3

end CFSG.StandardType
