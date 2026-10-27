module

public import CFSG.LocalAnalysis.StandardType.GGSporKM5T
public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Five
import CFSG.LocalAnalysis.StandardType.GGSporKM5CQ
import CFSG.LocalAnalysis.StandardType.GGSporKCommDataDich
import CFSG.LocalAnalysis.StandardType.GGSporKCommDataF
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFrontier
public import CFSG.RankThree.CentralExtension.PrimeToPKernel
public import CFSG.RankThree.Native.FiveLocalAction
public import CFSG.RankThree.Native.FiveLocalForms
public import CFSG.RankThree.Native.FiveLocalInterface

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Assembly CFSG.Blueprint CFSG.Monster.Generated CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271

private theorem gkm5g_Q_le :
    Subgroup.closure (Set.range qFiveB) ≤ Subgroup.closure (Set.range fiveGenG ∪ {m5tB}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact Subgroup.subset_closure (Or.inl ⟨⟨i.val + 2, by omega⟩, rfl⟩)

private theorem gkm5g_S_le :
    Subgroup.closure (Set.range fiveGenG) ≤ Subgroup.closure (Set.range fiveGenG ∪ {m5tB}) :=
  Subgroup.closure_mono Set.subset_union_left

private theorem gkm5g_le_normalizer [Finite Gmat]
    (hS : Subgroup.closure (Set.range fiveGenG) ≤
      Subgroup.normalizer (Subgroup.closure (Set.range qFiveB) : Set Gmat))
    (hb : ∀ g ∈ Subgroup.closure (Set.range qFiveB),
      m5tB⁻¹ * g * m5tB ∈ Subgroup.closure (Set.range qFiveB)) :
    Subgroup.closure (Set.range fiveGenG ∪ {m5tB}) ≤
      Subgroup.normalizer (Subgroup.closure (Set.range qFiveB) : Set Gmat) := by
  intro l hl
  apply mem_normalizer_of_conj
  refine conj_mem_of_mem_closure ?_ hl
  rintro s (⟨i, rfl⟩ | rfl) g hg
  · have hs : fiveGenG i ∈
        Subgroup.normalizer (Subgroup.closure (Set.range qFiveB) : Set Gmat) :=
      hS (Subgroup.subset_closure ⟨i, rfl⟩)
    exact (Subgroup.mem_normalizer_iff''.mp hs g).mp hg
  · exact hb g hg

private theorem gkm5g_central
    (hS : Subgroup.closure (Set.range fiveGenG) ≤ Subgroup.centralizer ({xFiveB} : Set Gmat))
    (hbx : m5tB * xFiveB = xFiveB * m5tB) :
    ∀ l ∈ Subgroup.closure (Set.range fiveGenG ∪ {m5tB}),
      l * xFiveB * l⁻¹ ∈ Subgroup.zpowers xFiveB := by
  have hL : Subgroup.closure (Set.range fiveGenG ∪ {m5tB}) ≤
      Subgroup.centralizer ({xFiveB} : Set Gmat) := by
    rw [Subgroup.closure_le]
    rintro s (⟨i, rfl⟩ | rfl)
    · exact hS (Subgroup.subset_closure ⟨i, rfl⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hbx
  intro l hl
  have hc : l * xFiveB = xFiveB * l :=
    Subgroup.mem_centralizer_singleton_iff.mp (hL hl)
  rw [mul_inv_eq_iff_eq_mul.mpr hc]
  exact Subgroup.mem_zpowers xFiveB

private theorem gkm5g_conj_q (hD : CommData 5 qFiveB xFiveB mFiveB)
    (hconj : ∀ j : Fin 6, m5tB⁻¹ * fiveGenG ⟨j.val + 2, by omega⟩ * m5tB =
      (List.ofFn fun k : Fin 6 => fiveGenG ⟨k.val + 2, by omega⟩ ^ (m5tMat j k).val).prod *
        xFiveB ^ m5tC j) :
    ∀ i : Fin 6, m5tB⁻¹ * qFiveB i * m5tB ∈ Subgroup.closure (Set.range qFiveB) := by
  intro i
  rw [show qFiveB i = fiveGenG ⟨i.val + 2, by omega⟩ from rfl]
  rw [hconj i]
  refine mul_mem (list_prod_mem ?_) (pow_mem hD.mem_z _)
  intro a ha
  rw [List.mem_ofFn'] at ha
  obtain ⟨k, rfl⟩ := ha
  apply pow_mem
  exact Subgroup.subset_closure ⟨k, rfl⟩

private theorem gkm5g_actMat_pow (hD : CommData 5 qFiveB xFiveB mFiveB)
    (hb : ∀ i : Fin 6, m5tB⁻¹ * qFiveB i * m5tB ∈ Subgroup.closure (Set.range qFiveB))
    (hR : CommData.actMat 5 qFiveB xFiveB mFiveB m5tB = m5tMat) (k : ℕ) :
    CommData.actMat 5 qFiveB xFiveB mFiveB (m5tB ^ k) = m5tMat ^ k := by
  have hx : ∀ g ∈ Subgroup.closure (Set.range qFiveB),
      m5tB⁻¹ * g * m5tB ∈ Subgroup.closure (Set.range qFiveB) :=
    fun g hg => CommData.conj_mem hb hg
  induction k with
  | zero => simp [hD.actMat_one]
  | succ k ih =>
    have hb' : ∀ i : Fin 6, (m5tB ^ k)⁻¹ * qFiveB i * m5tB ^ k ∈
        Subgroup.closure (Set.range qFiveB) := fun i =>
      conj_pow_mem (Q := Subgroup.closure (Set.range qFiveB)) (x := m5tB) hx k
        (Subgroup.subset_closure ⟨i, rfl⟩)
    rw [pow_succ, hD.actMat_mul hb' hb, ih, hR, pow_succ]

private theorem gkm5g_dich [Finite Gmat] (hD : CommData 5 qFiveB xFiveB mFiveB)
    (hz : bcomm (qFiveB 2) (qFiveB 1) = xFiveB)
    (hb : ∀ i : Fin 6, m5tB⁻¹ * qFiveB i * m5tB ∈ Subgroup.closure (Set.range qFiveB))
    (hR : CommData.actMat 5 qFiveB xFiveB mFiveB m5tB = m5tMat)
    (N : Subgroup Gmat) (hNQ : N ≤ Subgroup.closure (Set.range qFiveB))
    (hN : m5tB ^ 4 ∈ Subgroup.normalizer (N : Set Gmat)) :
    N ≤ Subgroup.zpowers xFiveB ∨ N = Subgroup.closure (Set.range qFiveB) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hx : ∀ g ∈ Subgroup.closure (Set.range qFiveB),
      m5tB⁻¹ * g * m5tB ∈ Subgroup.closure (Set.range qFiveB) :=
    fun g hg => CommData.conj_mem hb hg
  refine commData_dich_of_irred (i₀ := 2) (j₀ := 1) hD hz (a := ![m5tB ^ 4])
    ?_ ?_ N hNQ ?_
  · intro i j
    fin_cases i
    simpa [Matrix.cons_val_zero] using
      conj_pow_mem (Q := Subgroup.closure (Set.range qFiveB)) (x := m5tB) hx 4
        (Subgroup.subset_closure ⟨j, rfl⟩)
  · intro W hW
    refine m5_quot_irreducible_four W fun v hv => ?_
    have := hW 0 v hv
    simpa [gkm5g_actMat_pow hD hb hR 4, Matrix.cons_val_zero] using this
  · intro i
    fin_cases i
    simpa [Matrix.cons_val_zero] using hN

theorem gmat_bmPCentralF1At_F4At_xFiveB
    (hno : ∀ C : Subgroup Gmat,
      ¬ LargeEvenPComponent 5 (Subgroup.centralizer ({xFiveB} : Set Gmat)) C) :
    BMPCentralF1At 5 xFiveB ∧ BMPCentralF4At 5 xFiveB := by
  have hB5 : OPrimeCoreTrivialAt 5 NativeSporadic.B := oPrimeCoreTrivialAt_B_five
  have hM5 : OPrimeCoreTrivialAt 5 Gmat :=
    oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_five (by norm_num)
      (uninvertedOPrimeTrivial_gmat_of_twoATwoCommuting Nat.prime_five (by norm_num) hB5
        sporadicOPrimeHolds_Co1_five MonsterFiveGmat.twoATwoCommuting_five_Gmat)
  have hzo : orderOf xFiveB = 5 := fiveCommData.orderOf_z
  have hg1 : LargeEvenPPrimeCore 5 ↥(Subgroup.centralizer ({xFiveB} : Set Gmat)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp (hM5 xFiveB hzo)
  have : Finite Gmat := gmat_five_setup.1
  have hb := gkm5g_conj_q fiveCommData m5t_conj
  have hR : CommData.actMat 5 qFiveB xFiveB mFiveB m5tB = m5tMat :=
    fiveCommData.actMat_eq m5tMat m5tC m5t_conj
  exact bmPCentralF1At_F4At_of_commData Nat.prime_five (by norm_num) fiveCommData five_bcomm_z
    (Subgroup.closure (Set.range fiveGenG ∪ {m5tB})) gkm5g_Q_le
    (gkm5g_le_normalizer five_closure_le_normalizer fun g hg => CommData.conj_mem hb hg)
    (gkm5g_central five_sylow_closure.2 m5t_cent)
    (five_factorization_le_of_closure_le gkm5g_S_le) five_hCQ (m := 4) (by norm_num)
    (fun N hNQ hN => gkm5g_dich fiveCommData five_bcomm_z hb hR N hNQ
      (hN m5tB (Subgroup.subset_closure (Or.inr rfl))))
    hg1 hno

end CFSG.StandardType.SporadicShape
