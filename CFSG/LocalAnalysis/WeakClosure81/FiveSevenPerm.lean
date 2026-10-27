module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenFinish
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenPSL
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenReg
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixPerm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Equiv

theorem five_seven_perm (hR : R3_1) {n : ℕ} (hn : 4 < n) {K A : Subgroup (Perm (Fin n))}
    (hAlt : alternatingGroup (Fin n) ≤ K) (hA : IsElemAbelian 2 A) (hAne : A ≠ ⊥)
    (h1 : (maxOver K A).ncard = 1) :
    n = 5 ∧ K = alternatingGroup (Fin n) ∧ Nat.card A = 4 := by
  obtain ⟨⟨m, hm⟩, α, hM⟩ := five_six_perm hR hn hAlt hA.isPGroup h1
  obtain ⟨hfix, htrans⟩ := exists_smul_eq_of_maxOver_eq_stabilizer hAlt hAne hM
  have hreg := existsUnique_smul_eq_of_isMulCommutative hA.1 hfix htrans
  have hcardn : Nat.card (Fin n) = n := by simp
  have hAcard : Nat.card A = Nat.card (Fin n) - 1 :=
    card_eq_of_existsUnique_smul_eq (by omega) hfix hreg
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    omega
  obtain ⟨P, hP, hAP⟩ :=
    exists_isNaturalPSL2_ge_of_regular hm0 (by rw [hcardn]; exact hm) hA hfix hreg
  obtain ⟨h5, hK⟩ := eq_five_of_isNaturalPSL2 hn hAlt hM hP hAP
  exact ⟨h5, hK, by rw [hAcard, hcardn, h5]⟩

end CFSG.LocalAnalysis.WeakClosure81
