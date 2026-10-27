module

public import CFSG.Quasithin.Vol2.Ch9Sec1Coord
public import CFSG.Quasithin.Vol2.Ch9Inputs
public import CFSG.Quasithin.Vol2.Ch6Vocab

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem thompsonJk_le_of_bound {T V : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTN : T ≤ Subgroup.normalizer (V : Set G)) {d : ℕ} (hd : 1 ≤ d)
    (hb : ∀ A : Subgroup (MulAut (IntMod V hV)), A ≤ autI hV T → A ≠ ⊥ → IsElemAbelian2 A →
      rk A + d ≤ rkIdx (fixV A)) :
    thompsonJk (d - 1) T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold thompsonJk
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, hAe, hAmax⟩ := hA
  refine le_inf hAT ?_
  intro x hxA
  by_contra hxC
  obtain ⟨E, hET, hEe, hEc⟩ := H.exists_isElemAbelian_card_pRank T
  have hAE := hAmax E hET hEe
  have hAle := H.card_le_two_pow_pRank hAT hAe
  obtain ⟨k, hk⟩ := H.exists_card_eq_two_pow_of_isElemAbelian hAe
  set m := CFSG.Open.pRank 2 T with hm
  have hkm : k ≤ m := by
    rw [hk] at hAle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hAle
  have hmk : m ≤ k + (d - 1) := by
    have h2 : 2 ^ m ≤ 2 ^ (k + (d - 1)) :=
      calc 2 ^ m ≤ 2 ^ (d - 1) * 2 ^ k := by rw [← hEc, ← hk]; exact hAE
        _ = 2 ^ (k + (d - 1)) := by ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hcor : IsElemAbelianCorank T (m - k) A :=
    ⟨hAT, hAe, by rw [hk, ← pow_add]; congr 1; omega⟩
  have hB24 := card_le_relIndex_mul_card_mul_two_pow hV hVT hcor
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTN
  have hĀT : autI hV A ≤ autI hV T := autI_mono hV hAT
  have hĀ1 : autI hV A ≠ ⊥ := by
    intro h0
    apply hxC
    have hmem := convI_mem_autI hV hxA (hAN hxA)
    rw [h0, Subgroup.mem_bot] at hmem
    exact (convI_eq_one_iff hV _).mp hmem
  have hĀe : IsElemAbelian2 (autI hV A) := isElemAbelian2_autI hV hAe hAN
  have h2 := hb _ hĀT hĀ1 hĀe
  rw [E3.rk_autI_eq_mQuot hV hAN, E3.rkIdx_fixV_autI hV hAN] at h2
  have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAe
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  rw [E3.relIndex_eq_two_pow hA2 (A ⊓ Subgroup.centralizer (V : Set G)),
    E3.card_eq_two_pow_mul hV2
      (inf_le_left : V ⊓ Subgroup.centralizer (A : Set G) ≤ V)] at hB24
  set x := mQuot A (A ⊓ Subgroup.centralizer (V : Set G))
  set y := mQuot V (V ⊓ Subgroup.centralizer (A : Set G))
  set c := Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))
  have hc : 0 < c := Nat.card_pos
  have hj : 2 ^ (m - k) ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ y * c ≤ 2 ^ (x + (d - 1)) * c :=
    hB24.trans (calc 2 ^ x * c * 2 ^ (m - k) ≤ 2 ^ x * c * 2 ^ (d - 1) :=
        Nat.mul_le_mul_left _ hj
      _ = 2 ^ (x + (d - 1)) * c := by ring)
  have h5 : 2 ^ y ≤ 2 ^ (x + (d - 1)) := Nat.le_of_mul_le_mul_right h4 hc
  have h6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
  omega

namespace Setup

variable {T L I : Subgroup G} {n : ℕ} (S : Setup T L I n)
include S

theorem h11 (hH11 : Ch9InH11Plus) {A : Subgroup (MulAut (IntMod (fsuV T I) S.hV))}
    (hAM : A ≤ autI S.hV (fsuM T L)) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    rk A + n ≤ rkIdx (fixV A) + 1 ∧
      (rk A + 2 ≤ rkIdx (fixV A) ∨ (n = 2 ∧ ∃ t ∈ A, rkIdx (fixV (Subgroup.zpowers t)) = n)) ∧
      (A ≤ autI S.hV (fsuL0 T L) → rk A + n ≤ rkIdx (fixV A)) := by
  obtain ⟨-, hn, K, hKf, hKfin, hK, hreal⟩ := S.row
  exact hH11 (IntMod (fsuV T I) S.hV) (autI S.hV (fsuL0 T L)) (autI S.hV (fsuM T L)) n
    IntMod.sq_eq_one (by omega) (autI_mono S.hV L0_le_fsuM) S.autOn_M_le_normalizer
    ⟨K, hKf, hKfin, hK, hreal⟩ A hAM hA1 hAe

theorem thompsonJk_sub_two_le (hH11 : Ch9InH11Plus) :
    thompsonJk (n - 2) T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have h := thompsonJk_le_of_bound S.hV S.fsuV_le_T S.T_le_normalizer_V
    (d := n - 1) (by have := S.two_le; omega) fun A hAT hA1 hAe => by
      have := (S.h11 hH11 (hAT.trans (autI_mono S.hV T_le_fsuM)) hA1 hAe).1
      have := S.two_le
      omega
  have e : n - 1 - 1 = n - 2 := by omega
  rwa [e] at h

end Setup

end CFSG.Quasithin.H13.Ch9
