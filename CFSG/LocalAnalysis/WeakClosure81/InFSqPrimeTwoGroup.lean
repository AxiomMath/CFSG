module

public import CFSG.LocalAnalysis.WeakClosure81.InFSqSymThree
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
public import CFSG.Quasithin.EmptyFaithful.S1422Local
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem inEP_top_of_inE {Q : Type} [Group Q] [Finite Q] [Group.IsSolvable Q]
    (h : CFSG.Quasithin.E1.InE 1 (⊤ : Subgroup Q)) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InEP 1 (⊤ : Subgroup Q) := by
  classical
  intro T hT
  have hTs : CFSG.Quasithin.IsSylowIn 2 T ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T) (K := ⊤)).mp hT
  have hFor := h T hTs
  intro Ω hΩ hne hnt
  have hgen := hFor Ω hΩ
  have hle : CFSG.Quasithin.E1.eGen 1 (⊤ : Subgroup Q) T Ω ≤
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP 1 (⊤ : Subgroup Q) T Ω := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    haveI : Group.IsSolvable ↥K := inferInstance
    exact le_iSup₂_of_le A hA (le_iSup_of_le hAT
      (le_iSup₂_of_le K ⟨hK.1, hK.2.1, hK.2.2.1,
        Or.inl (CFSG.Quasithin.E1.isE_eOne_of_isSolvable hK inferInstance)⟩ le_rfl))
  exact top_le_iff.mp (hgen.symm.trans_le (sup_le_sup hle le_rfl))

private theorem exists_uniqueMaxOver_of_prime_index {Q : Type} [Group Q] [Finite Q] {q k : ℕ}
    (hq : q.Prime) (hO2 : CFSG.pCore 2 Q = ⊥) (hdvd : Nat.card Q ∣ q * 2 ^ k)
    (hQ2 : 2 ∣ Nat.card Q) :
    ∃ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧ HasUniqueMaxOver T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (⊤ : Subgroup Q)
  have hTs : CFSG.Quasithin.IsSylowIn 2 T ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T) (K := ⊤)).mp hT
  have hcardT : Nat.card T * T.index = Nat.card Q := Subgroup.card_mul_index T
  have hidx_dvd_Q : T.index ∣ Nat.card Q :=
    ⟨Nat.card T, by rw [mul_comm]; exact hcardT.symm⟩
  have hidx_dvd : T.index ∣ q * 2 ^ k := hidx_dvd_Q.trans hdvd
  have hodd : Odd T.index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    have h := hTs.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at h
  have hcop : Nat.Coprime T.index (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have hidx_dvd_q : T.index ∣ q := hcop.dvd_of_dvd_mul_right hidx_dvd
  have hidx_ne_one : T.index ≠ 1 := by
    intro h1
    have htop : T = ⊤ := Subgroup.index_eq_one.mp h1
    have hTtop2 : IsPGroup 2 (⊤ : Subgroup Q) := htop ▸ hTs.isPGroup
    have hle : (⊤ : Subgroup Q) ≤ CFSG.pCore 2 Q := by
      change _ ≤ sSup {K : Subgroup Q | K.Normal ∧ IsPGroup 2 K}
      exact le_sSup ⟨inferInstance, hTtop2⟩
    rw [hO2] at hle
    have hcard_le : Nat.card Q ≤ 1 := by
      have h := Subgroup.card_le_of_le hle
      rwa [Subgroup.card_top, Subgroup.card_bot] at h
    have hge : 2 ≤ Nat.card Q := Nat.le_of_dvd (Nat.card_pos (α := Q)) hQ2
    omega
  have hidx_eq : T.index = q := by
    rcases (Nat.dvd_prime hq).mp hidx_dvd_q with h1 | hq'
    · exact absurd h1 hidx_ne_one
    · exact hq'
  have hlt : T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 : T.index = 1 := by rw [htop, Subgroup.index_top]
    rw [hidx_eq] at h1
    exact hq.ne_one h1
  refine ⟨T, hT, T, hlt, ?_⟩
  intro X hTX hXlt
  have hidx' : (T.subgroupOf (⊤ : Subgroup Q)).index = q := by
    rw [show (T.subgroupOf (⊤ : Subgroup Q)).index = T.index from
      Subgroup.relIndex_top_right T, hidx_eq]
  rcases CFSG.Quasithin.eq_or_eq_of_le_of_index_prime (H := ⊤) hTX le_top hq hidx' with h | h
  · exact h.le
  · exact absurd h hXlt.ne

theorem inFSq_one_of_prime_mul_two_group
    (A T : Subgroup G) (q : ℕ)
    (hq : q.Prime) (hqodd : Odd q) (hAcard : Nat.card A = q)
    (hT : IsPGroup 2 T) (hperm : Permutes A T) :
    InFSq 1 (A ⊔ T) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : 2 ≠ q := by
    rintro rfl
    exact hqodd.not_two_dvd_nat (by norm_num)
  have hinf : A ⊓ T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hAcard]
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (hqodd.coprime_two_right)
  have hcardH : Nat.card ↥(A ⊔ T) = q * Nat.card T := by
    rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hperm hinf, hAcard]
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hcardHk : Nat.card ↥(A ⊔ T) = q * 2 ^ k := by rw [hcardH, hk]
  haveI : Fintype ↥(A ⊔ T) := Fintype.ofFinite ↥(A ⊔ T)
  have hcardH' : Fintype.card ↥(A ⊔ T) = 2 ^ k * q ^ 1 := by
    rw [← Nat.card_eq_fintype_card, hcardHk, pow_one, mul_comm]
  haveI : Group.IsSolvable ↥(A ⊔ T) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two hq hq2 hcardH'
  let Q := Bar2 (A ⊔ T)
  haveI : Group.IsSolvable Q := by
    dsimp [Q, Bar2]
    infer_instance
  have hO2 : CFSG.pCore 2 Q = ⊥ := by
    dsimp [Q, Bar2]
    exact CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hdvdQ : Nat.card Q ∣ q * 2 ^ k := by
    dsimp [Q, Bar2]
    exact (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(A ⊔ T))).trans
      (by rw [← hcardHk])
  by_cases hodd : Odd (Nat.card Q)
  · exact inFSq_of_odd_card_bar2 1 (A ⊔ T) hodd
  · have hQ2 : 2 ∣ Nat.card Q := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have hInE : CFSG.Quasithin.E1.InE 1 (⊤ : Subgroup Q) :=
      CFSG.Quasithin.E1.inE_one_top_of_isSolvable (Nat.card Q) Q le_rfl inferInstance
    have hInEP : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InEP 1 (⊤ : Subgroup Q) :=
      inEP_top_of_inE hInE
    have hU : ∃ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧ HasUniqueMaxOver T :=
      exists_uniqueMaxOver_of_prime_index hq hO2 hdvdQ hQ2
    exact inF_top_of_inEP 1 hInEP hU hO2

end CFSG.LocalAnalysis.WeakClosure81
