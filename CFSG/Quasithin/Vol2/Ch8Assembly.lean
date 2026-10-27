module

public import CFSG.Quasithin.Vol2.Ch8Sec2Statements
public import CFSG.Quasithin.Vol2.Ch8Sec3Statements
public import CFSG.Quasithin.Vol2.Ch8Sec1
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Vol2.Ch8InputsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

theorem stmt8_2_13_cocode_of (h8213 : Stmt8_2_13) : Stmt8_2_13_cocode := by
  intro G _ _ T L I hyp h731 h821 hc hrow
  obtain ⟨⟨-, h1, h2, h3, h4, h5⟩, h6, -⟩ := h8213 G T L I hyp h731 h821 hc hrow
  exact ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩

theorem stmt8_2_14_of (h8210 : Stmt8_2_10) (h8212 : Stmt8_2_12) (h8213 : Stmt8_2_13)
    (hfus : Stmt8_2_14_fusion) (has : InputAS91) : Stmt8_2_14 := by
  intro G _ _ T L I hyp h731 h821 hc hrow
  obtain ⟨-, -, z, hz2, hzV⟩ := h8210 G T L I hyp h731 h821 hc hrow
  obtain ⟨⟨hM24, -⟩, -, hquot⟩ := h8213 G T L I hyp h731 h821 hc hrow
  obtain ⟨-, ⟨-, -, hE6⟩, hEO, -, -⟩ := h8212 G T L I hyp h731 h821 hc hrow z hz2 hzV
  obtain ⟨g, -, hg, hgz⟩ := hfus G T L I hyp h731 h821 hc hrow z hz2 hzV
  refine has G hyp.fsu.simple hyp.fsu.nonabelian z hz2 (hE6 hM24).2 (hquot z hz2 hzV)
    ⟨g, ?_, hgz⟩
  rw [← hEO]
  exact le_conjClosure _ _ hg

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowIn_self {p : ℕ} {S : Subgroup G} (hS : IsPGroup p ↥S) (hp : p ≠ 1) :
    IsSylowIn p S S :=
  ⟨le_rfl, hS, by rw [Subgroup.relIndex_self]; exact fun h => hp (Nat.dvd_one.1 h)⟩

theorem exists_mQuot_eq_two {V : Subgroup G} (hV : IsPGroup 2 ↥V) (h3 : 3 ≤ rk ↥V) :
    ∃ A : Subgroup G, A ≤ V ∧ A ≠ ⊥ ∧ mQuot V A = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_eq_two_pow_of_isPGroup hV
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := rk ↥V - 2)
    (by rw [hcard]; exact Nat.pow_dvd_pow 2 (Nat.sub_le _ _))
  refine ⟨K.map V.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
  · intro h
    rw [Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective] at h
    rw [h, Subgroup.card_bot] at hK
    have : 1 ≤ rk ↥V - 2 := by omega
    have h2 : 2 ≤ 2 ^ (rk ↥V - 2) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (rk ↥V - 2) := Nat.pow_le_pow_right (by norm_num) this
    omega
  · have hm := mQuot_add_rk (A := V) (B := K.map V.subtype) (Subgroup.map_subtype_le K)
    have hrk : rk ↥(K.map V.subtype) = rk ↥V - 2 := by
      show padicValNat 2 (Nat.card ↥(K.map V.subtype)) = rk ↥V - 2
      rw [Subgroup.card_map_of_injective V.subtype_injective, hK, padicValNat.prime_pow]
    omega

theorem stmt8_3_1_of (hmod : StmtFSUModule) (huniq : Input7_0_2_unique) (hQ : Input8_3_Q)
    (hz : Input8_3_z) (h832 : Stmt8_3_2) (h835 : Stmt8_3_5) (h8310 : Stmt8_3_10)
    (h8314 : Stmt8_3_14) : Stmt8_3_1 := by
  intro G _ _ T L I hyp h731 hc hrow
  obtain ⟨hV, -⟩ := hmod G T L I hyp.fsu
  obtain ⟨z, hz2, hzV⟩ := hz G T L I hyp h731 hc hrow
  have hs := h832 G T L I hyp h731 hc hrow hV
  obtain ⟨hW0, -⟩ := h835 G T L I hyp h731 hc hrow z hz2 hzV
  obtain ⟨-, hHs, -, -, -, hSyl, hn⟩ := h8310 G T L I hyp h731 hc hrow z hz2 hzV
  have hW2 := h8314 G T L I hyp h731 hc hrow z hz2 hzV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hST : ch83S T L z ≤ T := pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)
  have hXL : ch83X T L z ≤ fsuL0 T L :=
    (twoResidual_le _).trans inf_le_left
  have hQS : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ ch83S T L z := by
    rw [hQ G T L I hyp]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)).trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQ2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    hyp.fsu.sylow.1.to_le inf_le_left
  have hW2Q : wClos (fsuV T I) 2 (ch83S T L z) ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    le_inf ((wClos_le _ _).trans hST) hW2
  have : IsMulCommutative ↥(fsuV T I) := hV.1
  have hVQ : fsuV T I ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    le_inf (fsuV_le_T hyp.fsu hV (hmod G T L I hyp.fsu).2)
      (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw => setLike_mul_comm hw hv)
  have hW2ne : wClos (fsuV T I) 2 (ch83S T L z) ≠ ⊥ := by
    have h3 : 3 ≤ rk ↥(fsuV T I) := by
      have := sParam_le_rk hV
      rw [hs] at this
      exact this
    obtain ⟨A, hAV, hA1, hAm⟩ := exists_mQuot_eq_two (isPGroup_of_isElemAbelian_two hV) h3
    intro h
    apply hA1
    rw [eq_bot_iff, ← h]
    refine le_wClos ⟨hAV.trans (hVQ.trans hQS), 1, ?_, ?_⟩
    · rw [conjSubgroup_one]; exact hAV
    · rw [conjSubgroup_one]; exact hAm
  have hC2 : Subgroup.centralizer (cClos (fsuV T I) 2 (ch83S T L z) : Set G) ≤ fsuM T L :=
    e3_16_three (isSylowIn_self (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) (by norm_num))
      hQS hQ2 hW2Q hW2ne
      (huniq G T L I hyp)
  have h19 := e3_19 hV hSyl (i := 0) (j := 2) (by rw [hn]; rfl) (by rw [hs]; norm_num)
  rw [zero_add] at h19
  have hle : ch83Kz T L z ⊔ ch83S T L z ≤ fsuM T L := by
    rw [← h19]
    exact sup_le (inf_le_right.trans hC2) (inf_le_right.trans hW0)
  exact hHs.2.1 (sup_le (le_sup_left.trans hle) (le_normalizer_conjClosure L T))

end CFSG.Quasithin.H13
