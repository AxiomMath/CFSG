module

public import CFSG.Quasithin.H13.GoldschmidtU43EIdx4
public import CFSG.Quasithin.H13.GoldschmidtU43EIdx5
public import CFSG.Sporadic.Recognition.JankoWongPSL

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem card_sylow_three_of_card_24_or_120 {K : Type} [Group K] [Finite K]
    (h : Nat.card K = 24 ∨ Nat.card K = 120) (P : Sylow 3 K) : Nat.card P = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have h1 : Nat.card P * (P : Subgroup K).index = Nat.card K := Subgroup.card_mul_index _
  have h2 : ¬ 3 ∣ (P : Subgroup K).index := P.not_dvd_index
  rw [hn] at h1
  have hlt : n < 2 := by
    by_contra hge
    push Not at hge
    have h9 : 3 ^ 2 ∣ Nat.card K := by
      rw [← h1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 3 hge) _
    rcases h with hK | hK <;> rw [hK] at h9 <;> omega
  interval_cases n
  · exfalso
    apply h2
    rcases h with hK | hK <;> rw [hK] at h1 <;> omega
  · rw [hn]
    norm_num

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem index_two_data {J : Subgroup S.Nbar} (hJ : J.index = 2) :
    ∃ m : ℕ, Odd m ∧ Nat.card S.Nbar = 8 * m ∧ Nat.card J = 4 * m ∧
      Nat.card ↥(J ⊓ S.Dbar) = 4 ∧ S.zbar ∈ J ∧ ¬ CFSG.HasNormalPComplement 2 ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJ
  obtain ⟨h8, h16⟩ := S.two_part_Nbar
  obtain ⟨m, hm⟩ := h8
  have hmodd : Odd m := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
    · exfalso
      apply h16
      exact ⟨k, by rw [hm, hk]; ring⟩
    · exact hodd
  have hm' : Nat.card S.Nbar = 8 * m := by rw [hm]; norm_num
  have hJcard : Nat.card J = 4 * m := by
    have := Subgroup.card_mul_index J
    rw [hJ, hm'] at this
    omega
  have hDJ : ¬ S.Dbar ≤ J := by
    intro hle
    have h1 := Subgroup.card_dvd_of_le hle
    rw [S.card_Dbar, hJcard] at h1
    obtain ⟨k, hk⟩ := h1
    have : Even m := ⟨k, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hmodd) this
  have hrel : J.relIndex S.Dbar = 2 := by
    have hdvd : J.relIndex S.Dbar ∣ J.index := Subgroup.relIndex_dvd_index_of_normal J S.Dbar
    rw [hJ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hDJ
    · exact h
  have hQcard : Nat.card ↥(J ⊓ S.Dbar) = 4 := by
    have := Subgroup.relIndex_mul_card J S.Dbar
    rw [hrel, S.card_Dbar] at this
    omega
  have hzJ : S.zbar ∈ J := by
    have := Subgroup.mul_self_mem_of_index_two hJ S.vbar
    rwa [S.vbar_sq] at this
  have hNC : ¬ CFSG.HasNormalPComplement 2 ↥J := by
    intro h
    apply S.not_hasNormalPComplement_Nbar
    have h2 : IsPGroup 2 S.Nbar := u43_isPGroup_two_of_complement S.oddCore_Nbar hJ h
    exact ⟨⊥, inferInstance, by simp, h2.of_equiv QuotientGroup.quotientBot.symm⟩
  exact ⟨m, hmodd, hm', hJcard, hQcard, hzJ, hNC⟩

theorem card_Nbar_of_index_two
    {J : Subgroup S.Nbar} (hJ : J.index = 2) :
    Nat.card S.Nbar = 24 ∨ Nat.card S.Nbar = 120 := by
  obtain ⟨m, hmodd, hN, hJcard, hQcard, hzJ, hNC⟩ := S.index_two_data hJ
  have hD : CFSG.GorensteinWalter.HasDihedralSylowTwo ↥J :=
    u43_hasDihedralSylowTwo_of_index_two hmodd hJcard hNC
  have h4 : 2 ^ 2 ∣ Nat.card ↥J ∧ ¬ 2 ^ 3 ∣ Nat.card ↥J := by
    rw [hJcard]
    refine ⟨⟨m, by norm_num⟩, ?_⟩
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hmodd
    omega
  have hO : CFSG.oddCore ↥J = ⊥ := by
    have : J.Normal := Subgroup.normal_of_index_eq_two hJ
    exact oddCore_normal_subgroup S.oddCore_Nbar J
  set u : ↥J := ⟨S.zbar, hzJ⟩ with hu
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    show S.zbar ^ 2 = 1
    rw [pow_two]
    exact S.zbar_sq
  have hu1 : u ≠ 1 := fun h => S.zbar_ne_one (congrArg Subtype.val h)
  have hcu : Nat.card (Subgroup.centralizer ({u} : Set ↥J)) = 4 := by
    have hcent : Subgroup.centralizer ({u} : Set ↥J) = (J ⊓ S.Dbar).subgroupOf J := by
      ext x
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        S.Dbar_eq_centralizer_zbar, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        exact ⟨x.2, congrArg Subtype.val h⟩
      · rintro ⟨-, h⟩
        exact Subtype.ext h
    rw [hcent, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hQcard]
  rcases CFSG.Sporadic.Recognition.JankoWong.card_eq_of_psl_step_four hD h4 hNC hO hu2 hu1 hcu
    with h | ⟨h, -⟩
  · left
    omega
  · right
    omega

end JWSetup

end CFSG.Quasithin.H13.U43
