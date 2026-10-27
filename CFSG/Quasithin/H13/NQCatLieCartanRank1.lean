module

public import CFSG.Quasithin.H13.NQCatLieCartan
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

theorem TorusConcl.mono {S : Type} [Group S] {a b : Prop} (h : TorusConcl S a) (hab : a → b) :
    TorusConcl S b := fun P Y E hP hY hodd hcard hEP hE hE16 hEC => by
  obtain ⟨h1, h2, h3⟩ := h P Y E hP hY hodd hcard hEP hE hE16 hEC
  exact ⟨h1, h2, fun h0 => hab (h3 h0)⟩

theorem odd_of_benderType {S : Type} [Group S] {n i e : ℕ} (h : BenderType S n i e) : Odd e := by
  rcases h.cases' with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, hn⟩
  · exact odd_one
  · exact odd_one
  · have h2 : Odd (2 ^ n + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    exact h2.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 (2 ^ n + 1)))

theorem torusConcl_of_benderType {S : Type} [Group S] [Finite S]
    {n i e : ℕ} (h : BenderType S n i e) : TorusConcl S (e = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 S)
  set U : Subgroup S := ((default : Sylow 2 S) : Subgroup S) with hUdef
  have hU : IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, (default : Sylow 2 S).isPGroup', ?_⟩
    change ¬ 2 ∣ U.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact (default : Sylow 2 S).not_dvd_index
  have hn : 1 ≤ n := by
    rcases h.cases' with ⟨-, -, hn⟩ | ⟨-, -, a, -, rfl⟩ | ⟨-, -, hn⟩ <;> omega
  have hodd : Odd (Nat.card (cartan U t)) := by
    rw [hc.card_cartan]
    refine Odd.mul ?_ (odd_of_benderType h)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.odd_iff, pow_succ]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  refine torusConcl_of_torus (H := cartan U t) hU inf_le_left hc.sup_eq.ge hodd
    (fun a ha b hb => hc.cartan_comm ha hb) fun E hEU hE hE16 hEC => ?_
  have hroot : ∀ z ∈ E, z ∈ rootCenter U := fun z hz => ⟨hEU hz, hEC hz⟩
  obtain ⟨z, hzE, hz1⟩ : ∃ z ∈ E, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hE0 : E = ⊥ := eq_bot_iff.2 fun w hw => hcon w hw
    rw [hE0, Subgroup.card_bot] at hE16
    norm_num at hE16
  have hCE : cartan U t ⊓ Subgroup.centralizer (E : Set S) = fixCartan U t := by
    apply le_antisymm
    · rw [← hc.cartan_inf_centralizer_eq (hroot z hzE) hz1]
      exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzE))
    · intro x hx
      refine ⟨fixCartan_le_cartan U t hx, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      by_cases hw1 : w = 1
      · rw [hw1, one_mul, mul_one]
      · have hx' : x ∈ cartan U t ⊓ Subgroup.centralizer ({w} : Set S) := by
          rw [hc.cartan_inf_centralizer_eq (hroot w hw) hw1]
          exact hx
        exact (Subgroup.mem_centralizer_singleton_iff.1 hx'.2).symm
  have h16 : 16 ≤ 2 ^ n := by
    rw [← hc.card_center, ← hE16]
    exact Subgroup.card_le_of_le fun w hw => hroot w hw
  have he : 0 < e := (odd_of_benderType h).pos
  refine ⟨?_, fun h0 => ?_⟩
  · rw [hCE]
    have h1 := Subgroup.relIndex_mul_card (fixCartan U t) (cartan U t)
    rw [inf_eq_left.2 (fixCartan_le_cartan U t), hc.card_fixCartan, hc.card_cartan] at h1
    have h2 : (fixCartan U t).relIndex (cartan U t) = 2 ^ n - 1 :=
      Nat.eq_of_mul_eq_mul_right he h1
    omega
  · rw [hCE] at h0
    have := hc.card_fixCartan
    rw [h0, Subgroup.card_bot] at this
    exact this.symm

theorem torusConcl_rank1 {S : Type} [Group S] [Finite S] {k : ℕ}
    (hk : 2 ≤ k) (h : IsPSL 2 2 k S ∨ IsPSU 3 2 k S ∨ IsSz k S) :
    TorusConcl S (∃ k : ℕ, 2 ≤ k ∧ (IsPSL 2 2 k S ∨ IsSz k S ∨ IsPSp4 2 k S)) := by
  rcases h with hL | hU | hS
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psl2_of_stated hL
    exact (torusConcl_of_benderType (.linear k hk e)).mono fun _ => ⟨k, hk, Or.inl hL⟩
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hk hU
    have hmodel : CFSG.Theory.Comparator.PSU3Model k = CFSG.Open.PSU3 2 k :=
        CFSG.Models.benderPSU3Model_eq_psu3 k
    refine (torusConcl_of_benderType
      (.unitary k hk (e.trans (MulEquiv.subgroupCongr hmodel.symm)))).mono fun he => ?_
    exfalso
    have h1 : 2 ^ k + 1 ≤ Nat.gcd 3 (2 ^ k + 1) := by
      have hd := Nat.div_mul_cancel (Nat.gcd_dvd_right 3 (2 ^ k + 1))
      rw [he, one_mul] at hd
      rw [hd]
    have h2 : Nat.gcd 3 (2 ^ k + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have h3 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · obtain ⟨a, ha, -, ⟨e⟩⟩ :=
      CFSG.ComponentClassification.GMS78.exists_mulEquiv_sz_of_suzukiModel hS
    exact (torusConcl_of_benderType
      (.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))).mono
        fun _ => ⟨k, hk, Or.inr (Or.inl hS)⟩

end CFSG.Quasithin.H13.NQCat.LieCartan
