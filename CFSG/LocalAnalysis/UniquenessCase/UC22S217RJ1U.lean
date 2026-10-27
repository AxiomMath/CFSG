module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217RJ1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsSixInf
import CFSG.LocalAnalysis.UniquenessCase.UC22S217RJ1N
import CFSG.LocalAnalysis.UniquenessCase.UC22S217RJ1Eta
import CFSG.LocalAnalysis.UniquenessCase.UC22S217RJ1X
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VPair
import CFSG.LocalAnalysis.UniquenessCase.UC22S217J
import CFSG.LocalAnalysis.UniquenessCase.UC22S217JPair
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xh
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.Quasithin.EmptyFaithful.S146D1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217rj_seven_not_mem_sig (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hSg : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) (hn : c.n = 3) {L : Subgroup G}
    (hL : L ∈ calC D.M) : 7 ∉ D.sig := fun h =>
  uc22s217j_not_sp_seven h211 hH c hn
    (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h)

theorem uc22s217rj_ncard_eq_two (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hSg : UC6S846.SigmaStd D) (h8107 : F08.R8107 D) (hH : H1930 D) (c : Ctx21 D Ch)
    (hn : c.n = 3) {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal)
    (hJ1 : IsJ1 (Bar2 L)) : (conjSetOf D.M L).ncard = 2 := by
  have h3 := uc22s217v_ncard_le_three D hSg hL hJ1 (r := 7) (by norm_num) (by norm_num)
    (by norm_num) (uc22s217j_not_sp_seven h211 hH c hn)
  obtain ⟨K, hK, hKL⟩ := uc22s217v_exists_ne hL hnN
  have h2 : 1 < (conjSetOf D.M L).ncard := (Set.one_lt_ncard_iff (Set.toFinite _)).2
    ⟨K, L, hK, ⟨1, D.M.one_mem, by ext x; simp⟩, hKL⟩
  have h3' : (conjSetOf D.M L).ncard ≠ 3 := fun hc =>
    uc22s217v_false_of_ncard_three D Ch h211 h8107 hH c hL hc hJ1
  omega

theorem uc22s217rj_mem_uniqueSet (D : Data G) (hSg : UC6S846.SigmaStd D) (h8107 : F08.R8107 D)
    (h920 : PartOne.Section9.R920J1 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) (hJ1 : IsJ1 (Bar2 L)) (h7σ : 7 ∉ D.sig)
    (h7 : CFSG.Open.pRank 7 D.M ≤ 2) {A : Subgroup G} (hAL : A ≤ L) (hA : Nat.card A = 7) :
    A ∈ uniqueSet D.M := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp7 : p ≠ 7 := fun h => h7σ (h ▸ hp)
  obtain ⟨K, hK, hKL⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc2]; norm_num) L
  have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
  have hcK : (conjSetOf D.M K).ncard = 2 := by rwa [uc22p2214_conjSetOf_eq hK]
  have hJK := uc22s217v_isJ1_of_mem hJ1 hK
  obtain ⟨A₀, hA₀M, hA₀el, hA₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hp)
  have hA₀p : IsPGroup p A₀ := hA₀el.isPGroup
  have hodd : ∀ a ∈ A₀, Odd (orderOf a) := fun a ha => by
    obtain ⟨k, hk⟩ := hA₀p ⟨a, ha⟩
    exact uc22ine229_odd_orderOf hpp hp2 (k := k) (by simpa using congrArg Subtype.val hk)
  obtain ⟨A₁, hA₁A₀, hA₁c, hA₁L⟩ := uc22s217v_exists_centralizesBar_le hJ1 hpp hp2 hA₀p
    fun a ha => uc22p2214_mem_normalizer_of_odd hc2 (hA₀M ha) (hodd a ha)
  obtain ⟨A₂, hA₂A₁, hA₂c, hA₂K⟩ := uc22s217v_exists_centralizesBar_le hJK hpp hp2
    (hA₀p.to_le hA₁A₀) fun a ha =>
      uc22p2214_mem_normalizer_of_odd hcK (hA₀M (hA₁A₀ ha)) (hodd a (hA₁A₀ ha))
  have hA₂A₀ : A₂ ≤ A₀ := hA₂A₁.trans hA₁A₀
  have hZ : center (Bar2 L) = ⊥ := by
    haveI := (kJ1_holds _ hJ1).2.1
    exact uc22p21k_center_eq_bot hL.2.2
  have hW : ∀ X ∈ calC D.M, IsJ1 (Bar2 X) →
      CFSG.Open.pRank 7 (barImage D.M X) ≤ 1 ∧ 7 ∣ Nat.card (barImage D.M X) := by
    intro X hX hJX
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hX
    have hc : Nat.card (barImage D.M X) = 175560 := by
      rw [← Nat.card_congr e.toEquiv]
      exact (kJ1_holds _ hJX).1
    refine ⟨?_, by rw [hc]; norm_num⟩
    by_contra h
    obtain ⟨E, hEX, -, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 7) (barImage D.M X)
    have h1 : 7 ^ CFSG.Open.pRank 7 (barImage D.M X) ∣ 175560 := by
      rw [← hEc, ← hc]
      exact Subgroup.card_dvd_of_le hEX
    exact uc22s217v_not_sq_dvd (by norm_num) (by norm_num) ((pow_dvd_pow 7 (by omega)).trans h1)
  have hN : ∀ x : ↥D.M, Odd (orderOf x) → uc22p21cPi D.M x ∈
      normalizer (barImage D.M L : Set (Bar2 D.M)) ⊓
        normalizer (barImage D.M K : Set (Bar2 D.M)) := by
    intro x hx
    rw [← Subgroup.orderOf_coe] at hx
    exact ⟨uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hc2 x.2 hx),
      uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcK x.2 hx)⟩
  obtain ⟨E, hEM, hEel, hEcard, hA₂E, hEZ⟩ := uc22s217v_exists_elemAbelian_centralizer hpp
    (by norm_num : Nat.Prime 7) hp2 (by norm_num) hp7 (uc22p22l_barImage_commute hL hKC hKL.symm)
    (uc22s217j_barImage_inf_eq_bot hL hKC hKL.symm hZ) (hW L hL hJ1) (hW K hKC hJK) hN
    (hA₂A₀.trans hA₀M) (hA₀p.to_le hA₂A₀) fun a ha =>
      ⟨uc22s217v_mem_centralizer_barImage hL _ (hA₁L a (hA₂A₁ ha)),
        uc22s217v_mem_centralizer_barImage hKC _ (hA₂K a ha)⟩
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  have hEZR := hEZ R hR.le hR.isPGroup hER
  have hΩ : ∀ x ∈ R, x ^ 7 = 1 → x ∈ E := by
    intro x hxR hx7
    by_contra hxE
    have hxo : orderOf x = 7 := orderOf_eq_prime hx7 fun h => hxE (h ▸ E.one_mem)
    have hdisj : E ⊓ zpowers x = ⊥ := by
      have hdvd : Nat.card ↥(E ⊓ zpowers x) ∣ 7 := by
        rw [← hxo, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h1 | h1
      · exact Subgroup.card_eq_one.1 h1
      · have heq : E ⊓ zpowers x = zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, hxo])
        exact absurd (mem_inf.1 (heq.symm ▸ mem_zpowers x : x ∈ E ⊓ zpowers x)).1 hxE
    have hsum := CFSG.Quasithin.pRank_add_le_pRank_sup (by norm_num : Nat.Prime 7)
      (A := E) (B := zpowers x)
      (fun a ha b hb => (mem_centralizer_iff.1 (hEZR ha) b (zpowers_le.2 hxR hb)).symm) hdisj
    have hE2 : 2 ≤ CFSG.Open.pRank 7 E := UC6S846.le_pRank' (by norm_num) le_rfl hEel hEcard
    have hx1 : 1 ≤ CFSG.Open.pRank 7 (zpowers x) :=
      UC6S846.le_pRank' (by norm_num) le_rfl (CFSG.Open.isElemAbelian_zpowers hx7)
        (by rw [Nat.card_zpowers, hxo, pow_one])
    have hle := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 7)
      (sup_le hEM (zpowers_le.2 (hR.le hxR)))
    omega
  obtain ⟨m, hmM, hm⟩ := UC6.exists_conj_le_of_isSylowOf hR (hAL.trans hL.1.le)
    (IsPGroup.of_card (n := 1) (by rw [hA, pow_one]))
  have hAmE : A.map (MulAut.conj m⁻¹).toMonoidHom ≤ E := by
    rintro _ ⟨a, ha, rfl⟩
    have ha7 : a ^ 7 = 1 := by
      have h : (⟨a, ha⟩ : ↥A) ^ Nat.card A = 1 := pow_card_eq_one'
      rw [hA] at h
      simpa using congrArg Subtype.val h
    refine hΩ _ ?_ (by rw [← map_pow, ha7, map_one])
    simpa [MulAut.conj_apply] using hm a ha
  have hAK : ⁅A, K⁆ ≤ pCoreOf 2 K :=
    (Subgroup.commutator_mono hAL le_rfl).trans
      ((PartTwo.calC_commutator_le_of_ne hL hKC hKL.symm).trans inf_le_right)
  have hNA : normalizer (A : Set G) ≤ D.M :=
    uc22s217rj_normalizer_le_of_ne D h8107 h920 hKC hL hKL hJK hJ1 (r := 7) (by norm_num)
      (by norm_num) (IsPGroup.of_card (n := 1) (by rw [hA, pow_one]))
      (fun h => by rw [h, Subgroup.card_bot] at hA; norm_num at hA) (hAL.trans hL.1.le) hAK
  have hdvd : p ∣ Nat.card (centralizer (E : Set G)) := by
    obtain ⟨j, hj⟩ := (hA₀p.to_le hA₂A₀).exists_card_eq
    have hj1 : 1 ≤ j := by
      have h1 : p ^ 3 ≤ p ^ (j + 2) :=
        calc p ^ 3 = Nat.card A₀ := hA₀c.symm
          _ ≤ p * Nat.card A₁ := hA₁c
          _ ≤ p * (p * Nat.card A₂) := Nat.mul_le_mul_left _ hA₂c
          _ = p ^ (j + 2) := by rw [hj]; ring
      have := (pow_le_pow_iff_right₀ hpp.one_lt).1 h1
      omega
    exact (show p ∣ Nat.card A₂ by rw [hj]; exact dvd_pow_self p (by omega)).trans
      (Subgroup.card_dvd_of_le hA₂E)
  have hU := u81_mem_uniqueSet_of_dvd (UC6S846.sp_of_mem_sig hSg hns hp) hR hER hEel hΩ hAmE
    ((UC6S898.normalizer_map_conj_le m⁻¹ hNA).trans
      (P22x.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (D.M.inv_mem hmM))).le) hdvd
  have h := PartTwo.conj_mem_uniqueSet hU hmM
  rw [uc22p22d_map_conj_map_conj, mul_inv_cancel] at h
  have hA1 : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by ext x; simp
  rwa [hA1] at h

theorem s21_17RJ1_of_three (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (h5 : S21_5 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h6 : S21_6Inf D Ch)
    (hSg : UC6S846.SigmaStd D) (h8107 : F08.R8107 D) (h920 : PartOne.Section9.R920J1 D)
    (h7 : 7 ∉ D.sig → CFSG.Open.pRank 7 D.M ≤ 2) : S21_17RJ1 D Ch := by
  intro hH c L hL hnN hJ1
  have hn := uc22s217rj_n_eq_three D Ch h5 h6 h8107 h920 hH c (hn3 hH c) hL hnN hJ1
  have h7σ := uc22s217rj_seven_not_mem_sig D Ch h211 hSg hH c hn hL
  have hc2 := uc22s217rj_ncard_eq_two D Ch h211 hSg h8107 hH c hn hL hnN hJ1
  exact ⟨hc2, hn, uc22s217rj_conjClosure_eq_opp hL hc2 hJ1 (h7 h7σ),
    fun A hAL hA => uc22s217rj_mem_uniqueSet D hSg h8107 h920 hL hc2 hJ1 h7σ (h7 h7σ) hAL hA⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
