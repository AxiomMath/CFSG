module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837T
public import CFSG.Quasithin.Vol2.Ch11SecBNPCasesC
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace Ch838

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem three_dvd_card_of_typeOne {Y : Type} [Group Y] (h : Vol2.Ch11.SecB.TypeOne Y) :
    3 ∣ Nat.card Y := by
  rcases h with h | h | ⟨p, e, -, -, -, h⟩ | ⟨s, p, -, -, h⟩
  · exact three_dvd_card_psl_model h
  · obtain ⟨e⟩ : Nonempty (Y ≃* alternatingGroup (Fin 6)) := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · exact three_dvd_card_psl_model h
  · cases s
    · exact three_dvd_card_psu_three_model h
    · exact three_dvd_card_psl_model h

omit [Finite G] in
theorem card_star_dvd {M H K : Subgroup G} (hKH : K ≤ H) :
    Nat.card ↥(E2.star M H K) ∣ Nat.card ↥K := by
  have h1 := Subgroup.card_map_dvd (K.subgroupOf H)
    (QuotientGroup.mk' ((kerIn M H).subgroupOf H))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h1

theorem le_twoResidual_of_mem_cComp {H K : Subgroup G} (hK : K ∈ cComp H) :
    K ≤ twoResidual H := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hnorm : K ≤ Subgroup.normalizer ((K ⊓ twoResidual H : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_twoResidual H (hKH hx)⟩
  have h2 : ∀ y ∈ K, ∃ k : ℕ, y ^ 2 ^ k ∈ K ⊓ twoResidual H := fun y hy => by
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H y (hKH hy)
    exact ⟨k, K.pow_mem hy _, hk⟩
  have h3 := twoResidual_le_of_isTwoQuotient inf_le_left hnorm h2
  rw [C124.twoResidual_eq_self_of_perfect' (perfect_of_mem_cComp hK)] at h3
  exact fun x hx => (h3 hx).2

theorem false_of_isHStar_of_not_three_dvd
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit')
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHGz : H ≤ Subgroup.centralizer ({z} : Set G))
    (hns : ¬ Group.IsSolvable ↥H) (h3 : ∀ K' ∈ cComp H, H = K' ⊔ T → ¬ 3 ∣ Nat.card ↥K') :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  have h37' := a37ForSQTK_of_cat h37
  have h38' := a38ForSQTK_of_cat h38
  have h39' := a39ForSQTK_of_cat h39
  obtain ⟨-, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := Ch837.isSylowTwoOf_of_le hyp.fsu.sylow hTH
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hU : IsUniqueMaxOver H T (H ⊓ fsuM T L) := by
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hyp.fsu.sylow
    have := IsHStar.isUniqueMaxOver S (hS ▸ hH) (hS ▸ hTM)
    rwa [hS] at this
  have hNT : Subgroup.normalizer (T : Set G) ≤ fsuM T L := by
    have hJ := thompsonJ_le_centralizer_fsuV h37' h38' h39' hyp hV hN
    have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
    have hVp : IsVplus T L I (fsuV T I) := by
      by_cases hc' : L ≠ conjClosure L T ∧ Case326VM T L I
      · exact Or.inl ⟨hc'.1, hc'.2, hVVM⟩
      · exact Or.inr ⟨hc', rfl⟩
    exact (h3108 G T L I (fsuV T I) hyp.fsu hVp hJ T hyp.fsu.sylow.1 (thompsonJ_le_self T)).2
  have hmin : MinParabolic H T (H ⊓ fsuM T L) :=
    ⟨hTsyl, fun hle => hH.2.1 (hle.trans hNT), hU⟩
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hH.1.2
  obtain ⟨⟨K', hK'c, hHK', -, hcases⟩, -⟩ := hNoN G H T (H ⊓ fsuM T L) hmin hSQ hns
  have hK'H : K' ≤ H := le_of_mem_cComp hK'c
  have h3K' : ¬ 3 ∣ Nat.card ↥K' := h3 K' hK'c hHK'
  rcases Vol2.Ch11.SecB.typeOne_or_lieCases hcases with hT1 | hlie
  · exact h3K' ((three_dvd_card_of_typeOne hT1).trans (card_star_dvd hK'H))
  have hloc := (local_structure_wreath_lie_of h326
    (Ch4.stmt4_4_14Lie_of_steps h443 hC58 h317 h37' h38' h39') hC58 h317 h37' h38' h39' h3228 hyp
    hrow H hH ⟨K', hK'c, hHK', hlie⟩).2
  obtain ⟨n, hn2, hty, hB⟩ := hlie.exists_borel
  have h3n : 3 ≤ 2 ^ n - 1 := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n - 1 ≠ 1)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
    have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  obtain ⟨x, ⟨hxM, hxK'⟩, hxo⟩ := Ch837.exists_orderOf_eq_of_isBorelIn hn2 hty hB hp hpd
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3K' (hxo ▸ Subgroup.orderOf_dvd_natCard K' hxK')
  exact Ch837.false_of_mem_inf_of_orderOf_prime h326 hyp hrow hV hz2 hzV hloc hxM.1 hxM.2
    (hHGz hxM.1) hp hp2 hp3 hxo

end Ch838

open Ch838 in
theorem claim838Solv_of_lie
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight) :
    Claim838Solv := by
  intro G _ _ T L I hyp h731 hc hrow hV H hH hIU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  obtain ⟨-, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  obtain ⟨z, hz2, hzV⟩ := input8_3_z G T L I hyp h731 hc hrow
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzU : z ∈ ch83CR hV := Ch838.mem_ch83CR hV hzmem
  have hU1 : ch83CR hV ≠ ⊥ := fun h => hz1 (by rw [h] at hzU; exact Subgroup.mem_bot.mp hzU)
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hUz : Subgroup.centralizer (ch83CR hV : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzU)
  have hTsyl : IsSylowTwoOf T H := Ch837.isSylowTwoOf_of_le hyp.fsu.sylow hH.1.1
  have hHGz : H ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← sup_twoResidual_eq hTsyl]
    exact sup_le hTz (hIU.trans hUz)
  have hHns : ¬ Group.IsSolvable ↥H := fun hs => hns
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (twoResidual_le H)))
  have h3U := Ch838.not_three_dvd_card_centralizer_ch83CR h37 h38 h326 hyp hV hrow hN hU1
  refine false_of_isHStar_of_not_three_dvd hNoN h443 h37 h38 h39 h3228 hC58 h317 h326 h3108 hyp
    hrow hV hz2 hzV hH hHGz hHns fun K' hK'c _ h3 => h3U ?_
  exact h3.trans (Subgroup.card_dvd_of_le ((le_twoResidual_of_mem_cComp hK'c).trans hIU))

theorem stmt8_3_8_of_lie
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (hmod : StmtFSUModule) (h326 : Stmt3_2_6C)
    (h3108 : Stmt3_2_10_eight) (h836 : Stmt8_3_6) (h837 : Stmt8_3_7) (hOut : KG838Out)
    (hPar : KG838Par) (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') : Stmt8_3_8 :=
  stmt8_3_8_of h37 h38 hmod h326 h836 h837 hOut hPar
    (claim838Solv_of_lie hNoN h443 h37 h38 h39 h3228 hC58 h317 h326 h3108)

end CFSG.Quasithin.H13
