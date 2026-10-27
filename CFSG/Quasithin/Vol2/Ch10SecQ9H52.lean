module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CE22D
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem false_of_isA5Module {H : Subgroup G} {hel : IsElemAbelian 2 (VZ T H)}
    {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
    (hD : C11AmS.E23Data H T (VZ T H) hel I') (h2J : twoResidual H ≤ thompsonJ H)
    (hall : ∀ L' ∈ I', E2.IsA5Module L') {b : G} (hbH : b ∈ H) (hbo : Odd (orderOf b))
    (hbS : b ∈ Subgroup.normalizer (baum T : Set G))
    (hbZ : b ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : False := by
  have hbW : b ∈ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H hbH
  have hb2 : b ∈ twoResidual H := by
    rw [SecE.twoResidual_eq_oTwoUpper]
    exact mem_oTwoUpper_of_odd hbH hbo
  have hφJ : convI hel ⟨b, hbW⟩ ∈ ⨆ L' ∈ I', L' := by
    rw [← hD.jeq]
    exact convI_mem_autI hel (h2J hb2) hbW
  have hφo : Odd (orderOf (convI hel ⟨b, hbW⟩)) := by
    refine hbo.of_dvd_nat ((orderOf_map_dvd (convI hel) _).trans ?_)
    rw [Subgroup.orderOf_mk]
  obtain ⟨h3a, -, h3c⟩ := hD.three hall
  have hφ1 : convI hel ⟨b, hbW⟩ = 1 := by
    refine C11AmS.eq_one_of_A5_components hD.card hD.comm hD.indep h3c hφJ hφo ?_
    intro x hx
    rw [← h3a] at hx ⊢
    exact C11AmS.conj_mem_autI hel hbS hx
  apply hbZ
  exact Subgroup.centralizer_le (le_conjClosure _ H) ((convI_eq_one_iff hel _).mp hφ1)

omit [Finite G] in
theorem three_dvd_card_of_case_one {n : ℕ} (h1 : Case10_1_1One T L I n) :
    3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨-, ⟨F, _, _, hF, ⟨e⟩⟩, -⟩ := h1
  rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF]
  refine Dvd.dvd.mul_left ?_ _
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 n

theorem mem_B0_of_orderOf_eq_three
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Case10_1_1One T L I n) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) {b : G}
    (hb : b ∈ H ⊓ fsuM T L) (hbo : orderOf b = 3) : b ∈ B0 T L := by
  have hbL0 : b ∈ fsuL0 T L := by
    rw [← h1013 G T L I hyp 3 Nat.prime_three (by norm_num) (three_dvd_card_of_case_one h1)]
    exact Subgroup.subset_closure ⟨hb.2, 1, by rw [pow_one, hbo]⟩
  have hK := (bender_of_cases (Or.inl ⟨n, h1⟩)).1
  have hbN := C11AmS.inf_fsuM_le_normalizer_T0 hF6 h37 h38 h331 hyp hK hH hb
  exact mem_oTwoUpper_of_odd ⟨hbL0, hbN⟩ (by rw [hbo]; decide)

theorem not_mem_centralizer_of_mem_B0
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (hyp : Hyp10 G T L I) {n : ℕ} (h1 : Case10_1_1One T L I n) {b : G} (hbB0 : b ∈ B0 T L)
    (hbo : Odd (orderOf b)) (hb1 : b ≠ 1) :
    b ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro hbZ
  obtain ⟨D, hD⟩ := SecA.exists_isHallTwoPrimeOf_B0 hyp
  obtain ⟨hPB, hP2, hPi⟩ := SecA.isSylowTwoOf_T0_inf_B0 hyp
  have hB0P : B0 T L ≤ Subgroup.normalizer ((T0 T L ⊓ B0 T L : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(oTwoUpper_le _ hx).2, Subgroup.le_normalizer hx⟩
  have hYB : Subgroup.zpowers b ≤ B0 T L := Subgroup.zpowers_le.mpr hbB0
  have hYo : Odd (Nat.card (Subgroup.zpowers b)) := by rw [Nat.card_zpowers]; exact hbo
  obtain ⟨c, hc, hcD⟩ := C11AmS.exists_conj_le_of_odd hPB hP2 hPi hB0P hD hYB hYo
  have hD' := C11AmS.isHallTwoPrimeOf_map_conj (Subgroup.le_normalizer (hPB hc)) hD
  have hbD : b ∈ D.map (MulAut.conj c).toMonoidHom := by
    refine ⟨_, hcD ⟨b, Subgroup.mem_zpowers b, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have h := SecA.inf_centralizer_eq_bot_of_case_one h37 h38 h322 hyp h1 hD'
  have hb : b ∈ D.map (MulAut.conj c).toMonoidHom ⊓
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := ⟨hbD, hbZ⟩
  rw [h, Subgroup.mem_bot] at hb
  exact hb1 hb

theorem isSylowTwoOf_baum_oTwoUpper
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) (hyp : Hyp10 G T L I) {n : ℕ} (h1 : Case10_1_1One T L I n)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) :
    IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T) := by
  by_contra hsyl
  have hn3 : ¬ Case10_1_1Three T L I := fun h3 => (bender_of_cases (Or.inl ⟨n, h1⟩)).2 h3.1
  obtain ⟨K, k, hk2, hKc, hHK, hcases, hKF, hel, I', h2J, hD, K₀, hK₀, -, -, hnat, -⟩ :=
    C11AmS.exists_K_dataC hE22 he23 hAS h1021 h331 hyp hH hn1 hZH hn3
  have hall : ∀ L' ∈ I', E2.IsA5Module L' := by
    by_contra hne
    push Not at hne
    obtain ⟨L', hL', hL'5⟩ := hne
    apply hsyl
    have hnatall : ∀ L'' ∈ I', ∃ m, E2.IsL2Natural L'' (fixV (autI hel (twoResidual H))) m := by
      intro L'' hL''
      rcases hD.types L'' hL'' with h | h5
      · exact h
      · exact absurd (C11AmS.isA5Module_of_isA5Module hD hL'' h5 L' hL') hL'5
    have h := (hD.two hnatall).2.2.1
    rwa [SecE.twoResidual_eq_oTwoUpper] at h
  have hk : k = 2 := by
    rcases hnat with h | ⟨-, h⟩
    · exfalso
      have hc := SecA.card_of_isL2Natural h
      rw [SecA.card_of_isA5Module (hall K₀ hK₀)] at hc
      exact SecA.two_pow_mul_ne_120 k hc.symm
    · exact h
  subst hk
  have hmin := minParabolic_of_isHStar h331 hyp hH
  have hTM : T ≤ fsuM T L := fun x hx => SecA.le_fsuM T L hx
  have hKX : ¬ K ≤ H ⊓ fsuM T L := fun h => hH.2.1 (hHK ▸ sup_le (h.trans inf_le_right) hTM)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hKF
  obtain ⟨y, hy, hyo, hyk⟩ := C11AmS.exists_odd_mem_inf_KC hmin hn1 hcases hKc hKX le_rfl hF e
  have hy0 : orderOf y ≠ 0 := hyo.pos.ne'
  have h3 : 3 ∣ orderOf y := by simpa using hyk
  have hbo : orderOf (y ^ (orderOf y / 3)) = 3 := orderOf_pow_orderOf_div hy0 h3
  have hbX : y ^ (orderOf y / 3) ∈ H ⊓ fsuM T L := (H ⊓ fsuM T L).pow_mem hy.1 _
  have hbB0 := mem_B0_of_orderOf_eq_three hF6 h37 h38 h331 h1013 hyp h1 hH hbX hbo
  have hbodd : Odd (orderOf (y ^ (orderOf y / 3))) := by rw [hbo]; decide
  have hb1 : y ^ (orderOf y / 3) ≠ 1 := fun h => by rw [h, orderOf_one] at hbo; omega
  have hbS : y ^ (orderOf y / 3) ∈ Subgroup.normalizer (baum T : Set G) :=
    (((h1022 G T L I hyp H hH hZH).2 (Or.inl ⟨n, h1⟩)).2.1 ⟨n, h1⟩).1 hbB0
  exact false_of_isA5Module hD h2J hall hbX.1 hbodd hbS
    (not_mem_centralizer_of_mem_B0 h37 h38 h322 hyp h1 hbB0 hbodd hb1)

end CFSG.Quasithin.Vol2.Ch10.SecB
