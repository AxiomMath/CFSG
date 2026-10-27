module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZA
public import CFSG.Quasithin.Vol2.Ch10SecQ3CE22C
public import CFSG.Quasithin.Vol2.Ch10SecQ3CU
public import CFSG.Quasithin.Vol2.Ch10SecQ3CW

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_odd_mem_inf_KC {H T X K : Subgroup G} (hmin : MinParabolic H T X)
    (hn1 : 1 < E1.nParam H) (hcases : E2.E22CasesC H T X K) (hKc : K ∈ cComp H)
    (hKX : ¬ K ≤ X) {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ y ∈ X ⊓ K, Odd (orderOf y) ∧ 2 ^ m - 1 ∣ orderOf y := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨-, -, -, hBor, -⟩ := E2.exists_borel_of_e22CasesC hn1 hcases
  obtain ⟨S, hS, hB⟩ := hBor
  have hKH : K ≤ H := le_of_mem_cComp hKc
  set N := (kerIn X H).subgroupOf H with hN
  set π : ↥H →* E2.StarQuot X H := QuotientGroup.mk' N with hπ
  set Ks := E2.star X H K with hKs
  have hmemKs : ∀ k : ↥K, π ⟨k, hKH k.2⟩ ∈ Ks := fun k =>
    Subgroup.mem_map_of_mem π (show (⟨k, hKH k.2⟩ : ↥H) ∈ K.subgroupOf H from k.2)
  set ψ : ↥K →* ↥Ks := (π.comp (Subgroup.inclusion hKH)).codRestrict Ks hmemKs with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨(x : G), hx⟩, Subtype.ext rfl⟩
  have hle : CFSG.pCore 2 ↥K ≤ ψ.ker := by
    intro k hk
    have h1 : (k : G) ∈ pCoreOf 2 K := (SecB.C10P34.mem_pCoreOf_iff k.2).mpr hk
    have h2 : (k : G) ∈ kerIn X H := hmin.pCoreOf_le_kerIn
      (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
        (subnormal_of_mem_cComp hKc) h1)
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show π ⟨k, hKH k.2⟩ = 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h2
  set χ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥Ks :=
    (QuotientGroup.lift (CFSG.pCore 2 ↥K) ψ hle).comp e.symm.toMonoidHom with hχ
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨k, rfl⟩ := hψs y
    exact ⟨e (QuotientGroup.mk k), by simp [hχ]⟩
  have hF' : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hsimple := CFSG.QuasithinUnique.AppE.sl2_isSimpleGroup hm hF'
  have hχi : Function.Injective χ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal χ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff χ).mp h
    · exfalso
      apply hKX
      intro k hk
      have hx : e (QuotientGroup.mk ⟨k, hk⟩) ∈ χ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hx
      have h1 : ψ ⟨k, hk⟩ = 1 := by simpa [hχ] using hx
      have h2 : π ⟨k, hKH hk⟩ = 1 := congrArg Subtype.val h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact kerIn_le h2
  set P := (S.subgroupOf Ks).comap χ with hP
  have hP2 : IsPGroup 2 P := by
    have h1 : IsPGroup 2 (S.subgroupOf Ks) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact h1.comap_of_injective χ hχi
  have hPi : ¬ 2 ∣ P.index := by
    rw [hP, Subgroup.index_comap_of_surjective _ hχs]
    exact hS.2.2
  obtain ⟨g, hg1, hg2⟩ := SecA.exists_conj_unip hF hP2 hPi
  have hPmem : ∀ p, p ∈ P ↔ ∃ b : F, g * p * g⁻¹ = SecA.unipSL b := by
    intro p
    refine ⟨hg1 p, ?_⟩
    rintro ⟨b, hb⟩
    have := hg2 b
    rwa [show g⁻¹ * SecA.unipSL b * g = p by rw [← hb]; group] at this
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hδN := conj_dU_mem_normalizer hPmem μ
  have hδo := orderOf_conj_dU hF hμ g
  set d : E2.StarQuot X H := (χ (g⁻¹ * dU μ * g) : E2.StarQuot X H) with hd
  have hdK : d ∈ Ks := (χ (g⁻¹ * dU μ * g)).2
  have hdN : d ∈ Subgroup.normalizer (S : Set (E2.StarQuot X H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    by_cases hsK : s ∈ Ks
    · obtain ⟨p, hp⟩ := hχs ⟨s, hsK⟩
      have e1 : s ∈ S ↔ p ∈ P := by
        rw [hP, Subgroup.mem_comap, hp, Subgroup.mem_subgroupOf]
      have e2 : d * s * d⁻¹ ∈ S ↔ (g⁻¹ * dU μ * g) * p * (g⁻¹ * dU μ * g)⁻¹ ∈ P := by
        rw [hP, Subgroup.mem_comap, map_mul, map_mul, map_inv, hp, Subgroup.mem_subgroupOf]
        rfl
      rw [e1, e2]
      exact Subgroup.mem_normalizer_iff.mp hδN p
    · have h1 : s ∉ S := fun h => hsK (hS.1 h)
      have h2 : d * s * d⁻¹ ∉ S := by
        intro h
        apply hsK
        have := Ks.mul_mem (Ks.mul_mem (Ks.inv_mem hdK) (hS.1 h)) hdK
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hdB : d ∈ E2.star X H (X ⊓ K) := by
    rw [hB]
    exact ⟨hdK, hdN⟩
  have hdo : orderOf d = 2 ^ m - 1 := by
    rw [hd, Subgroup.orderOf_coe, orderOf_injective χ hχi, hδo]
  obtain ⟨x, hx, hxd⟩ := hdB
  have hxo : 2 ^ m - 1 ∣ orderOf (x : G) := by
    have := orderOf_map_dvd π x
    rw [hxd, hdo] at this
    rwa [Subgroup.orderOf_coe]
  obtain ⟨j, o, ho, hxord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
  have hord : orderOf ((x : G) ^ 2 ^ j) = o := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨o, hxord⟩, hxord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
  refine ⟨(x : G) ^ 2 ^ j, Subgroup.pow_mem _ hx _, hord ▸ ho, ?_⟩
  rw [hord]
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  exact ((Nat.coprime_two_right.mpr hodd).pow_right j).dvd_of_dvd_mul_left (hxord ▸ hxo)

theorem exists_ctxC
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3)
    (hDHB : Ch11.SecB.DerivedHallBorel) (hB0K : Obl10_2_3B0K) (hE22 : E2.E22StatementC)
    (he23 : E2.E23Statement) (hAS : Ch11.SecH.AS_I_1_3_L2) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (h3228 : TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Case10_1_1One T L I n) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hn1 : 1 < E1.nParam H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (hfaith : HallFaithful T L I H) :
    ∃ (K : Subgroup G) (k : ℕ) (b : G) (hel : IsElemAbelian 2 (VZ T H))
      (I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel))))
      (K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))), Ctx T L I H K n k b hel I' K₀ := by
  have hn3 : ¬ Case10_1_1Three T L I := fun h3 => (bender_of_cases (Or.inl ⟨n, h1⟩)).2 h3.1
  obtain ⟨K, k, hk2, hKc, hHK, hcases, hKF, hel, I', h2J, hD, K₀, hK₀, t, ht, hnat, hKt⟩ :=
    exists_K_dataC hE22 he23 hAS h1021 h331 hyp hH hn1 hZH hn3
  have hmin := SecB.minParabolic_of_isHStar h331 hyp hH
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hTM : T ≤ fsuM T L := fun x hx => SecA.le_fsuM T L hx
  have hKX : ¬ K ≤ H ⊓ fsuM T L := fun h => hH.2.1 (hHK ▸ sup_le (h.trans inf_le_right) hTM)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hKF
  obtain ⟨y, hy, hyo, hyk⟩ := exists_odd_mem_inf_KC hmin hn1 hcases hKc hKX hk2 hF e
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H := H13.LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer (hTH ht))
  have hHK' : H = K' ⊔ T := by
    have h1 : (K ⊔ T).map (MulAut.conj t).toMonoidHom = K ⊔ T := by
      rw [← hHK]
      exact map_conj_eq_self (hTH ht)
    rw [Subgroup.map_sup, map_conj_eq_self ht] at h1
    rw [hK', h1]
    exact hHK
  have hK'F : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (↥K' ⧸ CFSG.pCore 2 ↥K' ≃* Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨F, inferInstance, inferInstance, hF, ⟨(C10P34.conjQuot K K' t rfl).symm.trans e⟩⟩
  set b := t * y * t⁻¹ with hb
  have hbK : b ∈ K' := ⟨y, hy.2, rfl⟩
  have hbHM : b ∈ H ⊓ fsuM T L :=
    ⟨H.mul_mem (H.mul_mem (hTH ht) hy.1.1) (H.inv_mem (hTH ht)),
      (fsuM T L).mul_mem ((fsuM T L).mul_mem (hTM ht) hy.1.2) ((fsuM T L).inv_mem (hTM ht))⟩
  have hbord : orderOf b = orderOf y := by
    rw [hb, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hbo : Odd (orderOf b) := hbord ▸ hyo
  have hbk : 2 ^ k - 1 ∣ orderOf b := hbord ▸ hyk
  have hKF' : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  have hO2 := oTwoUpper_inf_le_B0 hF6 h37 h38 h322 h331 h1013 hDHB hB0K hyp h1 hH hn1 hZH hfaith
    hKc hHK hKF'
  have hbB0 : b ∈ B0 T L := hO2 (mem_oTwoUpper_of_odd hbHM hbo)
  have hbD : ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (B0 T L) ∧ b ∈ D := by
    obtain ⟨D, hD⟩ := SecA.exists_isHallTwoPrimeOf_B0 hyp
    obtain ⟨hPB, hP2, hPi⟩ := SecA.isSylowTwoOf_T0_inf_B0 hyp
    have hB0P : B0 T L ≤ Subgroup.normalizer ((T0 T L ⊓ B0 T L : Subgroup G) : Set G) :=
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨(oTwoUpper_le _ hx).2, Subgroup.le_normalizer hx⟩
    have hYB : Subgroup.zpowers b ≤ B0 T L := Subgroup.zpowers_le.mpr hbB0
    have hYo : Odd (Nat.card (Subgroup.zpowers b)) := by rw [Nat.card_zpowers]; exact hbo
    obtain ⟨c, hc, hcD⟩ := exists_conj_le_of_odd hPB hP2 hPi hB0P hD hYB hYo
    refine ⟨D.map (MulAut.conj c).toMonoidHom,
      isHallTwoPrimeOf_map_conj (Subgroup.le_normalizer (hPB hc)) hD, ?_⟩
    refine ⟨_, hcD ⟨b, Subgroup.mem_zpowers b, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hbZ : b ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro hbZ
    obtain ⟨D, hD, hbD⟩ := hbD
    have hb1 : b ∈ D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := ⟨hbD, hbZ⟩
    rw [SecA.inf_centralizer_eq_bot_of_case_one h37 h38 h322 hyp h1 hD, Subgroup.mem_bot] at hb1
    rw [hb1, orderOf_one, Nat.dvd_one] at hbk
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hbS : b ∈ Subgroup.normalizer (baum T : Set G) :=
    (((h1022 G T L I hyp H hH hZH).2 (Or.inl ⟨n, h1⟩)).2.1 ⟨n, h1⟩).1 hbB0
  exact ⟨K', k, b, hel, I', K₀, ⟨h37, h38, h322, h331, h3228, he23, hyp, h1, hH, hn1, hZH, hfaith,
    hk2, hK'c, hHK', hK'F, h2J, hD, hK₀, hnat, hKt, hbHM, hbK, hbo, hbk, hbB0, hbD, hbZ, hbS,
    ((h1022 G T L I hyp H hH hZH).1).1⟩⟩

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
