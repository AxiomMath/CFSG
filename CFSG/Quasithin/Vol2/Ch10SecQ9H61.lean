module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H60
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecQ9H51
public import CFSG.Quasithin.Vol2.Ch10SecQ9H56
public import CFSG.Quasithin.Vol2.Ch10SecQ9H57
public import CFSG.Quasithin.Vol2.Ch10SecQ9H59

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

theorem b0KNonquasi_of
    (hF6 : FactBenderOver) (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1)
    (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1) (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC)
    (he23 : E2.E23Statement) (hAS : Ch11.SecH.AS_I_1_3_L2) : B0KNonquasi := by
  intro G _ _ T L I H K M₁ J n m cfg hd
  obtain ⟨hcomm, hJKO, p, hp, hp2, ⟨e⟩⟩ := hd
  have : Fact p.Prime := ⟨hp⟩
  have := cfg.hyp.fsu.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat cfg.hyp.fsu.nonabelian cfg.hyp.fsu.qtke).1
  have hO₁ : pCoreOf 2 M₁ ≠ ⊥ := (inH_of_inM cfg.hM₁).2
  have hJM : J ≤ M₁ := le_of_mem_cComp cfg.hJ
  have hKJ : K ≤ J := cfg.hKJ
  have hKp : ⁅K, K⁆ = K := perfect_of_mem_cComp cfg.hK
  obtain ⟨F₀, _, _, hF₀, ⟨eK⟩⟩ := cfg.hKF
  have hB0S : B0 T L ≤ Subgroup.normalizer (baum T : Set G) :=
    (((h1022 G T L I cfg.hyp H cfg.hH cfg.hZH).2 (Or.inl ⟨n, cfg.case1⟩)).2.1 ⟨n, cfg.case1⟩).1
  have hB0M : B0 T L ≤ M₁ := hB0S.trans (le_sup_left.trans cfg.hM₁.2)
  have hB0J : B0 T L ≤ Subgroup.normalizer (J : Set G) :=
    b0_le_normalizer_of_mem_cComp hLoc h37 h38 hO₁ cfg.hJ hB0M
  set K' := (modO2Image M₁ K).subgroupOf (modO2Image M₁ J) with hK'
  have hKF' : K' ⊓ CFSG.oddCore ↥(modO2Image M₁ J) = ⊥ :=
    inf_oddCore_eq_bot_of_SL2 hKJ hJM hKp hF₀ eK
  have hKbJ : modO2Image M₁ K ≤ modO2Image M₁ J := le_of_le_of_eq le_sup_left hJKO.symm
  have hsup : K' ⊔ CFSG.oddCore ↥(modO2Image M₁ J) = ⊤ := by
    have hOJ : ((CFSG.oddCore ↥(modO2Image M₁ J)).map (modO2Image M₁ J).subtype).subgroupOf
        (modO2Image M₁ J) = CFSG.oddCore ↥(modO2Image M₁ J) := by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (modO2Image M₁ J).subtype_injective]
    have h := congrArg (fun A : Subgroup (↥M₁ ⧸ CFSG.pCore 2 ↥M₁) =>
      A.subgroupOf (modO2Image M₁ J)) hJKO
    rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hKbJ (Subgroup.map_subtype_le _),
      hOJ] at h
    exact h.symm
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKp]
  have hK'p : ⁅K', K'⁆ = K' := by
    rw [hK', ← range_toModO2 hKJ hJM, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hKtop]
  have hSK := isSylowTwoOf_baum_inf hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS cfg
  obtain ⟨s, hsS, hs1⟩ : ∃ s : ↥K, (s : G) ∈ baum T ∧ toModO2 M₁ J K hKJ hJM s ≠ 1 := by
    by_contra hall
    push Not at hall
    have hle : (baum T ⊓ K).subgroupOf K ≤ (toModO2 M₁ J K hKJ hJM).ker := fun x hx =>
      MonoidHom.mem_ker.mpr (hall x (Subgroup.mem_subgroupOf.mp hx).1)
    exact hSK.2.2 ((two_dvd_index_ker hKJ hJM hKp hF₀ eK).trans (Subgroup.index_dvd_of_le hle))
  set x := toModO2 M₁ J K hKJ hJM s with hx
  obtain ⟨a, ha⟩ := cfg.hyp.fsu.sylow.1 ⟨(s : G), (inf_le_left : baum T ≤ T) hsS⟩
  have hsa : s ^ 2 ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val ha)
  have hxa : orderOf x ∣ 2 ^ a :=
    (orderOf_map_dvd _ s).trans (orderOf_dvd_of_pow_eq_one hsa)
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hx2 : 2 ∣ orderOf x := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hxa
    rcases j with _ | j
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hj, pow_zero])) hs1
    · rw [hj]
      exact dvd_pow_self 2 (by omega)
  set w := x ^ (orderOf x / 2) with hw
  have hwo : orderOf w = 2 := orderOf_pow_orderOf_div hx0 hx2
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hwo, pow_two] at h
    exact h
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hwo
    omega
  have hwK : w ∈ K' := by
    rw [hK', ← range_toModO2 hKJ hJM]
    exact ⟨s ^ (orderOf x / 2), by rw [map_pow]⟩
  set R : Subgroup ↥(modO2Image M₁ J) :=
    ((baum T).subgroupOf J).map (toModO2 M₁ J J le_rfl hJM) with hR
  have hRp : IsPGroup 2 ↥R := by
    refine IsPGroup.map ?_ _
    intro y
    obtain ⟨k, hk⟩ := cfg.hyp.fsu.sylow.1 ⟨((y : ↥J) : G), (inf_le_left : baum T ≤ T) y.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hxR : x ∈ R := ⟨⟨s, hKJ s.2⟩, hsS, Subtype.ext rfl⟩
  have hwR : w ∈ R := R.pow_mem hxR _
  have hwc : ∀ k ∈ K', k * w = w * k := by
    intro k hk
    have h := SL2Inv.fix_of_inf_eq_bot hp2 e hKF' (MulAut.conj k)
      (fun r hr => by
        rw [MulAut.conj_apply]
        exact K'.mul_mem (K'.mul_mem hk hr) (K'.inv_mem hk)) hwK hw2 hw1
    rw [MulAut.conj_apply] at h
    calc k * w = k * w * k⁻¹ * k := by group
      _ = w * k := by rw [h]
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ : ∃ k₁ ∈ K', ∃ k₂ ∈ K', k₁ * k₂ ≠ k₂ * k₁ := by
    by_contra h
    push Not at h
    have hb : ⁅K', K'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun b hb => h b hb a ha
    rw [hK'p] at hb
    rw [hb] at hwK
    exact hw1 (Subgroup.mem_bot.mp hwK)
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hLoc hO₁
  obtain ⟨hcases, hcommon, hextra⟩ := h36 _ hQ _ (modO2Image_mem_cComp cfg.hJ)
  have hFit : CFSG.fittingSubgroup ↥(modO2Image M₁ J) = CFSG.oddCore ↥(modO2Image M₁ J) :=
    hcommon.1
  have h34 : A36Case3 ↥(modO2Image M₁ J) ∨ A36Case4 ↥(modO2Image M₁ J) := by
    rcases hcases with hc | h | h
    · exfalso
      apply hcomm
      have hnc : ((k₁ : ↥(modO2Image M₁ J) ⧸ CFSG.oddCore ↥(modO2Image M₁ J))) * k₂ ≠
          k₂ * k₁ := by
        intro h
        apply hk
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
        have h' : (k₁ * k₂)⁻¹ * (k₂ * k₁) ∈ K' ⊓ CFSG.oddCore ↥(modO2Image M₁ J) :=
          ⟨K'.mul_mem (K'.inv_mem (K'.mul_mem hk₁ hk₂)) (K'.mul_mem hk₂ hk₁), h⟩
        rw [hKF', Subgroup.mem_bot, inv_mul_eq_one] at h'
        exact h'
      have hc' := commutator_eq_bot_of_isQuasisimple hc.1 hnc
      have hmap : ⁅(CFSG.oddCore ↥(modO2Image M₁ J)).map (modO2Image M₁ J).subtype,
          modO2Image M₁ J⁆ = (⁅CFSG.oddCore ↥(modO2Image M₁ J),
            (⊤ : Subgroup ↥(modO2Image M₁ J))⁆).map (modO2Image M₁ J).subtype := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [hmap, hc', Subgroup.map_bot]
    · exact Or.inl h
    · exact Or.inr h
  have hE := hextra h34
  have hKFfit : K' ⊓ CFSG.fittingSubgroup ↥(modO2Image M₁ J) = ⊥ := by rw [hFit]; exact hKF'
  have hsup' : K' ⊔ CFSG.fittingSubgroup ↥(modO2Image M₁ J) = ⊤ := by rw [hFit]; exact hsup
  have hwF : w ∉ CFSG.fittingSubgroup ↥(modO2Image M₁ J) := by
    intro h
    have h' : w ∈ K' ⊓ CFSG.fittingSubgroup ↥(modO2Image M₁ J) := ⟨hwK, h⟩
    rw [hKFfit, Subgroup.mem_bot] at h'
    exact hw1 h'
  have hC := fun f hf hwf =>
    SL2Inv.commute_props h34 hE hKFfit hK'p hk₁ hk₂ hk hw2 hwF hwc (f := f) hf hwf
  have hconj : ∀ b ∈ B0 T L, K.map (MulAut.conj b).toMonoidHom ≤ K := by
    intro b hb
    have hbM := hB0M hb
    have hbN := mk_mem_normalizer hbM (hB0J hb)
    set φ := (modO2Image M₁ J).normalizerMonoidHom ⟨_, hbN⟩ with hφdef
    have hφ : ∀ y : ↥(modO2Image M₁ J), ((φ y : ↥(modO2Image M₁ J)) :
        ↥M₁ ⧸ CFSG.pCore 2 ↥M₁) = QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨b, hbM⟩ * y *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨b, hbM⟩)⁻¹ := fun y => rfl
    have hφR : ∀ r ∈ R, φ r ∈ R := by
      rintro _ ⟨y, hy, rfl⟩
      have hyS : ((y : ↥J) : G) ∈ baum T := Subgroup.mem_subgroupOf.mp hy
      refine ⟨⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hB0J hb) y).mp y.2⟩,
        (Subgroup.mem_normalizer_iff.mp (hB0S hb) y).mp hyS, Subtype.ext ?_⟩
      rw [hφ, toModO2_coe, toModO2_coe, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hφw : φ w = w :=
      SL2Inv.fix_of_inf_eq_bot hp2 e (SL2Inv.inf_oddCore_eq_bot hRp) φ hφR hwR hw2 hw1
    have hmap := SL2Inv.map_le_of_fix hsup' hK'p hwc hC φ hφw
    have hle : K.map (MulAut.conj b).toMonoidHom ≤ K ⊔ pCoreOf 2 M₁ := by
      rintro _ ⟨k, hk, rfl⟩
      have hkM : b * k * b⁻¹ ∈ M₁ :=
        M₁.mul_mem (M₁.mul_mem hbM (hJM (hKJ hk))) (M₁.inv_mem hbM)
      show b * k * b⁻¹ ∈ K ⊔ pCoreOf 2 M₁
      refine P134.mem_sup_of_mem_modO2Image hkM ?_
      have hτk : toModO2 M₁ J K hKJ hJM ⟨k, hk⟩ ∈ K' := by
        rw [hK', ← range_toModO2 hKJ hJM]
        exact ⟨⟨k, hk⟩, rfl⟩
      have h2 := Subgroup.mem_subgroupOf.mp (hmap (Subgroup.mem_map_of_mem _ hτk))
      convert h2 using 1
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hφ, toModO2_coe, ← map_inv, ← map_mul, ← map_mul]
      rfl
    exact SL2Inv.le_of_le_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
      (pCoreOf_le_normalizer_K cfg) hle (by rw [← Subgroup.map_commutator, hKp])
  intro b hb
  exact mem_normalizer_of_map_le (hconj b hb) (hconj b⁻¹ (Subgroup.inv_mem _ hb))

end CFSG.Quasithin.Vol2.Ch10.SecB
