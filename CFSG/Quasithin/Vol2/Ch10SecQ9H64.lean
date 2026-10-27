module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H63
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecQ9H51
public import CFSG.Quasithin.Vol2.Ch10SecQ9H57
public import CFSG.Quasithin.Vol2.Ch10SecQ9H59
public import CFSG.Quasithin.Vol2.Ch10SecQ9H60
public import CFSG.Quasithin.Vol2.Ch10SecQ9H62

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

theorem b0KLie_of
    (hK1 : C10KH.KGRank2ParabolicOrder) (hG2 : FactG2CoreOddIndex) (hF6 : FactBenderOver)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) : B0KLie := by
  intro G _ _ T L I H K M₁ J n m cfg hb
  obtain ⟨⟨-, -, P, hP, hKP⟩, f, hf2, htype⟩ := hb
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
  have hrange : (toModO2 M₁ J K hKJ hJM).range = K' := range_toModO2 hKJ hJM
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKp]
  have hK'p : ⁅K', K'⁆ = K' := by
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hKtop]
  have hP' := Rank2.isMaxParabolic2_top_of_map hP
  have hK'P : K' = perfectCore (P.subgroupOf (modO2Image M₁ J)) := by
    rw [hK', hKP, Rank2.perfectCore_subgroupOf hP.1.1]
  have hK'odd : ¬ 2 ∣ K'.index := by
    rw [hK'P]
    exact Rank2.not_two_dvd_index_perfectCore hK1 hG2 hf2 htype hP'
  have hSK := isSylowTwoOf_baum_inf hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS cfg
  set A := (baum T ⊓ K).subgroupOf K with hA
  set τ := toModO2 M₁ J K hKJ hJM with hτ
  have hQK' : A.map τ ≤ K' := hrange ▸ A.map_le_range τ
  have hrel : (A.map τ).relIndex K' = (A.map τ.rangeRestrict).index := by
    rw [← hrange, Subgroup.relIndex]
    congr 1
    ext y
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, ha, hay⟩
      exact ⟨a, ha, Subtype.ext hay⟩
    · rintro ⟨a, ha, hay⟩
      exact ⟨a, ha, congrArg Subtype.val hay⟩
  have hQrel : ¬ 2 ∣ (A.map τ).relIndex K' := by
    rw [hrel]
    exact fun h => hSK.2.2 (h.trans (Subgroup.index_map_dvd A τ.rangeRestrict_surjective))
  have hQodd : ¬ 2 ∣ (A.map τ).index := by
    rw [← Subgroup.relIndex_mul_index hQK']
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · exact hQrel h
    · exact hK'odd h
  set R : Subgroup ↥(modO2Image M₁ J) :=
    ((baum T).subgroupOf J).map (toModO2 M₁ J J le_rfl hJM) with hR
  have hRp : IsPGroup 2 ↥R := by
    refine IsPGroup.map ?_ _
    intro y
    obtain ⟨k, hk⟩ := cfg.hyp.fsu.sylow.1 ⟨((y : ↥J) : G), (inf_le_left : baum T ≤ T) y.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hQR : A.map τ ≤ R := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, hKJ a.2⟩, (Subgroup.mem_subgroupOf.mp ha).1, Subtype.ext rfl⟩
  have hRQ : R ≤ A.map τ := by
    have h1 := Subgroup.relIndex_mul_index hQR
    have h2 : ¬ 2 ∣ (A.map τ).relIndex R := fun h => hQodd (h1 ▸ h.mul_right _)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    have h3 : (A.map τ).relIndex R ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact Subgroup.relIndex_eq_one.mp hj
    · exact (h2 (by rw [hj]; exact dvd_pow_self 2 (Nat.succ_ne_zero j))).elim
  have hRK' : R ≤ K' := hRQ.trans hQK'
  have hRsyl : IsSylowTwoOf R ⊤ := by
    refine ⟨le_top, hRp, ?_⟩
    have hidx : (R.subgroupOf ⊤).index = R.index := Subgroup.relIndex_top_right R
    rw [hidx]
    exact fun h => hQodd (h.trans (Subgroup.index_dvd_of_le hQR))
  obtain ⟨P₀, hres⟩ := Rank2.exists_residualOvergroupsAt (by omega) htype hRsyl
  have hK'ne : K' ≠ ⊥ := by
    intro h
    have h2 := two_dvd_index_ker hKJ hJM hKp hF₀ eK
    have hker : τ.ker = ⊤ := by
      refine eq_top_iff.mpr fun k _ => MonoidHom.mem_ker.mpr ?_
      have hk : τ k ∈ τ.range := ⟨k, rfl⟩
      rw [hrange, h] at hk
      exact Subgroup.mem_bot.mp hk
    rw [hker, Subgroup.index_top] at h2
    exact absurd h2 (by norm_num)
  have hK'top : K' ≠ ⊤ := by
    intro h
    apply hP'.2.1
    rw [eq_top_iff, ← h, hK'P]
    exact perfectCore_le _
  have hK'ns : ¬ Group.IsSolvable ↥K' := by
    intro hs
    have : Group.IsPerfect ↥K' := Subgroup.isPerfect_iff.mpr hK'p
    have : Nontrivial ↥K' := (Subgroup.nontrivial_iff_ne_bot K').mpr hK'ne
    exact Group.IsPerfect.not_isSolvable ↥K' hs
  have hdK' : Setup.X6.dInf K' = K' := le_antisymm (Setup.X6.dInf_le K')
    (Setup.X6.le_dInf_of_perfect (Subgroup.isPerfect_iff.mpr hK'p) le_rfl)
  have hconj : ∀ b ∈ B0 T L, Odd (orderOf b) → K.map (MulAut.conj b).toMonoidHom ≤ K := by
    intro b hb hbo
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
    have hφRe : R.map φ.toMonoidHom = R := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨r, hr, rfl⟩
        exact hφR r hr
      · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    have hφo : Odd (orderOf φ) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (modO2Image M₁ J).normalizerMonoidHom ⟨_, hbN⟩)
      rw [Subgroup.orderOf_mk]
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁)) ⟨b, hbM⟩)
      rwa [Subgroup.orderOf_mk]
    have hmap : K'.map φ.toMonoidHom = K' := by
      have h := hres.2.2.2.2.2 φ hφo hφRe K' hRK' hK'top hK'ns
      rwa [hdK'] at h
    have hle : K.map (MulAut.conj b).toMonoidHom ≤ K ⊔ pCoreOf 2 M₁ := by
      rintro _ ⟨k, hk, rfl⟩
      have hkM : b * k * b⁻¹ ∈ M₁ :=
        M₁.mul_mem (M₁.mul_mem hbM (hJM (hKJ hk))) (M₁.inv_mem hbM)
      show b * k * b⁻¹ ∈ K ⊔ pCoreOf 2 M₁
      refine P134.mem_sup_of_mem_modO2Image hkM ?_
      have hτk : τ ⟨k, hk⟩ ∈ K' := by
        rw [← hrange]
        exact ⟨⟨k, hk⟩, rfl⟩
      have h2 := Subgroup.mem_subgroupOf.mp (hmap.le (Subgroup.mem_map_of_mem _ hτk))
      convert h2 using 1
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hφ, hτ, toModO2_coe, ← map_inv, ← map_mul, ← map_mul]
      rfl
    exact SL2Inv.le_of_le_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
      (pCoreOf_le_normalizer_K cfg) hle (by rw [← Subgroup.map_commutator, hKp])
  refine (Subgroup.closure_le _).mpr ?_
  rintro b ⟨hbX, hbo⟩
  have hbB : b ∈ B0 T L := Subgroup.subset_closure ⟨hbX, hbo⟩
  exact mem_normalizer_of_map_le (hconj b hbB hbo)
    (hconj b⁻¹ (Subgroup.inv_mem _ hbB) (by rwa [orderOf_inv]))

end CFSG.Quasithin.Vol2.Ch10.SecB
