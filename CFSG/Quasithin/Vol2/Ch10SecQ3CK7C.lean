module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7A
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7B
public import CFSG.Quasithin.Vol2.Ch10SecQ9H51
public import CFSG.Quasithin.Vol2.Ch10SecQ9H57
public import CFSG.Quasithin.Vol2.Ch10SecQ9H60
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecQ9H59

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS.K7

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_sup_center {Y : Type*} [Group Y] {A B : Subgroup Y} (hB : ⁅B, B⁆ = B)
    (h : B ≤ A ⊔ Subgroup.center Y) : B ≤ A := by
  rw [← hB, Subgroup.commutator_le]
  intro b₁ hb₁ b₂ hb₂
  have hdec : ∀ b ∈ B, ∃ a ∈ A, ∃ z ∈ Subgroup.center Y, a * z = b := by
    intro b hb
    have hb' : b ∈ ((A ⊔ Subgroup.center Y : Subgroup Y) : Set Y) := h hb
    rw [Subgroup.mul_normal] at hb'
    obtain ⟨a, ha, z, hz, e⟩ := hb'
    exact ⟨a, ha, z, hz, e⟩
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdec b₁ hb₁
  obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdec b₂ hb₂
  have k₁ : ∀ x, z₁ * x * z₁⁻¹ = x := fun x => by
    rw [← Subgroup.mem_center_iff.mp hz₁ x, mul_inv_cancel_right]
  have k₂ : ∀ x, z₂ * x * z₂⁻¹ = x := fun x => by
    rw [← Subgroup.mem_center_iff.mp hz₂ x, mul_inv_cancel_right]
  have e : ⁅a₁ * z₁, a₂ * z₂⁆ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by
    rw [commutatorElement_def]
    calc a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹
        = a₁ * (z₁ * (a₂ * z₂) * z₁⁻¹) * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by group
      _ = a₁ * a₂ * (z₂ * a₁⁻¹ * z₂⁻¹) * a₂⁻¹ := by rw [k₁]; group
      _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by rw [k₂]
  rw [e]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)

theorem map_conj_le_of_odd
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) {T L I H K M₁ J : Subgroup G} {n m : ℕ}
    (cfg : B0KConfig G T L I H K M₁ J n m) (hc : B0KTypeC M₁ K J) (hn : Odd n) {x : G}
    (hxL0 : x ∈ fsuL0 T L) (hxN : x ∈ Subgroup.normalizer (T0 T L : Set G))
    (hxo : Odd (orderOf x)) : K.map (MulAut.conj x).toMonoidHom ≤ K := by
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
  have hxB : x ∈ B0 T L := mem_oTwoUpper_of_odd ⟨hxL0, hxN⟩ hxo
  set K' := (modO2Image M₁ K).subgroupOf (modO2Image M₁ J) with hK'
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKp]
  have hK'p : ⁅K', K'⁆ = K' := by
    rw [hK', ← range_toModO2 hKJ hJM, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hKtop]
  have hSK := isSylowTwoOf_baum_inf hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS cfg
  obtain ⟨s, hsS, hs1⟩ : ∃ s : ↥K, (s : G) ∈ baum T ∧ toModO2 M₁ J K hKJ hJM s ≠ 1 := by
    by_contra hall
    push Not at hall
    have hle : (baum T ⊓ K).subgroupOf K ≤ (toModO2 M₁ J K hKJ hJM).ker := fun y hy =>
      MonoidHom.mem_ker.mpr (hall y (Subgroup.mem_subgroupOf.mp hy).1)
    exact hSK.2.2 ((two_dvd_index_ker hKJ hJM hKp hF₀ eK).trans (Subgroup.index_dvd_of_le hle))
  set R : Subgroup ↥(modO2Image M₁ J) :=
    ((baum T).subgroupOf J).map (toModO2 M₁ J J le_rfl hJM) with hR
  have hRp : IsPGroup 2 ↥R := by
    refine IsPGroup.map ?_ _
    intro y
    obtain ⟨k, hk⟩ := cfg.hyp.fsu.sylow.1 ⟨((y : ↥J) : G), (inf_le_left : baum T ≤ T) y.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hR1 : R ≠ ⊥ := by
    intro h
    apply hs1
    have hmem : toModO2 M₁ J K hKJ hJM s ∈ R := ⟨⟨s, hKJ s.2⟩, hsS, Subtype.ext rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hTM₁ : T ≤ M₁ := (SecE.le_normalizer_baum T).trans (le_sup_left.trans cfg.hM₁.2)
  have hTS : IsSylowTwoOf T M₁ :=
    ⟨hTM₁, cfg.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le cfg.hyp.fsu.sylow hTM₁⟩
  have hTJ : IsSylowTwoOf (T ⊓ J) J :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp cfg.hJ) hTS
  have hsurj : Function.Surjective (toModO2 M₁ J J le_rfl hJM) := by
    rw [← MonoidHom.range_eq_top, range_toModO2, Subgroup.subgroupOf_self]
  set P : Subgroup ↥(modO2Image M₁ J) :=
    ((T ⊓ J).subgroupOf J).map (toModO2 M₁ J J le_rfl hJM) with hP
  have hTJ' : IsSylowTwoOf ((T ⊓ J).subgroupOf J) ⊤ := by
    refine ⟨le_top, hTJ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTJ.1).symm, ?_⟩
    show ¬ 2 ∣ ((T ⊓ J).subgroupOf J).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hTJ.2.2
  have hPs : IsSylowTwoOf P ⊤ := A312.isSylowTwoOf_top_map _ hsurj hTJ'
  have hPR : P ≤ Subgroup.normalizer (R : Set ↥(modO2Image M₁ J)) := by
    rintro _ ⟨t, ht, rfl⟩
    have htS := SecE.le_normalizer_baum T (Subgroup.mem_subgroupOf.mp ht).1
    rw [Subgroup.mem_normalizer_iff]
    intro r
    obtain ⟨u, rfl⟩ := hsurj r
    constructor
    · rintro ⟨u', hu', hu'u⟩
      refine ⟨t * u' * t⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp htS _).mp (Subgroup.mem_subgroupOf.mp hu')
      · rw [map_mul, map_mul, map_inv, hu'u]
    · rintro ⟨u', hu', hu'u⟩
      refine ⟨t⁻¹ * u' * t, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp htS ((t⁻¹ * u' * t : ↥J) : G)).mpr (by
          simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp hu')
        exact h1
      · rw [map_mul, map_mul, map_inv, hu'u]
        group
  have hxM := hB0M hxB
  have hxNJ := mk_mem_normalizer hxM (hB0J hxB)
  set φ := (modO2Image M₁ J).normalizerMonoidHom ⟨_, hxNJ⟩ with hφdef
  have hφ : ∀ y : ↥(modO2Image M₁ J), ((φ y : ↥(modO2Image M₁ J)) :
      ↥M₁ ⧸ CFSG.pCore 2 ↥M₁) = QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨x, hxM⟩ * y *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨x, hxM⟩)⁻¹ := fun y => rfl
  have hφR : ∀ r ∈ R, φ r ∈ R := by
    rintro _ ⟨y, hy, rfl⟩
    have hyS : ((y : ↥J) : G) ∈ baum T := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hB0J hxB) y).mp y.2⟩,
      (Subgroup.mem_normalizer_iff.mp (hB0S hxB) y).mp hyS, Subtype.ext ?_⟩
    rw [hφ, toModO2_coe, toModO2_coe, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hxpow : x ^ (2 ^ n - 1) = 1 := pow_eq_one h37 h38 cfg.hyp cfg.case1 hxL0 hxN hxo
  have hφm : φ ^ (2 ^ n - 1) = 1 := by
    have h1 : (⟨_, hxNJ⟩ : ↥(Subgroup.normalizer
        (modO2Image M₁ J : Set (↥M₁ ⧸ CFSG.pCore 2 ↥M₁)))) ^ (2 ^ n - 1) = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
      have : (⟨x, hxM⟩ : ↥M₁) ^ (2 ^ n - 1) = 1 := Subtype.ext (by simpa using hxpow)
      rw [this, map_one]
    rw [hφdef, ← map_pow, h1, map_one]
  have hcen := mul_inv_mem_center hc.2 hPs hPR hRp hR1 φ hφR (coprime_two_pow_sub_one hn) hφm
  have hmap : K'.map φ.toMonoidHom ≤ K' := by
    refine le_of_le_sup_center ?_ ?_
    · rw [← Subgroup.map_commutator, hK'p]
    · rintro _ ⟨y, hy, rfl⟩
      have hcy := hcen y
      have e : φ y = y * (φ y * y⁻¹) := by
        calc φ y = (φ y * y⁻¹) * y := by group
          _ = y * (φ y * y⁻¹) := (Subgroup.mem_center_iff.mp hcy y).symm
      show φ y ∈ K' ⊔ Subgroup.center ↥(modO2Image M₁ J)
      rw [e]
      exact Subgroup.mul_mem_sup hy hcy
  have hle : K.map (MulAut.conj x).toMonoidHom ≤ K ⊔ pCoreOf 2 M₁ := by
    rintro _ ⟨k, hk, rfl⟩
    have hkM : x * k * x⁻¹ ∈ M₁ :=
      M₁.mul_mem (M₁.mul_mem hxM (hJM (hKJ hk))) (M₁.inv_mem hxM)
    show x * k * x⁻¹ ∈ K ⊔ pCoreOf 2 M₁
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

theorem b0_le_normalizer_of_odd
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) {T L I H K M₁ J : Subgroup G} {n m : ℕ}
    (cfg : B0KConfig G T L I H K M₁ J n m) (hc : B0KTypeC M₁ K J) (hn : Odd n) :
    B0 T L ≤ Subgroup.normalizer (K : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxL0, hxN⟩, hxo⟩
  have hxo' : Odd (orderOf x⁻¹) := by rwa [orderOf_inv]
  exact mem_normalizer_of_map_le
    (map_conj_le_of_odd hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS cfg hc hn hxL0
      hxN hxo)
    (map_conj_le_of_odd hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS cfg hc hn
      ((fsuL0 T L).inv_mem hxL0) (Subgroup.inv_mem _ hxN) hxo')

end C11AmS.K7

end CFSG.Quasithin.Vol2.Ch10.SecB
