module

public import CFSG.RankThree.PartOne.KF.F132Row3
public import CFSG.RankThree.PartOne.KLAY.D4Outer
public import CFSG.RankThree.PartOne.KF.F132DihGen
public import CFSG.RankThree.PartOne.KF.F132SL2Torus
public import CFSG.RankThree.PartOne.KF.R3Final
public import CFSG.RankThree.PartOne.KFOUT3.KtyD4Ctx
public import CFSG.RankThree.PartOne.KFOUT3.KtyG2Act
public import CFSG.RankThree.PartOne.KFOUT3.KtyDihCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KLAY
  CFSG.RankThree.PartOne.KFOUT3

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem row3_wctx
    {F : Subgroup G} {K : Type} [Field K] {σ : K →+* K} (hP : D4Param p f K σ) (hFL : F ≤ L)
    (hFexp : ∀ x ∈ F, x ^ p = 1)
    (ε : ↥L →* DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ))
    (hε : IsCentralPQuot p ε)
    (hFT₁ : ∀ t ∈ Tp3 hP, ∃ x : F, ε (Subgroup.inclusion hFL x) = d4Q hP t)
    (hFT₂ : ∀ x : F, ∃ t ∈ Tp3 hP, ε (Subgroup.inclusion hFL x) = d4Q hP t) :
    ∃ S : WCtx (g2Act (K := K) hP.prime hP.five_le) L F,
      ∀ d, ε (Subgroup.inclusion hFL (S.tor d)) = d4Q hP (tp3M hP d) := by
  classical
  have hp := hP.prime
  have h5 := hP.five_le
  have : Finite K := hP.finite
  obtain ⟨SM, hSM⟩ := exists_wctx_d4' hP (d4tau p K) (fun a b => tp3Hom_d4tau a b)
  have hVexp : ∀ d : G2V p K, d ^ p = 1 := fun d =>
    funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
  obtain ⟨S₁, hrel₁⟩ := wctx_ofCentralQuot' hVexp SM (d4Q hP) (isCentralPQuot_d4Q hP) ε hε hFL
    hFexp hFT₁ hFT₂
  have hmem : ∀ γ : DihedralGroup 6, g2Act (K := K) hp h5 γ ∈
      Subgroup.closure (Set.range (d4tau p K)) := by
    intro γ
    rw [range_d4tau]
    exact pairAct_mem_closure g2s0_mul_self g2s1_mul_self (g2_braid hp h5) γ
  let f₁ : DihedralGroup 6 →* ↥(Subgroup.closure (Set.range (d4tau p K))) :=
    (g2Act (K := K) hp h5).codRestrict _ hmem
  have hf₁ : Function.Surjective f₁ := by
    rintro ⟨x, hx⟩
    rw [range_d4tau] at hx
    obtain ⟨γ, hγ⟩ := exists_pairAct_of_mem_closure (by decide) g2s0_mul_self g2s1_mul_self
      (g2_braid hp h5) hx
    exact ⟨γ, Subtype.ext hγ⟩
  let S := wctxPull (act := g2Act (K := K) hp h5) f₁ hf₁ (fun γ => rfl) S₁
  refine ⟨S, fun d => ?_⟩
  show ε (Subgroup.inclusion hFL (S₁.tor d)) = _
  rw [hrel₁ d, hSM d]

theorem row3_layer0 (h : Sec12Hyp G p A c L E)
    (hEA : E = A) (hEeq : E = (E ⊓ L) ⊔ Subgroup.zpowers c)
    {K : Type} [Field K] {σ : K →+* K} (hP : D4Param p f K σ)
    (ε : ↥L →* DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ))
    (hε : IsCentralPQuot p ε) (S : WCtx (g2Act (K := K) hP.prime hP.five_le) L (E ⊓ L))
    (hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = d4Q hP (tp3M hP d))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp3 hP).map (d4Q hP))
    {z : rootsOfUnity p K} (hz : IsPrimitiveRoot (z : Kˣ) p) :
    ∃ K₀ : Subgroup G, LayerCore p A L ((S.tor ![1, z] : ↥(E ⊓ L)) : G) K₀ ∧
      StatedClassicalModel (↥K₀ ⧸ Subgroup.center ↥K₀) .PSL 2 2 f := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := Sec12Three.five_le h; omega
  have : Finite K := hP.finite
  have hchar : CharP K 2 := ringChar.of_eq hP.ringChar_eq_two
  obtain ⟨k, hkmem, hkcard⟩ := exists_fixedField hP
  have hkchar : CharP ↥k 2 := inferInstance
  have hζp : (z : Kˣ) ^ p = 1 := hz.pow_eq_one
  have hz1 : z ≠ 1 := g2v_ne_one_of_primitive hp.one_lt hz
  have hf3 := three_le_of_dvd hP.five_le hP.one_le hP.dvd
  obtain ⟨χ, hχ⟩ := exists_unit_of_mem k (z : Kˣ) ((hkmem _).2 (hP.sigma_fix (z : Kˣ) hζp))
  have hζ' : IsPrimitiveRoot χ p := by
    refine IsPrimitiveRoot.of_map_of_injective (f := Units.map (k.subtype : ↥k →* K)) ?_
      (Units.map_injective k.subtype.injective)
    rw [hχ]
    exact hz
  have hSL := d4_SL2Torus_two hP hz k hkmem
  have hD := d4_layerD_two hP (z := z) hz k hkmem hkcard
  have hbA : ((S.tor ![1, z] : ↥(E ⊓ L)) : G) ∈ A := hEA ▸ (S.tor ![1, z]).2.1
  have hbL : ((S.tor ![1, z] : ↥(E ⊓ L)) : G) ∈ L := (S.tor ![1, z]).2.2
  have hb1 : ((S.tor ![1, z] : ↥(E ⊓ L)) : G) ≠ 1 := by
    intro h1
    have h2 : S.tor ![1, z] = 1 := Subtype.ext h1
    have h3 : (![1, z] : G2V p K) = 1 := (map_eq_one_iff S.tor S.tor.injective).1 h2
    exact hz1 (by simpa using congrFun h3 1)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hEeq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  exact layerCore_of_SL2Torus hp hp2 (IsPGroup.of_card h.A_card) h.A_elem
    h.L_le_centralizer hA ε (d4Q hP) hε (isCentralPQuot_d4Q hP) hbA hbL hb1
    (Tp3_exp hP _ (tp3M_mem_Tp3 hP _)) (hrel ![1, z]) hAT hkcard (by omega) ⟨χ, hζ'⟩ hSL hD

theorem row3_layer1 (h : Sec12Hyp G p A c L E)
    (hEA : E = A) (hEeq : E = (E ⊓ L) ⊔ Subgroup.zpowers c)
    {K : Type} [Field K] {σ : K →+* K} (hP : D4Param p f K σ)
    (ε : ↥L →* DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ))
    (hε : IsCentralPQuot p ε) (S : WCtx (g2Act (K := K) hP.prime hP.five_le) L (E ⊓ L))
    (hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = d4Q hP (tp3M hP d))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp3 hP).map (d4Q hP))
    {z : rootsOfUnity p K} (hz : IsPrimitiveRoot (z : Kˣ) p) :
    ∃ K₁ : Subgroup G, LayerCore p A L ((S.tor ![z, 1] : ↥(E ⊓ L)) : G) K₁ ∧
      StatedClassicalModel (↥K₁ ⧸ Subgroup.center ↥K₁) .PSL 2 2 (3 * f) := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := Sec12Three.five_le h; omega
  have : Finite K := hP.finite
  have hchar : CharP K 2 := ringChar.of_eq hP.ringChar_eq_two
  have hz1 : z ≠ 1 := g2v_ne_one_of_primitive hp.one_lt hz
  have hSL := d4_SL2Torus_three hP hz
  have hD := d4_layerD_three hP hz
  have hkg : Nat.card K = 2 ^ (3 * f) := by
    rw [hP.card, ← pow_mul, mul_comm]
  have hbA : ((S.tor ![z, 1] : ↥(E ⊓ L)) : G) ∈ A := hEA ▸ (S.tor ![z, 1]).2.1
  have hbL : ((S.tor ![z, 1] : ↥(E ⊓ L)) : G) ∈ L := (S.tor ![z, 1]).2.2
  have hb1 : ((S.tor ![z, 1] : ↥(E ⊓ L)) : G) ≠ 1 := by
    intro h1
    have h2 : S.tor ![z, 1] = 1 := Subtype.ext h1
    have h3 : (![z, 1] : G2V p K) = 1 := (map_eq_one_iff S.tor S.tor.injective).1 h2
    exact hz1 (by simpa using congrFun h3 0)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hEeq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have hf1 := hP.one_le
  exact layerCore_of_SL2Torus hp hp2 (IsPGroup.of_card h.A_card) h.A_elem
    h.L_le_centralizer hA ε (d4Q hP) hε (isCentralPQuot_d4Q hP) hbA hbL hb1
    (Tp3_exp hP _ (tp3M_mem_Tp3 hP _)) (hrel ![z, 1]) hAT hkg (by omega) ⟨(z : Kˣ), hz⟩ hSL hD

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KF132 CFSG.RankThree.PartOne.KFU
  CFSG.Blueprint CFSG.RankThree.PartOne.KFOUT3 CFSG.RankThree.PartOne.KLAY

theorem kf132At_row3
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hECS : ExceptionalCenterSmallPrimes) : KF132At 3 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9 t ht htL
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hrep : ExceptionalRep (L ⧸ Subgroup.center L) := by
    rcases hmod with ⟨hcl, -⟩ | ⟨-, ht, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
    · exact absurd hcl (by decide)
    · exact Or.inl ⟨.trialityD4, 2, f, ht, hexc⟩
    · exact absurd hrt (by decide)
    · exact absurd ht (by decide)
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_exceptional hECS hF hrep
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, σ, hP, ⟨ζ, hζ⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r3frame_of hcore hf1 hpq hmod
  obtain ⟨S, hrel⟩ := row3_wctx hP hcore.F_le hcore.F_exp ε hε hFT₁ hFT₂
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp3 hP).map (d4Q hP) := by
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp⟩
  have hz : IsPrimitiveRoot (z : Kˣ) p := hζ
  obtain ⟨K₀, hd₀, hm₀⟩ := row3_layer0 h hEA hG.E_eq hP ε hε S hrel hAT hz
  obtain ⟨K₁, hd₁, hm₁⟩ := row3_layer1 h hEA hG.E_eq hP ε hε S hrel hAT hz
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hv₀ : g2Act (K := K) hP.prime hP.five_le (DihedralGroup.sr 0) ![1, z] = ![1, z] := by
    rw [g2Act_sr_zero]
    exact g2v_ext (by simp [g2s0_apply_zero]) (by simp [g2s0_apply_one])
  have hv₁ : g2Act (K := K) hP.prime hP.five_le (DihedralGroup.sr 1) ![z, 1] = ![z, 1] := by
    rw [g2Act_sr_one]
    exact g2v_ext (by simp [g2s1_apply_zero]) (by simp [g2s1_apply_one])
  have hmov0 : Nat.card (movedV (g2Act (K := K) hP.prime hP.five_le (DihedralGroup.sr 0))) = p := by
    rw [g2Act_sr_zero]
    exact card_movedV_g2s0 hP.prime hP.five_le hζex
  have hmov1 : Nat.card (movedV (g2Act (K := K) hP.prime hP.five_le (DihedralGroup.sr 1))) = p := by
    rw [g2Act_sr_one]
    exact card_movedV_g2s1 hP.prime hP.five_le hζex
  have key := kfAt_dih_classes hGA h hF13 hEA hG (Or.inr (Or.inl rfl)) S
    (g2Act_injective hP.prime hP.five_le hζex) (g2Act_refl hP.prime hP.five_le hζex) hmov0 hmov1
    hv₀ hv₁ hd₀ hf3 hm₀ hd₁ (by omega) hm₁
  rcases key t ht htL with h0 | h1
  · exact ⟨f, f, ⟨hf1, hpq, hmod⟩, Or.inl rfl, h0⟩
  · exact ⟨f, 3 * f, ⟨hf1, hpq, hmod⟩, Or.inr rfl, h1⟩

theorem kf132Types_row3
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hECS : ExceptionalCenterSmallPrimes) : KF132Types 3 :=
  kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row3 hGA hECS)

end CFSG.RankThree.PartOne.S13K
