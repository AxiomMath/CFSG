module

public import CFSG.RankThree.PartOne.KF.F132Row2
public import CFSG.RankThree.PartOne.KF.F132DihGen
public import CFSG.RankThree.PartOne.KF.F132SL2Torus
public import CFSG.RankThree.PartOne.KF.F132G2Side
public import CFSG.RankThree.PartOne.KF.G2WctxTor
public import CFSG.RankThree.PartOne.KF.R2Final
public import CFSG.RankThree.PartOne.KFOUT3.KtyG2Act
public import CFSG.RankThree.PartOne.KFOUT3.KtyDihCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KLAY
  CFSG.RankThree.PartOne.KFOUT3 CFSG.ComponentClassification.UnbalancedCatalog

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem row2_wctx {F : Subgroup G} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (h5 : 5 ≤ p) (hFL : F ≤ L) (hFexp : ∀ x ∈ F, x ^ p = 1)
    (ε : ↥L →* AdjointQuotient .G2 K) (hε : IsCentralPQuot p ε)
    (hFT₁ : ∀ t ∈ Tp p K, ∃ x : F, ε (Subgroup.inclusion hFL x) = g2Q K t)
    (hFT₂ : ∀ x : F, ∃ t ∈ Tp p K, ε (Subgroup.inclusion hFL x) = g2Q K t) :
    ∃ S : WCtx (g2Act (K := K) hp h5) L F,
      ∀ d, ε (Subgroup.inclusion hFL (S.tor d)) = g2Q K (tpM p K d) := by
  classical
  obtain ⟨SM, hSM⟩ := exists_wctx_g2' (g2sigma p K) (fun i b => tpHom_g2sigma i b)
  have hVexp : ∀ d : G2V p K, d ^ p = 1 := fun d =>
    funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
  obtain ⟨S₁, hrel₁⟩ := wctx_ofCentralQuot' hVexp SM (g2Q K) (isCentralPQuot_g2Q p K) ε hε hFL
    hFexp hFT₁ hFT₂
  have hmem : ∀ γ : DihedralGroup 6, g2Act (K := K) hp h5 γ ∈
      Subgroup.closure (Set.range (g2sigma p K)) := by
    intro γ
    rw [range_g2sigma]
    exact pairAct_mem_closure g2s0_mul_self g2s1_mul_self (g2_braid hp h5) γ
  let f₁ : DihedralGroup 6 →* ↥(Subgroup.closure (Set.range (g2sigma p K))) :=
    (g2Act (K := K) hp h5).codRestrict _ hmem
  have hf₁ : Function.Surjective f₁ := by
    rintro ⟨x, hx⟩
    rw [range_g2sigma] at hx
    obtain ⟨γ, hγ⟩ := exists_pairAct_of_mem_closure (by decide) g2s0_mul_self g2s1_mul_self
      (g2_braid hp h5) hx
    exact ⟨γ, Subtype.ext hγ⟩
  let S := wctxPull (act := g2Act (K := K) hp h5) f₁ hf₁ (fun γ => rfl) S₁
  refine ⟨S, fun d => ?_⟩
  show ε (Subgroup.inclusion hFL (S₁.tor d)) = _
  exact (hrel₁ d).trans (congrArg (g2Q K) (hSM d))

theorem row2_layer0 (h : Sec12Hyp G p A c L E)
    (hEA : E = A) (hEeq : E = (E ⊓ L) ⊔ Subgroup.zpowers c) {f : ℕ} (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hpq : p ∣ 2 ^ f - 1)
    (ε : ↥L →* AdjointQuotient .G2 K) (hε : IsCentralPQuot p ε)
    (S : WCtx (g2Act (K := K) h.prime (Sec12Three.five_le h)) L (E ⊓ L))
    (hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = g2Q K (tpM p K d))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp p K).map (g2Q K))
    {z : rootsOfUnity p K} (hz : IsPrimitiveRoot (z : Kˣ) p) :
    ∃ K₀ : Subgroup G, LayerCore p A L ((S.tor ![1, z] : ↥(E ⊓ L)) : G) K₀ ∧
      StatedClassicalModel (↥K₀ ⧸ Subgroup.center ↥K₀) .PSL 2 2 f := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hz1 : z ≠ 1 := g2v_ne_one_of_primitive hp.one_lt hz
  have hSL := g2_SL2TorusI (K := K) hz hp.one_lt g2ia
  have hD := g2_layerD_I hp h5 hK hpq (by omega) hz g2ia
  rw [g2vec_zero] at hD
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
    h.L_le_centralizer hA ε (g2Q K) hε (isCentralPQuot_g2Q p K) hbA hbL hb1
    (Tp_exp _ (tpM_mem_Tp _)) (hrel ![1, z]) hAT hK (by omega) ⟨(z : Kˣ), hz⟩ hSL hD

theorem row2_layer1 (h : Sec12Hyp G p A c L E)
    (hEA : E = A) (hEeq : E = (E ⊓ L) ⊔ Subgroup.zpowers c) {f : ℕ} (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hpq : p ∣ 2 ^ f - 1)
    (ε : ↥L →* AdjointQuotient .G2 K) (hε : IsCentralPQuot p ε)
    (S : WCtx (g2Act (K := K) h.prime (Sec12Three.five_le h)) L (E ⊓ L))
    (hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = g2Q K (tpM p K d))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp p K).map (g2Q K))
    {z : rootsOfUnity p K} (hz : IsPrimitiveRoot (z : Kˣ) p) :
    ∃ K₁ : Subgroup G, LayerCore p A L ((S.tor ![z, 1] : ↥(E ⊓ L)) : G) K₁ ∧
      StatedClassicalModel (↥K₁ ⧸ Subgroup.center ↥K₁) .PSL 2 2 f := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hz1 : z ≠ 1 := g2v_ne_one_of_primitive hp.one_lt hz
  have hSL := g2_SL2TorusI (K := K) hz hp.one_lt g2ir
  have hD := g2_layerD_I hp h5 hK hpq (by omega) hz g2ir
  rw [g2vec_one] at hD
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
  exact layerCore_of_SL2Torus hp hp2 (IsPGroup.of_card h.A_card) h.A_elem
    h.L_le_centralizer hA ε (g2Q K) hε (isCentralPQuot_g2Q p K) hbA hbL hb1
    (Tp_exp _ (tpM_mem_Tp _)) (hrel ![z, 1]) hAT hK (by omega) ⟨(z : Kˣ), hz⟩ hSL hD

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KF132 CFSG.RankThree.PartOne.KFU
  CFSG.Blueprint CFSG.RankThree.PartOne.KFOUT3 CFSG.RankThree.PartOne.KLAY

theorem kf132At_row2
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hECS : ExceptionalCenterSmallPrimes) : KF132At 2 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9 t ht htL
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hrep : ExceptionalRep (L ⧸ Subgroup.center L) := by
    rcases hmod with ⟨hcl, -⟩ | ⟨-, ht, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
    · exact absurd hcl (by decide)
    · exact Or.inl ⟨.G2, 2, f, ht, hexc⟩
    · exact absurd hrt (by decide)
    · exact absurd ht (by decide)
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_exceptional hECS hF hrep
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hK, ⟨ζ, hζ⟩, hchar, ε, hε, hFT₁, hFT₂⟩ := exists_r2frame_of hcore hpq hmod
  obtain ⟨S, hrel⟩ := row2_wctx hp h5 hcore.F_le hcore.F_exp ε hε hFT₁ hFT₂
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp p K).map (g2Q K) := by
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
  obtain ⟨K₀, hd₀, hm₀⟩ := row2_layer0 h hEA hG.E_eq hf3 hK hpq ε hε S hrel hAT hz
  obtain ⟨K₁, hd₁, hm₁⟩ := row2_layer1 h hEA hG.E_eq hf3 hK hpq ε hε S hrel hAT hz
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hv₀ : g2Act (K := K) hp h5 (DihedralGroup.sr 0) ![1, z] = ![1, z] := by
    rw [g2Act_sr_zero]
    exact g2v_ext (by simp [g2s0_apply_zero]) (by simp [g2s0_apply_one])
  have hv₁ : g2Act (K := K) hp h5 (DihedralGroup.sr 1) ![z, 1] = ![z, 1] := by
    rw [g2Act_sr_one]
    exact g2v_ext (by simp [g2s1_apply_zero]) (by simp [g2s1_apply_one])
  have hmov0 : Nat.card (movedV (g2Act (K := K) hp h5 (DihedralGroup.sr 0))) = p := by
    rw [g2Act_sr_zero]
    exact card_movedV_g2s0 hp h5 hζex
  have hmov1 : Nat.card (movedV (g2Act (K := K) hp h5 (DihedralGroup.sr 1))) = p := by
    rw [g2Act_sr_one]
    exact card_movedV_g2s1 hp h5 hζex
  have key := kfAt_dih_classes hGA h hF13 hEA hG (Or.inr (Or.inl rfl)) S
    (g2Act_injective hp h5 hζex) (g2Act_refl hp h5 hζex) hmov0 hmov1
    hv₀ hv₁ hd₀ hf3 hm₀ hd₁ hf3 hm₁
  rcases key t ht htL with h0 | h1
  · exact ⟨f, f, ⟨hf1, hpq, hmod⟩, rfl, h0⟩
  · exact ⟨f, f, ⟨hf1, hpq, hmod⟩, rfl, h1⟩

theorem kf132Types_row2
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hECS : ExceptionalCenterSmallPrimes) : KF132Types 2 :=
  kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row2 hGA hECS)

end CFSG.RankThree.PartOne.S13K
