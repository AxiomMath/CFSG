module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrame
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeOddIndex
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextRankAux
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeTwFrob
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeTwTransport
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeTwLongest
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeConj
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6GraphNone

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem split_context_rank
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .E6 n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU .E6 n f).D .E6 n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : 3 ∣ 2 ^ f - 1)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {I : Subgroup (MulAut (ggG0 3 B x L D J))}
    (R : ShapeRealization (ggG0 3 B x L D J) I Ω)
    (hI : contextImage (ggG0 3 B x L D J) Bs ≤ I) :
    3 ^ 5 ≤ Nat.card (realizedSubgroup R (contextImage (ggG0 3 B x L D J) B)) := by
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hperf : commutator ↥(ggG0 3 B x L D J) = ⊤ := hctx.2.2.2.2.2.1.1
  have hC : Subgroup.centralizer (ggG0 3 B x L D J : Set G) = ⊥ := s1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange, -⟩ :=
    NoOffE6Three.exists_injective_factor_E6_comp ψ hker hCψ
  have hχG0 : χ.range = ggG0 3 B x L D J := hχrange.trans hrange
  have hZ : Subgroup.center (adjointGroup .E6 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot (τ := .E6) (K := GaloisField 2 f)
  obtain ⟨θ⟩ := NormalizerAut.nonempty_quotient_center_mulEquiv χ hχinj hZ hχG0
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hshape
  have hlift : GGTorusLift 3 5 (adjointGroup .E6 (GaloisField 2 f)) :=
    TableBExc.ggTorusLift_adjoint_E6_three h3
  have h5rank : 5 ≤ LargeEvenTwoLocalRank 3 G :=
    le_twoLocalRank_of_torusLift Nat.prime_three hperf θ hlift
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have hB5 : 3 ^ 5 ≤ Nat.card B := by
    rw [hBc]
    exact Nat.pow_le_pow_right (by norm_num) h5rank
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hctx.2.2.2.2.2.2.1.1
  have hBN : B ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hctx.2.1.1.trans hBsN
  have hfinj : Function.Injective (Subgroup.normalizerMonoidHom (ggG0 3 B x L D J)) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC]
    exact Subgroup.bot_subgroupOf _
  have hEI : contextImage (ggG0 3 B x L D J) B ≤ I := by
    rw [contextImage]
    exact (Subgroup.map_mono (Subgroup.comap_mono hctx.2.1.1)).trans hI
  have hcard : Nat.card (realizedSubgroup R (contextImage (ggG0 3 B x L D J) B)) =
      Nat.card B := by
    rw [realizedSubgroup, Subgroup.card_map_of_injective R.action_injective]
    rw [← Subgroup.card_map_of_injective I.subtype_injective
      (K := (contextImage (ggG0 3 B x L D J) B).comap I.subtype),
      Subgroup.map_comap_eq_self (by simpa only [Subgroup.range_subtype] using hEI)]
    rw [contextImage, Subgroup.card_map_of_injective hfinj]
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      (K := B.comap (Subgroup.normalizer (ggG0 3 B x L D J : Set G)).subtype),
      Subgroup.map_comap_eq_self (by simpa only [Subgroup.range_subtype] using hBN)]
  rw [hcard]
  exact hB5

private theorem exists_two_subgroup_meets_inner
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ Q ≤ ggG0 3 B x L D J ∧
      B ≤ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hctx.stdType.2.1
  set M : Subgroup G := ggM 3 B x L D J with hM
  have hDM : D ≤ Subgroup.normalizer (T : Set G) := hctx.stdSub.1.1.trans hBT
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · rw [Nat.coprime_pow_right_iff hkpos]; norm_num
  have hTM : T ≤ M := s1.2.2.1 T hDM hcop
  have hBM : B ≤ M := hctx.2.1.1.trans hctx.bstar_le_normalizer
  have hG1M : ggG1 ψ ≤ M := ggG1_le_ggM hctx.range_eq
  have hG1N : ggG1 ψ ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hG1M
  have hBG1 : B ≤ ggG1 ψ := hctx.2.1.1.trans (ggBs_le_ggG1 hctx)
  haveI hG0G1N : ((ggG0 3 B x L D J).subgroupOf (ggG1 ψ)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hG1N
  have hSt : ∀ m ∈ Subgroup.normalizer (ψ.range : Set G), ∃ g ∈ ψ.range,
      GGRootAdmissible (ggU .twistedE6 n f).D ψ (m * g) := by
    intro m hm
    rw [hctx.range_eq] at hm ⊢
    exact ggSteinbergCorrectionAt_twistedE6 G n f ψ _ ⟨hctx.2.2.2.1,
      ⟨hctx.range_eq, hctx.2.2.2.2.1.2⟩, hctx.perfect, hctx.lieModel⟩ m hm
  have hG1conj : ∀ m ∈ M, ∀ c ∈ ggG1 ψ, m * c * m⁻¹ ∈ ggG1 ψ :=
    fun m hm c hc => ggG1_conj_mem_of_steinberg hctx.range_eq hSt m hm c hc
  have hG0conj : ∀ m ∈ M, ∀ n ∈ ggG0 3 B x L D J, m * n * m⁻¹ ∈ ggG0 3 B x L D J := by
    intro m hm n hn
    exact (Subgroup.mem_set_normalizer_iff.mp hm n).mp hn
  have hodd1 : Odd ((ggG0 3 B x L D J).relIndex (ggG1 ψ)) :=
    ggG1OddAt_of_modelData ggOuterInvModelDataAt_twistedE6_holds G 3 B Bs x L D J n f ψ
      hctx s1
  have hQne : T ⊓ ggG0 3 B x L D J ≠ ⊥ := by
    intro hQbot
    have hPG0 : T ⊓ ggG1 ψ ≤ ggG0 3 B x L D J := by
      let N : Subgroup (ggG1 ψ) := (ggG0 3 B x L D J).subgroupOf (ggG1 ψ)
      haveI hN : N.Normal := hG0G1N
      let f : (ggG1 ψ) →* (ggG1 ψ) ⧸ N := QuotientGroup.mk' N
      have hodd' : Odd (Nat.card ((ggG1 ψ) ⧸ N)) := hodd1
      have hPpg : IsPGroup 2 ↥(T ⊓ ggG1 ψ) := hT2.to_le (inf_le_left : T ⊓ ggG1 ψ ≤ T)
      have hT1pg : IsPGroup 2 (T.subgroupOf (ggG1 ψ)) := by
        have h := hPpg.of_equiv
          (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ ggG1 ψ ≤ ggG1 ψ)).symm
        rwa [Subgroup.inf_subgroupOf_right] at h
      let R : Subgroup ((ggG1 ψ) ⧸ N) := (T.subgroupOf (ggG1 ψ)).map f
      have hRpg : IsPGroup 2 R := hT1pg.map f
      obtain ⟨k, hk⟩ := hRpg.exists_card_eq
      have hdvd : 2 ^ k ∣ Nat.card ((ggG1 ψ) ⧸ N) := by
        rw [← hk]; exact Subgroup.card_subgroup_dvd_card R
      have hcop2 : Nat.Coprime (2 ^ k) (Nat.card ((ggG1 ψ) ⧸ N)) := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0; simp
        · rw [Nat.coprime_pow_left_iff hkpos]
          exact hodd'.coprime_two_left
      have hk1 : 2 ^ k = 1 := Nat.eq_one_of_dvd_coprimes hcop2 dvd_rfl hdvd
      have hRbot : R = ⊥ := Subgroup.eq_bot_of_card_eq R (by rw [hk, hk1])
      intro x hx
      have hxT : x ∈ T := hx.1
      have hxG1 : x ∈ ggG1 ψ := hx.2
      have hxmap : f ⟨x, hxG1⟩ ∈ R :=
        Subgroup.mem_map_of_mem f
          (show (⟨x, hxG1⟩ : ggG1 ψ) ∈ T.subgroupOf (ggG1 ψ) from hxT)
      rw [hRbot, Subgroup.mem_bot] at hxmap
      exact (QuotientGroup.eq_one_iff (N := N) (x := (⟨x, hxG1⟩ : ggG1 ψ))).mp hxmap
    have hPbot : T ⊓ ggG1 ψ = ⊥ := by
      have hle : T ⊓ ggG1 ψ ≤ T ⊓ ggG0 3 B x L D J := le_inf inf_le_left hPG0
      rw [hQbot] at hle
      exact le_bot_iff.mp hle
    have hcommle : ⁅T, B⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro t ht b hb
      have hmemT : t * b * t⁻¹ * b⁻¹ ∈ T := by
        have hbt : b * t⁻¹ * b⁻¹ ∈ T :=
          (Subgroup.mem_set_normalizer_iff.mp (hBT hb) t⁻¹).mp (T.inv_mem ht)
        have hprod : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
        rw [hprod]
        exact T.mul_mem ht hbt
      have hmemG1 : t * b * t⁻¹ * b⁻¹ ∈ ggG1 ψ :=
        (ggG1 ψ).mul_mem (hG1conj t (hTM ht) b (hBG1 hb)) ((ggG1 ψ).inv_mem (hBG1 hb))
      have hmem : t * b * t⁻¹ * b⁻¹ ∈ T ⊓ ggG1 ψ := ⟨hmemT, hmemG1⟩
      rw [hPbot, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot, commutatorElement_def]
      exact hmem
    exact hTB (le_bot_iff.mp hcommle)
  refine ⟨T ⊓ ggG0 3 B x L D J, hQne, hT2.to_le inf_le_left, inf_le_right, ?_⟩
  intro b hb
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  constructor
  · rintro ⟨hnT, hnG⟩
    exact ⟨(Subgroup.mem_set_normalizer_iff.mp (hBT hb) n).mp hnT,
      hG0conj b (hBM hb) n hnG⟩
  · rintro ⟨hnT, hnG⟩
    refine ⟨(Subgroup.mem_set_normalizer_iff.mp (hBT hb) n).mpr hnT, ?_⟩
    have h := hG0conj b⁻¹ (M.inv_mem (hBM hb)) (b * n * b⁻¹) hnG
    have hprod : (b⁻¹) * (b * n * b⁻¹) * (b⁻¹)⁻¹ = n := by group
    rwa [hprod] at h

theorem twisted_context_root
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {I : Subgroup (MulAut (ggG0 3 B x L D J))}
    (R : ShapeRealization (ggG0 3 B x L D J) I Ω)
    (hI : contextImage (ggG0 3 B x L D J) Bs ≤ I)
    (hT : realizedSubgroup R (contextImage (ggG0 3 B x L D J) Bs) ≤ torusGroup .E6 Ω)
    (hs : ∀ α, R.setup.ρ α = -α) :
    ∃ α, IsRoot .E6 α ∧ ∀ u : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit .E6 u ∈ realizedSubgroup R (contextImage (ggG0 3 B x L D J) B) →
      rootChar u α = 1 := by
  have hΦ : ∃ Fr : Ω →+* Ω, (∀ c, Fr c = c ^ R.setup.D.q) ∧
      R.setup.D.Φ = twistHom .E6 Ω Fr := twisted_frobenius_form R.setup hs
  have hAlg : R.setup.IsAlgebraic := langSetup_isAlgebraic_of_halg R.setup halg
  have hd : R.setup.DescendsTwE6 := R.setup.descendsTwE6 hΦ hAlg
  let A₀ : Subgroup (ModGL .E6 Ω) :=
    realizedSubgroup R (contextImage (ggG0 3 B x L D J) B)
  have hA₀model : A₀ ≤ R.setup.D.model := by
    intro y hy
    obtain ⟨φ, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact R.action_mem φ
  have hA₀torus : A₀ ≤ torusGroup .E6 Ω := by
    refine (Subgroup.map_mono (Subgroup.comap_mono ?_)).trans hT
    rw [contextImage, contextImage]
    exact Subgroup.map_mono (Subgroup.comap_mono hctx.2.1.1)
  obtain ⟨K, hF, hFin, hAlgΩ, σ, e, A, hK, hσ, hIcl, hAI, hcard, hrel, he⟩ :=
    twisted_descend_torus R.setup hΦ hd hAlg A₀ hA₀model
  obtain ⟨hIcl'⟩ := hIcl
  haveI : IsAlgClosure K Ω := hIcl'
  have hA₀t : A₀ ≤ R.setup.D.torus := by
    intro y hy
    exact ⟨hA₀torus hy, (Subgroup.mem_inf.mp (hA₀model hy)).2⟩
  obtain ⟨v, hv⟩ := R.setup.D.n_weyl
  have hσ' : ∀ c : K, σ c = c ^ R.setup.D.q := by
    intro c
    apply (algebraMap K Ω).injective
    rw [map_pow]
    exact hσ c
  obtain ⟨Dtw, hDv, hkill⟩ :=
    twisted_langData_of_setup σ R.setup.D.q hK hσ' R.setup rfl hΦ A hAI A₀
      (fun y hy => ⟨hA₀t hy, hA₀model hy⟩) hrel hv
  have hlong : TwE6RootKill.IsLongest v := twisted_isLongest R.setup hΦ hs hv
  have hlongD : TwE6RootKill.IsLongest Dtw.v := hDv ▸ hlong
  haveI hCK2 : CharP K 2 := ⟨fun x => by
    rw [← (algebraMap K Ω).injective.eq_iff, map_zero, map_natCast,
      CharP.cast_eq_zero_iff Ω 2 x]⟩
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have hodd : Odd (Nat.card A) := by
    have hEI : contextImage (ggG0 3 B x L D J) B ≤ I := by
      rw [contextImage]
      exact (Subgroup.map_mono (Subgroup.comap_mono hctx.2.1.1)).trans hI
    have hfinj : Function.Injective (Subgroup.normalizerMonoidHom (ggG0 3 B x L D J)) := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, s1.1]
      exact Subgroup.bot_subgroupOf _
    have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
      hctx.2.2.2.2.2.2.1.1
    have hBN : B ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
      hctx.2.1.1.trans hBsN
    have hA0card : Nat.card A₀ = Nat.card B := by
      change Nat.card (realizedSubgroup R (contextImage (ggG0 3 B x L D J) B)) = Nat.card B
      rw [realizedSubgroup, Subgroup.card_map_of_injective R.action_injective]
      rw [← Subgroup.card_map_of_injective I.subtype_injective
        (K := (contextImage (ggG0 3 B x L D J) B).comap I.subtype),
        Subgroup.map_comap_eq_self (by simpa only [Subgroup.range_subtype] using hEI)]
      rw [contextImage, Subgroup.card_map_of_injective hfinj]
      rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
        (K := B.comap (Subgroup.normalizer (ggG0 3 B x L D J : Set G)).subtype),
        Subgroup.map_comap_eq_self (by simpa only [Subgroup.range_subtype] using hBN)]
    rw [hcard, hA0card, hctx.1.2.2.2.2.2.2.1.1.2.1]
    exact Odd.pow (by norm_num : Odd 3)
  have hodd1 : Odd ((ggG0 3 B x L D J).relIndex (ggG1 ψ)) :=
    ggG1OddAt_of_modelData ggOuterInvModelDataAt_twistedE6_holds G 3 B Bs x L D J n f ψ
      hctx s1
  have hBsG1 : Bs ≤ ggG1 ψ := ggBs_le_ggG1 hctx
  have hU : TwE6RootKill.TwNormTwo K σ A := by
    obtain ⟨Q, hQne, hQ2, hQle, hQnorm⟩ := exists_two_subgroup_meets_inner hctx s1
    let Q' : Subgroup ↥R.setup.Γ :=
      (Q.subgroupOf (ggG0 3 B x L D J)).map R.groupEquiv.toMonoidHom
    let U : Subgroup (ModGL TwistTag.E6.tag K) :=
      (Q'.map e.symm.toMonoidHom).map (twistedE6RootGroup K σ).subtype
    have hUroot : U ≤ twistedE6RootGroup K σ := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hUne : U ≠ ⊥ := by
      intro hbot
      apply hQne
      have h3 : Q'.map e.symm.toMonoidHom = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (H := Q'.map e.symm.toMonoidHom)
          (Subgroup.subtype_injective (twistedE6RootGroup K σ))).mp hbot
      have h2 : Q' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (H := Q') e.symm.injective).mp h3
      have h1 : Q.subgroupOf (ggG0 3 B x L D J) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective
          (H := Q.subgroupOf (ggG0 3 B x L D J)) R.groupEquiv.injective).mp h2
      rw [Subgroup.subgroupOf_eq_bot] at h1
      rw [disjoint_iff_inf_le, inf_eq_left.mpr hQle] at h1
      exact le_bot_iff.mp h1
    have hU2 : IsPGroup 2 U := by
      have h1 : IsPGroup 2 (Q.subgroupOf (ggG0 3 B x L D J)) :=
        hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQle).symm
      have h2 : IsPGroup 2 Q' := h1.map R.groupEquiv.toMonoidHom
      have h3 : IsPGroup 2 (Q'.map e.symm.toMonoidHom) := h2.map e.symm.toMonoidHom
      exact h3.map (twistedE6RootGroup K σ).subtype
    have hAU : A ≤ Subgroup.normalizer (U : Set (ModGL TwistTag.E6.tag K)) := by
      let ι : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 Ω := baseChangeGL (algebraMap K Ω)
      have hrel' : A.map ((MulAut.conj R.setup.D.g0⁻¹).toMonoidHom.comp ι) = A₀ := hrel
      have hQinv : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q := fun b hb q hq =>
        (Subgroup.mem_set_normalizer_iff.mp (hQnorm hb) q).mp hq
      let Q'' : Subgroup (ModGL Tag.E6 Ω) := Q'.map (R.setup.Γ).subtype
      have hA₀Q'' : A₀ ≤ Subgroup.normalizer (Q'' : Set (ModGL Tag.E6 Ω)) := by
        rw [Subgroup.le_normalizer_iff]
        intro a₀ ha₀ z hz
        obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp ha₀
        have hφ' : φ.1 ∈ contextImage (ggG0 3 B x L D J) B := hφ
        rw [contextImage] at hφ'
        obtain ⟨b, hb, hbφ⟩ := Subgroup.mem_map.mp hφ'
        obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz'
        have hwb : φ.1 w ∈ Q.subgroupOf (ggG0 3 B x L D J) := by
          rw [Subgroup.mem_subgroupOf]
          have hconj : ((φ.1 w : ↥(ggG0 3 B x L D J)) : G) = b * (w : G) * b⁻¹ := by
            rw [← hbφ]
            exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
          rw [hconj]
          exact hQinv b (Subgroup.mem_comap.mp hb) (w : G) (Subgroup.mem_subgroupOf.mp hw)
        rw [Subgroup.mem_map]
        exact ⟨R.groupEquiv (φ.1 w), Subgroup.mem_map.mpr ⟨φ.1 w, hwb, rfl⟩,
          R.compatible φ w⟩
      have hιe : ∀ h : twistedE6RootGroup K σ,
          ι (h : ModGL TwistTag.E6.tag K) =
            R.setup.D.g0 * (e h : ModGL Tag.E6 Ω) * R.setup.D.g0⁻¹ := by
        intro h
        show baseChangeGL (algebraMap K Ω) (h : ModGL TwistTag.E6.tag K) =
          R.setup.D.g0 * (e h : ModGL Tag.E6 Ω) * R.setup.D.g0⁻¹
        rw [he h]
        group
        rfl
      rw [Subgroup.le_normalizer_iff]
      intro a ha u hu
      have hu' : u ∈ twistedE6RootGroup K σ := hUroot hu
      have heu : e ⟨u, hu'⟩ ∈ Q' := by
        obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hu
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
        have hyv : y = (⟨u, hu'⟩ : ↥(twistedE6RootGroup K σ)) := by
          apply Subtype.ext
          exact hyu
        rw [← hyv, ← hzy]
        show e (e.symm z) ∈ Q'
        rw [MulEquiv.apply_symm_apply]
        exact hz
      have hy : R.setup.D.g0⁻¹ * ι a * R.setup.D.g0 ∈ A₀ := by
        have h1 : R.setup.D.g0⁻¹ * ι a * R.setup.D.g0 ∈
            A.map ((MulAut.conj R.setup.D.g0⁻¹).toMonoidHom.comp ι) := by
          rw [Subgroup.mem_map]
          exact ⟨a, ha, by
            change (MulAut.conj (R.setup.D.g0⁻¹)) (ι a) =
              R.setup.D.g0⁻¹ * ι a * R.setup.D.g0
            rw [MulAut.conj_apply]
            group⟩
        rwa [hrel'] at h1
      have hw : ((e ⟨u, hu'⟩ : ↥R.setup.Γ) : ModGL Tag.E6 Ω) ∈ Q'' :=
        Subgroup.mem_map.mpr ⟨e ⟨u, hu'⟩, heu, rfl⟩
      have hyw : (R.setup.D.g0⁻¹ * ι a * R.setup.D.g0) *
          ((e ⟨u, hu'⟩ : ↥R.setup.Γ) : ModGL Tag.E6 Ω) *
          (R.setup.D.g0⁻¹ * ι a * R.setup.D.g0)⁻¹ ∈ Q'' :=
        (Subgroup.le_normalizer_iff.mp hA₀Q'' _ hy) _ hw
      obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.mp hyw
      have hUz : (e.symm z' : ↥(twistedE6RootGroup K σ)).1 ∈ U := by
        show ((e.symm z' : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) ∈
          (Q'.map e.symm.toMonoidHom).map (twistedE6RootGroup K σ).subtype
        exact Subgroup.mem_map.mpr ⟨e.symm z', Subgroup.mem_map.mpr ⟨z', hz', rfl⟩, rfl⟩
      have hkey : a * u * a⁻¹ = (e.symm z' : ↥(twistedE6RootGroup K σ)) := by
        refine baseChangeGL_injective (algebraMap K Ω) ?_
        show ι (a * u * a⁻¹) = ι (e.symm z' : ↥(twistedE6RootGroup K σ))
        rw [map_mul, map_mul, map_inv, hιe ⟨u, hu'⟩, hιe (e.symm z')]
        have hιa : ι a =
            R.setup.D.g0 * (R.setup.D.g0⁻¹ * ι a * R.setup.D.g0) * R.setup.D.g0⁻¹ := by
          group
        have hz'' : (↑z' : ModGL Tag.E6 Ω) =
            (R.setup.D.g0⁻¹ * ι a * R.setup.D.g0) * ↑(e ⟨u, hu'⟩) *
              (R.setup.D.g0⁻¹ * ι a * R.setup.D.g0)⁻¹ := hz'eq
        rw [hιa, MulEquiv.apply_symm_apply, hz'']
        group
      rw [hkey]
      exact hUz
    exact twisted_twNormTwo σ A U hUroot hUne hU2 hAU
  obtain ⟨α, hα, hkillD⟩ :=
    twisted_root_kill σ R.setup.D.q hK hσ' h2 A hAI hodd hU Dtw hlongD
  have hkillA₀ : ∀ y ∈ A₀, ∃ a : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit .E6 a = y ∧ rootChar a α = 1 := by
    intro y hy
    have hy' : y ∈ A.map ((MulAut.conj R.setup.D.g0⁻¹).toMonoidHom.comp
        (baseChangeGL (algebraMap K Ω) : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 Ω)) := by
      rw [hrel]; exact hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy'
    obtain ⟨a, ha, hαa⟩ := hkill α hkillD x hx
    exact ⟨a, ha.trans hxy, hαa⟩
  exact twisted_kill_translate A₀ α hα hkillA₀

end CFSG.StandardType
