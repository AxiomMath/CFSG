module

public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.Generic
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCent
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofInndiag
import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofTrialityPGL
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofModel
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec11.AutThree1129

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

theorem subsingleton_of_perfect_solvable (J : Type) [Group J] [Group.IsPerfect J]
    [Group.IsSolvable J] : Subsingleton J := by
  have hall : ∀ n, derivedSeries J n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [derivedSeries_succ, ih]
      exact Group.IsPerfect.commutator_eq_top
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable J).solvable
  have htop : (⊤ : Subgroup J) = ⊥ := (hall n).symm.trans hn
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup J) := by rw [← htop]; exact Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup J) := by rw [← htop]; exact Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem card_le_27_of_model {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (h9 : ¬ Sec4.ModNine π (p ^ f))
    (P : Subgroup (MulAut (projImage (Sec4.slPi π 3 (p ^ f) K)))) (hP : IsPGroup 3 P) :
    Nat.card P ≤ 27 := by
  have hf3 : ¬ 3 ∣ f := by
    intro hf
    apply h9
    have hd := CFSG.RankThree.PartTwo.Sec15.Proof158Cartan.modNine_of_three_dvd hq hf
    cases π
    · exact hd.resolve_left (fun h1 => by simp only [Sec4.ModThree, cond_false] at hq; omega)
    · exact hd.resolve_right (fun h8 => by simp only [Sec4.ModThree, cond_true] at hq; omega)
  have := hK.finite
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  haveI : Finite (MulAut (projImage (Sec4.slPi π 3 (p ^ f) K))) :=
    Finite.of_injective (fun σ => (σ : projImage (Sec4.slPi π 3 (p ^ f) K) →
      projImage (Sec4.slPi π 3 (p ^ f) K))) fun σ τ h => MulEquiv.ext (congrFun h)
  let Φ : ↥(projImage (Sec4.glPi π 3 (p ^ f) K)) →*
      MulAut (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    (projImage (Sec4.slPi π 3 (p ^ f) K)).normalizerMonoidHom.comp
      (Subgroup.inclusion
        (CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two.projImage_glPi_le_normalizer hK))
  have hP_le : P ≤ Φ.range := by
    intro σ hσ
    obtain ⟨k, hk⟩ := hP ⟨σ, hσ⟩
    obtain ⟨y, hy, hconj⟩ :=
      CFSG.RankThree.PartTwo.Sec15.Proof158Cartan.inndiag_of_three_pow hK hq2 hf3 σ
        ⟨k, congrArg Subtype.val hk⟩
    refine MonoidHom.mem_range.mpr ⟨⟨Matrix.ProjGenLinGroup.mk y, ⟨y, hy, rfl⟩⟩, ?_⟩
    apply MulEquiv.ext
    intro m
    apply Subtype.ext
    simp only [Φ, MonoidHom.comp_apply]
    exact (hconj m).symm
  have hdvdN : Nat.card Φ.range ∣ Nat.card (projImage (Sec4.glPi π 3 (p ^ f) K)) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv]
    exact ⟨Nat.card Φ.ker, Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  have hdvdP : Nat.card P ∣ Nat.card (Sec4.slPi π 3 (p ^ f) K) := by
    rw [← CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two.card_projImage_glPi hK]
    exact (Subgroup.card_dvd_of_le hP_le).trans hdvdN
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn] at hdvdP
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h81 : 81 ∣ 3 ^ n := by
      have h := pow_dvd_pow 3 (show 4 ≤ n by omega)
      norm_num at h
      exact h
    exact CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two.not_eighty_one_dvd_card_slPi hK hq h9
      (h81.trans hdvdP)
  rw [hn]
  calc 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 27 := by norm_num

theorem not_modNine_of_block {G : Type} [Group G] [Finite G] {Y K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    (hK3 : (Nat.card K).factorization 3 = 1)
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf)) :
    ¬ Sec4.ModNine π (p ^ f) := by
  intro h9
  obtain ⟨g, hg, _e, -, -, hαc, hKblock⟩ :=
    KS11LieProof.core_block hcN hc3 hK hT hKf hq hq2 φ
  obtain ⟨μ, hμ⟩ := KS11LieProof.exists_orderOf_eq_qSubPi hKf hq
  have hμS : π = false → (μ : Kf) ^ (p ^ f + 1) = 1 := by
    intro hπ
    subst hπ
    have hdvd : orderOf μ ∣ p ^ f + 1 := by
      rw [hμ]
      simp [Sec4.qSubPi]
    have h2 := congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hdvd)
    simpa using h2
  have hB : KS11LieProof.diagTwo μ ∈ slPi π 2 (p ^ f) Kf :=
    KS11LieProof.diagTwo_mem_slPi hKf hμS
  obtain ⟨y, hyK, hy⟩ :=
    KS11LieProof.block_mem_image hcN hc3 hK hT hKf hq hq2 φ hg hαc hKblock ⟨_, hB⟩
  have hd : orderOf (KS11LieProof.blockProj hKf hg ⟨KS11LieProof.diagTwo μ, hB⟩) ∣
      Nat.card K :=
    KS11LieProof.orderOf_dvd_card_of_image φ ⟨y, hyK, hy⟩
  rw [KS11LieProof.orderOf_blockProj_diagTwo hKf hg hB, hμ] at hd
  have hne : Nat.card K ≠ 0 := by
    intro h0
    rw [h0, Nat.factorization_zero] at hK3
    simp at hK3
  have h9d : 9 ∣ Sec4.qSubPi π (p ^ f) := (Sec4.modNine_iff (show 1 ≤ p ^ f by omega)).mp h9
  have h9K : 9 ∣ Nat.card K := h9d.trans hd
  have h9K' : 3 ^ 2 ∣ Nat.card K := by
    norm_num
    exact h9K
  have hle : 2 ≤ (Nat.card K).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h9K'
  omega

theorem thetaComponentsIn_map_of_injective {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] (f : G →* G')
    (hf : Function.Injective f) {H L : Subgroup G}
    (hL : L ∈ CFSG.RankThree.PartTwo.thetaComponentsIn H) :
    L.map f ∈ CFSG.RankThree.PartTwo.thetaComponentsIn (H.map f) := by
  obtain ⟨L', hL', rfl⟩ := hL
  have hL'' := CFSG.RankThree.map_mulEquiv_mem_thetaComponents Nat.prime_three
    (Subgroup.equivMapOfInjective H f hf) hL'
  have heq : (L'.map (Subgroup.equivMapOfInjective H f hf).toMonoidHom).map (H.map f).subtype
      = (L'.map H.subtype).map f := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  show (L'.map H.subtype).map f ∈ CFSG.RankThree.PartTwo.thetaComponentsIn (H.map f)
  rw [← heq]
  exact Set.mem_image_of_mem (fun L : Subgroup (H.map f) => L.map (H.map f).subtype) hL''

theorem finite_mulAut_of_finite (Z : Type) [Group Z] [Finite Z] : Finite (MulAut Z) :=
  Finite.of_injective (fun σ : MulAut Z => (σ : Z → Z)) fun σ τ h => MulEquiv.ext (congrFun h)

abbrev AutSemi (Z : Type) [Group Z] (α : MulAut Z) : Type :=
  SemidirectProduct Z (Subgroup.zpowers α) (Subgroup.zpowers α).subtype

def autGen {Z : Type} [Group Z] (α : MulAut Z) : AutSemi Z α :=
  SemidirectProduct.inr ⟨α, Subgroup.mem_zpowers α⟩

abbrev autBase {Z : Type} [Group Z] (α : MulAut Z) : Subgroup (AutSemi Z α) :=
  (SemidirectProduct.inl : Z →* AutSemi Z α).range

theorem finite_autSemi {Z : Type} [Group Z] [Finite Z] (α : MulAut Z) :
    Finite (AutSemi Z α) := by
  haveI := finite_mulAut_of_finite Z
  exact Finite.of_injective (fun x : AutSemi Z α => (x.left, x.right)) fun x y h => by
    cases x
    cases y
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp only at h1 h2
    subst h1
    subst h2
    rfl

theorem autInl_injective {Z : Type} [Group Z] (α : MulAut Z) :
    Function.Injective (SemidirectProduct.inl : Z →* AutSemi Z α) :=
  SemidirectProduct.inl_injective

theorem autGen_mul_inl {Z : Type} [Group Z] (α : MulAut Z) (w : Z) :
    autGen α * SemidirectProduct.inl w = SemidirectProduct.inl (α w) * autGen α := by
  have h : SemidirectProduct.inl (α w) =
      autGen α * SemidirectProduct.inl w *
        SemidirectProduct.inr (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α)⁻¹ :=
    SemidirectProduct.inl_aut (φ := (Subgroup.zpowers α).subtype)
      (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) w
  have hinv : SemidirectProduct.inr (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α)⁻¹ *
      autGen α = 1 := by
    unfold autGen
    rw [← map_mul SemidirectProduct.inr, inv_mul_cancel, map_one]
  rw [h]
  simp only [mul_assoc, hinv, mul_one]

theorem autInl_mul_gen_iff {Z : Type} [Group Z] (α : MulAut Z) (w : Z) :
    SemidirectProduct.inl w * autGen α = autGen α * SemidirectProduct.inl w ↔ α w = w := by
  rw [autGen_mul_inl, mul_left_inj]
  constructor
  · intro h
    exact (SemidirectProduct.inl_injective h).symm
  · intro h
    rw [h]

theorem autGen_pow_three {Z : Type} [Group Z] (α : MulAut Z) (hα3 : α ^ 3 = 1) :
    autGen α ^ 3 = 1 := by
  have h3 : (⟨α, Subgroup.mem_zpowers α⟩ : Subgroup.zpowers α) ^ 3 = 1 := by
    apply Subtype.ext
    exact hα3
  unfold autGen
  rw [← map_pow SemidirectProduct.inr, h3, map_one]

theorem autBase_normal {Z : Type} [Group Z] (α : MulAut Z) : (autBase α).Normal := by
  have h : autBase α =
      (SemidirectProduct.rightHom : AutSemi Z α →* Subgroup.zpowers α).ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  rw [h]
  infer_instance

theorem autGen_mem_normalizer {Z : Type} [Group Z] (α : MulAut Z) :
    autGen α ∈ Subgroup.normalizer ((autBase α : Subgroup (AutSemi Z α)) : Set (AutSemi Z α)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact SetLike.mem_coe.mpr ((autBase_normal α).conj_mem h (SetLike.mem_coe.mp hh) (autGen α))
  · intro hh
    have h2 := (autBase_normal α).conj_mem _ (SetLike.mem_coe.mp hh) (autGen α)⁻¹
    have e2 : (autGen α)⁻¹ * (autGen α * h * (autGen α)⁻¹) * (autGen α)⁻¹⁻¹ = h := by
      group
    rw [e2] at h2
    exact SetLike.mem_coe.mpr h2

theorem map_fixSub_eq_inf_centralizer {Z : Type} [Group Z] (α : MulAut Z) :
    (Item426.fixSub α).map (SemidirectProduct.inl : Z →* AutSemi Z α) =
      autBase α ⊓ Subgroup.centralizer ({autGen α} : Set (AutSemi Z α)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨MonoidHom.mem_range.mpr ⟨w, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact ((autInl_mul_gen_iff α w).mpr (Item426.mem_fixSub.mp hw)).symm
  · intro hx
    obtain ⟨hxb, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxb
    refine Subgroup.mem_map.mpr ⟨w, Item426.mem_fixSub.mpr ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hxc
    exact (autInl_mul_gen_iff α w).mp (hxc (autGen α) (Set.mem_singleton _)).symm

theorem aschbacherSolvableCore_eq_bot_of_simple_L3 {X : Type} [Group X] [IsSimpleGroup X]
    (hns : ¬ Group.IsSolvable X) : aschbacherSolvableCore 3 X = ⊥ := by
  have hR : CFSG.solvableRadical X = ⊥ := by
    refine le_bot_iff.mp (sSup_le ?_)
    rintro N ⟨hN, hsol⟩
    have := hN
    rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact le_of_eq h
    · exfalso
      apply hns
      rw [h] at hsol
      exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup X).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  unfold aschbacherSolvableCore inSubgroup
  rw [hR]
  rw [eq_bot_iff]
  rintro _ ⟨y, -, rfl⟩
  have : y = 1 := Subsingleton.elim _ _
  simp [this]

theorem not_isSolvable_of_perfect_simple_L3 {X : Type} [Group X] [IsSimpleGroup X]
    (hX : Group.IsPerfect X) : ¬ Group.IsSolvable X := by
  intro hs
  haveI := subsingleton_of_perfect_solvable X
  exact (not_nontrivial_iff_subsingleton.mpr this) inferInstance

theorem isType424_map_inl {Z : Type} [Group Z] [Finite Z] (α : MulAut Z) (J : Subgroup Z)
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) :
    IsType424 (↥(J.map (SemidirectProduct.inl : Z →* AutSemi Z α)) ⧸
      aschbacherSolvableCore 3 ↥(J.map (SemidirectProduct.inl : Z →* AutSemi Z α))) := by
  let eK : ↥J ≃* ↥(J.map (SemidirectProduct.inl : Z →* AutSemi Z α)) :=
    Subgroup.equivMapOfInjective J (SemidirectProduct.inl : Z →* AutSemi Z α) (autInl_injective α)
  have hcore := aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK
  exact isType424_of_mulEquiv (QuotientGroup.congr _ _ eK hcore).symm hJT

theorem card_le_27_of_gt_two {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {Z : Type} [Group Z] [Finite Z]
    (g : Z ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (α : MulAut Z) (J : Subgroup Z) (hα3 : α ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub α))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) (hJ3 : (Nat.card J).factorization 3 = 1)
    (P : Subgroup (MulAut Z)) (hP : IsPGroup 3 P) : Nat.card P ≤ 27 := by
  by_cases h9 : Sec4.ModNine π (p ^ f)
  · exfalso
    haveI := finite_autSemi α
    haveI : IsSimpleGroup (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      CFSG.RankThree.PartTwo.Sec4.Res4Seven.isSimpleGroup_projImage_slPi hK hq2
    have hWperf : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hK hq2
    let e1 : ↥(autBase α) ≃* projImage (Sec4.slPi π 3 (p ^ f) K) :=
      (MonoidHom.ofInjective (autInl_injective α)).symm.trans g
    haveI : IsSimpleGroup ↥(autBase α) := e1.isSimpleGroup
    have hY : Group.IsPerfect ↥(autBase α) := isPerfect_of_mulEquiv hWperf e1
    have hcore : aschbacherSolvableCore 3 ↥(autBase α) = ⊥ :=
      aschbacherSolvableCore_eq_bot_of_simple_L3 (not_isSolvable_of_perfect_simple_L3 hY)
    let φ0 : ↥(autBase α) ⧸ aschbacherSolvableCore 3 ↥(autBase α) ≃*
        ↥(autBase α) ⧸ (⊥ : Subgroup ↥(autBase α)) :=
      QuotientGroup.congr _ _ (MulEquiv.refl _) (by rw [hcore, Subgroup.map_bot])
    let φ : ↥(autBase α) ⧸ aschbacherSolvableCore 3 ↥(autBase α) ≃*
        projImage (Sec4.slPi π 3 (p ^ f) K) :=
      (φ0.trans QuotientGroup.quotientBot).trans e1
    have hθ : J.map (SemidirectProduct.inl : Z →* AutSemi Z α) ∈
        thetaComponentsIn (autBase α ⊓ Subgroup.centralizer ({autGen α} : Set (AutSemi Z α))) := by
      rw [← map_fixSub_eq_inf_centralizer α]
      exact thetaComponentsIn_map_of_injective _ (autInl_injective α) hJ
    have hK3 : (Nat.card (J.map (SemidirectProduct.inl : Z →* AutSemi Z α))).factorization 3 = 1 := by
      rw [Subgroup.card_map_of_injective (autInl_injective α)]
      exact hJ3
    exact (not_modNine_of_block (autGen_mem_normalizer α) (autGen_pow_three α hα3) hθ
      (isType424_map_inl α J hJT) hK3 hK hq hq2 φ) h9
  · exact card_le_27_of_equiv g (fun Q hQ => card_le_27_of_model hK hq hq2 h9 Q hQ) P hP

theorem autThreeAut_l3 : AutThreeAut Sec13.IsLThreePi := by
  intro Z _ _ hZ α J hα3 hJ hJT hJ3 P hP
  obtain ⟨X, _, hF, ⟨e⟩⟩ := hZ
  obtain ⟨p, e', hpf, he, hiso⟩ := hF
  obtain ⟨π, K, hfield, hK, hq, ⟨f⟩⟩ :=
    Sec13.L3Proof.exists_model_of_isoLThreePi he hiso
  by_cases hq2 : 2 < p ^ e'
  · obtain ⟨g⟩ := nonempty_mulEquiv_of_commutator
      (CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hK hq2) f e
    exact card_le_27_of_gt_two hK hq hq2 g α J hα3 hJ hJT hJ3 P hP
  · exfalso
    have hp2 : 2 ≤ p ^ e' := by
      have h1 : p ^ 1 ≤ p ^ e' := Nat.pow_le_pow_right hpf.out.pos he
      rw [pow_one] at h1
      exact le_trans hpf.out.two_le h1
    have h2 : p ^ e' = 2 := le_antisymm (not_lt.mp hq2) hp2
    have hπ : π = false := by
      cases π
      · rfl
      · rw [h2] at hq
        simp [Sec4.ModThree] at hq
    subst hπ
    haveI : Group.IsSolvable (projImage (Sec4.slPi false 3 (p ^ e') K)) :=
      CFSG.RankThree.PartTwo.Sec13.isSolvable_projImage_slPi_two hK h2
    haveI : Group.IsSolvable X :=
      Group.isSolvable_of_surjective (f := f.symm.toMonoidHom) f.symm.surjective
    haveI : Group.IsSolvable Z :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    haveI : Group.IsPerfect ↥J :=
      CFSG.RankThree.PartTwo.isPerfect_of_mem_thetaComponentsIn hJ
    haveI := subsingleton_of_perfect_solvable ↥J
    have hc : Nat.card J = 1 := Nat.card_of_subsingleton (1 : ↥J)
    simp [hc] at hJ3

end CFSG.RankThree.PartTwo.Sec11.AutThree1129

end
