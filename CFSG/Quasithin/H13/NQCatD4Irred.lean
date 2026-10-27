module

public import CFSG.Quasithin.H13.NQCatG2RadFacts
public import CFSG.Quasithin.H13.NQCatD4Center
public import CFSG.Quasithin.Background.SmithB42D4Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.G2A5Seven
public import CFSG.Quasithin.Background.G2L2Seven
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.A6S4L1
public import CFSG.Quasithin.H13.NQCatLieOverRank1
public import CFSG.Quasithin.H13.U3L14E
public import CFSG.Quasithin.SteinbergCBSevenSylowAFive
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10SecAFacts
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrth
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19F
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19N
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Y
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Comp
public import CFSG.Quasithin.Vol2.Ch6Sec1Lin2Excl
public import CFSG.Quasithin.Vol2.Ch6Skeleton
public import CFSG.Quasithin.Vol2.Ch6Sp
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.NQCat.D4Irred

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4 CFSG.LieType.BorelTits CFSG.Quasithin.B42D4
  CFSG.QuasithinUnique.Setup.X6

theorem pCoreOf_eq_of_parabolicFacts {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hF : ParabolicFacts P Q) (hne : pCoreOf 2 (perfectCore P) ≠ ⊥) :
    pCoreOf 2 (perfectCore P) = Q := by
  rcases hF.levi with h | h
  · exfalso
    apply hne
    have h0 : perfectCore P = ⊥ :=
      G24Split.eq_bot_of_perfect_of_isPGroup (perfectCore_perfect P) (hF.pGroup.to_le h)
    rw [h0]
    exact le_bot_iff.1 (pCoreOf_le 2 ⊥)
  · exact G2Rad.pCoreOf_perfectCore_eq hF.le hF.normalizes hF.pGroup h

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K
local notation "Xr" => pinnedX TwistTag.D4.tag K

include hσ3 in
theorem qE_H_mem_centerOf
    {f : K} (hf : σ f = f) : qE σ 0 0 0 0 f ∈ centerOf (Q0 σ) := by
  refine ⟨qE_mem_Q0 σ hσ3 0 0 0 0 ⟨f, hf⟩, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  obtain ⟨b, c, d, e, f', rfl⟩ := (mem_Q0_iff' σ hσ3).1 hg
  exact (qE_commute_iff σ hσ3 _ _ _ _ _ _ _ _ _ _).2 (by simp [tr])

omit [Finite K] in
theorem weyl_x6_x6
    (b : trialityFixedField K σ.toRingHom) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa0) *
        ox₆ σ b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection fa0))⁻¹ = ox₆ σ b := by
  have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
  have hr : TwistTag.D4.orbitReflection fa0 • trialityRoot 5 = trialityRoot 5 := by
    have hw : TwistTag.D4.orbitWord fa0 =
        [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have := canonicalRep_conj_charTwo' (K := K) (TwistTag.D4.orbitReflection fa0) hroot6 (b : K)
  rw [hr] at this
  exact this

include hσ3 in
theorem perfectCore_le_centralizer :
    perfectCore (P0 σ) ≤ Subgroup.centralizer (centerOf (Q0 σ) : Set GL) := by
  have : Finite GL := finite_modGL
  have h1 : perfectCore (P0 σ) ≤ ⁅P0 σ, P0 σ⁆ :=
    calc perfectCore (P0 σ) = ⁅perfectCore (P0 σ), perfectCore (P0 σ)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅P0 σ, P0 σ⁆ := Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
  refine h1.trans ((commutator_graphFixedParabolic_le_fixedPosWeylGroup σ.surjective fa0).trans
    (sup_le (fun u hu => ?_) ?_))
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨f, rfl⟩ := D4Center.eq_ox₆_of_mem_center_a0 σ hσ3 hz
    obtain ⟨a, b, c, d, e, f', rfl⟩ := (mem_U_iff σ hσ3).1 hu
    have h6 : ox₆ σ f = qE σ 0 0 0 0 (f : K) := by rw [coe_ox₆_eq, qE_H]
    rw [h6]
    have hc1 : Commute (qE σ 0 0 0 0 (f : K)) (ox₁ σ a) := by
      rw [← qE_H]
      exact commute_H_ox₁ _ _ σ
    have hc2 : Commute (qE σ 0 0 0 0 (f : K)) (qE σ b c d e f') :=
      (qE_commute_iff σ hσ3 _ _ _ _ _ _ _ _ _ _).2 (by simp [tr])
    exact (hc1.mul_right hc2).eq
  · rw [Subgroup.closure_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨f, rfl⟩ := D4Center.eq_ox₆_of_mem_center_a0 σ hσ3 hz
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul]
    exact weyl_x6_x6 σ f

include hσ3 in
theorem lt_card_Q1 :
    Nat.card K ^ 3 < Nat.card (Q1 σ) := by
  have : Finite GL := finite_modGL
  let F : K × K × K × trialityFixedField K τ₀ → Q1 σ := fun v =>
    ⟨ox₁ σ v.1 * ox₃ σ v.2.1 * ox₄ σ v.2.2.1 * ox₅ σ v.2.2.2 * ox₆ σ 0,
      (mem_radical_a1_iff σ hσ3).2 ⟨_, _, _, _, _, rfl⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨a, c, d, e⟩ ⟨a', c', d', e'⟩ h
    simp only [F, Subtype.mk.injEq] at h
    have h' : ox₁ σ a * ox₂ σ 0 * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ 0 =
        ox₁ σ a' * ox₂ σ 0 * ox₃ σ c' * ox₄ σ d' * ox₅ σ e' * ox₆ σ 0 := by
      rw [ox₂_zero σ hσ3, mul_one, mul_one]
      exact h
    obtain ⟨h1, -, h3, h4, h5, -⟩ := coord_unique σ hσ3 h'
    rw [h1, h3, h4, h5]
  have h := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod] at h
  have hk : 1 < Nat.card (trialityFixedField K τ₀) :=
    Finite.one_lt_card_iff_nontrivial.2 inferInstance
  have hK0 : 0 < Nat.card K := Nat.card_pos
  calc Nat.card K ^ 3 = Nat.card K ^ 3 * 1 := (mul_one _).symm
    _ < Nat.card K ^ 3 * Nat.card (trialityFixedField K τ₀) :=
        Nat.mul_lt_mul_of_pos_left hk (pow_pos hK0 3)
    _ = Nat.card K * (Nat.card K * (Nat.card K * Nat.card (trialityFixedField K τ₀))) := by
        ring
    _ ≤ Nat.card (Q1 σ) := h

variable {W : Subgroup (ModGL TwistTag.D4.tag K)}

include hσ3 in
theorem qE_mem_add
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W) {b c d e f f' : K} (hf' : σ f' = f')
    (h : qE σ b c d e f ∈ W) : qE σ b c d e (f + f') ∈ W := by
  have h1 : qE σ b c d e (f + f') = qE σ b c d e f * qE σ 0 0 0 0 f' := by
    rw [qE_mul σ hσ3]
    exact qE_congr σ (add_zero b).symm (add_zero c).symm (add_zero d).symm (add_zero e).symm
      (by simp [tr])
  rw [h1]
  exact W.mul_mem h (hZ f' hf')

include hσ3 in
theorem qE_mem_zero
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W) {b c d e f : K} (hf : σ f = f)
    (h : qE σ b c d e f ∈ W) : qE σ b c d e 0 ∈ W := by
  have := qE_mem_add σ hσ3 hZ hf h
  rwa [CharTwo.add_self_eq_zero] at this

include hσ3 in
theorem qE_mem_mul
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W) {b c d e b' c' d' e' : K} (he : σ e = e)
    (hb' : σ b' = b') (h : qE σ b c d e 0 ∈ W) (h' : qE σ b' c' d' e' 0 ∈ W) :
    qE σ (b + b') (c + c') (d + d') (e + e') 0 ∈ W := by
  have h1 := W.mul_mem h h'
  rw [qE_mul σ hσ3] at h1
  refine qE_mem_zero σ hσ3 hZ ?_ h1
  simp only [map_add, map_mul, sigma_tr σ hσ3, he, hb', map_zero]

include hσ3 in
theorem qE_mem_conj
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W) {b c d e s : K} (hb : σ b = b)
    (hs : ox₁ σ s ∈ Subgroup.normalizer (W : Set GL)) (h : qE σ b c d e 0 ∈ W) :
    qE σ b (c + s * b) (d + b * (σ s * σ (σ s)) + bF σ s c)
      (e + b * nK σ s + e5F σ s c + tr σ (s * d)) 0 ∈ W := by
  have h1 := (Subgroup.mem_normalizer_iff.1 hs _).1 h
  rw [conj_ox₁_qE σ hσ3 hb] at h1
  refine qE_mem_zero σ hσ3 hZ ?_ h1
  simp only [map_add, map_mul, hb, map_zero, sigma_nK σ hσ3, sigma_e6F σ hσ3, sigma_e5F σ hσ3]

include hσ3 in
theorem qE_mem_delta
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W) {b c d e s : K} (hb : σ b = b) (he : σ e = e)
    (hs : ox₁ σ s ∈ Subgroup.normalizer (W : Set GL)) (h : qE σ b c d e 0 ∈ W) :
    qE σ 0 (s * b) (b * (σ s * σ (σ s)) + bF σ s c) (b * nK σ s + e5F σ s c + tr σ (s * d))
      0 ∈ W := by
  have h1 := qE_mem_conj σ hσ3 hZ hb hs h
  have he' : σ (e + b * nK σ s + e5F σ s c + tr σ (s * d)) =
      e + b * nK σ s + e5F σ s c + tr σ (s * d) := by
    simp only [map_add, map_mul, hb, he, sigma_nK σ hσ3, sigma_e5F σ hσ3, sigma_tr σ hσ3]
  have h2 := qE_mem_mul σ hσ3 hZ he' hb h1 h
  convert h2 using 1
  exact qE_congr σ (by ring2) (by ring2) (by ring2) (by ring2) rfl

omit [Finite K] in
theorem qE_mem_weyl
    {e : K} (he : σ e = e)
    (hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa0) ∈
      Subgroup.normalizer (W : Set GL)) (h : qE σ 0 0 0 e 0 ∈ W) : qE σ e 0 0 0 0 ∈ W := by
  have e5 : qE σ 0 0 0 e 0 = ox₅ σ ⟨e, he⟩ := by rw [coe_ox₅_eq, ← qE_P σ]
  have e2 : qE σ e 0 0 0 0 = ox₂ σ ⟨e, he⟩ := by rw [coe_ox₂_eq, ← qE_C σ]
  rw [e5] at h
  rw [e2, ← weyl_x5_x2 σ ⟨e, he⟩]
  exact (Subgroup.mem_normalizer_iff.1 hn _).1 h

include hσ3 in
theorem qE_mem_e_of_d
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W)
    (hx : ∀ s : K, ox₁ σ s ∈ Subgroup.normalizer (W : Set GL)) {d e : K} (hd : d ≠ 0)
    (he : σ e = e) (h : qE σ 0 0 d e 0 ∈ W) {e' : K} (he' : σ e' = e') :
    qE σ 0 0 0 e' 0 ∈ W := by
  obtain ⟨y, hy⟩ : ∃ y : K, tr σ y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact one_ne_zero (eq_zero_of_tr_mul σ fun s => by rw [one_mul]; exact hcon s)
  obtain ⟨c, hc⟩ : ∃ c : K, c = e' * (tr σ y)⁻¹ := ⟨_, rfl⟩
  have hcσ : σ c = c := by rw [hc, map_mul, map_inv₀, he', sigma_tr σ hσ3]
  have h1 := qE_mem_delta σ hσ3 hZ (b := 0) (map_zero σ) he (hx (c * y * d⁻¹)) h
  have e1 : e5F σ (c * y * d⁻¹) 0 = 0 := by simp [e5F, tr]
  convert h1 using 1
  refine qE_congr σ rfl (by rw [mul_zero]) (by simp [bF]) ?_ rfl
  rw [zero_mul, zero_add, e1, zero_add, inv_mul_cancel_right₀ hd, tr_mul_fixed σ hcσ, hc,
    inv_mul_cancel_right₀ hy]

include hσ3 in
theorem exists_d_of_c
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W)
    (hx : ∀ s : K, ox₁ σ s ∈ Subgroup.normalizer (W : Set GL)) (hσ1 : ∃ x : K, σ x ≠ x)
    {c d e : K} (hc : c ≠ 0) (he : σ e = e) (h : qE σ 0 c d e 0 ∈ W) :
    ∃ d' e' : K, d' ≠ 0 ∧ σ e' = e' ∧ qE σ 0 0 d' e' 0 ∈ W := by
  obtain ⟨x, hx1⟩ := hσ1
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx1 (map_zero σ)
  have h1 := qE_mem_delta σ hσ3 hZ (b := 0) (map_zero σ) he (hx (c * x)) h
  rw [mul_zero] at h1
  refine ⟨_, _, ?_, ?_, h1⟩
  · rw [zero_mul, zero_add]
    intro h0
    have h2 := fixed_of_bF_eq_zero σ hσ3 (mul_ne_zero hc hx0) h0
    rw [div_mul_cancel_left₀ hc, map_inv₀] at h2
    exact hx1 (inv_injective h2)
  · simp only [map_add, map_zero, zero_mul, sigma_e5F σ hσ3, sigma_tr σ hσ3]

include hσ3 in
theorem exists_c_of_b
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W)
    (hx : ∀ s : K, ox₁ σ s ∈ Subgroup.normalizer (W : Set GL)) {b c d e : K} (hb0 : b ≠ 0)
    (hb : σ b = b) (he : σ e = e) (h : qE σ b c d e 0 ∈ W) :
    ∃ c' d' e' : K, c' ≠ 0 ∧ σ e' = e' ∧ qE σ 0 c' d' e' 0 ∈ W := by
  refine ⟨_, _, _, ?_, ?_, qE_mem_delta σ hσ3 hZ hb he (hx 1) h⟩
  · rwa [one_mul]
  · simp only [map_add, map_mul, hb, sigma_nK σ hσ3, sigma_e5F σ hσ3, sigma_tr σ hσ3]

include hσ3 in
theorem qE_mem_e
    (hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W)
    (hx : ∀ s : K, ox₁ σ s ∈ Subgroup.normalizer (W : Set GL))
    (hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa0) ∈
      Subgroup.normalizer (W : Set GL)) (hσ1 : ∃ x : K, σ x ≠ x) {b c d e : K}
    (hb : σ b = b) (he : σ e = e) (hne : ¬ (b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0))
    (h : qE σ b c d e 0 ∈ W) {e' : K} (he' : σ e' = e') : qE σ 0 0 0 e' 0 ∈ W := by
  have hd : ∀ {d e : K}, d ≠ 0 → σ e = e → qE σ 0 0 d e 0 ∈ W → qE σ 0 0 0 e' 0 ∈ W :=
    fun hd he h => qE_mem_e_of_d σ hσ3 hZ hx hd he h he'
  have hc : ∀ {c d e : K}, c ≠ 0 → σ e = e → qE σ 0 c d e 0 ∈ W → qE σ 0 0 0 e' 0 ∈ W := by
    intro c d e hc he h
    obtain ⟨d', e'', hd', he'', h'⟩ := exists_d_of_c σ hσ3 hZ hx hσ1 hc he h
    exact hd hd' he'' h'
  have hb' : ∀ {b c d e : K}, b ≠ 0 → σ b = b → σ e = e → qE σ b c d e 0 ∈ W →
      qE σ 0 0 0 e' 0 ∈ W := by
    intro b c d e hb0 hb he h
    obtain ⟨c', d', e'', hc', he'', h'⟩ := exists_c_of_b σ hσ3 hZ hx hb0 hb he h
    exact hc hc' he'' h'
  by_cases hb0 : b = 0
  · subst hb0
    by_cases hc0 : c = 0
    · subst hc0
      by_cases hd0 : d = 0
      · subst hd0
        have he0 : e ≠ 0 := fun h0 => hne ⟨rfl, rfl, rfl, h0⟩
        exact hb' he0 he (map_zero σ) (qE_mem_weyl σ he hn h)
      · exact hd hd0 he h
    · exact hc hc0 he h
  · exact hb' hb0 hb he h

include hσ3 in
theorem eq_or_eq_of_le_normalizer
    (hK4 : 4 ≤ Nat.card K) (hσ1 : ∃ x : K, σ x ≠ x)
    (hspan : ∃ t₁ t₂ t₃ : K, ∀ x : K, ∃ a₁ a₂ a₃ : K, σ a₁ = a₁ ∧ σ a₂ = a₂ ∧ σ a₃ = a₃ ∧
      x = a₁ * t₁ + a₂ * t₂ + a₃ * t₃)
    (hZW : centerOf (Q0 σ) ≤ W) (hWQ : W ≤ Q0 σ)
    (hKW : perfectCore (P0 σ) ≤ Subgroup.normalizer (W : Set GL)) :
    W = centerOf (Q0 σ) ∨ W = Q0 σ := by
  have hU := isPGroup_posUnipotent σ hσ3
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa0), s.card = 4 := by
    have htop : orbitField TwistTag.D4 K τ₀ fa0 = ⊤ :=
      orbitField_D4_zero_eq_top σ (fun c => ringHom_apply_apply_apply_of_pow_three hσ3 c)
    have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa0) := by
      rw [htop, Nat.card_congr Subfield.topEquiv.toEquiv]
      exact hK4
    exact CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hc
  obtain ⟨R, hRx, -, hRW, hMP, -, -⟩ := levi_package σ fa0 hU hL4
  have hx : ∀ s : K, ox₁ σ s ∈ Subgroup.normalizer (W : Set GL) := by
    intro s
    have hs : s ∈ orbitField TwistTag.D4 K τ₀ fa0 :=
      mem_orbitField.2 (by rw [orbit_card_fa0, hσ3]; rfl)
    refine hKW (hMP ⟨uSL ⟨s, hs⟩, ?_⟩)
    rw [hRx]
    exact orbitX_fa0_eq σ ⟨s, hs⟩
  have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa0) ∈
      Subgroup.normalizer (W : Set GL) := hKW (hMP ⟨WSL, hRW⟩)
  have hZ : ∀ f : K, σ f = f → qE σ 0 0 0 0 f ∈ W := fun f hf =>
    hZW (qE_H_mem_centerOf σ hσ3 hf)
  by_cases hW : W ≤ centerOf (Q0 σ)
  · exact Or.inl (le_antisymm hW hZW)
  right
  obtain ⟨w, hwW, hwZ⟩ := Set.not_subset.1 hW
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_Q0_iff' σ hσ3).1 (hWQ hwW)
  have hne : ¬ ((b : K) = 0 ∧ c = 0 ∧ d = 0 ∧ (e : K) = 0) := by
    rintro ⟨hb, hc, hd, he⟩
    apply hwZ
    rw [qE_congr σ hb hc hd he rfl]
    exact qE_H_mem_centerOf σ hσ3 f.2
  have hE5 : ∀ e' : K, σ e' = e' → qE σ 0 0 0 e' 0 ∈ W := fun e' he' =>
    qE_mem_e σ hσ3 hZ hx hn hσ1 b.2 e.2 hne (qE_mem_zero σ hσ3 hZ f.2 hwW) he'
  have hE2 : ∀ β : K, σ β = β → qE σ β 0 0 0 0 ∈ W := fun β hβ =>
    qE_mem_weyl σ hβ hn (hE5 β hβ)
  have hE34 : ∀ β : K, σ β = β → ∀ s : K, qE σ 0 (s * β) (β * (σ s * σ (σ s))) 0 0 ∈ W := by
    intro β hβ s
    have h1 := qE_mem_delta σ hσ3 hZ (c := 0) (d := 0) hβ (map_zero σ) (hx s) (hE2 β hβ)
    have e1 : bF σ s 0 = 0 := by simp [bF]
    have e2 : e5F σ s 0 = 0 := by simp [e5F, tr]
    have e3 : tr σ (s * 0) = 0 := by simp [tr]
    rw [e1, e2, e3, add_zero, add_zero, add_zero] at h1
    have hN : σ (β * nK σ s) = β * nK σ s := by rw [map_mul, hβ, sigma_nK σ hσ3]
    have h2 := qE_mem_mul σ hσ3 hZ hN (map_zero σ) h1 (hE5 _ hN)
    simp only [add_zero, CharTwo.add_self_eq_zero] at h2
    exact h2
  have hE4 : ∀ x : K, qE σ 0 0 x 0 0 ∈ W := by
    obtain ⟨t₁, t₂, t₃, hsp⟩ := hspan
    let V : AddSubgroup K :=
      { carrier := {x | qE σ 0 0 x 0 0 ∈ W}
        add_mem' := fun {x y} hx' hy' => by
          have h := qE_mem_mul σ hσ3 hZ (map_zero σ) (map_zero σ) hx' hy'
          simp only [add_zero] at h
          exact h
        zero_mem' := by
          show qE σ 0 0 0 0 0 ∈ W
          rw [← qE_H σ, pinnedX_zero]
          exact W.one_mem
        neg_mem' := fun {x} hx' => by
          show qE σ 0 0 (-x) 0 0 ∈ W
          rw [CharTwo.neg_eq]
          exact hx' }
    intro x
    refine bF_generate σ hσ3 hσ1 hsp V (fun β hβ s _ s' _ => ?_) x
    show qE σ 0 0 (β * bF σ s s') 0 0 ∈ W
    have h1 := qE_mem_delta σ hσ3 hZ (b := 0) (s := s) (map_zero σ) (map_zero σ) (hx s)
      (hE34 β hβ s')
    have hX : σ (0 * nK σ s + e5F σ s (s' * β) + tr σ (s * (β * (σ s' * σ (σ s'))))) =
        0 * nK σ s + e5F σ s (s' * β) + tr σ (s * (β * (σ s' * σ (σ s')))) := by
      simp only [map_add, map_mul, map_zero, sigma_nK σ hσ3, sigma_e5F σ hσ3, sigma_tr σ hσ3]
    have h2 := qE_mem_mul σ hσ3 hZ hX (map_zero σ) h1 (hE5 _ hX)
    convert h2 using 1
    refine qE_congr σ (by simp) (by simp) ?_ (CharTwo.add_self_eq_zero _).symm rfl
    rw [zero_mul, zero_add, add_zero, mul_comm s' β, bF_smul_right σ hβ]
  have hE3 : ∀ x : K, qE σ 0 x 0 0 0 ∈ W := by
    intro x
    have h2 := qE_mem_mul σ hσ3 hZ (map_zero σ) (map_zero σ) (hE34 1 (map_one σ) x)
      (hE4 (1 * (σ x * σ (σ x))))
    convert h2 using 1
    exact qE_congr σ (by simp) (by simp) (CharTwo.add_self_eq_zero _).symm (by simp) rfl
  refine le_antisymm hWQ fun g hg => ?_
  obtain ⟨b', c', d', e', f', rfl⟩ := (mem_Q0_iff' σ hσ3).1 hg
  show Xr d4C (b' : K) * ox₃ σ c' * ox₄ σ d' * Xr d4P (e' : K) * Xr d4H (f' : K) ∈ W
  rw [qE_C σ, qE_ox₃ σ, qE_ox₄ σ, qE_P σ, qE_H σ]
  exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (hE2 _ b'.2) (hE3 c')) (hE4 d'))
    (hE5 _ e'.2)) (hZ _ f'.2)

end Model

section Amalgam

theorem exists_model
    {Y : Type} [Group Y] {n : ℕ} (hY : IsLieOverTwo .trialityD4 0 n Y) {T M₁ M : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M) :
    1 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (2 ^ n) ^ 3 ∧
      (∀ c, σ c = c ^ (2 ^ n)) ∧ ∃ (a : Fin TwistTag.D4.foldedTag.rank)
        (ι : Y →* ModGL TwistTag.D4.tag K), Function.Injective ι ∧
          M.map ι = graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} := by
  have hYm : ChevalleyExceptionalModel Y .trialityD4 2 n := by
    rcases hY with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp [classicalTags] at h
    · exact h
    · simp [reeTitsTags] at h
    · exact absurd h (by decide)
  obtain ⟨hn, K₀, _, _, σ₀, -, -, ⟨e₀⟩⟩ := exists_mulEquiv_triality_model hYm
  have : Finite (ModGL TwistTag.D4.tag K₀) := finite_modGL
  have : Finite Y := Finite.of_equiv _ e₀.symm.toEquiv
  obtain ⟨K, _, _, σ, φ, hK, hσ, -, hres, -⟩ := even_rank_two_residual_triality hYm hpair.1
  have : CharP K 2 := charP_two_of_card hn hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hBT := CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hYm
  have hPC : ∀ j : Fin 2, graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun j => graphFixedParabolic_le _ _ _ _
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
  have hne : ∀ j : Fin 2, ({d4Index j} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ :=
    fun j => by
      rcases hcases (d4Index j) with h | h <;> rw [h]
      · exact singleton_ne_univ_fa0
      · exact singleton_ne_univ_fa1
  have hQ : ∀ j : Fin 2,
      ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom ≠ ⊥ ∧
        IsPGroup 2 ↥(((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
          {d4Index j}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
            φ.symm.toMonoidHom) ∧
        ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom ≤
          Subgroup.normalizer ((((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
            {d4Index j}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
              φ.symm.toMonoidHom : Subgroup Y) : Set Y) := by
    intro j
    obtain ⟨hQP, hPN, hQ2, -⟩ := library_facts σ (d4Index j) (hne j)
    have hQC := hQP.trans (hPC j)
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      have hna : ∃ x ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j},
          ∃ y ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j},
            x * y ≠ y * x := by
        rcases hcases (d4Index j) with h | h <;> rw [h]
        · exact nonabelian_a0 σ hσ3
        · exact nonabelian_a1 σ hσ3
      obtain ⟨x, hx, y, hy, hxy⟩ := hna
      have hx1 : φ.symm ⟨x, hQC hx⟩ = 1 := by
        have : φ.symm ⟨x, hQC hx⟩ ∈ ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
            {d4Index j}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
              φ.symm.toMonoidHom := ⟨⟨x, hQC hx⟩, hx, rfl⟩
        rwa [h0, Subgroup.mem_bot] at this
      have hx' : x = 1 := congrArg Subtype.val ((MulEquiv.map_eq_one_iff φ.symm).1 hx1)
      exact hxy (by rw [hx', one_mul, mul_one])
    · exact (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm).map _
    · rintro _ ⟨p, hp, rfl⟩
      refine Subgroup.le_normalizer_map _ ⟨p, ?_, rfl⟩
      rw [← Subgroup.subgroupOf_normalizer_eq hQC]
      exact hPN hp
  obtain ⟨hM, hTM⟩ := (hpair.2.2 M).2 (Or.inr rfl)
  obtain ⟨j, g, hMj⟩ := G24Split.exists_eq_map_conj_of_isMaximalTwoLocal hpair.1 hres hBT
    (Q := fun j => ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) hQ hpair.1 hM hTM
  let ι : Y →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp
      (φ.toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom)
  have hι : Function.Injective ι :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective.comp
      (φ.injective.comp (MulAut.conj g⁻¹).injective)
  refine ⟨hn, K, inferInstance, inferInstance, σ, hK, hσ, d4Index j, ι, hι, ?_⟩
  have e : (ι.comp (MulAut.conj g).toMonoidHom).comp φ.symm.toMonoidHom =
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
    refine MonoidHom.ext fun x => ?_
    show ((φ ((MulAut.conj g⁻¹) ((MulAut.conj g) (φ.symm x))) :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) = x
    have h1 : (MulAut.conj g⁻¹) ((MulAut.conj g) (φ.symm x)) = φ.symm x := by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [h1, MulEquiv.apply_symm_apply]
  rw [hMj, Subgroup.map_map, Subgroup.map_map, e, Subgroup.map_subgroupOf_eq_of_le (hPC j)]

theorem d4ParabolicIrred
    {Y : Type} [Group Y] {n : ℕ} {T M₁ M : Subgroup Y} (hY : IsLieOverTwo .trialityD4 0 n Y)
    (hsp : IsSpecialPow 2 (2 ^ n) 4 ↥(pCoreOf 2 (perfectCore M)))
    (hpair : IsYAmalgamPair T M₁ M) :
    perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y) ∧
      ∀ W : Subgroup Y, centerOf (pCoreOf 2 (perfectCore M)) ≤ W →
        W ≤ pCoreOf 2 (perfectCore M) → perfectCore M ≤ Subgroup.normalizer (W : Set Y) →
          W = centerOf (pCoreOf 2 (perfectCore M)) ∨ W = pCoreOf 2 (perfectCore M) := by
  obtain ⟨hn, K, _, _, σ, hK, hσ, a, ι, hι, hM⟩ := exists_model hY hpair
  have : CharP K 2 := charP_two_of_card hn hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite Y := Finite.of_injective ι hι
  have hK' : (perfectCore M).map ι =
      perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
    rw [map_perfectCore, hM]
  have hO : (pCoreOf 2 (perfectCore M)).map ι =
      pCoreOf 2 (perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})) := by
    rw [← G24X3.pCoreOf_map_of_inj ι hι, hK']
  have hcardQ : Nat.card ↥((pCoreOf 2 (perfectCore M)).map ι) = (2 ^ n) ^ (1 + 2 * 4) := by
    rw [Subgroup.card_map_of_injective hι]
    exact hsp.2.1
  have hne : pCoreOf 2 (perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})) ≠ ⊥ := by
    intro h0
    rw [hO, h0, Subgroup.card_bot] at hcardQ
    have : 1 < (2 ^ n) ^ (1 + 2 * 4) :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
  rcases hcases a with rfl | rfl
  ·
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
    have hO0 : (pCoreOf 2 (perfectCore M)).map ι = Q0 σ := by
      rw [hO]
      exact pCoreOf_eq_of_parabolicFacts (parabolicFacts_a0 σ hσ3 hK4) hne
    have hZ : (centerOf (pCoreOf 2 (perfectCore M))).map ι = centerOf (Q0 σ) := by
      rw [G2Rad.map_centerOf hι, hO0]
    refine ⟨G2Rad.le_centralizer_of_map hι ?_, fun W hZW hWQ hKW => ?_⟩
    · rw [hK', hZ]
      exact perfectCore_le_centralizer σ hσ3
    · have h := eq_or_eq_of_le_normalizer σ hσ3 hK4 (exists_sigma_ne hn hK σ hσ)
        (exists_spanning hn hK σ hσ) (W := W.map ι) (hZ ▸ Subgroup.map_mono hZW)
        (hO0 ▸ Subgroup.map_mono hWQ) (hK' ▸ G2Rad.map_le_normalizer_map hKW)
      rcases h with h | h
      · exact Or.inl (Subgroup.map_injective hι (h.trans hZ.symm))
      · exact Or.inr (Subgroup.map_injective hι (h.trans hO0.symm))
  ·
    exfalso
    have hO1 := pCoreOf_eq_of_parabolicFacts (parabolicFacts_a1 σ hσ3) hne
    have h1 := lt_card_Q1 σ hσ3
    rw [← hO1, ← hO, hcardQ, hK, ← pow_mul] at h1
    norm_num at h1

theorem factG2D4ParabolicIrred_holds
    : FactG2D4ParabolicIrred := by
  intro Y _ n T M₁ M hY hpair
  rcases hY with ⟨hn, hG, hsp⟩ | ⟨-, hD, hsp⟩
  · exact G2Rad.g2ParabolicIrred hn hG hsp hpair
  · exact d4ParabolicIrred hD hsp hpair

end Amalgam

end CFSG.Quasithin.H13.NQCat.D4Irred
