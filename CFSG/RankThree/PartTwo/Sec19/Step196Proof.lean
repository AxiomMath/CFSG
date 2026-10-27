module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec19.Step196KFact
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

namespace Step196Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_eq_one {y : G} {k : ℕ} (hk : y ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨k, Subtype.ext ?_⟩
  change (y ^ n) ^ 3 ^ k = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem le_inf_centralizer_sup_theta {L B : Subgroup G} (hB3 : IsPGroup 3 B)
    (hBC : B ≤ Sec4.thetaQuotCentralizer L) :
    L ≤ (L ⊓ Subgroup.centralizer (B : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hθ3 : ¬ 3 ∣ Nat.card θL := (Sec6.theta_solvable_and_not_dvd L).2
  intro l hl
  set α : B →* MulAut G := MulAut.conj.comp B.subtype
  obtain ⟨y, hy, hyfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hB3 α θL
    hθ3 l).2 (by
      intro a x hx
      change l⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ θL
      have ha := hBC a.2
      have h1 : l⁻¹ * ((a : G) * l * (a : G)⁻¹) ∈ θL :=
        (Sec6.mem_thetaQuotCentralizer_iff.mp ha).2 l hl
      have h2 : (a : G) * (l⁻¹ * x) * (a : G)⁻¹ ∈ θL :=
        (Subgroup.mem_normalizer_iff.mp (Sec6.normalizer_le_normalizer_theta L
          (Sec6.thetaQuotCentralizer_le_normalizer L ha)) _).mp hx
      have h3 := θL.mul_mem h1 h2
      rwa [show l⁻¹ * ((a : G) * l * (a : G)⁻¹) * ((a : G) * (l⁻¹ * x) * (a : G)⁻¹) =
        l⁻¹ * ((a : G) * x * (a : G)⁻¹) by group] at h3)
  have hyL : y ∈ L := by
    have := L.mul_mem hl (Sec6.theta_le L hy)
    simpa using this
  have hyB : y ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : b * y * b⁻¹ = y := hyfix ⟨b, hb⟩
    calc b * y = (b * y * b⁻¹) * b := by group
      _ = y * b := by rw [h1]
  rw [show l = y * (y⁻¹ * l) by group]
  refine Subgroup.mul_mem_sup ⟨hyL, hyB⟩ ?_
  have := inv_mem hy
  simpa using this

variable {A L E M : Subgroup G} {c : G}

theorem normalizer_le_of_le (hctx : Ctx195 G A c L E M) {X : Subgroup G} (hXE : X ≤ E)
    (hX : ¬ IsCyclic X) : Subgroup.normalizer (X : Set G) ≤ M := by
  have hE := hctx.isE27
  have h9 : 9 ≤ Nat.card X :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun x hx => hE.1.2 x (hXE hx)) hX
  exact (normalizer_le_gamma hXE (two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hXE)
    h9)).trans hctx.mem_scriptM.2

theorem le_normalizer_of_ctx195 (hctx : Ctx195 G A c L E M) :
    E ≤ Subgroup.normalizer (L : Set G) :=
  (hctx.le_sup.trans inf_le_left).trans (sup_le Subgroup.le_normalizer hctx.mem_lA.2.1)

theorem theta_le_of_ctx195 (hctx : Ctx195 G A c L E M) :
    inSubgroup (aschbacherSolvableCore 3) L ≤ M := by
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hE := hctx.isE27
  have hEθ : E ≤ Subgroup.normalizer (θL : Set G) :=
    (le_normalizer_of_ctx195 hctx).trans (Sec6.normalizer_le_normalizer_theta L)
  have hcop : Nat.Coprime 3 (Nat.card θL) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (Sec6.theta_solvable_and_not_dvd L).2
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 2
    Nat.prime_three E θL hE.1 (by rw [hE.2]; norm_num) hEθ hcop
  rw [← hgen]
  refine iSup₂_le fun F hF => ?_
  have hFE : F ≤ E := hF.1
  have h2 : 2 ≤ CFSG.Open.pRank 3 F :=
    two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hFE) (by rw [hF.2]; norm_num)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((normalizer_le_gamma hFE h2).trans hctx.mem_scriptM.2))

theorem thetaQuotMulAut_normalizerMonoidHom_of_mem {L : Subgroup G} (l : L) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨l, Subgroup.le_normalizer l.2⟩) =
      MulAut.conj (l : L ⧸ aschbacherSolvableCore 3 L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1

theorem exists_pow_mem_sup {L : Subgroup G}
    (hout : OutThreeClosed (L ⧸ aschbacherSolvableCore 3 L)) {S : Set G}
    (hSN : S ⊆ Subgroup.normalizer (L : Set G)) (hS3 : ∀ y ∈ S, ∃ k : ℕ, y ^ 3 ^ k = 1)
    {y : G} (hy : y ∈ Subgroup.closure S) :
    ∃ k : ℕ, y ^ 3 ^ k ∈ L ⊔ Sec4.thetaQuotCentralizer L := by
  have hKN : Subgroup.closure S ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.closure_le _).mpr hSN
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L),
      ρ = (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom := ⟨_, rfl⟩
  have hgen : ∀ x (hx : x ∈ Subgroup.closure S), ρ ⟨x, hKN hx⟩ ∈
      Subgroup.closure {τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) | ∃ k : ℕ, τ ^ 3 ^ k = 1} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := hS3 x hx
      refine Subgroup.subset_closure ⟨k, ?_⟩
      have h1 : (⟨x, hKN (Subgroup.subset_closure hx)⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k =
          1 := Subtype.ext (by simpa using hk)
      rw [← map_pow, h1, map_one]
    | one =>
      have e : (⟨1, hKN (Subgroup.one_mem _)⟩ : Subgroup.normalizer (L : Set G)) = 1 := rfl
      rw [e, map_one]
      exact Subgroup.one_mem _
    | mul x z hx hz ihx ihz =>
      have e : (⟨x * z, hKN (Subgroup.mul_mem _ hx hz)⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨x, hKN hx⟩ * ⟨z, hKN hz⟩ := rfl
      rw [e, map_mul]
      exact Subgroup.mul_mem _ ihx ihz
    | inv x hx ih =>
      have e : (⟨x⁻¹, hKN (Subgroup.inv_mem _ hx)⟩ : Subgroup.normalizer (L : Set G)) =
          (⟨x, hKN hx⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact Subgroup.inv_mem _ ih
  obtain ⟨k, lb, hlb⟩ := hout _ (hgen y hy)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
  refine ⟨k, ?_⟩
  have hρl : ρ ⟨l, Subgroup.le_normalizer l.2⟩ =
      MulAut.conj (l : L ⧸ aschbacherSolvableCore 3 L) := by
    rw [hρ, MonoidHom.comp_apply, thetaQuotMulAut_normalizerMonoidHom_of_mem l]
  obtain ⟨u, hu⟩ : ∃ u : Subgroup.normalizer (L : Set G),
      u = ⟨y, hKN hy⟩ ^ 3 ^ k * (⟨l, Subgroup.le_normalizer l.2⟩)⁻¹ := ⟨_, rfl⟩
  have hρu : ρ u = 1 := by
    rw [hu, map_mul, map_pow, map_inv, hρl, hlb, mul_inv_cancel]
  have huC : (u : G) ∈ Sec4.thetaQuotCentralizer L :=
    ⟨u, MonoidHom.mem_ker.mpr (hρ ▸ hρu), rfl⟩
  have hu' : (u : G) = y ^ 3 ^ k * (l : G)⁻¹ := by
    rw [hu, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
  rw [show y ^ 3 ^ k = (u : G) * l by rw [hu', inv_mul_cancel_right]]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right huC) (Subgroup.mem_sup_left l.2)

end Step196Proof

open Step196Proof

variable {G : Type} [Group G] [Finite G] {A L E M : Subgroup G} {c : G}

theorem le_of_ctx195 (hctx : Ctx195 G A c L E M) : L ≤ M := by
  have hE := hctx.isE27
  have hB3 : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) :=
    hE.isPGroup.to_le inf_le_left
  refine (le_inf_centralizer_sup_theta hB3 inf_le_right).trans (sup_le ?_ (theta_le_of_ctx195 hctx))
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_le hctx inf_le_left hctx.centralizer_noncyclic))

theorem thetaQuotCentralizer_le_of_ctx195 (hctx : Ctx195 G A c L E M) :
    Sec4.thetaQuotCentralizer L ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set T := E ⊓ L with hT
  set Y := T ⊔ θL with hY
  have hE := hctx.isE27
  have hT3 : IsPGroup 3 T := hE.isPGroup.to_le inf_le_left
  have hθ3 : ¬ 3 ∣ Nat.card θL := (Sec6.theta_solvable_and_not_dvd L).2
  have hTθ : T ≤ Subgroup.normalizer (θL : Set G) :=
    inf_le_right.trans (Sec6.le_normalizer_theta L)
  have hTY : T ≤ Y := le_sup_left
  have hcardY := Sec6.card_sup_mul_card_inf hTθ
  rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hθ3 hT3, Subgroup.card_bot,
    mul_one] at hcardY
  have hcY : Nat.card Y = Nat.card T * Nat.card θL := hcardY
  have hrel := Subgroup.relIndex_mul_card T Y
  rw [inf_eq_left.mpr hTY, hcY] at hrel
  have hrel' : T.relIndex Y = Nat.card θL := by
    have hpos : 0 < Nat.card T := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hrel, mul_comm])
  have hSyl : IsSylowOf 3 T Y := isSylowOf_iff.mpr ⟨hTY, hT3, by rw [hrel']; exact hθ3⟩
  have hCY : Sec4.thetaQuotCentralizer L ≤ Subgroup.normalizer (Y : Set G) := by
    apply Sec6.le_normalizer_sup_of_conj
    · intro a ha x hx
      have h1 : x⁻¹ * (a * x * a⁻¹) ∈ θL := (Sec6.mem_thetaQuotCentralizer_iff.mp ha).2 x hx.2
      rw [show a * x * a⁻¹ = x * (x⁻¹ * (a * x * a⁻¹)) by group]
      exact Subgroup.mul_mem_sup hx h1
    · intro a ha x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (Sec6.normalizer_le_normalizer_theta L
          (Sec6.thetaQuotCentralizer_le_normalizer L ha)) x).mp hx)
  refine (Sec18.le_sup_normalizer_of_isSylowOf hSyl hCY).trans (sup_le (sup_le ?_ ?_) ?_)
  · exact inf_le_left.trans (le_of_mem_scriptM_gamma hE hctx.mem_scriptM)
  · exact theta_le_of_ctx195 hctx
  · exact normalizer_le_of_le hctx inf_le_left hctx.inf_noncyclic

theorem step196_of_outThreeClosed (h45 : Sec4.Item4_5) (h131 : Item131)
    (hspor : SporadicModels131) (hout : OutThreeClosed131) : Step196 := by
  intro G _ _ A c L E M hctx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L :=
    ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT,
      hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hE := hctx.isE27
  have hA := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  have hOut : OutThreeClosed (L ⧸ aschbacherSolvableCore 3 L) :=
    hout _ (Sec12.isQuasisimple_thetaQuot_of_mem hL)
      (Step1910O2Proof.type_of_mem h131 hspor hD hctx.mem_L)
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set S : Set G := {y | y ∈ H ∧ ∃ k : ℕ, y ^ 3 ^ k = 1} with hSdef
  set K := Subgroup.closure S with hKdef
  have hKH : K ≤ H := (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hSN : S ⊆ Subgroup.normalizer (L : Set G) := by
    rintro y ⟨hyH, k, hk⟩
    exact Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hctx.toTheoremFourHyp hc3 hL
      (isPGroup_zpowers_of_pow_eq_one hk) (Subgroup.zpowers_le.mpr hyH) (Subgroup.mem_zpowers y)
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := (Subgroup.closure_le _).mpr hSN
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun a ha x hx => ?_
    have hle : K ≤ K.comap (MulAut.conj a).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun y hy => Subgroup.subset_closure ?_
      obtain ⟨hyH, k, hk⟩ := hy
      refine ⟨H.mul_mem (H.mul_mem ha hyH) (H.inv_mem ha), k, ?_⟩
      change (a * y * a⁻¹) ^ 3 ^ k = 1
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
    exact hle hx
  have hEH : E ≤ H := by
    intro e he
    have hec : e ∈ Subgroup.centralizer ({c} : Set G) :=
      (sup_le (Sec6.le_centralizer_of_mem_thetaComponentsAt hL) (le_centralizer_of_mem hA.1.1 hcA))
        ((hctx.le_sup.trans inf_le_left) he)
    exact Sec12.mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hec)
  obtain ⟨Q, hEQ⟩ := (hE.isPGroup.comap_subtype (K := H)).exists_le_sylow
  set P₀ : Subgroup G := (Q : Subgroup H).map H.subtype with hP₀
  have hP₀H : IsSylowOf 3 P₀ H := ⟨Q, rfl⟩
  have hEP₀ : E ≤ P₀ := fun e he => ⟨⟨e, hEH he⟩, hEQ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  have hP₀3 : IsPGroup 3 P₀ := hP₀H.isPGroup
  have hP₀K : P₀ ≤ K := by
    intro x hx
    refine Subgroup.subset_closure ⟨hP₀H.le hx, ?_⟩
    obtain ⟨k, hk⟩ := hP₀3 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨Q₀, hQ₀⟩ := hP₀H.of_le hP₀K hKH
  have hNP₀ : Subgroup.normalizer (P₀ : Set G) ≤ M :=
    rank3II_19_3 hctx.hyp191 hE hctx.mem_scriptM hEP₀
      (CFSG.BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup hP₀3 _)
  set W := L ⊔ Sec4.thetaQuotCentralizer L with hW
  have hWM : W ≤ M := sup_le (le_of_ctx195 hctx) (thetaQuotCentralizer_le_of_ctx195 hctx)
  have hNW : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    apply Sec6.le_normalizer_sup_of_conj
    · intro a ha x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp ha x).mp hx)
    · intro a ha x hx
      exact Subgroup.mem_sup_right (Sec6.conj_mem_thetaQuotCentralizer hx ha)
  have hKW : K ≤ (Q₀ : Subgroup K).map K.subtype ⊔ (K ⊓ W) :=
    Sec6.le_sylow_sup_of_forall_pow_mem inf_le_left
      ((le_inf Subgroup.le_normalizer (hKN.trans hNW)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      (fun y hy => by
        obtain ⟨k, hk⟩ := exists_pow_mem_sup hOut hSN (fun y hy => hy.2) hy
        exact ⟨k, K.pow_mem hy _, hk⟩) Q₀
  rw [hQ₀] at hKW
  have hKM : K ≤ M :=
    hKW.trans (sup_le (Subgroup.le_normalizer.trans hNP₀) (inf_le_right.trans hWM))
  exact (Sec18.le_sup_normalizer_of_isSylowOf ⟨Q₀, hQ₀⟩ hHK).trans (sup_le hKM hNP₀)

theorem step196_of
    (h45 : Sec4.Item4_5)
    (h131 : Item131) (hspor : SporadicModels131) : Step196 :=
  step196_of_outThreeClosed h45 h131 hspor outThreeClosed131

end CFSG.RankThree.PartTwo.Sec19
