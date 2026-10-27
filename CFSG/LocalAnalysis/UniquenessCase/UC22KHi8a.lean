module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sp
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sm
import CFSG.Milestones.ASVolI.C61.HypBase
import CFSG.RankThree.PartTwo.KFacts.KS116ProofTools
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure P22k8.KLift (D : Data G) (Y : Subgroup (MBar D.M D.U)) (K : Subgroup G) : Prop where
  le_M : K ≤ D.M
  perfect : ⁅K, K⁆ = K
  image : mbarImage D.M D.U K = Y
  ker_le : K ⊓ centralizer (D.U : Set G) ≤ pCoreOf 2 K
  le_normalizer_S : proofS D ≤ normalizer (K : Set G)
  le_normalizer_C : D.M ⊓ centralizer (D.U : Set G) ≤ normalizer (K : Set G)
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K
  subnormal : (K.subgroupOf D.M).IsSubnormal

namespace P22k8

variable {D : Data G} {Y : Subgroup (MBar D.M D.U)} {K : Subgroup G}

theorem KLift.mk_mem (hK : KLift D Y K) {k : G} (hk : k ∈ K) :
    (QuotientGroup.mk ⟨k, hK.le_M hk⟩ : MBar D.M D.U) ∈ Y := by
  have h : (QuotientGroup.mk ⟨k, hK.le_M hk⟩ : MBar D.M D.U) ∈ mbarImage D.M D.U K := ⟨⟨k, hK.le_M hk⟩, hk, rfl⟩
  rwa [hK.image] at h

theorem KLift.exists_mk_eq (hK : KLift D Y K) {y : MBar D.M D.U} (hy : y ∈ Y) :
    ∃ k ∈ K, ∃ hk : k ∈ D.M, (QuotientGroup.mk ⟨k, hk⟩ : MBar D.M D.U) = y := by
  rw [← hK.image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, x.2, rfl⟩

theorem KLift.le_normalizer_preN (hK : KLift D Y K) : K ≤ normalizer (preN D Y : Set G) := fun k hk =>
  P22k2.mem_normalizer_preN D (hK.le_M hk) (Subgroup.le_normalizer (hK.mk_mem hk))

theorem KLift.le_normalizer_proofIi (hK : KLift D Y K) : K ≤ normalizer (proofIi D (preN D Y) : Set G) := by
  intro k hk
  have hkM := hK.le_M hk
  exact mem_normalizer_commutator (mem_normalizer_commutator (uc22p22xf_hV D hkM)
    (uc22p22t_M_le_normalizer_jOf D hkM)) (hK.le_normalizer_preN hk)

theorem KLift.proofIi_le (hK : KLift D Y K) : proofIi D (preN D Y) ≤ K := by
  have hV := uc22p22xf_hV D
  have hNM : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  have hIU : ⁅D.U, proofN D⁆ ≤ D.U := commutator_le_of_normalizer le_rfl (hNM.trans hV)
  rw [proofIi, Subgroup.commutator_le]
  intro x hx n hn
  obtain ⟨-, hnM, hnY⟩ := (mem_preN D).1 hn
  obtain ⟨k, hk, hkM, hkn⟩ := hK.exists_mk_eq hnY
  have hxU : x ∈ D.U := hIU hx
  have hc : k⁻¹ * n ∈ centralizer (D.U : Set G) := by
    have h1 : (QuotientGroup.mk ((⟨k, hkM⟩ : ↥D.M)⁻¹ * ⟨n, hnM⟩) : MBar D.M D.U) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hkn, inv_mul_cancel]
    exact (uc22br_gt_mk_eq_one_iff hV _).1 h1
  have hxc : x * (k⁻¹ * n) = (k⁻¹ * n) * x := Subgroup.mem_centralizer_iff.1 hc x hxU
  have hcx : (k⁻¹ * n) * x⁻¹ * (k⁻¹ * n)⁻¹ = x⁻¹ := by
    have h1 : (k⁻¹ * n) * x⁻¹ = x⁻¹ * (k⁻¹ * n) := by
      calc (k⁻¹ * n) * x⁻¹ = x⁻¹ * (x * (k⁻¹ * n)) * x⁻¹ := by group
        _ = x⁻¹ * ((k⁻¹ * n) * x) * x⁻¹ := by rw [hxc]
        _ = x⁻¹ * (k⁻¹ * n) := by group
    rw [h1]
    group
  have e : ⁅x, n⁆ = ⁅x, k⁆ := by
    calc ⁅x, n⁆ = x * (k * (k⁻¹ * n)) * x⁻¹ * (k * (k⁻¹ * n))⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = x * k * ((k⁻¹ * n) * x⁻¹ * (k⁻¹ * n)⁻¹) * k⁻¹ := by group
      _ = x * k * x⁻¹ * k⁻¹ := by rw [hcx]
      _ = ⁅x, k⁆ := by rw [commutatorElement_def]
  rw [e]
  have hxC : x ∈ D.M ⊓ centralizer (D.U : Set G) :=
    ⟨D.sylowM.le (uc22p22xf_UleT D hxU), Subgroup.mem_centralizer_iff.2 fun u hu =>
      (uc22p22xf_hel D).comm hu hxU⟩
  exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hK.le_normalizer_C hxC) k).1 hk) (K.inv_mem hk)

theorem KLift.isSylowOf_sup (hK : KLift D Y K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K ⊔ proofS D) (K ⊔ proofS D) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := proofS D with hSdef
  set P := D.T ⊓ K with hPdef
  have hP := hK.sylow
  have hST : S ≤ D.T := inf_le_left
  have hSK : S ≤ normalizer (K : Set G) := hK.le_normalizer_S
  have hSP : S ≤ normalizer (P : Set G) := fun s hs =>
    mem_normalizer_inf (Subgroup.le_normalizer (hST hs)) (hSK hs)
  have hPS2 : IsPGroup 2 (P ⊔ S : Subgroup G) := D.sylowM.isPGroup.to_le (sup_le inf_le_left hST)
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨sup_le_sup_right inf_le_right _, hPS2, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (P ⊔ S) (K ⊔ S)
  rw [inf_eq_left.2 (sup_le_sup_right (inf_le_right : P ≤ K) S)] at h1
  have h2' := Subgroup.relIndex_mul_card P K
  rw [inf_eq_left.2 (inf_le_right : P ≤ K)] at h2'
  have hc1 := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hSK
  have hc2 := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hSP
  rw [sup_comm] at hc1 hc2
  have hinf : S ⊓ P = S ⊓ K := by
    rw [hPdef, ← inf_assoc, inf_eq_left.2 hST]
  rw [hinf] at hc2
  have hpos : 0 < Nat.card S * Nat.card P := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hrel : (P ⊔ S).relIndex (K ⊔ S) = P.relIndex K := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (P ⊔ S).relIndex (K ⊔ S) * (Nat.card S * Nat.card P)
        = (P ⊔ S).relIndex (K ⊔ S) * (Nat.card (P ⊔ S : Subgroup G) * Nat.card (S ⊓ K : Subgroup G)) := by
          rw [hc2]
      _ = Nat.card (K ⊔ S : Subgroup G) * Nat.card (S ⊓ K : Subgroup G) := by rw [← h1]; ring
      _ = Nat.card S * Nat.card K := hc1
      _ = P.relIndex K * (Nat.card S * Nat.card P) := by rw [← h2']; ring
  rw [hrel]
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.2

theorem KLift.pCoreOf_le_T (hK : KLift D Y K) : pCoreOf 2 (K ⊔ proofS D) ≤ D.T :=
  (P22so.pCoreOf_le_of_isSylowOf hK.isSylowOf_sup).trans (sup_le inf_le_left inf_le_left)

theorem KLift.sup_le_preMbar_normalizer (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    K ⊔ proofS D ≤ preMbar D (normalizer (Nb i : Set (MBar D.M D.U))) := by
  refine sup_le (fun x hx => ?_) (fun s hs => ?_)
  · exact (mem_preMbar D).2 ⟨hK.le_M hx, Subgroup.le_normalizer (hK.mk_mem hx)⟩
  · exact (mem_preMbar D).2 ⟨proofS_le_M D hs, (uc22p22x_S_normalizes D Ch h2 h3 h51 hH c m Nb hNb i hs).1⟩

theorem KLift.kerN_le_pCoreOf (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    (K ⊔ proofS D) ⊓ preMbar D (centralizer (Nb i : Set (MBar D.M D.U))) ≤ pCoreOf 2 (K ⊔ proofS D) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := proofS D with hSdef
  set H : Subgroup G := K ⊔ S with hHdef
  set Kh : Subgroup G := H ⊓ preMbar D (centralizer (Nb i : Set (MBar D.M D.U))) with hKhdef
  have hV := uc22p22xf_hV D
  have hZ := P22y.center_eq_bot_of_isL2Ev (h51 hH c m Nb hNb i).choose_spec.1
  have hHP := KLift.sup_le_preMbar_normalizer D Ch h2 h3 h51 hH c hNb hK
  have hHK : H ≤ normalizer (Kh : Set G) := by
    intro h hh
    obtain ⟨hM, hn⟩ := (mem_preMbar D).1 (hHP hh)
    exact mem_normalizer_inf (Subgroup.le_normalizer hh)
      (mem_normalizer_preMbar D hM (P22so.mem_normalizer_centralizer_of hn))
  have hK2 : IsPGroup 2 Kh := by
    rintro ⟨x, hxH, hxC⟩
    obtain ⟨k, hk⟩ := exists_two_pow_mem_of_mem_sup (D.sylowM.isPGroup.to_le inf_le_left)
      hK.le_normalizer_S hxH
    have hyK : x ^ (2 ^ k) ∈ Kh := Kh.pow_mem ⟨hxH, hxC⟩ _
    have hyM := hK.le_M hk
    have hyb := hK.mk_mem hk
    obtain ⟨hyM', hyc⟩ := (mem_preMbar D).1 hyK.2
    have hcen : (⟨_, hyb⟩ : ↥(Nb i)) ∈ Subgroup.center ↥(Nb i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hyc g g.2
    rw [hZ, Subgroup.mem_bot] at hcen
    have hyC : x ^ (2 ^ k) ∈ centralizer (D.U : Set G) :=
      (uc22br_gt_mk_eq_one_iff hV ⟨_, hyM⟩).1 (congrArg Subtype.val hcen)
    have hyQ : x ^ (2 ^ k) ∈ pCoreOf 2 K := hK.ker_le ⟨hk, hyC⟩
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hyQ⟩
    refine ⟨k + b, ?_⟩
    apply Subtype.ext
    have hb' : (x ^ (2 ^ k)) ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul]
    exact hb'
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hHK hK2

theorem KLift.charTwo (hK : KLift D Y K) : CFSG.QuasithinUnique.CharTwo (K ⊔ proofS D) :=
  CFSG.Quasithin.A4.charTwo_sup (charTwo_of_isSubnormal' (D.standing.charTwo D.M D.maxLocal.1)
    ((CFSG.Open.IsSubnormal.iff_subgroupOf hK.le_M).2 hK.subnormal)) hK.le_normalizer_S
    (D.sylowM.isPGroup.to_le inf_le_left)

theorem KLift.exists_quotient (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    ∃ (n : ℕ) (X : Type) (_ : Group X) (φ : ↥(K ⊔ proofS D) →* X), 1 ≤ n ∧
      Function.Surjective φ ∧ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) ∧
      φ.ker ≤ CFSG.pCore 2 ↥(K ⊔ proofS D) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := proofS D with hSdef
  set H : Subgroup G := K ⊔ S with hHdef
  have hKM : K ≤ D.M := hK.le_M
  have hHM : H ≤ D.M := sup_le hKM (proofS_le_M D)
  obtain ⟨n, hL2, -⟩ := h51 hH c m Nb hNb i
  have hn : 1 ≤ n := by
    obtain ⟨F, _, _, hF, -⟩ := hL2
    exact P22y.one_le_of_card hF
  set Nbi : Subgroup (MBar D.M D.U) := Nb i with hNbi
  set NB : Subgroup (MBar D.M D.U) := normalizer (Nbi : Set (MBar D.M D.U)) with hNB
  set π : ↥H →* MBar D.M D.U :=
    (QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (Subgroup.inclusion hHM) with hπ
  have hπN : ∀ x : ↥H, π x ∈ NB := by
    intro x
    obtain ⟨hxM, hxb⟩ := (mem_preMbar D).1 (KLift.sup_le_preMbar_normalizer D Ch h2 h3 h51 hH c hNb hK x.2)
    exact hxb
  set ψ : ↥H →* ↥NB := π.codRestrict NB hπN with hψ
  set φ : ↥H →* MulAut ↥Nbi := Nbi.normalizerMonoidHom.comp ψ with hφ
  have hφapp : ∀ (x : ↥H) (g : ↥Nbi), ((φ x g : ↥Nbi) : MBar D.M D.U) = π x * g * (π x)⁻¹ := by
    intro x g
    rfl
  set Inn : Subgroup (MulAut ↥Nbi) := (MulAut.conj : ↥Nbi →* MulAut ↥Nbi).range with hInn
  have hrange : φ.range = Inn := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      set P : Subgroup G := (Inn.comap φ).map H.subtype with hP
      have hKP : K ≤ P := by
        intro y hy
        refine ⟨⟨y, Subgroup.mem_sup_left hy⟩, ⟨⟨_, hK.mk_mem hy⟩, ?_⟩, rfl⟩
        ext g
        rfl
      have hSP : S ≤ P := by
        intro s hs
        obtain ⟨-, a, ha, q, r, hq, -, -, -, hqN⟩ := uc22p22x_lemma25 D Ch h2 h3 h51 hH c m Nb hNb i hs
        refine ⟨⟨s, Subgroup.mem_sup_right hs⟩, ⟨⟨q, hq⟩, ?_⟩, rfl⟩
        ext g
        exact (hqN g g.2).symm
      obtain ⟨y, hy, hyx⟩ := (sup_le hKP hSP) x.2
      have : y = x := Subtype.ext hyx
      subst this
      exact hy
    · rintro _ ⟨q, rfl⟩
      obtain ⟨y, hy, hyM, hyq⟩ := hK.exists_mk_eq q.2
      refine ⟨⟨y, Subgroup.mem_sup_left hy⟩, ?_⟩
      have hyq' : π ⟨y, Subgroup.mem_sup_left hy⟩ = q := hyq
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hφapp, hyq', MulAut.conj_apply]
      rfl
  have hZ := P22y.center_eq_bot_of_isL2Ev hL2
  have hinj := P22y.conj_injective_of_center_eq_bot hZ
  obtain ⟨eL⟩ := exists_mulEquiv_projSL hL2 hn
  refine ⟨n, ↥φ.range, inferInstance, φ.rangeRestrict, hn, φ.rangeRestrict_surjective,
    ⟨(MulEquiv.subgroupCongr hrange).trans ((MonoidHom.ofInjective hinj).symm.trans eL)⟩, ?_⟩
  rw [MonoidHom.ker_rangeRestrict]
  intro x hx
  have hxK : (x : G) ∈ H ⊓ preMbar D (centralizer (Nb i : Set (MBar D.M D.U))) := by
    refine ⟨x.2, (mem_preMbar D).2 ⟨hHM x.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩⟩
    have h1 := congrArg (fun α : MulAut ↥Nbi => ((α ⟨g, hg⟩ : ↥Nbi) : MBar D.M D.U)) (MonoidHom.mem_ker.1 hx)
    simp only [hφapp, MulAut.one_apply] at h1
    change g * π x = π x * g
    calc g * π x = (π x * g * (π x)⁻¹) * π x := by rw [h1]
      _ = π x * g := by group
  obtain ⟨y, hy, hyx⟩ := KLift.kerN_le_pCoreOf D Ch h2 h3 h51 hH c hNb hK hxK
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem KLift.pCoreOf_le_preMbar (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    pCoreOf 2 (K ⊔ proofS D) ≤ preMbar D (centralizer (Nb i : Set (MBar D.M D.U))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := proofS D with hSdef
  set H : Subgroup G := K ⊔ S with hHdef
  set R : Subgroup G := pCoreOf 2 H with hRdef
  have hKM : K ≤ D.M := hK.le_M
  have hHM : H ≤ D.M := sup_le hKM (proofS_le_M D)
  have hRH : R ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHR : H ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hHK : H ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK.le_normalizer_S
  have hR2 : IsPGroup 2 (R ⊓ K : Subgroup G) := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left
  set Q : Subgroup ↥(Nb i) := (mbarImage D.M D.U (R ⊓ K)).subgroupOf (Nb i) with hQdef
  have hQle : mbarImage D.M D.U (R ⊓ K) ≤ Nb i := by
    rw [← hK.image]
    exact mbarImage_mono D.M D.U inf_le_right
  have hQ2 : IsPGroup 2 Q := by
    have h1 : IsPGroup 2 (mbarImage D.M D.U (R ⊓ K)) := (hR2.comap_subtype (K := D.M)).map _
    exact h1.comap_subtype
  have hQn : Q.Normal := by
    constructor
    intro q hq y
    obtain ⟨w, hw, hwq⟩ := hq
    obtain ⟨n, hn, hnM, hny⟩ := hK.exists_mk_eq y.2
    have hwRK : (w : G) ∈ R ⊓ K := hw
    have hcR : n * w * n⁻¹ ∈ R := (mem_normalizer_iff.1 (hHR (Subgroup.mem_sup_left hn)) w).1 hwRK.1
    have hcK : n * w * n⁻¹ ∈ K := K.mul_mem (K.mul_mem hn hwRK.2) (K.inv_mem hn)
    refine ⟨⟨n, hnM⟩ * w * ⟨n, hnM⟩⁻¹, ⟨hcR, hcK⟩, ?_⟩
    change (QuotientGroup.mk' _ (⟨n, hnM⟩ * w * ⟨n, hnM⟩⁻¹) : MBar D.M D.U) =
      ((y * q * y⁻¹ : ↥(Nb i)) : MBar D.M D.U)
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hny]
    congr 2
  have hQbot := P22so.eq_bot_of_normal_of_isL2Ev (h51 hH c m Nb hNb i).choose_spec.1 hQn hQ2
  intro r hr
  have hrM : r ∈ D.M := hHM (hRH hr)
  refine (mem_preMbar D).2 ⟨hrM, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  obtain ⟨n, hn, hnM, rfl⟩ := hK.exists_mk_eq hy
  have hcR : r * n * r⁻¹ * n⁻¹ ∈ R := by
    have h1 : n * r⁻¹ * n⁻¹ ∈ R := (mem_normalizer_iff.1 (hHR (Subgroup.mem_sup_left hn)) r⁻¹).1 (R.inv_mem hr)
    have h2 := R.mul_mem hr h1
    simpa [mul_assoc] using h2
  have hcK : r * n * r⁻¹ * n⁻¹ ∈ K := K.mul_mem ((mem_normalizer_iff.1 (hHK (hRH hr)) n).1 hn) (K.inv_mem hn)
  have hcM : r * n * r⁻¹ * n⁻¹ ∈ D.M := hKM hcK
  have hcQ : (⟨QuotientGroup.mk ⟨r * n * r⁻¹ * n⁻¹, hcM⟩, hQle ⟨⟨_, hcM⟩, ⟨hcR, hcK⟩, rfl⟩⟩ : ↥(Nb i)) ∈ Q :=
    ⟨⟨_, hcM⟩, ⟨hcR, hcK⟩, rfl⟩
  rw [hQbot, Subgroup.mem_bot] at hcQ
  have hc1 : (QuotientGroup.mk ⟨r * n * r⁻¹ * n⁻¹, hcM⟩ : MBar D.M D.U) = 1 := congrArg Subtype.val hcQ
  have e : (⟨r * n * r⁻¹ * n⁻¹, hcM⟩ : ↥D.M) = ⟨r, hrM⟩ * ⟨n, hnM⟩ * ⟨r, hrM⟩⁻¹ * ⟨n, hnM⟩⁻¹ := rfl
  rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at hc1
  have hcomm := mul_inv_eq_one.1 hc1
  show (QuotientGroup.mk ⟨n, hnM⟩ : MBar D.M D.U) * QuotientGroup.mk ⟨r, hrM⟩ =
    QuotientGroup.mk ⟨r, hrM⟩ * QuotientGroup.mk ⟨n, hnM⟩
  calc (QuotientGroup.mk ⟨n, hnM⟩ : MBar D.M D.U) * QuotientGroup.mk ⟨r, hrM⟩
      = (QuotientGroup.mk ⟨r, hrM⟩ * QuotientGroup.mk ⟨n, hnM⟩ * (QuotientGroup.mk ⟨r, hrM⟩)⁻¹) *
          QuotientGroup.mk ⟨r, hrM⟩ := by rw [hcomm]
    _ = QuotientGroup.mk ⟨r, hrM⟩ * QuotientGroup.mk ⟨n, hnM⟩ := by group

theorem KLift.pCoreOf_le_centralizer (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    pCoreOf 2 (K ⊔ proofS D) ≤ centralizer (proofIi D (preN D (Nb i)) : Set G) := by
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  set S := proofS D with hSdef
  set H : Subgroup G := K ⊔ S with hHdef
  have hZ := P22y.center_eq_bot_of_isL2Ev (h51 hH c m Nb hNb i).choose_spec.1
  intro r hr
  have hrH : r ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hr
  have hrM : r ∈ D.M := sup_le hK.le_M (proofS_le_M D) hrH
  obtain ⟨hrM', hrc⟩ := (mem_preMbar D).1 (KLift.pCoreOf_le_preMbar D Ch h2 h3 h51 hH c hNb hK hr)
  rw [P22sp.mem_centralizer_iff_fix D e ρ hc (d.le i) hrM]
  obtain ⟨n, hn, s, hs, rfl⟩ := exists_mul_of_mem_sup hK.le_normalizer_S hrH
  have hnM : n ∈ D.M := hK.le_M hn
  have hsM : s ∈ D.M := proofS_le_M D hs
  obtain ⟨-, f, -, hfI, hfN⟩ := P22x.core25 D Ch h2 h3 h51 hH c e ρ hc d i hs hsM
  set nb : MBar D.M D.U := QuotientGroup.mk ⟨n, hnM⟩ with hnbdef
  set sb : MBar D.M D.U := QuotientGroup.mk ⟨s, hsM⟩ with hsbdef
  set fi : MBar D.M D.U := ((f i : ↥(Nb i)) : MBar D.M D.U) with hfidef
  have hrb : (QuotientGroup.mk ⟨n * s, hrM⟩ : MBar D.M D.U) = nb * sb := rfl
  have hnb : nb ∈ Nb i := hK.mk_mem hn
  have hb : nb * fi ∈ Nb i := (Nb i).mul_mem hnb (f i).2
  have hcen : (⟨nb * fi, hb⟩ : ↥(Nb i)) ∈ Subgroup.center ↥(Nb i) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 : (g : MBar D.M D.U) * (nb * sb) = (nb * sb) * g := by
      rw [← hrb]
      exact Subgroup.mem_centralizer_iff.1 hrc g g.2
    have h2' : sb * g * sb⁻¹ = fi * g * fi⁻¹ := by rw [hfN g g.2, d.conj_natPi f i g.2]
    have key : (nb * fi) * g * (nb * fi)⁻¹ = g := by
      calc (nb * fi) * g * (nb * fi)⁻¹ = nb * (fi * g * fi⁻¹) * nb⁻¹ := by group
        _ = nb * (sb * g * sb⁻¹) * nb⁻¹ := by rw [h2']
        _ = ((nb * sb) * g) * (nb * sb)⁻¹ := by group
        _ = (g * (nb * sb)) * (nb * sb)⁻¹ := by rw [h1]
        _ = g := by group
    change (g : MBar D.M D.U) * (nb * fi) = (nb * fi) * g
    calc (g : MBar D.M D.U) * (nb * fi) = ((nb * fi) * g * (nb * fi)⁻¹) * (nb * fi) := by rw [key]
      _ = (nb * fi) * g := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  have hb1 : nb * fi = 1 := congrArg Subtype.val hcen
  intro v hv
  rw [hrb, map_mul, Module.End.mul_apply, hfI v hv, d.pi_act f i hv, ← Module.End.mul_apply, ← map_mul, hb1,
    map_one, Module.End.one_apply]

theorem KLift.isTwoReducedIn (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    CFSG.Quasithin.IsTwoReducedIn (K ⊔ proofS D) (proofIi D (preN D (Nb i))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  set S := proofS D with hSdef
  set H : Subgroup G := K ⊔ S with hHdef
  set Ii : Subgroup G := proofIi D (preN D (Nb i)) with hIidef
  have hKM : K ≤ D.M := hK.le_M
  have hHM : H ≤ D.M := sup_le hKM (proofS_le_M D)
  have hIU : Ii ≤ D.U := P22x.proofIi_le D (preN_le_M D (Nb i))
  have hIH : Ii ≤ H := hK.proofIi_le.trans le_sup_left
  have hHI : H ≤ normalizer (Ii : Set G) := sup_le hK.le_normalizer_proofIi fun s hs =>
    (uc22p22x_S_normalizes D Ch h2 h3 h51 hH c m Nb hNb i hs).2.2
  have hHK : H ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK.le_normalizer_S
  have hNbN : Nb i ≤ mbarImage D.M D.U (proofN D) := d.le i
  have hL2 : IsL2Ev ↥(Nb i) (h51 hH c m Nb hNb i).choose := (h51 hH c m Nb hNb i).choose_spec.1
  refine ⟨hIH, hHI, (uc22p22xf_hel D).mono hIU, fun D' hD'H hHD' h2' => ?_⟩
  set Q : Subgroup ↥(Nb i) := (mbarImage D.M D.U (D' ⊓ K)).subgroupOf (Nb i) with hQdef
  have hQle : mbarImage D.M D.U (D' ⊓ K) ≤ Nb i := by
    rw [← hK.image]
    exact mbarImage_mono D.M D.U inf_le_right
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, hxq⟩ := hq
    have hxD : (x : G) ∈ D' ⊓ K := hx
    obtain ⟨k, hk⟩ := h2' x hxD.1
    have hkM : (x : G) ^ 2 ^ k ∈ D.M := D.M.pow_mem x.2 _
    have hxK : ((x : G) ^ 2 ^ k) ∈ K := K.pow_mem hxD.2 _
    have hfix := (P22sp.mem_centralizer_iff_fix D e ρ hc hNbN hkM).1 hk
    have hmem : (QuotientGroup.mk ⟨(x : G) ^ 2 ^ k, hkM⟩ : MBar D.M D.U) ∈ Nb i := hK.mk_mem hxK
    have h1 := d.faithful i hmem hfix
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have e1 : (⟨(x : G) ^ 2 ^ k, hkM⟩ : ↥D.M) = x ^ 2 ^ k := rfl
    rw [e1, QuotientGroup.mk_pow] at h1
    have hxq' : (q : MBar D.M D.U) = QuotientGroup.mk x := hxq.symm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [hxq']
    exact h1
  have hQn : Q.Normal := by
    constructor
    intro q hq y
    obtain ⟨w, hw, hwq⟩ := hq
    obtain ⟨n, hn, hnM, hny⟩ := hK.exists_mk_eq y.2
    have hwDK : (w : G) ∈ D' ⊓ K := hw
    have hcD : n * w * n⁻¹ ∈ D' := (mem_normalizer_iff.1 (hHD' (Subgroup.mem_sup_left hn)) w).1 hwDK.1
    have hcK : n * w * n⁻¹ ∈ K := K.mul_mem (K.mul_mem hn hwDK.2) (K.inv_mem hn)
    refine ⟨⟨n, hnM⟩ * w * ⟨n, hnM⟩⁻¹, ⟨hcD, hcK⟩, ?_⟩
    change (QuotientGroup.mk' _ (⟨n, hnM⟩ * w * ⟨n, hnM⟩⁻¹) : MBar D.M D.U) =
      ((y * q * y⁻¹ : ↥(Nb i)) : MBar D.M D.U)
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hny]
    congr 2
  have hQbot := P22so.eq_bot_of_normal_of_isL2Ev hL2 hQn hQ2
  intro x hx
  have hxH := hD'H hx
  have hxM : x ∈ D.M := hHM hxH
  apply KLift.pCoreOf_le_centralizer D Ch h2 h3 h51 hH c hNb hK
  refine KLift.kerN_le_pCoreOf D Ch h2 h3 h51 hH c hNb hK
    ⟨hxH, (mem_preMbar D).2 ⟨hxM, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩⟩
  obtain ⟨n, hn, hnM, rfl⟩ := hK.exists_mk_eq hg
  have hcD : x * n * x⁻¹ * n⁻¹ ∈ D' := by
    have h1 : n * x⁻¹ * n⁻¹ ∈ D' := (mem_normalizer_iff.1 (hHD' (Subgroup.mem_sup_left hn)) x⁻¹).1 (D'.inv_mem hx)
    have h2'' := D'.mul_mem hx h1
    simpa [mul_assoc] using h2''
  have hcK : x * n * x⁻¹ * n⁻¹ ∈ K := K.mul_mem ((mem_normalizer_iff.1 (hHK hxH) n).1 hn) (K.inv_mem hn)
  have hcM : x * n * x⁻¹ * n⁻¹ ∈ D.M := hKM hcK
  have hcQ : (⟨QuotientGroup.mk ⟨x * n * x⁻¹ * n⁻¹, hcM⟩, hQle ⟨⟨_, hcM⟩, ⟨hcD, hcK⟩, rfl⟩⟩ : ↥(Nb i)) ∈ Q :=
    ⟨⟨_, hcM⟩, ⟨hcD, hcK⟩, rfl⟩
  rw [hQbot, Subgroup.mem_bot] at hcQ
  have hc1 : (QuotientGroup.mk ⟨x * n * x⁻¹ * n⁻¹, hcM⟩ : MBar D.M D.U) = 1 := congrArg Subtype.val hcQ
  have e : (⟨x * n * x⁻¹ * n⁻¹, hcM⟩ : ↥D.M) = ⟨x, hxM⟩ * ⟨n, hnM⟩ * ⟨x, hxM⟩⁻¹ * ⟨n, hnM⟩⁻¹ := rfl
  rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at hc1
  have hcomm := mul_inv_eq_one.1 hc1
  show (QuotientGroup.mk ⟨n, hnM⟩ : MBar D.M D.U) * QuotientGroup.mk ⟨x, hxM⟩ =
    QuotientGroup.mk ⟨x, hxM⟩ * QuotientGroup.mk ⟨n, hnM⟩
  calc (QuotientGroup.mk ⟨n, hnM⟩ : MBar D.M D.U) * QuotientGroup.mk ⟨x, hxM⟩
      = (QuotientGroup.mk ⟨x, hxM⟩ * QuotientGroup.mk ⟨n, hnM⟩ * (QuotientGroup.mk ⟨x, hxM⟩)⁻¹) *
          QuotientGroup.mk ⟨x, hxM⟩ := by rw [hcomm]
    _ = QuotientGroup.mk ⟨x, hxM⟩ * QuotientGroup.mk ⟨n, hnM⟩ := by group

theorem jOf_sup_eq (D : Data G) (K : Subgroup G) : jOf (D.T ⊓ K ⊔ proofS D) = jOf D.T := by
  set TH : Subgroup G := D.T ⊓ K ⊔ proofS D with hTHdef
  have hJTH : jOf D.T ≤ TH := (P22s.jOf_le_proofS D).trans le_sup_right
  have hTHT : TH ≤ D.T := sup_le inf_le_left inf_le_left
  obtain ⟨A, hA⟩ := exists_mem_elemThompsonFamily ↥D.T
  have hB := isMax_of_mem_family hA
  have hBTH : A.map D.T.subtype ≤ TH := (le_jOf_of_isMax hB).trans hJTH
  apply le_antisymm
  · exact jOf_le_of_forall_isMax fun A' hA' => le_jOf_of_isMax (P22so.isMax_of_isMax_of_le hB hBTH hTHT hA')
  · exact jOf_le_of_forall_isMax fun A' hA' =>
      le_jOf_of_isMax (P22so.isMax_of_le hA' ((le_jOf_of_isMax hA').trans hJTH) hTHT)

theorem KLift.exists_minParabolic (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hK : KLift D (Nb i) K) :
    ∃ Mx : Subgroup G, CFSG.Quasithin.MinParabolic (K ⊔ proofS D) (D.T ⊓ K ⊔ proofS D) Mx := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := K ⊔ proofS D with hHdef
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K ⊔ proofS D) H :=
    CFSG.ABGLocalTools.isSylowOf_iff.1 hK.isSylowOf_sup
  obtain ⟨n, X, _, φ, hn, hφ, ⟨eX⟩, hker⟩ := KLift.exists_quotient D Ch h2 h3 h51 hH c hNb hK
  set F := GaloisField 2 n with hFdef
  letI : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
  set eS : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    eX.trans (CFSG.RankThree.PartTwo.KFacts.KS116Proof.projSLEquiv F).symm with heSdef
  haveI : Finite X := Finite.of_equiv _ eS.symm.toEquiv
  have hL2 : IsL2Ev X n := ⟨F, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hF],
    ⟨eS.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)⟩⟩
  have hker' : φ.ker = CFSG.pCore 2 ↥H := by
    refine le_antisymm hker ?_
    have hnorm : ((CFSG.pCore 2 ↥H).map φ).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := ↥H)).map φ hφ
    have h2g : IsPGroup 2 ((CFSG.pCore 2 ↥H).map φ) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥H)).map φ
    have hbot := P22so.eq_bot_of_normal_of_isL2Ev hL2 hnorm h2g
    intro x hx
    rw [MonoidHom.mem_ker]
    have hx' : φ x ∈ (CFSG.pCore 2 ↥H).map φ := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hx'
    exact hx'
  have hY : ∀ S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index → CFSG.ASVolI.burnsideC5h_p1_UMaxIn ⊤ S :=
    CFSG.ASVolI.burnsideC56_umax_of_mulEquiv eS fun S hS hSi =>
      CFSG.ASVolI.burnsideC5h_p1_umax_sl2 (F := F) (n := n) hn hF hS hSi
  have hY2 : 2 ∣ Nat.card X := by
    rw [Nat.card_congr eS.toEquiv, CFSG.ASVolI.burnsideC5h_p1_sl2_card F, hF]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  obtain ⟨Mx, hMx⟩ := CFSG.ASVolI.burnsideC56_uniqueMax_of_quot hT le_rfl Subgroup.le_normalizer
    (sup_eq_left.mpr hT.1) φ hφ hker' hY
  exact ⟨Mx, ⟨hT, CFSG.ASVolI.burnsideC56_not_normal_of_quot hT le_rfl Subgroup.le_normalizer φ hφ hker' hY2,
    hMx⟩⟩

end P22k8

end CFSG.LocalAnalysis.UniquenessCase.UC22
