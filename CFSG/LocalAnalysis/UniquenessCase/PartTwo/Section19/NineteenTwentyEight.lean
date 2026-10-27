module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.CtxLemmas
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.CGT.PushingUpLit.A78Sp4.AuxLemmas
public import CFSG.CGT.PushingUpLit.SolKAb.CyclicTI
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20y
public import CFSG.CGT.PushingUpLit.EightOneFinalSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Thompson
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem normal_inter_IOf_subgroupOf (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) :
    ((H ⊓ IOf D p L).subgroupOf (H ⊓ D.M)).Normal := by
  have hIleM : IOf D p L ≤ D.M := IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le
  have hKleHM : H ⊓ IOf D p L ≤ H ⊓ D.M := le_inf inf_le_left (inf_le_right.trans hIleM)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKleHM]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx.1, le_normalizer_IOf D h.ctx22.ctx.hyp.hL.1 hx.2⟩

theorem pCoreOf_inter_IOf_le_sylow (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) :
    pCoreOf 2 (H ⊓ IOf D p L) ≤ S := by
  have hr2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I : Subgroup G := IOf D p L
  let O : Subgroup G := pCoreOf 2 (H ⊓ I)
  let K : Subgroup G := H ⊓ I
  let HM : Subgroup G := H ⊓ D.M
  have hIleM : I ≤ D.M := IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le
  have hKleHM : K ≤ HM := le_inf inf_le_left (inf_le_right.trans hIleM)
  have hKnorm : (K.subgroupOf HM).Normal := normal_inter_IOf_subgroupOf D h
  have hOleO2HM : O ≤ pCoreOf 2 HM :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K HM hKleHM hKnorm
  have hO2HM_le_S : pCoreOf 2 HM ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hS)
  exact hOleO2HM.trans hO2HM_le_S

theorem sylow_le_normalizer_inter_IOf (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) :
    S ≤ normalizer (H ⊓ IOf D p L : Set G) := by
  let I : Subgroup G := IOf D p L
  let K : Subgroup G := H ⊓ I
  let HM : Subgroup G := H ⊓ D.M
  have hIleM : I ≤ D.M := IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le
  have hKleHM : K ≤ HM := le_inf inf_le_left (inf_le_right.trans hIleM)
  have hKnorm : (K.subgroupOf HM).Normal := normal_inter_IOf_subgroupOf D h
  exact hS.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKleHM).mp hKnorm)

theorem A_le_normalizer_pCoreOf_inter_IOf (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) :
    A ≤ normalizer (pCoreOf 2 (H ⊓ IOf D p L) : Set G) := by
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  exact (le_inf hAH h.ctx22.ctx.hA).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ IOf D p L))

theorem le_normalizer_sup_pCoreOf_inter_IOf (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) :
    S ≤ normalizer ((A ⊔ pCoreOf 2 (H ⊓ IOf D p L) : Subgroup G) : Set G) := by
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
  have hOleH : pCoreOf 2 (H ⊓ IOf D p L) ≤ H :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ IOf D p L)).trans inf_le_left
  have hOleM : pCoreOf 2 (H ⊓ IOf D p L) ≤ D.M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ IOf D p L)).trans
      (inf_le_right.trans (IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le))
  have hE_le : A ⊔ pCoreOf 2 (H ⊓ IOf D p L) ≤ H ⊓ D.M :=
    sup_le (le_inf hAH hAM) (le_inf hOleH hOleM)
  exact hS.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hE_le).mp h25)

theorem permutes_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) : Permutes A S := by
  exact UC22.uc22pw_permutes_of_split (T := S)
    (S := pCoreOf 2 (H ⊓ IOf D p L))
    (Ê := A ⊔ pCoreOf 2 (H ⊓ IOf D p L))
    (pCoreOf_inter_IOf_le_sylow D h hS)
    (le_normalizer_sup_pCoreOf_inter_IOf D h h25 hS)
    (by rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (A_le_normalizer_pCoreOf_inter_IOf D h)])

@[expose] def Gap19_28 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h) : Prop :=
  ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) →
    (S ⊓ (⨅ a ∈ A, centModEl (pCoreOf 2 (H ⊓ IOf D p L)) a)).relIndex S ≤ 2

theorem kernel_le_pCoreOf_sup {A S O : Subgroup G} (hcomm : IsMulCommutative ↥A)
    (hOS : O ≤ S) (hAO : A ≤ normalizer (O : Set G)) (hSO : S ≤ normalizer (O : Set G))
    (hSE : S ≤ normalizer ((A ⊔ O : Subgroup G) : Set G)) (hS2 : IsPGroup 2 S) :
    S ⊓ (⨅ a ∈ A, centModEl O a) ≤ pCoreOf 2 (A ⊔ S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₀ := S ⊓ (⨅ a ∈ A, centModEl O a) with hS₀
  have hmem : ∀ s, s ∈ S₀ ↔ s ∈ S ∧ s ∈ normalizer (O : Set G) ∧
      ∀ a ∈ A, s * a * s⁻¹ * a⁻¹ ∈ O := by
    intro s
    constructor
    · rintro ⟨hs, hs'⟩
      have h1 : ∀ a ∈ A, s ∈ centModEl O a := fun a ha =>
        Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hs' a) ha
      exact ⟨hs, (h1 1 A.one_mem).1, fun a ha => (h1 a ha).2⟩
    · rintro ⟨hs, hsN, hsA⟩
      exact ⟨hs, Subgroup.mem_iInf.mpr fun a => Subgroup.mem_iInf.mpr fun ha => ⟨hsN, hsA a ha⟩⟩
  have hcA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hS₀le : S₀ ≤ A ⊔ S := fun s hs => Subgroup.mem_sup_right ((hmem s).1 hs).1
  have hS₀2 : IsPGroup 2 S₀ := hS2.to_le inf_le_left
  have hnorm : ∀ X : Subgroup G, (∀ b ∈ X, ∀ s ∈ S₀, b * s * b⁻¹ ∈ S₀) →
      X ≤ normalizer (S₀ : Set G) := by
    intro X hX b hb
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨hX b hb s, fun hs => ?_⟩
    have := hX b⁻¹ (X.inv_mem hb) _ hs
    simpa [mul_assoc] using this
  have hAN : A ≤ normalizer (S₀ : Set G) := by
    refine hnorm A fun b hb s hs => ?_
    obtain ⟨hsS, hsN, hsA⟩ := (hmem s).1 hs
    have hbN : b ∈ normalizer (O : Set G) := hAO hb
    have ho : s * b⁻¹ * s⁻¹ * b⁻¹⁻¹ ∈ O := hsA b⁻¹ (A.inv_mem hb)
    have hbo : b * (s * b⁻¹ * s⁻¹ * b⁻¹⁻¹) * b⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp hbN _).mp ho
    have hEq : b * s * b⁻¹ = (b * (s * b⁻¹ * s⁻¹ * b⁻¹⁻¹) * b⁻¹) * s := by group
    refine (hmem _).2 ⟨?_, ?_, ?_⟩
    · rw [hEq]; exact S.mul_mem (hOS hbo) hsS
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hsN) (Subgroup.inv_mem _ hbN)
    · intro a ha
      have hab : b⁻¹ * a * b = a := by
        have := hcA a ha b hb
        calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
          _ = b⁻¹ * (b * a) := by rw [this]
          _ = a := by group
      have hc' : b * (s * a * s⁻¹ * a⁻¹) * b⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp hbN _).mp (hsA a ha)
      have hab' : a * b⁻¹ * a⁻¹ = b⁻¹ := by
        have := hcA a ha b⁻¹ (A.inv_mem hb)
        calc a * b⁻¹ * a⁻¹ = (b⁻¹ * a) * a⁻¹ := by rw [this]
          _ = b⁻¹ := by group
      have hEq2 : b * s * b⁻¹ * a * (b * s * b⁻¹)⁻¹ * a⁻¹ =
          b * (s * a * s⁻¹ * a⁻¹) * b⁻¹ := by
        calc b * s * b⁻¹ * a * (b * s * b⁻¹)⁻¹ * a⁻¹
            = b * s * (b⁻¹ * a * b) * s⁻¹ * b⁻¹ * a⁻¹ := by group
          _ = b * s * a * s⁻¹ * b⁻¹ * a⁻¹ := by rw [hab]
          _ = b * (s * a * s⁻¹ * a⁻¹) * (a * b⁻¹ * a⁻¹) := by group
          _ = b * (s * a * s⁻¹ * a⁻¹) * b⁻¹ := by rw [hab']
      rw [hEq2]; exact hc'
  have hSN : S ≤ normalizer (S₀ : Set G) := by
    refine hnorm S fun x hx s hs => ?_
    obtain ⟨hsS, hsN, hsA⟩ := (hmem s).1 hs
    have hxN : x ∈ normalizer (O : Set G) := hSO hx
    have hAOs : A ⊔ O ≤ centModEl O s := by
      refine sup_le (fun a ha => ⟨hAO ha, ?_⟩) (fun o ho => ⟨Subgroup.le_normalizer ho, ?_⟩)
      · have h := O.inv_mem (hsA a ha)
        have hEq : (s * a * s⁻¹ * a⁻¹)⁻¹ = a * s * a⁻¹ * s⁻¹ := by group
        rwa [hEq] at h
      · have h1 : s * o⁻¹ * s⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hsN _).mp (O.inv_mem ho)
        have hEq : o * s * o⁻¹ * s⁻¹ = o * (s * o⁻¹ * s⁻¹) := by group
        rw [hEq]; exact O.mul_mem ho h1
    refine (hmem _).2 ⟨S.mul_mem (S.mul_mem hx hsS) (S.inv_mem hx),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hsN) (Subgroup.inv_mem _ hxN), fun a ha => ?_⟩
    have ha' : x⁻¹ * a * x ∈ A ⊔ O := by
      have h := (Subgroup.mem_normalizer_iff.mp (hSE (S.inv_mem hx)) a).mp
        (Subgroup.mem_sup_left ha)
      simpa using h
    have hc := (hAOs ha').2
    have hc2 : s * (x⁻¹ * a * x) * s⁻¹ * (x⁻¹ * a * x)⁻¹ ∈ O := by
      have h := O.inv_mem hc
      have hEq : ((x⁻¹ * a * x) * s * (x⁻¹ * a * x)⁻¹ * s⁻¹)⁻¹ =
          s * (x⁻¹ * a * x) * s⁻¹ * (x⁻¹ * a * x)⁻¹ := by group
      rwa [hEq] at h
    have hc3 := (Subgroup.mem_normalizer_iff.mp hxN _).mp hc2
    have hEq : x * s * x⁻¹ * a * (x * s * x⁻¹)⁻¹ * a⁻¹ =
        x * (s * (x⁻¹ * a * x) * s⁻¹ * (x⁻¹ * a * x)⁻¹) * x⁻¹ := by group
    rw [hEq]; exact hc3
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hS₀le (sup_le hAN hSN) hS₀2

theorem exists_tInvariant_sylow_of_isSylow {K : Subgroup G} {t : G}
    (ht2 : ∃ k : ℕ, orderOf t = 2 ^ k) (htK : t ∈ normalizer (K : Set G))
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K) :
    ∃ S' : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S' K ∧
      t ∈ normalizer (S' : Set G) ∧ Nat.card S' = Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := ht2
  have hS₀ : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers]; exact hk)
  obtain ⟨P, hP, hPnorm⟩ :=
    CFSG.CGT.PushingUpLit.EightOneFinal.exists_isSylowOf_normalized hS₀
      (Subgroup.zpowers_le.mpr htK)
  have hP' : CFSG.ABGLocalTools.IsSylowOf 2 P K := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact hP
  refine ⟨P, hP', ?_, ?_⟩
  · exact hPnorm (Subgroup.mem_zpowers t)
  · rw [hP'.card_eq, hS.card_eq]

theorem sylow_ne_bot_of_ctx (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) : S ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0data := inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne
  have hV0p : IsPGroup 2 V₀ := hV0data.1.2.2.2.isPGroup
  have hV0H : V₀ ≤ H := h.hH ▸ h.ctx22.hV₀
  have hV0M : V₀ ≤ D.M := hV0data.1.2.1
  have hV0HM : V₀ ≤ H ⊓ D.M := le_inf hV0H hV0M
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV0p
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hk
      exact absurd (Subgroup.eq_bot_of_card_eq V₀ hk) hV0ne
    · exact hkpos
  have h2dvd : 2 ∣ Nat.card (H ⊓ D.M : Subgroup G) := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hV0HM)
    rw [hk]
    exact dvd_pow_self 2 hkpos.ne'
  exact CFSG.ABGTheoremB.V56.ne_bot_of_isSylowOf Nat.prime_two hS h2dvd

theorem exists_normalU_of_trichotomy (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx22.ctx)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (htri : ((((Subgroup.center ↥S).map S.subtype : Subgroup G)).subgroupOf (A ⊔ S)).Normal ∨
      (((CFSG.Open.thompsonSubgroup S).subgroupOf (A ⊔ S)).Normal) ∨
        (S ⊓ centralizer (A : Set G)).relIndex S = 2) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ U ≤ S ∧
      normalizer (S : Set G) ≤ normalizer (U : Set G) ∧ A ≤ normalizer (U : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSne : S ≠ ⊥ := sylow_ne_bot_of_ctx D h hS
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
  rcases htri with hZ | hJ | hC
  ·
    refine ⟨(Subgroup.center ↥S).map S.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
    · intro hbot
      haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).2 hSne
      haveI : Nontrivial (Subgroup.center ↥S) := hS.isPGroup.center_nontrivial
      have hcenterbot : Subgroup.center ↥S = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).mp hbot
      exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hcenterbot
    · haveI : (Subgroup.center ↥S).Characteristic := Subgroup.centerCharacteristic
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (Subgroup.center ↥S)
    · have hZle : (Subgroup.center ↥S).map S.subtype ≤ A ⊔ S :=
        (Subgroup.map_subtype_le _).trans le_sup_right
      exact le_sup_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hZle).mp hZ)
  ·
    refine ⟨CFSG.Open.thompsonSubgroup S, ?_, CFSG.ambientMaxCardThompson_le S, ?_, ?_⟩
    · exact CFSG.LocalAnalysis.RankThreeTheoremC.thompsonSubgroup_ne_bot hSne
    · haveI : ((CFSG.Open.thompsonSubgroup S).subgroupOf S).Characteristic :=
        CFSG.LocalAnalysis.RankThreeTheoremC.thompsonSubgroup_characteristic S
      have hchar := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        ((CFSG.Open.thompsonSubgroup S).subgroupOf S)
      simpa [Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (CFSG.ambientMaxCardThompson_le S)] using hchar
    · have hJle : CFSG.Open.thompsonSubgroup S ≤ A ⊔ S :=
        (CFSG.ambientMaxCardThompson_le S).trans le_sup_right
      exact le_sup_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mp hJ)
  ·
    have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
    have hV0data := inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne
    have hV0p : IsPGroup 2 V₀ := hV0data.1.2.2.2.isPGroup
    have hV0H : V₀ ≤ H := h.hH ▸ h.ctx22.hV₀
    have hV0M : V₀ ≤ D.M := hV0data.1.2.1
    have hMV0 : D.M ≤ normalizer (V₀ : Set G) := hV0data.1.2.2.1
    have hV0HM : V₀ ≤ H ⊓ D.M := le_inf hV0H hV0M
    have hV0card4 : 4 ≤ Nat.card V₀ := by
      rw [card_eq_two_pow_mSub hV0p]
      have h2 : 2 ≤ mSub V₀ := Nat.succ_le_of_lt h.ctx22.ctx.hyp.big
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) h2
    let C : Subgroup G := S ⊓ centralizer (A : Set G)
    have hCS : C ≤ S := inf_le_left
    have hCidx : C.relIndex S = 2 := hC
    have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
    have key : ∀ g : G, CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ ≤ S →
        CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ = V₀ := by
      intro g hg
      let Vg : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g V₀
      let X : Subgroup G := Vg ⊓ C
      have hVgcard : Nat.card Vg = Nat.card V₀ :=
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective
      have hXidx : X.relIndex Vg ≤ 2 := by
        have h1 : X.relIndex Vg ≤ Vg.relIndex Vg * C.relIndex Vg := Subgroup.relIndex_inf_le
        rw [Subgroup.relIndex_self, one_mul] at h1
        refine h1.trans ?_
        exact (Subgroup.relIndex_le_of_le_right (H := C) (K := Vg) (L := S) hg (by
          rw [Subgroup.relIndex]
          exact Subgroup.index_ne_zero_of_finite)).trans (le_of_eq hCidx)
      have hXcard : 1 < Nat.card X := by
        set k := X.relIndex Vg with hk
        have hkpos : 0 < k := by
          rw [hk, Subgroup.relIndex]
          exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
        have hk2 : k ≤ 2 := hXidx
        have hmul' := Subgroup.relIndex_mul_card X Vg
        rw [inf_eq_left.mpr (show X ≤ Vg from inf_le_left)] at hmul'
        have hmul : k * Nat.card X = Nat.card Vg := by simpa [hk] using hmul'
        rw [hVgcard] at hmul
        have : 2 ≤ Nat.card X := by
          interval_cases k <;> omega
        omega
      haveI : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.mp hXcard
      obtain ⟨a, ha1⟩ := exists_ne (1 : ↥X)
      have haX : (a : G) ∈ X := a.2
      have ha1' : (a : G) ≠ 1 := fun h' => ha1 (Subtype.ext h')
      have hXA : A ≤ centralizer (X : Set G) := by
        intro a' ha'
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp hx.2.2 a' ha').symm
      have hTIg : CFSG.CGT.Timmesfeld75.IsTI Vg := by
        simpa [Vg] using CFSG.RankThree.GF2n.isTI_conjSubgroup hTI g
      have hXa : centralizer (X : Set G) ≤
          centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
        Subgroup.centralizer_le (Subgroup.zpowers_le.mpr haX)
      have hCXN : centralizer (X : Set G) ≤ normalizer (Vg : Set G) := by
        refine hXa.trans ?_
        intro y hy
        exact CFSG.CGT.PushingUpLit.SolKAb.centralizer_le_normalizer_of_isTI hTIg haX.1 ha1'
          (Subgroup.mem_centralizer_iff.mp hy (a : G) (Subgroup.mem_zpowers (a : G))).symm
      have hAg : A ≤ D.M.map (MulAut.conj g).toMonoidHom := by
        have hMgmax : CFSG.Open.rankThreeIsMaxTwoLocal
            (D.M.map (MulAut.conj g).toMonoidHom) :=
          CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map D.maxLocal
            (MulAut.conj g)
        have hVgne : Vg ≠ ⊥ := by
          intro hbot
          have hcard1 : Nat.card Vg = 1 := by rw [hbot, Subgroup.card_bot]
          rw [hVgcard] at hcard1
          omega
        have hVgp : IsPGroup 2 Vg := hV0p.map _
        have hMgle : D.M.map (MulAut.conj g).toMonoidHom ≤ normalizer (Vg : Set G) := by
          have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hMV0
          rwa [Subgroup.map_equiv_normalizer_eq] at h
        have hNVg : normalizer (Vg : Set G) = D.M.map (MulAut.conj g).toMonoidHom :=
          CFSG.LocalAnalysis.RankThreeUC.normalizer_eq_of_isMaxTwoLocal hMgmax hVgne hVgp hMgle
        rw [← hNVg]
        exact hXA.trans hCXN
      obtain ⟨E, hEA, hEel, hEcard⟩ :=
        exists_isElemAbelian_card_prime_sq_of_isZModSq h.ctx22.ctx.hAcard h.ctx22.ctx.hr.1
          h.ctx22.ctx.hr.2
      have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
        h12 E hEA hEel hEcard
      have hAU : A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
        CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hEU hEA hAM
      have hMge : D.M.map (MulAut.conj g).toMonoidHom = D.M := hAU.2 g hAg
      have hgM : g ∈ D.M := by
        have hgN : g ∈ normalizer (D.M : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMge
        rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
          at hgN
      have hgV : g ∈ normalizer (V₀ : Set G) := hMV0 hgM
      have hmap : V₀.map (MulAut.conj g).toMonoidHom = V₀ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgV
      simpa [Vg, CFSG.CGT.Timmesfeld75.conjSubgroup] using hmap
    obtain ⟨g, -, hgS⟩ :=
      CFSG.CGT.PushingUpLit.A78Sp4.exists_conj_le_of_isSylowOf hS hV0HM hV0p
    have hV0leS : V₀ ≤ S := by
      have h := key g hgS
      rw [← h]
      exact hgS
    refine ⟨V₀, hV0ne, hV0leS, ?_, hAM.trans hMV0⟩
    intro s hs
    have hSs : S.map (MulAut.conj s).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
    have hVgs : CFSG.CGT.Timmesfeld75.conjSubgroup s V₀ ≤ S := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup]
      calc V₀.map (MulAut.conj s).toMonoidHom ≤ S.map (MulAut.conj s).toMonoidHom :=
            Subgroup.map_mono hV0leS
        _ = S := hSs
    have h := key s hVgs
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (by simpa [CFSG.CGT.Timmesfeld75.conjSubgroup] using h)

theorem isSylow_of_normalU (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h14 : R19_14At D V₀ V p L A t B r h.ctx22.ctx)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (htS : t ∈ normalizer (S : Set G))
    {U : Subgroup G} (hUne : U ≠ ⊥) (hUle : U ≤ S)
    (hNSU : normalizer (S : Set G) ≤ normalizer (U : Set G))
    (hAU : A ≤ normalizer (U : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 S H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change muSet D B = ∅ at h14
  by_contra hnot
  obtain ⟨T, hST, hT⟩ : ∃ T : Subgroup G, S ≤ T ∧ CFSG.ABGLocalTools.IsSylowOf 2 T H :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge
      (p := 2) (R := S) (H := H) hS.isPGroup (hS.le.trans inf_le_left)
  have hSneT : S ≠ T := fun hEq => hnot (hEq ▸ hT)
  have hTM2 : IsPGroup 2 (T ⊓ D.M : Subgroup G) := by
    exact hT.isPGroup.to_inf_left (K := D.M)
  have hTM : T ⊓ D.M = S :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le hS (le_inf hST (hS.le.trans inf_le_right))
      (le_inf (inf_le_left.trans hT.le) inf_le_right) hTM2
  obtain ⟨x, hxT, hxS, hxNormS⟩ :=
    CFSG.RankThree.PartOne.Sec12Fus.exists_mem_normalizer_sdiff (p := 2) (P := S) (S := T)
      hST hT.isPGroup hSneT
  have hxnotM : x ∉ D.M := by
    intro hxM
    have hxTM : x ∈ T ⊓ D.M := ⟨hxT, hxM⟩
    rw [hTM] at hxTM
    exact hxS hxTM
  have hNGUnotM : ¬ normalizer (U : Set G) ≤ D.M := by
    intro hle
    exact hxnotM (hle (hNSU hxNormS))
  have hU2 : IsPGroup 2 U :=
    IsPGroup.of_equiv (hS.isPGroup.to_subgroup (U.subgroupOf S))
      (Subgroup.subgroupOfEquivOfLe hUle)
  have hUlocal : CFSG.Open.IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U, hUne, hU2, rfl⟩
  obtain ⟨N, hNmax, hNGUleN⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le hUlocal
  have hNne : N ≠ D.M := by
    intro hNM
    exact hNGUnotM (hNGUleN.trans (le_of_eq hNM))
  have hB_le : B ≤ normalizer (U : Set G) := by
    rw [h.ctx22.ctx.hB]
    refine sup_le hAU ?_
    exact Subgroup.zpowers_le.mpr (hNSU htS)
  have hYnormU : B ⊔ U ≤ normalizer (U : Set G) := sup_le hB_le Subgroup.le_normalizer
  have hYleN : B ⊔ U ≤ N :=
    sup_le (hB_le.trans hNGUleN) (Subgroup.le_normalizer.trans hNGUleN)
  have hUleO2 : U ≤ pCoreOf 2 (B ⊔ U) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) le_sup_right hYnormU hU2
  have hO2ne : pCoreOf 2 (B ⊔ U) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hUleO2
    exact hUne (le_bot_iff.mp hUleO2)
  have hYleM : B ⊔ U ≤ D.M := by
    have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
    have htM : t ∈ D.M :=
      IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le h.ctx22.ctx.htA
    have hBM : B ≤ D.M := by
      rw [h.ctx22.ctx.hB]
      exact sup_le hAM (Subgroup.zpowers_le.mpr htM)
    exact sup_le hBM (hUle.trans (hS.le.trans inf_le_right))
  have hYeq : B ⊔ U = B ⊔ pCoreOf 2 (B ⊔ U) := by
    apply le_antisymm
    · exact sup_le le_sup_left (hUleO2.trans le_sup_right)
    · exact sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hcalne : calMOf (B ⊔ U) ≠ {D.M} := by
    intro hcal
    have hNmem : N ∈ calMOf (B ⊔ U) := ⟨hNmax, hYleN⟩
    rw [hcal] at hNmem
    exact hNne (Set.mem_singleton_iff.mp hNmem)
  exact (Set.eq_empty_iff_forall_notMem.mp h14) (B ⊔ U)
    ⟨hYleM, hYeq, hO2ne, hcalne⟩

theorem relIndex_le_two_of_gap19_28 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h)
    (hgap : Gap19_28 D V₀ V p L A t B r A₀ H h h25 h26)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) :
    (pCoreOf 2 (A ⊔ S)).relIndex S ≤ 2 := by
  have hcomm : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard
  have hOS : pCoreOf 2 (H ⊓ IOf D p L) ≤ S := pCoreOf_inter_IOf_le_sylow D h hS
  have hAO : A ≤ normalizer (pCoreOf 2 (H ⊓ IOf D p L) : Set G) :=
    A_le_normalizer_pCoreOf_inter_IOf D h
  have hSO : S ≤ normalizer (pCoreOf 2 (H ⊓ IOf D p L) : Set G) :=
    (sylow_le_normalizer_inter_IOf D h hS).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (H ⊓ IOf D p L))
  have hSE : S ≤ normalizer ((A ⊔ pCoreOf 2 (H ⊓ IOf D p L) : Subgroup G) : Set G) :=
    le_normalizer_sup_pCoreOf_inter_IOf D h h25 hS
  have hS0le : S ⊓ (⨅ a ∈ A, centModEl (pCoreOf 2 (H ⊓ IOf D p L)) a) ≤
      pCoreOf 2 (A ⊔ S) :=
    kernel_le_pCoreOf_sup hcomm hOS hAO hSO hSE hS.isPGroup
  exact (Subgroup.relIndex_le_of_le_left hS0le (by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite)).trans (hgap S hS)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
