module

public import CFSG.RankThree.PartTwo.Sec18.Item183One
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Claim184Lc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M,
      Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) →
      ∃ c ∈ A, c ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 c,
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
        ∀ a ∈ A, InducesInnerMod a K (CFSG.Open.pCoreOf 2 K)

@[expose] def Claim184LcLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M,
      Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) →
      ∃ c ∈ A, c ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 c,
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
        (∀ a ∈ A, InducesInnerMod a K (CFSG.Open.pCoreOf 2 K)) ∧
        inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G)) ≤ K ∧
        inSubgroup perfectResidual H ≤
          inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
            CFSG.Open.pCoreOf 2 H

section Residual

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem map_perfectResidual_eq {f : X →* Y} (hf : Function.Surjective f) :
    (perfectResidual X).map f = perfectResidual Y := by
  refine le_antisymm (map_perfectResidual_le f) ?_
  have hXc := CFSG.perfect_residual_characterization (G := X)
  have : (perfectResidual X).Characteristic := hXc.2.1
  have hn : ((perfectResidual X).map f).Normal :=
    (inferInstance : (perfectResidual X).Normal).map f hf
  have hs : Group.IsSolvable (Y ⧸ (perfectResidual X).map f) := by
    have := hXc.2.2.2.1
    refine Group.isSolvable_of_surjective
      (f := QuotientGroup.map _ _ f (Subgroup.le_comap_map f (perfectResidual X))) ?_
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, rfl⟩
  exact ((CFSG.perfect_residual_characterization (G := Y)).2.2.2.2.1 _).mp hs

theorem perfectResidual_eq_commutator {X : Subgroup Y} [X.Normal]
    (hs : Group.IsSolvable (Y ⧸ X)) (hp : ⁅⁅X, X⁆, ⁅X, X⁆⁆ = ⁅X, X⁆) :
    perfectResidual Y = ⁅X, X⁆ := by
  have hYc := CFSG.perfect_residual_characterization (G := Y)
  apply le_antisymm
  · have h1 : perfectResidual Y ≤ X := (hYc.2.2.2.2.1 X).mp hs
    have hP : ⁅perfectResidual Y, perfectResidual Y⁆ = perfectResidual Y :=
      (Subgroup.isPerfect_iff).mp hYc.2.2.1
    rw [← hP]
    exact Subgroup.commutator_mono h1 h1
  · have key : ∀ n : ℕ, ⁅X, X⁆ ≤ derivedSeries Y n := by
      intro n
      induction n with
      | zero => exact le_top
      | succ n ih =>
        rw [derivedSeries_succ, ← hp]
        exact Subgroup.commutator_mono ih ih
    rw [perfectResidual]
    exact le_iInf key

end Residual

variable {G : Type} [Group G] [Finite G]

theorem mem_of_isPGroup_quotient {Y : Type*} [Group Y] {X : Subgroup Y} [X.Normal]
    (hq : IsPGroup 2 (Y ⧸ X)) {y : Y} {k : ℕ} (hy : y ^ 3 ^ k = 1) : y ∈ X := by
  obtain ⟨j, hj⟩ := hq (y : Y ⧸ X)
  have h2 : orderOf (y : Y ⧸ X) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
  have h3 : orderOf (y : Y ⧸ X) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hy]
    rfl
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) := Nat.Coprime.pow j k (by norm_num)
  have h1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem rank3II_18_4_1_of_not_SL
    (h1812 : Item181_2)
    (hno : ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
      ∀ H ∈ scriptH A M,
        Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) → False) :
    Item184_1 := by
  intro G _ _ A M h H hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨s, ⟨hsS, -, -, hsH, X, hXn, hX, hXt, -⟩, -, -⟩ := h1812 G A M h H hH
  set Q := CFSG.pCore 2 H with hQ
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set L := inSubgroup perfectResidual H with hLdef
  set Lb : Subgroup (H ⧸ Q) := (perfectResidual H).map π with hLb
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hQ, hRdef, CFSG.Open.pCoreOf]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have ht2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsH⟩)) := by
    have hT2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf H) := hS2.comap_subtype
    refine (hT2.map π).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hq2 : IsPGroup 2 ((H ⧸ Q) ⧸ X) := by
    have h1 := ht2.map (QuotientGroup.mk' X)
    have h2 : (Subgroup.zpowers (π ⟨s, hsH⟩)).map (QuotientGroup.mk' X) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' X)
        (QuotientGroup.mk'_surjective X), ← hXt, Subgroup.map_sup,
        (QuotientGroup.map_mk'_self X), bot_sup_eq]
    rw [h2] at h1
    exact h1.of_equiv Subgroup.topEquiv
  have hqs : Group.IsSolvable ((H ⧸ Q) ⧸ X) := by
    have := hq2.isNilpotent
    infer_instance
  have hLbeq : ⁅⁅X, X⁆, ⁅X, X⁆⁆ = ⁅X, X⁆ → Lb = ⁅X, X⁆ := fun hp => by
    rw [hLb, map_perfectResidual_eq (QuotientGroup.mk'_surjective Q)]
    exact perfectResidual_eq_commutator hqs hp
  set φ : L →* H ⧸ Q := π.comp (Subgroup.inclusion hLH) with hφ
  have hrange : φ.range = Lb := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Subgroup.inclusion hLH x, ?_, rfl⟩
      obtain ⟨z, hz, hzx⟩ := x.2
      have : Subgroup.inclusion hLH x = z := Subtype.ext hzx.symm
      rw [this]
      exact hz
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), ⟨x, hx, rfl⟩⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 L := by
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, ?_⟩
      have himg : φ.ker.map L.subtype ≤ R := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hmemR _).mp hx
      exact (hR2.to_le himg).of_equiv (φ.ker.equivMapOfInjective _ L.subtype_injective).symm
    · intro x hx
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hmemR]
      have hO : CFSG.Open.pCoreOf 2 L ≤ R :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
          ((le_normalizer_inSubgroup_perfectResidual H).trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      exact hO ((mem_pCore_iff_mem_pCoreOf x).mp hx)
  have hLiso : L ⧸ CFSG.pCore 2 L ≃* Lb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  rcases hX with he | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩
  ·
    obtain ⟨e⟩ := he
    have hk : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
    set e' := e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with he'
    have hcomm := KFacts.KS18.commutator_eq_range e'
    have hperf : Group.IsPerfect (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 2)) := KFacts.KS18.isPerfect_projectiveSL _
    have hrp : ⁅(KFacts.KS18.inrY e').range, (KFacts.KS18.inrY e').range⁆ =
        (KFacts.KS18.inrY e').range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
        Group.IsPerfect.commutator_eq_top]
    have hLbr : Lb = (KFacts.KS18.inrY e').range := by
      rw [hLbeq (by rw [hcomm, hrp]), hcomm]
    set ι := MonoidHom.ofInjective (KFacts.KS18.inrY_injective e') with hι
    refine ⟨⟨hLiso.trans ((MulEquiv.subgroupCongr hLbr).trans
      (ι.symm.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm))⟩, ?_⟩
    set f : A.subgroupOf H →* H ⧸ Q := π.comp (A.subgroupOf H).subtype with hf
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, hmemR] at ha
      have hbot := inf_eq_bot_of_elemAbelian_three hA.1 hR2
      have : ((a : H) : G) ∈ A ⊓ R := ⟨Subgroup.mem_subgroupOf.mp a.2, ha⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext this))
    set Ab := f.range with hAb
    have hAb27 : Nat.card Ab = 27 := by
      rw [hAb, Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, ← hA.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
    have hAexp : ∀ a : A.subgroupOf H, a ^ 3 = 1 := fun a =>
      Subtype.ext (by simpa using (isE27_subgroupOf hA hAH).1.2 (a : H) a.2)
    have hAb3 : IsPGroup 3 Ab := by
      rintro ⟨_, a, rfl⟩
      exact ⟨1, Subtype.ext (by rw [pow_one]; simp [← map_pow, hAexp a])⟩
    have hAbX : Ab ≤ X := by
      rintro _ ⟨a, rfl⟩
      exact mem_of_isPGroup_quotient hq2 (k := 1) (by rw [pow_one, ← map_pow, hAexp a, map_one])
    have hLbn : Lb.Normal := by
      have hc := CFSG.perfect_residual_characterization (G := H)
      have : (perfectResidual H).Characteristic := hc.2.1
      exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective Q)
    have hXLC : ∀ x ∈ X, ∃ l ∈ Lb, ∃ z ∈ Subgroup.centralizer (Lb : Set (H ⧸ Q)), x = l * z := by
      intro x hx
      refine ⟨KFacts.KS18.inrY e' (e' ⟨x, hx⟩).2, hLbr ▸ ⟨_, rfl⟩,
        KFacts.KS18.inlY e' (e' ⟨x, hx⟩).1, ?_, KFacts.KS18.eq_inrY_mul_inlY e' ⟨x, hx⟩⟩
      rw [hLbr]
      exact KFacts.KS18.inlY_mem_centralizer e' _
    set ιL : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) ≃*
        Lb := ι.trans (MulEquiv.subgroupCongr hLbr.symm) with hιL
    have hLbZ : Subgroup.center Lb = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : ιL.symm z ∈ Subgroup.center
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2)) := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro y
        obtain ⟨w, rfl⟩ := ιL.symm.surjective y
        rw [← map_mul, ← map_mul, hz w]
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter.center_projectiveSL_three_eq_bot
        hk, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact ιL.symm.injective (h1.trans ιL.symm.map_one.symm)
    set ψ : Lb ⧸ Subgroup.center Lb ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
      ((QuotientGroup.quotientMulEquivOfEq hLbZ).trans QuotientGroup.quotientBot).trans
        ιL.symm with hψ
    have hLbp : commutator Lb = ⊤ := by
      have : Group.IsPerfect Lb := Group.IsPerfect.ofSurjective (f := ιL.toMonoidHom)
        ιL.surjective
      exact Group.IsPerfect.commutator_eq_top
    have hge := KFacts.KS18.three_le_card_inf_centralizer ψ hk hLbp hXLC hAbX hAb3 hAb27
    have hle : Nat.card (Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Q)) : Subgroup (H ⧸ Q)) ≤ 3 :=
      by
      have hsub : Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Q)) ≤ (KFacts.KS18.inlY e').range :=
        fun x hx => KFacts.KS18.mem_range_inlY_of_mem_centralizer e' hk (hAbX hx.1)
          (hLbr ▸ hx.2)
      calc _ ≤ Nat.card (KFacts.KS18.inlY e').range := Subgroup.card_le_of_le hsub
        _ = 3 := KFacts.KS18.card_range_inlY e'
    have hC3 : Nat.card (Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Q)) : Subgroup (H ⧸ Q)) = 3 :=
      le_antisymm hle hge
    set SA := (Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Q))).comap f with hSA
    set SG : Subgroup G := (SA.map (A.subgroupOf H).subtype).map H.subtype with hSG
    have hSAcard : Nat.card SA = 3 := by
      have h1 : SA.map f = Ab ⊓ Subgroup.centralizer (Lb : Set (H ⧸ Q)) :=
        Subgroup.map_comap_eq_self inf_le_left
      rw [← hC3, ← h1, Subgroup.card_map_of_injective hfinj]
    have hSGcard : Nat.card SG = 3 := by
      rw [hSG, Subgroup.card_map_of_injective H.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hSAcard]
    have hkey : ∀ (a : G) (haA : a ∈ A), (∀ x ∈ L, a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L) ↔
        f ⟨⟨a, hAH haA⟩, Subgroup.mem_subgroupOf.mpr haA⟩ ∈
          Subgroup.centralizer (Lb : Set (H ⧸ Q)) := by
      intro a haA
      have hRL : R ⊓ L ≤ CFSG.Open.pCoreOf 2 L :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
          (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
            ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hx), Subgroup.le_normalizer hx⟩)
          (hR2.to_le inf_le_left)
      have hO : CFSG.Open.pCoreOf 2 L ≤ R :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
          ((le_normalizer_inSubgroup_perfectResidual H).trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      constructor
      · intro hc
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨x, hx, rfl⟩
        have hxL : (x : G) ∈ L := ⟨x, hx, rfl⟩
        have h1 := (hmemR (⟨a, hAH haA⟩ * x * ⟨a, hAH haA⟩⁻¹ * x⁻¹)).mpr (hO (hc _ hxL))
        simp only [map_mul, map_inv] at h1
        simp only [hf, MonoidHom.comp_apply, Subgroup.coe_subtype]
        calc π x * π ⟨a, hAH haA⟩ =
            π ⟨a, hAH haA⟩ * π x * (π ⟨a, hAH haA⟩)⁻¹ * (π x)⁻¹ * (π x * π ⟨a, hAH haA⟩) := by
              rw [h1, one_mul]
          _ = π ⟨a, hAH haA⟩ * π x := by group
      · intro hc x hxL
        obtain ⟨x', hx', rfl⟩ := hxL
        have h1 := Subgroup.mem_centralizer_iff.mp hc (π x') ⟨x', hx', rfl⟩
        simp only [hf, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
        have h2 : π (⟨a, hAH haA⟩ * x' * ⟨a, hAH haA⟩⁻¹ * x'⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [← h1]
          group
        have h3 := (hmemR _).mp h2
        refine hRL ⟨h3, ?_⟩
        have hxLG : (x' : G) ∈ L := ⟨x', hx', rfl⟩
        have haN : a ∈ Subgroup.normalizer (L : Set G) :=
          le_normalizer_inSubgroup_perfectResidual H (hAH haA)
        show a * (x' : G) * a⁻¹ * (x' : G)⁻¹ ∈ L
        exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp hxLG) (L.inv_mem hxLG)
    have hset : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (SG : Set G) := by
      ext a
      constructor
      · rintro ⟨haA, hc⟩
        show a ∈ SG
        set b : A.subgroupOf H := ⟨⟨a, hAH haA⟩, Subgroup.mem_subgroupOf.mpr haA⟩ with hb
        have hbSA : b ∈ SA := ⟨⟨b, rfl⟩, (hkey a haA).mp hc⟩
        exact Subgroup.mem_map.mpr ⟨⟨a, hAH haA⟩, Subgroup.mem_map.mpr ⟨b, hbSA, rfl⟩, rfl⟩
      · intro ha
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
        have hbA : (((b : A.subgroupOf H) : H) : G) ∈ A := Subgroup.mem_subgroupOf.mp b.2
        exact ⟨hbA, (hkey _ hbA).mpr hb.2⟩
    have hSG1 : SG ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hSGcard
      omega
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hSG1
    have hc3 : orderOf (c : G) = 3 := by
      have hd : orderOf (c : G) ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard SG c.2
        rwa [hSGcard] at this
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1 | h1
      · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h1)) hc1
      · exact h1
    refine ⟨c, hc3, ?_⟩
    rw [hset]
    have hzc : Subgroup.zpowers (c : G) = SG :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr c.2)
        (by rw [hSGcard, Nat.card_zpowers, hc3])
    rw [hzc]
  ·
    exfalso
    have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3
    have hXX : ⁅X, X⁆ = V.map X.subtype := by
      rw [← Subgroup.map_subtype_commutator, hcomm]
    have hVp : Group.IsPerfect V := by
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
        CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
      exact Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVmp : ⁅V.map X.subtype, V.map X.subtype⁆ = V.map X.subtype := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator,
        Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hLbV : Lb = V.map X.subtype := by
      rw [hLbeq (by rw [hXX, hVmp]), hXX]
    have hSL : Nonempty (L ⧸ CFSG.pCore 2 L ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      ⟨hLiso.trans ((MulEquiv.subgroupCongr hLbV).trans
        ((V.equivMapOfInjective _ X.subtype_injective).symm.trans eV))⟩
    exact hno G A M h H hH hSL

theorem rank3II_18_4_1_of_item183One
    (h1812 : Item181_2)
    (h183 : Item183One) (hLc : Claim184LcLe) : Item184_1 := by
  refine rank3II_18_4_1_of_not_SL h1812 fun G _ _ A M h H hH hSL => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcA, hc1, K, hK, hKiso, hinner, hLcK, hLLc⟩ := hLc G A M h H hH hSL
  have hKM : K ≤ M := le_of_item183One h183 h hcA hc1 hK hKiso hinner
  have hAH := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hRM : CFSG.Open.pCoreOf 2 H ≤ M :=
    le_of_le_normalizer_of_isPGroup_two h (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (hAH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  exact perfectResidual_not_le_of_mem_scriptH h hH
    (hLLc.trans (sup_le (hLcK.trans hKM) hRM))

end CFSG.RankThree.PartTwo.Sec18
