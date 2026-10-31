module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4ParAux1
public import CFSG.Quasithin.MS93.MSPLeviQ
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Par
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E6TorusFacts
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.U4ParSp
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Arith
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord2
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4MRad
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.M11
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Quasithin.MS93.MSP
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open CFSG.Quasithin.H13.KGL34P
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin.H13.Ch4.Sp4M
open CFSG.QuasithinUnique.Lin2.Five (tauEquiv)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)

variable {G : Type} [Group G]
variable {F : Type} [Field F]

private def wcgapsq_oTwoSet (K : Subgroup G) : Set (Subgroup G) :=
  {W | (⊥ : Subgroup G) ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧
    ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ (⊥ : Subgroup G)}

theorem wcgapsq_le_oTwoMod_of_isPGroup {K W : Subgroup G} (hWK : W ≤ K)
    (hWn : (W.subgroupOf K).Normal) (hW2 : IsPGroup 2 W) :
    W ≤ oTwoMod (⊥ : Subgroup G) K := by
  refine le_iSup₂ (f := fun (W : Subgroup G) (_ : W ∈ wcgapsq_oTwoSet K) => W) W
    ⟨bot_le, hWK, hWn, ?_⟩
  intro w hw
  obtain ⟨k, hk⟩ := hW2 ⟨w, hw⟩
  exact ⟨k, Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hk)⟩

section Lev

variable [Finite F] [CharP F 2]

private def wcgapsq_fixE1 : Subgroup (StatedSp 2 F) where
  carrier := {x | mat x *ᵥ e₁ F = e₁ F}
  one_mem' := by
    change mat (1 : StatedSp 2 F) *ᵥ e₁ F = e₁ F
    rw [mat_one, one_mulVec]
  mul_mem' := by
    intro x y hx hy
    change mat (x * y) *ᵥ e₁ F = e₁ F
    rw [mat_mul_mulVec, hy, hx]
  inv_mem' := by
    intro x hx
    change mat x⁻¹ *ᵥ e₁ F = e₁ F
    have h := mat_inv_mulVec x (e₁ F)
    rwa [hx] at h

private theorem wcgapsq_L2_fixes_e1 {g : StatedSp 2 F} (hg : g ∈ L₂ F) :
    mat g *ᵥ e₁ F = e₁ F := by
  have hsub : L₂ F ≤ wcgapsq_fixE1 := by
    rw [L₂]
    refine sup_le ?_ ?_
    · intro x hx
      exact (mem_Q₂_iff_levQ.1 hx).2.1
    · intro x hx
      exact (mem_lev₂_iff.1 hx).1
  exact hsub hg

@[expose] noncomputable def wcgapsq_leviL0 : ↥(L₂ F) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  (levQ (F := F)).comp (Subgroup.inclusion L₂_le_P₂)

theorem wcgapsq_leviL0_apply (g : ↥(L₂ F)) :
    wcgapsq_leviL0 g = levQ ⟨(g : StatedSp 2 F), L₂_le_P₂ g.2⟩ := rfl

theorem wcgapsq_leviL0_surjective : Function.Surjective (wcgapsq_leviL0 (F := F)) := by
  intro M
  refine ⟨⟨levHom₂ M, ?_⟩, ?_⟩
  · exact Subgroup.mem_sup_right (by rw [← range_levHom₂]; exact ⟨M, rfl⟩)
  · rw [wcgapsq_leviL0_apply]
    exact levQ_levHom₂ M

theorem wcgapsq_leviL0_ker :
    (wcgapsq_leviL0 (F := F)).ker = (Q₂ F).subgroupOf (L₂ F) := by
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    exact mem_Q₂_iff_levQ.2 ⟨L₂_le_P₂ g.2, wcgapsq_L2_fixes_e1 g.2, hg⟩
  · intro hg
    rw [MonoidHom.mem_ker, wcgapsq_leviL0_apply]
    exact levQ_of_mem_Q₂ (Subgroup.mem_subgroupOf.mp hg)

theorem wcgapsq_isComplement' {G : Type} [Group G] [Finite G] {H K : Subgroup G} [K.Normal]
    (hinf : H ⊓ K = ⊥) (hsup : H ⊔ K = ⊤) : H.IsComplement' K := by
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le, hinf]
  · rw [Set.eq_univ_iff_forall]
    intro g
    have hg : g ∈ H ⊔ K := by rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨h, hh, k, hk, hk_eq⟩ := (Subgroup.mem_sup_of_normal_right (s := H) (t := K)).mp hg
    exact Set.mem_mul.mpr ⟨h, hh, k, hk, hk_eq⟩

theorem wcgapsq_lev1_inf :
    (lev₁ F).subgroupOf (L₁ F) ⊓ (Q₁ F).subgroupOf (L₁ F) = ⊥ := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
  constructor
  · rintro ⟨hxL, hxQ⟩
    exact Subtype.ext (by
      have hx : (x : StatedSp 2 F) ∈ Q₁ F ⊓ lev₁ F := ⟨hxQ, hxL⟩
      rwa [Q₁_inf_lev₁, Subgroup.mem_bot] at hx)
  · intro hx
    rw [hx]
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

theorem wcgapsq_lev1_sup :
    (lev₁ F).subgroupOf (L₁ F) ⊔ (Q₁ F).subgroupOf (L₁ F) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup lev₁_le_L₁ Q₁_le_L₁, sup_comm]
  exact Subgroup.subgroupOf_self (H := L₁ F)

instance wcgapsq_Q1subgroupOfNormal : ((Q₁ F).subgroupOf (L₁ F)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer Q₁_le_L₁).mpr L₁_le_normalizer_Q₁

@[expose] noncomputable def wcgapsq_lev1Equiv :
    ↥(L₁ F) ⧸ ((Q₁ F).subgroupOf (L₁ F)) ≃* ↥((lev₁ F).subgroupOf (L₁ F)) :=
  IsComplement'.QuotientMulEquiv (wcgapsq_isComplement'
    (H := (lev₁ F).subgroupOf (L₁ F)) (K := (Q₁ F).subgroupOf (L₁ F))
    wcgapsq_lev1_inf wcgapsq_lev1_sup)

@[expose] noncomputable def wcgapsq_leviL1 : ↥(L₁ F) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  ((MonoidHom.ofInjective (levHom₁_injective (F := F))).symm.toMonoidHom).comp
    (((Subgroup.subgroupOfEquivOfLe (lev₁_le_L₁ (F := F))).toMonoidHom).comp
      (wcgapsq_lev1Equiv.toMonoidHom.comp
        (QuotientGroup.mk' ((Q₁ F).subgroupOf (L₁ F)))))

theorem wcgapsq_leviL1_ker :
    (wcgapsq_leviL1 (F := F)).ker = (Q₁ F).subgroupOf (L₁ F) := by
  rw [wcgapsq_leviL1]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

theorem wcgapsq_leviL1_surjective : Function.Surjective (wcgapsq_leviL1 (F := F)) := by
  rw [wcgapsq_leviL1]
  exact (MulEquiv.surjective
      (MonoidHom.ofInjective (levHom₁_injective (F := F))).symm).comp
    ((MulEquiv.surjective (Subgroup.subgroupOfEquivOfLe (lev₁_le_L₁ (F := F)))).comp
      ((MulEquiv.surjective wcgapsq_lev1Equiv).comp
        (QuotientGroup.mk'_surjective _)))

theorem wcgapsq_oTwoMod_eq_of_surj {M : Type} [Group M] [Finite M]
    {U K Q : Subgroup M} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (hU2 : IsPGroup 2 U) (hUK : U ≤ K) (hQU : Q ≤ U) (hQn : (Q.subgroupOf K).Normal)
    (φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    (hker : φ.ker = Q.subgroupOf K) :
    oTwoMod (⊥ : Subgroup M) K = Q ∧
    HasQuotShape K (oTwoMod (⊥ : Subgroup M) K : Set M) (fun X _ => IsL2 X 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_two_of_card_eq_four hF
  have hQ2 : IsPGroup 2 Q := hU2.to_le hQU
  have hle : oTwoMod (⊥ : Subgroup M) K ≤ Q := by
    rw [oTwoMod]
    refine iSup₂_le fun W hW => ?_
    have hW2' : IsPGroup 2 W := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro x
      obtain ⟨k, hk⟩ := hW.2.2.2 (x : M) x.2
      exact ⟨k, orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext (Subgroup.mem_bot.mp hk))⟩
    have hW2 : IsPGroup 2 (W.subgroupOf K) :=
      hW2'.of_equiv (Subgroup.subgroupOfEquivOfLe hW.2.1).symm
    have hS2 : IsPGroup 2 ((W.subgroupOf K).map φ) := hW2.map φ
    have hSn : ((W.subgroupOf K).map φ).Normal := hW.2.2.1.map φ hφ
    rcases (isSimpleGroup_sl_two hF).eq_bot_or_eq_top_of_normal
      ((W.subgroupOf K).map φ) with h | h
    · intro w hw
      have hleker : W.subgroupOf K ≤ φ.ker := by rw [← Subgroup.map_eq_bot_iff]; exact h
      have hmem : (⟨w, hW.2.1 hw⟩ : ↥K) ∈ φ.ker := hleker hw
      rw [hker] at hmem
      exact hmem
    · exfalso
      obtain ⟨n, hn⟩ := hS2.exists_card_dvd_pow
      rw [h, Subgroup.card_top, card_sl_two hF] at hn
      have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h32
  have hcore : oTwoMod (⊥ : Subgroup M) K = Q :=
    le_antisymm hle (wcgapsq_le_oTwoMod_of_isPGroup (hQU.trans hUK) hQn hQ2)
  refine ⟨hcore, ?_⟩
  have hL2 : IsL2 (Matrix.SpecialLinearGroup (Fin 2) F) 2 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL (n := 2) (F := F)
      (by norm_num) (by rw [hF]; norm_num)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
  refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, φ, hφ, ?_, hL2⟩
  intro k
  rw [hcore]
  change φ k = 1 ↔ k ∈ Q.subgroupOf K
  rw [← hker, MonoidHom.mem_ker]

end Lev

end CFSG.LocalAnalysis.WeakClosure81

end
