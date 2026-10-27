module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusTwE6Rank
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TorsionLabel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafComponent
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcAdj
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.Fischer.Classification.Recognition.Basic
public import Certificates.Certificate707001
public import Certificates.Certificate707002
public import Certificates.Data.E6TableT

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


private theorem q2cTE6_three_not_dvd {n : ℕ} (h3n : 3 ∣ 2 ^ n + 1) (h3m : 3 ∣ 2 ^ n - 1) :
    False := by
  have hd : 3 ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h3n h3m
  have heq : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [heq] at hd
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) hd

private theorem q2cTE6_labelIso_A5 {m : ℕ} {lab' : LargeEvenLabel}
    (hiso : GGLabelIso lab' (⟨.A, 5, m⟩ : LargeEvenLabel)) :
    lab' = ⟨.A, 5, m⟩ := by
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · exact False.elim (absurd h.2.1 (by simp))
  · exact False.elim (absurd (congrArg LargeEvenLabel.rank h.2) (by norm_num))
  · exact False.elim (absurd (congrArg LargeEvenLabel.tag h.2) (by simp))
  · exact False.elim (absurd (congrArg LargeEvenLabel.tag h.2) (by simp))
  · exact False.elim (absurd (congrArg LargeEvenLabel.tag h.2) (by simp))
  · exact False.elim (absurd (congrArg LargeEvenLabel.rank h.2) (by norm_num))
  · exact False.elim (absurd (congrArg LargeEvenLabel.tag h.1) (by simp))

private theorem q2cTE6_e6TwoCompLabelT_iso_A5_false {m : ℕ} {lab' : LargeEvenLabel}
    (hc : TablePThreeKG.E6TwoCompLabelT lab')
    (hiso : GGLabelIso lab' (⟨.A, 5, m⟩ : LargeEvenLabel)) : False := by
  unfold TablePThreeKG.E6TwoCompLabelT at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold GGLabelIso at hiso
     rcases hiso with h | h | h | h | h | h | h | h <;>
     simp_all [LargeEvenLabel.mk.injEq])

private abbrev q2cTE6G (n : ℕ) (Fld : Type) [Field Fld] : Type :=
  LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n)

private abbrev q2cTE6ID (n : ℕ) (Fld : Type) [Field Fld] : Set (MulAut (q2cTE6G n Fld)) :=
  LargeEvenChevIDImage (LargeEvenCartanE 6) Fld
    (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n)

theorem q2c_twE6_recipe_perfect {n : ℕ} {Fld : Type} [Field Fld] [Finite Fld]
    (hFldcard : Nat.card Fld = (2 ^ n) ^ 2) :
    Finite (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n)) ∧
    commutator (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n)) = ⊤ := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have h1 : Nat.card Fld = 1 := by rw [h] at hFldcard; simpa using hFldcard
      haveI : Nontrivial Fld := inferInstance
      have h2 : 1 < Nat.card Fld := Finite.one_lt_card
      omega
    · exact h
  haveI hchar : CharP Fld 2 := charP_two_of_card (m := n * 2) (by rw [hFldcard, pow_mul])
  have hK : Nat.card Fld = (2 ^ n) ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := by
    rw [show CFSG.Blueprint.Chevalley.TwistTag.E6.order = 2 from rfl, hFldcard]
  obtain ⟨-, -, hΓ, -, hcomm⟩ :=
    CFSG.LieType.Chevalley.finite_fixed_root_group_perfect
      CFSG.Blueprint.Chevalley.TwistTag.E6 Nat.prime_two hn Fld hK
      (iterateFrobenius Fld 2 n) (iterateFrobenius_def 2 n)
  obtain ⟨-, T₀, -, -⟩ :=
    InnerDiagTwE6.exists_twistedTransport (K := Fld) n (iterateFrobenius Fld 2 n)
      (iterateFrobenius_def 2 n)
  let e : ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.E6 Fld
        (iterateFrobenius Fld 2 n)) ≃*
      ↥(LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n) :=
    (MulEquiv.subgroupCongr hΓ.symm).trans T₀
  let eQ : (↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.E6 Fld
          (iterateFrobenius Fld 2 n)) ⧸
        Subgroup.center ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.E6 Fld (iterateFrobenius Fld 2 n))) ≃*
      LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  haveI : Group.IsPerfect (↥(CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.E6 Fld (iterateFrobenius Fld 2 n)) ⧸
      Subgroup.center ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.E6 Fld (iterateFrobenius Fld 2 n))) :=
    Group.isPerfect_def.mpr hcomm
  haveI : Finite (↥(CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.E6 Fld (iterateFrobenius Fld 2 n))) :=
    Subtype.finite
  exact ⟨Finite.of_injective (eQ.symm : _ → _) eQ.symm.injective,
    Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective eQ.surjective)⟩

private theorem q2cTE6_recipe {n m : ℕ} {Fld : Type} [Field Fld] [Finite Fld]
    (hFldcard : Nat.card Fld = (2 ^ n) ^ 2) (h3n : 3 ∣ 2 ^ n + 1)
    (hm : 2 ≤ m) (hpm : 3 ∣ 2 ^ m - 1)
    (u : MulAut (q2cTE6G n Fld)) (hu : u ∈ q2cTE6ID n Fld) (huo : orderOf u = 3)
    (J : Subgroup (q2cTE6G n Fld))
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    (huniq : ∀ J' : Subgroup (q2cTE6G n Fld),
      CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J)
    (K' : Type) [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ m)
    (he : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 6) K'))) : False := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have h1 : Nat.card Fld = 1 := by rw [h] at hFldcard; simpa using hFldcard
      haveI : Nontrivial Fld := inferInstance
      have h2 : 1 < Nat.card Fld := Finite.one_lt_card
      omega
    · exact h
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel (q2cTE6G n Fld) .twistedE6 2 n :=
    ⟨⟨Nat.prime_two, hn, rfl⟩, twistedChevalleyModel_largeEven .E6 hFldcard⟩
  have hsimple : IsSimpleGroup (q2cTE6G n Fld) :=
    CFSG.Timmesfeld.isSimpleGroup_of_lieModel (Or.inr (Or.inl ⟨rfl, by decide, hchev⟩))
  obtain ⟨hFinR, hcomm⟩ := q2c_twE6_recipe_perfect (n := n) hFldcard
  haveI : Finite (q2cTE6G n Fld) := hFinR
  haveI : Group.IsPerfect (q2cTE6G n Fld) := Group.isPerfect_def.mpr hcomm
  have hnaR : ∃ a b : q2cTE6G n Fld, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (G := q2cTE6G n Fld) ⟨⟨fun a b => h a b⟩⟩
  have hZ : Subgroup.center (q2cTE6G n Fld) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (q2cTE6G n Fld))
      with hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := hnaR
      have ha : a ∈ Subgroup.center (q2cTE6G n Fld) := by rw [hc]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  let θ : q2cTE6G n Fld ⧸ Subgroup.center (q2cTE6G n Fld) ≃* q2cTE6G n Fld :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hθmk : ∀ x : q2cTE6G n Fld, θ (QuotientGroup.mk x) = x := by
    intro x
    change QuotientGroup.quotientBot
      ((QuotientGroup.quotientMulEquivOfEq hZ) (QuotientGroup.mk x)) = x
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hθu : ggInducedAut θ u = u := by
    ext r
    obtain ⟨y, rfl⟩ := θ.surjective r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    change ggInducedAut θ u (θ (QuotientGroup.mk x)) = u (θ (QuotientGroup.mk x))
    rw [ggInducedAut_apply, hθmk, hθmk x]
  have hlabL : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel) := ⟨hn, rfl⟩
  have hHasL : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel)
      (q2cTE6G n Fld ⧸ Subgroup.center (q2cTE6G n Fld)) := by
    unfold GGHasLabel
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted]
    exact ⟨Fld, inferInstance, inferInstance, hFldcard, ⟨θ⟩⟩
  have hmark : LargeEvenMarking (q2cTE6G n Fld) (fun lab _ _ I' _ θ' =>
      (lab.tag = .E6 ∨ lab.tag = .twE6) ∧ ggInducedAut θ' u ∈ I') := by
    refine ⟨hcomm, ⟨.twE6, 0, n⟩, hlabL, ?_⟩
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted]
    refine ⟨Fld, inferInstance, inferInstance, hFldcard, ?_⟩
    exact ⟨hsimple, hnaR, θ, Or.inr rfl, by rw [hθu]; exact hu⟩
  have hu3 : u ^ 3 = 1 := by rw [← huo]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huo
    norm_num at huo
  have hJ' : IsComponentOf J (ggAutFixedSubgroup u) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hJ
  have huniq' : ∀ J' : Subgroup (q2cTE6G n Fld),
      IsComponentOf J' (ggAutFixedSubgroup u) → J' = J :=
    fun J' h => huniq J' (CFSG.Assembly.isComponentOf_iff_open.1 h)
  by_cases hn2 : 2 ≤ n
  · have hq : LargeEvenMarking (q2cTE6G n Fld) (fun lab _ _ _ _ _ => 2 ≤ lab.n) := by
      refine ⟨hcomm, ⟨.twE6, 0, n⟩, hlabL, ?_⟩
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted]
      refine ⟨Fld, inferInstance, inferInstance, hFldcard, ?_⟩
      exact ⟨hsimple, hnaR, θ, hn2⟩
    have hdat : GGTorsionDatum (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) 3 u J :=
      ⟨Nat.prime_three, by norm_num, hu3, hu1, hJ', hmark⟩
    obtain ⟨-, lab₁, hlab₁, hraw₁⟩ :=
      TablePThreeKG.ggTorsion_E6eps_unique_label hdat hq huniq'
    have hc : (lab₁.tag = .E6 ∨ lab₁.tag = .twE6) ∧
        ∃ lab', LargeEvenInLambda2 lab' ∧ GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧
          TablePThreeKG.E6CompLabel (2 ^ lab₁.n) lab' :=
      TablePThreeKG.e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun _ _ _ _ h => h.2.2.elim fun _ hh => hh) hraw₁)
    have hHas₁ : GGHasLabel lab₁ (q2cTE6G n Fld ⧸ Subgroup.center (q2cTE6G n Fld)) := by
      unfold GGHasLabel
      refine largeEvenRawDatum_mono (fun R' _ I' F' h => ⟨h.2.2.choose⟩) hraw₁
    have heqL : (⟨.twE6, 0, n⟩ : LargeEvenLabel) = lab₁ :=
      TablePThreeKG.eq_of_ggLabelIso_of_e6Tag
        (ggLabelRigidInput_holds (⟨.twE6, 0, n⟩) lab₁
          (q2cTE6G n Fld ⧸ Subgroup.center (q2cTE6G n Fld)) hlabL hlab₁ hHasL hHas₁)
        (Or.inr rfl)
    have hlab₁n : lab₁.n = n := by rw [← heqL]
    obtain ⟨-, lab', hΛ', hhas', hcomp'⟩ := hc
    have hcompn : TablePThreeKG.E6CompLabel (2 ^ n) lab' := by
      rw [hlab₁n] at hcomp'
      exact hcomp'
    have hΛA : LargeEvenInLambda2 (⟨.A, 5, m⟩ : LargeEvenLabel) :=
      ⟨le_trans (by norm_num : 1 ≤ 2) hm, by norm_num, fun h => by omega⟩
    have hhasA : GGHasLabel (⟨.A, 5, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
      unfold GGHasLabel
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
      exact ⟨K', inferInstance, inferInstance, hK', he⟩
    have hIso := ggLabelRigidInput_holds lab' (⟨.A, 5, m⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) hΛ' hΛA hhas' hhasA
    have heq' : lab' = ⟨.A, 5, m⟩ := q2cTE6_labelIso_A5 hIso
    have hmn : m = n := by
      rcases hcompn with ⟨-, -, hp⟩ | ⟨-, -, hp⟩ | ⟨-, hp⟩ | ⟨hr2, hp, -⟩
      · rw [heq'] at hp
        exact Nat.pow_right_injective (by norm_num) hp
      · rw [heq'] at hp
        exact Nat.pow_right_injective (by norm_num) hp
      · rw [heq'] at hp
        exact Nat.pow_right_injective (by norm_num) hp
      · rw [heq'] at hr2
        norm_num at hr2
    rw [hmn] at hpm
    exact q2cTE6_three_not_dvd h3n hpm
  · have hn1 : n = 1 := by omega
    subst hn1
    have hchev1 : CFSG.Blueprint.ChevalleyExceptionalModel (q2cTE6G 1 Fld) .twistedE6 2 1 :=
      hchev
    obtain ⟨dd, hdchar, hdfield, hd, ⟨e⟩⟩ :=
      TablePThreeKG.e6TwoLeaf_index_twE6 (p := 2) (f := 1) hchev1
    have hdfield2 : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize dd.1 = 2 := by
      rw [hdfield]
      norm_num
    have hnotE6 : ¬ (∃ q : TauCeti.PrimePower, dd.1 = .E6 q) := by
      rintro ⟨q1, hq1⟩
      obtain ⟨q2, hq2⟩ := hd
      rw [hq1] at hq2
      cases hq2
    have hEq : GGInndiagCommEq (q2cTE6G 1 Fld) (q2cTE6ID 1 Fld)
        (LargeEvenChevFieldImage (LargeEvenCartanE 6) Fld
          (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 1)) :=
      InndiagCommRest.ggInndiagCommEq_twE6 (n := 1) le_rfl Fld hFldcard
    obtain ⟨lab', hΛ', hhas', -, hpairT⟩ :=
      TablePThreeKG.e6TwoLeaf_component (X := q2cTE6G 1 Fld) (δ := u) (J := J)
        (R := q2cTE6G 1 Fld) (I := q2cTE6ID 1 Fld)
        (F := LargeEvenChevFieldImage (LargeEvenCartanE 6) Fld
          (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 1))
        θ hcomm hu3 hu1 hJ' huniq' (by rw [hθu]; exact hu) hEq dd hdchar hdfield2
        (Or.inr hd) e
    have hcT : TablePThreeKG.E6TwoCompLabelT lab' := hpairT hnotE6
    have hΛA : LargeEvenInLambda2 (⟨.A, 5, m⟩ : LargeEvenLabel) :=
      ⟨le_trans (by norm_num : 1 ≤ 2) hm, by norm_num, fun h => by omega⟩
    have hhasA : GGHasLabel (⟨.A, 5, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
      unfold GGHasLabel
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
      exact ⟨K', inferInstance, inferInstance, hK', he⟩
    exact q2cTE6_e6TwoCompLabelT_iso_A5_false hcT
      (ggLabelRigidInput_holds lab' (⟨.A, 5, m⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) hΛ' hΛA hhas' hhasA)

theorem q2c_twE6_three_false {p m : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .twE6)
    (hsplit : LargeEvenSplit p lab) (hm : 2 ≤ m) (hpm : p ∣ 2 ^ m - 1) :
    LargeEvenLabelAll lab (fun R _ I _ => p = 3 →
      ∀ u ∈ I, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 6) K)) → False) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  intro Q hQ
  obtain ⟨Fld, hFldfld, hFldfin, hFldcard, hQ'⟩ := hQ
  refine ⟨Fld, hFldfld, hFldfin, hFldcard, hQ', ?_⟩
  intro hp3 u hu huo J hJ huniq K' hK'fld hK'fin hK' he
  subst hp3
  have h3n : 3 ∣ 2 ^ n + 1 := by
    rcases hsplit with h | h | h | h
    · exact absurd h.1 (by simp [LargeEvenUntwisted])
    · exact h.2.2
    · rcases h.1 with h' | h' <;> cases h'
    · have hn1 : n = 1 := h.1
      rw [hn1]
      norm_num
  exact q2cTE6_recipe hFldcard h3n hm hpm u hu huo J hJ huniq K' hK' he

private theorem q2cTE6_congr_congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (f : MulAut H) : MulAut.congr e (MulAut.congr e.symm f) = f := by
  refine MulEquiv.ext fun g => ?_
  simp [MulAut.congr_apply, MulEquiv.trans_apply]

theorem q2cTE6_five_transport {n m : ℕ} {Fld : Type} [Field Fld] [Finite Fld]
    (hFldcard : Nat.card Fld = (2 ^ n) ^ 2) (hm : 2 ≤ m)
    (u : MulAut (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n)))
    (hu : u ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) Fld
      (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n)) (huo : orderOf u = 5)
    (J : Subgroup (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) Fld LargeEvenRhoE6 n)))
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    (K' : Type) [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ m)
    (he : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 5) K'))) :
    ∃ s : ℕ, 1 ≤ s ∧ Nat.card K' = (2 ^ n) ^ s ∧ s * 4 ≤ 6 := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have h1 : Nat.card Fld = 1 := by rw [h] at hFldcard; simpa using hFldcard
      haveI : Nontrivial Fld := inferInstance
      have h2 : 1 < Nat.card Fld := Finite.one_lt_card
      omega
    · exact h
  haveI hchar : CharP Fld 2 := charP_two_of_card (m := n * 2) (by rw [hFldcard, pow_mul])
  set σ : Fld ≃+* Fld := RingEquiv.ofBijective (iterateFrobenius Fld 2 n)
    ⟨(iterateFrobenius Fld 2 n).injective,
      Finite.surjective_of_injective (iterateFrobenius Fld 2 n).injective⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hFldcard σ hσ
  let e : TwE6Delta.RecipeR Fld n ≃* ↥(graphFixedRootGroup TwistTag.E6 Fld σ.toRingHom) :=
    ε.symm
  let u' : MulAut ↥(graphFixedRootGroup TwistTag.E6 Fld σ.toRingHom) := MulAut.congr e u
  have heu : MulAut.congr ε u' = u := q2cTE6_congr_congr_symm ε u
  have hu'i : u' ∈ (RecipeExcLang.twConj Fld σ).range :=
    (hε u').1 (by rw [heu]; exact hu)
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 hu'i
  have huord : orderOf u' = 5 := by
    change orderOf (MulAut.congr e u) = 5
    rw [MulEquiv.orderOf_eq (MulAut.congr e) u, huo]
  have huo' : u' ^ 5 = 1 := by
    rw [← huord]
    exact pow_orderOf_eq_one u'
  have hwp : w ^ 5 = 1 := by
    apply NoOffTwE6Three.twConj_injective hn hFldcard σ hσ
    rw [map_pow, map_one, hw, huo']
  have hw1 : w ≠ 1 := by
    rintro rfl
    have h1 : u' = 1 := by rw [← hw, map_one]
    rw [h1, orderOf_one] at huord
    norm_num at huord
  obtain ⟨p₀, hp₀, hp₀2, hq₀⟩ :=
    exists_setup_prime Nat.prime_two hn Nat.prime_five (by norm_num) (by norm_num)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1a, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two hn hFldcard σ hσ
      Nat.prime_five (by norm_num) hp₀ hp₀2 hq₀ monomialToralAt_E6_five
      (RecipeExcLang.twConj Fld σ w) (w : ModGL TwistTag.E6.tag Fld)
      (NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2)
      (fun c => RecipeExcLang.coe_twConj σ w c)
      (by rw [← Subgroup.coe_pow, hwp]; rfl) (fun h1 => hw1 (Subtype.ext h1))
  haveI hcharL : CharP (AlgebraicClosure Fld) 2 :=
    charP_of_injective_algebraMap (algebraMap Fld (AlgebraicClosure Fld)).injective 2
  have hpL : ((5 : ℕ) : AlgebraicClosure Fld) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_five hFldcard (by norm_num)
  have hsmall : Tag.E6 = .G2 → 5 ≤ 5 ∨ 4 ≤ S.D.q := fun h => absurd h (by decide)
  have hTame := langSetup_hTame_of_prime S Nat.prime_five hpL hsmall hT hap h1a
  let J' : Subgroup ↥(graphFixedRootGroup TwistTag.E6 Fld σ.toRingHom) := J.map e.toMonoidHom
  have hgg : ggAutFixedSubgroup u = fixSubgroup u := by
    ext x
    rw [mem_ggAutFixedSubgroup, mem_fixSubgroup]
  have hfix : (fixSubgroup u).map e.toMonoidHom = fixSubgroup u' :=
    (fixSubgroup_congr e u).symm
  have hJ' : CFSG.Open.IsComponentOf J' (fixSubgroup u') := by
    have h := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e hJ
    rw [hgg] at h
    rw [hfix] at h
    exact h
  have hJ'' : CFSG.Open.IsComponentOf J' (fixSubgroup (RecipeExcLang.twConj Fld σ w)) := by
    rw [hw]
    exact hJ'
  obtain ⟨i, hq, hmap⟩ := components_of_langSetup S Nat.prime_five ι hinj hrange
    (RecipeExcLang.twConj Fld σ w) hconj hT hap h1a hTame hJ''
  let eJR : ↥J' ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J'.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨θ0⟩ := he
  let eJJ' : ↥J ≃* ↥J' := J.equivMapOfInjective e.toMonoidHom e.injective
  have hc : (Subgroup.center ↥J).map eJJ' = Subgroup.center ↥J' := Subgroup.map_center_eq eJJ'
  let θJ' : ↥J' ⧸ Subgroup.center ↥J' ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 5) K') :=
    (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J') eJJ' hc).symm.trans θ0
  have hcR : (Subgroup.center ↥J').map eJR =
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    Subgroup.map_center_eq eJR
  let θR : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 5) K') :=
    (QuotientGroup.congr (Subgroup.center ↥J')
      (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) eJR hcR).symm.trans θJ'
  obtain ⟨hrank, hfield, -⟩ :=
    q2cEA_typeA_data (τ := Tag.E6) (Or.inl rfl) S Nat.prime_five (by norm_num)
      hT hap h1a i hq (by norm_num : 5 ≤ 5) hm hK' θR
  let s : ℕ := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  refine ⟨s, ?_, ?_, ?_⟩
  · have hpos := (outer_componentOrbitLength_spec S hT i).1
    simp only [s]
    omega
  · rw [hfield, hSq]
  · have hle := LangRat.componentOrbitLength_mul_compRank_le (τ := Tag.E6) S hT i
    have h4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    rw [h4] at hle
    exact hle

private theorem q2cTE6_five_not_dvd {n : ℕ} (h5n : 5 ∣ 2 ^ n + 1) (h5m : 5 ∣ 2 ^ n - 1) :
    False := by
  have hd : 5 ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h5n h5m
  have heq : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [heq] at hd
  exact (by norm_num : ¬ (5 : ℕ) ∣ 2) hd

theorem q2c_twE6_five_false {p m : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .twE6)
    (hsplit : LargeEvenSplit p lab) (hm : 2 ≤ m) (hpm : p ∣ 2 ^ m - 1) :
    LargeEvenLabelAll lab (fun R _ I _ => p = 5 →
      ∀ u ∈ I, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) → False) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  intro Q hQ
  obtain ⟨Fld, hFldfld, hFldfin, hFldcard, hQ'⟩ := hQ
  refine ⟨Fld, hFldfld, hFldfin, hFldcard, hQ', ?_⟩
  intro hp5 u hu huo J hJ huniq K' hK'fld hK'fin hK' he
  subst hp5
  obtain ⟨s, hs1, hfield, hs4⟩ :=
    q2cTE6_five_transport hFldcard hm u hu huo J hJ K' hK' he
  have hs : s = 1 := by omega
  rw [hs, pow_one] at hfield
  have hmn : m = n := by
    have h2 : 2 ^ m = 2 ^ n := by rw [← hK', hfield]
    exact Nat.pow_right_injective (le_refl 2) h2
  rw [hmn] at hpm
  have h5n : 5 ∣ 2 ^ n + 1 := by
    rcases hsplit with h | h | h | h
    · exact absurd h.1 (by simp [LargeEvenUntwisted])
    · exact h.2.2
    · rcases h.1 with h' | h' <;> cases h'
    · exact absurd h.2 (by norm_num)
  exact q2cTE6_five_not_dvd h5n hpm

theorem q2c_rLevel_twE6 :
    Q2CensusRLevel (fun lab => lab.tag = .twE6) (fun _ => False) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  have h1 := largeEvenLabelAll_and (q2c_twE6_rank hS hp hp2 hsplit hpd)
    (q2c_twE6_three_false (p := p) (m := m) hS hsplit hm hpm)
  have hall := largeEvenLabelAll_and h1
    (q2c_twE6_five_false (p := p) (m := m) hS hsplit hm hpm)
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, ⟨hrank, hthree⟩, hfive⟩
  refine ⟨hq, fun A hA hAI hbig _ hlo hup u hu huo J hJ huniq _ K _ _ hK he => ?_⟩
  exfalso
  rcases hrank A hA hAI hbig hlo hup with ⟨hp3, hd6⟩ | ⟨hp5, hd5⟩
  · subst hd6
    exact hthree hp3 u (hAI u hu) huo J hJ huniq K hK he
  · subst hd5
    exact hfive hp5 u (hAI u hu) huo J hJ huniq K hK he

end CFSG.StandardType
