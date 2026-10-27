module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.PCore.Construction
public import CFSG.Open.StatedDefs
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Walter.Bender1970.S2.PSL2Overgroups
import CFSG.Walter.PSL2Facts.Even
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
import CFSG.Assembly.OrderReductions.PermutationReduction
import CFSG.CGT.PushingUpLit.CGT6.SixFourLTwo
import CFSG.CharacterTheory.Burnside
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.CGT.PushingUp.BlockOrder
import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes
import CFSG.CGT.PushingUpLit.CGT6.SixFiveArrow
import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL
import CFSG.CGT.PushingUpLit.CGT6.SixFourStd
import CFSG.CGT.PushingUpLit.CGT6.SixFourTen
import CFSG.CGT.PushingUpLit.CGT6.SixTwoOff
import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
import CFSG.CGT.PushingUpLit.NineContent
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.GH74.SectionalRank
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.Walter.JRFacts
import CFSG.Walter.PSL2Facts
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.Open
open CFSG.BenderSuzuki.MatrixGroups (PSL2MatrixGroup)

private noncomputable def pgl2EquivPSL2OfCharTwo {F : Type} [Field F] [Finite F]
    (h2 : ringChar F = 2) : Matrix.ProjGenLinGroup (Fin 2) F ≃* PSL2MatrixGroup F :=
  (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
      Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun (r : Fˣ) => by
        obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two h2 (r : F)
        have hb0 : b ≠ 0 := by
          rintro rfl
          exact r.ne_zero (by rw [hb, mul_zero])
        refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
        rw [Fintype.card_fin, Units.val_pow_eq_pow_val, Units.val_mk0, sq, hb]⟩).symm

section Dickson

private theorem card_psl2MatrixGroup_two_pow {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) :
    Nat.card (PSL2MatrixGroup K) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    K).toEquiv]
  exact CFSG.CGT.PushingUpLit.CGT6.card_psl2_two_pow hm hK

private theorem isSolvable_psl2_galoisField_two_one :
    Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 1)) := by
  classical
  haveI : Fintype (PSL2MatrixGroup (GaloisField 2 1)) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have h6 := card_psl2MatrixGroup_two_pow le_rfl hK
  rw [Nat.card_eq_fintype_card] at h6
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [h6]; norm_num)


theorem exists_mulEquiv_psl2_of_not_isSolvable {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {G : Type} [Group G] (ι : G →* PSL2MatrixGroup F)
    (hι : Function.Injective ι) (hG : ¬ Group.IsSolvable G) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (G ≃* PSL2MatrixGroup (GaloisField 2 m)) := by
  classical
  set H := ι.range with hHdef
  let eG : G ≃* H := MonoidHom.ofInjective hι
  have hsolv : ∀ {A : Type} [Group A], (H ≃* A) → Group.IsSolvable A → False := by
    intro A _ e hA
    apply hG
    haveI := hA
    exact Group.isSolvable_of_isSolvable_injective (f := (eG.trans e).toMonoidHom)
      (eG.trans e).injective
  have hcomm : (∀ a b : H, a * b = b * a) → False := fun h =>
    hsolv (MulEquiv.refl H) (isSolvable_of_comm h)
  have hpsl : ∀ m : ℕ, m ≠ 0 → Nonempty (H ≃* PSL2MatrixGroup (GaloisField 2 m)) →
      ∃ m : ℕ, 2 ≤ m ∧ Nonempty (G ≃* PSL2MatrixGroup (GaloisField 2 m)) := by
    rintro m hm ⟨e⟩
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      exact (hsolv e isSolvable_psl2_galoisField_two_one).elim
    · exact ⟨m, hm2, ⟨eG.trans e⟩⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification (p := 2) hF
      H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hzc, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hC, -, -, hNC⟩ | ⟨m, hm, -, he⟩ | ⟨m, hm, -, ⟨e⟩⟩
  · haveI := hEl
    exact (hcomm fun a b => mul_comm' a b).elim
  · haveI := hcyc
    exact (hcomm fun a b => mul_comm' a b).elim
  · haveI : NeZero z := ⟨by
      rintro rfl
      have : Nat.card H = 0 := by rw [hzc, mul_zero]
      exact (Nat.card_pos (α := H)).ne' this⟩
    exact (hsolv eD (CFSG.Walter.isSolvable_dihedralGroup' z)).elim
  · exact (hsolv eA4 CFSG.OrderReductions.PermutationReduction.alternating_four_solvable).elim
  · exact (hsolv eS4 CFSG.OrderReductions.PermutationReduction.permutation_four_solvable).elim
  ·
    have hK4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 two_ne_zero
    haveI : IsSimpleGroup (PSL2MatrixGroup (GaloisField 2 2)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK4]; norm_num)
    obtain ⟨e60⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (G := PSL2MatrixGroup (GaloisField 2 2))
      (by rw [card_psl2MatrixGroup_two_pow (by norm_num) hK4]; norm_num)
    exact ⟨2, le_rfl, ⟨eG.trans (eA5.trans e60.symm)⟩⟩
  ·
    haveI := hN
    haveI := hNel
    haveI := hC
    have hle : commutator H ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hNC inferInstance
    have hNN : ⁅N, N⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : N) ⟨x, hx⟩)
    refine (hsolv (MulEquiv.refl H) ((isSolvable_def _).2 ⟨2, ?_⟩)).elim
    rw [derivedSeries_succ, derivedSeries_one, eq_bot_iff, ← hNN]
    exact Subgroup.commutator_mono hle hle
  · exact hpsl m hm he
  · exact hpsl m hm ⟨e.trans (pgl2EquivPSL2OfCharTwo (ringChar.eq (GaloisField 2 m) 2))⟩

end Dickson

section Section


theorem exists_statedProj_of_hom {X Y : Type} [Group X] [Finite X] [Group Y] {U : Subgroup X}
    (hrad : inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) = U)
    (f : ↥(Subgroup.normalizer (U : Set X)) →* Y) (hf : IsPGroup 2 f.ker)
    (L₀ : Subgroup Y) (hab : ⁅f.range, f.range⁆ ≤ L₀)
    (hL₀ : L₀ = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F) (s : ℕ), Nat.card F = 2 ^ s ∧
      ∃ ι : ↥L₀ →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Injective ι)
    (S : Subgroup (↥(Subgroup.normalizer (U : Set X)) ⧸
      U.subgroupOf (Subgroup.normalizer (U : Set X))))
    (hSq : IsQuasisimple S) :
    ∃ (s : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 2 ≤ s ∧ Nat.card K = 2 ^ s ∧
      ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
        Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL 2 K)) := by
  classical
  have hker : f.ker ≤ U.subgroupOf (Subgroup.normalizer (U : Set X)) := by
    intro n hn
    have hle : f.ker ≤ pCore 2 ↥(Subgroup.normalizer (U : Set X)) := le_sSup ⟨inferInstance, hf⟩
    rw [Subgroup.mem_subgroupOf]
    have h : (n : X) ∈ inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) := ⟨n, hle hn, rfl⟩
    rwa [hrad] at h
  let θ : f.range →* ↥(Subgroup.normalizer (U : Set X)) ⧸ U.subgroupOf (Subgroup.normalizer (U : Set X)) :=
    (QuotientGroup.map f.ker (U.subgroupOf (Subgroup.normalizer (U : Set X))) (MonoidHom.id _) hker).comp
      (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom
  have hθ : ∀ n : ↥(Subgroup.normalizer (U : Set X)), θ (f.rangeRestrict n) = QuotientGroup.mk n := by
    intro n
    have h : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict n) =
        QuotientGroup.mk n := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.map f.ker (U.subgroupOf (Subgroup.normalizer (U : Set X))) (MonoidHom.id _) hker
      ((QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict n)) = _
    rw [h]
    rfl
  set T : Subgroup f.range := (S.comap (QuotientGroup.mk' (U.subgroupOf (Subgroup.normalizer (U : Set X))))).map f.rangeRestrict
    with hTdef
  have hTS : T.map θ = S := by
    rw [hTdef, Subgroup.map_map]
    have he : θ.comp f.rangeRestrict = QuotientGroup.mk' (U.subgroupOf (Subgroup.normalizer (U : Set X))) :=
      MonoidHom.ext fun n => hθ n
    rw [he, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hSperf : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.1 hSq.1
  set H : Subgroup f.range := ⁅T, T⁆ with hHdef
  have hHS : H.map θ = S := by rw [hHdef, Subgroup.map_commutator, hTS, hSperf]
  have hHL : ∀ h : ↥H, ((h : f.range) : Y) ∈ L₀ := by
    intro h
    apply hab
    have hmem : ((h : f.range) : Y) ∈ ⁅T.map f.range.subtype, T.map f.range.subtype⁆ := by
      rw [← Subgroup.map_commutator]
      exact ⟨h, h.2, rfl⟩
    exact Subgroup.commutator_mono (Subgroup.map_subtype_le T) (Subgroup.map_subtype_le T) hmem
  let θH : ↥H →* ↥S := (θ.comp H.subtype).codRestrict S fun h => hHS ▸ ⟨h, h.2, rfl⟩
  have hθH : Function.Surjective θH := by
    rintro ⟨s, hs⟩
    rw [← hHS] at hs
    obtain ⟨h, hh, rfl⟩ := hs
    exact ⟨⟨h, hh⟩, rfl⟩
  have hSns : ¬ Group.IsSolvable S := by
    intro hsol
    obtain ⟨-, hsimp, a, b, hab'⟩ := hSq
    haveI := hsimp
    haveI : Group.IsSolvable (↥S ⧸ Subgroup.center ↥S) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center ↥S))
    exact hab' ((IsSimpleGroup.comm_iff_isSolvable).2 inferInstance a b)
  have hHns : ¬ Group.IsSolvable H := fun hsol => hSns (by
    haveI := hsol
    exact Group.isSolvable_of_surjective hθH)
  rcases hL₀ with hL₀ | ⟨F, _, _, s, hFs, ι₀, hι₀⟩
  ·
    refine (hHns (isSolvable_of_comm fun a b => ?_)).elim
    have ha := hHL a
    have hb := hHL b
    rw [hL₀, Subgroup.mem_bot] at ha hb
    have ha' : a = 1 := Subtype.ext (Subtype.ext ha)
    have hb' : b = 1 := Subtype.ext (Subtype.ext hb)
    rw [ha', hb']
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := s) (by rw [← Nat.card_eq_fintype_card, hFs])
    let j : ↥H →* ↥L₀ := (f.range.subtype.comp H.subtype).codRestrict L₀ hHL
    have hj : Function.Injective j := by
      intro a b hab''
      have h' := congrArg Subtype.val hab''
      exact Subtype.ext (Subtype.ext h')
    let eP : PSL2MatrixGroup F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)
    let ι : ↥H →* PSL2MatrixGroup F := eP.symm.toMonoidHom.comp (ι₀.comp j)
    have hι : Function.Injective ι := eP.symm.injective.comp (hι₀.comp hj)
    obtain ⟨m, hm, ⟨eH⟩⟩ := exists_mulEquiv_psl2_of_not_isSolvable hFs ι hι hHns
    have hKm : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
    haveI : IsSimpleGroup (PSL2MatrixGroup (GaloisField 2 m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [hKm]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)
    haveI : IsSimpleGroup ↥H := (MulEquiv.isSimpleGroup_congr eH).2 inferInstance
    have hθHi : Function.Injective θH := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θH.ker with hk | hk
      · exact (MonoidHom.ker_eq_bot_iff θH).1 hk
      · exfalso
        obtain ⟨-, hsimp, -⟩ := hSq
        haveI : Nontrivial ↥S := by
          by_contra hnt
          rw [not_nontrivial_iff_subsingleton] at hnt
          have : Subsingleton (↥S ⧸ Subgroup.center ↥S) :=
            (QuotientGroup.mk'_surjective _).subsingleton
          exact not_nontrivial_iff_subsingleton.2 this hsimp.toNontrivial
        obtain ⟨x, hx⟩ := exists_ne (1 : ↥S)
        obtain ⟨h, rfl⟩ := hθH x
        exact hx ((MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top h))
    let eS : ↥H ≃* ↥S := MulEquiv.ofBijective θH ⟨hθHi, hθH⟩
    refine ⟨m, GaloisField 2 m, inferInstance, inferInstance, hm, hKm, ⊥, bot_le, inferInstance,
      ⟨QuotientGroup.quotientBot.trans (eS.symm.trans (eH.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
          (GaloisField 2 m))))⟩⟩

theorem exists_statedProj_of_radical {X : Type} [Group X] [Finite X] {U P R : Subgroup X}
    (hrad : inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) = U)
    (hNP : Subgroup.normalizer (U : Set X) ≤ P) (hRP : R ≤ P) (hRn : (R.subgroupOf P).Normal)
    (hR2 : IsPGroup 2 R) (L₀ : Subgroup (↥P ⧸ R.subgroupOf P))
    (hab : commutator (↥P ⧸ R.subgroupOf P) ≤ L₀)
    (hL₀ : L₀ = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F) (s : ℕ), Nat.card F = 2 ^ s ∧
      Nonempty (↥L₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (S : Subgroup (↥(Subgroup.normalizer (U : Set X)) ⧸
      U.subgroupOf (Subgroup.normalizer (U : Set X))))
    (hSq : IsQuasisimple S) :
    ∃ (s : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 2 ≤ s ∧ Nat.card K = 2 ^ s ∧
      ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
        Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL 2 K)) := by
  haveI := hRn
  let f : ↥(Subgroup.normalizer (U : Set X)) →* ↥P ⧸ R.subgroupOf P :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hNP)
  have hmem : ∀ n : ↥f.ker, ((n : ↥(Subgroup.normalizer (U : Set X))) : X) ∈ R := fun n => by
    have h := n.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h
    exact h
  let g : ↥f.ker →* ↥R :=
    { toFun := fun n => ⟨_, hmem n⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : IsPGroup 2 f.ker :=
    hR2.of_injective g fun a b h => Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥R → X) h))
  refine exists_statedProj_of_hom hrad f hf L₀
    ((Subgroup.commutator_mono le_top le_top).trans hab) ?_ S hSq
  rcases hL₀ with hL₀ | ⟨F, hF, hFf, s, hFs, ⟨eL⟩⟩
  · exact Or.inl hL₀
  · exact Or.inr ⟨F, hF, hFf, s, hFs, eL.toMonoidHom, eL.injective⟩

end Section

end CFSG.RankThree.GF2n.Stroth80

end
