module

public import CFSG.RankThree.PartTwo.Sec16.Item163ResProofA7
public import CFSG.RankThree.PartTwo.Sec16.Item163ResProofMeets
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofQL
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

@[expose] def Step163LeA7Norm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ (e : G) (Le : Subgroup G),
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A e →
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) →
      ∀ K : Subgroup G, K ≤ Y → K ≤ Le →
        Le = K ⊔ (aschbacherSolvableCore 3 ↥Le).map Le.subtype →
        Le ≤ Subgroup.normalizer (Y : Set G)

namespace Res163

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_theta_of_card {K L : Subgroup G} (hKL : K ≤ L)
    (hcard : Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) =
      Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    L = K ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
  have hθL := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hθK := solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  set θL := aschbacherSolvableCore 3 ↥L with hθLdef
  set θK := aschbacherSolvableCore 3 ↥K with hθKdef
  have : θL.Normal := by
    have := hθL.2.1
    infer_instance
  set f : ↥K →* ↥L ⧸ θL := (QuotientGroup.mk' θL).comp (Subgroup.inclusion hKL) with hf
  have hker : f.ker ≤ θK := by
    have hmemθ : ∀ x : f.ker, Subgroup.inclusion hKL (x : ↥K) ∈ θL := fun x => by
      have h1 : f (x : ↥K) = 1 := x.2
      change QuotientGroup.mk' θL (Subgroup.inclusion hKL (x : ↥K)) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    let g : f.ker →* θL :=
      { toFun := fun x => ⟨Subgroup.inclusion hKL (x : ↥K), hmemθ x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective g := fun x y hxy => by
      have := congrArg (fun z : θL => ((z : ↥L) : G)) hxy
      exact Subtype.ext (Subtype.ext this)
    have : Group.IsSolvable θL := hθL.1
    refine hθK.2.2.2.1 f.ker inferInstance
      (Group.isSolvable_of_isSolvable_injective (f := g) hinj) fun h3 => ?_
    exact hθL.2.2.1 (h3.trans (Subgroup.card_dvd_of_injective g hinj))
  have hK1 : Nat.card ↥K = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hK2 : Nat.card ↥K = Nat.card (↥K ⧸ θK) * Nat.card θK :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup θK
  have hle : Nat.card f.ker ≤ Nat.card θK := Subgroup.card_le_of_le hker
  have hpos : 0 < Nat.card θK := Nat.card_pos
  have hrange : Nat.card (↥K ⧸ θK) ≤ Nat.card f.range := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul_of_lt_of_le hlt hle hpos
    omega
  have htop : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    rw [← hcard]
    exact hrange
  refine le_antisymm (fun l hl => ?_) (sup_le hKL (Subgroup.map_subtype_le _))
  obtain ⟨k, hk⟩ : QuotientGroup.mk' θL ⟨l, hl⟩ ∈ f.range := htop ▸ Subgroup.mem_top _
  have hkl : (Subgroup.inclusion hKL k)⁻¹ * ⟨l, hl⟩ ∈ θL := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hk' : (Subgroup.inclusion hKL k : ↥L ⧸ θL) = ((⟨l, hl⟩ : ↥L) : ↥L ⧸ θL) := hk
    rw [hk', inv_mul_cancel]
  have hle' : l = (k : G) * (((Subgroup.inclusion hKL k)⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_cancel_left]
  rw [hle']
  exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨_, hkl, rfl⟩)

theorem le_of_le_normalizer_of_eq_sup {K L Y : Subgroup G} (hLp : Group.IsPerfect ↥L)
    (hKY : K ≤ Y) (hcov : L = K ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype)
    (hN : L ≤ Subgroup.normalizer (Y : Set G)) : L ≤ Y := by
  have hθL := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θL := aschbacherSolvableCore 3 ↥L with hθLdef
  set M := Y.subgroupOf L with hM
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN g.2) n).mp hn
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp θL.subtype) := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective M q
    have hl : (l : G) ∈ ((K ⊔ θL.map L.subtype : Subgroup G) : Set G) := hcov ▸ l.2
    have hKN : K ≤ Subgroup.normalizer ((θL.map L.subtype : Subgroup G) : Set G) := by
      intro k hk
      have hkL : k ∈ L := hcov ▸ Subgroup.mem_sup_left hk
      have : (⟨k, hkL⟩ : ↥L) ∈ Subgroup.normalizer (θL : Set ↥L) := by
        have hθn : θL.Normal := by
          have := hθL.2.1
          infer_instance
        refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => hθn.conj_mem n hn _,
          fun hn => ?_⟩
        have := hθn.conj_mem _ hn (⟨k, hkL⟩ : ↥L)⁻¹
        rwa [show (⟨k, hkL⟩ : ↥L)⁻¹ * ((⟨k, hkL⟩ : ↥L) * n * (⟨k, hkL⟩ : ↥L)⁻¹) *
          (⟨k, hkL⟩ : ↥L)⁻¹⁻¹ = n by group] at this
      exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype this)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ hKN] at hl
    obtain ⟨k, hk, t, ht, hkt⟩ := hl
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    refine ⟨⟨t', ht'⟩, ?_⟩
    have hkL : k ∈ L := hcov ▸ Subgroup.mem_sup_left hk
    have hlk : l = ⟨k, hkL⟩ * t' := Subtype.ext hkt.symm
    have h1 : QuotientGroup.mk' M (⟨k, hkL⟩ : ↥L) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hKY hk))
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [hlk, map_mul, h1, one_mul]
  have : Group.IsSolvable θL := hθL.1
  have hsol : Group.IsSolvable (↥L ⧸ M) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (↥L ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  have hMtop : M = ⊤ := by
    by_contra hne
    have : Nontrivial (↥L ⧸ M) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ M) hsol
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end Res163

open Res163

theorem step163LeA7_of_norm
    (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hN : Step163LeA7Norm) (hA7 : Step163A7) : Step163LeA7 := by
  intro G _ _ A c L h Y hY a La ha hLa _ h7 hW hT hY'
  have ha' : Sec15R G A a La := sec15R_of_point h ha hLa
  have hS : Sec14Std G A c L := h.toSec14Std
  have h7all : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* alternatingGroup (Fin 7)) :=
    fun b Lb hb hLb => Step163Alt.nonempty_a7_of_point ha' h7 hT hb hLb
  have hno : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro b Lb hb hLb
    obtain ⟨χ⟩ := h7all b Lb hb hLb
    exact ⟨fun ψ => KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1.false (ψ.symm.trans χ)⟩
  have hY0 : Y ∈ scriptY0 A (lB A) := hY.prop
  have hYY : Y ∈ scriptY A := hY0.1.1
  obtain ⟨hYs, hYB, B, Q, e, K, Le, hP, he, hLe⟩ :=
    exists_point148_of_noHJ hCore h hno (hPoint G A c L hS) hY0
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKLe : K ≤ Le := hP.2.2.2.2.2.2.2.1
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  let := ker148_normal hYY.2
  have hkt := hKT G A c L hS Y hYY hYs hYB B Q e K Le hP
  have hsα : IsSimpleGroup ↥(img148 A Y K) := isSimpleGroup_img148_of_kType148 hS hkt
  obtain ⟨-, ⟨ψ⟩⟩ := Main148.theta_equiv_of_img148 hKM hKp hKq hsα (MulEquiv.refl _)
  obtain ⟨χ⟩ := h7all e Le he hLe
  have h2520 : Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = 2520 := by
    rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  have hKα : Nat.card ↥(img148 A Y K) = 2520 := by
    rcases hkt.2 with ⟨-, -, ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, -, -, hiso, -⟩⟩ | ⟨h3, -⟩
    · rw [Nat.card_congr φ.toEquiv, h2520]
    · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    · exact (not_isoLThreePi_of_card_eq_2520 h2520 p (f * e') hiso).elim
    · exfalso
      obtain ⟨-, hZ, -, -, -⟩ := KFacts.KS14.a7_facts _ ⟨χ⟩
      have h3' := h3.1
      rw [hZ, Subgroup.card_bot] at h3'
      omega
  have hcard : Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) =
      Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) := by
    rw [Nat.card_congr ψ.toEquiv, hKα, h2520]
  have hcov := eq_sup_theta_of_card hKLe hcard
  have he' : Sec15R G A e Le := sec15R_of_point h he hLe
  obtain ⟨v, hv, hev⟩ := hT.2 _ he
  have hTe : TransOmegaThree A e := transOmegaThree_of_conj hv hT hev
  have hLeN := hN G A c L h Y hY e Le he hLe ⟨χ⟩ hW hTe hY' K hKY hKLe hcov
  have hLeY : Le ≤ Y := le_of_le_normalizer_of_eq_sup
    (Sec6.isPerfect_of_mem_thetaComponentsAt he'.toSec13Data.mem_thetaComponentsAt) hKY hcov hLeN
  exact le_of_le_of_trans hA7 he' ⟨χ⟩ hW hTe hY hY' hLeY ha hLa

theorem step163PtA7_of_norm
    (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hN : Step163LeA7Norm) (hA7 : Step163A7) : Step163PtA7 :=
  step163PtA7_of_leA7 (step163LeA7_of_norm hCore hPoint hKT hN hA7)

theorem step163YaA7_of_norm
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (h1411 : Item1411_1R) (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType)
    (hN : Step163LeA7Norm) (hA7 : Step163A7) : Step163YaA7 :=
  step163YaA7_of_leA7 h1514 h1523 h153 hobs h1411 (step163MeetsPoint_of_steps148 hCore hPoint hKT)
    (step163LeA7_of_norm hCore hPoint hKT hN hA7) hA7

end CFSG.RankThree.PartTwo.Sec16
