module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyNine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineOffender
import CFSG.GroupTheory.ThompsonOffender
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNineAbFinal
import CFSG.GroupTheory.CardSupInf
import CFSG.CGT.PushingUpLit.CGT6.SixFourEightBasic
import CFSG.CGT.PushingUpLit.A78.BenderTI
import CFSG.CGT.PushingUpLit.C2L.Gomi42
import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
import CFSG.LocalAnalysis.UniquenessCase.UC22P20ya
import CFSG.ClassicalInvolution.AschTight.WreathedData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

theorem pCoreOf_sup_le_T (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ D.T :=
  uc22p20b_pCoreOf_le_T D le_sup_right

theorem pCoreOf_sup_le_centralizer_V (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤
      Subgroup.centralizer (c.V : Set G) := by
  rw [← cent_sup_eq_pCoreOf D Ch h4 h23 h1930 c]
  exact inf_le_right

theorem V_le_omegaOneCenterIn (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.V ≤ CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) := by
  intro v hv
  have hVH : c.V ≤ c.L ⊔ D.T := (c.V_le_T h4 h1930).trans le_sup_right
  have hVR : c.V ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVH
      (c.sup_le_normalizer_V D Ch) ((c.isElemAbelian_V h4 h1930).isPGroup)
  have hRC : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤
      Subgroup.centralizer (c.V : Set G) :=
    pCoreOf_sup_le_centralizer_V D Ch h4 h23 h1930 c
  rw [CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff]
  exact ⟨hVR hv, fun r hr =>
    (Subgroup.mem_centralizer_iff.mp (hRC hr) v hv).symm,
    (c.isElemAbelian_V h4 h1930).2 v hv⟩

theorem omegaOneCenterIn_le_thompsonJ (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ≤
      InS3.thompsonJ (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) := by
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  have hWr : CFSG.Open.IsElemAbelian 2 (W.subgroupOf R) :=
    CFSG.Open.IsElemAbelian.subgroupOf
      (CFSG.CGT.PushingUpLit.CGT6.isElemAbelian_omegaOneCenterIn R) R
  have hcent : ∀ A : Subgroup ↥R, IsElementaryAbelian 2 A →
      Nat.card A = 2 ^ CFSG.pRank 2 ↥R →
      W.subgroupOf R ≤ Subgroup.centralizer (A : Set ↥R) := by
    intro A _ _ x hx a ha
    have hxW : (x : G) ∈ W := Subgroup.mem_subgroupOf.mp hx
    have hxR : (x : G) ∈ Subgroup.centralizer (R : Set G) :=
      (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hxW).2.1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxR (a : G) a.2)
  have h : W.subgroupOf R ≤ CFSG.elemThompson ↥R 2 :=
    CFSG.le_elemThompson_of_le_centralizer Nat.prime_two hWr hcent
  have hmap := Subgroup.map_mono (f := R.subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le
      (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le R)] at hmap
  simpa [InS3.thompsonJ, CFSG.inSubgroup] using hmap

private theorem two_le_pRank_Z (D : Data G) (Ch : Choice2011 G) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) :
    2 ≤ CFSG.Open.pRank 2 D.Z := by
  obtain ⟨hV, hS⟩ := h23 h1930 c
  obtain ⟨hL2, _⟩ := hS
  have hadm := CFSG.Blueprint.LieModel.admissible hL2
  rw [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hf, -, hne, -⟩ := hadm
  have hn1 : CFSG.Open.pRank 2 D.Z ≠ 1 := by
    intro hn
    exact hne (by simp [hn])
  omega

private theorem not_L_le_centralizer_V (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ¬ c.L ≤ Subgroup.centralizer (c.V : Set G) := by
  intro hLC
  obtain ⟨hV, hLV, κ, hker, -⟩ := c.exists_coordinates_V D Ch h4 h23 h1930
  have hαall : ∀ l : ↥c.L, κ.α l = 1 := by
    intro l
    have hmem : l ∈ κ.α.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact ⟨l.2, hLC l.2⟩
    exact MonoidHom.mem_ker.mp hmem
  have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) κ.K) := by
    refine ⟨fun g h => ?_⟩
    obtain ⟨l, rfl⟩ := κ.α_surj g
    obtain ⟨l', rfl⟩ := κ.α_surj h
    rw [hαall l, hαall l']
  let M : Matrix.SpecialLinearGroup (Fin 2) κ.K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hM1 : M ≠ 1 := by
    intro h
    have := congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) κ.K =>
      (N : Matrix (Fin 2) (Fin 2) κ.K) 0 1) h
    simp [M] at this
  exact hM1 (Subsingleton.elim _ _)

private theorem card_fixed_eq_card_of_alpha_ne_one
    {L V : Subgroup G} {hV : IsElemAbelian 2 V}
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates L V hV hLV n)
    {l : ↥L} (hA1 : κ.α l ≠ 1) {e : Fin 2 → κ.K} (he : e ≠ 0)
    (hfix : (κ.α l : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ e = e) :
    Nat.card {x : Fin 2 → κ.K // (κ.α l : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ x = x} =
      Nat.card κ.K :=
  CFSG.Quasithin.card_fixed_eq_of_specialLinear_two (κ.α l).det_coe
    (by intro hmat; exact hA1 (Subtype.ext hmat)) he hfix

private theorem fixed_of_mem_centV
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {t l : G} (hl : l ∈ c.L) (hw : t * l⁻¹ ∈ Subgroup.centralizer (c.V : Set G)) :
    ∀ x : ↥(c.V ⊓ Subgroup.centralizer ({t} : Set G)),
      (κ.α ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ
        Multiplicative.toAdd (κ.β ⟨(x : G), x.2.1⟩) =
        Multiplicative.toAdd (κ.β ⟨(x : G), x.2.1⟩) := by
  intro x
  have hxt : t * (x : G) * t⁻¹ = (x : G) := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    calc t * (x : G) * t⁻¹ = (x : G) * t * t⁻¹ := by rw [hcomm]
      _ = x := by group
  have hcx' : (t * l⁻¹)⁻¹ * (x : G) * (t * l⁻¹) = (x : G) := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hw (x : G) x.2.1
    calc (t * l⁻¹)⁻¹ * (x : G) * (t * l⁻¹)
        = (t * l⁻¹)⁻¹ * ((x : G) * (t * l⁻¹)) := by group
      _ = (t * l⁻¹)⁻¹ * ((t * l⁻¹) * (x : G)) := by rw [hcomm]
      _ = x := by group
  have hxl : l * (x : G) * l⁻¹ = (x : G) := by
    calc l * (x : G) * l⁻¹
        = (t * l⁻¹)⁻¹ * (t * (x : G) * t⁻¹) * (t * l⁻¹) := by group
      _ = (t * l⁻¹)⁻¹ * (x : G) * (t * l⁻¹) := by rw [hxt]
      _ = x := hcx'
  have hconjV : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV ⟨l, hl⟩
      ⟨(x : G), x.2.1⟩ = ⟨(x : G), x.2.1⟩ := Subtype.ext hxl
  have h := congrArg Multiplicative.toAdd (κ.β_act ⟨l, hl⟩ ⟨(x : G), x.2.1⟩)
  rw [hconjV] at h
  exact h.symm

private theorem card_centV_eq_card_fixed
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {t l : G} (hl : l ∈ c.L) (hw : t * l⁻¹ ∈ Subgroup.centralizer (c.V : Set G)) :
    Nat.card ↥(c.V ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card {x : Fin 2 → κ.K //
        (κ.α ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ x = x} := by
  classical
  have hfix_f := fixed_of_mem_centV D Ch c κ hl hw
  let f : ↥(c.V ⊓ Subgroup.centralizer ({t} : Set G)) →
      {x : Fin 2 → κ.K // (κ.α ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ x = x} :=
    fun x => ⟨Multiplicative.toAdd (κ.β ⟨(x : G), x.2.1⟩), hfix_f x⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hval : (⟨(x : G), x.2.1⟩ : ↥c.V) = ⟨(y : G), y.2.1⟩ :=
        κ.β_bij.1 (Multiplicative.toAdd.injective (Subtype.ext_iff.mp hxy))
      exact congrArg (fun z : ↥c.V => (z : G)) hval
    · rintro ⟨y, hy⟩
      obtain ⟨v, hvβ⟩ := κ.β_bij.2 (Multiplicative.ofAdd y)
      have hconjV : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV ⟨l, hl⟩ v = v := by
        apply κ.β_bij.1
        rw [κ.β_act]
        simp [hvβ, hy]
      have hvl : l * (v : G) * l⁻¹ = (v : G) := congrArg Subtype.val hconjV
      have hvt : t * (v : G) * t⁻¹ = (v : G) := by
        have hdecomp : t = (t * l⁻¹) * l := by group
        calc t * (v : G) * t⁻¹
            = (t * l⁻¹) * (l * (v : G) * l⁻¹) * (t * l⁻¹)⁻¹ := by
                rw [hdecomp]; group
          _ = (t * l⁻¹) * (v : G) * (t * l⁻¹)⁻¹ := by rw [hvl]
          _ = (v : G) := by
              have hcomm := Subgroup.mem_centralizer_iff.mp hw (v : G) v.2
              rw [← hcomm]; group
      have hvC : (v : G) ∈ Subgroup.centralizer ({t} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have h2 : t * (v : G) = (v : G) * t := by
          have := congrArg (fun x => x * t) hvt
          simpa [mul_assoc] using this
        exact h2.symm
      refine ⟨⟨v, ⟨v.2, hvC⟩⟩, ?_⟩
      apply Subtype.ext
      show Multiplicative.toAdd (κ.β ⟨(v : G), v.2⟩) = y
      simpa using congrArg Multiplicative.toAdd hvβ
  exact Nat.card_congr (Equiv.ofBijective f hf)

private theorem card_centV_eq_of_mem_T_not_mem_centralizer
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {t : G} (ht : t ∈ D.T)
    (htC : t ∉ Subgroup.centralizer (c.V : Set G)) :
    Nat.card ↥(c.V ⊓ Subgroup.centralizer ({t} : Set G)) =
      2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  obtain ⟨hV, hLV, κ, hker, hcardK⟩ := c.exists_coordinates_V D Ch h4 h23 h1930
  obtain ⟨l, hl, hw⟩ :=
    exists_mem_T_inf_L_mul_inv_mem_centralizer D Ch h4 h23 h1930 c ht
  have hlT : l ∈ D.T := (Subgroup.mem_inf.mp hl).1
  have hlL : l ∈ c.L := (Subgroup.mem_inf.mp hl).2
  have hA1 : κ.α ⟨l, hlL⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨l, hlL⟩ : ↥c.L) ∈ κ.α.ker := MonoidHom.mem_ker.mpr h1
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
    apply htC
    have ht_eq : t = (t * l⁻¹) * l := by group
    rw [ht_eq]
    exact (Subgroup.centralizer (c.V : Set G)).mul_mem hw hmem.2
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (uc22main1_Z_ne_bot D)
  have hz₀V : (z₀ : G) ∈ c.V := uc22p22v_le_conjClosure c.N D.Z z₀.2
  let zV : ↥c.V := ⟨z₀, hz₀V⟩
  let e : Fin 2 → κ.K := Multiplicative.toAdd (κ.β zV)
  have he : e ≠ 0 := by
    intro h0
    have h1 : κ.β zV = 1 := Multiplicative.toAdd.injective (by simpa [e] using h0)
    have h2 : zV = 1 := κ.β_bij.1 (by simpa using h1)
    exact hz₀1 (Subtype.ext (by simpa [zV] using congrArg Subtype.val h2))
  have hfix : (κ.α ⟨l, hlL⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ e = e := by
    have hconj : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV ⟨l, hlL⟩ zV = zV := by
      apply Subtype.ext
      have hcomm : (z₀ : G) * l = l * z₀ :=
        Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D hlT) z₀ z₀.2
      calc l * (z₀ : G) * l⁻¹ = (z₀ : G) * l * l⁻¹ := by rw [hcomm]
        _ = z₀ := by group
    have h := congrArg Multiplicative.toAdd (κ.β_act ⟨l, hlL⟩ zV)
    rw [hconj] at h
    simpa [e] using h.symm
  have hfixcard := card_fixed_eq_card_of_alpha_ne_one κ hA1 he hfix
  rw [card_centV_eq_card_fixed D Ch c κ hlL hw, hfixcard, hcardK]

private theorem offender_X_elemAbelian (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {A : Subgroup G} (hAel : IsElemAbelian 2 A) :
    CFSG.Open.IsElemAbelian 2
        ((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
          CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ∧
      ((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
          CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤
        CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  let B : Subgroup G := A ⊓ R
  let X : Subgroup G := B ⊔ W
  have hW_le_R : W ≤ R := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le R
  have hBel : IsElemAbelian 2 B := CFSG.Open.IsElemAbelian.mono hAel inf_le_left
  have hWel : IsElemAbelian 2 W :=
    CFSG.CGT.PushingUpLit.CGT6.isElemAbelian_omegaOneCenterIn R
  have hcommBW : ∀ b ∈ B, ∀ w ∈ W, b * w = w * b := by
    intro b hb w hw
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hw).2.1 b hb.2
  have hXel : IsElemAbelian 2 X :=
    CFSG.Open.IsElemAbelian.sup_of_commute hBel hWel hcommBW
  have hXR : X ≤ R := sup_le inf_le_right hW_le_R
  exact ⟨by simpa [X, B, H, R, W] using hXel, by simpa [X, B, H, R, W] using hXR⟩

private theorem offender_card_le (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {A : Subgroup G} (hAT : A ≤ D.T) (hAel : IsElemAbelian 2 A)
    (hAmax : Nat.card A = 2 ^ CFSG.Open.pRank 2 D.T) :
    Nat.card ↥((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
        CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤ Nat.card A := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  let B : Subgroup G := A ⊓ R
  let X : Subgroup G := B ⊔ W
  change Nat.card X ≤ Nat.card A
  have hXel : IsElemAbelian 2 X := (offender_X_elemAbelian D Ch c hAel).1
  have hW_le_R : W ≤ R := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le R
  have hXT : X ≤ D.T :=
    sup_le (inf_le_left.trans hAT) (hW_le_R.trans (pCoreOf_sup_le_T D Ch c))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := CFSG.Quasithin.BlueprintB2.exists_card_eq_pow_of_isElementaryAbelian
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hXel)
  have hk_le : k ≤ CFSG.Open.pRank 2 D.T :=
    CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hXT hXel hk
  rw [hk, hAmax]
  exact Nat.pow_le_pow_right (by norm_num) hk_le

private theorem offender_pow_le_relIndex
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {A : Subgroup G} (hAT : A ≤ D.T)
    (hAR : ¬ A ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :
    2 ^ CFSG.Open.pRank 2 D.Z ≤
      (c.V ⊓ Subgroup.centralizer (A : Set G)).relIndex c.V := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let C : Subgroup G := Subgroup.centralizer (c.V : Set G)
  let CV : Subgroup G := c.V ⊓ Subgroup.centralizer (A : Set G)
  change 2 ^ CFSG.Open.pRank 2 D.Z ≤ CV.relIndex c.V
  have hH : A ≤ H := hAT.trans le_sup_right
  have hRinf : R = H ⊓ C := by
    exact (cent_sup_eq_pCoreOf D Ch h4 h23 h1930 c).symm
  have hAR_notC : ¬ A ≤ C := by
    intro hAC
    exact hAR (by change A ≤ R; rw [hRinf]; exact le_inf hH hAC)
  obtain ⟨a, haA, haC⟩ := Set.not_subset.mp hAR_notC
  have haT : a ∈ D.T := hAT haA
  have hrel_a : (c.V ⊓ Subgroup.centralizer ({a} : Set G)).relIndex c.V =
      2 ^ CFSG.Open.pRank 2 D.Z := by
    have hcard_a := card_centV_eq_of_mem_T_not_mem_centralizer D Ch h4 h23 h1930 c
      (t := a) haT haC
    have hcardV := card_V_eq D Ch h4 h23 h1930 c
    have hrel := Subgroup.relIndex_mul_card
      (H := c.V ⊓ Subgroup.centralizer ({a} : Set G)) (K := c.V)
    rw [inf_eq_left.mpr inf_le_left, hcard_a, hcardV] at hrel
    rw [pow_two] at hrel
    exact Nat.mul_right_cancel (pow_pos (by norm_num) _) hrel
  have hCV_le_CVa : CV ≤ c.V ⊓ Subgroup.centralizer ({a} : Set G) := by
    refine inf_le_inf le_rfl ?_
    exact Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      simpa [hx] using haA)
  calc 2 ^ CFSG.Open.pRank 2 D.Z
      = (c.V ⊓ Subgroup.centralizer ({a} : Set G)).relIndex c.V := hrel_a.symm
    _ ≤ CV.relIndex c.V := Subgroup.relIndex_le_of_le_left hCV_le_CVa
        Subgroup.index_ne_zero_of_finite

private theorem relIndex_centV_le_centW
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {A : Subgroup G} :
    (c.V ⊓ Subgroup.centralizer (A : Set G)).relIndex c.V ≤
      (CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓
        Subgroup.centralizer (A : Set G)).relIndex
      (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) := by
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  let C : Subgroup G := Subgroup.centralizer (c.V : Set G)
  let CV : Subgroup G := c.V ⊓ Subgroup.centralizer (A : Set G)
  let CW : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G)
  have hVW : c.V ≤ W := V_le_omegaOneCenterIn D Ch h4 h23 h1930 c
  have hleft : c.V ⊓ CW = CV := by
    change c.V ⊓ (W ⊓ Subgroup.centralizer (A : Set G)) =
      c.V ⊓ Subgroup.centralizer (A : Set G)
    rw [← inf_assoc, inf_eq_left.mpr hVW]
  have hright : W ⊓ CW = CW := by
    change W ⊓ (W ⊓ Subgroup.centralizer (A : Set G)) =
      W ⊓ Subgroup.centralizer (A : Set G)
    rw [← inf_assoc, inf_idem]
  calc CV.relIndex c.V = (c.V ⊓ CW).relIndex c.V := by rw [hleft]
    _ = CW.relIndex c.V := Subgroup.inf_relIndex_left c.V CW
    _ ≤ CW.relIndex W :=
        Subgroup.relIndex_le_of_le_right hVW Subgroup.index_ne_zero_of_finite
    _ = (W ⊓ CW).relIndex W := (Subgroup.inf_relIndex_left W CW).symm
    _ = CW.relIndex W := by rw [hright]

private theorem offender_chain_le
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {A : Subgroup G}
    (hAel : IsElemAbelian 2 A)
    (hcardX_le : Nat.card ↥((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
        CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤ Nat.card A) :
    (c.V ⊓ Subgroup.centralizer (A : Set G)).relIndex c.V ≤
        (CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓
          Subgroup.centralizer (A : Set G)).relIndex
        (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ∧
      (CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓
          Subgroup.centralizer (A : Set G)).relIndex
        (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤
        (A ⊓ CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))).relIndex
          (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ∧
      (A ⊓ CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))).relIndex
        (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤
        (A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)).relIndex A := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  let CV : Subgroup G := c.V ⊓ Subgroup.centralizer (A : Set G)
  let CW : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G)
  let B : Subgroup G := A ⊓ R
  let X : Subgroup G := B ⊔ W
  have hstep2 : CV.relIndex c.V ≤ CW.relIndex W := by
    simpa [CV, CW, W] using relIndex_centV_le_centW D Ch h4 h23 h1930 c
  have hAcent : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAel.1
  have hAW_le_CW : A ⊓ W ≤ CW :=
    le_inf inf_le_right (inf_le_left.trans hAcent)
  have hstep3 : CW.relIndex W ≤ (A ⊓ W).relIndex W :=
    Subgroup.relIndex_le_of_le_left hAW_le_CW Subgroup.index_ne_zero_of_finite
  have hB_le_A : B ≤ A := inf_le_left
  have hcentW_B : W ≤ Subgroup.centralizer (B : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hw).2.1 b hb.2
  have hW_norm_B : W ≤ Subgroup.normalizer (B : Set G) :=
    hcentW_B.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hstep4 : (A ⊓ W).relIndex W ≤ B.relIndex A := by
    have h := CFSG.GroupTheory.relIndex_inf_le_relIndex_of_card_sup_le
      (A := A) (B := B) (C := W) hB_le_A hW_norm_B (by simpa [X] using hcardX_le)
    simpa [B, inf_assoc, inf_eq_right.mpr (show W ≤ R from
      CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le R)] using h
  exact ⟨by simpa [CV, CW, W] using hstep2, by simpa [CW, W] using hstep3,
    by simpa [B, W, R, H] using hstep4⟩

private theorem offender_chain_last
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {A : Subgroup G} (hAT : A ≤ D.T) :
    (A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)).relIndex A ≤
      2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let C : Subgroup G := Subgroup.centralizer (c.V : Set G)
  change (A ⊓ R).relIndex A ≤ 2 ^ CFSG.Open.pRank 2 D.Z
  have hRinf : R = H ⊓ C := (cent_sup_eq_pCoreOf D Ch h4 h23 h1930 c).symm
  have hH : A ≤ H := hAT.trans le_sup_right
  have hAC_eq : A ⊓ R = A ⊓ C := by
    rw [hRinf, ← inf_assoc, inf_eq_left.mpr hH]
  rw [hAC_eq]
  calc (A ⊓ C).relIndex A = C.relIndex A := Subgroup.inf_relIndex_left A C
    _ ≤ C.relIndex D.T :=
        Subgroup.relIndex_le_of_le_right hAT Subgroup.index_ne_zero_of_finite
    _ = (D.T ⊓ C).relIndex D.T := (Subgroup.inf_relIndex_left D.T C).symm
    _ = 2 ^ CFSG.Open.pRank 2 D.Z := relIndex_centralizer_V_eq D Ch h4 h23 h1930 c

private theorem offender_chain_relIndex
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {A : Subgroup G}
    (hAT : A ≤ D.T) (hAel : IsElemAbelian 2 A)
    (hcardX_le : Nat.card ↥((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
        CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤ Nat.card A) :
    (c.V ⊓ Subgroup.centralizer (A : Set G)).relIndex c.V ≤
        (CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓
          Subgroup.centralizer (A : Set G)).relIndex
        (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ∧
      (CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓
          Subgroup.centralizer (A : Set G)).relIndex
        (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤
        (A ⊓ CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))).relIndex
          (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ∧
      (A ⊓ CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))).relIndex
        (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤
        (A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)).relIndex A ∧
      (A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)).relIndex A ≤
        2 ^ CFSG.Open.pRank 2 D.Z := by
  obtain ⟨h1, h2, h3⟩ := offender_chain_le D Ch h4 h23 h1930 c hAel hcardX_le
  exact ⟨h1, h2, h3, offender_chain_last D Ch h4 h23 h1930 c hAT⟩

private theorem offender_chain
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {A : Subgroup G} (hAT : A ≤ D.T)
    (hAel : IsElemAbelian 2 A)
    (hAmax : Nat.card A = 2 ^ CFSG.Open.pRank 2 D.T)
    (hAR : ¬ A ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :
    CFSG.Open.IsElemAbelian 2
        ((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
          CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ∧
      ((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
          CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) ≤
        CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ∧
      Nat.card ↥((A ⊓ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊔
          CFSG.RankThree.PartOne.omegaOneCenterIn
            (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) = Nat.card A ∧
      (CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓
          Subgroup.centralizer (A : Set G)).relIndex
        (CFSG.RankThree.PartOne.omegaOneCenterIn
          (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) =
      (c.V ⊓ Subgroup.centralizer (A : Set G)).relIndex c.V := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  let C : Subgroup G := Subgroup.centralizer (c.V : Set G)
  let CV : Subgroup G := c.V ⊓ Subgroup.centralizer (A : Set G)
  let CW : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G)
  let B : Subgroup G := A ⊓ R
  let X : Subgroup G := B ⊔ W
  obtain ⟨hXel, hXR⟩ := offender_X_elemAbelian D Ch c hAel
  have hcardX_le := offender_card_le D Ch c hAT hAel hAmax
  have hq_le := offender_pow_le_relIndex D Ch h4 h23 h1930 c hAT hAR
  obtain ⟨hstep2, hstep3, hstep4, hstep5⟩ :=
    offender_chain_relIndex D Ch h4 h23 h1930 c hAT hAel hcardX_le
  have hB_le_A : B ≤ A := inf_le_left
  have hcentW_B : W ≤ Subgroup.centralizer (B : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hw).2.1 b hb.2
  have hW_norm_B : W ≤ Subgroup.normalizer (B : Set G) :=
    hcentW_B.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hr34 : (A ⊓ W).relIndex W = B.relIndex A :=
    le_antisymm hstep4 (hstep5.trans ((hq_le.trans hstep2).trans hstep3))
  have hcardX : Nat.card X = Nat.card A := by
    have h := CFSG.GroupTheory.card_sup_eq_card_of_relIndex_eq
      (A := A) (B := B) (C := W) hB_le_A hW_norm_B ?_
    · simpa [X, B, W, R, H] using h
    · simpa [B, inf_assoc, inf_eq_right.mpr (show W ≤ R from
        CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le R)] using hr34
  have hr1 : CV.relIndex c.V = 2 ^ CFSG.Open.pRank 2 D.Z :=
    le_antisymm (hstep2.trans (hstep3.trans (hstep4.trans hstep5))) hq_le
  have hr2 : CW.relIndex W = 2 ^ CFSG.Open.pRank 2 D.Z :=
    le_antisymm (hstep3.trans (hstep4.trans hstep5)) (hq_le.trans hstep2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [X, B, W, R, H] using hXel
  · simpa [X, B, W, R, H] using hXR
  · simpa [X, B, W, R, H] using hcardX
  · exact hr2.trans hr1.symm

private theorem exists_sylow_coe_eq_T (D : Data G) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowG
  have hT2 : IsPGroup 2 D.T := hsyl.2.1
  have hnot : ¬ 2 ∣ D.T.index := by
    simpa [Subgroup.relIndex_top_right] using hsyl.2.2
  exact ⟨hT2.toSylow hnot, IsPGroup.toSylow_coe hT2 hnot⟩

private theorem pRank_sup_eq_pRank_T (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    CFSG.Open.pRank 2 (c.L ⊔ D.T) = CFSG.Open.pRank 2 D.T := by
  obtain ⟨S, hScoe⟩ := exists_sylow_coe_eq_T D
  refine le_antisymm ?_ (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 2) le_sup_right)
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 2) ?_
  intro E hEH hEel
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := CFSG.Quasithin.BlueprintB2.exists_card_eq_pow_of_isElementaryAbelian
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hEel)
  obtain ⟨x, hxH, hxE⟩ := CFSG.ClassicalInvolution.Disconnected.AschTight.exists_conj_le_of_sylow_le
    S (hScoe.trans_le le_sup_right) hEH hEel.isPGroup
  let E' : Subgroup G := CFSG.ClassicalInvolution.Generic.conjSub x E
  have hE'el : IsElemAbelian 2 E' :=
    CFSG.SectionRank.isElemAbelian_map hEel (MulAut.conj x).toMonoidHom
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hE'T : E' ≤ D.T := by
    simpa [E', hScoe] using hxE
  have hk_le : k ≤ CFSG.Open.pRank 2 D.T :=
    CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hE'T hE'el (by rw [hE'card, hk])
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk_le

private theorem exists_max_elemAbelian_not_le_pCoreOf (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hLJ : c.L ≤ InS3.thompsonJ (c.L ⊔ D.T)) :
    ∃ B : Subgroup G, B ≤ c.L ⊔ D.T ∧ IsElemAbelian 2 B ∧
      Nat.card B = 2 ^ CFSG.Open.pRank 2 (c.L ⊔ D.T) ∧
      ¬ B ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
  classical
  by_contra h
  have hall : ∀ B : Subgroup G, B ≤ c.L ⊔ D.T → IsElemAbelian 2 B →
      Nat.card B = 2 ^ CFSG.Open.pRank 2 (c.L ⊔ D.T) →
      B ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
    intro B hBH hBel hBcard
    by_contra hBR
    exact h ⟨B, hBH, hBel, hBcard, hBR⟩
  have hJR : InS3.thompsonJ (c.L ⊔ D.T) ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    InS3.thompsonJ_le_of_forall_max (X := c.L ⊔ D.T)
      (Y := CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) hall
  have hLR : c.L ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := hLJ.trans hJR
  exact not_L_le_centralizer_V D Ch h4 h23 h1930 c
    (hLR.trans (pCoreOf_sup_le_centralizer_V D Ch h4 h23 h1930 c))

private theorem exists_max_elemAbelian_in_T_not_le_pCoreOf (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hLJ : c.L ≤ InS3.thompsonJ (c.L ⊔ D.T)) :
    ∃ A : Subgroup G, A ≤ D.T ∧ IsElemAbelian 2 A ∧
      Nat.card A = 2 ^ CFSG.Open.pRank 2 D.T ∧
      ¬ A ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
  classical
  obtain ⟨B, hBH, hBel, hBcard, hBR⟩ :=
    exists_max_elemAbelian_not_le_pCoreOf D Ch h4 h23 h1930 c hLJ
  obtain ⟨S, hScoe⟩ := exists_sylow_coe_eq_T D
  obtain ⟨x, hxH, hxconj⟩ :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.exists_conj_le_of_sylow_le
      S (hScoe.trans_le le_sup_right) hBH hBel.isPGroup
  let A : Subgroup G := CFSG.ClassicalInvolution.Generic.conjSub x B
  have hAT : A ≤ D.T := by simpa [A, hScoe] using hxconj
  have hAel : IsElemAbelian 2 A :=
    CFSG.SectionRank.isElemAbelian_map hBel (MulAut.conj x).toMonoidHom
  have hAcard : Nat.card A = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hAmax : Nat.card A = 2 ^ CFSG.Open.pRank 2 D.T := by
    rw [hAcard, hBcard, pRank_sup_eq_pRank_T D Ch c]
  have hHnorm : c.L ⊔ D.T ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (c.L ⊔ D.T)
  have hAR : ¬ A ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
    intro hA
    apply hBR
    intro b hb
    have hbA : x * b * x⁻¹ ∈ A := by
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm hxH) b).mpr (hA hbA)
  exact ⟨A, hAT, hAel, hAmax, hAR⟩

private theorem W_eq_sup_centW (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {A : Subgroup G}
    (hAT : A ≤ D.T) (hAel : IsElemAbelian 2 A)
    (hAmax : Nat.card A = 2 ^ CFSG.Open.pRank 2 D.T)
    (hAR : ¬ A ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :
    CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) =
      c.V ⊔ (CFSG.RankThree.PartOne.omegaOneCenterIn
        (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓ Subgroup.centralizer (A : Set G)) := by
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  let Y : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G)
  obtain ⟨-, -, -, hrel⟩ := offender_chain D Ch h4 h23 h1930 c hAT hAel hAmax hAR
  have hVW : c.V ≤ W := V_le_omegaOneCenterIn D Ch h4 h23 h1930 c
  have hYeq : c.V ⊓ Y = c.V ⊓ Subgroup.centralizer (A : Set G) := by
    change c.V ⊓ (W ⊓ Subgroup.centralizer (A : Set G)) =
      c.V ⊓ Subgroup.centralizer (A : Set G)
    rw [← inf_assoc, inf_eq_left.mpr hVW]
  have h := CFSG.GroupTheory.eq_sup_of_relIndex_eq (H := W) (M := c.V) (B := Y)
    hVW inf_le_left (by rw [← Subgroup.inf_relIndex_left c.V Y, hYeq]; exact hrel.symm)
  simpa [Y] using h.symm

private theorem commutator_sup_le_of_le_centralizer
    {V W A : Subgroup G} (hWV : W ≤ Subgroup.centralizer (V : Set G))
    (hWA : W ≤ Subgroup.centralizer (A : Set G))
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V ⊔ W, A⁆ ≤ V := by
  have hWN : W ≤ Subgroup.normalizer (V : Set G) :=
    hWV.trans (Subgroup.centralizer_le_normalizer (V : Set G))
  refine Subgroup.commutator_le.mpr ?_
  rintro v hv a ha
  rw [sup_comm] at hv
  obtain ⟨w, hw, v', hv', rfl⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pws_exists_mul_of_mem_sup
      (H := W) (K := V) hWN hv
  have hwa : ⁅w, a⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hWA hw) a ha).symm
  have hva : ⁅v', a⁆ ∈ V := by
    rw [commutatorElement_def]
    have h1 : a * v'⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV ha) v'⁻¹).mp (V.inv_mem hv')
    have h1' : v' * (a * v'⁻¹ * a⁻¹) ∈ V := V.mul_mem hv' h1
    simpa [mul_assoc] using h1'
  rw [commutatorElement_mul_left_eq_conj_mul, hwa, mul_one]
  have hconj : w * ⁅v', a⁆ * w⁻¹ = ⁅v', a⁆ := by
    have hcomm := Subgroup.mem_centralizer_iff.mp (hWV hw) ⁅v', a⁆ hva
    rw [← hcomm]; group
  simpa [hconj] using hva

private theorem commutator_W_A_le (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {A : Subgroup G} (hAT : A ≤ D.T)
    (hVW : c.V ≤ CFSG.RankThree.PartOne.omegaOneCenterIn
      (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)))
    (hW : CFSG.RankThree.PartOne.omegaOneCenterIn
        (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) =
      c.V ⊔ (CFSG.RankThree.PartOne.omegaOneCenterIn
        (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓ Subgroup.centralizer (A : Set G))) :
    ⁅CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)), A⁆ ≤
      c.V := by
  rw [hW]
  change ⁅c.V ⊔ (CFSG.RankThree.PartOne.omegaOneCenterIn
      (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓ Subgroup.centralizer (A : Set G)), A⁆ ≤ c.V
  have hW_le_R : CFSG.RankThree.PartOne.omegaOneCenterIn
      (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le _
  have hY_cent : (CFSG.RankThree.PartOne.omegaOneCenterIn
      (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ⊓ Subgroup.centralizer (A : Set G)) ≤
      Subgroup.centralizer (c.V : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hy.1).2.1
      v (hW_le_R (hVW hv))
  have hAV : A ≤ Subgroup.normalizer (c.V : Set G) :=
    (hAT.trans le_sup_right).trans (c.sup_le_normalizer_V D Ch)
  exact commutator_sup_le_of_le_centralizer hY_cent inf_le_right hAV

private def commutatorKernel (V W H : Subgroup G)
    (hVH : H ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {g | g ∈ H ∧ ∀ w ∈ W, ⁅w, g⁆ ∈ V}
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    intro w _
    simp
  mul_mem' := by
    rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
    refine ⟨H.mul_mem haH hbH, fun w hw => ?_⟩
    rw [CFSG.commutator_mul_right]
    have h1 : ⁅w, a⁆ ∈ V := ha w hw
    have h2 : a * ⁅w, b⁆ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVH haH) ⁅w, b⁆).mp (hb w hw)
    have heq : ⁅w, a⁆ * a * ⁅w, b⁆ * a⁻¹ =
        ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by group
    rw [heq]
    exact V.mul_mem h1 h2
  inv_mem' := by
    rintro a ⟨haH, ha⟩
    refine ⟨H.inv_mem haH, fun w hw => ?_⟩
    rw [commutatorElement_inv_right]
    have haw : ⁅a, w⁆ = ⁅w, a⁆⁻¹ := (commutatorElement_inv w a).symm
    rw [haw]
    simpa using (Subgroup.mem_normalizer_iff.mp (hVH (H.inv_mem haH)) ⁅w, a⁆⁻¹).mp
      (V.inv_mem (ha w hw))

private theorem commutatorKernel_conj_mem (V W H : Subgroup G)
    (hVH : H ≤ Subgroup.normalizer (V : Set G))
    (hWH : H ≤ Subgroup.normalizer (W : Set G)) {n : G} (hn : n ∈ H) {k : G}
    (hk : k ∈ commutatorKernel V W H hVH) :
    n * k * n⁻¹ ∈ commutatorKernel V W H hVH := by
  refine ⟨H.mul_mem (H.mul_mem hn hk.1) (H.inv_mem hn), fun w hw => ?_⟩
  have hw' : n⁻¹ * w * n ∈ W := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hWH (H.inv_mem hn)) w).mp hw
  have hc := hk.2 (n⁻¹ * w * n) hw'
  have hval : ⁅w, n * k * n⁻¹⁆ = n * ⁅n⁻¹ * w * n, k⁆ * n⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [hval]
  exact (Subgroup.mem_normalizer_iff.mp (hVH hn) _).mp hc

private theorem pRank_pCoreOf_eq (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    CFSG.Open.pRank 2 (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) =
      CFSG.Open.pRank 2 D.T := by
  classical
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)
  have hRT : R ≤ D.T := pCoreOf_sup_le_T D Ch c
  have hmono : CFSG.Open.pRank 2 R ≤ CFSG.Open.pRank 2 D.T :=
    CFSG.SectionRank.pRank_mono (by norm_num : 1 < 2) hRT
  by_cases hex : ∃ A : Subgroup G, A ≤ D.T ∧ IsElemAbelian 2 A ∧
      Nat.card A = 2 ^ CFSG.Open.pRank 2 D.T ∧ ¬ A ≤ R
  · obtain ⟨A, hAT, hAel, hAmax, hAR⟩ := hex
    obtain ⟨hXel, hXR, hXcard, -⟩ := offender_chain D Ch h4 h23 h1930 c hAT hAel hAmax hAR
    have hge : CFSG.Open.pRank 2 D.T ≤ CFSG.Open.pRank 2 R :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hXR hXel
        (by rw [hXcard, hAmax])
    exact le_antisymm hmono hge
  · obtain ⟨A, hAT, hAel, hAmax⟩ :=
      CFSG.SectionRank.exists_pRank (p := 2) (by norm_num : 1 < 2) D.T
    have hAR : A ≤ R := by
      by_contra h
      exact hex ⟨A, hAT, hAel, hAmax, h⟩
    have hge : CFSG.Open.pRank 2 D.T ≤ CFSG.Open.pRank 2 R :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hAR hAel (by rw [hAmax])
    exact le_antisymm hmono hge

private theorem thompsonJ_pCoreOf_le (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    InS3.thompsonJ (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ≤ InS3.thompsonJ D.T :=
  InS3.thompsonJ_mono_of_pRank_eq (pCoreOf_sup_le_T D Ch c)
    (pRank_pCoreOf_eq D Ch h4 h23 h1930 c)

theorem omegaOneZJ_pCoreOf_le_and_V_le (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    InS3.omegaOneZJ (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ≤ InS3.thompsonJ D.T ∧
      c.V ≤ InS3.thompsonJ D.T := by
  have hJT := thompsonJ_pCoreOf_le D Ch h4 h23 h1930 c
  have hWJ := omegaOneCenterIn_le_thompsonJ D Ch c
  have hVW := V_le_omegaOneCenterIn D Ch h4 h23 h1930 c
  exact ⟨(InS3.omegaOneZJ_le_thompsonJ _).trans hJT, hVW.trans (hWJ.trans hJT)⟩

private theorem exists_mem_commutatorKernel_not_centralizer
    (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    (hker : κ.α.ker = (c.L ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf c.L)
    {A K : Subgroup G} (hAT : A ≤ D.T)
    (hAR : ¬ A ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))
    (hR_le_K : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ K) (hA_le_K : A ≤ K) :
    ∃ l0 : G, ∃ _ : l0 ∈ K, ∃ hl0L : l0 ∈ c.L, κ.α ⟨l0, hl0L⟩ ≠ 1 := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let C : Subgroup G := Subgroup.centralizer (c.V : Set G)
  have hRinf : R = H ⊓ C := (cent_sup_eq_pCoreOf D Ch h4 h23 h1930 c).symm
  obtain ⟨a0, ha0A, ha0R⟩ := Set.not_subset.mp hAR
  have ha0T : a0 ∈ D.T := hAT ha0A
  obtain ⟨l0, hl0, hc0⟩ :=
    exists_mem_T_inf_L_mul_inv_mem_centralizer D Ch h4 h23 h1930 c ha0T
  have hl0T : l0 ∈ D.T := (Subgroup.mem_inf.mp hl0).1
  have hl0L : l0 ∈ c.L := (Subgroup.mem_inf.mp hl0).2
  have hc0R : a0 * l0⁻¹ ∈ R := by
    rw [hRinf]
    exact ⟨Subgroup.mem_sup_right (D.T.mul_mem ha0T (D.T.inv_mem hl0T)), hc0⟩
  have hc0K : a0 * l0⁻¹ ∈ K := hR_le_K hc0R
  have ha0K : a0 ∈ K := hA_le_K ha0A
  have hl0K : l0 ∈ K := by
    have h : l0 = (a0 * l0⁻¹)⁻¹ * a0 := by group
    rw [h]
    exact K.mul_mem (K.inv_mem hc0K) ha0K
  have hαl0 : κ.α ⟨l0, hl0L⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨l0, hl0L⟩ : ↥c.L) ∈ κ.α.ker := MonoidHom.mem_ker.mpr h1
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
    apply ha0R
    have ha0_eq : a0 = (a0 * l0⁻¹) * l0 := by group
    change a0 ∈ R
    rw [ha0_eq, hRinf]
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_sup_right (D.T.mul_mem
        (D.T.mul_mem ha0T (D.T.inv_mem hl0T)) hl0T),
        (Subgroup.centralizer (c.V : Set G)).mul_mem hc0 hmem.2⟩
  exact ⟨l0, hl0K, hl0L, hαl0⟩

private theorem map_commutatorKernel_eq_top
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {K H : Subgroup G} (hLH : c.L ≤ H)
    (hKconj : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    {l0 : G} (hl0K : l0 ∈ K) (hl0L : l0 ∈ c.L)
    (hαl0 : κ.α ⟨l0, hl0L⟩ ≠ 1) (hcard4 : 4 ≤ Nat.card κ.K) :
    ((K ⊓ c.L).subgroupOf c.L).map κ.α = ⊤ := by
  classical
  let K' : Subgroup G := K ⊓ c.L
  have hK'_normal : (K'.subgroupOf c.L).Normal := by
    refine Subgroup.Normal.mk ?_
    intro x hx l
    have hxK' : (x : G) ∈ K' := Subgroup.mem_subgroupOf.mp hx
    have hxK : (x : G) ∈ K := hxK'.1
    have hxL : (x : G) ∈ c.L := hxK'.2
    refine Subgroup.mem_subgroupOf.mpr
      ⟨hKconj (l : G) (hLH l.2) (x : G) hxK, ?_⟩
    exact c.L.mul_mem (c.L.mul_mem l.2 hxL) (c.L.inv_mem l.2)
  have hmapNormal : ((K'.subgroupOf c.L).map κ.α).Normal :=
    hK'_normal.map κ.α κ.α_surj
  have hIm_ne_bot : (K'.subgroupOf c.L).map κ.α ≠ ⊥ := by
    intro hbot
    have hmem : κ.α ⟨l0, hl0L⟩ ∈ (K'.subgroupOf c.L).map κ.α :=
      Subgroup.mem_map.mpr ⟨⟨l0, hl0L⟩, Subgroup.mem_subgroupOf.mpr ⟨hl0K, hl0L⟩, rfl⟩
    rw [hbot] at hmem
    exact hαl0 (Subgroup.mem_bot.mp hmem)
  haveI : CharP κ.K 2 := κ.charP_two
  haveI hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) κ.K) :=
    CFSG.CGT.PushingUpLit.A78.isSimpleGroup_SL2_charTwo κ.K hcard4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((K'.subgroupOf c.L).map κ.α) with hbot | htop
  · exact absurd hbot hIm_ne_bot
  · exact htop

private theorem L_le_commutatorKernel_of_map_eq_top
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {K H : Subgroup G} (hLH : c.L ≤ H)
    (hker : κ.α.ker = (c.L ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf c.L)
    (hRinf : CFSG.Open.pCoreOf 2 H = H ⊓ Subgroup.centralizer (c.V : Set G))
    (hR_le_K : CFSG.Open.pCoreOf 2 H ≤ K)
    (htop : ((K ⊓ c.L).subgroupOf c.L).map κ.α = ⊤) :
    c.L ≤ K := by
  intro l hl
  let lL : ↥c.L := ⟨l, hl⟩
  have hmem : κ.α lL ∈ ((K ⊓ c.L).subgroupOf c.L).map κ.α := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkα⟩ := Subgroup.mem_map.mp hmem
  have hkK : (k : G) ∈ K := (Subgroup.mem_subgroupOf.mp hk).1
  have hlk_ker : κ.α (lL * k⁻¹) = 1 := by
    rw [map_mul, map_inv, hkα]
    group
  have hlk_mem : lL * k⁻¹ ∈ κ.α.ker := MonoidHom.mem_ker.mpr hlk_ker
  rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hlk_mem
  have hlk_R : ((lL * k⁻¹ : ↥c.L) : G) ∈ CFSG.Open.pCoreOf 2 H := by
    rw [hRinf]
    exact ⟨hLH (lL * k⁻¹).2, hlk_mem.2⟩
  have hlk_K : ((lL * k⁻¹ : ↥c.L) : G) ∈ K := hR_le_K hlk_R
  have heq : l = ((lL * k⁻¹ : ↥c.L) : G) * (k : G) := by
    change l = (l * (k : G)⁻¹) * (k : G)
    group
  rw [heq]
  exact K.mul_mem hlk_K hkK

private theorem commutator_L_W_eq_of_L_le_K
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)} {n : ℕ}
    (κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV n)
    {W H : Subgroup G}
    (hVH : H ≤ Subgroup.normalizer (c.V : Set G)) (hVW : c.V ≤ W)
    (hL_le_K : c.L ≤ commutatorKernel c.V W H hVH) :
    ⁅c.L, W⁆ = c.V := by
  have hWL : ⁅W, c.L⁆ ≤ c.V := by
    refine Subgroup.commutator_le.mpr ?_
    intro w hw l hl
    exact (hL_le_K hl).2 w hw
  have hLW_le : ⁅c.L, W⁆ ≤ c.V := by
    rw [Subgroup.commutator_comm]
    exact hWL
  have hV_le_LW : c.V ≤ ⁅c.L, W⁆ := by
    calc c.V = ⁅c.V, c.L⁆ := κ.commutator_eq.symm
      _ ≤ ⁅W, c.L⁆ := Subgroup.commutator_mono hVW le_rfl
      _ = ⁅c.L, W⁆ := Subgroup.commutator_comm W c.L
  exact le_antisymm hLW_le hV_le_LW

private theorem normalizer_omegaOneCenterIn_pCoreOf
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    c.L ⊔ D.T ≤ Subgroup.normalizer
      (CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) :
        Set G) := by
  have hHR : c.L ⊔ D.T ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (c.L ⊔ D.T)
  exact hHR.trans
    (CFSG.CGT.PushingUpLit.C2L.normalizer_le_normalizer_omegaOneCenterIn
      (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)))

private theorem pCoreOf_le_commutatorKernel
    (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (hVH : c.L ⊔ D.T ≤ Subgroup.normalizer (c.V : Set G)) :
    CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤
      commutatorKernel c.V (CFSG.RankThree.PartOne.omegaOneCenterIn
        (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))) (c.L ⊔ D.T) hVH := by
  intro r hr
  refine ⟨Subgroup.mem_sup_right (pCoreOf_sup_le_T D Ch c hr), fun w hw => ?_⟩
  have hwr : ⁅w, r⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hw).2.1
      r hr).symm
  rw [hwr]
  exact c.V.one_mem

theorem commutator_L_omegaOneCenterIn (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hLJ : c.L ≤ InS3.thompsonJ (c.L ⊔ D.T)) :
    ⁅c.L, CFSG.RankThree.PartOne.omegaOneCenterIn
      (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))⁆ = c.V := by
  classical
  let H : Subgroup G := c.L ⊔ D.T
  let R : Subgroup G := CFSG.Open.pCoreOf 2 H
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn R
  obtain ⟨A, hAT, hAel, hAmax, hAR⟩ :=
    exists_max_elemAbelian_in_T_not_le_pCoreOf D Ch h4 h23 h1930 c hLJ
  have hVW : c.V ≤ W := V_le_omegaOneCenterIn D Ch h4 h23 h1930 c
  have hW_eq : W = c.V ⊔ (W ⊓ Subgroup.centralizer (A : Set G)) :=
    W_eq_sup_centW D Ch h4 h23 h1930 c hAT hAel hAmax hAR
  have hWA : ⁅W, A⁆ ≤ c.V := commutator_W_A_le D Ch c hAT hVW hW_eq
  obtain ⟨hVκ, hLV, κ, hker, hcardK⟩ := c.exists_coordinates_V D Ch h4 h23 h1930
  have hVH : H ≤ Subgroup.normalizer (c.V : Set G) := c.sup_le_normalizer_V D Ch
  have hRinf : R = H ⊓ Subgroup.centralizer (c.V : Set G) :=
    (cent_sup_eq_pCoreOf D Ch h4 h23 h1930 c).symm
  have hWH : H ≤ Subgroup.normalizer (W : Set G) := by
    simpa [H, W, R] using normalizer_omegaOneCenterIn_pCoreOf D Ch c
  let K : Subgroup G := commutatorKernel c.V W H hVH
  have hKconj : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk =>
    commutatorKernel_conj_mem c.V W H hVH hWH hx hk
  have hR_le_K : R ≤ K := by
    simpa [H, W, R, K] using pCoreOf_le_commutatorKernel D Ch c hVH
  have hA_le_K : A ≤ K := by
    intro a ha
    refine ⟨hAT.trans le_sup_right ha, fun w hw => ?_⟩
    exact (Subgroup.commutator_le.mp hWA) w hw a ha
  obtain ⟨l0, hl0K, hl0L, hαl0⟩ :=
    exists_mem_commutatorKernel_not_centralizer D Ch h4 h23 h1930 c κ hker hAT hAR
      hR_le_K hA_le_K
  have hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z := two_le_pRank_Z D Ch h23 h1930 c
  have hcard4 : 4 ≤ Nat.card κ.K := by
    rw [hcardK]
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
  have htop := map_commutatorKernel_eq_top D Ch c κ le_sup_left hKconj hl0K hl0L hαl0 hcard4
  have hL_le_K : c.L ≤ K :=
    L_le_commutatorKernel_of_map_eq_top D Ch c κ le_sup_left hker hRinf hR_le_K htop
  exact commutator_L_W_eq_of_L_le_K D Ch c κ hVH hVW hL_le_K

end Ctx23L

theorem offenderV2329_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) : OffenderV2329 D Ch := by
  intro h1930 c
  have h := Ctx23L.omegaOneZJ_pCoreOf_le_and_V_le D Ch h4 h23 h1930 c
  refine ⟨h.1, h.2, ?_⟩
  intro hLJ
  exact Ctx23L.commutator_L_omegaOneCenterIn D Ch h4 h23 h1930 c hLJ

end CFSG.LocalAnalysis.UniquenessCase.UC22

end