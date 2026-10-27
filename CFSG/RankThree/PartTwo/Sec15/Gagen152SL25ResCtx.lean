module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Conf
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step152SL25OneOmegaResR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
      omegaA A = {Subgroup.zpowers b} →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → P ≤ Subgroup.centralizer ({e} : Set G) →
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) = ⊥ → False

namespace Gagen152SL25Res

variable {G : Type} [Group G] [Finite G]

structure ResCtx (A : Subgroup G) (c : G) (L M X B : Subgroup G) (b d : G) (Lb : Subgroup G)
    (p : ℕ) (P : Subgroup G) (e : G) : Prop where
  sec15R : Sec15R G A c L
  allHJ : AllPointsHJ A
  ctx : Ctx152J A (lB A) M X
  hyp : IsHyperplane A B
  config : IsLBConfig A B b d Lb
  cent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G)
  omega : omegaA A = {Subgroup.zpowers b}
  pdata : PData152 A X p P
  three_lt : 3 < p
  fr : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype
  mem_e : e ∈ B
  not_mem_e : e ∉ Subgroup.zpowers b
  le_centralizer_e : P ≤ Subgroup.centralizer ({e} : Set G)

theorem exists_resCtx
    (h142 : Item142AllS14) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hHJ : AllPointsHJ A) {M X : Subgroup G} (hctx : Ctx152J A (lB A) M X)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (B : Set G))
    (hΩ : omegaA A = {Subgroup.zpowers b}) :
    ∃ (p : ℕ) (P : Subgroup G) (e : G), ResCtx A c L M X B b d Lb p P e := by
  have hA := h.isE27
  obtain ⟨p, P, hP, hp3⟩ := Ronan152SL25.exists_pData152J h.toTheoremFourHyp hctx hA.isPGroup
  have hp3' : p ≠ 3 := by omega
  have hfr :=
    Ronan152SL25.inf_centralizer_le_frattini_of_lbConfig h142 h.toSec14Std hctx hB hc hcent hP hp3'
  obtain ⟨-, -, -, -, hbA, hb1, hdA, -, -, hdb⟩ := Ronan152SL25.lbConfig_facts hA hB hc
  have hcent' : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {b, d} : Set G) := by rw [hcent, hc.1]
  obtain ⟨e, heB, heb, hPe⟩ :=
    Ronan152SL25.exists_le_centralizerJ hA hctx hbA hdA hb1 hdb hcent' hP hp3' hfr
  refine ⟨p, P, e, ?_⟩
  exact ⟨h, hHJ, hctx, hB, hc, hcent, hΩ, hP, hp3, hfr, hc.1 ▸ heB, heb, hPe⟩

variable {A : Subgroup G} {c : G} {L M X B : Subgroup G} {b d : G} {Lb : Subgroup G} {p : ℕ}
  {P : Subgroup G} {e : G}

theorem ResCtx.mem_A (h : ResCtx A c L M X B b d Lb p P e) : e ∈ A :=
  h.hyp.1 h.mem_e

theorem ResCtx.ne_one (h : ResCtx A c L M X B b d Lb p P e) : e ≠ 1 := by
  intro h1
  apply h.not_mem_e
  rw [h1]
  exact Subgroup.one_mem _

theorem ResCtx.not_mem_omegaA (h : ResCtx A c L M X B b d Lb p P e) :
    Subgroup.zpowers e ∉ omegaA A := by
  intro he
  rw [h.omega, Set.mem_singleton_iff] at he
  have hmem : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
  rw [he] at hmem
  exact h.not_mem_e hmem

theorem ResCtx.le_centralizer_A (h : ResCtx A c L M X B b d Lb p P e) :
    A ≤ Subgroup.centralizer ({e} : Set G) := by
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (h.sec15R.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨e, h.mem_A⟩))

theorem ResCtx.mem_thetaQuotCentralizer (h : ResCtx A c L M X B b d Lb p P e) :
    e ∈ Sec4.thetaQuotCentralizer X := by
  refine Proof152F.mem_thetaQuotCentralizer_of_mem h.ctx.norm_x ?_
  rw [h.cent]
  exact h.mem_e

theorem ResCtx.lB_le_centralizer (h : ResCtx A c L M X B b d Lb p P e) :
    lB A B ≤ Subgroup.centralizer ({e} : Set G) :=
  (Sec14.lB_le_centralizer A B).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.mem_e))

theorem ResCtx.lB_le
    (h : ResCtx A c L M X B b d Lb p P e) :
    lB A B ≤ Lb ⊓ Subgroup.centralizer ({d} : Set G) := by
  rw [Item148HJ.lB_eq_residual h.sec15R.toSec14Std h.hyp h.config]
  exact le_inf (Item148HJ.residual_le Lb d)
    (Item148HJ.residual_le_centralizer_singleton Lb d)

theorem ResCtx.A_le_normalizer_lB
    (h : ResCtx A c L M X B b d Lb p P e) :
    A ≤ Subgroup.normalizer (lB A B : Set G) := by
  have hdB : d ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdA : d ∈ A := h.hyp.1 hdB
  have hSb : Sec14Std G A b Lb := Item148HJ.sec14Std_of_isLBConfig h.sec15R.toSec14Std h.config
  have hNLb : A ≤ Subgroup.normalizer (Lb : Set G) := hSb.toSec13Data.le_normalizer
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.sec15R.toSec13Data.commute ha hdA)
  have hNCd : A ≤ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
    hAd.trans Subgroup.le_normalizer
  have hNinf : A ≤ Subgroup.normalizer
      ((Lb ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
    (le_inf hNLb hNCd).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hNres : A ≤ Subgroup.normalizer
      (inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) :=
    hNinf.trans (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _)
  rw [Item148HJ.lB_eq_residual h.sec15R.toSec14Std h.hyp h.config]
  exact hNres

theorem ResCtx.le_lB
    (h : ResCtx A c L M X B b d Lb p P e) {D : Subgroup G}
    (hD : D ≤ Lb ⊓ Subgroup.centralizer ({d} : Set G)) (hDp : Group.IsPerfect D) :
    D ≤ lB A B :=
  (Sec6.le_inSubgroup_perfectResidual_of_isPerfect hDp hD).trans
    (Item148HJ.residual_le_lB h.config)

end Gagen152SL25Res


end CFSG.RankThree.PartTwo.Sec15
