module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFortyOneFrame
public import CFSG.Quasithin.Background.HL3WrA3
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup Matrix
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

private theorem mQuot_E_inf_centralizer_le {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    E3.mQuot c.E (c.E ⊓ Subgroup.centralizer (X.W : Set G)) ≤
      CFSG.Open.pRank 2 D.Z + 1 := by
  classical
  let C : Subgroup G := Subgroup.centralizer (X.W : Set G)
  change E3.mQuot c.E (c.E ⊓ C) ≤ CFSG.Open.pRank 2 D.Z + 1
  have hEp : IsPGroup 2 c.E := (c.isElemAbelian_E h4 h39 h1930).isPGroup
  have hFp : IsPGroup 2 X.F := hEp.to_le X.hFE
  have hmqF : E3.mQuot X.F (X.F ⊓ C) ≤ CFSG.Open.pRank 2 D.Z :=
    CFSG.Quasithin.H.L3Wr.mQuot_le_of_relIndex_le hFp
      (X.relIndex_centralizer_le h4 h23 h1930)
  have hrelEF : X.F.relIndex c.E ≤ 2 := by
    simpa [Subgroup.relIndex] using X.hFindex
  have hmqEF : E3.mQuot c.E X.F ≤ 1 :=
    CFSG.Quasithin.H.L3Wr.mQuot_le_of_relIndex_le hEp (k := 1) (by simpa using hrelEF)
  have hadd := E3.mQuot_add (V := c.E) (U := X.F ⊓ C) (U' := X.F) inf_le_left X.hFE
  calc E3.mQuot c.E (c.E ⊓ C) ≤ E3.mQuot c.E (X.F ⊓ C) :=
        E3.mQuot_mono (inf_le_inf_right C X.hFE)
    _ = E3.mQuot X.F (X.F ⊓ C) + E3.mQuot c.E X.F := hadd
    _ ≤ CFSG.Open.pRank 2 D.Z + 1 := Nat.add_le_add hmqF hmqEF

private theorem centralizer_inf_le_M {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h40 : S23_40 D Ch) (h1930 : H1930 D)
    {U : Subgroup G} (hUE : U ≤ c.E)
    (hmq : E3.mQuot c.E U ≤ CFSG.Open.pRank 2 D.Z + 1) :
    Subgroup.centralizer (U : Set G) ≤ D.M := by
  by_contra hcon
  have hmem : U ∈ {V : Subgroup G | V ≤ c.E ∧
      ¬ Subgroup.centralizer (V : Set G) ≤ D.M} := ⟨hUE, hcon⟩
  have hle : CFSG.LocalAnalysis.UniquenessCase.PartTwo.rMV D.M c.E ≤
      (E3.mQuot c.E U : ℕ∞) := by
    unfold CFSG.LocalAnalysis.UniquenessCase.PartTwo.rMV
    exact iInf₂_le U hmem
  have hle' : (E3.mQuot c.E U : ℕ∞) ≤
      ((CFSG.Open.pRank 2 D.Z + 1 : ℕ) : ℕ∞) := by exact_mod_cast hmq
  exact (not_lt_of_ge (hle.trans hle')) (h40 h1930 c)

theorem s2341_W_le_M {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) : X.W ≤ D.M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (X.W : Set G)
  let U : Subgroup G := c.E ⊓ C
  have hmq : E3.mQuot c.E U ≤ CFSG.Open.pRank 2 D.Z + 1 := by
    simpa [U] using mQuot_E_inf_centralizer_le X h4 h23 h39 h1930
  have hCU : Subgroup.centralizer (U : Set G) ≤ D.M :=
    centralizer_inf_le_M h40 h1930 inf_le_left hmq
  intro w hw
  apply hCU
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have huC : u ∈ C := hu.2
  exact (Subgroup.mem_centralizer_iff.mp huC w hw).symm

namespace S2341Frame

theorem le_normalizer_W {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    X.F ≤ Subgroup.normalizer (X.W : Set G) := by
  have hTN : D.T ≤ Subgroup.normalizer (c.V : Set G) := by
    rw [c.normalizer_V_eq h4 h1930]
    exact (le_sup_right : D.T ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c)
  have hconj := E3.conjSubgroup_mono_left X.h hTN
  rw [E3.conjSubgroup_normalizer, ← X.hW] at hconj
  exact X.hF.trans hconj

theorem card_Zh {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    Nat.card X.Zh = 2 ^ CFSG.Open.pRank 2 D.Z := by
  rw [X.hZh, E3.card_conjSubgroup]
  exact CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
    (c.isElemAbelian_Z h4 h1930)

theorem Zh_le_centralizer_F {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h1930 : H1930 D) :
    X.Zh ≤ Subgroup.centralizer (X.F : Set G) := by
  intro z hz
  rw [X.hZh] at hz
  have hz₀Z : X.h * z * X.h⁻¹ ∈ D.Z :=
    CFSG.Quasithin.mem_conjSubgroup_iff.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfT : X.h * f * X.h⁻¹ ∈ D.T :=
    CFSG.Quasithin.mem_conjSubgroup_iff.mp (X.hF hf)
  have hcent : (X.h * z * X.h⁻¹) * (X.h * f * X.h⁻¹) =
      (X.h * f * X.h⁻¹) * (X.h * z * X.h⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D hfT) _ hz₀Z
  calc f * z = X.h⁻¹ * ((X.h * f * X.h⁻¹) * (X.h * z * X.h⁻¹)) * X.h := by group
    _ = X.h⁻¹ * ((X.h * z * X.h⁻¹) * (X.h * f * X.h⁻¹)) * X.h := by rw [hcent]
    _ = z * f := by group

theorem Zh_le_W {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) : X.Zh ≤ X.W := by
  rw [X.hZh, X.hW]
  exact E3.conjSubgroup_mono_left X.h (uc22p22v_le_conjClosure c.N D.Z)

end S2341Frame

private theorem exists_not_mem_centralizer_of_comm_ne_bot {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    ∃ a ∈ X.F, a ∉ Subgroup.centralizer (X.W : Set G) := by
  by_contra h
  push Not at h
  apply hneq
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact h

private noncomputable def frameCommMap {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D) (a : G)
    (haF : a ∈ X.F) : ↥X.W →* ↥X.W :=
  CFSG.RankThree.PartTwo.Sec19.SolEven.H2.commMap X.W
    (fun x hx y hy => (X.isElemAbelian_W h4 h1930).comm hx hy) a
    (fun w hw => (Subgroup.mem_normalizer_iff.mp
      (X.le_normalizer_W h4 h1930 haF) w).mp hw)

private theorem frameCommMap_ker_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {a : G} (haF : a ∈ X.F) (haC : a ∉ Subgroup.centralizer (X.W : Set G)) :
    (frameCommMap X h4 h1930 a haF).ker = X.Zh.subgroupOf X.W := by
  have hker : (frameCommMap X h4 h1930 a haF).ker =
      (X.W ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf X.W := by
    ext w
    unfold frameCommMap
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      CFSG.RankThree.PartTwo.Sec19.SolEven.H2.mem_ker_commMap,
      Subgroup.mem_centralizer_singleton_iff]
    simp
  rw [hker, X.centralizer_eq h4 h23 h1930 haF haC]

private theorem frameCommMap_range_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {a : G} (haF : a ∈ X.F) (haC : a ∉ Subgroup.centralizer (X.W : Set G)) :
    (frameCommMap X h4 h1930 a haF).range = X.Zh.subgroupOf X.W := by
  classical
  let φ := frameCommMap X h4 h1930 a haF
  change φ.range = X.Zh.subgroupOf X.W
  have hker : φ.ker = X.Zh.subgroupOf X.W :=
    frameCommMap_ker_eq X h4 h23 h1930 haF haC
  have hcardZhW : Nat.card ↥(X.Zh.subgroupOf X.W) =
      2 ^ CFSG.Open.pRank 2 D.Z := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (X.Zh_le_W)).toEquiv]
    exact X.card_Zh h4 h1930
  have hcardker : Nat.card ↥φ.ker = 2 ^ CFSG.Open.pRank 2 D.Z := by
    rw [hker]
    exact hcardZhW
  have hrange_le_Zh : φ.range ≤ X.Zh.subgroupOf X.W := by
    rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    change a * (w : G) * a⁻¹ * (w : G)⁻¹ ∈ X.Zh
    exact X.commutator_mem h4 h23 h1930 haF w.2
  have hcardRange : Nat.card ↥φ.range = 2 ^ CFSG.Open.pRank 2 D.Z := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hcardker, X.card_W h4 h23 h1930] at hmul
    have hqpos : 0 < 2 ^ CFSG.Open.pRank 2 D.Z := pow_pos (by norm_num) _
    have hsquare : 2 ^ CFSG.Open.pRank 2 D.Z * 2 ^ CFSG.Open.pRank 2 D.Z =
        (2 ^ CFSG.Open.pRank 2 D.Z) ^ 2 := by ring
    rw [← hsquare] at hmul
    exact Nat.eq_of_mul_eq_mul_left hqpos hmul
  exact Subgroup.eq_of_le_of_card_ge hrange_le_Zh (by rw [hcardRange, hcardZhW])

private theorem Zh_le_commutator {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {a : G} (haF : a ∈ X.F) (haC : a ∉ Subgroup.centralizer (X.W : Set G)) :
    X.Zh ≤ ⁅X.F, X.W⁆ := by
  have hrange_eq := frameCommMap_range_eq X h4 h23 h1930 haF haC
  have hrange_le_comm : (frameCommMap X h4 h1930 a haF).range ≤
      (⁅X.F, X.W⁆).subgroupOf X.W := by
    rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    change a * (w : G) * a⁻¹ * (w : G)⁻¹ ∈ ⁅X.F, X.W⁆
    exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr haF) le_rfl
      (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a) w.2)
  intro z hz
  have hzW : z ∈ X.W := X.Zh_le_W hz
  have hmem : (⟨z, hzW⟩ : ↥X.W) ∈ (frameCommMap X h4 h1930 a haF).range := by
    rw [hrange_eq]
    exact hz
  exact Subgroup.mem_subgroupOf.mp (hrange_le_comm hmem)

private theorem inf_centralizer_F_eq_Zh {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    X.W ⊓ Subgroup.centralizer (X.F : Set G) = X.Zh := by
  obtain ⟨a, haF, haC⟩ := exists_not_mem_centralizer_of_comm_ne_bot X hneq
  have hle : (X.W ⊓ Subgroup.centralizer (X.F : Set G)).subgroupOf X.W ≤
      (X.W ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf X.W :=
    Subgroup.subgroupOf_mono X.W
      (inf_le_inf_left _ (Subgroup.centralizer_le (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact haF)))
  have hle' : (X.W ⊓ Subgroup.centralizer (X.F : Set G)).subgroupOf X.W ≤
      X.Zh.subgroupOf X.W := by
    rwa [X.centralizer_eq h4 h23 h1930 haF haC] at hle
  refine le_antisymm ?_ (le_inf X.Zh_le_W (X.Zh_le_centralizer_F h1930))
  intro x hx
  exact hle' (show (⟨x, hx.1⟩ : ↥X.W) ∈
    (X.W ⊓ Subgroup.centralizer (X.F : Set G)).subgroupOf X.W from hx)

theorem s2341_comm_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    ⁅X.W, X.F⁆ = X.Zh ∧ X.W ⊓ Subgroup.centralizer (X.F : Set G) = X.Zh ∧
      X.Zh ≤ c.E := by
  classical
  have hcomm_le : ⁅X.W, X.F⁆ ≤ X.Zh := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_le.mpr fun f hf w hw =>
      X.commutator_mem h4 h23 h1930 hf hw
  obtain ⟨a, haF, haC⟩ := exists_not_mem_centralizer_of_comm_ne_bot X hneq
  have hZh_le : X.Zh ≤ ⁅X.F, X.W⁆ := Zh_le_commutator X h4 h23 h1930 haF haC
  have hcomm_eq : ⁅X.W, X.F⁆ = X.Zh := by
    have h' : ⁅X.F, X.W⁆ ≤ X.Zh := by
      rwa [Subgroup.commutator_comm] at hcomm_le
    rw [Subgroup.commutator_comm]
    exact le_antisymm h' hZh_le
  have hCWF_eq := inf_centralizer_F_eq_Zh X h4 h23 h1930 hneq
  have hW_le_M := s2341_W_le_M X h4 h23 h39 h40 h1930
  have hWE : X.W ≤ Subgroup.normalizer (c.E : Set G) := by
    rw [c.normalizer_E_eq h4 h39 h1930]
    exact hW_le_M
  have hcomm_le_E : ⁅X.W, X.F⁆ ≤ c.E := by
    rw [Subgroup.commutator_le]
    intro w hw f hf
    have hfE : f ∈ c.E := X.hFE hf
    exact c.E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWE hw) f).mp hfE)
      (c.E.inv_mem hfE)
  exact ⟨hcomm_eq, hCWF_eq, hcomm_eq ▸ hcomm_le_E⟩

private theorem not_Zh_eq_Z {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) (hEq : X.Zh = D.Z) : False := by
  apply hneq
  rw [X.hZh] at hEq
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← (h4 h1930 c).1]
    exact D.normalizer_U_eq
  have hhM : X.h ∈ D.M := by
    rw [← hNZ]
    exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hEq
  have hNE : D.M ≤ Subgroup.normalizer (c.E : Set G) := by
    rw [c.normalizer_E_eq h4 h39 h1930]
  have hEeq : conjSubgroup c.E X.h = c.E :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr (hNE hhM)
  have hWleE : X.W ≤ c.E := by
    rw [X.hW]
    calc conjSubgroup c.V X.h ≤ conjSubgroup c.E X.h :=
          E3.conjSubgroup_mono_left X.h (uc22p22v_le_conjClosure D.M c.V)
      _ = c.E := hEeq
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro w hw f hf
  rw [Subgroup.mem_bot]
  have hcw : w * f = f * w :=
    congrArg Subtype.val ((c.isMulCommutative_E h39 h1930).is_comm.comm
      ⟨w, hWleE hw⟩ ⟨f, X.hFE hf⟩)
  change w * f * w⁻¹ * f⁻¹ = 1
  rw [hcw]
  group

theorem s2341_Z_inf {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) : D.Z ⊓ X.Zh = ⊥ := by
  by_cases hEq : X.Zh = D.Z
  · exact (not_Zh_eq_Z X h4 h39 h1930 hneq hEq).elim
  · rcases c.Z_right_TI h4 h1930 X.h with h | h
    · rw [X.hZh]
      exact h
    · exfalso
      exact hEq (by rw [X.hZh]; exact h)

private theorem W_le_conjSubgroup_E {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) : X.W ≤ conjSubgroup c.E X.h := by
  rw [X.hW]
  exact E3.conjSubgroup_mono_left X.h (uc22p22v_le_conjClosure D.M c.V)

private theorem E_le_conjSubgroup_M {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    c.E ≤ conjSubgroup D.M X.h := by
  have hZhE : X.Zh ≤ c.E := (s2341_comm_eq X h4 h23 h39 h40 h1930 hneq).2.2
  have hZhbot : X.Zh ≠ ⊥ := by
    rw [X.hZh]
    exact fun h => uc22main1_Z_ne_bot D
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSubgroup_eq_bot_iff.mp h)
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZhbot
  have hzZ : (z : G) ∈ X.Zh := z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hEcomm := c.isMulCommutative_E h39 h1930
  have hEcent : c.E ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hEcomm.is_comm.comm ⟨e, he⟩ ⟨(z : G), hZhE hzZ⟩)
  exact hEcent.trans (X.centralizer_le h4 h1930 hzZ hz1')

private theorem commutator_E_W_le_inf {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    ⁅c.E, X.W⁆ ≤ c.E ⊓ conjSubgroup c.E X.h := by
  have hE_le_Mh := E_le_conjSubgroup_M X h4 h23 h39 h40 h1930 hneq
  have hW_le_Eh := W_le_conjSubgroup_E X
  have hW_le_M := s2341_W_le_M X h4 h23 h39 h40 h1930
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm, Subgroup.commutator_le]
    intro w hw e he
    have hWE : X.W ≤ Subgroup.normalizer (c.E : Set G) := by
      rw [c.normalizer_E_eq h4 h39 h1930]
      exact hW_le_M
    exact c.E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWE hw) e).mp he)
      (c.E.inv_mem he)
  · rw [Subgroup.commutator_le]
    intro e he w hw
    have hMh_le : conjSubgroup D.M X.h ≤
        Subgroup.normalizer (conjSubgroup c.E X.h : Set G) := by
      have hNE : D.M ≤ Subgroup.normalizer (c.E : Set G) := by
        rw [c.normalizer_E_eq h4 h39 h1930]
      have := E3.conjSubgroup_mono_left X.h hNE
      rwa [E3.conjSubgroup_normalizer] at this
    have hE_norm : c.E ≤ Subgroup.normalizer (conjSubgroup c.E X.h : Set G) :=
      hE_le_Mh.trans hMh_le
    exact (conjSubgroup c.E X.h).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hE_norm he) w).mp (hW_le_Eh hw))
      ((conjSubgroup c.E X.h).inv_mem (hW_le_Eh hw))

private theorem commutator_commutator_E_W_eq_bot {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h39 : S23_39 D Ch) (h40 : S23_40 D Ch) (h1930 : H1930 D)
    (hneq : ⁅X.W, X.F⁆ ≠ ⊥) : ⁅⁅c.E, X.W⁆, X.W⁆ = ⊥ := by
  have hcomm_le_inf := commutator_E_W_le_inf X h4 h23 h39 h40 h1930 hneq
  have hW_le_Eh := W_le_conjSubgroup_E X
  haveI : IsMulCommutative ↥c.E := c.isMulCommutative_E h39 h1930
  have hEh_comm : IsMulCommutative ↥(conjSubgroup c.E X.h) :=
    Subgroup.map_isMulCommutative (H := c.E) (MulAut.conj X.h⁻¹).toMonoidHom
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha w hw
  rw [Subgroup.mem_bot]
  have haEh : a ∈ conjSubgroup c.E X.h := (Subgroup.mem_inf.mp (hcomm_le_inf ha)).2
  have hwEh : w ∈ conjSubgroup c.E X.h := hW_le_Eh hw
  have haw : a * w = w * a :=
    congrArg Subtype.val (hEh_comm.is_comm.comm ⟨a, haEh⟩ ⟨w, hwEh⟩)
  change a * w * a⁻¹ * w⁻¹ = 1
  rw [haw]
  group

theorem s2341_quadratic {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    ⁅⁅c.E, X.W⁆, X.W⁆ = ⊥ := by
  exact commutator_commutator_E_W_eq_bot X h4 h23 h39 h40 h1930 hneq

private theorem Zh_le_centModE {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    X.Zh ≤ centModE D Ch c := by
  have hZhE : X.Zh ≤ c.E := (s2341_comm_eq X h4 h23 h39 h40 h1930 hneq).2.2
  have hW_le_M := s2341_W_le_M X h4 h23 h39 h40 h1930
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]
    exact (h4 h1930 c).2.2
  intro z hz
  refine ⟨hW_le_M (X.Zh_le_W hz), hMZ (hW_le_M (X.Zh_le_W hz)), ?_⟩
  intro e he
  have hze : z * e = e * z :=
    congrArg Subtype.val ((c.isMulCommutative_E h39 h1930).is_comm.comm
      ⟨z, hZhE hz⟩ ⟨e, he⟩)
  have h1 : z * e * z⁻¹ * e⁻¹ = 1 := by rw [hze]; group
  rw [h1]
  exact D.Z.one_mem

private theorem pCoreOf_le_centModE {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    CFSG.Open.pCoreOf 2 D.M ≤ centModE D Ch c := by
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]
    exact (h4 h1930 c).2.2
  intro m hm
  refine ⟨CFSG.openPCoreOf_le 2 D.M hm, hMZ (CFSG.openPCoreOf_le 2 D.M hm), ?_⟩
  intro e he
  have hmem : ⁅e, m⁆ ∈ D.Z :=
    (h39 h1930 c).2.2.1 (Subgroup.commutator_mem_commutator he hm)
  have hinv := D.Z.inv_mem hmem
  have h1 : ⁅e, m⁆⁻¹ = m * e * m⁻¹ * e⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h1] at hinv

private theorem inf_centModE_le_Zh {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    X.W ⊓ centModE D Ch c ≤ X.Zh := by
  intro w hw
  have hwC : w ∈ X.W ⊓ Subgroup.centralizer (X.F : Set G) := by
    refine ⟨hw.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro f hf
    have hZ : w * f * w⁻¹ * f⁻¹ ∈ D.Z := hw.2.2.2 f (X.hFE hf)
    have hZh' : f * w * f⁻¹ * w⁻¹ ∈ X.Zh :=
      X.commutator_mem h4 h23 h1930 hf hw.1
    have hZh : w * f * w⁻¹ * f⁻¹ ∈ X.Zh := by
      have := X.Zh.inv_mem hZh'
      rwa [show (f * w * f⁻¹ * w⁻¹)⁻¹ = w * f * w⁻¹ * f⁻¹ by group] at this
    have hbot : w * f * w⁻¹ * f⁻¹ = 1 := by
      have hmem : w * f * w⁻¹ * f⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← s2341_Z_inf X h4 h39 h1930 hneq]
        exact ⟨hZ, hZh⟩
      rwa [Subgroup.mem_bot] at hmem
    have h1 : w * f * w⁻¹ = f := mul_inv_eq_one.mp hbot
    calc f * w = (w * f * w⁻¹) * w := by rw [h1]
      _ = w * f := by group
  rw [← inf_centralizer_F_eq_Zh X h4 h23 h1930 hneq]
  exact hwC

theorem s2341_W_inf_O2 {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h40 : S23_40 D Ch) (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) :
    X.W ⊓ centModE D Ch c = X.Zh ∧
      X.W ⊓ CFSG.Open.pCoreOf 2 D.M = X.Zh := by
  have hcomm := s2341_comm_eq X h4 h23 h39 h40 h1930 hneq
  have hZhW : X.Zh ≤ X.W := X.Zh_le_W
  have hZhE : X.Zh ≤ c.E := hcomm.2.2
  have hZh_le_O2 : X.Zh ≤ CFSG.Open.pCoreOf 2 D.M :=
    hZhE.trans (c.E_le_pCoreOf_M h39 h1930)
  have hZh_le_cent : X.Zh ≤ centModE D Ch c :=
    Zh_le_centModE X h4 h23 h39 h40 h1930 hneq
  have hO2_le_cent := pCoreOf_le_centModE (D := D) (Ch := Ch) (c := c) h4 h39 h1930
  have hEqCent : X.W ⊓ centModE D Ch c = X.Zh :=
    le_antisymm (inf_centModE_le_Zh X h4 h23 h39 h1930 hneq) (le_inf hZhW hZh_le_cent)
  refine ⟨hEqCent, le_antisymm ?_ (le_inf hZhW hZh_le_O2)⟩
  exact (inf_le_inf_left X.W hO2_le_cent).trans hEqCent.le

theorem s2341_P {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h39 : S23_39 D Ch)
    (h1930 : H1930 D) (hneq : ⁅X.W, X.F⁆ ≠ ⊥) {w f : G}
    (hwW : w ∈ X.W) (hwZh : w ∉ X.Zh) (hfF : f ∈ X.F)
    (hcommZ : w * f * w⁻¹ * f⁻¹ ∈ D.Z) :
    f ∈ X.F ⊓ Subgroup.centralizer (X.W : Set G) := by
  have hZh' : f * w * f⁻¹ * w⁻¹ ∈ X.Zh :=
    X.commutator_mem h4 h23 h1930 hfF hwW
  have hZh : w * f * w⁻¹ * f⁻¹ ∈ X.Zh := by
    have := X.Zh.inv_mem hZh'
    rwa [show (f * w * f⁻¹ * w⁻¹)⁻¹ = w * f * w⁻¹ * f⁻¹ by group] at this
  have hbot : w * f * w⁻¹ * f⁻¹ = 1 := by
    have hmem : w * f * w⁻¹ * f⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← s2341_Z_inf X h4 h39 h1930 hneq]
      exact ⟨hcommZ, hZh⟩
    rwa [Subgroup.mem_bot] at hmem
  by_contra hfC
  have hfCW : f ∉ Subgroup.centralizer (X.W : Set G) := by
    intro hfw
    exact hfC ⟨hfF, hfw⟩
  have hwf : w * f = f * w := by
    have h1 : w * f * w⁻¹ = f := mul_inv_eq_one.mp hbot
    calc w * f = (w * f * w⁻¹) * w := by group
      _ = f * w := by rw [h1]
  have hwC : w ∈ X.W ⊓ Subgroup.centralizer ({f} : Set G) :=
    ⟨hwW, Subgroup.mem_centralizer_singleton_iff.mpr hwf⟩
  rw [X.centralizer_eq h4 h23 h1930 hfF hfCW] at hwC
  exact hwZh hwC

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
