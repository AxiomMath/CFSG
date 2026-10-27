module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneGamma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.GroupTheory.StronglyPEmbeddedRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_seven_uniqueMax_of_mem_V₀ (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h3 : R19_3At D V₀ V p L K h)
    (h61 : UC6.R6_1 D) {w : G} (hw : w ∈ V₀) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hcent : L ⊔ K ≤ centralizer (V₀ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
  have hLK : L ⊔ K ≤ D.M ⊓ centralizer ({w} : Set G) := by
    refine le_inf (sup_le hLM hKM) fun y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy' : y ∈ centralizer (V₀ : Set G) := hcent hy
    exact (Subgroup.mem_centralizer_iff.1 hy' w hw).symm
  have h2 : 2 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({w} : Set G)) :=
    (nineteen_seven_two_le_pRank_sup D h).trans
      (CFSG.SectionRank.pRank_mono (p := 5) (by norm_num) hLK)
  exact s16c34_uniqueMax_of_pRank D h61 (h.p_eq ▸ h.hyp.hp) inf_le_left h2

theorem nineteen_seven_one_le_pRank_centralizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h3 : R19_3At D V₀ V p L K h)
    (h5 : R19_5At D V₀ V p L K h) (hC : 5 ∣ Nat.card (F11.CTilde D.M V₀ V)) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1
  by_cases hv0 : v ∈ V₀
  · exact s19_one_le_pRank_of_mem_V0 D h h3 hv0 hv1
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hCT_le : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ v :=
    iInf_le_of_le v (iInf_le_of_le hv le_rfl)
  have h5E : 5 ∣ Nat.card (F11.CElt D.M V₀ v) :=
    hC.trans (Subgroup.card_dvd_of_le hCT_le)
  have h5H : 5 ∣ Nat.card ↥(centModInM D V₀ v) := by
    rwa [← cElt_eq_centModInM D V₀ v]
  obtain ⟨Q, hQ⟩ := h5 v hv hv0
  have hQdvd : 5 ∣ Nat.card ↥Q := Q.pow_dvd_card_of_pow_dvd_card (n := 1) h5H
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 5 hQdvd
  let x : ↥(centModInM D V₀ v) := q.1
  have hxord : orderOf ((x : ↥(centModInM D V₀ v)) : G) = 5 := by
    rw [Subgroup.orderOf_coe x]
    exact (Subgroup.orderOf_coe q).trans hq
  have hxC : ((x : ↥(centModInM D V₀ v)) : G) ∈ Subgroup.centralizer ({v} : Set G) :=
    hQ (Subgroup.mem_map_of_mem (centModInM D V₀ v).subtype q.2)
  have hxM : ((x : ↥(centModInM D V₀ v)) : G) ∈ D.M := x.2.1
  have hmem : ((x : ↥(centModInM D V₀ v)) : G) ∈ D.M ⊓ centralizer ({v} : Set G) :=
    ⟨hxM, hxC⟩
  refine CFSG.SectionRank.le_pRank (p := 5)
    (H := D.M ⊓ centralizer ({v} : Set G))
    (E := Subgroup.zpowers ((x : ↥(centModInM D V₀ v)) : G)) (by norm_num)
    (Subgroup.zpowers_le.2 hmem) (CFSG.Open.isElemAbelian_zpowers (p := 5) ?_) ?_
  · rw [← hxord]
    exact pow_orderOf_eq_one _
  · rw [Nat.card_zpowers, hxord, pow_one]

theorem nineteen_seven_conj_inf_eq_bot (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {U V : Subgroup G} {p : ℕ} (hp : p ∈ D.sig)
    (hcent : ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)))
    (hU : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ D.M) :
    ∀ g : G, g ∉ D.M → conjSubgroup U g ⊓ V = ⊥ := by
  intro g hg
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    hSg.sig1_sp p (h1219 ▸ hp)
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  obtain ⟨hwU, hwV⟩ := Subgroup.mem_inf.1 hw
  have hu : g * w * g⁻¹ ∈ U := mem_conjSubgroup_iff.mp hwU
  have hu1 : g * w * g⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [e, h1]
    group
  have hcentu : centralizer ({g * w * g⁻¹} : Set G) ≤ D.M := hU _ hu hu1
  have hcentw : centralizer ({w} : Set G) ≤ conjSubgroup D.M g := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    apply hcentu
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hx]
      _ = (g * w * g⁻¹) * (g * x * g⁻¹) := by group
  have hpos : 0 < CFSG.Open.pRank p (D.M ⊓ centralizer ({w} : Set G)) := by
    have := hcent w hwV hw1
    omega
  exact hg (CFSG.GroupTheory.mem_of_pRank_pos_of_le_inf_conjSubgroup (D.sig_prime p hp).1 hsp
    (inf_le_inf_left _ hcentw) hpos)

theorem nineteen_seven_noncyclic_cent_of_index (D : Data G) {q : ℕ} (hq : q.Prime)
    {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hP : PairFacts D.M V₀ V) (x : IntMod V hV)
    (hidx : ¬ q ∣ ((D.M ⊓ centralizer ({x.val} : Set G)).subgroupOf
      (F11.CElt D.M V₀ x.val)).index)
    {P₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hP₀ : P₀ ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)) (hperf : Group.IsPerfect P₀)
    (hqP₀ : q ∣ Nat.card P₀) (hqC : q ∣ Nat.card (F11.CTilde D.M V₀ V)) :
    ∃ X : Subgroup G, X ≤ D.M ⊓ centralizer ({x.val} : Set G) ∧ IsPGroup q X ∧
      ¬ IsCyclic X := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hCs : F11.CElt D.M V₀ x.val ≤ stabTil V₀ V := fun c hc =>
    ⟨hP.le_normalizer hc.1, hc.2.1⟩
  let f : ↥(F11.CElt D.M V₀ x.val) →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hCs)
  have hfmem : ∀ c : ↥(F11.CElt D.M V₀ x.val),
      f c ∈ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    intro c
    refine Subgroup.mem_inf.2 ⟨actTil_mem_barSub V₀ V hV c.2.1 (hCs c.2), ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    show actTil V₀ V hV ⟨c, hCs c.2⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    exact c.2.2.2
  let g : ↥(F11.CElt D.M V₀ x.val) →* ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)) :=
    f.codRestrict _ hfmem
  have hg : Function.Surjective g := by
    rintro ⟨φ, hφ⟩
    obtain ⟨hφM, hφst⟩ := Subgroup.mem_inf.1 hφ
    obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφM
    have hfix : actTil V₀ V hV m (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
      MulAction.mem_stabilizer_iff.1 hφst
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
    exact ⟨⟨(m : G), hmM, stabTil_le_normalizer₀ V₀ V m.2, hfix⟩, Subtype.ext rfl⟩
  have hCT_le : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ x.val :=
    iInf_le_of_le x.val (iInf_le_of_le x.val_mem le_rfl)
  have hker_eq : g.ker =
      (F11.CTilde D.M V₀ V).subgroupOf (F11.CElt D.M V₀ x.val) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hP.le_normalizer]
    constructor
    · intro hc
      refine ⟨c.2.1, hCs c.2, ?_⟩
      change f c = 1
      exact congrArg Subtype.val hc
    · rintro ⟨-, h, h1⟩
      apply Subtype.ext
      change actTil V₀ V hV (Subgroup.inclusion hCs c) = 1
      rw [show actTil V₀ V hV (Subgroup.inclusion hCs c) =
          actTil V₀ V hV ⟨(c : G), h⟩ from
        congrArg (actTil V₀ V hV) (Subtype.ext rfl), h1]
  have hqker' : q ∣ Nat.card g.ker := by
    have hcard : Nat.card g.ker = Nat.card (F11.CTilde D.M V₀ V) := by
      rw [hker_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT_le).toEquiv
    rw [hcard]
    exact hqC
  haveI : Group.IsPerfect ↥P₀ := hperf
  have hperf' : Group.IsPerfect ↥(P₀.subgroupOf
      (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hP₀).symm.toMonoidHom) (MulEquiv.surjective _)
  have hcardP : Nat.card ↥(P₀.subgroupOf
      (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀).toEquiv
  have hqP₀' : q ∣ Nat.card ↥(P₀.subgroupOf
      (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) := hcardP.symm ▸ hqP₀
  obtain ⟨X₀, hX₀p, hX₀c⟩ :=
    exists_noncyclic_pGroup_of_perfect_section g hg hperf' hqP₀' hqker'
  obtain ⟨X₁, hX₁K, hX₁p, hX₁c⟩ :=
    SpLift.exists_noncyclic_pSubgroup_le (MonoidHom.id ↥(F11.CElt D.M V₀ x.val))
      Function.surjective_id hidx hX₀p hX₀c
  refine ⟨X₁.map (F11.CElt D.M V₀ x.val).subtype, ?_, hX₁p.map _, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hX₁K hc)
  · exact SpLift.not_isCyclic_map (F11.CElt D.M V₀ x.val).subtype
      (F11.CElt D.M V₀ x.val).subtype_injective hX₁c

theorem nineteen_seven_noncyclic_cent_of_perfect_bar (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hV : IsElemAbelian 2 V)
    (h5 : R19_5At D V₀ V p L K h) (x : IntMod V hV) (hx0 : x.val ∉ V₀)
    {P₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hP₀ : P₀ ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))
    (hperf : Group.IsPerfect P₀) (h5P₀ : 5 ∣ Nat.card P₀)
    (h5C : 5 ∣ Nat.card (F11.CTilde D.M V₀ V)) :
    ∃ X : Subgroup G, X ≤ D.M ⊓ centralizer ({x.val} : Set G) ∧ IsPGroup 5 X ∧
      ¬ IsCyclic X :=
  nineteen_seven_noncyclic_cent_of_index D Nat.prime_five hV h.hyp.hyp125.pairFacts x
    (nineteen_seven_not_dvd_index D h h5 x.val_mem hx0) hP₀ hperf h5P₀ h5C

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
