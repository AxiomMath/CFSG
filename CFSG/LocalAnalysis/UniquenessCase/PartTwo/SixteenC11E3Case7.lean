module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Aux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3AutL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_commutator_card_of_iso {F Z S : Type*} [Group F] [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) (e : F ≃* Z × S) :
    Nat.card (_root_.commutator F) = Nat.card S := by
  have h2 : _root_.commutator (Z × S) = (⊥ : Subgroup Z).prod (⊤ : Subgroup S) := by
    rw [_root_.commutator, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod,
      show ⁅(⊤ : Subgroup Z), (⊤ : Subgroup Z)⁆ = ⊥ from commutator_eq_bot Z,
      show ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ from hperf.commutator_eq_top]
  have h1 : (_root_.commutator F).map e.toMonoidHom = _root_.commutator (Z × S) := by
    rw [_root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    rfl
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h1, h2]
  rw [Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup Z) (⊤ : Subgroup S)).toEquiv,
    Nat.card_prod, Subgroup.card_bot, Subgroup.card_top, one_mul]

theorem s1611e3_case7_pRank_two_le {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h7 : Case168_7 D V₀ V hV L) :
    CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) ≤ 2 := by
  classical
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨⟨e⟩, hL3, hsum, -⟩ := h7
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let F : Subgroup (MulAut (Vtil V₀ V hV)) := Fstar Mb
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts Mb
  obtain ⟨X, hXF, hXM, hXcard, hXnorm, hXc⟩ :=
    s16c1610_center_fstar (Mb := Mb) (p := 7) (center_eq_bot_of_isL3 hL3) e
  have hrk : rk (Vtil V₀ V hV) = 9 := by
    have h9 := s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
    rwa [rk_top] at h9
  have hodd : Odd (rk (Vtil V₀ V hV)) := by rw [hrk]; decide
  have hcent : ∀ t ∈ Mb, orderOf t = 2 → ∀ x ∈ X, t * x = x * t :=
    s1611e3_cent_of_normal_seven h h125 hXM hXcard hXnorm hodd
  have hperf : Group.IsPerfect ↥Lb := ⟨s16c1610_commutator_of_isL3 hL3⟩
  haveI : Group.IsPerfect ↥Lb := hperf
  have hLbcard : Nat.card Lb = 168 := card_eq_of_isL3 hL3
  have hLbMb : Lb ≤ Mb := barSub_mono V₀ V hV hc.setting.hyp151.le
  have hPSL : IsPSL 3 2 1 ↥Lb := by
    rcases hL3 with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hh
    all_goals exact absurd h0 (by norm_num)
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Lb) :=
    s16c167_isPSL_outer_solvable hPSL
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsCyclic (Multiplicative (ZMod 7)) :=
    isCyclic_of_prime_card (p := 7) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  haveI : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (↥Lb × Multiplicative (ZMod 7))) :=
    CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor.outer_solvable_of_cyclic
      (center_eq_bot_of_isL3 hL3)
  have hOutF : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥F) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      ((e.trans MulEquiv.prodComm).symm)
  have hLbF : Lb ≤ F := s16c167_frame_le_of_perfect hFX hLbMb hFn hself hOutF hperf
  have hXinf : X ⊓ Lb = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxX, hxL⟩ := Subgroup.mem_inf.mp hx
    have hmem : (⟨x, hxL⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hXc l (hLbF l.2) x hxX)
    rw [center_eq_bot_of_isL3 hL3] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hXZ : X ≤ (Subgroup.center ↥F).map F.subtype := fun x hx =>
    ⟨⟨x, hXF hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hXc g g.2 x hx), rfl⟩
  have hZcard : Nat.card ((Subgroup.center ↥F).map F.subtype) ≤ Nat.card X := by
    rw [Subgroup.card_map_of_injective F.subtype_injective, hXcard]
    exact s16n9b_case7_card_center_le hL3 e
  have hXeq : X = (Subgroup.center ↥F).map F.subtype :=
    Subgroup.eq_of_le_of_card_ge hXZ hZcard
  have hcardF : Nat.card F = 7 * 168 := by
    have h1 : Nat.card F = Nat.card (Multiplicative (ZMod 7) × ↥Lb) := Nat.card_congr e.toEquiv
    rw [h1, Nat.card_prod, hLbcard, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hXcomm : ∀ x ∈ X, ∀ y ∈ Lb, x * y = y * x := fun x hx y hy =>
    (hXc y (hLbF hy) x hx).symm
  have hcard_sup : Nat.card ↥(X ⊔ Lb) = 7 * 168 := by
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X Lb hXcomm).1
    rw [hXinf, Subgroup.card_bot, mul_one, hXcard, hLbcard] at h1
    exact h1
  have hFsup : F = X ⊔ Lb :=
    (Subgroup.eq_of_le_of_card_ge (sup_le hXF hLbF) (by rw [hcardF, hcard_sup])).symm
  have hLbComm : ⁅Lb, Lb⁆ = Lb := (Subgroup.isPerfect_iff (H := Lb)).mp hperf
  have hcommF_eq : ⁅F, F⁆ = (_root_.commutator ↥F).map F.subtype := by
    rw [_root_.commutator, Subgroup.map_commutator]
    congr 1 <;> rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcardComm : Nat.card ↥⁅F, F⁆ = 168 := by
    rw [hcommF_eq, Subgroup.card_map_of_injective F.subtype_injective]
    exact (s1611e3_commutator_card_of_iso (F := ↥F) hperf e).trans hLbcard
  have hLb_le_comm : Lb ≤ ⁅F, F⁆ := by
    rw [← hLbComm]
    exact Subgroup.commutator_mono hLbF hLbF
  have hLbEqComm : Lb = ⁅F, F⁆ :=
    Subgroup.eq_of_le_of_card_ge hLb_le_comm (by rw [hcardComm, hLbcard])
  have hxnormF : ∀ x ∈ Mb, x ∈ Subgroup.normalizer (F : Set (MulAut (Vtil V₀ V hV))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact hFn x hx y hy
    · intro hy
      have h1 := hFn x⁻¹ (Mb.inv_mem hx) (x * y * x⁻¹) hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
  have hMbNorm : Mb ≤ Subgroup.normalizer (Lb : Set (MulAut (Vtil V₀ V hV))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hFx : F.map (MulAut.conj x) = F :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hxnormF x hx)
    rw [hLbEqComm, Subgroup.map_commutator, hFx]
  refine CFSG.SectionRank.pRank_le (p := 2) (k := 2) (by norm_num) ?_
  intro E hEM hEab
  have hEU : E ≤ Subgroup.normalizer (Lb : Set (MulAut (Vtil V₀ V hV))) := hEM.trans hMbNorm
  have hb : ∀ F' : Subgroup (MulAut ↥Lb), IsElemAbelian 2 F' → Nat.card F' ≤ 4 :=
    fun F' hF' => s1611e3_card_le_four_mulAut_l3 hL3 hF'
  have hbound := s16n9b_card_le_mul_card_inf_centralizer (p := 2) hEU hEab hb
  have htriv : E ⊓ Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
    by_cases hx1 : x = 1
    · exact hx1
    · have hx2 : x ^ 2 = 1 := hEab.2 x hxE
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
      have hxX : ∀ z ∈ X, x * z = z * x := hcent x (hEM hxE) hxord
      have hxL : ∀ l ∈ Lb, x * l = l * x :=
        fun l hl => (Subgroup.mem_centralizer_iff.1 hxC l hl).symm
      have hxFcent : ∀ f ∈ F, x * f = f * x := by
        have hle : F ≤ Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV))) := by
          rw [hFsup]
          refine sup_le ?_ ?_
          · intro a ha
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hxX a ha
          · intro b hb
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hxL b hb
        intro f hf
        exact Subgroup.mem_centralizer_iff.1 (hle hf) x (Set.mem_singleton x)
      have hxF : x ∈ F := hself x (hEM hxE) (fun f hf => hxFcent f hf)
      have hxZ : x ∈ (Subgroup.center ↥F).map F.subtype :=
        ⟨⟨x, hxF⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hxFcent g g.2).symm, rfl⟩
      rw [← hXeq] at hxZ
      have hx7 : x ^ 7 = 1 := by
        have h1 := pow_card_eq_one' (x := (⟨x, hxZ⟩ : ↥X))
        rw [hXcard] at h1
        simpa using congrArg Subtype.val h1
      have hdvd7 : orderOf x ∣ 7 := orderOf_dvd_iff_pow_eq_one.2 hx7
      have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 hx2
      have hord1 : orderOf x = 1 := by
        have h1 : orderOf x ∣ 1 := by
          have h2 := Nat.dvd_gcd hdvd7 hdvd2
          have h3 : Nat.gcd 7 2 = 1 := by norm_num
          rwa [h3] at h2
        exact Nat.dvd_one.mp h1
      exact orderOf_eq_one_iff.mp hord1
  rw [htriv, Subgroup.card_bot, mul_one] at hbound
  have h22 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [h22]
  exact hbound

theorem s1611e3_case7_three_le_mBar {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h7 : Case168_7 D V₀ V hV L) :
    3 ≤ mBar D.M V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨⟨e⟩, hL3, hsum, -⟩ := h7
  obtain ⟨X, -, hXM, hXcard, hXnorm, -⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M V₀ V hV) (p := 7) (center_eq_bot_of_isL3 hL3) e
  have hrk : rk (Vtil V₀ V hV) = 9 := by
    have h9 := s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
    rwa [rk_top] at h9
  exact s1611e3_three_le_mBar_of_normal_seven h h125 hXM hXcard hXnorm (by omega)

section Certified


theorem s1611e3_normalizer_le_of_case7 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h7 : Case168_7 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp7 : 7 ∈ D.sig := by
    rw [h7.2.2.2]
    exact Set.mem_singleton 7
  exact s1611e3_normalizer_le_of_two_rank h hc
    (s1611e3_tiConj_of_pRank_lt h hc.setting.hyp16 hp7 (s16n9b_case7_pRank_lt D hV h7))
    (s1611e3_case7_pRank_two_le h hc h7) (s1611e3_case7_three_le_mBar h hc h7) hp7

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
