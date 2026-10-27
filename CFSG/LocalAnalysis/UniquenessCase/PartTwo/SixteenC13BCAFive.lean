module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCPerf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBNatOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveOrbEq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveStab
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16c13bcA_derived_normal {A : Type*} [Group A] {Mb F : Subgroup A}
    (hFn : ∀ x ∈ Mb, ∀ f ∈ F, x * f * x⁻¹ ∈ F) :
    ∀ m ∈ Mb, ∀ n ∈ ⁅F, F⁆, m * n * m⁻¹ ∈ ⁅F, F⁆ := by
  intro m hm n hn
  have key : ⁅F, F⁆ ≤ (⁅F, F⁆).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have h : (MulAut.conj m).toMonoidHom ⁅a, b⁆ = ⁅m * a * m⁻¹, m * b * m⁻¹⁆ := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
        commutatorElement_def]
      group
    rw [h]
    exact Subgroup.commutator_mem_commutator (hFn m hm a ha) (hFn m hm b hb)
  have h := key hn
  rw [Subgroup.mem_comap] at h
  simpa [MulAut.conj_apply] using h

private theorem s16c13bcA_card_derived {W : Type} [CommGroup W] [Finite W]
    {Mb : Subgroup (MulAut W)} {Q : Type} [Group Q] (hQ : _root_.commutator Q = ⊤)
    (e : ↥(Fstar Mb) ≃* Multiplicative (ZMod 3) × Q) :
    Nat.card ↥⁅Fstar Mb, Fstar Mb⁆ = Nat.card Q := by
  have hF : (⊤ : Subgroup ↥(Fstar Mb)).map (Fstar Mb).subtype = Fstar Mb := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : ⁅Fstar Mb, Fstar Mb⁆ = (_root_.commutator ↥(Fstar Mb)).map (Fstar Mb).subtype := by
    rw [_root_.commutator, Subgroup.map_commutator, hF]
  have hZ : ⁅(⊤ : Subgroup (Multiplicative (ZMod 3))),
      (⊤ : Subgroup (Multiplicative (ZMod 3)))⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm a b
  have h2 : (_root_.commutator ↥(Fstar Mb)).map e.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (⊤ : Subgroup Q) := by
    rw [_root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective, ← Subgroup.top_prod_top,
      Subgroup.commutator_prod_prod, hZ,
      show ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ from hQ]
  rw [h1, Subgroup.card_map_of_injective (f := (Fstar Mb).subtype) (Fstar Mb).subtype_injective,
    ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h2,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
    Subgroup.card_top, one_mul]

private theorem s16c13bcA_eq_derived {W : Type} [CommGroup W] [Finite W]
    {Mb Lb : Subgroup (MulAut W)} (hP : _root_.commutator ↥Lb = ⊤)
    (e : ↥(Fstar Mb) ≃* Multiplicative (ZMod 3) × ↥Lb) (hLF : Lb ≤ Fstar Mb) :
    Lb = ⁅Fstar Mb, Fstar Mb⁆ := by
  haveI : Group.IsPerfect ↥Lb := Group.isPerfect_def.mpr hP
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · calc Lb = ⁅Lb, Lb⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅Fstar Mb, Fstar Mb⁆ := Subgroup.commutator_mono hLF hLF
  · rw [s16c13bcA_card_derived hP e]

theorem s16c13bcA_case168_5 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (h5 : Case168_5 D ⊥ V hV L) : Insp1613U D V := by
  classical
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hLM : L ≤ D.M := hc.setting.hyp151.le
  obtain ⟨⟨e⟩, hΩ, hnat, hσ⟩ := h5
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [hσ]
    exact Set.mem_singleton 3
  have hQ : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥ := s16c1610_center_of_isOmegaPlus_four_two hΩ
  have hP : _root_.commutator ↥(lBar ⊥ V hV L) = ⊤ :=
    s16c1610_commutator_of_isOmegaPlus_four_two hΩ
  have hperf : Group.IsPerfect ↥(lBar ⊥ V hV L) := Group.isPerfect_def.mpr hP
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts (Mbar D.M ⊥ V hV)
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hLM
  have hOutF : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(Fstar (Mbar D.M ⊥ V hV))) :=
    s16c13bcA_outer_solvable_om hΩ e
  have hLF : lBar ⊥ V hV L ≤ Fstar (Mbar D.M ⊥ V hV) :=
    s16c167_frame_le_of_perfect hFX hLX hFn hself hOutF hperf
  have hLeq : lBar ⊥ V hV L = ⁅Fstar (Mbar D.M ⊥ V hV), Fstar (Mbar D.M ⊥ V hV)⁆ :=
    s16c13bcA_eq_derived hP e hLF
  have hLn : ∀ m ∈ Mbar D.M ⊥ V hV, ∀ l ∈ lBar ⊥ V hV L, m * l * m⁻¹ ∈ lBar ⊥ V hV L := by
    intro m hm l hl
    rw [hLeq] at hl ⊢
    exact s16c13bcA_derived_normal hFn m hm l hl
  obtain ⟨X, hXF, -, hXcard, hXn, hXc⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M ⊥ V hV) (p := 3) hQ e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥X := isCyclic_of_prime_card hXcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥X)
  have hgord : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hXcard]
  have hzX : (g : MulAut (Vtil ⊥ V hV)) ∈ X := g.prop
  have hzord : orderOf (g : MulAut (Vtil ⊥ V hV)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hgord
  have hz3 : (g : MulAut (Vtil ⊥ V hV)) ^ 3 = 1 := by
    rw [← hzord]
    exact pow_orderOf_eq_one _
  have hz1 : (g : MulAut (Vtil ⊥ V hV)) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzord
    omega
  have hzL : (g : MulAut (Vtil ⊥ V hV)) ∉ lBar ⊥ V hV L := fun hzL' =>
    s16c13bc_not_mem_of_perfect Nat.prime_three hP hQ hXcard
      (fun m hm x hx => hXn m (hLX hm) x hx) hzL' hz1 hzX
  have hzc : ∀ l ∈ lBar ⊥ V hV L, (g : MulAut (Vtil ⊥ V hV)) * l = l * g := fun l hl =>
    (hXc l (hLF hl) g hzX).symm
  have hT : ∀ w₁ w₂ : Vtil ⊥ V hV, w₁ ≠ 1 → w₂ ≠ 1 →
      Odd (Nat.card (MulAction.orbit ↥(lBar ⊥ V hV L) w₁)) →
      Odd (Nat.card (MulAction.orbit ↥(lBar ⊥ V hV L) w₂)) →
      w₂ ∈ MulAction.orbit ↥(lBar ⊥ V hV L) w₁ :=
    fun w₁ w₂ h₁ h₂ o₁ o₂ => s16c13bcA_orbit_eq_of_odd hnat h₁ h₂ o₁ o₂
  obtain ⟨n₀, hn₀, -⟩ := s16c13bc_exists_fixed D h
  obtain ⟨n, hn1, hnP, hnodd⟩ := s16c13bcA_exists_fixed_odd_orbit
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) ⟨n₀, hn₀⟩ (H := lBar ⊥ V hV L)
    (P := barSub ⊥ V hV (E3.wClos V D.k D.T)) (s16c13bcA_wBar_isPGroup D hV)
    (fun p hp l hl => hLn p (s16c13bcA_wBar_le_mbar D hV hp) l hl) hT
  have hnfix : n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)) := mem_fixV.mpr hnP
  obtain ⟨y, hyL, hyn⟩ := s16c13bcA_mem_orbit_smul hzc hT hn1 hnodd
  obtain ⟨ψ, hψL, hψo, hψn⟩ := s16n9b_natOmegaPlus_fix hnat hn1
  have h9 : ∀ y ∈ lBar ⊥ V hV L, orderOf y ≠ 9 := by
    intro y hy
    have h' := s16c13bcA_orderOf_ne_nine_om hΩ ⟨y, hy⟩
    rwa [← Subgroup.orderOf_coe] at h'
  obtain ⟨Xs, hXsle, hXsp, hXsc, hXsn⟩ := s16c13bcA_noncyclic_stab hz3 hzL hzc h9
    ⟨ψ, hψL, hψo, hψn⟩ ⟨y, hyL, hyn⟩
  have hXsM : Xs ≤ Mbar D.M ⊥ V hV := by
    refine hXsle.trans (sup_le ?_ hLX)
    rw [Subgroup.zpowers_le]
    exact hFX (hXF hzX)
  exact s16c13bcA_insp_of_fixing D h hp3 hn1 hnfix hXsM hXsp hXsc hXsn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
