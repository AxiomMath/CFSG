module

import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec4.T444.Lift

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

section General

variable {W : Type*} [Group W]

theorem le_of_isPerfect_of_isSolvable_quotient {N : Subgroup W} [N.Normal]
    (hs : Group.IsSolvable (W ⧸ N)) {P : Subgroup W} [Group.IsPerfect P] : P ≤ N := by
  set f : P →* W ⧸ N := (QuotientGroup.mk' N).comp P.subtype with hf
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro x hx
  have h1 : f ⟨x, hx⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩ : f.range) 1)
  exact (QuotientGroup.eq_one_iff x).mp h1

end General

section Model

theorem isPerfect_projSL : Group.IsPerfect (projSL 3 (GaloisField 2 2)) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have : Group.IsPerfect (projectiveSL 3 (GaloisField 2 2)) :=
    Group.IsPerfect.ofSurjective (proj_surjective 3 _)
  exact Group.IsPerfect.ofSurjective
    (f := (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem center_projSL_eq_bot : Subgroup.center (projSL 3 (GaloisField 2 2)) = ⊥ := by
  set e := KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)
  have h := LinearThreeFourOuter.center_projectiveSL_three_eq_bot
    KFacts.L34.card_galoisField_two_two
  rw [← Subgroup.map_center_eq e.symm, h, Subgroup.map_bot]

theorem isSimpleGroup_projSL : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

noncomputable def specialLinearQuotientCenterEquiv :
    Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ≃*
      projSL 3 (GaloisField 2 2) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 (GaloisField 2 2)).symm).trans
    (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm

end Model

section Shape

variable {W : Type} [Group W] [Finite W]

theorem exists_mulEquiv_projSL_of_isZ3L34OrHeisSL34 (hW : IsZ3L34OrHeisSL34 W)
    {N : Subgroup W} [N.Normal] [Group.IsPerfect N] (hs : Group.IsSolvable (W ⧸ N)) :
    Nonempty (N ⧸ Subgroup.center N ≃* projSL 3 (GaloisField 2 2)) ∧
      Nat.card (Subgroup.center N) ∣ 3 := by
  rcases hW with he | ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩
  ·
    obtain ⟨e⟩ := he
    set P := projSL 3 (GaloisField 2 2)
    have : Group.IsPerfect P := isPerfect_projSL
    set φ : W →* Multiplicative (ZMod 3) := (MonoidHom.fst _ _).comp e.toMonoidHom with hφ
    set Pw : Subgroup W := ((MonoidHom.inr (Multiplicative (ZMod 3)) P).range).comap
      e.toMonoidHom with hPw
    have hPwe : Pw.map e.toMonoidHom = (MonoidHom.inr (Multiplicative (ZMod 3)) P).range :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective _
    set ePw : Pw ≃* P := (Pw.equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hPwe).trans
        ((MonoidHom.inr (Multiplicative (ZMod 3)) P).ofInjective
          (fun a b h => congrArg Prod.snd h)).symm) with hePw
    have : Group.IsPerfect Pw :=
      Group.IsPerfect.ofSurjective (f := ePw.symm.toMonoidHom) ePw.symm.surjective
    have hPwN : Pw ≤ N := le_of_isPerfect_of_isSolvable_quotient hs
    have hNPw : N ≤ Pw := by
      have hNφ : N ≤ φ.ker := by
        have : Group.IsPerfect (N.map φ) := Group.IsPerfect.map φ
        have hcomm' : ∀ a b : N.map φ, a * b = b * a := fun a b => Subtype.ext (mul_comm _ _)
        have hsub : Subsingleton (N.map φ) := by
          by_contra hnt
          rw [not_subsingleton_iff_nontrivial] at hnt
          exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hcomm')
        intro x hx
        have h1 := congrArg Subtype.val
          (Subsingleton.elim (⟨φ x, x, hx, rfl⟩ : N.map φ) 1)
        exact h1
      intro x hx
      have hx1 : (e x).1 = 1 := hNφ hx
      refine ⟨(e x).2, ?_⟩
      ext
      · exact hx1.symm
      · rfl
    have hNeq : N = Pw := le_antisymm hNPw hPwN
    have eN : N ≃* P := (MulEquiv.subgroupCongr hNeq).trans ePw
    have hZ : Subgroup.center N = ⊥ := by
      rw [← Subgroup.map_center_eq eN.symm, center_projSL_eq_bot, Subgroup.map_bot]
    refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans eN)⟩, ?_⟩
    rw [hZ, Subgroup.card_bot]
    exact one_dvd 3
  ·
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have : Group.IsPerfect V :=
      Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVN : V ≤ N := le_of_isPerfect_of_isSolvable_quotient hs
    have hkey : ∀ u ∈ U, ∀ x ∈ V, u * x * u⁻¹ = x := fun u hu x hx => by
      rw [hcomm u hu x hx, mul_inv_cancel_right]
    have hVn : V.Normal := by
      refine ⟨fun v hv w => ?_⟩
      obtain ⟨u, hu, v', hv', rfl⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hUV hcomm w
      have hx : v' * v * v'⁻¹ ∈ V := V.mul_mem (V.mul_mem hv' hv) (V.inv_mem hv')
      have h1 : u * v' * v * (u * v')⁻¹ = u * (v' * v * v'⁻¹) * u⁻¹ := by group
      rw [h1, hkey u hu _ hx]
      exact hx
    have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 3) hU.2.1
    have hsV : Group.IsSolvable (W ⧸ V) := by
      have : Group.IsNilpotent U := hUp.isNilpotent
      refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' V).comp U.subtype) ?_
      intro q
      induction q using QuotientGroup.induction_on with
      | H w =>
        obtain ⟨u, hu, v, hv, rfl⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hUV hcomm w
        refine ⟨⟨u, hu⟩, ?_⟩
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        change u⁻¹ * (u * v) ∈ V
        rwa [inv_mul_cancel_left]
    have hNV : N ≤ V := le_of_isPerfect_of_isSolvable_quotient hsV
    have hNeq : N = V := le_antisymm hNV hVN
    subst hNeq
    refine ⟨⟨(QuotientGroup.congr _ _ eV (Subgroup.map_center_eq eV)).trans
      specialLinearQuotientCenterEquiv⟩, ?_⟩
    rw [KFacts.L34.card_center_of_mulEquiv eV]

end Shape

section Star

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_projSL_map_starQuot {A L : Subgroup G} (hA : IsPGroup 3 A)
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hZ : IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G))) :
    Nonempty (L.map (starQuot G) ⧸ Subgroup.center (L.map (starQuot G)) ≃*
        projSL 3 (GaloisField 2 2)) ∧
      Nat.card (Subgroup.center (L.map (starQuot G))) ∣ 3 := by
  set π := starQuot G with hπ
  set W := (A ⊔ L).map π with hW
  set Ls := L.map π with hLs
  have hLW : Ls ≤ W := Subgroup.map_mono le_sup_right
  set N := Ls.subgroupOf W with hN
  have hWL : A ⊔ L ≤ Subgroup.normalizer (L : Set G) := sup_le hAL Subgroup.le_normalizer
  have hNn : N.Normal := by
    refine ⟨fun x hx w => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyw⟩ := w.2
    have hyn : π y ∈ Subgroup.normalizer (Ls : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
      Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π (hWL hy))
    change (w : G ⧸ CFSG.pPrimeCore 3 G) * x * (w : G ⧸ CFSG.pPrimeCore 3 G)⁻¹ ∈ Ls
    rw [← hyw]
    exact (Subgroup.mem_normalizer_iff.mp hyn _).mp hx
  have : Group.IsPerfect L := hL.1
  have : Group.IsPerfect Ls := Group.IsPerfect.map π
  have : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hLW).symm.toMonoidHom) (MulEquiv.surjective _)
  have hsW : Group.IsSolvable (W ⧸ N) := by
    have : Group.IsNilpotent A := hA.isNilpotent
    set ι : A →* W := (π.comp A.subtype).codRestrict W
      (fun a => Subgroup.mem_map_of_mem π (le_sup_left (b := L) a.2)) with hι
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).comp ι) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      obtain ⟨x, hx, hxw⟩ := w.2
      have hx' : x ∈ (A : Set G) * (L : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right A L hAL]
        exact hx
      obtain ⟨a, ha, l, hl, rfl⟩ := hx'
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change (π a)⁻¹ * (w : G ⧸ CFSG.pPrimeCore 3 G) ∈ Ls
      rw [← hxw, map_mul, inv_mul_cancel_left]
      exact Subgroup.mem_map_of_mem π hl
  obtain ⟨⟨ψ⟩, h3⟩ := exists_mulEquiv_projSL_of_isZ3L34OrHeisSL34 hZ hsW (N := N)
  set e := Subgroup.subgroupOfEquivOfLe hLW
  have hce : (Subgroup.center N).map e.toMonoidHom = Subgroup.center Ls :=
    Subgroup.map_center_eq e
  refine ⟨⟨(QuotientGroup.congr _ _ e.symm (by rw [← hce, Subgroup.map_map]; simp)).trans ψ⟩,
    ?_⟩
  rwa [← hce, Subgroup.card_map_of_injective e.injective]

theorem exists_solvable_quotient_projSL {A L : Subgroup G} (hA : IsPGroup 3 A)
    (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hZ : IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G))) :
    ∃ (K : Subgroup L) (_ : K.Normal), Group.IsSolvable K ∧ ¬ 9 ∣ Nat.card K ∧
      Nonempty (L ⧸ K ≃* projSL 3 (GaloisField 2 2)) := by
  obtain ⟨⟨ψ⟩, hZ3⟩ := exists_mulEquiv_projSL_map_starQuot hA hL hAL hZ
  set π := starQuot G with hπ
  set Ls := L.map π with hLs
  set φ : L →* Ls := (π.comp L.subtype).codRestrict Ls
    (fun l => Subgroup.mem_map_of_mem π l.2) with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨_, l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  set K : Subgroup L := (Subgroup.center Ls).comap φ with hK
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance φ
  set χ : L →* Ls ⧸ Subgroup.center Ls := (QuotientGroup.mk' (Subgroup.center Ls)).comp φ
    with hχ
  have hχs : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hφs
  have hχk : χ.ker = K := by
    ext x
    rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hK, Subgroup.mem_comap]
  have hθL := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3
  have hkerφ : ∀ l : L, φ l = 1 ↔ l ∈ aschbacherSolvableCore 3 L := by
    intro l
    constructor
    · intro h
      have h1 : π l = 1 := congrArg Subtype.val h
      have hm : (l : G) ∈ L ⊓ CFSG.pPrimeCore 3 G := ⟨l.2, (QuotientGroup.eq_one_iff _).mp h1⟩
      rw [hθL] at hm
      obtain ⟨t, ht, hte⟩ := hm
      have : t = l := Subtype.ext hte
      rwa [← this]
    · intro h
      apply Subtype.ext
      change π l = 1
      have hm : (l : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨l, h, rfl⟩
      rw [← hθL] at hm
      exact (QuotientGroup.eq_one_iff _).mpr hm.2
  set θL := aschbacherSolvableCore 3 L with hθLdef
  have hθK : θL ≤ K := fun l hl => by
    change φ l ∈ Subgroup.center Ls
    rw [(hkerφ l).mpr hl]
    exact one_mem _
  set g : K →* Subgroup.center Ls := (φ.comp K.subtype).codRestrict (Subgroup.center Ls)
    (fun k => k.2) with hg
  have hgker : ∀ k : K, g k = 1 ↔ (k : L) ∈ θL := fun k => by
    rw [← hkerφ]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hsolvθ : Group.IsSolvable θL :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have h3θ : ¬ 3 ∣ Nat.card θL :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hKs : Group.IsSolvable K := by
    have : Group.IsSolvable (Subgroup.center Ls) := Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hθK) g ?_
    intro k hk
    exact ⟨⟨k, (hgker k).mp hk⟩, rfl⟩
  have h9 : ¬ 9 ∣ Nat.card K := by
    intro h9
    have hcard : Nat.card K = Nat.card g.range * Nat.card g.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    have hr : Nat.card g.range ∣ 3 := (Subgroup.card_subgroup_dvd_card _).trans hZ3
    have hk : Nat.card g.ker = Nat.card θL := by
      refine Nat.card_congr (Equiv.ofBijective (fun k => ⟨k.1, (hgker k.1).mp k.2⟩) ⟨?_, ?_⟩)
      · intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : θL => (t : L)) hab
      · intro t
        exact ⟨⟨⟨t, hθK t.2⟩, (hgker _).mpr t.2⟩, rfl⟩
    rw [hcard, hk] at h9
    rcases (Nat.dvd_prime Nat.prime_three).mp hr with h1 | h1
    · rw [h1, one_mul] at h9
      exact h3θ ((Dvd.intro_left 3 rfl).trans h9)
    · rw [h1] at h9
      exact h3θ (Nat.dvd_of_mul_dvd_mul_left (show 0 < 3 by norm_num)
        (show 3 * 3 ∣ 3 * Nat.card θL by simpa using h9))
  refine ⟨K, hKn, hKs, h9, ⟨(QuotientGroup.quotientMulEquivOfEq hχk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective χ hχs).trans ψ)⟩⟩

end Star

end CFSG.RankThree.PartTwo.Sec4
