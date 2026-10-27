module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A3
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

private theorem r95_card_gl2_lt_168 {F : Type} [Field F] [Finite F]
    (hq : Nat.card F = 2 ∨ Nat.card F = 3) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) < 168 := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field (n := 2), Fin.prod_univ_two]
  rcases hq with hq | hq
  · have h2 : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hq
    rw [h2]; norm_num
  · have h3 : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hq
    rw [h3]; norm_num

theorem r95_gl2_section_psl2 {F : Type} [Field F] [Finite F]
    {G : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)} {Qm : Type} [Group Qm] [IsSimpleGroup Qm]
    (hnc : ¬ IsMulCommutative Qm) (π : ↥G →* Qm) (hπ : Function.Surjective π) :
    ∃ (X : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (π' : ↥X →* Qm),
      Function.Surjective π' := by
  haveI : Finite ↥G := inferInstance
  haveI : Group.IsPerfect Qm := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  have hZ : Subgroup.center Qm = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  obtain ⟨⟨k, hk, -⟩, -, hPperf, -⟩ := CFSG.perfect_residual_characterization (G := ↥G)
  let P : Subgroup ↥G := CFSG.perfectResidual ↥G
  have hPmap : P.map π = ⊤ := by
    change (CFSG.perfectResidual ↥G).map π = ⊤
    rw [hk, map_derivedSeries_eq hπ, Group.IsPerfect.derivedSeries_eq_top]
  haveI : Group.IsPerfect ↥P := hPperf
  let πP : ↥P →* Qm := π.comp P.subtype
  have hπP : Function.Surjective πP := by
    intro y
    have hy : y ∈ P.map π := by rw [hPmap]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, hxy⟩
  let ι : ↥P →* Matrix.GeneralLinearGroup (Fin 2) F := G.subtype.comp P.subtype
  have hιinj : Function.Injective ι := G.subtype_injective.comp P.subtype_injective
  haveI : Group.IsPerfect ↥(P.map G.subtype) := Group.IsPerfect.map (f := G.subtype)
  have hdet : ∀ x : ↥P,
      ((ι x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    intro x
    exact CFSG.SectionRank.Ccomm.det_eq_one_of_perfect (P.map G.subtype)
      ⟨(x : ↥G), x.2, rfl⟩
  let toSL : ↥P →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun x => ⟨(ι x : Matrix (Fin 2) (Fin 2) F), hdet x⟩
      map_one' := by
        apply Subtype.ext
        show ((ι 1 : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = 1
        rw [map_one]
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        show ((ι (x * y) : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) =
            ((ι x : Matrix.GeneralLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) *
              ((ι y : Matrix.GeneralLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F)
        rw [map_mul]
        rfl }
  have htoSLinj : Function.Injective toSL := by
    intro x y h
    apply hιinj
    exact Units.ext (congrArg Subtype.val h)
  let κ : ↥P →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp toSL
  have hker : κ.ker ≤ πP.ker := by
    intro x hx
    have hxcen : toSL x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      refine (QuotientGroup.eq_one_iff (toSL x)).mp ?_
      show κ x = 1
      exact MonoidHom.mem_ker.mp hx
    have hxc : x ∈ Subgroup.center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply htoSLinj
      simp only [map_mul]
      exact (Subgroup.mem_center_iff.mp hxcen) (toSL y)
    exact MonoidHom.center_le_ker πP hπP hZ hxc
  let π' : ↥(κ.range) →* Qm :=
    MonoidHom.liftOfRightInverse (f := κ.rangeRestrict)
      (Function.surjInv (MonoidHom.rangeRestrict_surjective κ))
      (Function.rightInverse_surjInv (MonoidHom.rangeRestrict_surjective κ))
      ⟨πP, by rw [MonoidHom.ker_rangeRestrict]; exact hker⟩
  refine ⟨κ.range, π', ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hπP y
  exact ⟨κ.rangeRestrict x, by
    show MonoidHom.liftOfRightInverse (f := κ.rangeRestrict)
      (Function.surjInv (MonoidHom.rangeRestrict_surjective κ))
      (Function.rightInverse_surjInv (MonoidHom.rangeRestrict_surjective κ)) _ (κ.rangeRestrict x) =
        πP x
    rw [MonoidHom.liftOfRightInverse_comp_apply]⟩

theorem r95_gl2_char_seven {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p ^ f)
    {G : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)} {Qm : Type} [Group Qm]
    (π : ↥G →* Qm) (hπ : Function.Surjective π) (hm : LieModel Qm .PSL 3 2 1) : p = 7 := by
  obtain ⟨hsimple, hcard⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hm
  haveI : IsSimpleGroup Qm := hsimple
  haveI : Finite Qm := Finite.of_surjective π hπ
  have hnc : ¬ IsMulCommutative Qm := by
    intro hc
    haveI : IsMulCommutative Qm := hc
    have hprime : (Nat.card Qm).Prime := (Group.is_simple_iff_prime_card (α := Qm)).mp hsimple
    rw [hcard] at hprime
    norm_num at hprime
  by_cases hsmall : p ^ f < 4
  · exfalso
    have hq2 : 2 ≤ p ^ f := by
      rw [← hF]
      exact Nat.succ_le_of_lt (Finite.one_lt_card (α := F))
    have hq : p ^ f = 2 ∨ p ^ f = 3 := by omega
    have hcardF : Nat.card F = 2 ∨ Nat.card F = 3 := by rw [hF]; exact hq
    have hleG : Nat.card Qm ≤ Nat.card ↥G := Nat.card_le_card_of_surjective π hπ
    have hle : Nat.card Qm ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) :=
      hleG.trans (Subgroup.card_le_card_group (H := G))
    have h168 : 168 ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) := hcard ▸ hle
    have := r95_card_gl2_lt_168 hcardF
    omega
  · have h4 : 4 ≤ p ^ f := not_lt.1 hsmall
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with hf0 | hfp
      · subst hf0; simp at h4
      · exact hfp
    obtain ⟨X, π', hπ'⟩ := r95_gl2_section_psl2 hnc π hπ
    haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
    have hLM : LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) .PSL 2 p f :=
      CFSG.GH74.Generic.BProg.B2.L2Cover.lieModel_psl2_of_equiv
        (Y := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) hp hf hF (by omega) (by omega)
        (MulEquiv.refl _)
    exact r95_char_seven_of_section hLM π' hπ' hm

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
