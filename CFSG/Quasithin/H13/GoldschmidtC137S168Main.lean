module

public import CFSG.Quasithin.H13.GoldschmidtC137S168Rho
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ.S168

open CFSG.SeitzReduction.RankOne.DegreeEight CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem card_psl_two_seven :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) = 168 := by
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one
    (K := ZMod 7) (by decide)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := ZMod 7)
  rw [Nat.card_zmod, hcenter] at hcard
  omega

theorem nonempty_mulEquiv_psl_seven {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcard : Nat.card S = 168) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) := by
  obtain ⟨F⟩ := nonempty_frame hcard
  have hρ := F.rho_injective hcard
  let N : Subgroup (Equiv.Perm (Option (ZMod 7))) := (F.rho hcard).range
  have hshift : shift ∈ N := ⟨F.x, F.rho_x hcard⟩
  have hdbl : dbl ∈ N := ⟨F.y, F.rho_y hcard⟩
  have hstab : ∀ σ ∈ N, σ none = none → IsAffine σ := by
    rintro _ ⟨g, rfl⟩ hg
    exact F.rho_isAffine hcard ((F.rho_none_iff hcard g).1 hg)
  have hswap : ∃ s ∈ N, s none = some 0 ∧ s (some 0) = none := by
    obtain ⟨g, h1, h2⟩ := F.exists_swap hcard
    exact ⟨F.rho hcard g, ⟨g, rfl⟩, h1, h2⟩
  let eSN : S ≃* N := MonoidHom.ofInjective hρ
  have hNcard : Nat.card N = 168 := by rw [← hcard]; exact (Nat.card_congr eSN.toEquiv).symm
  have hNs : IsSimpleGroup N := eSN.symm.isSimpleGroup
  rcases degreeEight_classification hshift hdbl hstab hswap with ⟨E, hEN, hEnorm, hEreg⟩ | hle
  · exfalso
    have hbij : Function.Bijective (fun e : E => (e : Equiv.Perm (Option (ZMod 7))) none) :=
      Function.bijective_iff_existsUnique _ |>.2 fun q => hEreg none q
    have hE8 : Nat.card E = 8 := by
      rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card,
        Fintype.card_option, ZMod.card]
    have hEc : Nat.card (E.subgroupOf N) = 8 := by
      rw [← hE8]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.subgroupOf N) with hb | ht
    · rw [hb, Subgroup.card_bot] at hEc
      omega
    · rw [ht, Subgroup.card_top, hNcard] at hEc
      omega
  · let ψ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) →*
        Equiv.Perm (Option (ZMod 7)) :=
      projEquiv.symm.permCongrHom.toMonoidHom.comp Projectivization.PSLAction.toPermHom
    have hnat : natPSL = ψ.range := rfl
    have hψc : Nat.card ψ.range ≤ 168 := by
      rw [← card_psl_two_seven]
      exact Nat.card_le_card_of_surjective _ ψ.rangeRestrict_surjective
    have hNeq : N = ψ.range :=
      Subgroup.eq_of_le_of_card_ge (hnat ▸ hle) (by rw [hNcard]; exact hψc)
    have hsurj : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
    let e2 : N ≃* ψ.range := MulEquiv.subgroupCongr hNeq
    have hc : Nat.card ψ.range = 168 := by rw [← Nat.card_congr e2.toEquiv, hNcard]
    have hbij : Function.Bijective ψ.rangeRestrict :=
      hsurj.bijective_of_nat_card_le (by rw [card_psl_two_seven, hc])
    exact ⟨eSN.trans (e2.trans (MulEquiv.ofBijective ψ.rangeRestrict hbij).symm)⟩

theorem catalog_of_simple_card_168 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcard : Nat.card S = 168) : Catalog S := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_seven hcard
  have hm : StatedClassicalModel S .PSL 2 7 1 :=
    ⟨⟨by norm_num, le_rfl, le_rfl, by decide, by decide⟩, ZMod 7, inferInstance, inferInstance,
      by simp, ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 7))⟩⟩
  exact lieModel_catalog S .PSL 2 7 1 (Or.inl ⟨by decide, hm⟩)

end CFSG.Quasithin.H13.U3.GC137.SQ.S168
