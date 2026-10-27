module

public import CFSG.Quasithin.Vol2.Ch10SecCFactsCheck
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s1611e3_a5_fix_three {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {J : Subgroup W} (hL : IsAlt ↥L 5) (hJ : AlternatingNatural L J ⊥ 5) :
    ∀ w ∈ J, w ≠ 1 → ∃ y ∈ L, orderOf y = 3 ∧ y w = w := by
  obtain ⟨π, hsurj, -, -, hJinv, -, hsecinv, -, β, -, hβker, hβeq⟩ := hJ
  let e : (↥(G6.coreMod 5) ⧸
      ((FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec)) ≃* Multiplicative (AltHeart 5) :=
    CFSG.Quasithin.C124.altQuotEquiv 5 (by norm_num)
  let β' : ↥J →* Multiplicative (AltHeart 5) := e.toMonoidHom.comp β
  have hstab : ∀ x : ↥L, ∀ u ∈ J, (x : MulAut W) u ∈ J := hJinv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥J) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hβ'inj : Function.Injective β' := e.injective.comp hβinj
  have hπinj : Function.Injective π := by
    have hs5 : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup (FFModel.altDn 5).Gam := hs5
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff π).mp hk
    · exfalso
      obtain ⟨eL⟩ := hL
      haveI : Nontrivial (alternatingGroup (Fin 5)) :=
        alternatingGroup.nontrivial_of_three_le_card (by simp)
      haveI : Nontrivial ↥L := Equiv.nontrivial (eL : ↥L ≃ alternatingGroup (Fin 5))
      obtain ⟨z, hz⟩ := exists_ne (1 : ↥L)
      obtain ⟨σ, hσ⟩ := hsurj z
      have hmem : π σ = 1 := by
        rw [← MonoidHom.mem_ker, hk]
        exact Subgroup.mem_top σ
      exact hz (by rw [← hσ]; exact hmem)
  have hβe' : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥J)
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J),
      β' ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ : Equiv.Perm (Fin 5))
          (Multiplicative.toAdd (β' u))) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn 5).act γ (m : (FFModel.altDn 5).Amb) ∈
        (FFModel.altDn 5).sec := hsecinv γ m m.2
    have h1 := hβeq γ u m hu hsec hmu
    change e (β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) =
      Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ : Equiv.Perm (Fin 5))
        (Multiplicative.toAdd (e (β u))))
    rw [h1, hmu]
    rfl
  intro w hwJ hwne
  let u : ↥J := ⟨w, hwJ⟩
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β' u))
  have hsum : ∑ i, (a : Fin 5 → ZMod 2) i = 0 :=
    CFSG.Quasithin.C124.mem_evenWeight_iff'.1 a.2
  obtain ⟨σ, hσ3, hσne, hσsign, hσfix⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecC.d5_fixed_by_three (a : Fin 5 → ZMod 2) hsum
  let γ : (FFModel.altDn 5).Gam := ⟨σ, (Equiv.Perm.mem_alternatingGroup).mpr hσsign⟩
  have hγ3 : γ ^ 3 = 1 := Subtype.ext hσ3
  have hγne : γ ≠ 1 := fun h => hσne (congrArg Subtype.val h)
  let y : ↥L := π γ
  have hpermfix : CFSG.Quasithin.permWeight 5 σ a = a := by
    apply Subtype.ext
    funext i
    rw [CFSG.Quasithin.C41Pf.AltN.permWeight_apply]
    simpa using (hσfix (σ⁻¹ i)).symm
  have hfixperm : CFSG.Quasithin.C41Pf.AltN.hAct 5 σ (Multiplicative.toAdd (β' u)) =
      Multiplicative.toAdd (β' u) := by
    rw [← ha, CFSG.Quasithin.C41Pf.AltN.hAct_mk 5 σ a, hpermfix]
  have hfixβ : β' ⟨((π γ : ↥L) : MulAut W) (u : W), hstab (π γ) u u.2⟩ = β' u := by
    rw [hβe' γ u (hstab (π γ) u u.2), hfixperm, ofAdd_toAdd]
  have hsub : (⟨((π γ : ↥L) : MulAut W) (u : W), hstab (π γ) u u.2⟩ : ↥J) = u :=
    hβ'inj hfixβ
  have hyw : ((π γ : ↥L) : MulAut W) w = w := by
    have h := congrArg Subtype.val hsub
    simpa [u] using h
  have hy1 : y ≠ 1 := by
    intro h
    apply hγne
    apply hπinj
    rw [map_one]
    exact h
  have hy3' : (y ^ 3 : ↥L) = 1 := by
    change (π γ) ^ 3 = 1
    rw [← map_pow π γ 3, hγ3, map_one]
  have hy3 : ((y : ↥L) : MulAut W) ^ 3 = 1 := by
    have h := congrArg (fun z : ↥L => (z : MulAut W)) hy3'
    simpa using h
  have hyne : ((y : ↥L) : MulAut W) ≠ 1 := fun h => hy1 (Subtype.ext h)
  exact ⟨((y : ↥L) : MulAut W), y.2, orderOf_eq_prime hy3 hyne, hyw⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
