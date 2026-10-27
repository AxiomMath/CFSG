module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4M24
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Inner
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Quot
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Transport

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (starHom ker_starHom range_starHom_eq)

theorem innerOnModO2_of_le_Hj
    {B : Subgroup J} (hB : B ≤ Hj)
    (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) (f : ↥B →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) (hker : f.ker = CFSG.Open.pCore 2 ↥B) :
    ∀ x ∈ P0, A38c8.InnerOnModO2 B x := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have hmem : ∀ g : ↥Hj, starHom g ∈ NativeSporadic.M24 := fun g => by
    rw [← range_starHom_eq]
    exact ⟨g, rfl⟩
  let π : ↥Hj →* ↥NativeSporadic.M24 := starHom.codRestrict NativeSporadic.M24 hmem
  have hπsurj : Function.Surjective π := by
    intro y
    have hy : (y : Equiv.Perm (Fin 24)) ∈ starHom.range := by
      rw [range_starHom_eq]
      exact y.2
    obtain ⟨g, hg⟩ := hy
    exact ⟨g, Subtype.ext hg⟩
  have hπker : π.ker = starHom.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hπkerP : IsPGroup 2 π.ker := by
    rw [hπker, ker_starHom]
    exact (isPGroup_Eg (elem_uJ hM)).of_equiv (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).symm
  have hSylHj : IsSylowTwoOf P0 Hj :=
    isSylowTwoOf_of_le CFSG.Quasithin.J4Loc.isSylowTwoOf_P0 P0_le_Hj
  have hT := Setup.Family.isSylowTwoOf_map_range π hSylHj
  rw [MonoidHom.range_eq_top.2 hπsurj] at hT
  obtain ⟨g, hg, hgP⟩ := exists_alt8_image π hπkerP hB f hf hker
  have hgker : g.ker = CFSG.Open.pCore 2 ↥((B.subgroupOf Hj).map π) :=
    ker_eq_pCore_of_alt8 g hg hgP
  exact innerOnModO2_of_quotient π hπkerP P0_le_Hj hB hPB
    (exists_mul_pCore hT (map_le_normalizer_map π hPB) g hg hgker)

end CFSG.Quasithin.J4L4
