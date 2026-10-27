module

public import CFSG.RankThree.PartOne.HNB.UnitaryBridge
public import CFSG.RankThree.PartOne.HNB.NativeTransfer
public import CFSG.Sporadic.HNOddCore.Five
public import CFSG.Sporadic.HNSchreier.Simple
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.S11c.HNProps

public section

namespace CFSG.RankThree.PartOne.HNB

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CFSG.Assembly.LowTwoRank HNUnitaryBridge
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem smallPermLists_eq : smallPermLists = FAData.iSmall := rfl

theorem exists_noncomm_of_simple_card {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 126000) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup G := { ‹Group G› with mul_comm := fun a b => hcon a b }
  have := IsSimpleGroup.prime_card (α := G)
  rw [hcard] at this
  exact absurd this (by norm_num)


theorem exists_rho : ∃ ρ : IJ →* Equiv.Perm (Fin 50),
    ∀ (g : IJ) (k : Fin 50), (g : JH) • omPt k = omPt (ρ g k) := by
  classical
  have hex : ∀ (g : IJ) (k : Fin 50), ∃ l : Fin 50, (g : JH) • omPt k = omPt l := by
    intro g k
    obtain ⟨l, hl⟩ := mem_omega_of_comm (IJ_le_CJ g.2) (⟨k, rfl⟩ : omPt k ∈ Set.range omPt)
    exact ⟨l, hl.symm⟩
  choose f hf using hex
  have hmul : ∀ (g h : IJ) (k : Fin 50), f (g * h) k = f g (f h k) := by
    intro g h k
    apply omPt_injective
    calc omPt (f (g * h) k) = ((g * h : IJ) : JH) • omPt k := (hf _ _).symm
      _ = (g : JH) • ((h : JH) • omPt k) := by rw [Subgroup.coe_mul, mul_smul]
      _ = (g : JH) • omPt (f h k) := by rw [hf h k]
      _ = omPt (f g (f h k)) := hf g _
  have hone : ∀ k, f 1 k = k := by
    intro k
    apply omPt_injective
    rw [← hf, Subgroup.coe_one, one_smul]
  have hleft : ∀ (g : IJ) (k : Fin 50), f g⁻¹ (f g k) = k := fun g k => by
    rw [← hmul, inv_mul_cancel, hone]
  have hright : ∀ (g : IJ) (k : Fin 50), f g (f g⁻¹ k) = k := fun g k => by
    rw [← hmul, mul_inv_cancel, hone]
  exact ⟨{ toFun := fun g => ⟨f g, f g⁻¹, hleft g, hright g⟩
           map_one' := Equiv.ext fun k => hone k
           map_mul' := fun g h => Equiv.ext fun k => hmul g h k }, hf⟩

noncomputable def rhoI : IJ →* Equiv.Perm (Fin 50) := exists_rho.choose

theorem rhoI_spec (g : IJ) (k : Fin 50) : (g : JH) • omPt k = omPt (rhoI g k) :=
  exists_rho.choose_spec g k

theorem rhoI_injective : Function.Injective rhoI := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : (g : JH) = 1 := IJ_faithful g.2 (fun k => by rw [rhoI_spec, hg]; rfl)
  exact Subtype.ext this

noncomputable def gI (k : Fin 6) : IJ :=
  ⟨iGen k, by rw [IJ_eq]; exact Subgroup.subset_closure ⟨k, rfl⟩⟩

theorem gI_generate : Subgroup.closure (Set.range gI) = ⊤ := by
  have himg : (IJ.subtype '' Set.range gI : Set JH) = Set.range fun k : Fin 6 => iGen k := by
    ext x
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨gI k, ⟨k, rfl⟩, rfl⟩
  apply Subgroup.map_injective IJ.subtype_injective
  rw [MonoidHom.map_closure, himg, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact IJ_eq.symm

theorem smallPerms_get {s : ℕ} (hs : s < 6) : smallPerms[s]! = iSm[s]! := by
  have h1 : smallPerms[s]! = (smallPermLists[s]!).toArray :=
    map_getElem! List.toArray smallPermLists (by simpa [smallPermLists] using hs)
  rw [h1, smallPermLists_eq, iSm_get hs]

theorem rhoI_gI (k : Fin 6) (x : Fin 50) :
    (rhoI (gI k) x : ℕ) = (smallPerms[(k : ℕ)]!)[(x : ℕ)]! := by
  have hsz : iSm.size = 6 := by simp [iSm, iSmall_size]
  have hs : (k : ℕ) < iSm.size := by rw [hsz]; exact k.2
  obtain ⟨h, hact⟩ := hactI (k : ℕ) hs ⟨(x : ℕ), lt_of_lt_of_eq x.2 fFixed_size.symm⟩
  have e1 : (gI k : JH) • omPt x =
      omPt ⟨(iSm[(k : ℕ)]!)[(x : ℕ)]!, lt_of_lt_of_eq h fFixed_size⟩ := hact
  have e3 := omPt_injective ((rhoI_spec (gI k) x).symm.trans e1)
  have e4 : (rhoI (gI k) x : ℕ) = (iSm[(k : ℕ)]!)[(x : ℕ)]! := congrArg Fin.val e3
  rw [e4, smallPerms_get k.2]

theorem model_IJ : StatedClassicalModel IJ .PSU 3 5 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psu3 gI gI_generate rhoI rhoI_injective rhoI_gI card_IJ
  exact ⟨model_PSU3.1, F25, inferInstance, inferInstance, by rw [F25.card]; norm_num, ⟨e⟩⟩

end CFSG.RankThree.PartOne.HNB
