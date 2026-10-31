
module

public import CFSG.Sporadic.HNOddCore.InvRow
public import CFSG.Sporadic.HNOddCore.Alt12
public import CFSG.Sporadic.HNOddCore.OrbitX
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem thetaHom_injective :
    Function.Injective thetaHom := fun _ _ h =>
  thetaJ.injective (Subtype.ext h)

theorem card_closure_eq_nat
    {ι : Type*} (g : ι → JH) (hg : ∀ i, g i ∈ HJ) :
    Nat.card (Subgroup.closure (Set.range g)) =
      Nat.card (Subgroup.closure (Set.range fun i => (thetaJ ⟨g i, hg i⟩ : Perm (Fin 12)))) := by
  let g' : ι → HJ := fun i => ⟨g i, hg i⟩
  have h1 : Subgroup.closure (Set.range g) = (Subgroup.closure (Set.range g')).map HJ.subtype := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have h2 : Subgroup.closure (Set.range fun i => (thetaJ ⟨g i, hg i⟩ : Perm (Fin 12))) =
      (Subgroup.closure (Set.range g')).map thetaHom := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [h1, h2, Subgroup.card_map_of_injective HJ.subtype_injective,
    Subgroup.card_map_of_injective thetaHom_injective]

theorem closure_le_HJ {ι : Type*} {g : ι → JH} (hg : ∀ i, g i ∈ HJ) :
    Subgroup.closure (Set.range g) ≤ HJ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact hg i

theorem card_le_of_thetaJ
    {K : Subgroup JH} (hK : K ≤ HJ) {Z : Subgroup (Perm (Fin 12))}
    (hZ : ∀ g (hg : g ∈ K), (thetaJ ⟨g, hK hg⟩ : Perm (Fin 12)) ∈ Z) : Nat.card K ≤ Nat.card Z := by
  have hinj : Function.Injective fun g : K => (⟨thetaJ ⟨g, hK g.2⟩, hZ g g.2⟩ : Z) := by
    intro a b h
    have := congrArg (fun x : Z => (x : Perm (Fin 12))) h
    have h' := thetaHom_injective this
    exact Subtype.ext (Subtype.mk.inj h')
  exact Nat.card_le_card_of_injective _ hinj

def c1G (j : ℕ) : JH := hWordJ InvData.c1Words[j]!

theorem c1G_mem_HJ (j : ℕ) : c1G j ∈ HJ := hWordJ_mem _

theorem c1_spec :
    InvData.c1Words.size = InvData.c1Nat.size ∧ ∀ j < InvData.c1Words.size,
    plettersOK 17 InvData.c1Words[j]! = true ∧
      PRep 12 (natArr InvData.c1Nat[j]!) (natWord InvData.c1Words[j]!) :=
  natAllOK_spec nat_parts.2.2.1

theorem prep_tau : PRep 12 (natArr InvData.nat1) (swap 0 1) := by
  unfold PRep natArr InvData.nat1
  decide

theorem natComm_parts :
    (∀ j < InvData.c1Nat.size, commOK (natArr InvData.c1Nat[j]!) (natArr InvData.nat1) = true) ∧
    (∀ j < InvData.c4Nat.size, commOK (natArr InvData.c4Nat[j]!) (natArr InvData.nat4) = true) ∧
    (∀ j < InvData.c6Nat.size, commOK (natArr InvData.c6Nat[j]!) (natArr InvData.nat6) = true) ∧
    commOK (natArr InvData.nat1) (natArr InvData.nat4) = true := by
  have h := natComm_cert
  unfold natCommChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun j hj => allBelowN_spec h1 hj, fun j hj => allBelowN_spec h2 hj,
    fun j hj => allBelowN_spec h3 hj, h4⟩

theorem fix_cR_smul
    {g : JH} (hg : g ∈ CJ cR) {y : X} (hy : cR • y = y) : cR • (g • y) = g • y := by
  rw [← jR_smul, ← mul_smul, ← (mem_CJ.1 hg), mul_smul, hy]

abbrev K1 : Subgroup JH := Subgroup.closure (Set.range fun s : Fin InvData.s1Perms.size => c1G s)

theorem orbit1_parts : InvData.o1Lists.size = 3 ∧
    InvData.o1Lists.map Array.size = #[1, 945, 210] ∧
    ∀ i < 3, orbitOK InvData.f1Arr.size InvData.s1Perms InvData.o1Lists[i]! = true := by
  have h := orbits_cert
  unfold orbitChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨beq_iff_eq.1 h1, beq_iff_eq.1 h2, fun i hi => allBelowN_spec h3 hi⟩

theorem o1_size
    (i : ℕ) (hi : i < 3) : (InvData.o1Lists[i]!).size = [1, 945, 210][i]! := by
  have hs : (InvData.o1Lists.map Array.size)[i]! = (InvData.o1Lists[i]!).size := by
    rw [getElem!_pos _ i (by simp [orbit1_parts.1, hi]), Array.getElem_map,
      getElem!_pos InvData.o1Lists i (by rw [orbit1_parts.1]; exact hi)]
  rw [← hs, orbit1_parts.2.1]
  interval_cases i <;> rfl

theorem orbitCert1 {i : ℕ} (hi : i < 3) :
    orbitCertOK InvData.f1Arr.size InvData.s1Perms InvData.o1Lists[i]!
      (posArr InvData.f1Arr.size InvData.o1Lists[i]!)
      (orbitRecs InvData.s1Perms InvData.o1Lists[i]!
        (posArr InvData.f1Arr.size InvData.o1Lists[i]!)).1
      (orbitRecs InvData.s1Perms InvData.o1Lists[i]!
        (posArr InvData.f1Arr.size InvData.o1Lists[i]!)).2 = true :=
  orbit1_parts.2.2 i hi

theorem K1_le_HJ : K1 ≤ HJ := closure_le_HJ fun s => c1G_mem_HJ s

theorem disjoint_orbit_of_ncard_ne {G Y : Type*} [Group G] [MulAction G Y] {a b : Y}
    (h : (MulAction.orbit G a).ncard ≠ (MulAction.orbit G b).ncard) :
    Disjoint (MulAction.orbit G a) (MulAction.orbit G b) := by
  rw [Set.disjoint_left]
  intro y hya hyb
  apply h
  have e1 : MulAction.orbit G y = MulAction.orbit G a := MulAction.orbit_eq_iff.2 hya
  have e2 : MulAction.orbit G y = MulAction.orbit G b := MulAction.orbit_eq_iff.2 hyb
  rw [← e1, ← e2]

end CFSG.Sporadic.HNOddCore
