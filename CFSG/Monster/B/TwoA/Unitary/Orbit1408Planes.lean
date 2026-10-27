module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Schreier
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Schreier
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.BData
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.Planes
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PlanesInputs
public import Certificates.Certificate3124
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3175
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate16016
import CFSG.Fischer.F4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Generic

@[expose] def orbitA
    (P : Submodule F4 V6) : Set
    (Submodule F4 V6) :=
  {Q | ∃ a ∈ Atau, sigmaAct P (phiU a) = Q}

@[expose] def ptOrbit (c : ℕ) : Set (Submodule F4 V6) :=
  {P | ∃ i : Fin 693, (i : ℕ) ∈ o14PtOrb[c]! ∧ singPt i = P}

@[expose] def plOrbit (c : ℕ) : Set (Submodule F4 V6) :=
  {P | ∃ p : Fin 891, (p : ℕ) ∈ o14PlOrb[c]! ∧ plane p = P}

@[expose] def singAct :
    UsigIdxAct 693 := ⟨singIdx, singIdx_mul, singIdx_one⟩

@[expose] def natAct :
    UsigIdxAct 891 := ⟨natIdx, natIdx_mul, natIdx_one⟩

theorem singGenArr_eq : ∀ (k : Fin 17) (i : Fin 693),
    (singGenArr[(k : ℕ)]!)[(i : ℕ)]! = (singGen k i : ℕ) :=
  Certificates.certificate3124.1

theorem singAct_gen
    (k : ℕ) (hk : k < 17) (x : Fin 693) :
    (singAct.f (genU ⟨k, hk⟩) x : ℕ) = (singGenArr[k]!)[(x : ℕ)]! := by
  change (singIdx (genU ⟨k, hk⟩) x : ℕ) = _
  rw [singIdx_genU, ← singGenArr_eq ⟨k, hk⟩ x]

theorem natAct_gen
    (k : ℕ) (hk : k < 17) (x : Fin 891) :
    (natAct.f (genU ⟨k, hk⟩) x : ℕ) = (n6PermsArr[k]!)[(x : ℕ)]! := by
  change (natIdx (genU ⟨k, hk⟩) x : ℕ) = _
  rw [natIdx_genU, n6perm_val]

theorem singTree_ok : treeOK singGenArr singT singI 693 = true :=
  Certificates.certificate3124.2.1

theorem natTree_ok : treeOK n6PermsArr natT natI 891 = true :=
  Certificates.certificate3124.2.2.1

theorem singSchreier_ok :
    schreierOK singGenArr singT singI singPart 693 = true :=
  Certificates.certificate3124.2.2.2.1

theorem natSchreier_ok :
    schreierOK n6PermsArr natT natI natPart 891 = true :=
  Certificates.certificate3124.2.2.2.2.1

theorem singSel_ok : ∀ r < o14PtSel.size, o14PtSel[r]!.1 < 1408 ∧ o14PtSel[r]!.2 < 17 := by
  decide +kernel

theorem natSel_ok : ∀ r < o14PlSel.size, o14PlSel[r]!.1 < 1408 ∧ o14PlSel[r]!.2 < 17 := by
  decide +kernel

theorem singCert_ok0 :
    natCertOK (selAct singGenArr singT singI o14PtSel) o14PtSel.size
    (fun x => decide (x < 693)) (o14PtOrb[0]!)[0]! (singCert 0) = true :=
  Certificates.certificate3124.2.2.2.2.2.1

theorem singCert_ok1 :
    natCertOK (selAct singGenArr singT singI o14PtSel) o14PtSel.size
    (fun x => decide (x < 693)) (o14PtOrb[1]!)[0]! (singCert 1) = true :=
  Certificates.certificate3124.2.2.2.2.2.2.1

theorem natCert_ok0 :
    natCertOK (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size
    (fun x => decide (x < 891)) (natOf (o14PlOrb[0]!)[0]!) (natCert 0) = true :=
  Certificates.certificate3124.2.2.2.2.2.2.2.1

theorem natCert_ok1 :
    natCertOK (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size
    (fun x => decide (x < 891)) (natOf (o14PlOrb[1]!)[0]!) (natCert 1) = true :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.1

theorem singCov :
    ∀ y < 693, (singPart[y]! = 0 ∧ (singCert 0).pts.contains y = true) ∨
    (singPart[y]! = 1 ∧ (singCert 1).pts.contains y = true) :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.1

theorem natCov :
    ∀ y < 891, (natPart[y]! = 0 ∧ (natCert 0).pts.contains y = true) ∨
    (natPart[y]! = 1 ∧ (natCert 1).pts.contains y = true) :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.2.1

theorem singPart_spec :
    ∀ i < 693, (i ∈ o14PtOrb[0]! ↔ singPart[i]! = 0) ∧
    (i ∈ o14PtOrb[1]! ↔ singPart[i]! = 1) :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.2.2.1

theorem natPart_spec :
    ∀ j : Fin 891, ((b6Iso j : ℕ) ∈ o14PlOrb[0]! ↔ natPart[(j : ℕ)]! = 0) ∧
    ((b6Iso j : ℕ) ∈ o14PlOrb[1]! ↔ natPart[(j : ℕ)]! = 1) :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem singIdxOrbit
    (x : Fin 693) :
    {y | ∃ a ∈ Atau, singAct.f a x = y} =
      {y : Fin 693 | singPart[(y : ℕ)]! = singPart[(x : ℕ)]!} :=
  idxOrbit_eq singAct singAct_gen singTree_ok singSchreier_ok singSel_ok singCert_ok0
    singCert_ok1 singCov x

theorem natIdxOrbit
    (x : Fin 891) :
    {y | ∃ a ∈ Atau, natAct.f a x = y} =
      {y : Fin 891 | natPart[(y : ℕ)]! = natPart[(x : ℕ)]!} :=
  idxOrbit_eq natAct natAct_gen natTree_ok natSchreier_ok natSel_ok natCert_ok0 natCert_ok1
    natCov x

theorem singPart_lt (y : Fin 693) : singPart[(y : ℕ)]! = 0 ∨
    singPart[(y : ℕ)]! = 1 := by
  rcases singCov y y.2 with ⟨h, -⟩ | ⟨h, -⟩
  · exact .inl h
  · exact .inr h

theorem natPart_lt (y : Fin 891) : natPart[(y : ℕ)]! = 0 ∨
    natPart[(y : ℕ)]! = 1 := by
  rcases natCov y y.2 with ⟨h, -⟩ | ⟨h, -⟩
  · exact .inl h
  · exact .inr h

theorem ptOrbit_eq {c : ℕ} (hc : c < 2) :
    ptOrbit c = singPt '' {y : Fin 693 | singPart[(y : ℕ)]! = c} := by
  ext P
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    interval_cases c
    · exact ((singPart_spec i i.2).1).1 hi
    · exact ((singPart_spec i i.2).2).1 hi
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    interval_cases c
    · exact ((singPart_spec i i.2).1).2 hi
    · exact ((singPart_spec i i.2).2).2 hi

theorem orbitA_singPt
    (i : Fin 693) :
    orbitA (singPt i) = singPt '' {y | ∃ a ∈ Atau, singAct.f a i = y} := by
  ext Q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨singIdx a i, ⟨a, ha, rfl⟩, singPt_singIdx a i⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (singPt_singIdx a i).symm⟩

theorem orbitA_of_mem_ptOrbit
    {c : ℕ} (hc : c < 2)
    {P : Submodule F4 V6} (hP : P ∈ ptOrbit c) :
    orbitA P = ptOrbit c := by
  rw [ptOrbit_eq hc] at hP ⊢
  obtain ⟨i, hi, rfl⟩ := hP
  rw [orbitA_singPt, singIdxOrbit]
  congr 1
  ext y
  exact ⟨fun h => h.trans hi, fun h => h.trans hi.symm⟩

theorem ncard_setOf_fin {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    {y | p y}.ncard = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter_univ]

theorem card_singPart :
    (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 0).card = 126 ∧
    (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 1).card = 567 :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_natPart :
    (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 0).card = 324 ∧
    (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 1).card = 567 :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ncard_ptOrbit {c : ℕ}
    (hc : c < 2) :
    (ptOrbit c).ncard = (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = c).card := by
  rw [ptOrbit_eq hc, Set.ncard_image_of_injective _ singPt_injective, ncard_setOf_fin]

theorem setOf_isSingPt_eq_union :
    {P | IsSingPt P} = ptOrbit 0 ∪
    ptOrbit 1 := by
  rw [setOf_isSingPt, ptOrbit_eq (c := 0) (by norm_num), ptOrbit_eq (c := 1) (by norm_num),
    ← Set.image_union]
  ext P
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, singPart_lt i, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

theorem disjoint_ptOrbit : Disjoint
    (ptOrbit 0) (ptOrbit 1) := by
  rw [ptOrbit_eq (c := 0) (by norm_num), ptOrbit_eq (c := 1) (by norm_num), Set.disjoint_left]
  rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, e⟩
  rw [singPt_injective e] at hj
  rw [Set.mem_ofPred_eq] at hi hj
  omega

theorem plOrbit_eq {c : ℕ}
    (hc : c < 2) :
    plOrbit c = (fun j => plane (b6Iso j)) '' {y : Fin 891 | natPart[(y : ℕ)]! = c} := by
  ext P
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨j, rfl⟩ := b6Iso_bijective.2 p
    refine ⟨j, ?_, rfl⟩
    interval_cases c
    · exact ((natPart_spec j).1).1 hp
    · exact ((natPart_spec j).2).1 hp
  · rintro ⟨j, hj, rfl⟩
    refine ⟨b6Iso j, ?_, rfl⟩
    interval_cases c
    · exact ((natPart_spec j).1).2 hj
    · exact ((natPart_spec j).2).2 hj

theorem orbitA_plane
    (j : Fin 891) :
    orbitA (plane (b6Iso j)) =
      (fun j => plane (b6Iso j)) '' {y | ∃ a ∈ Atau, natAct.f a j = y} := by
  ext Q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨natIdx a j, ⟨a, ha, rfl⟩, plane_natIdx a j⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (plane_natIdx a j).symm⟩

theorem orbitA_of_mem_plOrbit
    {c : ℕ} (hc : c < 2)
    {P : Submodule F4 V6} (hP : P ∈ plOrbit c) :
    orbitA P = plOrbit c := by
  rw [plOrbit_eq hc] at hP ⊢
  obtain ⟨j, hj, rfl⟩ := hP
  rw [orbitA_plane, natIdxOrbit]
  congr 1
  ext y
  exact ⟨fun h => h.trans hj, fun h => h.trans hj.symm⟩

theorem plane_b6Iso_injective :
    Function.Injective fun j => plane
    (b6Iso j) :=
  plane_injective.comp b6Iso_bijective.1

theorem ncard_plOrbit
    {c : ℕ}
    (hc : c < 2) :
    (plOrbit c).ncard = (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = c).card := by
  rw [plOrbit_eq hc, Set.ncard_image_of_injective _ plane_b6Iso_injective, ncard_setOf_fin]

theorem setOf_isMaxIso_eq_union :
    {P | IsMaxIso P} = plOrbit 0 ∪
    plOrbit 1 := by
  rw [plOrbit_eq (c := 0) (by norm_num), plOrbit_eq (c := 1) (by norm_num), ← Set.image_union]
  ext P
  constructor
  · intro hP
    obtain ⟨p, rfl⟩ := exists_plane_of_isMaxIso hP
    obtain ⟨j, rfl⟩ := b6Iso_bijective.2 p
    exact ⟨j, natPart_lt j, rfl⟩
  · rintro ⟨j, -, rfl⟩
    exact isMaxIso_plane _

theorem disjoint_plOrbit :
    Disjoint
    (plOrbit 0) (plOrbit 1) := by
  rw [plOrbit_eq (c := 0) (by norm_num), plOrbit_eq (c := 1) (by norm_num), Set.disjoint_left]
  rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, e⟩
  rw [plane_b6Iso_injective e] at hj
  rw [Set.mem_ofPred_eq] at hi hj
  omega

theorem incid_check : ∀ p : Fin 891,
    ((Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 0 ∧ expand p (singVec i) = singVec i).card,
      (Finset.univ.filter fun i : Fin 693 =>
        singPart[(i : ℕ)]! = 1 ∧ expand p (singVec i) = singVec i).card) =
      if (p : ℕ) ∈ o14PlOrb[0]! then (0, 21) else (6, 15) :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem plList_spec :
    ∀ p < 891, ¬ (p ∈ o14PlOrb[0]! ∧ p ∈ o14PlOrb[1]!) :=
  Certificates.certificate3124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem ncard_incid
    {c : ℕ}
    (hc : c < 2) (p : Fin 891) :
    {Q | Q ∈ ptOrbit c ∧ Q ≤ plane p}.ncard = (Finset.univ.filter fun i : Fin 693 =>
      singPart[(i : ℕ)]! = c ∧ expand p (singVec i) = singVec i).card := by
  have e : {Q | Q ∈ ptOrbit c ∧ Q ≤ plane p} =
      singPt '' {i | singPart[(i : ℕ)]! = c ∧ expand p (singVec i) = singVec i} := by
    rw [ptOrbit_eq hc]
    ext Q
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hQ⟩
      refine ⟨i, ⟨hi, ?_⟩, rfl⟩
      rw [← mem_plane_iff, ← Submodule.span_singleton_le_iff_mem]
      exact hQ
    · rintro ⟨i, ⟨hi, hp⟩, rfl⟩
      refine ⟨⟨i, hi, rfl⟩, ?_⟩
      rw [singPt, Submodule.span_singleton_le_iff_mem, mem_plane_iff]
      exact hp
  rw [e, Set.ncard_image_of_injective _ singPt_injective, ncard_setOf_fin]

theorem smul_sigmaPt
    {a : Usig} : (a : Kstab v0) • sigmaPt = sigmaPt :=
  Subtype.ext (mem_Usig.1 (Usig.inv_mem a.2))

theorem coe_tauPt :
    (tauPt : Wv v0) = tauW := rfl

theorem smul_tauPt
    {a : Usig} (ha : a ∈ Atau) :
    (a : Kstab v0) • tauPt = tauPt := by
  apply Subtype.ext
  rw [coe_smul_OmegaPt, coe_tauPt]
  have h := mem_Atau.1 (Atau.inv_mem ha)
  rw [Subgroup.coe_inv] at h
  exact h

theorem smul_mem_commonNeighbors
    {a : Usig} (ha : a ∈ Atau)
    {x : OmegaPt}
    (hx : x ∈ omegaGraph.commonNeighbors sigmaPt tauPt) :
    (a : Kstab v0) • x ∈ omegaGraph.commonNeighbors sigmaPt tauPt := by
  rw [SimpleGraph.mem_commonNeighbors] at hx ⊢
  have h1 := suborbitGraph_adj_smul (H := Kstab v0) (Ω := OmegaPt) 891 (a : Kstab v0) sigmaPt x
  have h2 := suborbitGraph_adj_smul (H := Kstab v0) (Ω := OmegaPt) 891 (a : Kstab v0) tauPt x
  rw [smul_sigmaPt] at h1
  rw [smul_tauPt ha] at h2
  exact ⟨h1.2 hx.1, h2.2 hx.2⟩

theorem shiftPlane_commonNeighbors :
    shiftPlane '' (Subtype.val '' omegaGraph.commonNeighbors sigmaPt tauPt) = plOrbit 0 := by
  set CN := omegaGraph.commonNeighbors sigmaPt tauPt with hCN
  have hsub : Subtype.val '' CN ⊆ DeltaW := by
    rintro _ ⟨x, hx, rfl⟩
    exact (adj_sigmaPt_iff x).1 ((omegaGraph.mem_commonNeighbors).1 hx).1
  set S := shiftPlane '' (Subtype.val '' CN) with hS
  have hcard : S.ncard = 324 := by
    rw [hS, Set.InjOn.ncard_image (bijOn_shiftPlane.injOn.mono hsub),
      Set.ncard_image_of_injective _ Subtype.val_injective, hCN,
      ncard_commonNeighbors_sigmaPt_tauPt]
  have hmax : S ⊆ plOrbit 0 ∪ plOrbit 1 := by
    rw [← setOf_isMaxIso_eq_union]
    exact (bijOn_shiftPlane.mapsTo.mono_left hsub).image_subset
  have hinv : ∀ P ∈ S, orbitA P ⊆ S := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨a, ha, rfl⟩
    have hxd : (x : Wv v0) ∈ DeltaW := hsub ⟨x, hx, rfl⟩
    refine ⟨_, ⟨((a⁻¹ : Usig) : Kstab v0) • x, smul_mem_commonNeighbors (Atau.inv_mem ha) hx,
      rfl⟩, ?_⟩
    have e : (((a⁻¹ : Usig) : Kstab v0) • x : OmegaPt).val = wAct v0 a x := by
      rw [coe_smul_OmegaPt, Subgroup.coe_inv, inv_inv]
    rw [e, (shiftPlane_wAct a hxd).2]
  have h1 : S ⊆ plOrbit 0 := by
    intro P hP
    rcases hmax hP with h | h
    · exact h
    · exfalso
      have hle : plOrbit 1 ⊆ S := by
        rw [← orbitA_of_mem_plOrbit (c := 1) (by norm_num) h]
        exact hinv P hP
      have := Set.ncard_le_ncard hle (Set.toFinite _)
      rw [hcard, ncard_plOrbit (c := 1) (by norm_num), card_natPart.2] at this
      omega
  refine Set.eq_of_subset_of_ncard_le h1 ?_ (Set.toFinite _)
  rw [hcard, ncard_plOrbit (c := 0) (by norm_num), card_natPart.1]

theorem native_unitary_1408_stabilizer_point_plane_orbits :
    {P | IsSingPt P} = Set.range singPt ∧ Function.Injective singPt ∧
    (∀ c < 2, ∀ P ∈ ptOrbit c, orbitA P = ptOrbit c) ∧
    {P | IsSingPt P} = ptOrbit 0 ∪ ptOrbit 1 ∧ Disjoint (ptOrbit 0) (ptOrbit 1) ∧
    (ptOrbit 0).ncard = 126 ∧ (ptOrbit 1).ncard = 567 ∧
    (∀ c < 2, ∀ P ∈ plOrbit c, orbitA P = plOrbit c) ∧
    {P | IsMaxIso P} = plOrbit 0 ∪ plOrbit 1 ∧ Disjoint (plOrbit 0) (plOrbit 1) ∧
    (plOrbit 0).ncard = 324 ∧ (plOrbit 1).ncard = 567 ∧
    (∀ P ∈ plOrbit 0,
      {Q | Q ∈ ptOrbit 0 ∧ Q ≤ P}.ncard = 0 ∧ {Q | Q ∈ ptOrbit 1 ∧ Q ≤ P}.ncard = 21) ∧
    (∀ P ∈ plOrbit 1,
      {Q | Q ∈ ptOrbit 0 ∧ Q ≤ P}.ncard = 6 ∧ {Q | Q ∈ ptOrbit 1 ∧ Q ≤ P}.ncard = 15) ∧
    shiftPlane '' (Subtype.val '' omegaGraph.commonNeighbors sigmaPt tauPt) = plOrbit 0 := by
  refine ⟨setOf_isSingPt, singPt_injective, fun c hc P hP => orbitA_of_mem_ptOrbit hc hP,
    setOf_isSingPt_eq_union, disjoint_ptOrbit, ?_, ?_,
    fun c hc P hP => orbitA_of_mem_plOrbit hc hP, setOf_isMaxIso_eq_union, disjoint_plOrbit, ?_, ?_,
    ?_, ?_, shiftPlane_commonNeighbors⟩
  · rw [ncard_ptOrbit (c := 0) (by norm_num), card_singPart.1]
  · rw [ncard_ptOrbit (c := 1) (by norm_num), card_singPart.2]
  · rw [ncard_plOrbit (c := 0) (by norm_num), card_natPart.1]
  · rw [ncard_plOrbit (c := 1) (by norm_num), card_natPart.2]
  · rintro _ ⟨p, hp, rfl⟩
    have h := incid_check p
    rw [ite_eq_left hp, Prod.mk.injEq] at h
    rw [ncard_incid (c := 0) (by norm_num), ncard_incid (c := 1) (by norm_num)]
    exact h
  · rintro _ ⟨p, hp, rfl⟩
    have h := incid_check p
    rw [ite_eq_right (fun h0 => plList_spec p p.2 ⟨h0, hp⟩), Prod.mk.injEq] at h
    rw [ncard_incid (c := 0) (by norm_num), ncard_incid (c := 1) (by norm_num)]
    exact h

end CFSG.Monster.B.TwoA.Unitary
