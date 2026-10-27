
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Base

public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Monster.B.Generic.RankThree
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public import Certificates.Certificate3079
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.BData
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import CFSG.Monster.B.TwoA.Unitary.Planes
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import CFSG.Monster.B.Co2.MatrixIso
public import CFSG.Monster.B.Co2.MatrixW
public import Certificates.Certificate3041Base
public import CFSG.Monster.B.Co2.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Generic

attribute [local irreducible] Native.vectors

theorem wvec_kvEquivP
    (k : Kstab v0) (j : Ω) :
    wvec ((kvEquivP k : Equiv.Perm Ω) j) = wAct v0 k⁻¹ (wvec j) := by
  rw [kvEquivP, MulEquiv.trans_apply, agrpEquivPgrp_apply, wvec_theta]
  rfl

theorem OmegaW_eq :
    OmegaW = Set.range wvec := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(kvEquivP k⁻¹ : Equiv.Perm Ω) 0, ?_⟩
    rw [wvec_kvEquivP, inv_inv, ← sigmaW_eq_wvec]
  · rintro ⟨j, rfl⟩
    obtain ⟨p, hp⟩ := MulAction.exists_smul_eq Pgrp (0 : Ω) j
    have h := wvec_kvEquivP (kvEquivP.symm p) 0
    rw [MulEquiv.apply_symm_apply] at h
    refine ⟨(kvEquivP.symm p)⁻¹, ?_⟩
    change wAct v0 (kvEquivP.symm p)⁻¹ sigmaW = wvec j
    rw [sigmaW_eq_wvec, ← h]
    exact congrArg wvec hp

theorem wvec_mem_OmegaW
    (j : Ω) : wvec j ∈ OmegaW := by
  rw [OmegaW_eq]
  exact ⟨j, rfl⟩

theorem ncard_OmegaW :
    OmegaW.ncard = 2300 := by
  rw [OmegaW_eq, ← Set.image_univ, Set.ncard_image_of_injective _ wvec_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem decW_mem_OmegaW
    {a : ℕ}
    (h : Native.vectors.contains a = true) : decW a ∈ OmegaW := by
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 h)
  have hi' : i < 2300 := by rwa [vectors_size] at hi
  rw [← e, ← getElem!_pos Native.vectors i hi]
  exact wvec_mem_OmegaW ⟨i, hi'⟩

theorem shift_codes_ok :
    ∀ j < 891, Native.vectors.contains (6144 ^^^ n6VecArr[j]!) = true ∧
    6144 ^^^ n6VecArr[j]! < 2 ^ 22 ∧ 6144 ^^^ n6VecArr[j]! ≠ 6144 :=
  Certificates.certificate3079.1

theorem tau_codes_ok :
    ∀ i < 1408, Native.vectors.contains o14VecArr[i]! = true ∧
    o14VecArr[i]! ≠ 6144 :=
  Certificates.certificate3079.2.1

theorem tau_shift_disjoint :
    ∀ i < 1408, ∀ j < 891, o14VecArr[i]! ≠ 6144 ^^^ n6VecArr[j]! :=
  Certificates.certificate3079.2.2.1

theorem DeltaW_subset :
    DeltaW ⊆
    OmegaW := by
  rintro _ ⟨j, rfl⟩
  rw [sigmaW_add_n6vec]
  exact decW_mem_OmegaW (shift_codes_ok j j.2).1

theorem sigmaW_notMem_DeltaW :
    sigmaW ∉ DeltaW := by
  rintro ⟨j, hj⟩
  rw [sigmaW_add_n6vec, sigmaW_eq_decW] at hj
  exact (shift_codes_ok j j.2).2.2 (decW_injective (shift_codes_ok j j.2).2.1 (by norm_num) hj)

theorem sigmaW_add_injective :
    Function.Injective fun j : Fin
    891 =>
    sigmaW + n6vec j :=
  fun _ _ h => n6vec_injective (add_left_cancel h)

theorem ncard_DeltaW :
    DeltaW.ncard = 891 := by
  have e : DeltaW = Set.range fun j : Fin 891 => sigmaW + n6vec j := rfl
  rw [e, ← Set.image_univ, Set.ncard_image_of_injective _ sigmaW_add_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

attribute [local instance] wLeftAction

theorem usigOrbit_delta :
    usigOrbit (sigmaW + wFr) = DeltaW := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨j, hj⟩ := (mem_range_n6vec_iff (wAct v0 u wFr)).1 ⟨u, hu, rfl⟩
    exact ⟨j, by rw [wAct_sigmaW_add hu, hj]⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨u, hu, e⟩ := exists_wAct_wFr j
    exact ⟨u, hu, by rw [wAct_sigmaW_add hu, e]⟩

@[expose] def genUL
    (k : ℕ) : Usig := if h : k < 17 then (genU ⟨k, h⟩)⁻¹ else 1

theorem genUL_smul
    {k : ℕ} (hk : k < 17) (x : Wv v0) :
    genUL k • x = wAct v0 (genK ⟨k, hk⟩) x := by
  rw [genUL, dite_eq_left hk]
  change wAct v0 ((genK ⟨k, hk⟩)⁻¹)⁻¹ x = _
  rw [inv_inv]

theorem closure_genUL :
    Subgroup.closure (genUL '' {k | k < 17}) = ⊤ := by
  have e : genUL '' {k | k < 17} = (Set.range genU)⁻¹ := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inv, Set.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, by rw [genUL, dite_eq_left hk, inv_inv]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, k.2, ?_⟩
      rw [genUL, dite_eq_left k.2, hk, inv_inv]
  rw [e, Subgroup.closure_inv, closure_genU]

theorem genUL_act :
    ∀ k < 17, ∀ a, decide (a < 2 ^ 22) = true →
    decW (genAct k a) = genUL k • decW a := by
  intro k hk a _
  rw [genUL_smul hk, wAct_genK_decW]
  rfl

theorem tauCert_ok :
    natCertOK genAct 17 (fun a => decide (a < 2 ^ 22)) 60 tauCert = true :=
  Certificates.certificate3079.2.2.2.1

theorem tauCert_pts : tauCert.pts = o14VecArr :=
  Certificates.certificate3079.2.2.2.2

theorem tauCert_size : tauCert.pts.size = 1408 := by rw
    [tauCert_pts, o14VecArr_size]

theorem tauP_eq (i : ℕ) : tauP i = decW o14VecArr[i]! := by rw
    [tauP, tauCert_pts]

theorem o14VecArr_zero : o14VecArr[0]! = 60 := by
  rw [← tauCert_pts]
  exact natCertOK_root tauCert_ok

theorem tauP_zero : tauP 0 = tauW := by
  rw [tauP_eq, o14VecArr_zero]; rfl

theorem tauP_inj : ∀ i < 1408, ∀ j < 1408, tauP i = tauP j → i = j :=
    by
  intro i hi j hj h
  rw [← tauCert_size] at hi hj
  exact natCertOK_inj tauCert_ok hi hj (decW_injective
    (of_decide_eq_true (natCertOK_valid tauCert_ok hi))
    (of_decide_eq_true (natCertOK_valid tauCert_ok hj)) h)

theorem tauP_closed :
    ∀ i < 1408, ∀ s ∈ genUL ''
    {k | k < 17}, ∃ j <
    1408, tauP j = s • tauP i := by
  intro i hi s hs
  rw [← tauCert_size] at hi ⊢
  exact natCertOK_closed tauCert_ok genUL_act hi hs

theorem tauPar_lt : ∀ i, 0 < i → i < 1408 → tauPar i < i := by
  intro i h0 hi
  rw [← tauCert_size] at hi
  exact (natCertOK_tree tauCert_ok h0 hi).1

theorem tauLab_lt : ∀ i, 0 < i → i < 1408 → tauLab i < 17 := by
  intro i h0 hi
  rw [← tauCert_size] at hi
  exact (natCertOK_tree tauCert_ok h0 hi).2.1

theorem tauP_tree :
    ∀ i, 0 < i → i < 1408 → tauP i
    = genUL (tauLab i)
    • tauP (tauPar i) := by
  intro i h0 hi
  rw [← tauCert_size] at hi
  obtain ⟨hp, hl, e⟩ := natCertOK_tree tauCert_ok h0 hi
  rw [tauP, e, genUL_act _ hl _ (natCertOK_valid tauCert_ok (hp.trans hi))]

theorem orbit_tauW :
    MulAction.orbit Usig tauW = tauP
    ''
    {i | i < 1408} := by
  rw [← tauP_zero]
  exact CFSG.Perm.orbitTree_orbit_eq closure_genUL (by norm_num) tauP_closed tauPar_lt tauP_tree

theorem usigOrbit_tau :
    usigOrbit tauW = {x | ∃ i : Fin 1408, decW o14VecArr[(i : ℕ)]! = x} := by
  rw [usigOrbit_eq_orbit, orbit_tauW]
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, (tauP_eq i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, tauP_eq i⟩

theorem ncard_usigOrbit_tau :
    (usigOrbit tauW).ncard = 1408 :=
    by
  rw [usigOrbit_eq_orbit, ← Nat.card_coe_set_eq, ← tauP_zero]
  exact CFSG.Perm.orbitTree_card_orbit closure_genUL (by norm_num) tauP_inj tauP_closed tauPar_lt
    tauP_tree

theorem natCard_Atau :
    Nat.card Atau = 13063680 := by
  have h := (CFSG.Perm.orbitTree_schreier (genUL '' {k | k < 17}) closure_genUL 1408
    (by norm_num) tauP tauP_inj tauP_closed tauPar tauLab genUL tauPar_lt tauP_tree ⊤
    (fun _ _ _ _ _ _ _ => Subgroup.mem_top _)).2
  rw [natCard_Usig, tauP_zero, stabilizer_tauW] at h
  omega

theorem tauOrb_subset :
    usigOrbit tauW ⊆ OmegaW := by
  rw [usigOrbit_tau]
  rintro _ ⟨i, rfl⟩
  exact decW_mem_OmegaW (tau_codes_ok i i.2).1

theorem tauW_mem_OmegaW :
    tauW ∈ OmegaW := tauOrb_subset
    (mem_usigOrbit_self _)

theorem tau_lt (i : Fin 1408) : o14VecArr[(i : ℕ)]! < 2 ^ 22 := by
  have hi : (i : ℕ) < tauCert.pts.size := by rw [tauCert_size]; exact i.2
  have := of_decide_eq_true (natCertOK_valid tauCert_ok hi)
  rwa [tauCert_pts] at this

theorem sigmaW_notMem_tauOrb :
    sigmaW ∉ usigOrbit tauW := by
  rw [usigOrbit_tau]
  rintro ⟨i, hi⟩
  rw [sigmaW_eq_decW] at hi
  exact (tau_codes_ok i i.2).2 (decW_injective (tau_lt i) (by norm_num) hi)

theorem disjoint_DeltaW_tauOrb :
    Disjoint DeltaW (usigOrbit tauW)
    :=
    by
  rw [usigOrbit_tau, Set.disjoint_left]
  rintro _ ⟨j, rfl⟩ ⟨i, hi⟩
  rw [sigmaW_add_n6vec] at hi
  exact tau_shift_disjoint i i.2 j j.2 (decW_injective (tau_lt i) (shift_codes_ok j j.2).2.1 hi)

theorem OmegaW_eq_union :
    OmegaW = {sigmaW} ∪ DeltaW ∪
    usigOrbit tauW
    := by
  have hsub : {sigmaW} ∪ DeltaW ∪ usigOrbit tauW ⊆ OmegaW :=
    Set.union_subset (Set.union_subset (Set.singleton_subset_iff.2 sigmaW_mem_OmegaW)
      DeltaW_subset) tauOrb_subset
  have hd1 : Disjoint ({sigmaW} : Set (Wv v0)) DeltaW :=
    Set.disjoint_singleton_left.2 sigmaW_notMem_DeltaW
  have hd2 : Disjoint ({sigmaW} ∪ DeltaW) (usigOrbit tauW) :=
    Set.disjoint_union_left.2 ⟨Set.disjoint_singleton_left.2 sigmaW_notMem_tauOrb,
      disjoint_DeltaW_tauOrb⟩
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [Set.ncard_union_eq hd2, Set.ncard_union_eq hd1, Set.ncard_singleton, ncard_DeltaW,
    ncard_usigOrbit_tau, ncard_OmegaW]

theorem usigOrbit_of_mem_OmegaW
    {x : Wv v0} (hx : x ∈ OmegaW) :
    usigOrbit x = {sigmaW} ∨ usigOrbit x = DeltaW ∨ usigOrbit x = usigOrbit tauW := by
  rw [OmegaW_eq_union] at hx
  rcases hx with (hx | hx) | hx
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact .inl usigOrbit_sigma
  · rw [← usigOrbit_delta] at hx ⊢
    exact .inr (.inl (usigOrbit_eq_of_mem hx))
  · exact .inr (.inr (usigOrbit_eq_of_mem hx))

theorem ncard_usigOrbit_of_mem
    {x : Wv v0} (hx : x ∈ OmegaW)
    (hσ : x ≠ sigmaW) :
    (usigOrbit x).ncard = 891 ∧ x ∈ DeltaW ∨ (usigOrbit x).ncard = 1408 ∧ x ∉ DeltaW := by
  rcases usigOrbit_of_mem_OmegaW hx with h | h | h
  · exact absurd (by simpa [h] using mem_usigOrbit_self x) hσ
  · exact .inl ⟨by rw [h, ncard_DeltaW], h ▸ mem_usigOrbit_self x⟩
  · refine .inr ⟨by rw [h, ncard_usigOrbit_tau], fun hd => ?_⟩
    have hx' : x ∈ usigOrbit tauW := h ▸ mem_usigOrbit_self x
    exact Set.disjoint_left.1 disjoint_DeltaW_tauOrb hd hx'

theorem deltaIdx_add
    (j : Fin 891) : deltaIdx
    (sigmaW + n6vec j) = j
    :=
  Function.leftInverse_invFun sigmaW_add_injective j

theorem shiftPlane_add
    (j : Fin 891) : shiftPlane
    (sigmaW + n6vec j)
    = plane (b6Iso j) := by
  rw [shiftPlane, deltaIdx_add]

theorem wAct_sigmaW_add_n6vec
    (u : Usig) (j : Fin 891) :
    wAct v0 u (sigmaW + n6vec j) = sigmaW + n6vec (natIdx u j) := by
  rw [wAct_sigmaW_add u.2, n6vec_natIdx]

theorem shiftPlane_wAct
    (u : Usig) {x : Wv v0}
    (hx : x ∈ DeltaW) :
    wAct v0 u x ∈ DeltaW ∧ shiftPlane (wAct v0 u x) = sigmaAct (shiftPlane x) (phiU u) := by
  obtain ⟨j, rfl⟩ := hx
  rw [wAct_sigmaW_add_n6vec, shiftPlane_add, shiftPlane_add]
  exact ⟨⟨_, rfl⟩, plane_natIdx u j⟩

theorem bijOn_shiftPlane :
    Set.BijOn shiftPlane DeltaW
    {P | IsMaxIso P} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    rw [Set.mem_ofPred_eq, shiftPlane_add]
    exact isMaxIso_plane _
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    rw [shiftPlane_add, shiftPlane_add] at h
    rw [b6Iso_bijective.1 (plane_injective h)]
  · intro P hP
    obtain ⟨p, rfl⟩ := exists_plane_of_isMaxIso hP
    obtain ⟨j, rfl⟩ := b6Iso_bijective.2 p
    exact ⟨_, ⟨j, rfl⟩, shiftPlane_add j⟩

theorem card_OmegaPt :
    Fintype.card OmegaPt =
    2300 := by
  rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, ncard_OmegaW]

@[expose] def tauPt :
    OmegaPt :=
    ⟨tauW, tauW_mem_OmegaW⟩

@[expose] def wvecHom :
    Ω
    →ₑ[(kvEquivP.symm : Pgrp → Kstab v0)]
    OmegaPt where
  toFun j := ⟨wvec j, wvec_mem_OmegaW j⟩
  map_smul' p j := by
    apply Subtype.ext
    change wvec ((p : Equiv.Perm Ω) j) = wAct v0 (kvEquivP.symm p)⁻¹ (wvec j)
    rw [← wvec_kvEquivP, MulEquiv.apply_symm_apply]

theorem wvecHom_bijective :
    Function.Bijective wvecHom := by
  refine ⟨fun i j h => wvec_injective (congrArg Subtype.val h), fun x => ?_⟩
  obtain ⟨j, hj⟩ : (x : Wv v0) ∈ Set.range wvec := by
    rw [← OmegaW_eq]
    exact x.2
  exact ⟨j, Subtype.ext hj⟩

instance isPreprimitive_OmegaPt :
    MulAction.IsPreprimitive
    (Kstab v0)
    OmegaPt :=
  (MulAction.isPreprimitive_congr (f := wvecHom) kvEquivP.symm.surjective
    wvecHom_bijective).1 isPreprimitive_Pgrp

theorem omegaGraph_adj_iff
    (α β : OmegaPt) :
    omegaGraph.Adj α β ↔ Nat.card (MulAction.orbit (MulAction.stabilizer (Kstab v0) α) β) = 891 :=
  suborbitGraph_adj_iff (by norm_num)

theorem omega_suborbits
    (α β : OmegaPt) (h : β ≠ α) :
    Nat.card (MulAction.orbit (MulAction.stabilizer (Kstab v0) α) β) = 891 ∨
      Nat.card (MulAction.orbit (MulAction.stabilizer (Kstab v0) α) β) = 1408 := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Kstab v0) sigmaPt α
  have e := card_orbit_stabilizer_smul g sigmaPt (g⁻¹ • β)
  rw [smul_inv_smul] at e
  rw [e, card_orbit_sigmaPt]
  have hne : ((g⁻¹ • β : OmegaPt) : Wv v0) ≠ sigmaW := by
    intro h'
    apply h
    have h'' : g⁻¹ • β = sigmaPt := Subtype.ext h'
    rw [← h'', smul_inv_smul]
  rcases ncard_usigOrbit_of_mem (g⁻¹ • β).2 hne with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact .inl h1
  · exact .inr h1

theorem adj_sigmaPt_iff
    (x : OmegaPt) : omegaGraph.Adj
    sigmaPt x ↔
    (x : Wv v0) ∈ DeltaW := by
  rw [omegaGraph_adj_iff, card_orbit_sigmaPt]
  by_cases hσ : (x : Wv v0) = sigmaW
  · rw [hσ, usigOrbit_sigma, Set.ncard_singleton]
    exact ⟨fun h => absurd h (by norm_num), fun h => absurd h sigmaW_notMem_DeltaW⟩
  · rcases ncard_usigOrbit_of_mem x.2 hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · rw [h1]
      exact ⟨fun h => absurd h (by norm_num), fun h => absurd h h2⟩

theorem sigmaPt_ne_tauPt :
    sigmaPt ≠ tauPt := by
  intro h
  have h' : sigmaW = tauW := congrArg Subtype.val h
  apply sigmaW_notMem_tauOrb
  rw [h']
  exact mem_usigOrbit_self _

theorem not_adj_sigmaPt_tauPt :
    ¬ omegaGraph.Adj sigmaPt tauPt
    := by
  rw [adj_sigmaPt_iff]
  intro h
  exact Set.disjoint_left.1 disjoint_DeltaW_tauOrb h (mem_usigOrbit_self tauW)

theorem ncard_commonNeighbors_sigmaPt_tauPt :
    (omegaGraph.commonNeighbors sigmaPt tauPt).ncard = 324 := by
  classical
  have h := (rank_three_2300_graph_parameters (H := Kstab v0) (Ω := OmegaPt) card_OmegaPt
    omega_suborbits).2.2.2.2.of_not_adj sigmaPt_ne_tauPt not_adj_sigmaPt_tauPt
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  convert h
  rfl

theorem native_unitary_1408_suborbit_and_plane_shift :
    OmegaW = Set.range wvec ∧ OmegaW.ncard = 2300 ∧ tauW = decW 60 ∧ tauW ∈ OmegaW ∧
    OmegaW = {sigmaW} ∪ DeltaW ∪ usigOrbit tauW ∧
    Disjoint ({sigmaW} : Set (Wv v0)) DeltaW ∧ sigmaW ∉ usigOrbit tauW ∧
    Disjoint DeltaW (usigOrbit tauW) ∧
    ({sigmaW} : Set (Wv v0)).ncard = 1 ∧ DeltaW.ncard = 891 ∧ (usigOrbit tauW).ncard = 1408 ∧
    usigOrbit sigmaW = {sigmaW} ∧ usigOrbit (sigmaW + wFr) = DeltaW ∧
    (∀ x ∈ OmegaW,
      usigOrbit x = {sigmaW} ∨ usigOrbit x = DeltaW ∨ usigOrbit x = usigOrbit tauW) ∧
    usigOrbit tauW = {x | ∃ i : Fin 1408, decW o14VecArr[(i : ℕ)]! = x} ∧
    (∀ j : Fin 891, shiftPlane (sigmaW + n6vec j) = plane (b6Iso j)) ∧
    Set.BijOn shiftPlane DeltaW {P | IsMaxIso P} ∧
    (∀ (u : Usig), ∀ x ∈ DeltaW,
      wAct v0 u x ∈ DeltaW ∧ shiftPlane (wAct v0 u x) = sigmaAct (shiftPlane x) (phiU u)) ∧
    Nat.card Atau = 13063680 ∧
    (∀ x : OmegaPt, omegaGraph.Adj sigmaPt x ↔ (x : Wv v0) ∈ DeltaW) ∧
    ¬ omegaGraph.Adj sigmaPt tauPt ∧ (omegaGraph.commonNeighbors sigmaPt tauPt).ncard = 324 :=
  ⟨OmegaW_eq, ncard_OmegaW, rfl, tauW_mem_OmegaW, OmegaW_eq_union,
    Set.disjoint_singleton_left.2 sigmaW_notMem_DeltaW, sigmaW_notMem_tauOrb,
    disjoint_DeltaW_tauOrb, Set.ncard_singleton _, ncard_DeltaW, ncard_usigOrbit_tau,
    usigOrbit_sigma, usigOrbit_delta, fun _ hx => usigOrbit_of_mem_OmegaW hx, usigOrbit_tau,
    shiftPlane_add, bijOn_shiftPlane, fun u _ hx => shiftPlane_wAct u hx, natCard_Atau,
    adj_sigmaPt_iff, not_adj_sigmaPt_tauPt, ncard_commonNeighbors_sigmaPt_tauPt⟩

end CFSG.Monster.B.TwoA.Unitary
