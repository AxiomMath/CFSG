module

public import CFSG.Monster.B.GSide.EdgeQCertMB
public import CFSG.Monster.B.CTIB.Cert
public meta import Certificates.Data.CFSGNative.CTIB.Arith
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import CFSG.Monster.B.GSide.MuFourOmega
public import Certificates.Certificate3132
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3061
public import Certificates.Certificate3079
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate16016
public import Certificates.Certificate16022
public import Certificates.Certificate16951
public meta import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdj
public meta import CFSG.Monster.B.TwoA.Base.GeomNative
public meta import CFSG.Monster.B.TwoA.Par3.MainBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public meta import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public meta import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public meta import CFSG.Monster.B.TwoA.Unitary.Twenty

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.Co2 (v0 decW)
open CFSG.Monster.B.TwoA.Census (NatCert natCertOK ncard_orbit_of_natCertOK)

attribute [local instance] wLeftAction

@[expose] def edgeV :
    Set (Wv v0) := {v | bV Unitary.sigmaW v = 1 ∧ qV v = 0}

theorem card_Wv :
    Nat.card (Wv v0) = 2 ^ 22 := by
  have : Fintype (Wv v0) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
    Co2.finrank_W]

theorem finite_Wv :
    Finite (Wv v0) := inferInstance

theorem ncard_eq_of_translate {S T : Set (Wv v0)} (z : Wv v0) (h : (· + z) '' S = T) :
    S.ncard = T.ncard := by
  rw [← h, Set.ncard_image_of_injective _ (add_left_injective z)]

theorem ncard_bV_sigma_one :
    {v : Wv v0 | bV Unitary.sigmaW v = 1}.ncard = 2 ^ 21 := by
  have hfin := finite_Wv
  obtain ⟨z, hz⟩ : ∃ z, bV Unitary.sigmaW z = 1 := Unitary.exists_bW_sigmaW_eq_one
  have himg : (· + z) '' {v : Wv v0 | bV Unitary.sigmaW v = 0} =
      {v | bV Unitary.sigmaW v = 1} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      show bV Unitary.sigmaW (v + z) = 1
      rw [map_add, hv, hz, zero_add]
    · intro hw
      refine ⟨w + z, ?_, by show w + z + z = w; rw [add_assoc, ZModModule.add_self, add_zero]⟩
      show bV Unitary.sigmaW (w + z) = 0
      rw [map_add, show bV Unitary.sigmaW w = 1 from hw, hz]
      rfl
  have hc := ncard_eq_of_translate z himg
  have hd : Disjoint {v : Wv v0 | bV Unitary.sigmaW v = 0} {v | bV Unitary.sigmaW v = 1} :=
    Set.disjoint_left.2 fun v h0 h1 => zero_ne_one ((show _ = (0 : ZMod 2) from h0).symm.trans h1)
  have hu : {v : Wv v0 | bV Unitary.sigmaW v = 0} ∪ {v | bV Unitary.sigmaW v = 1} = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact Fischer.zmod2_cases _
  have h := Set.ncard_union_eq hd
  rw [hu, Set.ncard_univ, card_Wv, hc] at h
  omega

theorem ncard_edgeV :
    edgeV.ncard = 2 ^ 20 := by
  have hfin := finite_Wv
  have himg : (· + Unitary.sigmaW) '' edgeV =
      {v : Wv v0 | bV Unitary.sigmaW v = 1 ∧ qV v = 1} := by
    have key : ∀ v : Wv v0, bV Unitary.sigmaW v = 1 →
        qV (v + Unitary.sigmaW) = qV v + 1 := fun v hv => by
      rw [qV_add, show qV Unitary.sigmaW = 0 from Unitary.qWv_sigmaW, bV_comm, hv, add_zero]
    have hb : ∀ v : Wv v0, bV Unitary.sigmaW (v + Unitary.sigmaW) = bV Unitary.sigmaW v :=
      fun v => by rw [map_add, bV_self, add_zero]
    ext w
    constructor
    · rintro ⟨v, ⟨hv1, hv0⟩, rfl⟩
      exact ⟨(hb v).trans hv1, by rw [key v hv1, hv0, zero_add]⟩
    · rintro ⟨hw1, hw0⟩
      refine ⟨w + Unitary.sigmaW, ⟨(hb w).trans hw1, ?_⟩, ?_⟩
      · rw [key w hw1, hw0]
        rfl
      · show w + Unitary.sigmaW + Unitary.sigmaW = w
        rw [add_assoc, ZModModule.add_self, add_zero]
  have hc := ncard_eq_of_translate Unitary.sigmaW himg
  have hd : Disjoint edgeV {v : Wv v0 | bV Unitary.sigmaW v = 1 ∧ qV v = 1} :=
    Set.disjoint_left.2 fun v h0 h1 => zero_ne_one (h0.2.symm.trans h1.2)
  have hu : edgeV ∪ {v : Wv v0 | bV Unitary.sigmaW v = 1 ∧ qV v = 1} =
      {v | bV Unitary.sigmaW v = 1} := by
    ext v
    simp only [edgeV, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      rcases Fischer.zmod2_cases (qV v) with h0 | h0
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h0⟩
  have h := Set.ncard_union_eq hd
  rw [hu, ncard_bV_sigma_one, ← hc] at h
  omega

theorem orbitOK_39 :
    CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 39 228096 = true :=
  Certificates.certificate3132.1

theorem orbitOK_35 :
    CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 35 798336 = true :=
  Certificates.certificate3132.2.1

theorem orbitOK_32 :
    CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 32 20736 = true :=
  Certificates.certificate3132.2.2.1

theorem orbit_top_eq {G X : Type*} [Group G] [MulAction G X] (x : X) :
    MulAction.orbit (⊤ : Subgroup G) x = MulAction.orbit G x := by
  refine Set.Subset.antisymm (MulAction.orbit_subgroup_subset _ x) ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩

theorem ncard_usigOrbit_of_cert
    {r : ℕ} {c : NatCert}
    (h : natCertOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) r c = true) :
    (Unitary.usigOrbit (decW r)).ncard = c.pts.size := by
  have h1 := ncard_orbit_of_natCertOK (G := Unitary.Usig) (dec := decW) (gens := Unitary.genUL) h
    (fun k hk a ha => Unitary.genUL_act k hk a ha)
    (fun a b ha hb e => Co2.decW_injective (of_decide_eq_true ha) (of_decide_eq_true hb) e)
  rw [Unitary.closure_genUL, orbit_top_eq] at h1
  rw [Unitary.usigOrbit_eq_orbit]
  exact h1

theorem ncard_usigOrbit_of_orbitOK
    {r n : ℕ}
    (h : CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) r n = true) :
    (Unitary.usigOrbit (decW r)).ncard = n := by
  obtain ⟨hc, hs, -⟩ := CTIB.orbitOK_parts h
  exact (ncard_usigOrbit_of_cert hc).trans hs

@[expose] def orbRep : Fin 4 → ℕ := ![60, 39, 35, 32]

@[expose] def edgeT
    (i : Fin 4) : Set (Wv v0) := Unitary.usigOrbit (decW (orbRep i))

@[expose] def orbSize : Fin 4 → ℕ := ![1408, 228096, 798336, 20736]

theorem edgeT_zero :
    edgeT 0 = Unitary.usigOrbit Unitary.tauW := rfl

theorem ncard_edgeT
    (i : Fin 4) : (edgeT i).ncard = orbSize i := by
  fin_cases i
  · exact Unitary.ncard_usigOrbit_tau
  · exact ncard_usigOrbit_of_orbitOK orbitOK_39
  · exact ncard_usigOrbit_of_orbitOK orbitOK_35
  · exact ncard_usigOrbit_of_orbitOK orbitOK_32

theorem vec_checks : Co2.Native.vectors.contains 2311997 = true ∧
    Co2.Native.vectors.contains 3378621 = true ∧ Co2.Native.vectors.contains 1100455 = true ∧
    Co2.Native.vectors.contains 1050624 = true ∧ Co2.Native.vectors.contains 2099200 = true ∧
    Co2.Native.vectors.contains 3145763 = true ∧ Co2.Native.vectors.contains 12315 = true ∧
    Co2.Native.vectors.contains 12347 = true :=
  Certificates.certificate3132.2.2.2.1

theorem bW_sigma_checks :
    bWcode 6144 39 = 1 ∧ bWcode 6144 35 = 1 ∧ bWcode 6144 32 = 1 :=
  Certificates.certificate3132.2.2.2.2.1

theorem bW_orth_checks :
    bWcode 2311997 3378621 = 0 ∧ bWcode 2311997 1100455 = 0 ∧
    bWcode 3378621 1100455 = 0 ∧ bWcode 1050624 2099200 = 0 ∧ bWcode 1050624 3145763 = 0 ∧
    bWcode 2099200 3145763 = 0 ∧ bWcode 12315 12347 = 0 :=
  Certificates.certificate3132.2.2.2.2.2

theorem qV_of_mem_OmegaW
    {x : Wv v0} (hx : x ∈ Unitary.OmegaW) : qV x = 0 := by
  rw [native_Co2_coset_fiber_data.2.2.2.2.1] at hx
  obtain ⟨k, rfl⟩ := hx
  exact (Unitary.qWv_wAct k Unitary.sigmaW).trans Unitary.qWv_sigmaW

theorem qV_decW_of_vec
    {a : ℕ}
    (h : Co2.Native.vectors.contains a = true) : qV (decW a) = 0 :=
  qV_of_mem_OmegaW (Unitary.decW_mem_OmegaW h)

theorem bV_decW (a b : ℕ) : bV (decW a) (decW b) = (bWcode a b : ZMod 2) := bW_decW a b

theorem qV_decW_two
    {a b : ℕ}
    (ha : Co2.Native.vectors.contains a = true)
    (hb : Co2.Native.vectors.contains b = true) (hab : bWcode a b = 0) :
    qV (decW (a ^^^ b)) = 0 := by
  rw [Co2.decW_xor, qV_add, qV_decW_of_vec ha, qV_decW_of_vec hb, bV_decW, hab]
  rfl

theorem qV_decW_three
    {a b c : ℕ}
    (ha : Co2.Native.vectors.contains a = true)
    (hb : Co2.Native.vectors.contains b = true) (hc : Co2.Native.vectors.contains c = true)
    (hab : bWcode a b = 0) (hac : bWcode a c = 0) (hbc : bWcode b c = 0) :
    qV (decW (a ^^^ b ^^^ c)) = 0 := by
  rw [Co2.decW_xor, qV_add, qV_decW_two ha hb hab, qV_decW_of_vec hc, Co2.decW_xor, map_add,
    LinearMap.add_apply, bV_decW, bV_decW, hac, hbc]
  rfl

theorem bV_sigma_decW
    (r : ℕ) : bV Unitary.sigmaW (decW r) =
    (bWcode 6144 r : ZMod 2) := by
  rw [Unitary.sigmaW_eq_decW, bV_decW]

theorem bV_sigma_decW_one
    {r : ℕ} (h : bWcode 6144 r = 1) : bV Unitary.sigmaW (decW r) =
    1 := by
  rw [bV_sigma_decW, h]
  rfl

theorem orbRep_mem_edgeV
    (i : Fin 4) : decW (orbRep i) ∈ edgeV := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := vec_checks
  obtain ⟨h39, h35, h32⟩ := bW_sigma_checks
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bW_orth_checks
  fin_cases i
  · exact ⟨bV_sigmaW_of_mem_tauOrb (Unitary.mem_usigOrbit_self _),
      qV_of_mem_OmegaW Unitary.tauW_mem_OmegaW⟩
  · refine ⟨bV_sigma_decW_one h39, ?_⟩
    show qV (decW 39) = 0
    rw [show (39 : ℕ) = 2311997 ^^^ 3378621 ^^^ 1100455 by decide]
    exact qV_decW_three v1 v2 v3 b1 b2 b3
  · refine ⟨bV_sigma_decW_one h35, ?_⟩
    show qV (decW 35) = 0
    rw [show (35 : ℕ) = 1050624 ^^^ 2099200 ^^^ 3145763 by decide]
    exact qV_decW_three v4 v5 v6 b4 b5 b6
  · refine ⟨bV_sigma_decW_one h32, ?_⟩
    show qV (decW 32) = 0
    rw [show (32 : ℕ) = 12315 ^^^ 12347 by decide]
    exact qV_decW_two v7 v8 b7

theorem wAct_mem_edgeV
    {u : Kstab v0} (hu : u ∈ Unitary.Usig) {x : Wv v0}
    (hx : x ∈ edgeV) :
    wAct v0 u x ∈ edgeV := by
  have hs : wAct v0 u Unitary.sigmaW = Unitary.sigmaW := hu
  refine ⟨?_, (Unitary.qWv_wAct u x).trans hx.2⟩
  have h := Unitary.bW_wAct u Unitary.sigmaW x
  rw [hs] at h
  exact h.trans hx.1

theorem edgeT_subset
    (i : Fin 4) : edgeT i ⊆ edgeV := by
  rintro _ ⟨u, hu, rfl⟩
  exact wAct_mem_edgeV hu (orbRep_mem_edgeV i)

theorem orbSize_injective : Function.Injective orbSize := by decide

theorem edgeT_disjoint :
    Pairwise (Function.onFun Disjoint edgeT) :=
    by
  intro i j hij
  refine Set.disjoint_left.2 fun y hi hj => hij (orbSize_injective ?_)
  have e1 := Unitary.usigOrbit_eq_of_mem hi
  have e2 := Unitary.usigOrbit_eq_of_mem hj
  rw [← ncard_edgeT i, ← ncard_edgeT j]
  show (Unitary.usigOrbit (decW (orbRep i))).ncard = (Unitary.usigOrbit (decW (orbRep j))).ncard
  rw [← e1, ← e2]

theorem iUnion_edgeT :
    ⋃
    i, edgeT i = edgeV := by
  have hfin := finite_Wv
  refine Set.eq_of_subset_of_ncard_le (Set.iUnion_subset edgeT_subset) ?_ (Set.toFinite _)
  rw [ncard_edgeV, Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) edgeT_disjoint,
    finsum_eq_sum_of_fintype, Fin.sum_univ_four, ncard_edgeT, ncard_edgeT, ncard_edgeT,
    ncard_edgeT]
  decide

end CFSG.Monster.B.GSide
