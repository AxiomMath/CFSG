module

public import CFSG.Quasithin.Background.F9Dual
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Quasithin.EmptyFaithful.S14113Stage
public import CFSG.Quasithin.EmptyFaithful.S146A1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
private theorem le_normalizer_oTwoFstarIn_aux (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oTwoFstarIn H : Set G) := by
  rw [← map_O2Fstar_eq_oTwoFstarIn]
  have : (CFSG.layer (OTwoQuot H)).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (CFSG.generalizedFitting (OTwoQuot H)).Normal := by
    simp only [CFSG.generalizedFitting.eq_sup]
    infer_instance
  exact normalizer_preimH (N := CFSG.generalizedFitting (OTwoQuot H))


omit [Finite G] in
private theorem mem_pCore_of_mem_pCoreOf {H : Subgroup G} {y : ↥H} (hy : (y : G) ∈ pCoreOf 2 H) :
    y ∈ CFSG.Open.pCore 2 ↥H := (CFSG.mem_openPCoreOf_iff_open y).mp hy

omit [Finite G] in
theorem isElemAbelian_conjClosure_of_le_center (hF : HypF91 T V L V₁ Vp H)
    (hcU : conjClosure Vp H ≤ centerOf (omegaOneOf (pCoreOf 2 H))) :
    IsElemAbelian 2 (conjClosure Vp H) := by
  refine HypF91.isElemAbelian_conjClosure_of_forall hF.elemAbelian_Vp fun k hk z hz => ?_
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hyU : y ∈ conjClosure Vp H := HypF91.conjSub_le_conjClosure hk hy
  have hzU : z ∈ conjClosure Vp H := le_conjClosure Vp H hz
  exact Subgroup.mem_centralizer_iff.mp (hcU hzU).2 y (hcU hyU).1


theorem centralizerMod_UC_le_pCoreOf (hF : HypF91 T V L V₁ Vp H)
    (hU : IsElemAbelian 2 (conjClosure Vp H))
    (ha : oTwoFstarIn H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G)) :
    centralizerMod (conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) H
        (conjClosure Vp H) ≤ pCoreOf 2 H := by
  set Q := pCoreOf 2 H with hQ
  set U := conjClosure Vp H with hUdef
  set UC : Subgroup G := U ⊓ Subgroup.centralizer (Q : Set G) with hUC
  set K := centralizerMod UC H U with hK
  set F := oTwoFstarIn H with hFdef
  have hUQ : U ≤ Q := hF.conjClosure_Vp_le_pCoreOf
  have hUCΩ : UC ≤ omegaOneCenterOf Q := fun u hu =>
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUQ hu.1, hu.2, isElemAbelian_pow_eq_one hU hu.1⟩
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Vp H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hHCQ : H ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    hHQ.trans (normalizer_le_normalizer_centralizer Q)
  have hHUC : H ≤ Subgroup.normalizer (UC : Set G) := le_normalizer_inf hHU hHCQ
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_centralizerMod hHUC Subgroup.le_normalizer hHU
  have hHF : H ≤ Subgroup.normalizer (F : Set G) := le_normalizer_oTwoFstarIn_aux H
  have hKH : K ≤ H := centralizerMod_le_left _ _ _
  have hFH : F ≤ H := oTwoFstarIn_le H
  have step1 : ∀ x ∈ K ⊓ F, x ^ 2 ∈ Q := by
    rintro x ⟨hxK, hxF⟩
    have hxH : x ∈ H := hKH hxK
    have hcom : ∀ u ∈ U, x ^ 2 * u * (x ^ 2)⁻¹ = u := by
      intro u hu
      set c : G := x * u * x⁻¹ * u⁻¹ with hc
      have hcUC : c ∈ UC := hxK.2.2 u hu
      have hxu : x * u * x⁻¹ = c * u := by rw [hc]; group
      have hxc : x * c * x⁻¹ = c := by
        have := Subgroup.mem_centralizer_iff.mp (ha hxF) c (hUCΩ hcUC)
        calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [← this]
          _ = c := by group
      have hc2 : c ^ 2 = 1 := isElemAbelian_pow_eq_one hU hcUC.1
      calc x ^ 2 * u * (x ^ 2)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * (c * u) * x⁻¹ := by rw [hxu]
        _ = (x * c * x⁻¹) * (x * u * x⁻¹) := by group
        _ = c * (c * u) := by rw [hxc, hxu]
        _ = c ^ 2 * u := by rw [pow_two]; group
        _ = u := by rw [hc2]; group
    have hQeq : Q = centralizerMod V₁ H U := hF.pCoreOf_eq_centralizerMod
    rw [hQeq]
    refine ⟨H.pow_mem hxH 2, hF.H_normalizes_V₁ (H.pow_mem hxH 2), fun u hu => ?_⟩
    rw [hcom u hu]
    simp
  have step2 : K ⊓ F ≤ Q := by
    refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hKH) (le_normalizer_inf hHK hHF) ?_
    refine isPGroup_two_of_forall fun x hx => ?_
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x ^ 2, step1 x hx⟩
    refine ⟨k + 1, ?_⟩
    have := congrArg Subtype.val hk
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow] at this
    rw [pow_succ', pow_mul]
    exact this
  have step3 : K ≤ F := by
    intro x hxK
    have hxH : x ∈ H := hKH hxK
    have hcent : (QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot H) ∈
        Subgroup.centralizer (CFSG.generalizedFitting (OTwoQuot H) : Set (OTwoQuot H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective y
      have hfF : (f : G) ∈ F := by
        rw [hFdef, ← map_O2Fstar_eq_oTwoFstarIn]
        exact ⟨f, hy, rfl⟩
      have hcomm : x * (f : G) * x⁻¹ * (f : G)⁻¹ ∈ K ⊓ F := by
        refine ⟨?_, ?_⟩
        · have h1 : (f : G) * x⁻¹ * (f : G)⁻¹ ∈ K :=
            (Subgroup.mem_normalizer_iff.mp (hHK (hFH hfF)) x⁻¹).mp (K.inv_mem hxK)
          have : x * (f : G) * x⁻¹ * (f : G)⁻¹ = x * ((f : G) * x⁻¹ * (f : G)⁻¹) := by group
          rw [this]
          exact K.mul_mem hxK h1
        · have h1 : x * (f : G) * x⁻¹ ∈ F :=
            (Subgroup.mem_normalizer_iff.mp (hHF hxH) f).mp hfF
          exact F.mul_mem h1 (F.inv_mem hfF)
      have hmem : (⟨x, hxH⟩ * f * ⟨x, hxH⟩⁻¹ * f⁻¹ : ↥H) ∈ CFSG.Open.pCore 2 ↥H :=
        mem_pCore_of_mem_pCoreOf (step2 hcomm)
      have h1 : (QuotientGroup.mk (⟨x, hxH⟩ * f * ⟨x, hxH⟩⁻¹ * f⁻¹) : OTwoQuot H) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
      have h3 : ⁅(QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot H),
          (QuotientGroup.mk f : OTwoQuot H)⁆ = 1 := by
        rw [commutatorElement_def]
        exact h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    have hgen := CFSG.centralizer_generalizedFitting_le (OTwoQuot H) hcent
    rw [hFdef, ← map_O2Fstar_eq_oTwoFstarIn]
    exact ⟨⟨x, hxH⟩, hgen, rfl⟩
  exact fun x hx => step2 ⟨hx, step3 hx⟩


omit [Finite G] in
private theorem le_normalizer_conjClosure_inf_centralizer (H Vp : Subgroup G) :
    H ≤ Subgroup.normalizer
      ((conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf (le_normalizer_conjClosure Vp H)
    ((le_normalizer_pCoreOf 2 H).trans (normalizer_le_normalizer_centralizer _))

theorem commutator_V_U_comm_Q (hF : HypF91 T V L V₁ Vp H)
    (hcU : conjClosure Vp H ≤ centerOf (omegaOneOf (pCoreOf 2 H)))
    {v u q : G} (hv : v ∈ V) (hu : u ∈ conjClosure Vp H) (hq : q ∈ pCoreOf 2 H) :
    q * (v * u * v⁻¹ * u⁻¹) = (v * u * v⁻¹ * u⁻¹) * q := by
  have hvH : v ∈ H := hF.V_le_H hv
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le hF.sylow_H
  have hu' : v * u * v⁻¹ ∈ conjClosure Vp H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hvH) u).mp hu
  have huinv : u⁻¹ ∈ conjClosure Vp H := (conjClosure Vp H).inv_mem hu
  have hq' : v⁻¹ * q * v ∈ pCoreOf 2 H := by
    have := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hvH)) q).mp hq
    simpa using this
  obtain ⟨w, hw⟩ : ∃ w : G, w = q⁻¹ * (v⁻¹ * q * v) := ⟨_, rfl⟩
  have hq'w : v⁻¹ * q * v = q * w := by rw [hw]; group
  have hwQ : w ∈ pCoreOf 2 H := by
    rw [hw]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hq) hq'
  have hwV : w ∈ V := by
    have h1 : q⁻¹ * v⁻¹ * q⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hF.T_normalizes_V (hQT ((pCoreOf 2 H).inv_mem hq))) v⁻¹).mp
        (V.inv_mem hv)
    have e : w = (q⁻¹ * v⁻¹ * q⁻¹⁻¹) * v := by rw [hw]; group
    rw [e]
    exact V.mul_mem h1 hv
  have hwΩ : w ∈ omegaOneOf (pCoreOf 2 H) := Subgroup.subset_closure ⟨hwQ, hF.elemAbelian.2 _ hwV⟩
  have hwu : w * u = u * w := Subgroup.mem_centralizer_iff.mp (hcU hu).2 _ hwΩ
  have hA : q * (v * u * v⁻¹) * q⁻¹ * (v * u * v⁻¹)⁻¹ = q * u * q⁻¹ * u⁻¹ := by
    have h1 := hF.commutator_conj hvH hq' hu
    have e1 : v * (v⁻¹ * q * v) * v⁻¹ = q := by group
    rw [e1] at h1
    rw [h1, hq'w, hF.commutator_mul_left hq hwQ hu]
    have : w * u * w⁻¹ * u⁻¹ = 1 := by rw [hwu]; group
    rw [this, mul_one]
  have hC1 := hF.commutator_mul_right hq hu huinv
  have hC2 := hF.commutator_mul_right hq hu' huinv
  have h1 : q * (u * u⁻¹) * q⁻¹ * (u * u⁻¹)⁻¹ = 1 := by group
  have h2 : q * (v * u * v⁻¹ * u⁻¹) * q⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹ = 1 := by
    calc _ = (q * (v * u * v⁻¹) * q⁻¹ * (v * u * v⁻¹)⁻¹) * (q * u⁻¹ * q⁻¹ * u⁻¹⁻¹) := hC2
      _ = (q * u * q⁻¹ * u⁻¹) * (q * u⁻¹ * q⁻¹ * u⁻¹⁻¹) := by rw [hA]
      _ = 1 := by rw [← hC1]; exact h1
  calc q * (v * u * v⁻¹ * u⁻¹)
      = (q * (v * u * v⁻¹ * u⁻¹) * q⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹) * (v * u * v⁻¹ * u⁻¹) * q := by
        group
    _ = (v * u * v⁻¹ * u⁻¹) * q := by rw [h2]; group

theorem V_mem_centralizerMod_UC (hF : HypF91 T V L V₁ Vp H)
    (hcU : conjClosure Vp H ≤ centerOf (omegaOneOf (pCoreOf 2 H))) {v : G} (hv : v ∈ V) :
    v ∈ centralizerMod (conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) H
      (conjClosure Vp H) := by
  have hvH : v ∈ H := hF.V_le_H hv
  refine ⟨hvH, le_normalizer_conjClosure_inf_centralizer H Vp hvH, fun u hu => ⟨?_, ?_⟩⟩
  · have hu' : v * u * v⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hvH) u).mp hu
    exact (conjClosure Vp H).mul_mem hu' ((conjClosure Vp H).inv_mem hu)
  · exact Subgroup.mem_centralizer_iff.mpr fun q hq => commutator_V_U_comm_Q hF hcU hv hu hq

theorem conjClosure_V_le_pCoreOf_of_center (hF : HypF91 T V L V₁ Vp H)
    (hcU : conjClosure Vp H ≤ centerOf (omegaOneOf (pCoreOf 2 H)))
    (ha : oTwoFstarIn H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G)) :
    conjClosure V H ≤ pCoreOf 2 H := by
  have hU := isElemAbelian_conjClosure_of_le_center hF hcU
  have hK := centralizerMod_UC_le_pCoreOf hF hU ha
  refine conjClosure_le fun k hk v hv => ?_
  have hvQ : v ∈ pCoreOf 2 H := hK (V_mem_centralizerMod_UC hF hcU hv)
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hk) v).mp hvQ

end S1549C

end CFSG.Quasithin
