module

public import CFSG.Quasithin.Background.B15P4Res
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.Vol2.Ch10SecKIK4b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem map_commSub_autOn {J V U' : Subgroup G} [IsMulCommutative ↥V]
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hU'V : U' ≤ V) :
    (commSub (U'.subgroupOf V) (autOn J V)).map V.subtype = ⁅U', J⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro _ ⟨σ, hσ, v, hv, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.1 hσ
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show ((conjAct V g v * v⁻¹ : ↥V) : G) ∈ ⁅U', J⁆
    rw [Subgroup.coe_mul, InternalSec.coe_conjAct_apply, Subgroup.coe_inv]
    have e : (g : G) * v * (g : G)⁻¹ * (v : G)⁻¹ = ⁅(v : G), (g : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (⁅U', J⁆).inv_mem (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hv) hgL)
  · rw [Subgroup.commutator_le]
    intro w hw l hl
    have hwV : w ∈ V := hU'V hw
    have hmem : conjAct V ⟨l, hJN hl⟩ ⟨w, hwV⟩ * (⟨w, hwV⟩ : ↥V)⁻¹ ∈
        commSub (U'.subgroupOf V) (autOn J V) :=
      Subgroup.subset_closure ⟨_, InternalSec.conjAct_mem_autOn hJN hl, ⟨w, hwV⟩,
        Subgroup.mem_subgroupOf.2 hw, rfl⟩
    refine ⟨(conjAct V ⟨l, hJN hl⟩ ⟨w, hwV⟩ * (⟨w, hwV⟩ : ↥V)⁻¹)⁻¹,
      (commSub _ _).inv_mem hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul,
      InternalSec.coe_conjAct_apply]
    rw [commutatorElement_def]
    group

theorem commutator_self_eq {M : Type*} [Group M] {X : Subgroup M} (h : commutator ↥X = ⊤) :
    ⁅X, X⁆ = X := by
  have h2 : (commutator ↥X).map X.subtype = ⁅X, X⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← h2, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_le_left {J V : Subgroup G} (hJN : J ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, J⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp hJN

theorem commutator_commutator_eq {J V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hperf : commutator ↥(autOn J V) = ⊤) :
    ⁅⁅V, J⁆, J⁆ = ⁅V, J⁆ := by
  have : IsMulCommutative ↥V := hV.1
  have h1 := B15P4.commSub_commV_of_perfect (commutator_self_eq hperf)
  rw [commV_autOn_eq1527d hJN] at h1
  have h2 := congrArg (Subgroup.map V.subtype) h1
  rwa [map_commSub_autOn hJN (commutator_le_left hJN),
    Subgroup.map_subgroupOf_eq_of_le (commutator_le_left hJN)] at h2

theorem not_le_centralizer_commutator {J V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hperf : commutator ↥(autOn J V) = ⊤)
    (hJV : ¬ J ≤ Subgroup.centralizer (V : Set G)) :
    ¬ J ≤ Subgroup.centralizer ((⁅V, J⁆ : Subgroup G) : Set G) := by
  intro h
  apply hJV
  have h1 : ⁅⁅V, J⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (h hj) w hw).symm
  rw [commutator_commutator_eq hV hJN hperf, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (h1 hv) j hj).symm

theorem isElemAbelian_of_le {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem le_normalizer_commutator {A B N : Subgroup G} (hA : N ≤ Subgroup.normalizer (A : Set G))
    (hB : N ≤ Subgroup.normalizer (B : Set G)) :
    N ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hh)]

theorem isTwoReducedIn_commutator [Finite G] {H J V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hred : IsTwoReducedIn H V) (hJH : J ≤ H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) (hZ : Subgroup.center ↥(autI hV J) = ⊥)
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G)) (α : ↥J →* ↥(alternatingGroup (Fin 7)))
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥J) (hJperf : ⁅J, J⁆ = J)
    (hJW : ¬ J ≤ Subgroup.centralizer ((⁅V, J⁆ : Subgroup G) : Set G)) :
    IsTwoReducedIn H ⁅V, J⁆ := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hWV : ⁅V, J⁆ ≤ V := commutator_le_left (hJH.trans hHV)
  have hWe : IsElemAbelian 2 ⁅V, J⁆ := isElemAbelian_of_le hWV hV
  have hHW : H ≤ Subgroup.normalizer ((⁅V, J⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hHV hHJ
  refine ⟨hWV.trans hred.1, hHW, hWe, fun D hDH hHD hD2 => ?_⟩
  have hCV : Subgroup.centralizer (V : Set G) ≤
      Subgroup.centralizer ((⁅V, J⁆ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hWV
  set K := (D ⊓ J).subgroupOf J with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk j => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨?_, J.mul_mem (J.mul_mem j.2 hk.2) (J.inv_mem j.2)⟩
    simpa using (Subgroup.mem_normalizer_iff.mp (hHD (hJH j.2)) _).mp hk.1
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  have := hKn.map α hαs
  rcases hs.eq_bot_or_eq_top_of_normal (K.map α) with h | h
  ·
    intro d hd
    refine hCV (mem_centralizer_of_commutator hV hred hHJ h2 hZ (hDH hd) fun j hj => ?_)
    have hdj : ⁅d, j⁆ ∈ D ⊓ J := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h1 : j * d⁻¹ * j⁻¹ ∈ D := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hHD (hJH hj)) _).mp (D.inv_mem hd)
        have e : d * j * d⁻¹ * j⁻¹ = d * (j * d⁻¹ * j⁻¹) := by group
        rw [e]
        exact D.mul_mem hd h1
      · rw [commutatorElement_def]
        have h1 : d * j * d⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hHJ (hDH hd)) j).mp hj
        exact J.mul_mem h1 (J.inv_mem hj)
    have hk : (⟨_, hdj.2⟩ : ↥J) ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf]
      exact hdj
    have h1 : α ⟨_, hdj.2⟩ ∈ K.map α := ⟨_, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2' : (⟨_, hdj.2⟩ : ↥J) ∈ CFSG.pCore 2 ↥J := hαk ▸ MonoidHom.mem_ker.2 h1
    exact hO ((C1Pack.coe_mem_pCoreOf_iff J _).2 h2')
  ·
    exfalso
    have : IsMulCommutative ↥⁅V, J⁆ := hWe.1
    have hJN : J ≤ Subgroup.normalizer ((⁅V, J⁆ : Subgroup G) : Set G) := hJH.trans hHW
    have hp : IsPGroup 2 ↥(autOn J ⁅V, J⁆) := by
      rintro ⟨x, hx⟩
      obtain ⟨g, hgJ, rfl⟩ := Setup.mem_autOn_iff.1 hx
      have h1 : α ⟨g, hgJ⟩ ∈ K.map α := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := h1
      have hk' : (k : G) ∈ D ⊓ J := Subgroup.mem_subgroupOf.1 hk
      have ho : k⁻¹ * ⟨g, hgJ⟩ ∈ CFSG.pCore 2 ↥J := by
        rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
      have hoC := hCV (hO ((C1Pack.coe_mem_pCoreOf_iff J _).2 ho))
      obtain ⟨e, he⟩ := hD2 k hk'.1
      refine ⟨e, Subtype.ext ?_⟩
      have hkN : (k : G) ∈ Subgroup.normalizer ((⁅V, J⁆ : Subgroup G) : Set G) := hJN k.2
      have e1 : g = (k : G) * ((k⁻¹ * ⟨g, hgJ⟩ : ↥J) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      have e2 : conjAct ⁅V, J⁆ g = conjAct ⁅V, J⁆ ⟨k, hkN⟩ := by
        have hmul : g = ⟨k, hkN⟩ * ⟨((k⁻¹ * ⟨g, hgJ⟩ : ↥J) : G), hJN (k⁻¹ * ⟨g, hgJ⟩).2⟩ :=
          Subtype.ext e1
        rw [hmul, map_mul, InternalSec.conjAct_eq_one_of_mem_centralizer
          ⟨((k⁻¹ * ⟨g, hgJ⟩ : ↥J) : G), hJN (k⁻¹ * ⟨g, hgJ⟩).2⟩ hoC, mul_one]
      show (conjAct ⁅V, J⁆ g) ^ 2 ^ e = 1
      rw [e2, ← map_pow]
      apply InternalSec.conjAct_eq_one_of_mem_centralizer
      simpa using he
    have hperf : Group.IsPerfect ↥(autOn J ⁅V, J⁆) := by
      have hsurj := InternalSec.autOnHom_surjective hJN
      have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJperf
      exact Group.IsPerfect.ofSurjective (f := InternalSec.autOnHom hJN) hsurj
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsub : Subsingleton ↥(autOn J ⁅V, J⁆) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
    apply hJW
    intro j hj
    have h1 : conjAct ⁅V, J⁆ ⟨j, hJN hj⟩ = 1 := by
      have hmem : conjAct ⁅V, J⁆ ⟨j, hJN hj⟩ ∈ autOn J ⁅V, J⁆ :=
        InternalSec.conjAct_mem_autOn hJN hj
      have := Subsingleton.elim (⟨_, hmem⟩ : ↥(autOn J ⁅V, J⁆)) 1
      exact congrArg Subtype.val this
    exact (convI_eq_one_iff hWe ⟨j, hJN hj⟩).1 h1

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
