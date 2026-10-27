module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

theorem eq_top_of_forall_eq_mul_center {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    {K : Subgroup X} (h : ∀ x : X, ∃ k ∈ K, ∃ z ∈ Subgroup.center X, x = k * z) : K = ⊤ := by
  have hc : ∀ z ∈ Subgroup.center X, ∀ g : X, Commute z g := fun z hz g =>
    (Subgroup.mem_center_iff.mp hz g).symm
  rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := h a
  obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := h b
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_commute.mpr (hc z₁ hz₁ _), mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_commute.mpr (hc z₂ hz₂ k₁).symm, mul_one, mul_inv_cancel_right,
    commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)

section Pi

variable {Γ : Type} [Group Γ] {J V : Subgroup Γ} (hV : IsElemAbelian 2 V)
  (hJN : J ≤ Subgroup.normalizer (V : Set Γ))

@[expose] noncomputable def rhoJ : ↥J →* ↥(autI hV J) :=
  (convHom hV J hJN).codRestrict (autI hV J) fun j => by
    rw [← range_convHom hV J hJN]
    exact ⟨j, rfl⟩

theorem rhoJ_surjective : Function.Surjective (rhoJ hV hJN) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hx
  exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

theorem rhoJ_eq_one_iff (j : ↥J) :
    rhoJ hV hJN j = 1 ↔ (j : Γ) ∈ Subgroup.centralizer (V : Set Γ) := by
  rw [← convI_eq_one_iff hV ⟨j, hJN j.2⟩]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

variable {hV hJN} in
theorem pCore_le_ker_rhoJ (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ)) :
    CFSG.pCore 2 ↥J ≤ (rhoJ hV hJN).ker := fun j hj => by
  rw [MonoidHom.mem_ker, rhoJ_eq_one_iff]
  exact hO ((C1Pack.coe_mem_pCoreOf_iff J j).mpr hj)

@[expose] noncomputable def piJ (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ)) :
    ↥J ⧸ CFSG.pCore 2 ↥J →* ↥(autI hV J) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥J) (rhoJ hV hJN) (pCore_le_ker_rhoJ hO)

variable (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ))

theorem piJ_surjective : Function.Surjective (piJ hV hJN hO) := by
  intro x
  obtain ⟨j, rfl⟩ := rhoJ_surjective hV hJN x
  exact ⟨QuotientGroup.mk j, rfl⟩

theorem piJ_mk_eq_one_iff (j : ↥J) :
    piJ hV hJN hO (QuotientGroup.mk j) = 1 ↔ (j : Γ) ∈ Subgroup.centralizer (V : Set Γ) :=
  rhoJ_eq_one_iff hV hJN j

theorem piJ_mem_autI {L : Subgroup Γ} {y : ↥J ⧸ CFSG.pCore 2 ↥J} (hy : y ∈ modO2Image J L) :
    ((piJ hV hJN hO y : ↥(autI hV J)) : MulAut (IntMod V hV)) ∈ autI hV L := by
  obtain ⟨j, hj, rfl⟩ := hy
  have hj' : (j : Γ) ∈ L := hj
  exact convI_mem_autI hV hj' (hJN j.2)

end Pi

theorem autI_eq_of_sup {Γ : Type} [Group Γ] [Finite Γ] {J V : Subgroup Γ}
    (hV : IsElemAbelian 2 V) (hJN : J ≤ Subgroup.normalizer (V : Set Γ))
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ))
    (hJq : CFSG.IsQuasisimple ↥(autI hV J)) {L : Subgroup Γ}
    (hLJ : L ≤ J) {N : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} [N.Normal] (hNs : Group.IsSolvable ↥N)
    (hsup : modO2Image J L ⊔ N = ⊤) : autI hV L = autI hV J := by
  set π := piJ hV hJN hO with hπ
  have hπs : Function.Surjective π := piJ_surjective hV hJN hO
  have hNn : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπs
  have hNc : N.map π ≤ Subgroup.center ↥(autI hV J) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq hNn with h | h
    · exfalso
      have hs : Group.IsSolvable ↥(N.map π) :=
        Group.isSolvable_of_surjective (π.subgroupMap_surjective N)
      let e : ↥(N.map π) ≃* ↥(autI hV J) := (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
      have hsJ : Group.IsSolvable ↥(autI hV J) :=
        Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
      have : Group.IsPerfect ↥(autI hV J) := hJq.1
      have : Nontrivial ↥(autI hV J) := CFSG.LocalCores.isQuasisimple_nontrivial hJq
      exact Group.IsPerfect.not_isSolvable _ hsJ
    · exact h
  have hK := eq_top_of_forall_eq_mul_center (K := (autI hV L).subgroupOf (autI hV J)) hJq.1
    (fun x => by
      obtain ⟨y, rfl⟩ := hπs x
      have hy : y ∈ ((modO2Image J L ⊔ N : Subgroup _) : Set _) := by rw [hsup]; trivial
      rw [Subgroup.mul_normal] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      exact ⟨π a, by rw [Subgroup.mem_subgroupOf]; exact piJ_mem_autI hV hJN hO ha, π b,
        hNc ⟨b, hb, rfl⟩, map_mul π a b⟩)
  refine le_antisymm (autI_mono hV hLJ) fun x hx => ?_
  have : (⟨x, hx⟩ : ↥(autI hV J)) ∈ (autI hV L).subgroupOf (autI hV J) := by rw [hK]; trivial
  exact this

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
