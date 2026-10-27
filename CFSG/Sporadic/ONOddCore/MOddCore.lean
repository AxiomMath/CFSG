module

public import CFSG.Sporadic.ONOddCore.SOddCore
public import CFSG.LocalAnalysis.ComponentInitial.CentralPrimeKernelFixedCore
public import CFSG.LocalAnalysis.ComponentInitial.OddCoreCorrespondence
public import CFSG.Sporadic.ONOddCore.OuterQuot

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open UnbalancedCatalog.EvenCatalog (oddCore_eq_bot_of_mulEquiv)

theorem oddCore_eq_pPrimeCore (G : Type*) [Group G] : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]

theorem fixedSubgroup_map_congr {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    (β : MulAut G) : (fixedSubgroup β).map φ.toMonoidHom = fixedSubgroup (MulAut.congr φ β) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : β x = x := hx
    show MulAut.congr φ β (φ x) = φ x
    simp [MulAut.congr_apply, hx']
  · intro hy
    have hy' : φ (β (φ.symm y)) = y := hy
    refine ⟨φ.symm y, ?_, by simp⟩
    show β (φ.symm y) = φ.symm y
    calc β (φ.symm y) = φ.symm (φ (β (φ.symm y))) := (φ.symm_apply_apply _).symm
      _ = φ.symm y := by rw [hy']

@[expose] def fixedCongr {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (β : MulAut G) :
    fixedSubgroup β ≃* fixedSubgroup (MulAut.congr φ β) :=
  (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (fixedSubgroup_map_congr φ β))

theorem map_eq_of_iff {G : Type*} [Group G] {K : Subgroup G} {φ : MulAut G}
    (h : ∀ x, φ x ∈ K ↔ x ∈ K) : K.map (φ : G →* G) = K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).2 hx
  · intro hy
    exact ⟨φ.symm y, (h _).1 (by simpa using hy), by simp⟩

theorem mem_L_resM
    (φ : MulAut onM) (l : onL) :
    ((φ ⟨l, onL_le_M l.2⟩ : onM) : Equiv.Perm (Fin N)) ∈ onL :=
  Subgroup.mem_subgroupOf.1 ((mem_char_iff LM_characteristic φ _).2 (mem_LM l))

@[expose] def resL
    (φ : MulAut onM) : MulAut onL where
  toFun l := ⟨φ ⟨l, onL_le_M l.2⟩, mem_L_resM φ l⟩
  invFun l := ⟨φ⁻¹ ⟨l, onL_le_M l.2⟩, mem_L_resM φ⁻¹ l⟩
  left_inv l := by
    apply Subtype.ext
    show ((φ⁻¹ ⟨_, _⟩ : onM) : Equiv.Perm (Fin N)) = l
    rw [show (⟨((φ ⟨l, onL_le_M l.2⟩ : onM) : Equiv.Perm (Fin N)), _⟩ : onM) =
      φ ⟨l, onL_le_M l.2⟩ from rfl, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  right_inv l := by
    apply Subtype.ext
    show ((φ ⟨_, _⟩ : onM) : Equiv.Perm (Fin N)) = l
    rw [show (⟨((φ⁻¹ ⟨l, onL_le_M l.2⟩ : onM) : Equiv.Perm (Fin N)), _⟩ : onM) =
      φ⁻¹ ⟨l, onL_le_M l.2⟩ from rfl, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  map_mul' a b := by
    apply Subtype.ext
    show ((φ ⟨((a * b : onL) : Equiv.Perm (Fin N)), onL_le_M (a * b).2⟩ : onM) :
      Equiv.Perm (Fin N)) = ((φ ⟨a, onL_le_M a.2⟩ : onM) : Equiv.Perm (Fin N)) *
        ((φ ⟨b, onL_le_M b.2⟩ : onM) : Equiv.Perm (Fin N))
    rw [← Subgroup.coe_mul, ← map_mul]
    rfl

theorem resL_val
    (φ : MulAut onM) (l : onL) :
    ((resL φ l : onL) : Equiv.Perm (Fin N)) = ((φ ⟨l, onL_le_M l.2⟩ : onM) :
      Equiv.Perm (Fin N)) := Subtype.coe_mk _ _

theorem resL_fix
    {φ : MulAut onM} {m : onM} (hm : φ m = m) (hL : (m : Equiv.Perm (Fin N)) ∈ onL) :
    resL φ ⟨m, hL⟩ = ⟨m, hL⟩ := by
  apply Subtype.ext
  rw [resL_val]
  have e : (⟨((⟨(m : Equiv.Perm (Fin N)), hL⟩ : onL) : Equiv.Perm (Fin N)), onL_le_M hL⟩ : onM) =
    m := rfl
  rw [e, hm]

theorem fix_of_resL
    {φ : MulAut onM} {l : onL} (hl : resL φ l = l) :
    φ ⟨l, onL_le_M l.2⟩ = ⟨l, onL_le_M l.2⟩ := by
  apply Subtype.ext
  rw [← resL_val, hl]

abbrev QL :
    Subgroup onL := onQ.subgroupOf onL

instance QL_normal :
    QL.Normal := by
  rw [QL, ← ker_lToS]
  infer_instance

theorem QL_le_center :
    QL ≤ Subgroup.center onL := by
  intro q hq
  rw [Subgroup.mem_subgroupOf, ← onL_centerIn, CFSG.centerIn, Subgroup.mem_inf] at hq
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hq.2) g g.2)

theorem QL_isPGroup :
    IsPGroup 2 QL := by
  have h : Nat.card QL = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_L).toEquiv, card_onQ]
    norm_num
  exact IsPGroup.of_card h

@[expose] def quotLS :
    onL ⧸ QL ≃* S3 :=
  (QuotientGroup.quotientMulEquivOfEq ker_lToS.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective lToS lToS_surjective)

theorem quotLS_mk
    (a : onL) : quotLS (a : onL ⧸ QL) = lToS a := rfl

theorem map_fixed_resL
    (φ : MulAut onM) :
    (fixedSubgroup (resL φ)).map (Subgroup.inclusion onL_le_M) = fixedSubgroup φ ⊓ LM := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show φ ⟨l, onL_le_M l.2⟩ = ⟨l, onL_le_M l.2⟩
      exact fix_of_resL hl
    · rw [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact l.2
  · intro hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have hL : (x : Equiv.Perm (Fin N)) ∈ onL := Subgroup.mem_subgroupOf.1 hx2
    refine ⟨⟨x, hL⟩, resL_fix (show φ x = x from hx1) hL, Subtype.ext ?_⟩
    rw [Subgroup.coe_inclusion]

@[expose] def fixedLEquiv
    (φ : MulAut onM) : fixedSubgroup (resL φ) ≃* ↥(fixedSubgroup φ ⊓ LM) :=
  (Subgroup.equivMapOfInjective _ _ (Subgroup.inclusion_injective onL_le_M)).trans
    (MulEquiv.subgroupCongr (map_fixed_resL φ))

theorem oddCore_fixed_M
    {γ : MulAut Pv} (hz : γ zP = zP) {γbar : MulAut S3}
    (hcompat : ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
      ((γ ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) → lToS a' = γbar (lToS a))
    (hS : CFSG.oddCore (fixedSubgroup γbar) = ⊥) :
    CFSG.oddCore (fixedSubgroup (resM γ hz)) = ⊥ := by
  set γM := resM γ hz with hγM
  have hQ : ∀ l : onL, resL γM l ∈ QL ↔ l ∈ QL := by
    intro l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resL_val, hγM, resM_val]
    have h := mem_sub_map onQ_le_M Q_characteristic hz (toP ⟨l, onL_le_M l.2⟩)
    rw [coe_toP] at h
    exact h
  have hβZ : QL.map (resL γM : onL →* onL) = QL := map_eq_of_iff hQ
  have hcongr : MulAut.congr quotLS (QuotientGroup.congr QL QL (resL γM) hβZ) = γbar := by
    ext s
    obtain ⟨a, rfl⟩ := lToS_surjective s
    show quotLS (QuotientGroup.congr QL QL (resL γM) hβZ (quotLS.symm (lToS a))) =
      γbar (lToS a)
    rw [← quotLS_mk, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk]
    simp only [quotLS_mk]
    exact hcompat a (resL γM a) ((resL_val γM a).trans (resM_val γ hz _))
  have hcoreS : CFSG.pPrimeCore 2
      (fixedSubgroup (QuotientGroup.congr QL QL (resL γM) hβZ)) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore]
    refine oddCore_eq_bot_of_mulEquiv (fixedCongr quotLS _).symm ?_
    rw [hcongr]
    exact hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : CFSG.pPrimeCore 2 (fixedSubgroup (resL γM)) = ⊥ :=
    central_prime_kernel_fixed_group_prime_complement_core QL QL_le_center QL_isPGroup (resL γM)
      hβZ hcoreS
  have hidx : IsPGroup 2 (onM ⧸ LM) := by
    have h : Nat.card (onM ⧸ LM) = 2 ^ 1 := by
      have h1 := LM.card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onL_le_M).toEquiv, card_onL,
        card_onM] at h1
      rw [← Subgroup.index_eq_card]
      omega
    exact IsPGroup.of_card h
  have key := (normal_prime_power_index_prime_complement_core 2 hidx).1 (fixedSubgroup γM)
  have e := fixedLEquiv γM
  have hML : CFSG.pPrimeCore 2 ↥(fixedSubgroup γM ⊓ LM) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore] at hL ⊢
    exact oddCore_eq_bot_of_mulEquiv e hL
  rw [hML, Subgroup.map_bot] at key
  rw [oddCore_eq_pPrimeCore]
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 key

theorem oddCore_M :
    CFSG.oddCore onM = ⊥ := by
  have h1 : (1 : MulAut Pv) zP = zP := rfl
  have hS : CFSG.oddCore (fixedSubgroup (1 : MulAut S3)) = ⊥ := by
    rw [fixedSubgroup_one]
    exact oddCore_eq_bot_of_mulEquiv Subgroup.topEquiv.symm oddCore_S3
  have h := oddCore_fixed_M h1 (γbar := 1) (fun a a' ha => by
    rw [MulAut.one_apply] at ha ⊢
    rw [show a' = a from Subtype.ext ha]) hS
  have hres : resM 1 h1 = 1 := MulEquiv.ext fun m => Subtype.ext (by
    rw [resM_val, MulAut.one_apply, coe_toP, MulAut.one_apply])
  rw [hres, fixedSubgroup_one] at h
  exact oddCore_eq_bot_of_mulEquiv Subgroup.topEquiv h

end CFSG.Sporadic.ONOddCore
