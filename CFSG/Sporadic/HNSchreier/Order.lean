module

public import CFSG.Sporadic.HNSchreier.Separating
public import CFSG.Sporadic.HNSchreier.ChainCheck
public import CFSG.Sporadic.Schreier.ONCompactSpec
public import CFSG.Certificates.SchreierPointSiftSoundness
public import Certificates.Certificate2096
public import Certificates.Certificate2102
public import Certificates.Certificate2107
public import CFSG.Sporadic.HN
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Sporadic.HN.CertificateBase

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Certificates CFSG.Sporadic.Th.Native

theorem baseArr_size : Data.baseList.toArray.size = 22 := by simp [base_facts.1]

theorem qhn_originalSubgroup : QHN.originalSubgroup = PH := by
  rw [RawSchreierDatum.originalSubgroup, cert_hn_schreier_action_data.2.2.2.1, PH]
  congr 1
  ext x
  simp

theorem qhn_base_set : {b | b ∈ QHN.base.toList} = baseSet := by
  have h22 : QHN.baseCount = 22 := baseFin_length
  ext x
  show x ∈ QHN.base.toList ↔ ∃ k : Fin 22, x = baseX k
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (schreier_vector_mem_toList_iff_get QHN.base x).1 hx
    refine ⟨⟨i.val, by have := i.isLt; omega⟩, Fin.ext ?_⟩
    rw [← hi, cert_hn_schreier_action_data.2.2.2.2.2.2.2.2.1 i]
  · rintro ⟨k, rfl⟩
    apply (schreier_vector_mem_toList_iff_get QHN.base _).2
    refine ⟨⟨k.val, by omega⟩, Fin.ext ?_⟩
    rw [cert_hn_schreier_action_data.2.2.2.2.2.2.2.2.1]

theorem qhn_stab :
    QHN.originalSubgroup ⊓
    fixingSubgroup (Equiv.Perm X) {b | b ∈ QHN.base.toList} = ⊥ := by
  rw [qhn_originalSubgroup, qhn_base_set]
  exact ph_inf_fixing_base

theorem qhn_baseCount : QHN.baseCount = 22 := baseFin_length

theorem levelsOf_qhn_size :
    (levelsOf hnsData.n hnStrongArrs Data.baseList.toArray).size = 22 := by
  rw [CArrays.levelsOf_size, baseArr_size]

theorem qhn_base_take_one :
    {b | b ∈ QHN.base.toList.take 1} = ({x0} : Set X) := by
  ext x
  have h0 : QHN.base.toList.take 1 = [x0] := by
    have hb : QHN.base.toList = baseFin := by simp [QHN, RawSchreierDatum.ofWords]
    rw [hb, baseFin]
    decide
  simp [h0]

theorem card_JH :
    Nat.card JH = 273030912000000 := card_J_cert

theorem card_PH :
    Nat.card PH = 273030912000000 := by
  rw [← Nat.card_congr jEquivP.toEquiv, card_JH]

theorem ph_orbit_x0 (y : X) : ∃ g : PH, g • x0 = y := by
  have := hns_pretransitive
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq JH x0 y
  exact ⟨jEquivP h, by rw [Subgroup.smul_def, Equiv.Perm.smul_def, jEquivP_apply, hh]⟩

theorem card_PH_stab_zero :
    Nat.card (PH ⊓ fixingSubgroup (Equiv.Perm X) {x0} : Subgroup _) = 239500800 := by
  have horb : Nat.card (MulAction.orbit PH x0) = 1140000 := by
    have e : MulAction.orbit PH x0 = Set.univ :=
      Set.eq_univ_of_forall fun y => (ph_orbit_x0 y)
    rw [e, Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hos : Nat.card (MulAction.orbit PH x0) * Nat.card (MulAction.stabilizer PH x0) =
      Nat.card PH := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm]
    exact Subgroup.card_mul_index _
  rw [horb, card_PH] at hos
  have hst : Nat.card (MulAction.stabilizer PH x0) = 239500800 := by omega
  rw [← hst]
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩
      invFun := fun g => ⟨g.1.1, Subgroup.mem_inf.2 ⟨g.1.2, (mem_fixingSubgroup_iff _).2 ?_⟩⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  · exact (mem_fixingSubgroup_iff (Equiv.Perm X)).1 (Subgroup.mem_inf.1 g.2).2 x0 rfl
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact g.2

theorem card_HN :
    Nat.card Blueprint.NativeSporadic.HN = 273030912000000 := by
  rw [Nat.card_congr hnEquivP.toEquiv, card_PH]

theorem fam_hn_certified_order :
    Nat.card PH = 273030912000000 ∧
      Nat.card (PH ⊓ fixingSubgroup (Equiv.Perm X) {x0} : Subgroup _) = 239500800 ∧
      Nat.card Blueprint.NativeSporadic.HN = 273030912000000 ∧ Nat.card JH = 273030912000000 :=
  ⟨card_PH, card_PH_stab_zero, card_HN, card_JH⟩

end CFSG.Sporadic.HNSchreier
