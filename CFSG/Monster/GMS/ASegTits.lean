module

public import CFSG.Monster.GMS.S4FamilyIso
public import CFSG.Monster.GMS.S4FamilyAdjust
public import CFSG.Monster.GMS.S4FamilyModify
public import CFSG.Monster.GMS.S4FamilyAssemble
public import CFSG.Monster.GMS.S4FamilyGroup
public import CFSG.Monster.GMS.S4FamilyTwoB
public import CFSG.Monster.GMS.S4FamilyCases
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate10070
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10077
public import Certificates.Certificate8955
public import CFSG.Monster.GMS.S365
public import CFSG.Monster.GMS.TwoAGraph
public import CFSG.Monster.GMS.ASegDefs
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10043
public import Certificates.Certificate10069
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import CFSG.Monster.GMS.S365Coset
public import Certificates.Certificate10042Base

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Family

structure Comm3 {G : Type*} [Group G] (a y z : G) : Prop where
  aa : a * a = 1
  yy : y * y = 1
  zz : z * z = 1
  ay : a * y = y * a
  az : a * z = z * a
  yz : y * z = z * y

namespace Comm3

variable {G : Type*} [Group G] {a y z : G} (h : Comm3 a y z)
include h

theorem ya : y * a = a * y := h.ay.symm

theorem za : z * a = a * z := h.az.symm

theorem zy : z * y = y * z := h.yz.symm

theorem ya' (x : G) : y * (a * x) = a * (y * x) := by rw [← mul_assoc, h.ya, mul_assoc]

theorem za' (x : G) : z * (a * x) = a * (z * x) := by rw [← mul_assoc, h.za, mul_assoc]

theorem zy' (x : G) : z * (y * x) = y * (z * x) := by rw [← mul_assoc, h.zy, mul_assoc]

theorem aa' (x : G) : a * (a * x) = x := by rw [← mul_assoc, h.aa, one_mul]

theorem yy' (x : G) : y * (y * x) = x := by rw [← mul_assoc, h.yy, one_mul]

theorem zz' (x : G) : z * (z * x) = x := by rw [← mul_assoc, h.zz, one_mul]

end Comm3

macro "comm3_simp " h:term : tactic =>
  `(tactic| simp only [mul_assoc, Comm3.ya $h, Comm3.za $h, Comm3.zy $h, Comm3.ya' $h,
    Comm3.za' $h, Comm3.zy' $h, Comm3.aa $h, Comm3.yy $h, Comm3.zz $h, Comm3.aa' $h,
    Comm3.yy' $h, Comm3.zz' $h, mul_one, one_mul])

section Data

variable {G : Type} [Group G]

structure ASegData (a z₀ y z : G) : Prop where
  isConj_y : IsConj a y
  isConj_ay : IsConj a (a * y)
  isConj_z : IsConj z₀ z
  comm_az : a * z = z * a
  comm_yz : y * z = z * y
  isConj_az : IsConj a (a * z)
  isConj_yz : IsConj a (y * z)
  isConj_ayz : IsConj a (a * y * z)

variable {d₀ : B} {a z₀ y z : G}

theorem ASegData.comm3 (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z) : Comm3 a y z := by
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf hG.1.1
  have hyy : y * y = 1 :=
    mul_self_eq_one_of_orderOf (orderOf_eq_two_of_isConj_a hG D.isConj_y)
  have hzz : z * z = 1 :=
    mul_self_eq_one_of_orderOf (orderOf_eq_two_of_isConj_z₀ hG D.isConj_z)
  have hay : a * y * (a * y) = 1 :=
    mul_self_eq_one_of_orderOf (orderOf_eq_two_of_isConj_a hG D.isConj_ay)
  exact ⟨haa, hyy, hzz, mul_comm_of_mul_self_eq_one haa hyy hay, D.comm_az, D.comm_yz⟩

end Data

section LineConj

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_conj_fixing_z (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀) {z p q p' q' : G}
    (hz : IsConj z₀ z) (hl : IsLineTriple a p q) (hl' : IsLineTriple a p' q')
    (hzp : z * p = p * z) (hzq : z * q = q * z) (hzp' : z * p' = p' * z)
    (hzq' : z * q' = q' * z) (h1 : IsConj a (z * p)) (h2 : IsConj a (z * q))
    (h3 : IsConj a (z * p * q)) (h1' : IsConj a (z * p')) (h2' : IsConj a (z * q'))
    (h3' : IsConj a (z * p' * q')) :
    ∃ g : G, g * p * g⁻¹ = p' ∧ g * q * g⁻¹ = q' ∧ g * z * g⁻¹ = z := by
  have hz2 : orderOf z = 2 := orderOf_eq_two_of_isConj_z₀ hG hz
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf hz2
  have hn : ∀ {w : G}, IsConj a w → ¬ IsConj z₀ w := fun hw h => not_isConj_of_isConj hG hw h
  have he : IsEightExt p q z := ⟨hzz, hzp, hzq, ne_one_of_orderOf hz2,
    fun h => hn hl.1 (h ▸ hz), fun h => hn hl.2.1 (h ▸ hz), fun h => hn hl.2.2 (h ▸ hz)⟩
  have he' : IsEightExt p' q' z := ⟨hzz, hzp', hzq', ne_one_of_orderOf hz2,
    fun h => hn hl'.1 (h ▸ hz), fun h => hn hl'.2.1 (h ▸ hz), fun h => hn hl'.2.2 (h ▸ hz)⟩
  have hc : twoBCount z₀ p q z = 1 := by
    rw [S365.twoBCount_eq_ite]
    simp [hz, hn h1, hn h2, hn h3, -isConj_iff]
  have hc' : twoBCount z₀ p' q' z = 1 := by
    rw [S365.twoBCount_eq_ite]
    simp [hz, hn h1', hn h2', hn h3', -isConj_iff]
  obtain ⟨g, hgp, hgq, hgz⟩ := EL.2 p q z p' q' z hl he hl' he' (hc.trans hc'.symm)
  refine ⟨g, hgp, hgq, ?_⟩
  have hB : IsConj z₀ (g * z * g⁻¹) := hz.trans (isConj_iff.mpr ⟨g, rfl⟩)
  rcases hgz with h | h | h | h
  · exact h
  · exact absurd hB (by rw [h]; exact hn h1')
  · exact absurd hB (by rw [h]; exact hn h2')
  · exact absurd hB (by rw [h]; exact hn h3')

end LineConj

section Elements

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ y z : G}

theorem ASegData.exists_conj_of (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) {p' q' : G} (hl' : IsLineTriple a p' q') (hzp' : z * p' = p' * z)
    (hzq' : z * q' = q' * z) (h1' : IsConj a (z * p')) (h2' : IsConj a (z * q'))
    (h3' : IsConj a (z * p' * q')) :
    ∃ g : G, g * a * g⁻¹ = p' ∧ g * y * g⁻¹ = q' ∧ g * z * g⁻¹ = z := by
  have h := D.comm3 hG
  refine exists_conj_fixing_z EL hG D.isConj_z ⟨IsConj.refl a, D.isConj_y, D.isConj_ay⟩ hl'
    h.za h.zy hzp' hzq' ?_ ?_ ?_ h1' h2' h3'
  · rw [h.za]; exact D.isConj_az
  · rw [h.zy]; exact D.isConj_yz
  · rw [show z * a * y = a * y * z by comm3_simp h]; exact D.isConj_ayz

theorem ASegData.exists_s (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) : ∃ s : G, s * a * s⁻¹ = y ∧ s * y * s⁻¹ = a ∧ s * z * s⁻¹ = z := by
  have h := D.comm3 hG
  refine D.exists_conj_of EL hG
    ⟨D.isConj_y, IsConj.refl a, by rw [h.ya]; exact D.isConj_ay⟩ h.zy h.za ?_ ?_ ?_
  · rw [h.zy]; exact D.isConj_yz
  · rw [h.za]; exact D.isConj_az
  · rw [show z * y * a = a * y * z by comm3_simp h]; exact D.isConj_ayz

theorem ASegData.exists_r₀ (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) :
    ∃ r : G, r * a * r⁻¹ = y ∧ r * y * r⁻¹ = a * y ∧ r * z * r⁻¹ = z := by
  have h := D.comm3 hG
  refine D.exists_conj_of EL hG
    ⟨D.isConj_y, D.isConj_ay, by rw [show y * (a * y) = a by comm3_simp h]⟩ h.zy
    (by comm3_simp h) ?_ ?_ ?_
  · rw [h.zy]; exact D.isConj_yz
  · rw [show z * (a * y) = a * y * z by comm3_simp h]; exact D.isConj_ayz
  · rw [show z * y * (a * y) = a * z by comm3_simp h]; exact D.isConj_az

theorem ASegData.exists_r₁ (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) :
    ∃ r : G, r * a * r⁻¹ = y ∧ r * y * r⁻¹ = a * y * z ∧ r * z * r⁻¹ = z := by
  have h := D.comm3 hG
  refine D.exists_conj_of EL hG
    ⟨D.isConj_y, D.isConj_ayz, by rw [show y * (a * y * z) = a * z by comm3_simp h]; exact
      D.isConj_az⟩ h.zy (by comm3_simp h) ?_ ?_ ?_
  · rw [h.zy]; exact D.isConj_yz
  · rw [show z * (a * y * z) = a * y by comm3_simp h]; exact D.isConj_ay
  · rw [show z * y * (a * y * z) = a by comm3_simp h]

theorem ASegData.exists_t' (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) :
    ∃ t : G, t * a * t⁻¹ = a ∧ t * y * t⁻¹ = a * y ∧ t * z * t⁻¹ = z := by
  have h := D.comm3 hG
  refine D.exists_conj_of EL hG
    ⟨IsConj.refl a, D.isConj_ay, by rw [show a * (a * y) = y by comm3_simp h]; exact
      D.isConj_y⟩ h.za (by comm3_simp h) ?_ ?_ ?_
  · rw [h.za]; exact D.isConj_az
  · rw [show z * (a * y) = a * y * z by comm3_simp h]; exact D.isConj_ayz
  · rw [show z * a * (a * y) = y * z by comm3_simp h]; exact D.isConj_yz

end Elements

section Exists

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem not_isConj_of_twoBCount_eq_one {z₀ x y t : G} (h : twoBCount z₀ x y t = 1)
    (ht : IsConj z₀ t) :
    ¬ IsConj z₀ (t * x) ∧ ¬ IsConj z₀ (t * y) ∧ ¬ IsConj z₀ (t * x * y) := by
  rw [S365.twoBCount_eq_ite] at h
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · by_cases h2 : IsConj z₀ (t * y) <;> by_cases h3 : IsConj z₀ (t * x * y) <;>
      simp [ht, h1, h2, h3, -isConj_iff] at h
  · by_cases h1 : IsConj z₀ (t * x) <;> by_cases h3 : IsConj z₀ (t * x * y) <;>
      simp [ht, h1, h2, h3, -isConj_iff] at h
  · by_cases h1 : IsConj z₀ (t * x) <;> by_cases h2 : IsConj z₀ (t * y) <;>
      simp [ht, h1, h2, h3, -isConj_iff] at h

theorem exists_asegData
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∃ y z : G, ASegData a z₀ y z := by
  obtain ⟨y, z₁, u, hT, hay⟩ := exists_twoClasses_isConj_mul I.sls I.tableV I.leech hG
  have hyA : IsConj a y := hT.isConj_b
  have ha2 : orderOf a = 2 := hG.1.1
  have hy2 : orderOf y = 2 := orderOf_eq_two_of_isConj_a hG hyA
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf ha2
  have hyy : y * y = 1 := mul_self_eq_one_of_orderOf hy2
  have hay2 : orderOf (a * y) = 2 := orderOf_eq_two_of_isConj_a hG hay
  have hl : IsLineTriple a a y := ⟨IsConj.refl a, hyA, hay⟩
  obtain ⟨t, he, hcount⟩ := eightGroupExists_of I hG a y hl 1 (Or.inl rfl)
  obtain ⟨z, hzB, hzmem⟩ := S365.exists_twoB_mem_cosetSet I hG hl he
  have hK := S365.isKlein_of_isLineTriple ha2 hl
  obtain ⟨hza, hzy⟩ := S365.commute_of_mem_cosetSet hK.comm he.2.1 he.2.2.1 hzmem
  have hz2 : orderOf z = 2 := orderOf_eq_two_of_isConj_z₀ hG hzB
  have hcz : twoBCount z₀ a y z = 1 := (S365.twoBCount_eq_of_mem_cosetSet hK hzmem).trans hcount
  obtain ⟨hna, hny, hnay⟩ := not_isConj_of_twoBCount_eq_one hcz hzB
  have hne : ∀ {w : G}, IsConj a w → z ≠ w := fun hw h => not_isConj_of_isConj hG hw (h ▸ hzB)
  have hzay : z * (a * y) = (a * y) * z := by
    rw [← mul_assoc, hza, mul_assoc, hzy, ← mul_assoc]
  have hA : ∀ {w : G}, orderOf w = 2 → ¬ IsConj z₀ w → IsConj a w := fun hw hn =>
    isConj_a_of_not_isConj_z₀ I hG hw hn
  refine ⟨y, z, hyA, hay, hzB, hza.symm, hzy.symm, ?_, ?_, ?_⟩
  · rw [← hza]
    exact hA (orderOf_mul_eq_two hz2 ha2 hza (hne (IsConj.refl a))) hna
  · rw [← hzy]
    exact hA (orderOf_mul_eq_two hz2 hy2 hzy (hne hyA)) hny
  · rw [← hzay, ← mul_assoc]
    exact hA (by rw [mul_assoc]; exact orderOf_mul_eq_two hz2 hay2 hzay (hne hay)) hnay

end Exists

end CFSG.Monster.GMS
