module

public import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenNormalizer
public import CFSG.RankThree.GF2n.Stroth78.Sec2FourLower
public import CFSG.RankThree.GF2n.Stroth78.Sec2QaIndex

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem z_mul_self_eq_one (S : Setting z E F) : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rw [S.hyp.orderOf_z] at h
  simpa [pow_two] using h

theorem a_mul_self_eq_one (S : Setting z E F) {a : G} (hconj : IsConj z a) :
    a * a = 1 := by
  have h := sq_eq_one_of_isConj S hconj
  simpa [pow_two] using h

theorem mul_comm_z_of_mem_Q (S : Setting z E F) {a : G} (haQ : a ∈ Q z) :
    a * z = z * a :=
  Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (z_mem_ZQ S)).2 a haQ

theorem mem_QaOf_mul_z_of_mem_QaOf (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) : z ∈ QaOf (a * z) := by
  obtain ⟨x, hxQ, hx⟩ := exists_conj_eq_mul_z S haQ haZ
  have hxz : x * z * x⁻¹ = z := by
    have h1 : z * x = x * z :=
      Subgroup.mem_centralizer_iff.mp (Q_le_H S hxQ) z (Set.mem_singleton z)
    calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [h1]
      _ = z := by group
  have hmap : (QaOf a).map (MulAut.conj x).toMonoidHom = QaOf (a * z) := by
    rw [map_conj_QaOf a x, hx]
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨z, hza, by simpa [MulAut.conj_apply] using hxz⟩

theorem mem_QaOf_mul_z_of_mem_Q (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) : a ∈ QaOf (a * z) := by
  have hz_mem : z ∈ QaOf (a * z) := mem_QaOf_mul_z_of_mem_QaOf S haQ haZ hza
  have haz_mem : a * z ∈ QaOf (a * z) := mem_QaOf_self (a * z)
  have hz2 : z * z = 1 := z_mul_self_eq_one S
  have haeq : (a * z) * z = a := by rw [mul_assoc, hz2, mul_one]
  let K : Subgroup G := QaOf (a * z)
  have haz_mem' : a * z ∈ K := haz_mem
  have hz_mem' : z ∈ K := hz_mem
  have hprod : (a * z) * z ∈ K := K.mul_mem haz_mem' hz_mem'
  rwa [haeq] at hprod

theorem mul_z_not_mem_ZQ (S : Setting z E F) {a : G} (haZ : a ∉ ZQ z) :
    a * z ∉ ZQ z := by
  intro h
  apply haZ
  have hz2 : z * z = 1 := z_mul_self_eq_one S
  have hmem : (a * z) * z ∈ ZQ z := (ZQ z).mul_mem h (z_mem_ZQ S)
  simpa [mul_assoc, hz2] using hmem

theorem not_mem_centerIn_QaOf_mul_z (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) :
    a ∉ centerIn (QaOf (a * z)) := by
  intro ha
  have hbQ : a * z ∈ Q z := (Q z).mul_mem haQ (z_mem_Q S)
  have hconj_b : IsConj z (a * z) := hconj.trans (isConj_mul_z S haQ haZ)
  have hbZ : a * z ∉ ZQ z := mul_z_not_mem_ZQ S haZ
  have hzb : z ∈ QaOf (a * z) := mem_QaOf_mul_z_of_mem_QaOf S haQ haZ hza
  have hzZ : z ∉ centerIn (QaOf (a * z)) :=
    z_not_mem_centerIn_Qa S hbQ hconj_b hbZ hzb
  have hbZc : a * z ∈ centerIn (QaOf (a * z)) :=
    mem_centerIn_QaOf_of_isConj S hconj_b
  have haz : a * z = z * a := mul_comm_z_of_mem_Q S haQ
  have ha2 : a * a = 1 := a_mul_self_eq_one S hconj
  have hz_eq : (a * z) * a = z := by
    calc (a * z) * a = a * (z * a) := by group
      _ = a * (a * z) := by rw [← haz]
      _ = (a * a) * z := by group
      _ = z := by rw [ha2, one_mul]
  let K : Subgroup G := centerIn (QaOf (a * z))
  have hbZc' : a * z ∈ K := hbZc
  have ha' : a ∈ K := ha
  have hprod : (a * z) * a ∈ K := K.mul_mem hbZc' ha'
  have hzK : z ∈ K := by rwa [hz_eq] at hprod
  exact hzZ hzK

theorem exists_conj_eq_z_of_mem_QaOf_mul_z (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) :
    ∃ g ∈ QaOf (a * z), g * a * g⁻¹ = z := by
  classical
  have hbQ : a * z ∈ Q z := (Q z).mul_mem haQ (z_mem_Q S)
  have hconj_b : IsConj z (a * z) := hconj.trans (isConj_mul_z S haQ haZ)
  have hbZ : a * z ∉ ZQ z := mul_z_not_mem_ZQ S haZ
  have hzb : z ∈ QaOf (a * z) := mem_QaOf_mul_z_of_mem_QaOf S haQ haZ hza
  have haQb : a ∈ QaOf (a * z) := mem_QaOf_mul_z_of_mem_Q S haQ haZ hza
  have haZb : a ∉ centerIn (QaOf (a * z)) :=
    not_mem_centerIn_QaOf_mul_z S haQ hconj haZ hza
  have hderiv : ⁅QaOf (a * z), QaOf (a * z)⁆ = Subgroup.zpowers (a * z) :=
    QaOf_deriv_eq_zpowers S hconj_b
  have hb2 : (a * z) * (a * z) = 1 := by
    have haz : a * z = z * a := mul_comm_z_of_mem_Q S haQ
    have ha2 : a * a = 1 := a_mul_self_eq_one S hconj
    have hz2 : z * z = 1 := z_mul_self_eq_one S
    calc (a * z) * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [← haz]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2, mul_one]
  have hb1 : a * z ≠ 1 := by
    intro h
    have haz_eq : a = z := by
      calc a = (a * z) * z := by rw [mul_assoc, z_mul_self_eq_one S, mul_one]
        _ = 1 * z := by rw [h]
        _ = z := one_mul z
    apply haZ
    rw [haz_eq]
    exact z_mem_ZQ S
  have hb2' : (a * z) ^ 2 = 1 := by simpa [pow_two] using hb2
  have hbord : orderOf (a * z) = 2 := orderOf_eq_prime hb2' hb1
  have hex : ∃ g ∈ QaOf (a * z), ⁅g, a⁆ = a * z := by
    by_contra h
    have h' : ∀ g ∈ QaOf (a * z), ⁅g, a⁆ ≠ a * z := fun g hg hgz => h ⟨g, hg, hgz⟩
    apply haZb
    refine Subgroup.mem_inf.mpr ⟨haQb, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hycomm : ⁅y, a⁆ ∈ Subgroup.zpowers (a * z) := by
      have hmem : ⁅y, a⁆ ∈ ⁅QaOf (a * z), QaOf (a * z)⁆ :=
        Subgroup.commutator_mem_commutator hy haQb
      rwa [hderiv] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hycomm
    rcases zpow_eq_one_or_self_of_orderOf_eq_two hbord k with h1 | h1
    · exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [← hk, h1])
    · exact absurd (by rw [← hk, h1]) (h' y hy)
  obtain ⟨g, hgQ, hgcomm⟩ := hex
  refine ⟨g, hgQ, ?_⟩
  have haz : a * z = z * a := mul_comm_z_of_mem_Q S haQ
  have ha2 : a * a = 1 := a_mul_self_eq_one S hconj
  calc g * a * g⁻¹ = ⁅g, a⁆ * a := by rw [commutatorElement_def]; group
    _ = (a * z) * a := by rw [hgcomm]
    _ = a * (z * a) := by group
    _ = a * (a * z) := by rw [← haz]
    _ = (a * a) * z := by group
    _ = z := by rw [ha2, one_mul]

theorem conj_z_eq_of_conj_a_eq (S : Setting z E F) {a g : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hgQaz : g ∈ QaOf (a * z))
    (hga : g * a * g⁻¹ = z) : g * z * g⁻¹ = a := by
  have hconj_b : IsConj z (a * z) := hconj.trans (isConj_mul_z S haQ haZ)
  have hgcent : g * (a * z) * g⁻¹ = a * z := by
    have hcent : a * z ∈ Subgroup.centralizer (QaOf (a * z) : Set G) :=
      (Subgroup.mem_inf.mp (mem_centerIn_QaOf_of_isConj S hconj_b)).2
    have hcomm : g * (a * z) = (a * z) * g :=
      Subgroup.mem_centralizer_iff.mp hcent g hgQaz
    calc g * (a * z) * g⁻¹ = (a * z) * g * g⁻¹ := by rw [hcomm]
      _ = a * z := by group
  have ha2 : a * a = 1 := a_mul_self_eq_one S hconj
  have haz : a * z = z * a := mul_comm_z_of_mem_Q S haQ
  have hz_eq : z = (a * z) * a := by
    rw [haz, mul_assoc, ha2, mul_one]
  calc g * z * g⁻¹ = g * ((a * z) * a) * g⁻¹ := by
        conv_lhs => rw [hz_eq]
    _ = (g * (a * z) * g⁻¹) * (g * a * g⁻¹) := by group
    _ = (a * z) * z := by rw [hgcent, hga]
    _ = a := by rw [mul_assoc, z_mul_self_eq_one S, mul_one]

theorem map_conj_Q_eq_QaOf (S : Setting z E F) {a g : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hgQaz : g ∈ QaOf (a * z))
    (hga : g * a * g⁻¹ = z) :
    (Q z).map (MulAut.conj g).toMonoidHom = QaOf a := by
  have hgz := conj_z_eq_of_conj_a_eq S haQ hconj haZ hgQaz hga
  rw [map_conj_QaOf z g, hgz]

theorem map_conj_QaOf_eq_Q {a g : G} (hga : g * a * g⁻¹ = z) :
    (QaOf a).map (MulAut.conj g).toMonoidHom = Q z := by
  rw [map_conj_QaOf a g, hga]

theorem map_conj_CQ_eq_L0 (S : Setting z E F) {a g : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hgQaz : g ∈ QaOf (a * z))
    (hga : g * a * g⁻¹ = z) :
    ((Q z ⊓ Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom) =
      QaOf a ⊓ H z := by
  have hgz := conj_z_eq_of_conj_a_eq S haQ hconj haZ hgQaz hga
  exact map_conj_CQ_eq_centerIn_QaOf hgz hga

theorem map_conj_L0_eq_CQ (S : Setting z E F) {a g : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hgQaz : g ∈ QaOf (a * z))
    (hga : g * a * g⁻¹ = z) :
    ((QaOf a ⊓ H z).map (MulAut.conj g).toMonoidHom) =
      Q z ⊓ Subgroup.centralizer ({a} : Set G) := by
  have hgz := conj_z_eq_of_conj_a_eq S haQ hconj haZ hgQaz hga
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_QaOf a g, hga,
    ← centralizer_map_conj z g, hgz]

end CFSG.RankThree.GF2n.Stroth78
