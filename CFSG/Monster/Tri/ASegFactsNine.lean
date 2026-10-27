module

public import CFSG.Monster.Tri.ASegFactsCapstone
public import CFSG.Monster.Tri.ASegFactsCo1W
public import CFSG.Monster.GMS.S365Embed

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Monster.GMS.S365 CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem edgeNbrInQ_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hU : Co1FourU)
    (hW : Co1FourW) : EdgeNbrInQ a z₀ := by
  intro z hz u v hzu hzv huQ hvQ huv
  have ha : orderOf a = 2 := hG.1.1
  have hz2 : z * z = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hz).symm.trans hG.2.1)
  have huu := mul_self_of_vertex ha u
  have hvv := mul_self_of_vertex ha v
  have huv' : (u : G) * v = v * u := commute_of_adj' ha huv
  by_cases huvQ : (u : G) * v ∈ leechQ z
  ·
    refine ⟨⟨(u : G) * v, huv.2⟩, huvQ, ?_, ?_⟩
    · refine adj_of_conj (fun h => ?_) ?_
      · exact S36Lines.ne_one_of_isConj ha v.2 (mul_eq_left.1 h)
      · show IsConj a ((u : G) * v * u)
        have e : (u : G) * v * u = v := by
          rw [huv', mul_assoc, huu, mul_one]
        rw [e]
        exact v.2
    · refine adj_of_conj (fun h => ?_) ?_
      · exact S36Lines.ne_one_of_isConj ha u.2 (mul_eq_right.1 h)
      · show IsConj a ((u : G) * v * v)
        have e : (u : G) * v * v = u := by rw [mul_assoc, hvv, mul_one]
        rw [e]
        exact u.2
  ·
    have hl : IsLineTriple a (u : G) v := ⟨u.2, v.2, huv.2⟩
    have huC : (u : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hzu.symm
    have hvC : (v : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hzv.symm
    obtain ⟨q, hqB, hqz, -, huq, hvq, hzq⟩ :=
      exists_embed I hG hU hz hl huv' huC hvC huQ hvQ huvQ
    obtain ⟨L⟩ := exists_leechSystem_of_isConj hG hqB
    have huT : (u : G) ∈ L.typeSet 0 := mem_typeSet_zero_of_isConj I hG hqB L huq u.2
    have hvT : (v : G) ∈ L.typeSet 0 := mem_typeSet_zero_of_isConj I hG hqB L hvq v.2
    have huvT : (u : G) * v ∈ L.typeSet 0 :=
      mem_typeSet_zero_of_isConj I hG hqB L (mul_mem huq hvq) huv.2
    have hzT : z ∈ L.typeSet 2 := mem_typeSet_two_of_isConj I hG hqB L hzq hz hqz.symm
    have hzc : ∀ c : G, IsConj a c → c * z = z * c → c ∉ leechQ z → c ∈ leechQ q →
        z * c ∈ L.typeSet 2 := by
      intro c hc hcz hcQ hcq
      have hB : IsConj z₀ (z * c) := (isConj_mul_iff I hG hz hc hcz).2 hcQ
      refine mem_typeSet_two_of_isConj I hG hqB L (mul_mem hzq hcq) hB ?_
      intro hzcq
      have hv0 : L.vec z + L.vec c = 0 := by
        rw [← L.vec_mul z hzq c hcq, hzcq]
        exact L.vec_z
      have hcc : L.vec c + L.vec c = 0 := funext fun i => CharTwo.add_self_eq_zero _
      have hvv' : L.vec z = L.vec c :=
        calc L.vec z = L.vec z + (L.vec c + L.vec c) := by rw [hcc, add_zero]
          _ = (L.vec z + L.vec c) + L.vec c := by rw [add_assoc]
          _ = L.vec c := by rw [hv0, zero_add]
      have hcT : c ∈ L.typeSet 0 := mem_typeSet_zero_of_isConj I hG hqB L hcq hc
      have h20 : L.vec z ∈ co1Orbit 0 := by rw [hvv']; exact hcT.2
      exact absurd (Leech.eq_of_mem_co1Orbit hzT.2 h20) (by decide)
    have hcomm_uv : (u : G) * v * z = z * (u * v) := by
      calc (u : G) * v * z = u * (v * z) := mul_assoc _ _ _
        _ = u * (z * v) := by rw [← hzv]
        _ = (u * z) * v := (mul_assoc _ _ _).symm
        _ = (z * u) * v := by rw [hzu]
        _ = z * (u * v) := mul_assoc _ _ _
    have hzu' : z * (u : G) ∈ L.typeSet 2 := hzc u u.2 hzu.symm huQ huq
    have hzv' : z * (v : G) ∈ L.typeSet 2 := hzc v v.2 hzv.symm hvQ hvq
    have hzuv' : z * ((u : G) * v) ∈ L.typeSet 2 :=
      hzc _ huv.2 hcomm_uv huvQ (mul_mem huq hvq)
    have hPat : FourPattern (L.vec u) (L.vec v) (L.vec z) := by
      refine ⟨huT.2, hvT.2, ?_, hzT.2, ?_, ?_, ?_⟩
      · rw [← L.vec_mul u huq v hvq]
        exact huvT.2
      · rw [← L.vec_mul z hzq u huq]
        exact hzu'.2
      · rw [← L.vec_mul z hzq v hvq]
        exact hzv'.2
      · rw [add_assoc, ← L.vec_mul u huq v hvq, ← L.vec_mul z hzq _ (mul_mem huq hvq)]
        exact hzuv'.2
    obtain ⟨p, hp, hpu, hpv, hpz⟩ := hW _ _ _ hPat
    obtain ⟨w, hwq, hwp⟩ := L.vec_surj p
    have hwT : w ∈ L.typeSet 0 := ⟨hwq, hwp ▸ hp⟩
    have hwA : IsConj a w := isConj_of_mem_typeSet_zero I hG hqB L hwT
    have hmul : ∀ c : G, c ∈ leechQ q → p + L.vec c ∈ co1Orbit 0 → IsConj a (w * c) := by
      intro c hcq hc
      refine isConj_of_mem_typeSet_zero I hG hqB L ⟨mul_mem hwq hcq, ?_⟩
      rw [L.vec_mul w hwq c hcq, hwp]
      exact hc
    have hwu : IsConj a (w * (u : G)) := hmul u huq hpu
    have hwv : IsConj a (w * (v : G)) := hmul v hvq hpv
    have hwz : IsConj a (w * z) := hmul z hzq hpz
    have hww := S36Lines.sq_eq_one_of_isConj ha hwA
    have hwzc : w * z = z * w :=
      commute_of_mul_self hww hz2 (S36Lines.sq_eq_one_of_isConj ha hwz)
    refine ⟨⟨w, hwA⟩, ?_, ?_, ?_⟩
    · exact mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG hwA hz hwzc hwz
    · exact adj_of_conj (fun (h : w = (u : G)) =>
        S36Lines.ne_one_of_isConj ha hwu (by rw [h]; exact huu)) hwu
    · exact adj_of_conj (fun (h : w = (v : G)) =>
        S36Lines.ne_one_of_isConj ha hwv (by rw [h]; exact hvv)) hwv

end CFSG.Monster.Tri
