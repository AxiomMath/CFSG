module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Defs
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem caseB_L3 {G : Type} [Group G] [Finite G] {N T E : Subgroup G} (hN : N.Normal) {p : ℕ}
    (hp5 : 5 < p) (h : L3FusFacts N p) (hTs : IsSylowTwoOf T (N ⊔ T)) {y z : G} (hyN : y ∈ N)
    (hy5 : orderOf y = 5) (hzN : z ∈ N) (hz2 : orderOf z = 2) (hyK : y ∈ leviOfL3 N z)
    (hTy : T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G)) (hET : E ≤ T)
    (hEa : IsElemAbelian 2 E) (hE1 : E ≠ ⊥)
    (hEC : E ≤ Subgroup.centralizer (leviOfL3 N z : Set G)) :
    ∃ n ∈ N, E.map (MulAut.conj n).toMonoidHom ≤ T ∧
      ¬ E.map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer ({y} : Set G) := by
  have hsq : ∀ v ∈ E, v = 1 ∨ v = z := fun v hv =>
    h.factB z hzN hz2 v (by rw [← pow_two]; exact hEa.2 v hv) (hEC hv)
  have hzE : z ∈ E := by
    obtain ⟨⟨v, hvE⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have hv1' : v ≠ 1 := fun e => hv1 (Subtype.ext e)
    rcases hsq v hvE with e | e
    · exact absurd e hv1'
    · rw [← e]
      exact hvE
  have hEz : E = Subgroup.zpowers z := by
    apply le_antisymm
    · intro v hv
      rcases hsq v hv with e | e
      · rw [e]
        exact Subgroup.one_mem _
      · rw [e]
        exact Subgroup.mem_zpowers z
    · exact Subgroup.zpowers_le.mpr hzE
  obtain ⟨t, htN, ht2, hty⟩ := h.invert hp5 y hyN z hzN hy5 hz2 hyK
  obtain ⟨g, hgN, hgz⟩ := h.invConj z hzN t htN hz2 ht2
  have hmap : E.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers t := by
    rw [hEz, MonoidHom.map_zpowers, show (MulAut.conj g).toMonoidHom z = t from hgz]
  have ht22 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact ht22
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hty' : t * y * t = y⁻¹ := by
    have := hty
    rwa [hti] at this
  have htN' : t ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    mem_normalizer_zpowers_of_conj614
      (by rw [hty]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
      (by rw [hti, hty']; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  have htC : ¬ Subgroup.zpowers t ≤ Subgroup.centralizer ({y} : Set G) := by
    intro hle
    have htc : t * y = y * t :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_zpowers t))
    have e1 : t * y * t⁻¹ = y := by
      rw [htc]
      group
    have e2 : y⁻¹ = y := hty.symm.trans e1
    have hyy : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [e2]
        _ = 1 := by simp
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hyy)
    rw [hy5] at hdvd
    norm_num at hdvd
  have hEg : E.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    rw [hmap, Subgroup.zpowers_le]
    exact htN'
  have hEgc : ¬ E.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [hmap]
    exact htC
  exact exists_conj_le_of_conj_le_normalizer614 hN hTs hTy hET
    ((le_sup_left : N ≤ N ⊔ T) hgN) hEg hEgc

end CFSG.Quasithin.H13
