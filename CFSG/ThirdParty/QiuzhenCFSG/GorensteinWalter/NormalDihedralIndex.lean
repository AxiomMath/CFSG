module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralNormalSubgroup

namespace CFSG
end CFSG
open CFSG

/-!
# Index of a normal subgroup with dihedral Sylow 2-subgroups

If `H ◁ G` and both `H` and `G` have dihedral Sylow `2`-subgroups, then
`4` does not divide `[G : H]`.  A Sylow `2`-subgroup of `H` can be placed
inside an ambient Sylow `2`-subgroup.  It is then a normal noncyclic subgroup
of an ambient dihedral group, so its index is at most two.  The quotient map
identifies that index with the order of a Sylow `2`-subgroup of `G/H`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A normal subgroup with dihedral Sylow `2`-subgroups has ambient index not
divisible by four when the ambient Sylow `2`-subgroups are also dihedral. -/
public theorem normal_subgroup_index_not_dvd_four_of_dihedral_sylow
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hHd : HasDihedralSylowTwo H) :
    ¬ 4 ∣ H.index := by
  classical
  let : H.Normal := hHnormal
  let Q : Sylow 2 H := Classical.choice Sylow.nonempty
  let Qmap : Subgroup G := (Q : Subgroup H).map H.subtype
  have hQmap : IsPGroup 2 Qmap := by
    exact Q.isPGroup'.map H.subtype
  obtain ⟨P, hQmapP⟩ := IsPGroup.exists_le_sylow hQmap
  obtain ⟨m, hm, eP⟩ := hGd P
  rcases eP with ⟨eP⟩
  have hInt : H ⊓ (P : Subgroup G) = Qmap := by
    let Dg : Subgroup G := H ⊓ (P : Subgroup G)
    have hDgH : Dg ≤ H := inf_le_left
    have hDgp : IsPGroup 2 Dg := by
      have htmp := P.isPGroup'.to_inf_left (K := H)
      rw [inf_comm] at htmp
      simpa [Dg] using htmp
    let Q' : Subgroup H := Dg.subgroupOf H
    have hQ'p : IsPGroup 2 Q' := by
      exact hDgp.of_equiv (Subgroup.subgroupOfEquivOfLe hDgH).symm
    have hQleQ' : (Q : Subgroup H) ≤ Q' := by
      intro x hx
      change (x : G) ∈ Dg
      exact ⟨(Subgroup.map_subtype_le (Q : Subgroup H))
        (Subgroup.mem_map_of_mem H.subtype hx),
        hQmapP (Subgroup.mem_map_of_mem H.subtype hx)⟩
    have hQ'eq : Q' = (Q : Subgroup H) := Q.is_maximal' hQ'p hQleQ'
    have hmapQ' : Q'.map H.subtype = Dg := by
      simpa [Q', Dg] using (Subgroup.map_subgroupOf_eq_of_le hDgH)
    calc
      H ⊓ (P : Subgroup G) = Dg := rfl
      _ = Q'.map H.subtype := hmapQ'.symm
      _ = Qmap := by rw [hQ'eq]
  let D : Subgroup P :=
    (H ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)
  have hDnormal : D.Normal := by
    apply (Subgroup.normal_subgroupOf_iff inf_le_right).2
    intro d p hd hp
    exact ⟨hHnormal.conj_mem (d : G) hd.1 (p : G),
      P.mul_mem (P.mul_mem hp hd.2) (P.inv_mem hp)⟩
  have hQmapP' : Qmap ≤ (P : Subgroup G) := hQmapP
  let eQmap : (Q : Subgroup H) ≃* Qmap :=
    (Q : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  have hDeq : D = Qmap.subgroupOf (P : Subgroup G) := by
    dsimp [D]
    rw [hInt]
  let eDmap : D ≃* Qmap := by
    rw [hDeq]
    exact Subgroup.subgroupOfEquivOfLe hQmapP'
  let eDQ : D ≃* Q := eDmap.trans eQmap.symm
  obtain ⟨k, hk, eQdihedral⟩ := hHd Q
  rcases eQdihedral with ⟨eQdihedral⟩
  have hDnc : ¬ IsCyclic D := by
    intro hcyc
    have hcycDih : IsCyclic (DihedralGroup (2 ^ k)) :=
      (eDQ.trans eQdihedral).isCyclic.mp hcyc
    have hkne : 2 ^ k ≠ 1 := by
      intro hk1
      rcases Nat.pow_eq_one.mp hk1 with htwo | hkzero
      · norm_num at htwo
      · omega
    exact DihedralGroup.not_isCyclic hkne hcycDih
  have hDindex : D.index ≤ 2 :=
    normal_noncyclic_subgroup_dihedral_of_mulEquiv_index_le_two
      hm eP D hDnormal hDnc
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  let qP : P →* G ⧸ H := q.comp (P : Subgroup G).subtype
  have hker : qP.ker = D := by
    ext x
    simp only [MonoidHom.mem_ker]
    dsimp [qP, q]
    change QuotientGroup.mk' H (x : G) = 1 ↔
      (x : G) ∈ H ⊓ (P : Subgroup G)
    constructor
    · intro hx
      exact ⟨(QuotientGroup.eq_one_iff (N := H) (x : G)).mp hx,
        x.property⟩
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := H) (x : G)).mpr hx.1
  have hDindexRange : D.index = Nat.card qP.range := by
    rw [← hker, Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange qP).toEquiv
  let Pq : Sylow 2 (G ⧸ H) :=
    P.mapSurjective (QuotientGroup.mk'_surjective H)
  have hPqRange : (Pq : Subgroup (G ⧸ H)) = qP.range := by
    rw [Sylow.coe_mapSurjective]
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, by rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.property, by rfl⟩
  intro hfour
  have hfourCard : 4 ∣ Nat.card (G ⧸ H) := by
    simpa [Subgroup.index_eq_card] using hfour
  have hfourProd : 4 ∣ Pq.index * Nat.card Pq := by
    rw [Pq.index_mul_card]
    exact hfourCard
  have hcoprime : Nat.Coprime 4 Pq.index := by
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
    exact (Nat.prime_two.coprime_iff_not_dvd).2 Pq.not_dvd_index
  have hfourPq : 4 ∣ Nat.card Pq :=
    hcoprime.dvd_of_dvd_mul_left hfourProd
  have hfourD : 4 ∣ D.index := by
    rw [hDindexRange, ← hPqRange]
    exact hfourPq
  have hfourLe : 4 ≤ D.index :=
    Nat.le_of_dvd
      (Nat.zero_lt_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := D)))
      hfourD
  omega

end CFSG.GorensteinWalter
