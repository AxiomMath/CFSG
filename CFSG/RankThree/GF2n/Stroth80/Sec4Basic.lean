module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_le_M {L : Subgroup G} (hL : L ≤ M) {m : G} (hm : m ∈ M) :
    conjSubgroup m L ≤ M := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h2 : m * (m⁻¹ * x * m) * m⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hm (hL hx)) (M.inv_mem hm)
  rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h2

theorem Lgen_le {L : Subgroup G} (hL : L ≤ M) : Lgen M L ≤ M := by
  unfold Lgen
  exact iSup₂_le fun m hm => conj_le_M hL hm

theorem conjSubgroup_iSup_eq {ι : Sort*} (k : G) (s : ι → Subgroup G) :
    conjSubgroup k (⨆ i, s i) = ⨆ i, conjSubgroup k (s i) :=
  Subgroup.map_iSup (MulAut.conj k).toMonoidHom s

theorem conjSubgroup_Lgen_le {L : Subgroup G} {k : G} (hk : k ∈ M) :
    conjSubgroup k (Lgen M L) ≤ Lgen M L := by
  unfold Lgen
  rw [conjSubgroup_iSup_eq]
  refine iSup_le fun m => ?_
  rw [conjSubgroup_iSup_eq]
  refine iSup_le fun hm => ?_
  rw [← CFSG.RankThree.GF2n.conjSubgroup_mul]
  exact le_iSup₂_of_le (k * m) (M.mul_mem hk hm) le_rfl

theorem Lgen_normal {L : Subgroup G} (hL : L ≤ M) : ((Lgen M L).subgroupOf M).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Lgen_le hL)]
  intro h k hh hk
  have hmem : k * h * k⁻¹ ∈ conjSubgroup k (Lgen M L) := by
    rw [mem_conjSubgroup, show k⁻¹ * (k * h * k⁻¹) * k = h by group]
    exact hh
  exact conjSubgroup_Lgen_le hk hmem

theorem le_Lgen (L : Subgroup G) : L ≤ Lgen M L := by
  have h1 : L ≤ conjSubgroup 1 L := by
    intro x hx
    rw [mem_conjSubgroup]
    simpa using hx
  refine h1.trans ?_
  unfold Lgen
  exact le_iSup₂_of_le (1 : G) M.one_mem le_rfl

theorem bar_normal [(Q.subgroupOf M).Normal] {S : Subgroup G}
    (hSn : (S.subgroupOf M).Normal) : (bar M Q S).Normal :=
  Subgroup.Normal.map hSn (QuotientGroup.mk' (Q.subgroupOf M))
    (QuotientGroup.mk'_surjective (N := Q.subgroupOf M))

theorem Ctx.pCore_two_Mbar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    pCore 2 (Mbar M Q) = ⊥ := by
  have hQ2 : IsPGroup 2 Q := by
    rw [hc.hyp.hQ]
    unfold inSubgroup
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype
  have hker : IsPGroup 2 (QuotientGroup.mk' (Q.subgroupOf M)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hQ2.comap_subtype
  have hPn : ((pCore 2 (Mbar M Q)).comap (QuotientGroup.mk' (Q.subgroupOf M))).Normal :=
    (CFSG.pCore_normal (p := 2) (G := Mbar M Q)).comap _
  have hPp : IsPGroup 2 ((pCore 2 (Mbar M Q)).comap (QuotientGroup.mk' (Q.subgroupOf M))) :=
    (CFSG.pCore_isPGroup (p := 2) (G := Mbar M Q)).comap_of_ker_isPGroup _ hker
  have hPle : (pCore 2 (Mbar M Q)).comap (QuotientGroup.mk' (Q.subgroupOf M)) ≤
      CFSG.pCore 2 ↥M := le_sSup ⟨hPn, hPp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := (QuotientGroup.mk'_surjective (N := Q.subgroupOf M)) x
  have hy0 : y ∈ (pCore 2 (Mbar M Q)).comap (QuotientGroup.mk' (Q.subgroupOf M)) := hx
  have hyQ : (y : G) ∈ Q := by
    rw [hc.hyp.hQ]
    unfold inSubgroup
    exact Subgroup.mem_map.mpr ⟨y, hPle hy0, rfl⟩
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) y).mpr
    (Subgroup.mem_subgroupOf.mpr hyQ)

theorem bar_Lgen_eq_normalClosure_of_le [(Q.subgroupOf M).Normal] {L : Subgroup G}
    (hLM : L ≤ M) :
    bar M Q (Lgen M L) = Subgroup.normalClosure (bar M Q L : Set (Mbar M Q)) := by
  set N := Subgroup.normalClosure (bar M Q L : Set (Mbar M Q))
  haveI hNn : N.Normal := Subgroup.normalClosure_normal
  set X : Subgroup M := N.comap (QuotientGroup.mk' (Q.subgroupOf M))
  have hinj : Function.Injective M.subtype := Subtype.coe_injective
  have hsub : Lgen M L ≤ X.map M.subtype := by
    unfold Lgen
    refine iSup₂_le fun m hm => ?_
    intro x hx
    have hxM : x ∈ M := conj_le_M hLM hm hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
    have hz : m⁻¹ * x * m ∈ L := mem_conjSubgroup.mp hx
    have hzM : m⁻¹ * x * m ∈ M := hLM hz
    have hxeq : (⟨x, hxM⟩ : M) = (⟨m, hm⟩ : M) * ⟨m⁻¹ * x * m, hzM⟩ * (⟨m, hm⟩ : M)⁻¹ :=
      Subtype.ext (show x = m * (m⁻¹ * x * m) * m⁻¹ by group)
    have hz' : (⟨m⁻¹ * x * m, hzM⟩ : M) ∈ L.subgroupOf M := hz
    have hzbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨m⁻¹ * x * m, hzM⟩ ∈ bar M Q L :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf M)) hz'
    have hzN : QuotientGroup.mk' (Q.subgroupOf M) ⟨m⁻¹ * x * m, hzM⟩ ∈ N :=
      Subgroup.le_normalClosure (H := bar M Q L) hzbar
    show QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ ∈ N
    rw [hxeq, map_mul, map_mul, map_inv]
    exact hNn.conj_mem _ hzN _
  have hLX : (Lgen M L).subgroupOf M ≤ X := by
    intro x hx
    have hx' : (x : G) ∈ Lgen M L := hx
    have h1 : (x : G) ∈ X.map M.subtype := hsub hx'
    rw [← Subgroup.comap_map_eq_self_of_injective hinj X]
    exact h1
  have e2 : X.map (QuotientGroup.mk' (Q.subgroupOf M)) = N :=
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (N := Q.subgroupOf M)) N
  have hle : bar M Q (Lgen M L) ≤ N := (Subgroup.map_mono hLX).trans e2.le
  refine le_antisymm hle ?_
  have hmono : bar M Q L ≤ bar M Q (Lgen M L) :=
    Subgroup.map_mono (fun x hx => le_Lgen L (show (x : G) ∈ L from hx))
  have hnorm : (bar M Q (Lgen M L)).Normal := bar_normal (Lgen_normal hLM)
  haveI := hnorm
  exact Subgroup.normalClosure_le_normal (fun y hy => hmono (show y ∈ bar M Q L from hy))

theorem bar_Lgen_eq_normalClosure [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    bar M Q (Lgen M (LB M Q B)) =
      Subgroup.normalClosure (bar M Q (LB M Q B) : Set (Mbar M Q)) :=
  bar_Lgen_eq_normalClosure_of_le hc.LB_le_M

end CFSG.RankThree.GF2n.Stroth80
