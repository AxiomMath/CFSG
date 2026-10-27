module

public import CFSG.RankThree.GF2n.Tim81.Setting
public import CFSG.RankThree.GF2n.Tim81.HBar
public import CFSG.RankThree.GF2n.Tim81.ConjugatesInM
public import CFSG.RankThree.GF2n.Tim81.Overgroups
public import CFSG.RankThree.GF2n.Tim78Frattini
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.RankThree.GF2n.Tim78S4Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace Hyp
private theorem exists_sylow_conj_data (h : Hyp M V) (hPH : Pc M V ≤ H) {g : G}
    (hgH : conjSubgroup g (Pc M V) ≤ H) :
    ∃ (T : Subgroup G) (c : ↥H), IsPGroup 2 T ∧ T ≠ ⊥ ∧
      conjSubgroup g (Pc M V) ≤ T ∧ conjSubgroup (c : G) (Pc M V) ≤ T := by

  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPne : Pc M V ≠ ⊥ := fun hbot => h.ne_bot (le_bot_iff.mp (h.le_Pc.trans_eq hbot))
  have hPg2 : IsPGroup 2 (conjSubgroup g (Pc M V)) := hP2.map (MulAut.conj g).toMonoidHom
  have hPg2H : IsPGroup 2 ((conjSubgroup g (Pc M V)).subgroupOf H) :=
    IsPGroup.comap_subtype (K := H) hPg2
  obtain ⟨T', hT'⟩ := hPg2H.exists_le_sylow
  set T : Subgroup G := (T' : Subgroup ↥H).map H.subtype with hTdef
  have hT2 : IsPGroup 2 T := T'.isPGroup'.map H.subtype
  have hTne : T ≠ ⊥ := by
    intro hbot
    have h1 : conjSubgroup g (Pc M V) = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [← Subgroup.map_subgroupOf_eq_of_le hgH]
      exact (Subgroup.map_mono (f := H.subtype) hT').trans (le_of_eq hbot)
    exact hPne (conjSubgroup_eq_bot_iff.mp h1)
  have hPgT : conjSubgroup g (Pc M V) ≤ T := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hgH]
    exact Subgroup.map_mono (f := H.subtype) hT'
  obtain ⟨c, hcH, hcT⟩ :=
    CFSG.QuasiDihedralFusion.exists_conj_le_sylow (p := 2) (K := ⊤) T' le_top
      ((Pc M V).subgroupOf H) le_top (IsPGroup.comap_subtype (K := H) hP2)
  have hPcT : conjSubgroup (c : G) (Pc M V) ≤ T := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    have hp' : (⟨p, hPH hp⟩ : ↥H) ∈ (Pc M V).subgroupOf H := Subgroup.mem_subgroupOf.mpr hp
    have hmem : MulAut.conj c ⟨p, hPH hp⟩ ∈ (T' : Subgroup ↥H) :=
      hcT (Subgroup.mem_map.mpr ⟨⟨p, hPH hp⟩, hp', rfl⟩)
    exact Subgroup.mem_map.mpr ⟨MulAut.conj c ⟨p, hPH hp⟩, hmem, by simp [MulAut.conj_apply]⟩
  exact ⟨T, c, hT2, hTne, hPgT, hPcT⟩

private theorem conj_V_eq_of_central_element (h : Hyp M V) {g : G} {T : Subgroup G}
    {c : ↥H} (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hPgT : conjSubgroup g (Pc M V) ≤ T)
    (hPcT : conjSubgroup (c : G) (Pc M V) ≤ T) :
    conjSubgroup g V = conjSubgroup (c : G) V := by

  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTne
  haveI : Nontrivial ↥(Subgroup.center ↥T) := hT2.center_nontrivial
  obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥T)
  set t : G := ((w : ↥T) : G) with ht
  have ht1 : t ≠ 1 := fun h1 => hw1 (Subtype.ext (Subtype.ext h1))
  have hcent : ∀ x ∈ T, x * t = t * x := fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨x, hx⟩)
  have htVg : t ∈ conjSubgroup g V := by
    rw [← h.centralizer_conj_Pc g, Subgroup.mem_centralizer_iff]
    intro p hp
    exact hcent p (hPgT hp)
  have htVc : t ∈ conjSubgroup (c : G) V := by
    rw [← h.centralizer_conj_Pc (c : G), Subgroup.mem_centralizer_iff]
    intro p hp
    exact hcent p (hPcT hp)
  have hne : conjSubgroup g V ⊓ conjSubgroup (c : G) V ≠ ⊥ := by
    intro hbot
    have hmem : t ∈ conjSubgroup g V ⊓ conjSubgroup (c : G) V :=
      Subgroup.mem_inf.mpr ⟨htVg, htVc⟩
    rw [hbot] at hmem
    exact ht1 (Subgroup.mem_bot.mp hmem)
  have hkne : V ⊓ conjSubgroup (g⁻¹ * c) V ≠ ⊥ := by
    intro hbot
    apply hne
    have hEq : conjSubgroup g (V ⊓ conjSubgroup (g⁻¹ * c) V) =
        conjSubgroup g V ⊓ conjSubgroup (c : G) V := by
      rw [conjSubgroup_mul, conjSubgroup_inf, conjSubgroup_conjSubgroup, mul_inv_cancel,
        conjSubgroup_one]
    rw [← hEq, hbot]
    exact conjSubgroup_eq_bot_iff.mpr rfl
  have hVgVc : conjSubgroup g V = conjSubgroup (c : G) V := by
    have hk : conjSubgroup (g⁻¹ * c) V = V := conjSubgroup_eq_of_isTI h.ti hkne
    have h2 : conjSubgroup (c : G) V = conjSubgroup g V := by
      calc conjSubgroup (c : G) V = conjSubgroup (g * (g⁻¹ * (c : G))) V := by
            rw [show g * (g⁻¹ * (c : G)) = (c : G) by group]
        _ = conjSubgroup g (conjSubgroup (g⁻¹ * c) V) := conjSubgroup_mul g (g⁻¹ * c) V
        _ = conjSubgroup g V := by rw [hk]
    exact h2.symm
  exact hVgVc

private theorem exists_conj_eq_of_conj_V_eq (h : Hyp M V)
    {g : G} {c : ↥H} (hVgVc : conjSubgroup g V = conjSubgroup (c : G) V) :
    ∃ y ∈ H, conjSubgroup g (Pc M V) = conjSubgroup y (Pc M V) ∧
      conjSubgroup g V = conjSubgroup y V := by

  have hmemM : (c : G)⁻¹ * g ∈ M := by
    have hN : (c : G)⁻¹ * g ∈ Subgroup.normalizer (V : Set G) := by
      rw [← conjSubgroup_eq_self_iff]
      calc conjSubgroup ((c : G)⁻¹ * g) V = conjSubgroup (c : G)⁻¹ (conjSubgroup g V) :=
            conjSubgroup_mul (c : G)⁻¹ g V
        _ = conjSubgroup (c : G)⁻¹ (conjSubgroup (c : G) V) := by rw [hVgVc]
        _ = conjSubgroup ((c : G)⁻¹ * (c : G)) V := conjSubgroup_conjSubgroup (c : G)⁻¹ (c : G) V
        _ = V := by rw [inv_mul_cancel, conjSubgroup_one]
    rwa [h.normalizer_eq] at hN
  have hPc : conjSubgroup ((c : G)⁻¹ * g) (Pc M V) = Pc M V := by
    rw [conjSubgroup_eq_self_iff]
    exact h.le_normalizer_Pc hmemM
  refine ⟨(c : G), c.2, ?_, hVgVc⟩
  calc conjSubgroup g (Pc M V) = conjSubgroup ((c : G) * ((c : G)⁻¹ * g)) (Pc M V) := by
        rw [show (c : G) * ((c : G)⁻¹ * g) = g by group]
    _ = conjSubgroup (c : G) (conjSubgroup ((c : G)⁻¹ * g) (Pc M V)) :=
        conjSubgroup_mul (c : G) ((c : G)⁻¹ * g) _
    _ = conjSubgroup (c : G) (Pc M V) := by rw [hPc]

theorem exists_mem_conj_eq_of_conj_Pc_le (h : Hyp M V) (hPH : Pc M V ≤ H) {g : G}
    (hgH : conjSubgroup g (Pc M V) ≤ H) :
    ∃ y ∈ H, conjSubgroup g (Pc M V) = conjSubgroup y (Pc M V) ∧
      conjSubgroup g V = conjSubgroup y V := by
  obtain ⟨T, c, hT2, hTne, hPgT, hPcT⟩ := exists_sylow_conj_data h hPH hgH
  exact exists_conj_eq_of_conj_V_eq h (conj_V_eq_of_central_element h hT2 hTne hPgT hPcT)

theorem centralizer_conj_singleton_le (h : Hyp M V) {g x : G}
    (hx : x ∈ conjSubgroup g V) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ conjSubgroup g M := by
  have hxV : g⁻¹ * x * g ∈ V := mem_conjSubgroup.mp hx
  have hxV1 : g⁻¹ * x * g ≠ 1 := by
    intro h1
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  intro c hc
  have hxc : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hmem : g⁻¹ * c * g ∈ Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g⁻¹ * c * g) * (g⁻¹ * x * g) = g⁻¹ * (c * x) * g := by group
      _ = g⁻¹ * (x * c) * g := by rw [hxc]
      _ = (g⁻¹ * x * g) * (g⁻¹ * c * g) := by group
  exact mem_conjSubgroup.mpr (h.centralizer_le_M hxV hxV1 hmem)

end Hyp

namespace RootHyp

theorem conj_eq_of_inf_conj_Pc_ne_bot (h : RootHyp M V) {g : G}
    (hg : V ⊓ conjSubgroup g (Pc M V) ≠ ⊥) : conjSubgroup g V = V := by
  have hneRoot : V ⊓ Subgroup.normalizer (conjSubgroup g V : Set G) ≠ ⊥ := by
    refine fun hbot => hg (le_bot_iff.mp ?_)
    refine (inf_le_inf_left V ?_).trans (le_of_eq hbot)
    rw [normalizer_conjSubgroup]
    exact Subgroup.map_mono (h.toHyp.Pc_le_M.trans h.toHyp.le_normalizer)
  have hcomm : ∀ a ∈ V, ∀ b ∈ conjSubgroup g V, a * b = b * a := by
    have hc := Tim78.commute_of_isRootTypeTI h.rootType (g := 1) (h := g)
      (by simpa [conjSubgroup_one] using hneRoot)
    simpa [conjSubgroup_one] using hc
  have hVgne : conjSubgroup g V ≠ ⊥ := fun hbot =>
    h.toHyp.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVgne
  have hwVg : (w : G) ∈ conjSubgroup g V := w.2
  have hw1' : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hVMg : V ≤ conjSubgroup g M := by
    intro v hv
    refine h.toHyp.centralizer_conj_singleton_le hwVg hw1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm v hv (w : G) hwVg
  have hVgM : conjSubgroup g⁻¹ V ≤ M := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ V := by
      rwa [mem_conjSubgroup, inv_inv] at hx
    have hmem : g * x * g⁻¹ ∈ conjSubgroup g M := hVMg hx'
    have := mem_conjSubgroup.mp hmem
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  rcases h.toHyp.conj_le_Pc_or_inf_eq_bot h.rootType (g := g⁻¹) hVgM with hP | hbot
  · have hEq : conjSubgroup g⁻¹ V = V := h.weaklyClosed_P.2 g⁻¹ hP
    have h2 : conjSubgroup g (conjSubgroup g⁻¹ V) = conjSubgroup g V := by rw [hEq]
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
    exact h2.symm
  · exfalso
    have h2 : conjSubgroup g⁻¹ (V ⊓ conjSubgroup g (Pc M V)) ≠ ⊥ := by
      intro hb
      apply hg
      have h1 := congrArg (conjSubgroup g) hb
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h1
      rw [h1]
      exact conjSubgroup_eq_bot_iff.mpr rfl
    have h3 : conjSubgroup g⁻¹ V ⊓ Pc M V ≠ ⊥ := by
      have hEq : conjSubgroup g⁻¹ (V ⊓ conjSubgroup g (Pc M V)) =
          conjSubgroup g⁻¹ V ⊓ Pc M V := by
        rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      rwa [hEq] at h2
    have hle : conjSubgroup g⁻¹ V ⊓ Pc M V ≤
        conjSubgroup g⁻¹ V ⊓ inSubgroup (pCore 2) M :=
      le_inf inf_le_left (inf_le_right.trans inf_le_left)
    rw [hbot] at hle
    exact h3 (le_bot_iff.mp hle)

theorem xOf_le_pCore (hVH : V ≤ inSubgroup (pCore 2) H) :
    Tim79a.xOf V H ≤ inSubgroup (pCore 2) H :=
  iSup₂_le fun _ hU => by
    obtain ⟨g, hg, rfl⟩ := hU
    calc conjSubgroup g V ≤ conjSubgroup g (inSubgroup (pCore 2) H) := Subgroup.map_mono hVH
      _ = inSubgroup (pCore 2) H :=
        conjSubgroup_eq_self_iff.mpr ((inSubgroup_pCore_two H).2.2 hg)

theorem xOf_le_M (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) : Tim79a.xOf V H ≤ M :=
  (xOf_le_pCore hVH).trans (h.toHyp.pCore_le_of_Pc_le hPH)

theorem isElemAbelian_xOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) : Assembly.IsElemAbelian 2 (Tim79a.xOf V H) := by
  classical
  set s : Set G := {a : G | ∃ U ∈ Tim79a.omegaOf V H, a ∈ U} with hs
  have hxOf_eq : Tim79a.xOf V H = Subgroup.closure s := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun U hU a ha => ?_
      exact Subgroup.subset_closure ⟨U, hU, ha⟩
    · refine (Subgroup.closure_le (K := Tim79a.xOf V H)).mpr ?_
      rintro a ⟨U, hU, ha⟩
      exact Tim79a.le_xOf hU ha
  rw [hxOf_eq]
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨U, hU, ha⟩ b ⟨W, hW, hb⟩
    obtain ⟨p, hp, rfl⟩ := hU
    obtain ⟨q, hq, rfl⟩ := hW
    change a ∈ conjSubgroup p V at ha
    change b ∈ conjSubgroup q V at hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hu : p⁻¹ * q ∈ H := H.mul_mem (H.inv_mem hp) hq
    have hVuM : conjSubgroup (p⁻¹ * q) V ≤ M :=
      (Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hu)).trans (xOf_le_M h hPH hVH)
    have hne : conjSubgroup (p⁻¹ * q) V ⊓ M ≠ ⊥ := by
      rw [inf_eq_left.mpr hVuM]
      exact fun hbot => h.toHyp.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
    have hcomm := h.toHyp.commute_of_conj_inf_ne_bot h.rootType hne
    have hy : ((p⁻¹ * q) * b' * (p⁻¹ * q)⁻¹) ∈ conjSubgroup (p⁻¹ * q) V := by
      rw [mem_conjSubgroup]
      have hb'' : (p⁻¹ * q)⁻¹ * ((p⁻¹ * q) * b' * (p⁻¹ * q)⁻¹) * (p⁻¹ * q) = b' := by group
      rw [hb'']
      exact hb'
    have h1 : a' * ((p⁻¹ * q) * b' * (p⁻¹ * q)⁻¹) =
        ((p⁻¹ * q) * b' * (p⁻¹ * q)⁻¹) * a' := hcomm a' ha' _ hy
    calc p * a' * p⁻¹ * (q * b' * q⁻¹)
        = p * (a' * ((p⁻¹ * q) * b' * (p⁻¹ * q)⁻¹)) * p⁻¹ := by group
      _ = p * (((p⁻¹ * q) * b' * (p⁻¹ * q)⁻¹) * a') * p⁻¹ := by rw [h1]
      _ = (q * b' * q⁻¹) * (p * a' * p⁻¹) := by group
  · rintro a ⟨U, hU, ha⟩
    obtain ⟨p, hp, rfl⟩ := hU
    change a ∈ conjSubgroup p V at ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hsq : a' * a' = 1 := by
      simpa [pow_two] using h.toHyp.elem.2 a' ha'
    rw [pow_two, show p * a' * p⁻¹ * (p * a' * p⁻¹) = p * (a' * a') * p⁻¹ by group, hsq]
    group

theorem xOf_le_kOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) : Tim79a.xOf V H ≤ kOf V H := by
  have hVH' : V ≤ H := hVH.trans (inSubgroup_pCore_two H).2.1
  refine le_inf (Tim79a.xOf_le_H hVH') ?_
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr
    (isElemAbelian_xOf h hPH hVH).1

theorem xOf_le_centralizer_conj (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {x : G} (hx : x ∈ H) :
    Tim79a.xOf V H ≤ Subgroup.centralizer (conjSubgroup x V : Set G) := by
  have hEab := isElemAbelian_xOf h hPH hVH
  have hcent : Tim79a.xOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hEab.1
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp (hcent hw) v
    (Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hx) hv)

theorem xOf_inf_centralizer_conj_Pc (h : RootHyp M V) {x : G} (hx : x ∈ H) :
    Tim79a.xOf V H ⊓ Subgroup.centralizer (conjSubgroup x (Pc M V) : Set G) =
      conjSubgroup x V := by
  refine le_antisymm ?_ ?_
  · intro y hy
    have hcent : y ∈ Subgroup.centralizer (conjSubgroup x (Pc M V) : Set G) := hy.2
    rwa [h.toHyp.centralizer_conj_Pc x] at hcent
  · refine le_inf (Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hx)) ?_
    rw [h.toHyp.centralizer_conj_Pc x]

theorem commutator_xOf_conj_Pc_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {x : G} (hx : x ∈ H) :
    ⁅Tim79a.xOf V H, conjSubgroup x (Pc M V)⁆ ≤
      Tim79a.xOf V H ⊓ conjSubgroup x (Pc M V) := by
  refine le_inf ?_ ?_
  · refine (Subgroup.le_normalizer_iff_commutator_le_left
      (H := conjSubgroup x (Pc M V)) (K := Tim79a.xOf V H)).mp ?_
    exact (conjSubgroup_le_of_le_of_mem hPH hx).trans (Tim79a.H_le_normalizer_xOf V H)
  · refine (Subgroup.le_normalizer_iff_commutator_le_right
      (H := Tim79a.xOf V H) (K := conjSubgroup x (Pc M V))).mp ?_
    have hxOfMx : Tim79a.xOf V H ≤ conjSubgroup x M :=
      (xOf_le_pCore hVH).trans (h.toHyp.pCore_le_conj_of_Pc_le hPH hx)
    refine hxOfMx.trans ?_
    rw [normalizer_conjSubgroup]
    exact Subgroup.map_mono h.toHyp.le_normalizer_Pc

theorem isElemAbelian_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) :
    Assembly.IsElemAbelian 2 (imgK V H (Pc M V)) := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPhiV : inSubgroup frattini (Pc M V) ≤ V := h.toHyp.frattini_Pc_le
  have hEab := isElemAbelian_xOf h hPH hVH
  have hVW : V ≤ Tim79a.xOf V H := by
    simpa [conjSubgroup_one] using Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf (V := V)
      (H := H) (h := 1) H.one_mem)
  have hVK : V ≤ kOf V H := by
    refine le_inf (hVH.trans (inSubgroup_pCore_two H).2.1) ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨w, hw⟩ ⟨v, hVW hv⟩)
  have hPhiK : inSubgroup frattini (Pc M V) ≤ kOf V H := hPhiV.trans hVK
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨p, hpP, hp⟩ := mem_imgK_iff.mp a.2
    obtain ⟨q, hqP, hq⟩ := mem_imgK_iff.mp b.2
    have hdiv : (p * q) / (q * p) ∈ (kOf V H).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : (((p * q) / (q * p) : ↥H) : G) = ⁅(p : G), (q : G)⁆ := by
        simp [div_eq_mul_inv, commutatorElement_def, mul_assoc]
      rw [hcoe]
      exact hPhiK (commutatorElement_mem_inSubgroup_frattini hP2 hpP hqP)
    have heq : piK V H (p * q) = piK V H (q * p) :=
      (QuotientGroup.eq_iff_div_mem).mpr hdiv
    have hmain : (a : HBar V H) * b = (b : HBar V H) * a := by
      calc (a : HBar V H) * b = piK V H (p * q) := by rw [← hp, ← hq, map_mul]
        _ = piK V H (q * p) := heq
        _ = (b : HBar V H) * a := by rw [← hp, ← hq, map_mul]
    exact Subtype.ext hmain
  · intro a ha
    obtain ⟨p, hpP, hp⟩ := mem_imgK_iff.mp ha
    have hsq : (p ^ 2) ∈ (kOf V H).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((p ^ 2 : ↥H) : G) = (p : G) ^ 2 := by simp
      rw [hcoe]
      exact hPhiK (sq_mem_inSubgroup_frattini hP2 hpP)
    have h1 : piK V H (p ^ 2) = 1 := (piK_eq_one_iff (p ^ 2)).mpr hsq
    calc a ^ 2 = (piK V H p) ^ 2 := by rw [← hp]
      _ = piK V H (p ^ 2) := (map_pow (piK V H) p 2).symm
      _ = 1 := h1

private theorem commutatorElement_mul_left_of_centralizes {W : Subgroup G} {k w x : G}
    (hw : w ∈ W) (hz : w * x * w⁻¹ * x⁻¹ ∈ W)
    (hk : k ∈ Subgroup.centralizer (W : Set G)) :
    ⁅w, k * x⁆ = ⁅w, x⁆ := by
  have hkw : w * k = k * w := Subgroup.mem_centralizer_iff.mp hk w hw
  have hkz : (w * x * w⁻¹ * x⁻¹) * k = k * (w * x * w⁻¹ * x⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hk _ hz
  have hwk : w * k * w⁻¹ = k := by
    calc w * k * w⁻¹ = (k * w) * w⁻¹ := by rw [hkw]
      _ = k := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc w * (k * x) * w⁻¹ * (k * x)⁻¹
      = (w * k * w⁻¹) * (w * x * w⁻¹ * x⁻¹) * k⁻¹ := by group
    _ = k * (w * x * w⁻¹ * x⁻¹) * k⁻¹ := by rw [hwk]
    _ = w * x * w⁻¹ * x⁻¹ := by rw [← hkz]; group


private theorem conjSubgroup_iInf_eq_of_perm {ι : Type*} [Nonempty ι] (r : G)
    (f : ι → Subgroup G) (σ σ' : ι → ι) (hσ : ∀ i, conjSubgroup r (f i) = f (σ i))
    (hσσ' : ∀ i, σ (σ' i) = i) :
    conjSubgroup r (⨅ i, f i) = ⨅ i, f i := by
  rw [show conjSubgroup r (⨅ i, f i) = ⨅ i, conjSubgroup r (f i) from by
    have h := Subgroup.map_iInf (MulAut.conj r).toMonoidHom (MulAut.conj r).injective f
    simpa [conjSubgroup] using h]
  rw [iInf_congr hσ]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun j => ?_
    calc (⨅ i, f (σ i)) ≤ f (σ (σ' j)) := iInf_le _ (σ' j)
      _ = f j := by rw [hσσ' j]
  · refine le_iInf fun i => ?_
    exact iInf_le (fun i => f i) (σ i)


private theorem isTI_imgK_eq (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {y : ↥H}
    (hVy : conjSubgroup (y : G) V = V) :
    imgK V H (Pc M V) ⊓ conjSubgroup (piK V H y) (imgK V H (Pc M V)) =
      imgK V H (Pc M V) := by
  have hconj : conjSubgroup (piK V H y) (imgK V H (Pc M V)) =
      imgK V H (conjSubgroup (y : G) (Pc M V)) :=
    (imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) y.2 hPH).symm
  rw [hconj]

  have hyM : (y : G) ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact conjSubgroup_eq_self_iff.mp hVy
  have hPy : conjSubgroup (y : G) (Pc M V) = Pc M V := by
    rw [conjSubgroup_eq_self_iff]
    exact h.toHyp.le_normalizer_Pc hyM
  rw [hPy, inf_idem]

private theorem isTI_hbar_in_py (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : ↥H} {tbar : HBar V H}
    (htbarP : tbar ∈ imgK V H (Pc M V))
    (htbarPy : tbar ∈ imgK V H (conjSubgroup (y : G) (Pc M V))) :
    ∀ p : ↥(Pc M V),
      tbar ∈ imgK V H (conjSubgroup ((p : G) * (y : G)) (Pc M V)) := by

  intro p
  have hpbar : piK V H ⟨(p : G), hPH p.2⟩ ∈ imgK V H (Pc M V) :=
    Subgroup.mem_map.mpr ⟨⟨(p : G), hPH p.2⟩, Subgroup.mem_subgroupOf.mpr p.2, rfl⟩
  have hcomm : (piK V H ⟨(p : G), hPH p.2⟩) * (tbar : HBar V H) =
      (tbar : HBar V H) * piK V H ⟨(p : G), hPH p.2⟩ :=
    congrArg Subtype.val
      ((isElemAbelian_imgK h hPH hVH).1.is_comm.comm ⟨_, hpbar⟩ ⟨_, htbarP⟩)
  have hfix : MulAut.conj (piK V H ⟨(p : G), hPH p.2⟩) (tbar : HBar V H) =
      (tbar : HBar V H) := by
    rw [MulAut.conj_apply, hcomm]
    group
  have hle : conjSubgroup (y : G) (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH y.2
  have hEq := imgK_conjSubgroup (V := V) (H := H)
    (S := conjSubgroup (y : G) (Pc M V)) (g := (p : G)) (hPH p.2) hle
  rw [show conjSubgroup ((p : G) * (y : G)) (Pc M V) =
    conjSubgroup (p : G) (conjSubgroup (y : G) (Pc M V)) from
      (conjSubgroup_conjSubgroup (p : G) (y : G) (Pc M V)).symm, hEq]
  exact Subgroup.mem_map.mpr ⟨(tbar : HBar V H), htbarPy, hfix⟩

private theorem isTI_hkey_comm_mem (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : ↥H} {N : Subgroup G}
    {tbar : HBar V H} {t : G} {x₀ : ↥H} (ht : t = (x₀ : G))
    (htH : t ∈ H) (hx₀P : (x₀ : G) ∈ Pc M V)
    (hx₀pi : piK V H x₀ = tbar)
    (hbar_in_py : ∀ p : ↥(Pc M V),
      tbar ∈ imgK V H (conjSubgroup ((p : G) * (y : G)) (Pc M V)))
    (hNdef : N = Tim79a.xOf V H ⊓ Pc M V ⊓
      ⨅ p : ↥(Pc M V), conjSubgroup ((p : G) * (y : G)) (Pc M V)) :
    ∀ w ∈ Tim79a.xOf V H, ⁅w, t⁆ ∈ N := by

  have hkey : ∀ w ∈ Tim79a.xOf V H, ∀ (x : ↥H),
      piK V H x = (tbar : HBar V H) → ⁅w, t⁆ = ⁅w, (x : G)⁆ := by
    intro w hw x hxpi
    have hkK : t * (x : G)⁻¹ ∈ kOf V H := by
      have hEq : piK V H x = piK V H x₀ := by rw [hxpi, hx₀pi]
      have hdiv : x / x₀ ∈ (kOf V H).subgroupOf H := (QuotientGroup.eq_iff_div_mem).mp hEq
      have hinv : (x / x₀ : ↥H)⁻¹ ∈ (kOf V H).subgroupOf H := Subgroup.inv_mem _ hdiv
      rw [Subgroup.mem_subgroupOf] at hinv
      have hval : (((x / x₀ : ↥H)⁻¹) : G) = t * (x : G)⁻¹ := by
        simp [div_eq_mul_inv, ht, mul_assoc]
      rw [← hval]
      exact hinv
    have hzW : w * (x : G) * w⁻¹ * (x : G)⁻¹ ∈ Tim79a.xOf V H := by
      have hNW : (x : G) ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
        Tim79a.H_le_normalizer_xOf V H x.2
      have hmem : (x : G) * w⁻¹ * (x : G)⁻¹ ∈ Tim79a.xOf V H :=
        (Subgroup.mem_normalizer_iff.mp hNW w⁻¹).mp ((Tim79a.xOf V H).inv_mem hw)
      have h := (Tim79a.xOf V H).mul_mem hw hmem
      rw [show w * (x : G) * w⁻¹ * (x : G)⁻¹ =
        w * ((x : G) * w⁻¹ * (x : G)⁻¹) by group]
      exact h
    have ht_eq : t = (t * (x : G)⁻¹) * (x : G) := by group
    conv_lhs => rw [ht_eq]
    exact commutatorElement_mul_left_of_centralizes hw hzW hkK.2
  have hcomm_mem : ∀ w ∈ Tim79a.xOf V H, ⁅w, t⁆ ∈ N := by
    intro w hw
    rw [hNdef]
    have hmemW : ⁅w, t⁆ ∈ Tim79a.xOf V H := by
      have hNW : t ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
        Tim79a.H_le_normalizer_xOf V H htH
      have hmem : t * w⁻¹ * t⁻¹ ∈ Tim79a.xOf V H :=
        (Subgroup.mem_normalizer_iff.mp hNW w⁻¹).mp ((Tim79a.xOf V H).inv_mem hw)
      have h := (Tim79a.xOf V H).mul_mem hw hmem
      rw [commutatorElement_def,
        show w * t * w⁻¹ * t⁻¹ = w * (t * w⁻¹ * t⁻¹) by group]
      exact h
    have hcommP : ⁅w, t⁆ ∈ Pc M V := by
      have hle : ⁅Tim79a.xOf V H, Pc M V⁆ ≤ Tim79a.xOf V H ⊓ Pc M V := by
        simpa [conjSubgroup_one] using
          commutator_xOf_conj_Pc_le h hPH hVH (x := 1) H.one_mem
      rw [hkey w hw x₀ hx₀pi]
      exact (Subgroup.mem_inf.mp (hle (Subgroup.commutator_mem_commutator hw hx₀P))).2
    refine Subgroup.mem_inf.mpr ⟨⟨hmemW, hcommP⟩, ?_⟩
    rw [Subgroup.mem_iInf]
    intro p
    obtain ⟨x, hxP, hxpi⟩ := mem_imgK_iff.mp (hbar_in_py p)
    rw [hkey w hw x hxpi]
    exact (Subgroup.mem_inf.mp
      ((commutator_xOf_conj_Pc_le h hPH hVH (H.mul_mem (hPH p.2) y.2))
        (Subgroup.commutator_mem_commutator hw hxP))).2
  exact hcomm_mem

private theorem isTI_hPN (h : RootHyp M V) (hPH : Pc M V ≤ H) {y : ↥H}
    {N : Subgroup G}
    (hNdef : N = Tim79a.xOf V H ⊓ Pc M V ⊓
      ⨅ p : ↥(Pc M V), conjSubgroup ((p : G) * (y : G)) (Pc M V)) :
    Pc M V ≤ Subgroup.normalizer (N : Set G) := by

  intro r hr
  rw [← conjSubgroup_eq_self_iff]
  have hrH : r ∈ H := hPH hr
  have hconjW : conjSubgroup r (Tim79a.xOf V H) = Tim79a.xOf V H :=
    conjSubgroup_eq_self_iff.mpr (Tim79a.H_le_normalizer_xOf V H hrH)
  have hconjP : conjSubgroup r (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc (h.toHyp.Pc_le_M hr))
  have hconjI : conjSubgroup r (⨅ p : ↥(Pc M V),
      conjSubgroup ((p : G) * (y : G)) (Pc M V)) =
      ⨅ p : ↥(Pc M V), conjSubgroup ((p : G) * (y : G)) (Pc M V) := by
    refine conjSubgroup_iInf_eq_of_perm r
      (fun p : ↥(Pc M V) => conjSubgroup ((p : G) * (y : G)) (Pc M V))
      (fun p : ↥(Pc M V) => ⟨r, hr⟩ * p) (fun p : ↥(Pc M V) => (⟨r, hr⟩ : ↥(Pc M V))⁻¹ * p)
      ?_ ?_
    · intro p
      rw [conjSubgroup_conjSubgroup]
      congr 1
      simp only [Subgroup.coe_mul]
      group
    · intro p
      group
  rw [hNdef, conjSubgroup_inf, conjSubgroup_inf, hconjW, hconjP, hconjI]

private theorem isTI_ne_final (h : RootHyp M V) {y : ↥H}
    (hVy : conjSubgroup (y : G) V ≠ V) {N : Subgroup G}
    (hN_le_P : N ≤ Pc M V) (hN_le_Py : N ≤ conjSubgroup (y : G) (Pc M V))
    (hPN : Pc M V ≤ Subgroup.normalizer (N : Set G))
    {tbar : HBar V H} {t : G} {x₀ : ↥H} (ht : t = (x₀ : G)) (htH : t ∈ H)
    (hx₀pi : piK V H x₀ = tbar) (htbar1' : tbar ≠ 1)
    (hcomm_mem : ∀ w ∈ Tim79a.xOf V H, ⁅w, t⁆ ∈ N) : False := by
    have hcommPN : ⁅Pc M V, N⁆ ≤ N :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp hPN
    have hPhiP : ⁅Pc M V, Pc M V⁆ ≤ inSubgroup frattini (Pc M V) := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      exact commutatorElement_mem_inSubgroup_frattini
        ((inSubgroup_pCore_two M).1.to_le inf_le_left) ha hb
    have hcommPP : ⁅Pc M V, N⁆ ≤ ⁅Pc M V, Pc M V⁆ :=
      Subgroup.commutator_mono le_rfl hN_le_P
    have hVinf : V ⊓ conjSubgroup (y : G) (Pc M V) = ⊥ := by
      by_contra hcon
      exact hVy (conj_eq_of_inf_conj_Pc_ne_bot h (by rwa [inf_comm] at hcon ⊢))
    have hcomm_triv : ⁅Pc M V, N⁆ = ⊥ := by
      have hle : ⁅Pc M V, N⁆ ≤ N ⊓ V :=
        le_inf hcommPN (hcommPP.trans (hPhiP.trans h.toHyp.frattini_Pc_le))
      have hle2 : ⁅Pc M V, N⁆ ≤ conjSubgroup (y : G) (Pc M V) ⊓ V :=
        le_inf (hle.trans inf_le_left |>.trans hN_le_Py) (hle.trans inf_le_right)
      rw [inf_comm, hVinf] at hle2
      exact le_bot_iff.mp hle2
    have hNV : N ≤ V := by
      rw [← h.toHyp.centralizer_Pc]
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_
      rw [Subgroup.commutator_comm]
      exact hcomm_triv
    have hNbot : N = ⊥ := by
      have hle : N ≤ V ⊓ conjSubgroup (y : G) (Pc M V) := le_inf hNV hN_le_Py
      rw [hVinf] at hle
      exact le_bot_iff.mp hle
    have ht_cent : t ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hmem : ⁅w, t⁆ ∈ N := hcomm_mem w hw
      rw [hNbot] at hmem
      exact (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hmem)).eq
    have htK : t ∈ kOf V H := Subgroup.mem_inf.mpr ⟨htH, ht_cent⟩
    have h1 : piK V H x₀ = 1 := (piK_eq_one_iff x₀).mpr (by rwa [← ht])
    rw [h1] at hx₀pi
    exact htbar1' hx₀pi.symm

private theorem isTI_imgK_ne (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : ↥H}
    (hVy : conjSubgroup (y : G) V ≠ V) :
    imgK V H (Pc M V) ⊓ conjSubgroup (piK V H y) (imgK V H (Pc M V)) = ⊥ := by
  have hconj : conjSubgroup (piK V H y) (imgK V H (Pc M V)) =
      imgK V H (conjSubgroup (y : G) (Pc M V)) :=
    (imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) y.2 hPH).symm
  rw [hconj]
  by_contra hne
  obtain ⟨tbar, htbar1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have htbar1' : (tbar : HBar V H) ≠ 1 := fun h => htbar1 (Subtype.ext h)
  have htbarP : (tbar : HBar V H) ∈ imgK V H (Pc M V) := tbar.2.1
  have htbarPy : (tbar : HBar V H) ∈ imgK V H (conjSubgroup (y : G) (Pc M V)) := tbar.2.2
  obtain ⟨x₀, hx₀P, hx₀pi⟩ := mem_imgK_iff.mp htbarP
  set t : G := (x₀ : G) with ht
  have htP : t ∈ Pc M V := hx₀P
  have htH : t ∈ H := hPH htP
  let N : Subgroup G := Tim79a.xOf V H ⊓ Pc M V ⊓
    ⨅ p : ↥(Pc M V), conjSubgroup ((p : G) * (y : G)) (Pc M V)
  have hNdef : N = Tim79a.xOf V H ⊓ Pc M V ⊓
      ⨅ p : ↥(Pc M V), conjSubgroup ((p : G) * (y : G)) (Pc M V) := rfl
  have hN_le_W : N ≤ Tim79a.xOf V H := inf_le_left.trans inf_le_left
  have hN_le_P : N ≤ Pc M V := inf_le_left.trans inf_le_right
  have hN_le_iInf : N ≤ ⨅ p : ↥(Pc M V),
      conjSubgroup ((p : G) * (y : G)) (Pc M V) := inf_le_right
  have hN_le_Py : N ≤ conjSubgroup (y : G) (Pc M V) := by
    refine hN_le_iInf.trans ?_
    have hle := iInf_le (fun p : ↥(Pc M V) =>
      conjSubgroup ((p : G) * (y : G)) (Pc M V)) (1 : ↥(Pc M V))
    simpa using hle
  have hbar_in_py := isTI_hbar_in_py h hPH hVH htbarP htbarPy
  have hcomm_mem := isTI_hkey_comm_mem h hPH hVH ht htH hx₀P hx₀pi
    hbar_in_py hNdef
  have hPN := isTI_hPN h hPH hNdef
  exact isTI_ne_final h hVy hN_le_P hN_le_Py hPN ht htH hx₀pi htbar1' hcomm_mem

theorem isTI_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) : IsTI (imgK V H (Pc M V)) := by
  classical
  intro gbar
  obtain ⟨y, rfl⟩ := piK_surjective V H gbar
  by_cases hVy : conjSubgroup (y : G) V = V
  · exact Or.inr (isTI_imgK_eq h hPH hVy)
  · exact Or.inl (isTI_imgK_ne h hPH hVH hVy)

private theorem inf_centralizer_ne_bot_of_isPGroup {A W : Subgroup G} (hA : IsPGroup 2 A)
    (hW : IsPGroup 2 W) (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hWne : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := A ⊔ W with hRdef
  have hR2 : IsPGroup 2 R := hA.to_sup_of_normal_right' hW hAW
  have hWR : W ≤ R := le_sup_right
  have hRN : R ≤ Subgroup.normalizer (W : Set G) :=
    sup_le hAW (Subgroup.le_normalizer (H := W))
  haveI hNormal : (W.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hRN
  have hWne' : W.subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hWne
    have h := congrArg (Subgroup.map R.subtype) hbot
    rw [Subgroup.map_subgroupOf_eq_of_le hWR, Subgroup.map_bot] at h
    exact h
  haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥R)
    (H := W.subgroupOf R) hWne'
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hzW : ((z : ↥R) : G) ∈ W := Subgroup.mem_subgroupOf.mp z.2.1
  have hzC : ((z : ↥R) : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haR : a ∈ R := Subgroup.mem_sup_left ha
    have hcomm := Subgroup.mem_center_iff.mp z.2.2 (⟨a, haR⟩ : ↥R)
    exact congrArg Subtype.val hcomm
  intro hbot
  have hmem : ((z : ↥R) : G) ∈ W ⊓ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_inf.mpr ⟨hzW, hzC⟩
  rw [hbot] at hmem
  have hz1' : ((z : ↥R) : G) = 1 := Subgroup.mem_bot.mp hmem
  exact hz1 (Subtype.ext (by simpa using hz1'))

end RootHyp

omit [Finite G] in
theorem imgK_eq_iff_sup_kOf_eq {S T : Subgroup G} (hS : S ≤ H) (hT : T ≤ H) :
    imgK V H S = imgK V H T ↔ S ⊔ kOf V H = T ⊔ kOf V H := by
  constructor
  · intro h
    have key : ∀ {S T : Subgroup G}, S ≤ H → T ≤ H → imgK V H S = imgK V H T →
        S ≤ T ⊔ kOf V H := by
      intro S T hS hT hST x hx
      have hmem : piK V H ⟨x, hS hx⟩ ∈ imgK V H S :=
        Subgroup.mem_map.mpr ⟨⟨x, hS hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hST] at hmem
      obtain ⟨z, hzT, hzpi⟩ := mem_imgK_iff.mp hmem
      have hdiv : (z / ⟨x, hS hx⟩) ∈ (kOf V H).subgroupOf H :=
        (QuotientGroup.eq_iff_div_mem).mp hzpi
      have hdiv' : (⟨x, hS hx⟩ / z) ∈ (kOf V H).subgroupOf H := by
        have := Subgroup.inv_mem _ hdiv
        simpa [div_eq_mul_inv] using this
      rw [Subgroup.mem_subgroupOf] at hdiv'
      have hK : x * (z : G)⁻¹ ∈ kOf V H := by
        simpa [div_eq_mul_inv] using hdiv'
      have hmem2 : (x * (z : G)⁻¹) * (z : G) ∈ kOf V H ⊔ T :=
        Subgroup.mul_mem_sup hK hzT
      rw [sup_comm] at hmem2
      have hx' : x = (x * (z : G)⁻¹) * (z : G) := by group
      rw [← hx'] at hmem2
      exact hmem2
    have hTS : T ≤ S ⊔ kOf V H := key (S := T) (T := S) hT hS h.symm
    refine le_antisymm ?_ ?_
    · exact sup_le (key (S := S) (T := T) hS hT h) le_sup_right
    · exact sup_le hTS le_sup_right
  · intro h
    have key2 : ∀ {S T : Subgroup G}, S ≤ H → T ≤ H → S ⊔ kOf V H = T ⊔ kOf V H →
        imgK V H S ≤ imgK V H T := by
      intro S T hS hT hST y hy
      obtain ⟨x, hxS, rfl⟩ := mem_imgK_iff.mp hy
      have hx : (x : G) ∈ T ⊔ kOf V H := by
        have hle : (x : G) ∈ S ⊔ kOf V H := Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hxS)
        rwa [hST] at hle
      have hx' : (x : G) ∈ (kOf V H ⊔ T : Subgroup G) := by rwa [sup_comm]
      obtain ⟨k, hkK, t, htT, hxeq⟩ := exists_mul_of_mem_sup (V := kOf V H) (U := T)
        (hT.trans (le_normalizer_kOf V H)) hx'
      have hkH : k ∈ H := kOf_le V H hkK
      have htH : t ∈ H := hT htT
      have hxe : x = (⟨k, hkH⟩ : ↥H) * ⟨t, htH⟩ := Subtype.ext (by
        change (x : G) = k * t
        exact hxeq)
      rw [hxe, map_mul, (piK_eq_one_iff (⟨k, hkH⟩ : ↥H)).mpr hkK, one_mul]
      exact Subgroup.mem_map.mpr ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩
    exact le_antisymm (key2 hS hT h) (key2 hT hS h.symm)

namespace RootHyp

private theorem conj_mem_normalizer_sup_kOf (hPH : Pc M V ≤ H)
    {g : G} (hg : g ∈ H)
    (hnorm : imgK V H (conjSubgroup g (Pc M V)) ≤
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))) :
    ∀ p ∈ Pc M V, MulAut.conj g p ∈
      Subgroup.normalizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left

  have key : ∀ p ∈ Pc M V,
      MulAut.conj g p ∈ Subgroup.normalizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) := by
    intro p hpP
    have hxp : MulAut.conj g p ∈ conjSubgroup g (Pc M V) := Subgroup.mem_map.mpr ⟨p, hpP, rfl⟩
    have hxH : MulAut.conj g p ∈ H := conjSubgroup_le_of_le_of_mem hPH hg hxp
    have hx_eq : (⟨MulAut.conj g p, hxH⟩ : ↥H) =
        ⟨g, hg⟩ * ⟨p, hPH hpP⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply])
    have hpi : piK V H ⟨MulAut.conj g p, hxH⟩ =
        MulAut.conj (piK V H ⟨g, hg⟩) (piK V H ⟨p, hPH hpP⟩) := by
      rw [hx_eq, map_mul, map_mul, map_inv, MulAut.conj_apply]
    have hmemImg : piK V H ⟨MulAut.conj g p, hxH⟩ ∈ imgK V H (conjSubgroup g (Pc M V)) :=
      Subgroup.mem_map.mpr ⟨⟨MulAut.conj g p, hxH⟩, Subgroup.mem_subgroupOf.mpr hxp, rfl⟩
    have hconjEq : conjSubgroup (piK V H ⟨MulAut.conj g p, hxH⟩) (imgK V H (Pc M V)) =
        imgK V H (Pc M V) := conjSubgroup_eq_self_iff.mpr (hnorm hmemImg)
    have himg : imgK V H (conjSubgroup (MulAut.conj g p) (Pc M V)) = imgK V H (Pc M V) := by
      rw [imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) hxH hPH, hpi]
      exact hconjEq
    have hle : conjSubgroup (MulAut.conj g p) (Pc M V) ≤ H :=
      conjSubgroup_le_of_le_of_mem hPH hxH
    have hsup : conjSubgroup (MulAut.conj g p) (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H :=
      (imgK_eq_iff_sup_kOf_eq (V := V) (H := H) hle hPH).mp himg
    have hconjK : conjSubgroup (MulAut.conj g p) (kOf V H) = kOf V H :=
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hxH)
    have hsup' : conjSubgroup (MulAut.conj g p) (Pc M V ⊔ kOf V H) = Pc M V ⊔ kOf V H := by
      rw [show conjSubgroup (MulAut.conj g p) (Pc M V ⊔ kOf V H) =
        conjSubgroup (MulAut.conj g p) (Pc M V) ⊔ conjSubgroup (MulAut.conj g p) (kOf V H)
        from Subgroup.map_sup _ _ _, hconjK, hsup]
    exact conjSubgroup_eq_self_iff.mp hsup'
  exact key

private theorem V_eq_inf_centralizer_sup_kOf (h : RootHyp M V) (hPH : Pc M V ≤ H) :
    V = Tim79a.xOf V H ⊓
      Subgroup.centralizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) := by

  have hVW : V ≤ Tim79a.xOf V H := by
    simpa [conjSubgroup_one] using Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf (V := V)
      (H := H) (h := 1) H.one_mem)
  have hVeq : V = Tim79a.xOf V H ⊓
      Subgroup.centralizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) := by
    have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
      rw [h.toHyp.centralizer_Pc]
    have hVK : V ≤ Subgroup.centralizer (kOf V H : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp hk.2 v (hVW hv)).symm
    refine le_antisymm ?_ ?_
    · intro v hv
      refine Subgroup.mem_inf.mpr ⟨hVW hv, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ (kOf V H ⊔ Pc M V : Subgroup G) := by rwa [sup_comm]
      obtain ⟨k, hkK, p, hpP, rfl⟩ := exists_mul_of_mem_sup (V := kOf V H) (U := Pc M V)
        (hPH.trans (le_normalizer_kOf V H)) hy'
      calc k * p * v = k * (p * v) := by group
        _ = k * (v * p) := by rw [Subgroup.mem_centralizer_iff.mp (hVP hv) p hpP]
        _ = (k * v) * p := by group
        _ = (v * k) * p := by rw [Subgroup.mem_centralizer_iff.mp (hVK hv) k hkK]
        _ = v * (k * p) := by group
    · intro y hy
      have hyP : y ∈ Subgroup.centralizer (Pc M V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        exact Subgroup.mem_centralizer_iff.mp hy.2 p (Subgroup.mem_sup_left hp)
      have hmem : y ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer (Pc M V : Set G) :=
        Subgroup.mem_inf.mpr ⟨hy.1, hyP⟩
      have hEq := xOf_inf_centralizer_conj_Pc h (x := 1) H.one_mem
      simp only [conjSubgroup_one] at hEq
      rwa [hEq] at hmem
  exact hVeq

theorem weaklyClosed_imgK (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {g : G} (hg : g ∈ H)
    (hnorm : imgK V H (conjSubgroup g (Pc M V)) ≤
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))) :
    imgK V H (conjSubgroup g (Pc M V)) = imgK V H (Pc M V) := by
  classical
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have key := conj_mem_normalizer_sup_kOf hPH hg hnorm
  have hVeq := V_eq_inf_centralizer_sup_kOf h hPH
  have hPg_M : conjSubgroup g (Pc M V) ≤ M := by
    intro x hx
    rw [← h.toHyp.normalizer_eq, hVeq]
    obtain ⟨p, hpP, rfl⟩ := Subgroup.mem_map.mp hx
    have hxp : MulAut.conj g p ∈ conjSubgroup g (Pc M V) := Subgroup.mem_map.mpr ⟨p, hpP, rfl⟩
    have hxH : MulAut.conj g p ∈ H := conjSubgroup_le_of_le_of_mem hPH hg hxp
    exact mem_normalizer_inf (Tim79a.H_le_normalizer_xOf V H hxH)
      (mem_normalizer_centralizer (key p hpP))
  have hPg2 : IsPGroup 2 (conjSubgroup g (Pc M V)) := hP2.map (MulAut.conj g).toMonoidHom
  have hfix : V ⊓ Subgroup.centralizer (conjSubgroup g (Pc M V) : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_isPGroup hPg2 h.toHyp.isPGroup_V
      (by rwa [h.toHyp.normalizer_eq]) h.toHyp.ne_bot
  have hfixV : V ⊓ conjSubgroup g V ≠ ⊥ := by
    have hle : V ⊓ Subgroup.centralizer (conjSubgroup g (Pc M V) : Set G) ≤
        V ⊓ conjSubgroup g V :=
      inf_le_inf_left V (le_of_eq (h.toHyp.centralizer_conj_Pc g))
    intro hbot
    exact hfix (le_bot_iff.mp (hle.trans (le_of_eq hbot)))
  have hVg : conjSubgroup g V = V := conjSubgroup_eq_of_isTI h.toHyp.ti hfixV
  have hgM : g ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact conjSubgroup_eq_self_iff.mp hVg
  have hPgP : conjSubgroup g (Pc M V) = Pc M V := by
    rw [conjSubgroup_eq_self_iff]
    exact h.toHyp.le_normalizer_Pc hgM
  rw [hPgP]

theorem xOf_inf_centralizer_sup_kOf_eq (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {x : G} (hx : x ∈ H) :
    Tim79a.xOf V H ⊓
        Subgroup.centralizer ((conjSubgroup x (Pc M V) ⊔ kOf V H : Subgroup G) : Set G) =
      conjSubgroup x V := by
  refine le_antisymm ?_ ?_
  · intro y hy
    have hyP : y ∈ Subgroup.centralizer (conjSubgroup x (Pc M V) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact Subgroup.mem_centralizer_iff.mp hy.2 p (Subgroup.mem_sup_left hp)
    have hmem : y ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer (conjSubgroup x (Pc M V) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hy.1, hyP⟩
    rwa [xOf_inf_centralizer_conj_Pc h hx] at hmem
  · intro y hy
    have hyW : y ∈ Tim79a.xOf V H := Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hx) hy
    have hyC : y ∈ Subgroup.centralizer (conjSubgroup x (Pc M V) : Set G) := by
      have hEq := xOf_inf_centralizer_conj_Pc h hx
      have hmem : y ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer (conjSubgroup x (Pc M V) : Set G) := by
        rw [hEq]
        exact hy
      exact hmem.2
    have hyK : y ∈ Subgroup.centralizer (kOf V H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact ((Subgroup.mem_centralizer_iff.mp hk.2) y hyW).symm
    refine Subgroup.mem_inf.mpr ⟨hyW, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ (kOf V H ⊔ conjSubgroup x (Pc M V) : Subgroup G) := by rwa [sup_comm]
    obtain ⟨k, hkK, p, hpP, rfl⟩ := exists_mul_of_mem_sup (V := kOf V H)
      (U := conjSubgroup x (Pc M V))
      ((conjSubgroup_le_of_le_of_mem hPH hx).trans (le_normalizer_kOf V H)) hz'
    calc k * p * y = k * (p * y) := by group
      _ = k * (y * p) := by rw [Subgroup.mem_centralizer_iff.mp hyC p hpP]
      _ = (k * y) * p := by group
      _ = (y * k) * p := by rw [Subgroup.mem_centralizer_iff.mp hyK k hkK]
      _ = y * (k * p) := by group

private theorem normalizer_imgK_mp (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {g : G} (hg : g ∈ H)
    (hgV : conjSubgroup g V ≠ V) {t : G} (htP : t ∈ Pc M V)
    (hnorm : piK V H ⟨t, hPH htP⟩ ∈ Subgroup.normalizer
        (imgK V H (conjSubgroup g (Pc M V)) : Set (HBar V H))) :
    t ∈ Subgroup.centralizer (conjSubgroup g V : Set G) := by
  have htH : t ∈ H := hPH htP
  have hPgH : conjSubgroup g (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hg
  have hconjEq : conjSubgroup (piK V H ⟨t, htH⟩) (imgK V H (conjSubgroup g (Pc M V))) =
      imgK V H (conjSubgroup g (Pc M V)) := conjSubgroup_eq_self_iff.mpr hnorm
  have hle : conjSubgroup t (conjSubgroup g (Pc M V)) ≤ H :=
    conjSubgroup_le_of_le_of_mem hPgH htH
  have himg : imgK V H (conjSubgroup t (conjSubgroup g (Pc M V))) =
      imgK V H (conjSubgroup g (Pc M V)) := by
    rw [imgK_conjSubgroup (V := V) (H := H) (S := conjSubgroup g (Pc M V)) htH hPgH]
    exact hconjEq
  have hsup : conjSubgroup t (conjSubgroup g (Pc M V)) ⊔ kOf V H =
      conjSubgroup g (Pc M V) ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq (V := V) (H := H) hle hPgH).mp himg
  have ht_norm : t ∈ Subgroup.normalizer
      ((conjSubgroup g (Pc M V) ⊔ kOf V H : Subgroup G) : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    rw [show conjSubgroup t (conjSubgroup g (Pc M V) ⊔ kOf V H) =
      conjSubgroup t (conjSubgroup g (Pc M V)) ⊔ conjSubgroup t (kOf V H)
      from Subgroup.map_sup _ _ _,
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H htH), hsup]
  have htVg : t ∈ Subgroup.normalizer (conjSubgroup g V : Set G) := by
    rw [← xOf_inf_centralizer_sup_kOf_eq h hPH hg]
    exact mem_normalizer_inf (Tim79a.H_le_normalizer_xOf V H htH)
      (mem_normalizer_centralizer ht_norm)
  have hVgP : conjSubgroup g V ⊓ Pc M V = ⊥ := by
    by_contra hcon
    have hne : V ⊓ conjSubgroup g⁻¹ (Pc M V) ≠ ⊥ := by
      intro hbot
      apply hcon
      have h := congrArg (conjSubgroup g) hbot
      rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
      rw [h]
      exact conjSubgroup_eq_bot_iff.mpr rfl
    have hEq : conjSubgroup g⁻¹ V = V := conj_eq_of_inf_conj_Pc_ne_bot h hne
    have h2 : conjSubgroup g (conjSubgroup g⁻¹ V) = conjSubgroup g V := by rw [hEq]
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
    exact hgV h2.symm
  have hcomm_inf : ⁅conjSubgroup g V, Subgroup.zpowers t⁆ ≤ conjSubgroup g V ⊓ Pc M V := by
    refine le_inf ?_ ?_
    · refine (Subgroup.le_normalizer_iff_commutator_le_left
        (H := Subgroup.zpowers t) (K := conjSubgroup g V)).mp ?_
      exact Subgroup.zpowers_le.mpr htVg
    · have hleP : ⁅Pc M V, conjSubgroup g V⁆ ≤ Pc M V :=
        (Subgroup.le_normalizer_iff_commutator_le_left
          (H := conjSubgroup g V) (K := Pc M V)).mp
          ((Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hg)).trans
            ((xOf_le_M h hPH hVH).trans h.toHyp.le_normalizer_Pc))
      have hmono : ⁅conjSubgroup g V, Subgroup.zpowers t⁆ ≤
          ⁅conjSubgroup g V, Pc M V⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr htP)
      rw [Subgroup.commutator_comm (conjSubgroup g V) (Pc M V)] at hmono
      exact hmono.trans hleP
  have hcomm_bot : ⁅conjSubgroup g V, Subgroup.zpowers t⁆ = ⊥ := by
    rw [hVgP] at hcomm_inf
    exact le_bot_iff.mp hcomm_inf
  rw [Subgroup.commutator_comm] at hcomm_bot
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot (Subgroup.mem_zpowers t)
private theorem normalizer_imgK_mpr (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {g : G} (hg : g ∈ H) {t : G} (htP : t ∈ Pc M V)
    (htC : t ∈ Subgroup.centralizer (conjSubgroup g V : Set G)) :
    piK V H ⟨t, hPH htP⟩ ∈ Subgroup.normalizer
      (imgK V H (conjSubgroup g (Pc M V)) : Set (HBar V H)) := by
  have htH : t ∈ H := hPH htP
  have hPgH : conjSubgroup g (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hg

  have htVg : t ∈ Subgroup.normalizer (conjSubgroup g V : Set G) :=
    Subgroup.centralizer_le_normalizer _ htC
  have htMg : t ∈ conjSubgroup g M := by
    have hmem := htVg
    rw [normalizer_conjSubgroup, h.toHyp.normalizer_eq] at hmem
    exact hmem
  have htNP : t ∈ Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) := by
    rw [normalizer_conjSubgroup]
    exact Subgroup.map_mono h.toHyp.le_normalizer_Pc htMg
  have hconj : conjSubgroup t (conjSubgroup g (Pc M V)) = conjSubgroup g (Pc M V) :=
    conjSubgroup_eq_self_iff.mpr htNP
  rw [← conjSubgroup_eq_self_iff]
  rw [← imgK_conjSubgroup (V := V) (H := H) (S := conjSubgroup g (Pc M V)) htH hPgH]
  rw [hconj]

theorem normalizer_imgK_iff (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {g : G} (hg : g ∈ H)
    (hgV : conjSubgroup g V ≠ V) {t : G} (htP : t ∈ Pc M V) :
    piK V H ⟨t, hPH htP⟩ ∈ Subgroup.normalizer
        (imgK V H (conjSubgroup g (Pc M V)) : Set (HBar V H)) ↔
      t ∈ Subgroup.centralizer (conjSubgroup g V : Set G) := by
  exact ⟨normalizer_imgK_mp h hPH hVH hg hgV htP,
    normalizer_imgK_mpr h hPH hg htP⟩

theorem imgK_ne_bot_and_ne_of_sup (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    imgK V H (Pc M V) ≠ ⊥ ∧
      imgK V H (Pc M V) ≠ imgK V H (conjSubgroup h₀ (Pc M V)) := by
  classical
  obtain ⟨y, hyH, hPy₀, hVy₀⟩ := Hyp.exists_mem_conj_eq_of_conj_Pc_le h.toHyp hPH
    (g := h₀) (by rw [hH]; exact le_sup_right)
  have hH' : H = Pc M V ⊔ conjSubgroup y (Pc M V) := by rw [hH, hPy₀]
  have hVPy : conjSubgroup y (Pc M V) ≤ H := by rw [hH']; exact le_sup_right
  have contra : conjSubgroup y V = V → False := by
    intro hVy
    have hyM : y ∈ M := by
      rw [← h.toHyp.normalizer_eq]
      exact conjSubgroup_eq_self_iff.mp hVy
    have hPy : conjSubgroup y (Pc M V) = Pc M V := by
      rw [conjSubgroup_eq_self_iff]
      exact h.toHyp.le_normalizer_Pc hyM
    apply hnM
    rw [hH', hPy, sup_idem]
    exact h.toHyp.Pc_le_M
  constructor
  · intro himg
    have hPK : Pc M V ≤ kOf V H := by
      intro p hp
      have hmem : piK V H ⟨p, hPH hp⟩ ∈ imgK V H (Pc M V) :=
        Subgroup.mem_map.mpr ⟨⟨p, hPH hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
      rw [himg] at hmem
      exact (piK_eq_one_iff (⟨p, hPH hp⟩ : ↥H)).mp (Subgroup.mem_bot.mp hmem)
    have hWCP : Tim79a.xOf V H ≤ Subgroup.centralizer (Pc M V : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (Subgroup.mem_centralizer_iff.mp (hPK hp).2 w hw).symm
    have hWV : Tim79a.xOf V H ≤ V := by
      rwa [h.toHyp.centralizer_Pc] at hWCP
    have hle : conjSubgroup y V ≤ V :=
      (Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hyH)).trans hWV
    have heq : conjSubgroup y V = V :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
    exact contra heq
  · intro heq
    have heq' : imgK V H (Pc M V) = imgK V H (conjSubgroup y (Pc M V)) := by rwa [← hPy₀]
    have hsup : Pc M V ⊔ kOf V H = conjSubgroup y (Pc M V) ⊔ kOf V H :=
      (imgK_eq_iff_sup_kOf_eq (V := V) (H := H) hPH hVPy).mp heq'
    have hV1 := xOf_inf_centralizer_sup_kOf_eq h hPH (x := 1) H.one_mem
    simp only [conjSubgroup_one] at hV1
    have hVy1 := xOf_inf_centralizer_sup_kOf_eq h hPH hyH
    have hVeq : V = conjSubgroup y V := by
      have h2 : Tim79a.xOf V H ⊓
          Subgroup.centralizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) =
          Tim79a.xOf V H ⊓
            Subgroup.centralizer ((conjSubgroup y (Pc M V) ⊔ kOf V H : Subgroup G) : Set G) := by
        rw [hsup]
      exact hV1.symm.trans (h2.trans hVy1)
    exact contra hVeq.symm

private theorem commutatorElement_mul_right_of_centralizes {W : Subgroup G} {k w x : G}
    (hw : w ∈ W) (hk : k ∈ Subgroup.centralizer (W : Set G)) :
    ⁅w, x * k⁆ = ⁅w, x⁆ := by
  have hkw : w * k = k * w := Subgroup.mem_centralizer_iff.mp hk w hw
  have hkw' : k * w⁻¹ = w⁻¹ * k := by
    calc k * w⁻¹ = w⁻¹ * (w * k) * w⁻¹ := by group
      _ = w⁻¹ * (k * w) * w⁻¹ := by rw [← hkw]
      _ = w⁻¹ * k := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc w * (x * k) * w⁻¹ * (x * k)⁻¹
      = w * x * (k * w⁻¹) * k⁻¹ * x⁻¹ := by group
    _ = w * x * (w⁻¹ * k) * k⁻¹ * x⁻¹ := by rw [hkw']
    _ = w * x * w⁻¹ * x⁻¹ := by group

private theorem commutatorElement_mul_left_eq_of_centralizes {W : Subgroup G} {k a x : G}
    (ha : a * x * a⁻¹ ∈ W) (hk : k ∈ Subgroup.centralizer (W : Set G)) :
    ⁅k * a, x⁆ = ⁅a, x⁆ := by
  have hk' : (a * x * a⁻¹) * k = k * (a * x * a⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hk _ ha
  rw [commutatorElement_def, commutatorElement_def]
  calc (k * a) * x * (k * a)⁻¹ * x⁻¹
      = k * (a * x * a⁻¹) * k⁻¹ * x⁻¹ := by group
    _ = (a * x * a⁻¹) * k * k⁻¹ * x⁻¹ := by rw [← hk']
    _ = a * x * a⁻¹ * x⁻¹ := by group

private theorem exists_mul_zpowers_of_mem_pc
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {xα : ↥H} {α : G} (hα : α = (xα : G))
    {abar : ↥(imgK V H (Pc M V))}
    (hαP : α ∈ Pc M V) (hαH : α ∈ H)
    (hαpi : piK V H xα = (abar : HBar V H))
    (hbar_uniq : ∀ b : ↥(imgK V H (Pc M V)), b ≠ 1 → b = abar) :
    ∀ p ∈ Pc M V, ∃ k ∈ Pc M V ⊓ kOf V H,
      ∃ a ∈ Subgroup.zpowers α, p = k * a := by
  have hdecomp : Pc M V = (Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers α := by
    refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.zpowers_le.mpr hαP))
    intro p hp
    by_cases hpK : p ∈ kOf V H
    · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hp, hpK⟩)
    · have hbar_p : (⟨piK V H ⟨p, hPH hp⟩,
          Subgroup.mem_map.mpr ⟨⟨p, hPH hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩⟩ :
          ↥(imgK V H (Pc M V))) = abar := by
        refine hbar_uniq _ ?_
        intro h
        exact hpK ((piK_eq_one_iff (⟨p, hPH hp⟩ : ↥H)).mp (congrArg Subtype.val h))
      have hpi : piK V H ⟨p, hPH hp⟩ = piK V H xα := by
        have h1 : piK V H ⟨p, hPH hp⟩ = (abar : HBar V H) := congrArg Subtype.val hbar_p
        rw [h1, ← hαpi]
      have hmemK : p * α⁻¹ ∈ kOf V H := by
        have h1 : piK V H ⟨p * α⁻¹, H.mul_mem (hPH hp) (H.inv_mem hαH)⟩ = 1 := by
          rw [show (⟨p * α⁻¹, H.mul_mem (hPH hp) (H.inv_mem hαH)⟩ : ↥H) =
            ⟨p, hPH hp⟩ * xα⁻¹ from Subtype.ext (by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα])]
          rw [map_mul, map_inv, hpi, mul_inv_cancel]
        exact (piK_eq_one_iff _).mp h1
      have hp_eq : p = (p * α⁻¹) * α := by group
      rw [hp_eq]
      exact Subgroup.mul_mem_sup
        (Subgroup.mem_inf.mpr ⟨Pc M V |>.mul_mem hp (Pc M V |>.inv_mem hαP), hmemK⟩)
        (Subgroup.mem_zpowers α)
  have hP_mul : ∀ p ∈ Pc M V, ∃ k ∈ Pc M V ⊓ kOf V H,
      ∃ a ∈ Subgroup.zpowers α, p = k * a := by
    intro p hp
    have hmem : p ∈ (Pc M V ⊓ kOf V H) ⊔ Subgroup.zpowers α := by rw [← hdecomp]; exact hp
    refine exists_mul_of_mem_sup (V := Pc M V ⊓ kOf V H) (U := Subgroup.zpowers α) ?_ hmem
    refine Subgroup.zpowers_le.mpr ?_
    exact mem_normalizer_inf (Subgroup.le_normalizer (H := Pc M V) hαP)
      (le_normalizer_kOf V H hαH)
  exact hP_mul

private theorem commutator_mem_V_of_mem_xOf
    (h : RootHyp M V) {α : G}
    (hαH : α ∈ H)
    (hEab : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (hα2K : α ^ 2 ∈ kOf V H)
    (hP_mul : ∀ p ∈ Pc M V, ∃ k ∈ Pc M V ⊓ kOf V H,
      ∃ a ∈ Subgroup.zpowers α, p = k * a) :
    ∀ w ∈ Tim79a.xOf V H, ⁅w, α⁆ ∈ V := by
  intro w hw
  have hzW : ⁅w, α⁆ ∈ Tim79a.xOf V H := by
    have hNW : α ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
      Tim79a.H_le_normalizer_xOf V H hαH
    have hmem : α * w⁻¹ * α⁻¹ ∈ Tim79a.xOf V H :=
      (Subgroup.mem_normalizer_iff.mp hNW w⁻¹).mp ((Tim79a.xOf V H).inv_mem hw)
    have h := (Tim79a.xOf V H).mul_mem hw hmem
    rw [commutatorElement_def, show w * α * w⁻¹ * α⁻¹ = w * (α * w⁻¹ * α⁻¹) by group]
    exact h
  have hw2 : w * w = 1 := by
    simpa [pow_two] using hEab.2 w hw
  have hw2' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hα2w : α ^ 2 * w * (α ^ 2)⁻¹ = w := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hα2K.2 w hw
    calc α ^ 2 * w * (α ^ 2)⁻¹ = (w * α ^ 2) * (α ^ 2)⁻¹ := by rw [hcomm]
      _ = w := by group
  have hαwW : α * w * α⁻¹ ∈ Tim79a.xOf V H :=
    (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hαH) w).mp hw
  have hab : (α * w * α⁻¹) * w⁻¹ = w⁻¹ * (α * w * α⁻¹) :=
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨_, hαwW⟩ ⟨_, (Tim79a.xOf V H).inv_mem hw⟩)
  have hfix : α * ⁅w, α⁆ * α⁻¹ = ⁅w, α⁆ := by
    rw [commutatorElement_def]
    calc α * (w * α * w⁻¹ * α⁻¹) * α⁻¹
        = (α * w * α⁻¹) * (α ^ 2 * w⁻¹ * (α ^ 2)⁻¹) := by group
      _ = (α * w * α⁻¹) * w⁻¹ := by rw [hw2', hα2w]
      _ = w⁻¹ * (α * w * α⁻¹) := hab
      _ = w * α * w⁻¹ * α⁻¹ := by rw [hw2']; group
  have hzα : α * ⁅w, α⁆ = ⁅w, α⁆ * α := by
    calc α * ⁅w, α⁆ = (α * ⁅w, α⁆ * α⁻¹) * α := by group
      _ = ⁅w, α⁆ * α := by rw [hfix]
  have hzC : ⁅w, α⁆ ∈ Subgroup.centralizer (Pc M V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨k, hkPK, a, haZ, rfl⟩ := hP_mul p hp
    have hza : a * ⁅w, α⁆ = ⁅w, α⁆ * a :=
      Subgroup.mem_centralizer_singleton_iff.mp
        ((Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzα)) haZ)
    have hzk : k * ⁅w, α⁆ = ⁅w, α⁆ * k := by
      have h := Subgroup.mem_centralizer_iff.mp hkPK.2.2 (⁅w, α⁆) hzW
      exact h.symm
    calc k * a * ⁅w, α⁆ = k * (a * ⁅w, α⁆) := by group
      _ = k * (⁅w, α⁆ * a) := by rw [hza]
      _ = (k * ⁅w, α⁆) * a := by group
      _ = (⁅w, α⁆ * k) * a := by rw [hzk]
      _ = ⁅w, α⁆ * (k * a) := by group
  have hEq := xOf_inf_centralizer_conj_Pc h (x := 1) H.one_mem
  simp only [conjSubgroup_one] at hEq
  rw [← hEq]
  exact Subgroup.mem_inf.mpr ⟨hzW, hzC⟩

private theorem commutator_xOf_zpowers_le_V
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {xα : ↥H} {α : G} (hα : α = (xα : G))
    {abar : ↥(imgK V H (Pc M V))}
    (hαP : α ∈ Pc M V) (hαH : α ∈ H)
    (hαpi : piK V H xα = (abar : HBar V H))
    (hbar_uniq : ∀ b : ↥(imgK V H (Pc M V)), b ≠ 1 → b = abar)
    (hpoint : ∀ w ∈ Tim79a.xOf V H, ⁅w, α⁆ ∈ V) :
    ⁅Tim79a.xOf V H, Subgroup.zpowers α⁆ ≤ V := by
  have hV_le_C : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [h.toHyp.centralizer_Pc]
  have hmain : ⁅Tim79a.xOf V H, Subgroup.zpowers α⁆ ≤
      Subgroup.centralizer (Pc M V : Set G) := by
    refine Subgroup.commutator_le.mpr fun w hw a ha => ?_
    by_cases haK : a ∈ kOf V H
    · have h1 : ⁅w, a⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_commute]
        exact Subgroup.mem_centralizer_iff.mp haK.2 w hw
      rw [h1]
      exact (Subgroup.centralizer (Pc M V : Set G)).one_mem
    · have haP : a ∈ Pc M V := Subgroup.zpowers_le.mpr hαP ha
      have hbar_a : (⟨piK V H ⟨a, hPH haP⟩,
          Subgroup.mem_map.mpr ⟨⟨a, hPH haP⟩, Subgroup.mem_subgroupOf.mpr haP, rfl⟩⟩ :
          ↥(imgK V H (Pc M V))) = abar := by
        refine hbar_uniq _ ?_
        intro h
        exact haK ((piK_eq_one_iff (⟨a, hPH haP⟩ : ↥H)).mp (congrArg Subtype.val h))
      have hpi : piK V H ⟨a, hPH haP⟩ = piK V H xα := by
        have h1 : piK V H ⟨a, hPH haP⟩ = (abar : HBar V H) := congrArg Subtype.val hbar_a
        rw [h1, ← hαpi]
      have hmemK : a * α⁻¹ ∈ kOf V H := by
        have h1 : piK V H ⟨a * α⁻¹, H.mul_mem (hPH haP) (H.inv_mem hαH)⟩ = 1 := by
          rw [show (⟨a * α⁻¹, H.mul_mem (hPH haP) (H.inv_mem hαH)⟩ : ↥H) =
            ⟨a, hPH haP⟩ * xα⁻¹ from Subtype.ext (by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα])]
          rw [map_mul, map_inv, hpi, mul_inv_cancel]
        exact (piK_eq_one_iff _).mp h1
      have haeq : a = α * (α⁻¹ * a) := by group
      have hmemK' : α⁻¹ * a ∈ kOf V H := by
        have h2 : piK V H ⟨α⁻¹ * a, H.mul_mem (H.inv_mem hαH) (hPH haP)⟩ = 1 := by
          rw [show (⟨α⁻¹ * a, H.mul_mem (H.inv_mem hαH) (hPH haP)⟩ : ↥H) =
            xα⁻¹ * ⟨a, hPH haP⟩ from Subtype.ext (by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα])]
          rw [map_mul, map_inv, hpi, inv_mul_cancel]
        exact (piK_eq_one_iff _).mp h2
      rw [haeq]
      have hcomm1 : ⁅w, α * (α⁻¹ * a)⁆ = ⁅w, α⁆ :=
        commutatorElement_mul_right_of_centralizes hw hmemK'.2
      rw [hcomm1]
      exact hV_le_C (hpoint w hw)
  rwa [h.toHyp.centralizer_Pc] at hmain

private theorem false_of_commutator_conj_V_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    (hEab : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V))
    (hnM : ¬ H ≤ M)
    (hcommPV : ⁅Pc M V, conjSubgroup y V⁆ ≤ V) : False := by
  have hVyW : conjSubgroup y V ≤ Tim79a.xOf V H :=
    Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hyH)
  have hVyC : conjSubgroup y V ≤ Subgroup.centralizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hvW : v ∈ Tim79a.xOf V H := hVyW hv
    have hwW : w ∈ Tim79a.xOf V H := by
      have h1 : w ∈ conjSubgroup 1 V := by rwa [conjSubgroup_one]
      exact Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf (V := V) (H := H) (h := 1)
        H.one_mem) h1
    exact (congrArg Subtype.val (hEab.1.is_comm.comm ⟨v, hvW⟩ ⟨w, hwW⟩)).symm
  have hVyQ : conjSubgroup y V ≤ inSubgroup (pCore 2) M :=
    h.toHyp.le_pCore_of_commutator_le (hVyW.trans (xOf_le_M h hPH hVH)) hVyC hcommPV
  have hVyP : conjSubgroup y V ≤ Pc M V := le_inf hVyQ hVyC
  have hVyV : conjSubgroup y V = V := h.weaklyClosed_P.2 y hVyP
  have hyM : y ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact conjSubgroup_eq_self_iff.mp hVyV
  have hPy : conjSubgroup y (Pc M V) = Pc M V := by
    rw [conjSubgroup_eq_self_iff]
    exact h.toHyp.le_normalizer_Pc hyM
  apply hnM
  rw [hH, hPy, sup_idem]
  exact h.toHyp.Pc_le_M

theorem false_of_card_imgK_eq_two (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hcard : Nat.card (imgK V H (Pc M V)) = 2) : False := by
  classical
  obtain ⟨y, hyH, hPy₀, hVy₀⟩ := Hyp.exists_mem_conj_eq_of_conj_Pc_le h.toHyp hPH
    (g := h₀) (by rw [hH]; exact le_sup_right)
  have hH' : H = Pc M V ⊔ conjSubgroup y (Pc M V) := by rw [hH, hPy₀]
  have hEab := isElemAbelian_xOf h hPH hVH
  have huniq := (Nat.card_eq_two_iff' (1 : ↥(imgK V H (Pc M V)))).mp (by simpa using hcard)
  obtain ⟨abar, hbar1, hbar_uniq⟩ := huniq
  obtain ⟨xα, hxαP, hxαpi⟩ := mem_imgK_iff.mp abar.2
  set α : G := (xα : G) with hα
  have hαP : α ∈ Pc M V := hxαP
  have hαH : α ∈ H := hPH hαP
  have hαpi : piK V H xα = (abar : HBar V H) := hxαpi
  have hαK : α ∉ kOf V H := by
    intro hK
    apply hbar1
    apply Subtype.ext
    rw [← hαpi]
    exact (piK_eq_one_iff xα).mpr hK
  have hpow : (abar : ↥(imgK V H (Pc M V))) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := abar)
    rwa [show Nat.card ↥(imgK V H (Pc M V)) = 2 from by simpa using hcard] at h
  have halpha_sq : (piK V H xα) ^ 2 = 1 := by
    rw [hαpi]
    have h := congrArg Subtype.val hpow
    simpa using h
  have hα2K : α ^ 2 ∈ kOf V H := by
    have h1 : (piK V H) (xα ^ 2) = 1 := by rw [map_pow]; exact halpha_sq
    exact (piK_eq_one_iff (xα ^ 2)).mp h1
  have hP_mul := exists_mul_zpowers_of_mem_pc h hPH hα hαP hαH hαpi hbar_uniq
  have hpoint := commutator_mem_V_of_mem_xOf h hαH hEab hα2K hP_mul
  have hcommWα := commutator_xOf_zpowers_le_V h hPH hα hαP hαH hαpi hbar_uniq hpoint
  have hVyW : conjSubgroup y V ≤ Tim79a.xOf V H :=
    Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hyH)
  have hcommPV : ⁅Pc M V, conjSubgroup y V⁆ ≤ V := by
    refine Subgroup.commutator_le.mpr fun p hp x hx => ?_
    obtain ⟨k, hkPK, a, haZ, rfl⟩ := hP_mul p hp
    have hxW : x ∈ Tim79a.xOf V H := hVyW hx
    have haW : a * x * a⁻¹ ∈ Tim79a.xOf V H := by
      have haH : a ∈ H := hPH (Subgroup.zpowers_le.mpr hαP haZ)
      exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H haH) x).mp hxW
    rw [commutatorElement_mul_left_eq_of_centralizes haW hkPK.2.2]
    have hmem : ⁅x, a⁆ ∈ V := hcommWα (Subgroup.commutator_mem_commutator hxW haZ)
    rw [← commutatorElement_inv]
    exact (V).inv_mem hmem
  exact false_of_commutator_conj_V_le h hPH hVH hEab hyH hH' hnM hcommPV

end RootHyp

end CFSG.RankThree.GF2n.Tim81
