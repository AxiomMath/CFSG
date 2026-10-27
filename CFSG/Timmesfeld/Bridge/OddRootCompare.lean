module

public import CFSG.Timmesfeld.Bridge.OddRootNormalizer
import CFSG.Timmesfeld.Bridge.OddLocalRoot
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem inf_le_Wof_left
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) :
    rootGroup D d ⊓ rootGroup D x ≤ Wof D d x :=
  le_inf inf_le_left (rootGroup_inf_le_Qof h hd hx hdx hpx)

private theorem inf_le_Wof_right
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx' : PSL2Pair D x d) :
    rootGroup D d ⊓ rootGroup D x ≤ Wof D x d :=
  le_inf inf_le_right
    (by simpa [inf_comm] using rootGroup_inf_le_Qof h hx hd (fun h' => hdx h'.symm) hpx')

private theorem commutator_mem_Z
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) {u w : G}
    (hu : u ∈ Wof D x d) (hw : w ∈ Wof D d x) :
    u * w * u⁻¹ * w⁻¹ ∈ rootGroup D d ⊓ rootGroup D x := by
  have hQ := Qof_comm h hd hx hdx hpx hpx'
  have huQ : u ∈ Qof D d x := by rw [hQ]; exact hu.2
  have hwQ : w ∈ Qof D x d := hQ ▸ hw.2
  have huNorm : u ∈ Subgroup.normalizer (rootGroup D d) :=
    Subgroup.normalizer_le_normalizer_closure (rootSet D d)
      (Qof_le_normalizer h hd hx hdx hpx huQ)
  have hwNorm : w ∈ Subgroup.normalizer (rootGroup D x) :=
    Subgroup.normalizer_le_normalizer_closure (rootSet D x)
      (Qof_le_normalizer h hx hd (fun h' => hdx h'.symm) hpx' hwQ)
  have h1 : u * w * u⁻¹ ∈ rootGroup D d :=
    (Subgroup.mem_normalizer_iff.mp huNorm w).mp hw.1
  have h2 : w * u * w⁻¹ ∈ rootGroup D x :=
    (Subgroup.mem_normalizer_iff.mp hwNorm u).mp hu.1
  refine Subgroup.mem_inf.mpr ⟨(rootGroup D d).mul_mem h1 ((rootGroup D d).inv_mem hw.1), ?_⟩
  have h3 : (w * u * w⁻¹) * u⁻¹ ∈ rootGroup D x :=
    (rootGroup D x).mul_mem h2 ((rootGroup D x).inv_mem hu.1)
  have h4 : ((w * u * w⁻¹) * u⁻¹)⁻¹ = u * w * u⁻¹ * w⁻¹ := by group
  rw [← h4]
  exact (rootGroup D x).inv_mem h3


private def conjDefect (s u : G) : G := u * s * u⁻¹ * s

private theorem conjDefect_mem_Wof
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) {u s : G}
    (hu : u ∈ Wof D x d) (hs : s ∈ rootSet D d) :
    conjDefect s u ∈ Wof D d x := by
  have hsD : s ∈ D := hs.1
  have hss : s * s = 1 := h.setup.oddT.mul_self_eq_one hsD
  have hQ := Qof_comm h hd hx hdx hpx hpx'
  have huQ : u ∈ Qof D d x := by rw [hQ]; exact hu.2
  have hconj : u * s * u⁻¹ ∈ rootSet D d := by
    have huN := Qof_le_normalizer h hd hx hdx hpx huQ
    exact (Subgroup.mem_set_normalizer_iff.mp huN s).mp hs
  have hQmem : u * s * u⁻¹ * s⁻¹ ∈ Qof D d x := by
    have hsX : s ∈ rootGen D d x := mem_rootGen_of_mem hs
    have h1 : s * u⁻¹ * s⁻¹ ∈ Qof D d x :=
      conj_mem_Qof d x hsX ((Qof D d x).inv_mem huQ)
    have h2 : u * (s * u⁻¹ * s⁻¹) ∈ Qof D d x := (Qof D d x).mul_mem huQ h1
    simpa [mul_assoc] using h2
  have hEq : u * s * u⁻¹ * s = u * s * u⁻¹ * s⁻¹ := by
    rw [h.setup.oddT.inv_eq hsD]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [conjDefect, hEq]
    exact (rootGroup D d).mul_mem (rootSet_subset_rootGroup D d hconj)
      ((rootGroup D d).inv_mem (rootSet_subset_rootGroup D d hs))
  · rw [conjDefect, hEq]
    exact hQmem

private theorem conjDefect_mul {s u v : G} (hss : s * s = 1) :
    conjDefect s (u * v) = u * conjDefect s v * u⁻¹ * conjDefect s u := by
  unfold conjDefect
  rw [mul_inv_rev]
  rw [show u * (v * s * v⁻¹ * s) * u⁻¹ * (u * s * u⁻¹ * s) =
      u * v * s * v⁻¹ * (s * s) * u⁻¹ * s from by group, hss]
  group

private theorem conjDefect_mul_mem_Z
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) {u v s : G}
    (hu : u ∈ Wof D x d) (hv : v ∈ Wof D x d) (hs : s ∈ rootSet D d) :
    conjDefect s (u * v) * (conjDefect s u * conjDefect s v)⁻¹ ∈
      rootGroup D d ⊓ rootGroup D x := by
  have hμu : conjDefect s u ∈ Wof D d x := conjDefect_mem_Wof h hd hx hdx hpx hpx' hu hs
  have hμv : conjDefect s v ∈ Wof D d x := conjDefect_mem_Wof h hd hx hdx hpx hpx' hv hs
  have hz : u * conjDefect s v * u⁻¹ * (conjDefect s v)⁻¹ ∈
      rootGroup D d ⊓ rootGroup D x :=
    commutator_mem_Z h hd hx hdx hpx hpx' hu hμv
  have hcomm : Commute (conjDefect s u) (conjDefect s v) :=
    commute_of_mem_rootGroup hd hμu.1 hμv.1
  have hsplit : u * conjDefect s v * u⁻¹ * conjDefect s u =
      (u * conjDefect s v * u⁻¹ * (conjDefect s v)⁻¹) *
        (conjDefect s v * conjDefect s u) := by group
  have hcollapse : (u * conjDefect s v * u⁻¹ * (conjDefect s v)⁻¹) *
      (conjDefect s u * conjDefect s v) *
      (conjDefect s u * conjDefect s v)⁻¹ =
      u * conjDefect s v * u⁻¹ * (conjDefect s v)⁻¹ := by group
  have hss : s * s = 1 := h.setup.oddT.mul_self_eq_one hs.1
  rw [conjDefect_mul hss, hsplit, ← hcomm.eq, hcollapse]
  exact hz

private theorem conjDefect_eq_one_of_mem_Z
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) {u s : G} (hs : s ∈ rootSet D d)
    (hZ : conjDefect s u ∈ rootGroup D d ⊓ rootGroup D x) :
    conjDefect s u = 1 := by
  by_contra hne
  have hsD : s ∈ D := hs.1
  have hss : s * s = 1 := h.setup.oddT.mul_self_eq_one hsD
  have hsE : s ∈ rootGroup D d := rootSet_subset_rootGroup D d hs
  have hzE : conjDefect s u ∈ rootGroup D d := hZ.1
  have hsz : Commute s (conjDefect s u) := commute_of_mem_rootGroup hd hsE hzE
  have hus : u * s * u⁻¹ = conjDefect s u * s := by
    unfold conjDefect
    rw [mul_assoc (u * s * u⁻¹) s s, hss, mul_one]
  have hzsD : conjDefect s u * s ∈ D := by
    rw [← hus]
    exact h.setup.normal u s hsD
  have hcomm : Commute s (conjDefect s u * s) :=
    hsz.mul_right (Commute.refl s)
  have hne' : s ≠ conjDefect s u * s := by
    intro hEq
    apply hne
    have h2 : conjDefect s u * s = 1 * s := by rw [one_mul]; exact hEq.symm
    exact mul_right_cancel h2
  have hxs : ¬ Commute x s := by
    intro hc
    exact hdx ((hs.2 x hx).mp hc.symm)
  have hxz : Commute x (conjDefect s u) :=
    (Subgroup.mem_centralizer_iff.mp (rootGroup_inf_le_centralizer h hd hx hdx hpx hZ))
      x (mem_rootGen_left d x)
  have hprod : s * (conjDefect s u * s) = conjDefect s u := by
    calc s * (conjDefect s u * s) = (s * conjDefect s u) * s := by group
      _ = (conjDefect s u * s) * s := by rw [hsz.eq]
      _ = conjDefect s u * (s * s) := by group
      _ = conjDefect s u := by rw [hss, mul_one]
  have hkey := Asc72.IsOddTransp.commute_mul_iff h.setup.oddT hsD hzsD hx hne' hcomm
  have hxprod : Commute x (s * (conjDefect s u * s)) := by
    rw [hprod]
    exact hxz
  exact hxs (hkey.mp hxprod).1


private theorem map_conjSubgroup_sylow {C : Subgroup G} (SC : Sylow 2 ↥C) {g : G} (hg : g ∈ C) :
    Subgroup.map C.subtype
      (Sylow.mapSurjective (f := (MulAut.conj (⟨g, hg⟩ : ↥C)).toMonoidHom)
        (MulAut.conj (⟨g, hg⟩ : ↥C)).surjective SC : Subgroup ↥C)
      = conjSubgroup g (Subgroup.map C.subtype (SC : Subgroup ↥C)) := by
  let gC : ↥C := ⟨g, hg⟩
  have hcoe : (Sylow.mapSurjective (f := (MulAut.conj gC).toMonoidHom)
      (MulAut.conj gC).surjective SC : Subgroup ↥C) =
      Subgroup.map (MulAut.conj gC).toMonoidHom (SC : Subgroup ↥C) :=
    Sylow.coe_mapSurjective (f := (MulAut.conj gC).toMonoidHom)
      (MulAut.conj gC).surjective SC
  rw [hcoe, Subgroup.map_map]
  have hcomp : C.subtype.comp (MulAut.conj gC).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp C.subtype := by
    ext z
    rfl
  rw [hcomp, ← Subgroup.map_map]
  rfl

private theorem conj_sylow_le_rootGroup {x : G} {S : Subgroup G} {n₀ : G}
    (hn₀S : ∀ s ∈ S, s ≠ 1 → n₀ * s * n₀⁻¹ ∈ rootSet D x) :
    conjSubgroup n₀ S ≤ rootGroup D x := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  by_cases ht1 : t = 1
  · subst ht1
    simp
  · simpa [MulAut.conj_apply] using rootSet_subset_rootGroup D x (hn₀S t ht ht1)

private theorem not_mem_rootGroup_right_of_mem_rootSet
    (h : Hyp G D) {d x s : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) (hs : s ∈ rootSet D d) :
    s ∉ rootGroup D x := by
  intro hsE
  have hsZ : s ∈ rootGroup D d ⊓ rootGroup D x :=
    ⟨rootSet_subset_rootGroup D d hs, hsE⟩
  exact not_mem_Qof_of_mem_rootSet h.setup.oddT hx hdx hs
    (rootGroup_inf_le_Qof h hd hx hdx hpx hsZ)

private theorem not_conj_sylow_eq
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) {C S : Subgroup G} (hC : GoodCompl D d x C S)
    {n₀ : G} (hn₀C : n₀ ∈ C)
    (hn₀S : ∀ s ∈ S, s ≠ 1 → n₀ * s * n₀⁻¹ ∈ rootSet D x)
    {s : G} (hsS : s ∈ S) (hs1 : s ≠ 1) :
    conjSubgroup s (conjSubgroup n₀ S) ≠ conjSubgroup n₀ S := by
  obtain ⟨n, hn, ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hC.le hC.inf hC.sup
  obtain ⟨SC, hmapSC⟩ := hC.exists_sylow_map_eq h
  let nC : ↥C := ⟨n₀, hn₀C⟩
  let SC' : Sylow 2 ↥C := Sylow.mapSurjective (f := (MulAut.conj nC).toMonoidHom)
    (MulAut.conj nC).surjective SC
  have hmapSC' : Subgroup.map C.subtype (SC' : Subgroup ↥C) = conjSubgroup n₀ S := by
    show Subgroup.map C.subtype
      (Sylow.mapSurjective (f := (MulAut.conj nC).toMonoidHom)
        (MulAut.conj nC).surjective SC : Subgroup ↥C) = _
    rw [map_conjSubgroup_sylow SC hn₀C]
    simp only [hmapSC]
  have hsC : s ∈ C := hC.S_le hsS
  let sC : ↥C := ⟨s, hsC⟩
  let SCs : Sylow 2 ↥C := Sylow.mapSurjective (f := (MulAut.conj sC).toMonoidHom)
    (MulAut.conj sC).surjective SC'
  have hmapSCs : Subgroup.map C.subtype (SCs : Subgroup ↥C) =
      conjSubgroup s (conjSubgroup n₀ S) := by
    show Subgroup.map C.subtype
      (Sylow.mapSurjective (f := (MulAut.conj sC).toMonoidHom)
        (MulAut.conj sC).surjective SC' : Subgroup ↥C) = _
    rw [map_conjSubgroup_sylow SC' hsC, hmapSC']
  have hS'root : conjSubgroup n₀ S ≤ rootGroup D x := conj_sylow_le_rootGroup hn₀S
  have hsE : s ∈ rootSet D d := hC.S_root s hsS hs1
  have hneSS : conjSubgroup n₀ S ≠ S := by
    intro hEq
    have hsS' : s ∈ conjSubgroup n₀ S := by rw [hEq]; exact hsS
    exact not_mem_rootGroup_right_of_mem_rootSet h hd hx hdx hpx hsE (hS'root hsS')
  have hneSC : SC' ≠ SC := by
    intro hEq
    apply hneSS
    have h := congrArg (fun P : Sylow 2 ↥C =>
      Subgroup.map C.subtype (P : Subgroup ↥C)) hEq
    rw [hmapSC', hmapSC] at h
    exact h
  intro hEqG
  have hEqSC : SCs = SC' := by
    apply Sylow.ext
    apply Subgroup.map_injective C.subtype_injective
    rw [hmapSCs, hmapSC', hEqG]
  have hnorm : sC ∈ Subgroup.normalizer (SC' : Subgroup ↥C) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulAut.conj sC).toMonoidHom (SC' : Subgroup ↥C) =
      (SC' : Subgroup ↥C)
    have hcoe : Subgroup.map (MulAut.conj sC).toMonoidHom (SC' : Subgroup ↥C) =
        (SCs : Subgroup ↥C) :=
      (Sylow.coe_mapSurjective (f := (MulAut.conj sC).toMonoidHom)
        (MulAut.conj sC).surjective SC').symm
    rw [hcoe]
    exact congrArg (fun P : Sylow 2 ↥C => (P : Subgroup ↥C)) hEqSC
  have hsSC : sC ∈ (SC : Subgroup ↥C) := by
    apply (Subgroup.mem_map_iff_mem C.subtype_injective).mp
    rw [hmapSC]
    exact hsS
  have hbot : sC ∈ Subgroup.normalizer (SC' : Subgroup ↥C) ⊓ (SC : Subgroup ↥C) :=
    ⟨hnorm, hsSC⟩
  rw [psl2_normalizer_inf_eq_bot eC hn (S := SC') (S' := SC) hneSC] at hbot
  have hsC1 : sC = 1 := Subgroup.mem_bot.mp hbot
  exact hs1 (by simpa [sC] using congrArg Subtype.val hsC1)

private theorem compl_sylow_sup
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) {C S : Subgroup G} (hC : GoodCompl D d x C S)
    {n₀ : G} (hn₀C : n₀ ∈ C)
    (hn₀S : ∀ s ∈ S, s ≠ 1 → n₀ * s * n₀⁻¹ ∈ rootSet D x)
    {s : G} (hsS : s ∈ S) (hs1 : s ≠ 1) :
    conjSubgroup n₀ S ⊔ conjSubgroup s (conjSubgroup n₀ S) = C := by
  obtain ⟨n, hn, ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hC.le hC.inf hC.sup
  obtain ⟨SC, hmapSC⟩ := hC.exists_sylow_map_eq h
  let nC : ↥C := ⟨n₀, hn₀C⟩
  let SC' : Sylow 2 ↥C := Sylow.mapSurjective (f := (MulAut.conj nC).toMonoidHom)
    (MulAut.conj nC).surjective SC
  have hmapSC' : Subgroup.map C.subtype (SC' : Subgroup ↥C) = conjSubgroup n₀ S := by
    show Subgroup.map C.subtype
      (Sylow.mapSurjective (f := (MulAut.conj nC).toMonoidHom)
        (MulAut.conj nC).surjective SC : Subgroup ↥C) = _
    rw [map_conjSubgroup_sylow SC hn₀C]
    simp only [hmapSC]
  have hsC : s ∈ C := hC.S_le hsS
  let sC : ↥C := ⟨s, hsC⟩
  let SCs : Sylow 2 ↥C := Sylow.mapSurjective (f := (MulAut.conj sC).toMonoidHom)
    (MulAut.conj sC).surjective SC'
  have hmapSCs : Subgroup.map C.subtype (SCs : Subgroup ↥C) =
      conjSubgroup s (conjSubgroup n₀ S) := by
    show Subgroup.map C.subtype
      (Sylow.mapSurjective (f := (MulAut.conj sC).toMonoidHom)
        (MulAut.conj sC).surjective SC' : Subgroup ↥C) = _
    rw [map_conjSubgroup_sylow SC' hsC, hmapSC']
  have hneSCs : SC' ≠ SCs := by
    intro hEq
    apply not_conj_sylow_eq h hd hx hdx hpx hC hn₀C hn₀S hsS hs1
    have h := congrArg (fun P : Sylow 2 ↥C =>
      Subgroup.map C.subtype (P : Subgroup ↥C)) hEq
    rw [hmapSC', hmapSCs] at h
    exact h.symm
  have hsup := psl2_sup_sylow_eq_top eC hn hneSCs
  have hmap := congrArg (Subgroup.map C.subtype) hsup
  rw [Subgroup.map_sup, hmapSC', hmapSCs, Subgroup.map_top, Subgroup.range_subtype] at hmap
  exact hmap


private theorem conjDefect_eq_one_imp_mem_Z
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) {C S : Subgroup G}
    (hC : GoodCompl D d x C S) {n₀ : G} (hn₀C : n₀ ∈ C)
    (hn₀S : ∀ s ∈ S, s ≠ 1 → n₀ * s * n₀⁻¹ ∈ rootSet D x)
    (hn₀W : conjSubgroup n₀ (Wof D d x) = Wof D x d) {s u : G} (hsS : s ∈ S) (hs1 : s ≠ 1)
    (hu : u ∈ Wof D x d) (hmu : conjDefect s u = 1) :
    u ∈ rootGroup D d ⊓ rootGroup D x := by
  have hsE : s ∈ rootSet D d := hC.S_root s hsS hs1
  have hss : s * s = 1 := h.setup.oddT.mul_self_eq_one hsE.1
  have hu1 : u * s * u⁻¹ = s := by
    have h1 : (u * s * u⁻¹) * s = s * s := by
      have hm := hmu
      unfold conjDefect at hm
      rw [hm, hss]
    exact mul_right_cancel h1
  have hus : Commute u s := by
    show u * s = s * u
    calc u * s = (u * s * u⁻¹) * u := by group
      _ = s * u := by rw [hu1]
  have hS'root : conjSubgroup n₀ S ≤ rootGroup D x := conj_sylow_le_rootGroup hn₀S
  have hS'cent : conjSubgroup n₀ S ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem_rootGroup hx (hS'root hy) hu.1).eq
  have hSscent : conjSubgroup s (conjSubgroup n₀ S) ≤
      Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    have htcent : Commute u t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hS'cent ht)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [MulAut.conj_apply] using
        ((hus.mul_right htcent).mul_right hus.inv_right).symm.eq)
  have hgen := compl_sylow_sup h hd hx hdx hpx hC hn₀C hn₀S hsS hs1
  have hCcent : C ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [← hgen]
    exact sup_le hS'cent hSscent
  have hn₀cent : Commute n₀ u :=
    Subgroup.mem_centralizer_singleton_iff.mp (hCcent hn₀C)
  have huWx : u ∈ conjSubgroup n₀ (Wof D d x) := by rw [hn₀W]; exact hu
  have huWd : u ∈ Wof D d x := by
    have h1 : n₀⁻¹ * u * n₀ ∈ Wof D d x := mem_conjSubgroup.mp huWx
    have hEq : n₀⁻¹ * u * n₀ = u := by
      calc n₀⁻¹ * u * n₀ = n₀⁻¹ * (u * n₀) := by group
        _ = n₀⁻¹ * (n₀ * u) := by rw [← hn₀cent.eq]
        _ = u := by group
    rwa [hEq] at h1
  exact ⟨huWd.1, hu.1⟩


private theorem isMulCommutative_Wof {d x : G} (hd : d ∈ D) :
    IsMulCommutative ↥(Wof D d x) :=
  IsMulCommutative.of_comm (fun a b =>
    Subtype.ext (commute_of_mem_rootGroup hd a.2.1 b.2.1).eq)

private def conjDefectHom
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) [IsMulCommutative ↥(Wof D d x)]
    {s : G} (hs : s ∈ rootSet D d) :
    ↥(Wof D x d) →* (↥(Wof D d x) ⧸
      (rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D d x)) where
  toFun u := QuotientGroup.mk' _ ⟨conjDefect s (u : G),
    conjDefect_mem_Wof h hd hx hdx hpx hpx' u.2 hs⟩
  map_one' := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hss : s * s = 1 := h.setup.oddT.mul_self_eq_one hs.1
    change conjDefect s ((1 : ↥(Wof D x d)) : G) ∈ rootGroup D d ⊓ rootGroup D x
    have h1 : conjDefect s ((1 : ↥(Wof D x d)) : G) = 1 := by
      simpa [conjDefect] using hss
    rw [h1]
    exact (rootGroup D d ⊓ rootGroup D x).one_mem
  map_mul' u v := by
    rw [← map_mul]
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv] using
      conjDefect_mul_mem_Z h hd hx hdx hpx hpx' u.2 v.2 hs

private theorem conjDefectHom_apply
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) [IsMulCommutative ↥(Wof D d x)]
    {s : G} (hs : s ∈ rootSet D d) (u : ↥(Wof D x d)) :
    conjDefectHom h hd hx hdx hpx hpx' hs u =
      QuotientGroup.mk' _ ⟨conjDefect s (u : G),
        conjDefect_mem_Wof h hd hx hdx hpx hpx' u.2 hs⟩ := rfl

private theorem conjDefectHom_ker
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) [IsMulCommutative ↥(Wof D d x)]
    {C S : Subgroup G}
    (hC : GoodCompl D d x C S) {n₀ : G} (hn₀C : n₀ ∈ C)
    (hn₀S : ∀ s ∈ S, s ≠ 1 → n₀ * s * n₀⁻¹ ∈ rootSet D x)
    (hn₀W : conjSubgroup n₀ (Wof D d x) = Wof D x d)
    {s : G} (hsS : s ∈ S) (hs1 : s ≠ 1) :
    (conjDefectHom h hd hx hdx hpx hpx' (hC.S_root s hsS hs1)).ker =
      (rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D x d) := by
  ext u
  rw [MonoidHom.mem_ker, conjDefectHom_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hu
    have hmu : conjDefect s (u : G) = 1 :=
      conjDefect_eq_one_of_mem_Z h hd hx hdx hpx (hC.S_root s hsS hs1) hu
    exact conjDefect_eq_one_imp_mem_Z h hd hx hdx hpx hC hn₀C hn₀S hn₀W hsS hs1 u.2 hmu
  · intro hu
    have hcent := rootGroup_inf_le_centralizer h hd hx hdx hpx hu
    have hus : Commute s (u : G) :=
      (Subgroup.mem_centralizer_iff.mp hcent) s (mem_rootGen_of_mem (hC.S_root s hsS hs1))
    have hss : s * s = 1 := h.setup.oddT.mul_self_eq_one (hC.S_root s hsS hs1).1
    have h1 : (u : G) * s * (u : G)⁻¹ * s = 1 := by
      rw [show (u : G) * s = s * (u : G) from hus.eq.symm]
      simp [hss]
    show (u : G) * s * (u : G)⁻¹ * s ∈ rootGroup D d ⊓ rootGroup D x
    rw [h1]
    exact (rootGroup D d ⊓ rootGroup D x).one_mem


private theorem card_quotient_Z_eq
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d)
    {n₀ : G} (hn₀W : conjSubgroup n₀ (Wof D d x) = Wof D x d)
    [IsMulCommutative ↥(Wof D d x)] [IsMulCommutative ↥(Wof D x d)] :
    Nat.card (↥(Wof D x d) ⧸
      (rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D x d)) =
    Nat.card (↥(Wof D d x) ⧸
      (rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D d x)) := by
  have hcardW : Nat.card ↥(Wof D x d) = Nat.card ↥(Wof D d x) := by
    rw [← hn₀W]
    simpa [conjSubgroup] using
      Subgroup.card_map_of_injective (K := Wof D d x)
        (f := (MulAut.conj n₀).toMonoidHom) (MulAut.conj n₀).injective
  have hcardZx : Nat.card ↥((rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D x d)) =
      Nat.card ↥(rootGroup D d ⊓ rootGroup D x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_Wof_right h hd hx hdx hpx')).toEquiv
  have hcardZd : Nat.card ↥((rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D d x)) =
      Nat.card ↥(rootGroup D d ⊓ rootGroup D x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_Wof_left h hd hx hdx hpx)).toEquiv
  have h1 : Nat.card ↥(Wof D d x) =
      Nat.card (↥(Wof D x d) ⧸
        (rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D x d)) *
      Nat.card ↥(rootGroup D d ⊓ rootGroup D x) := by
    rw [← hcardW, ← hcardZx]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ↥(Wof D d x) =
      Nat.card (↥(Wof D d x) ⧸
        (rootGroup D d ⊓ rootGroup D x).subgroupOf (Wof D d x)) *
      Nat.card ↥(rootGroup D d ⊓ rootGroup D x) := by
    rw [← hcardZd]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  haveI : Nonempty ↥(rootGroup D d ⊓ rootGroup D x) :=
    ⟨1, (rootGroup D d ⊓ rootGroup D x).one_mem⟩
  exact Nat.mul_right_cancel Nat.card_pos (h1.symm.trans h2)


private theorem exists_conjDefect_mul_mem_Z
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d)
    {C S : Subgroup G} (hC : GoodCompl D d x C S) {n₀ : G} (hn₀C : n₀ ∈ C)
    (hn₀S : ∀ s ∈ S, s ≠ 1 → n₀ * s * n₀⁻¹ ∈ rootSet D x)
    (hn₀W : conjSubgroup n₀ (Wof D d x) = Wof D x d)
    {s : G} (hsS : s ∈ S) (hs1 : s ≠ 1) {w : G} (hw : w ∈ Wof D d x) :
    ∃ u ∈ Wof D x d, ∃ z ∈ rootGroup D d ⊓ rootGroup D x,
      w = conjDefect s u * z := by
  haveI hWd : IsMulCommutative ↥(Wof D d x) := isMulCommutative_Wof hd
  haveI hWx : IsMulCommutative ↥(Wof D x d) :=
    isMulCommutative_Wof (d := x) (x := d) hx
  let Z := rootGroup D d ⊓ rootGroup D x
  let Zx : Subgroup ↥(Wof D x d) := Z.subgroupOf (Wof D x d)
  let Zd : Subgroup ↥(Wof D d x) := Z.subgroupOf (Wof D d x)
  let φ : ↥(Wof D x d) →* (↥(Wof D d x) ⧸ Zd) :=
    conjDefectHom h hd hx hdx hpx hpx' (hC.S_root s hsS hs1)
  have hker : φ.ker = Zx :=
    conjDefectHom_ker h hd hx hdx hpx hpx' hC hn₀C hn₀S hn₀W hsS hs1
  let F : (↥(Wof D x d) ⧸ Zx) →* (↥(Wof D d x) ⧸ Zd) :=
    QuotientGroup.lift Zx φ (by rw [hker])
  have hinj : Function.Injective F := by
    exact (QuotientGroup.injective_lift_iff Zx φ (by rw [hker])).mpr hker.symm
  have hcard := card_quotient_Z_eq h hd hx hdx hpx hpx' hn₀W
  have hsurj : Function.Surjective F := by
    haveI : Fintype (↥(Wof D x d) ⧸ Zx) := Fintype.ofFinite _
    haveI : Fintype (↥(Wof D d x) ⧸ Zd) := Fintype.ofFinite _
    have hcard' : Fintype.card (↥(Wof D x d) ⧸ Zx) =
        Fintype.card (↥(Wof D d x) ⧸ Zd) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hcard
    exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard')).mp hinj
  obtain ⟨q, hq⟩ := hsurj ((QuotientGroup.mk' Zd) ⟨w, hw⟩)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective Zx q
  have hq' : φ u = QuotientGroup.mk' Zd ⟨w, hw⟩ := by
    simpa [F] using hq
  have hq'' : QuotientGroup.mk' Zd ⟨conjDefect s (u : G),
      conjDefect_mem_Wof h hd hx hdx hpx hpx' u.2 (hC.S_root s hsS hs1)⟩ =
      QuotientGroup.mk' Zd ⟨w, hw⟩ := hq'
  have hmem : (⟨conjDefect s (u : G),
      conjDefect_mem_Wof h hd hx hdx hpx hpx' u.2 (hC.S_root s hsS hs1)⟩ /
      (⟨w, hw⟩ : ↥(Wof D d x))) ∈ Zd :=
    QuotientGroup.eq_iff_div_mem.mp hq''
  have hz : conjDefect s (u : G) * w⁻¹ ∈ Z := by
    have hh := hmem
    rw [Subgroup.mem_subgroupOf] at hh
    simpa [div_eq_mul_inv] using hh
  have hz2 : (conjDefect s (u : G) * w⁻¹) * (conjDefect s (u : G) * w⁻¹) = 1 :=
    mul_self_eq_one_of_mem_closure (pairwise_commute_rootSet hd)
      (fun e he => h.setup.oddT.mul_self_eq_one he.1) hz.1
  have hmW : conjDefect s (u : G) ∈ Wof D d x :=
    conjDefect_mem_Wof h hd hx hdx hpx hpx' u.2 (hC.S_root s hsS hs1)
  have hmX : conjDefect s (u : G) ∈ rootGen D d x :=
    rootGroup_le_rootGen d x hmW.1
  have hcent := rootGroup_inf_le_centralizer h hd hx hdx hpx hz
  have hmz : (conjDefect s (u : G)) * (conjDefect s (u : G) * w⁻¹) =
      (conjDefect s (u : G) * w⁻¹) * conjDefect s (u : G) :=
    (Subgroup.mem_centralizer_iff.mp hcent) (conjDefect s (u : G)) hmX
  have hzw : (conjDefect s (u : G) * w⁻¹) * w = conjDefect s (u : G) := by group
  have hz_inv : (conjDefect s (u : G) * w⁻¹)⁻¹ = conjDefect s (u : G) * w⁻¹ :=
    inv_eq_of_mul_eq_one_right hz2
  refine ⟨u, u.2, conjDefect s (u : G) * w⁻¹, hz, ?_⟩
  calc w = (conjDefect s (u : G) * w⁻¹)⁻¹ *
        ((conjDefect s (u : G) * w⁻¹) * w) := by group
    _ = (conjDefect s (u : G) * w⁻¹) * conjDefect s (u : G) := by rw [hz_inv, hzw]
    _ = conjDefect s (u : G) * (conjDefect s (u : G) * w⁻¹) := hmz.symm


theorem exists_rootSet_mul
    {G : Type} [Group G] [Finite G] {D : Set G} (h : Hyp G D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d)
    {g : G} (hg : g ∈ rootGroup D d) (hgW : g ∉ Wof D d x) :
    ∃ e ∈ rootSet D d, ∃ z ∈ rootGroup D d ⊓ rootGroup D x, g = e * z := by
  obtain ⟨C, S, hC⟩ := exists_goodCompl h hd hx hdx hpx
  obtain ⟨n₀, hn₀C, hn₀S, -, hn₀Wraw⟩ := exists_conj_rootGroup h hx hpx hC
  have hQ := Qof_comm h hd hx hdx hpx hpx'
  have hn₀W : conjSubgroup n₀ (Wof D d x) = Wof D x d := by
    have hWx : Wof D x d = rootGroup D x ⊓ Qof D d x := by
      rw [Wof, ← hQ]
    rw [hWx]
    exact hn₀Wraw
  have hsup : rootGroup D d = S ⊔ Wof D d x := rootGroup_eq_sup h hd hx hdx hpx hC
  have hg_sup : g ∈ S ⊔ Wof D d x := hsup ▸ hg
  have hS_le : S ≤ rootGroup D d := by rw [hsup]; exact le_sup_left
  have hS_cent : S ≤ Subgroup.centralizer (Wof D d x : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (commute_of_mem_rootGroup hd (hS_le hs) (Wof_le_rootGroup d x hw)).symm.eq
  have hS_norm : S ≤ Subgroup.normalizer (Wof D d x : Set G) :=
    hS_cent.trans (Subgroup.centralizer_le_normalizer (Wof D d x : Set G))
  have hprod : (↑(S ⊔ Wof D d x) : Set G) = (S : Set G) * (Wof D d x : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S (Wof D d x) hS_norm
  have hg_mul : g ∈ (S : Set G) * (Wof D d x : Set G) := by
    rw [← hprod]
    exact hg_sup
  obtain ⟨s, hsS, w, hwW, hsw⟩ := Set.mem_mul.mp hg_mul
  have hs1 : s ≠ 1 := by
    intro h1
    apply hgW
    rw [← hsw, h1, one_mul]
    exact hwW
  have hsE : s ∈ rootSet D d := hC.S_root s hsS hs1
  obtain ⟨u, hu, z, hz, hwz⟩ :=
    exists_conjDefect_mul_mem_Z h hd hx hdx hpx hpx' hC hn₀C hn₀S hn₀W hsS hs1 hwW
  have huQ : u ∈ Qof D d x := by rw [hQ]; exact hu.2
  have heE : u * s * u⁻¹ ∈ rootSet D d :=
    (Subgroup.mem_set_normalizer_iff.mp (Qof_le_normalizer h hd hx hdx hpx huQ) s).mp hsE
  have hcommse : Commute s (u * s * u⁻¹) := commute_of_mem_rootSet hd hsE heE
  have hss : s * s = 1 := h.setup.oddT.mul_self_eq_one hsE.1
  have hcalc : s * (conjDefect s u * z) = (u * s * u⁻¹) * z := by
    unfold conjDefect
    calc s * ((u * s * u⁻¹) * s * z)
        = (s * (u * s * u⁻¹)) * (s * z) := by group
      _ = ((u * s * u⁻¹) * s) * (s * z) := by rw [hcommse.eq]
      _ = (u * s * u⁻¹) * (s * s) * z := by group
      _ = (u * s * u⁻¹) * z := by rw [hss, mul_one]
  refine ⟨u * s * u⁻¹, heE, z, hz, ?_⟩
  calc g = s * w := hsw.symm
    _ = s * (conjDefect s u * z) := by rw [hwz]
    _ = (u * s * u⁻¹) * z := hcalc

end CFSG.Timmesfeld.Bridge.OddRoot
