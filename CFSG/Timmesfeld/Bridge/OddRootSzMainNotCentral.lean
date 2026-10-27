module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainBlock
import CFSG.Timmesfeld.Bridge.OddLocalMain
import CFSG.GF2Type.Widths1112.Core
import CFSG.Timmesfeld.Bridge.Asc72RootSet
import CFSG.Timmesfeld.Bridge.RootClosureThree
import CFSG.Timmesfeld.Bridge.RootSetsConn16

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

theorem SzCfg.exists_not_commute_both (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    ∃ x ∈ D, ¬ Commute x d ∧ ¬ Commute x a := by
  classical
  by_contra h
  push Not at h
  have hcommH : ∀ k ∈ Subgroup.closure E, Commute k d := by
    intro k hk
    have hle : Subgroup.closure E ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.closure_le]
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr (c.subset_commSet hz).2.1
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
  have hD_pairs : ∀ y ∈ E, ∀ x ∈ D, Commute x d ∨ Commute x y := by
    intro y hy x hx
    obtain ⟨k, hk, hky⟩ := c.exists_conj ha hy
    have hkd : k * d * k⁻¹ = d := by
      rw [(hcommH k hk).eq, mul_inv_cancel_right]
    have hmem : k⁻¹ * x * k ∈ D := by simpa using c.hyp.setup.conj_mem k⁻¹ hx
    by_cases h1 : Commute (k⁻¹ * x * k) d
    · left
      have h2 := (Commute.conj_iff k).mpr h1
      rw [show k * (k⁻¹ * x * k) * k⁻¹ = x by group, hkd] at h2
      exact h2
    · right
      have h2 := (Commute.conj_iff k).mpr (h (k⁻¹ * x * k) hmem h1)
      rw [show k * (k⁻¹ * x * k) * k⁻¹ = x by group, hky] at h2
      exact h2
  have hAd : ∀ x ∈ D, ¬ Commute x d → ∀ y ∈ E, Commute x y := fun x hx hxd y hy =>
    (hD_pairs y hy x hx).resolve_left hxd
  have hDsub : ∀ x ∈ D, x ∈ E ∨ ∀ y ∈ E, Commute x y := by
    intro x hx
    by_cases hxd : Commute x d
    · rcases (c.commute_d_iff hx).mp hxd with hxr | hxE
      · right
        intro y hy
        exact c.commute_of_mem_rootSet_d hxr (Subgroup.subset_closure hy)
      · exact Or.inl hxE
    · exact Or.inr (hAd x hx hxd)
  have hnormD : D ⊆ Subgroup.normalizer E := by
    intro x hx
    rcases hDsub x hx with hxE | hxc
    · have hxH : x ∈ Subgroup.closure E := Subgroup.subset_closure hxE
      have hxinv : x⁻¹ ∈ Subgroup.closure E := Subgroup.inv_mem _ hxH
      change x ∈ Subgroup.normalizer E
      rw [Subgroup.mem_set_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact c.conj_mem hxH hy
      · intro hy
        have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ E := by
          simpa using c.conj_mem hxinv hy
        rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at hy'
    · exact Subgroup.centralizer_le_normalizer (E : Set G)
        (Subgroup.mem_centralizer_iff.mpr fun y hy => (hxc y hy).symm)
  have htop : Subgroup.normalizer E = ⊤ := by
    rw [eq_top_iff, ← c.hyp.setup.gen, Subgroup.closure_le]
    exact hnormD
  have hDE : D ⊆ E := by
    intro x hx
    have heD : e ∈ D := (c.subset_commSet c.e_mem).1
    obtain ⟨g, hg⟩ := isConj_iff.mp (c.hyp.setup.isConj heD hx)
    have hgN : g ∈ Subgroup.normalizer E := htop ▸ Subgroup.mem_top g
    have hmem : g * e * g⁻¹ ∈ E := (Subgroup.mem_set_normalizer_iff.mp hgN e).mp c.e_mem
    rw [← hg]
    exact hmem
  exact c.d_not_mem (hDE c.d_mem)

private theorem szQ_eq_bot_of_forall_commute (c : SzCfg G D d E e n)
    (hcent : ∀ q ∈ szQ E, ∀ x ∈ E, Commute q x) : szQ E = ⊥ := by
  let H : Subgroup G := Subgroup.closure E
  let Q : Subgroup H := CFSG.pCore 2 H
  have hQZ : Q ≤ Subgroup.center H := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro h
    have hcommE : ∀ x ∈ E, Commute (q : G) x := fun x hx =>
      hcent (q : G) (mem_szQ_iff.mpr ⟨q.2, hq⟩) x hx
    have hle : H ≤ Subgroup.centralizer ({(q : G)} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommE x hx).eq.symm
    have hh : Commute (q : G) (h : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hle h.2)).symm
    exact Subtype.ext hh.eq.symm
  have hNPC : Q ≤ ⁅Q, (⊤ : Subgroup H)⁆ :=
    OddTransp.pCore_le_commutator_of_isBenderGroup (G := H) (D := szE E) c.setup c.perfect
      c.isBenderGroup_zStar
  have hbot : ⁅Q, (⊤ : Subgroup H)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hQZ
  have hQbot : Q = ⊥ := eq_bot_iff.mpr (hbot ▸ hNPC)
  rw [szQ, CFSG.Open.pCoreOf]
  change Subgroup.map H.subtype Q = ⊥
  rw [hQbot, Subgroup.map_bot]

private theorem center_eq_bot_of_szQ_eq_bot (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) :
    Subgroup.center ↥(Subgroup.closure E) = ⊥ := by
  let H : Subgroup G := Subgroup.closure E
  have hp : CFSG.pCore 2 H = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hqG : (q : G) ∈ szQ E := mem_szQ_iff.mpr ⟨q.2, hq⟩
    rw [hQ, Subgroup.mem_bot] at hqG
    exact Subtype.ext hqG
  rw [eq_bot_iff]
  intro z hz
  have hzZ : z ∈ zStar H := by
    rw [zStar, Subgroup.mem_comap]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (CFSG.pCore 2 H))
      ⟨z, hz, rfl⟩
  rw [c.zStar_eq, hp, Subgroup.mem_bot] at hzZ
  exact hzZ

private theorem szMk_eq_iff_of_szQ_eq_bot (hQ : szQ E = ⊥)
    {x y : G} (hx : x ∈ Subgroup.closure E) (hy : y ∈ Subgroup.closure E) :
    szMk E ⟨x, hx⟩ = szMk E ⟨y, hy⟩ ↔ x = y := by
  let H : Subgroup G := Subgroup.closure E
  constructor
  · intro h
    have h1 : szMk E (⟨x, hx⟩ * ⟨y, hy⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have hmem : (⟨x, hx⟩ * ⟨y, hy⟩⁻¹ : H) ∈ CFSG.pCore 2 H :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 H) _).mp h1
    have hxy : x * y⁻¹ ∈ szQ E :=
      mem_szQ_iff.mpr ⟨H.mul_mem hx (H.inv_mem hy), hmem⟩
    rw [hQ, Subgroup.mem_bot] at hxy
    exact mul_inv_eq_one.mp hxy
  · rintro rfl
    exact congrArg (szMk E) (Subtype.ext rfl)

private theorem szMk_injective_of_szQ_eq_bot (hQ : szQ E = ⊥) :
    Function.Injective (szMk E) := by
  intro x y h
  apply Subtype.ext
  exact (szMk_eq_iff_of_szQ_eq_bot hQ x.2 y.2).mp h

private theorem szComp_mul_mem_of_szQ_eq_bot (c : SzCfg G D d E e n) (hQ : szQ E = ⊥)
    {a u v : G} (ha : a ∈ E) (hu : u ∈ szComp E a) (hv : v ∈ szComp E a) (huv : u ≠ v) :
    u * v ∈ szComp E a := by
  let H : Subgroup G := Subgroup.closure E
  have huE : u ∈ E := hu.1
  have hvE : v ∈ E := hv.1
  obtain ⟨P, haP⟩ := c.exists_szS ha
  have huP : u ∈ szS E P := (c.mem_szS_iff_commute P ha huE haP).mpr hu.2
  have hvP : v ∈ szS E P := (c.mem_szS_iff_commute P ha hvE haP).mpr hv.2
  have huv_comm : Commute u v :=
    c.hyp.setup.oddT.commute_of_isPGroup (isPGroup_szS E P) (c.subset_commSet huE).1
      (c.subset_commSet hvE).1 huP hvP
  let uH : H := ⟨u, Subgroup.subset_closure huE⟩
  let vH : H := ⟨v, Subgroup.subset_closure hvE⟩
  have hu2 : szMk E uH * szMk E uH = 1 := by
    have huu : uH * uH = 1 := by
      apply Subtype.ext
      show u * u = 1
      exact c.hyp.setup.oddT.mul_self_eq_one (c.subset_commSet huE).1
    rw [← map_mul, huu, map_one]
  have hv2 : szMk E vH * szMk E vH = 1 := by
    have hvv : vH * vH = 1 := by
      apply Subtype.ext
      show v * v = 1
      exact c.hyp.setup.oddT.mul_self_eq_one (c.subset_commSet hvE).1
    rw [← map_mul, hvv, map_one]
  have huPK : szMk E uH ∈ (P : Subgroup (SzBar E)) := by
    obtain ⟨huH, hmem⟩ := mem_szS_iff.mp huP
    have hsub : (⟨u, huH⟩ : H) = uH := Subtype.ext rfl
    rwa [hsub] at hmem
  have hvPK : szMk E vH ∈ (P : Subgroup (SzBar E)) := by
    obtain ⟨hvH, hmem⟩ := mem_szS_iff.mp hvP
    have hsub : (⟨v, hvH⟩ : H) = vH := Subtype.ext rfl
    rwa [hsub] at hmem
  set w : SzBar E := szMk E uH * szMk E vH with hwdef
  have hwP : w ∈ (P : Subgroup (SzBar E)) := P.mul_mem huPK hvPK
  have hw2 : w * w = 1 := by
    have hcH : uH * vH = vH * uH := Subtype.ext huv_comm.eq
    have hc : Commute (szMk E uH) (szMk E vH) := by
      show szMk E uH * szMk E vH = szMk E vH * szMk E uH
      rw [← map_mul, ← map_mul, hcH]
    rw [hwdef]
    calc szMk E uH * szMk E vH * (szMk E uH * szMk E vH)
        = szMk E uH * (szMk E vH * szMk E uH) * szMk E vH := by group
      _ = szMk E uH * (szMk E uH * szMk E vH) * szMk E vH := by rw [← hc.eq]
      _ = szMk E uH * szMk E uH * (szMk E vH * szMk E vH) := by group
      _ = 1 := by rw [hu2, hv2, mul_one]
  have hw1 : w ≠ 1 := by
    intro h1
    rw [hwdef] at h1
    have huveq : szMk E uH = szMk E vH := by
      have h2 : szMk E uH = (szMk E vH)⁻¹ := by
        calc szMk E uH = szMk E uH * ((szMk E vH) * (szMk E vH)⁻¹) := by group
          _ = (szMk E uH * szMk E vH) * (szMk E vH)⁻¹ := by group
          _ = (szMk E vH)⁻¹ := by rw [h1, one_mul]
      rwa [inv_eq_of_mul_eq_one_right hv2] at h2
    have hH : uH = vH := szMk_injective_of_szQ_eq_bot hQ huveq
    exact huv (congrArg Subtype.val hH)
  have hwZ : w ∈ sylowCenter (P : Subgroup (SzBar E)) := by
    rw [mem_sylowCenter]
    exact ⟨hwP, fun y hy =>
      (Asc72.IsBenderGroup.commute_of_mul_self_eq_one c.isBenderGroup P hwP hw2 y hy).symm⟩
  obtain ⟨b, hbC, hbH, hbimg⟩ :=
    c.exists_comp_of_mem_sylowCenter P ha haP hwZ hw1
  have hmem : u * v ∈ H := H.mul_mem (Subgroup.subset_closure huE)
    (Subgroup.subset_closure hvE)
  have himg : szMk E ⟨u * v, hmem⟩ = w := by
    have hdec : (⟨u * v, hmem⟩ : H) = uH * vH := rfl
    rw [hdec, map_mul, hwdef]
  have hbH' : b ∈ H := hbH
  have hEq : (⟨b, hbH'⟩ : H) = ⟨u * v, hmem⟩ :=
    szMk_injective_of_szQ_eq_bot hQ (by rw [hbimg, himg])
  have huveq : b = u * v := congrArg Subtype.val hEq
  exact ⟨huveq ▸ hbC.1, huveq ▸ hbC.2⟩

private theorem exists_conj_base (c : SzCfg G D d E e n) : ∃ g : G, g * d * g⁻¹ = e :=
  isConj_iff.mp (c.hyp.setup.isConj c.d_mem (c.subset_commSet c.e_mem).1)

private theorem viewE_e_eq_image (c : SzCfg G D d E e n) {g : G} (hg : g * d * g⁻¹ = e) :
    viewE D e = (fun x => g * x * g⁻¹) '' E := by
  have h := viewE_conj c.hyp.setup.normal g d
  rw [hg, c.viewE_eq] at h
  exact h

private theorem d_mem_viewE (c : SzCfg G D d E e n) : d ∈ viewE D e :=
  ⟨c.d_mem, (c.subset_commSet c.e_mem).2.1.symm, fun h => c.d_not_mem (c.rootSet_subset h)⟩

private theorem closure_rootSet_le_centralizer (c : SzCfg G D d E e n) :
    Subgroup.closure (rootSet D d) ≤
      Subgroup.centralizer (Subgroup.closure E : Set G) := by
  rw [Subgroup.closure_le]
  intro u hu
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro x hx
  exact (c.commute_of_mem_rootSet_d hu hx).eq.symm

private theorem mem_center_of_mem_closure_rootSet (c : SzCfg G D d E e n) {t : G}
    (ht : t ∈ Subgroup.closure (rootSet D d)) (htH : t ∈ Subgroup.closure E) :
    (⟨t, htH⟩ : ↥(Subgroup.closure E)) ∈
      Subgroup.center ↥(Subgroup.closure E) := by
  rw [Subgroup.mem_center_iff]
  intro h
  have hc := Subgroup.mem_centralizer_iff.mp (closure_rootSet_le_centralizer c ht) (h : G) h.2
  exact Subtype.ext hc

private theorem viewE_mul_mem_of_commute_d (c : SzCfg G D d E e n) (hQ : szQ E = ⊥)
    {g : G} (hg : g * d * g⁻¹ = e) {u v : G} (hu : u ∈ viewE D e) (hv : v ∈ viewE D e)
    (hud : Commute u d) (hvd : Commute v d) (huv : u ≠ v) :
    u * v ∈ viewE D e ∧ Commute (u * v) d := by
  have himg : viewE D e = (fun x => g * x * g⁻¹) '' E := viewE_e_eq_image c hg
  have hd : d ∈ (fun x => g * x * g⁻¹) '' E := himg ▸ d_mem_viewE c
  obtain ⟨a, haE, haeq⟩ := hd
  have hu' : u ∈ (fun x => g * x * g⁻¹) '' E := himg ▸ hu
  have hv' : v ∈ (fun x => g * x * g⁻¹) '' E := himg ▸ hv
  obtain ⟨x, hxE, hxeq⟩ := hu'
  obtain ⟨y, hyE, hyeq⟩ := hv'
  have hxeq' : g * x * g⁻¹ = u := hxeq
  have hyeq' : g * y * g⁻¹ = v := hyeq
  have haeq' : g * a * g⁻¹ = d := haeq
  have hxa : Commute x a := by
    apply (Commute.conj_iff g).mp
    rw [hxeq', haeq']
    exact hud
  have hya : Commute y a := by
    apply (Commute.conj_iff g).mp
    rw [hyeq', haeq']
    exact hvd
  have hxy : x ≠ y := by
    intro h
    apply huv
    rw [← hxeq, ← hyeq, h]
  have hcomp := szComp_mul_mem_of_szQ_eq_bot c hQ haE ⟨hxE, hxa⟩ ⟨hyE, hya⟩ hxy
  have huv_eq : u * v = g * (x * y) * g⁻¹ := by
    rw [← hxeq', ← hyeq']
    group
  refine ⟨?_, ?_⟩
  · rw [himg]
    exact ⟨x * y, hcomp.1, huv_eq.symm⟩
  · rw [huv_eq, ← haeq']
    exact (Commute.conj_iff g).mpr hcomp.2

private theorem mem_rootSet_d_or_comp_e_of_commute (c : SzCfg G D d E e n) {x : G}
    (hx : x ∈ D) (hxd : Commute x d) (hxe : Commute x e) :
    x ∈ rootSet D d ∨ x ∈ szComp E e := by
  rcases (c.commute_d_iff hx).mp hxd with hxr | hxE
  · exact Or.inl hxr
  · exact Or.inr ⟨hxE, hxe⟩

private theorem szComp_e_subset_rootSet (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) :
    szComp E e ⊆ rootSet D e := by
  intro t ht
  by_contra htroot
  have htE : t ∈ E := ht.1
  have htd : Commute t d := (c.subset_commSet htE).2.1
  have htview : t ∈ viewE D e := ⟨(c.subset_commSet htE).1, ht.2, htroot⟩
  have hdview : d ∈ viewE D e := d_mem_viewE c
  obtain ⟨g, hg⟩ := exists_conj_base c
  have hdt_ne : d ≠ t := fun h => c.d_not_mem (h.symm ▸ htE)
  obtain ⟨hdtview, hdtd⟩ :=
    viewE_mul_mem_of_commute_d c hQ hg hdview htview (Commute.refl d) htd hdt_ne
  rcases mem_rootSet_d_or_comp_e_of_commute c hdtview.1 hdtd hdtview.2.1 with hroot | hcomp
  · have htclosure : t ∈ Subgroup.closure (rootSet D d) := by
      have hdeq : d * (d * t) = t := by
        rw [← mul_assoc, c.hyp.setup.oddT.mul_self_eq_one c.d_mem, one_mul]
      rw [← hdeq]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (mem_rootSet_self c.d_mem))
        (Subgroup.subset_closure hroot)
    have htH : t ∈ Subgroup.closure E := Subgroup.subset_closure htE
    have hcenter := mem_center_of_mem_closure_rootSet c htclosure htH
    rw [center_eq_bot_of_szQ_eq_bot c hQ, Subgroup.mem_bot] at hcenter
    exact c.hyp.setup.oddT.ne_one (c.subset_commSet htE).1 (congrArg Subtype.val hcenter)
  · have hdt_ne_t : d * t ≠ t := by
      intro h
      exact c.hyp.setup.oddT.ne_one c.d_mem
        (mul_right_cancel (h.trans (one_mul t).symm))
    have hcomp' := szComp_mul_mem_of_szQ_eq_bot c hQ c.e_mem ht hcomp hdt_ne_t.symm
    have htdt : t * (d * t) = d := by
      calc t * (d * t) = (t * d) * t := by group
        _ = (d * t) * t := by rw [htd.eq]
        _ = d * (t * t) := by group
        _ = d := by rw [c.hyp.setup.oddT.mul_self_eq_one (c.subset_commSet htE).1, mul_one]
    have hdcomp : d ∈ szComp E e := htdt ▸ hcomp'
    exact c.d_not_mem hdcomp.1

private theorem szComp_eq_rootSet_e (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) :
    szComp E e = rootSet D e := by
  apply Set.Subset.antisymm (szComp_e_subset_rootSet c hQ)
  intro x hx
  refine ⟨c.rootSet_subset hx, ?_⟩
  exact (hx.2 e (c.subset_commSet c.e_mem).1).2 (Commute.refl e)

private theorem rootSet_d_eq_viewComp (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) :
    rootSet D d = {u | u ∈ viewE D e ∧ Commute u d} := by
  ext x
  constructor
  · intro hx
    have hxD : x ∈ D := hx.1
    have hxd : Commute x d := (hx.2 d c.d_mem).2 (Commute.refl d)
    have hxe : Commute x e := c.commute_of_mem_rootSet_d hx (Subgroup.subset_closure c.e_mem)
    have hxnot : x ∉ rootSet D e := fun hxre =>
      (Set.disjoint_left.mp c.disjoint) hx (c.rootSet_subset hxre)
    exact ⟨⟨hxD, hxe, hxnot⟩, hxd⟩
  · rintro ⟨hxview, hxd⟩
    rcases mem_rootSet_d_or_comp_e_of_commute c hxview.1 hxd hxview.2.1 with h | h
    · exact h
    · have hxrootE : x ∈ rootSet D e := (szComp_eq_rootSet_e c hQ).symm ▸ h
      exact absurd hxrootE hxview.2.2

private theorem rootSet_d_mul_mem (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) {u v : G}
    (hu : u ∈ rootSet D d) (hv : v ∈ rootSet D d) (huv : u ≠ v) :
    u * v ∈ rootSet D d := by
  rw [rootSet_d_eq_viewComp c hQ] at hu hv ⊢
  obtain ⟨g, hg⟩ := exists_conj_base c
  exact viewE_mul_mem_of_commute_d c hQ hg hu.1 hv.1 hu.2 hv.2 huv

private theorem isTriangle_of_not_commute (c : SzCfg G D d E e n) {y : G} (hy : y ∈ D)
    (hyd : ¬ Commute y d) (hye : ¬ Commute y e) : IsTriangle D d y e :=
  ⟨c.d_mem, (c.subset_commSet c.e_mem).1, hy, fun h => c.d_not_mem (h ▸ c.e_mem),
    (c.subset_commSet c.e_mem).2.1.symm, fun h => hyd h.symm, fun h => hye h.symm⟩

private theorem not_first_kind_of_not_commute (c : SzCfg G D d E e n) {y : G} (hy : y ∈ D)
    (hyd : ¬ Commute y d) (hye : ¬ Commute y e) : ¬ Odd (orderOf (d * e * y)) := by
  intro hodd
  have htri := isTriangle_of_not_commute c hy hyd hye
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  have hdeD : d * e ∈ D := htri.mul_mem_of_odd c.hyp.setup.oddT c.hyp.setup.normal hodd
  have hde_ne : d ≠ e := fun h => c.d_not_mem (h ▸ c.e_mem)
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  have hiff := Asc72.IsOddTransp.commute_iff_of_mul_mem c.hyp.setup.oddT c.d_mem heD
    hde_ne hde_comm hdeD
  have hroot : e ∈ rootSet D d := by
    refine (CFSG.Timmesfeld.mem_rootSet_iff c.hyp.setup.isClass c.d_mem).mpr
      ⟨heD, hde_comm, ?_⟩
    intro f hf hdf
    exact ((hiff f hf).mp hdf.symm).symm
  exact (Set.disjoint_left.mp c.disjoint) hroot c.e_mem

private theorem false_of_third_kind_rootSet (c : SzCfg G D d E e n) (hQ : szQ E = ⊥)
    {y z : G} (hy : y ∈ D) (hye : ¬ Commute y e)
    (hz1 : z ≠ 1) (hzy : Commute z y) (ht : d * e * z ∈ rootSet D d) : False := by
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  have hdd : d * d = 1 := c.hyp.setup.oddT.mul_self_eq_one c.d_mem
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  by_cases ht_eq : d * e * z = d
  · have hez : e * z = 1 := by
      have h := congrArg (fun w => d * w) ht_eq
      rw [hdd] at h
      rwa [show d * (d * e * z) = e * z by
        calc d * (d * e * z) = (d * d) * (e * z) := by group
          _ = e * z := by rw [hdd, one_mul]] at h
    have hzeq : z = e := by
      have h := congrArg (fun w => e * w) hez
      rw [mul_one] at h
      rwa [show e * (e * z) = z by
        rw [← mul_assoc, c.hyp.setup.oddT.mul_self_eq_one heD, one_mul]] at h
    exact hye ((hzeq ▸ hzy : Commute e y)).symm
  · have hroot_d : d ∈ rootSet D d := mem_rootSet_self c.d_mem
    have ht_ne : d ≠ d * e * z := fun h => ht_eq h.symm
    have hroot_prod : d * (d * e * z) ∈ rootSet D d :=
      rootSet_d_mul_mem c hQ hroot_d ht ht_ne
    have hez_root : e * z ∈ rootSet D d := by
      have hEq : d * (d * e * z) = e * z := by
        calc d * (d * e * z) = (d * d) * (e * z) := by group
          _ = e * z := by rw [hdd, one_mul]
      rwa [hEq] at hroot_prod
    have hezD : e * z ∈ D := hez_root.1
    have he_ne : e ≠ e * z := by
      intro h
      have h1 : e * 1 = e * z := by rw [mul_one]; exact h
      exact hz1 (mul_left_cancel h1).symm
    have hz_decomp : e * (e * z) = z := by
      rw [← mul_assoc, c.hyp.setup.oddT.mul_self_eq_one heD, one_mul]
    have hyz : Commute y (e * (e * z)) := by
      rw [hz_decomp]
      exact hzy.symm
    have hcomm_e_ez : Commute e (e * z) :=
      (c.commute_of_mem_rootSet_d hez_root (Subgroup.subset_closure c.e_mem)).symm
    exact hye ((c.hyp.setup.oddT.commute_mul_iff heD hezD hy he_ne hcomm_e_ez).mp hyz).1

private theorem false_of_third_kind_comp (c : SzCfg G D d E e n) (hQ : szQ E = ⊥)
    {y z : G} (hy : y ∈ D) (hyd : ¬ Commute y d)
    (hz1 : z ≠ 1) (hzd : Commute z d) (hzy : Commute z y)
    (ht : d * e * z ∈ szComp E e) : False := by
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  have hdd : d * d = 1 := c.hyp.setup.oddT.mul_self_eq_one c.d_mem
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  by_cases ht_eq : d * e * z = e
  · have hdz : d * z = 1 := by
      have h := congrArg (fun w => e * w) ht_eq
      rw [c.hyp.setup.oddT.mul_self_eq_one heD] at h
      rwa [show e * (d * e * z) = d * z by
        calc e * (d * e * z) = (e * d) * e * z := by group
          _ = (d * e) * e * z := by rw [hde_comm.eq.symm]
          _ = d * (e * e) * z := by group
          _ = d * z := by rw [c.hyp.setup.oddT.mul_self_eq_one heD, mul_one]] at h
    have hzeq : z = d := by
      have h := congrArg (fun w => d * w) hdz
      rw [mul_one] at h
      rwa [show d * (d * z) = z by rw [← mul_assoc, hdd, one_mul]] at h
    exact hyd ((hzeq ▸ hzy : Commute d y)).symm
  · have ht_ne : e ≠ d * e * z := fun h => ht_eq h.symm
    have he_comp : e ∈ szComp E e := ⟨c.e_mem, Commute.refl e⟩
    have hcomp : e * (d * e * z) ∈ szComp E e :=
      szComp_mul_mem_of_szQ_eq_bot c hQ c.e_mem he_comp ht ht_ne
    have heq_dz : e * (d * e * z) = d * z := by
      calc e * (d * e * z) = (e * d) * e * z := by group
        _ = (d * e) * e * z := by rw [hde_comm.eq.symm]
        _ = d * (e * e) * z := by group
        _ = d * z := by rw [c.hyp.setup.oddT.mul_self_eq_one heD, mul_one]
    have hdz_comp : d * z ∈ szComp E e := heq_dz ▸ hcomp
    have hdzD : d * z ∈ D := (c.subset_commSet hdz_comp.1).1
    have hne : d ≠ d * z := by
      intro h
      have h1 : d * 1 = d * z := by rw [mul_one]; exact h
      exact hz1 (mul_left_cancel h1).symm
    have hz_decomp : d * (d * z) = z := by
      rw [← mul_assoc, hdd, one_mul]
    have hyz : Commute y (d * (d * z)) := by
      rw [hz_decomp]
      exact hzy.symm
    have hcomm_d_dz : Commute d (d * z) := (Commute.refl d).mul_right hzd.symm
    exact hyd ((c.hyp.setup.oddT.commute_mul_iff c.d_mem hdzD hy hne hcomm_d_dz).mp hyz).1

private theorem not_third_kind_of_not_commute (c : SzCfg G D d E e n) (hQ : szQ E = ⊥)
    {y : G} (hy : y ∈ D) (hyd : ¬ Commute y d) (hye : ¬ Commute y e) :
    ¬ IsThirdKind d y e := by
  rintro ⟨m, hm_odd, hm1, hord⟩
  have htri := isTriangle_of_not_commute c hy hyd hye
  obtain ⟨-, hz1, hzd, hze, hzy, htD⟩ :=
    htri.third_kind c.hyp.setup.oddT c.hyp.setup.normal hm_odd hord
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  have hd_de : Commute d (d * e) := (Commute.refl d).mul_right hde_comm
  have hde_z : Commute (d * e) ((d * e * y) ^ m) := by
    show (d * e) * (d * e * y) ^ m = (d * e * y) ^ m * (d * e)
    have h1 : Commute d ((d * e * y) ^ m) := hzd.symm
    have h2 : Commute e ((d * e * y) ^ m) := hze.symm
    exact (h1.mul_left h2).eq
  have htd : Commute (d * e * (d * e * y) ^ m) d :=
    (hd_de.symm).mul_left hzd
  have hte : Commute (d * e * (d * e * y) ^ m) e :=
    (hde_comm.mul_left (Commute.refl e)).mul_left hze
  rcases mem_rootSet_d_or_comp_e_of_commute c htD htd hte with hroot | hcomp
  · exact false_of_third_kind_rootSet c hQ hy hye hz1 hzy hroot
  · exact false_of_third_kind_comp c hQ hy hyd hz1 hzd hzy hcomp

private theorem isPGroup_zpowers_sup_conjClosure {x : G}
    (hx2 : x * x = 1) (hSK : SecondKindStructure d x e) :
    IsPGroup 2 ↥(Subgroup.zpowers x ⊔ conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e)) := by
  let N : Subgroup G := conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e)
  have hN2 : IsPGroup 2 N := by
    rw [IsPGroup.iff_orderOf]
    intro q
    have hq2 : q * q = 1 := by
      apply Subtype.ext
      exact hSK.sq (q : G) q.2
    have hdvd : orderOf q ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hq2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact ⟨0, by simpa [h]⟩
    · exact ⟨1, by simpa [h]⟩
  have h1 : IsPGroup 2 (Subgroup.zpowers x) :=
    RootClosure.isPGroup_zpowers_of_mul_self_eq_one hx2
  have hxN : x ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hSK.normal x (Subgroup.subset_closure (by simp)) q hq
    · intro hq
      have hxinvK : x⁻¹ ∈ Subgroup.closure ({d, x, e} : Set G) :=
        Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      have := hSK.normal x⁻¹ hxinvK (x * q * x⁻¹) hq
      rwa [show x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q by group] at this
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  exact IsPGroup.to_sup_of_normal_right' h1 hN2 hnorm

private theorem secondKind_d_pow (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) {x : G}
    (hxD : x ∈ D) (hxd : ¬ Commute x d) (hxe : ¬ Commute x e)
    (hSK : SecondKindStructure d x e) :
    ∀ n ∈ conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e),
      n * d * n⁻¹ = d ∨ n * d * n⁻¹ = e := by
  let K : Subgroup G := Subgroup.closure ({d, x, e} : Set G)
  let N : Subgroup G := conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e)
  have hdeN : d * e ∈ N := Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hdd : d * d = 1 := c.hyp.setup.oddT.mul_self_eq_one c.d_mem
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  have hde_ne : d ≠ e := fun h => c.d_not_mem (h ▸ c.e_mem)
  intro n hn
  have hnD : n * d * n⁻¹ ∈ D := c.hyp.setup.conj_mem n c.d_mem
  have hn_de : Commute n (d * e) := hSK.comm n hn (d * e) hdeN
  have hd_de : Commute d (d * e) := (Commute.refl d).mul_right hde_comm
  have hconj : Commute (n * d * n⁻¹) (n * (d * e) * n⁻¹) :=
    (Commute.conj_iff n).mpr hd_de
  have hdn_de : Commute (n * d * n⁻¹) (d * e) := by
    rwa [show n * (d * e) * n⁻¹ = d * e by rw [hn_de.eq]; group] at hconj
  have hboth := (c.hyp.setup.oddT.commute_mul_iff c.d_mem heD hnD hde_ne hde_comm).mp hdn_de
  have hprodN : d * (n * d * n⁻¹) ∈ N := by
    have hdn_norm : d * n * d⁻¹ ∈ N :=
      hSK.normal d (Subgroup.subset_closure (by simp)) n hn
    have hn2 : n * n = 1 := hSK.sq n hn
    have hEq : d * (n * d * n⁻¹) = (d * n * d⁻¹) * n⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hdd, inv_eq_of_mul_eq_one_right hn2]
      group
    rw [hEq]
    exact N.mul_mem hdn_norm (N.inv_mem hn)
  rcases mem_rootSet_d_or_comp_e_of_commute c hnD hboth.1 hboth.2 with hroot | hcomp
  · by_cases hdn_eq : n * d * n⁻¹ = d
    · exact Or.inl hdn_eq
    · exfalso
      have hroot_prod : d * (n * d * n⁻¹) ∈ rootSet D d :=
        rootSet_d_mul_mem c hQ (mem_rootSet_self c.d_mem) hroot (fun h => hdn_eq h.symm)
      have hsup := isPGroup_zpowers_sup_conjClosure (c.hyp.setup.oddT.mul_self_eq_one hxD) hSK
      have hcommx : Commute (d * (n * d * n⁻¹)) x :=
        c.hyp.setup.oddT.commute_of_isPGroup hsup hroot_prod.1 hxD
          (Subgroup.mem_sup_right hprodN) (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      exact hxd (((hroot_prod.2 x hxD).mp hcommx)).symm
  · by_cases hdn_eq : n * d * n⁻¹ = e
    · exact Or.inr hdn_eq
    · exfalso
      have he_comp : e ∈ szComp E e := ⟨c.e_mem, Commute.refl e⟩
      have hcomp' : e * (n * d * n⁻¹) ∈ szComp E e :=
        szComp_mul_mem_of_szQ_eq_bot c hQ c.e_mem he_comp hcomp (fun h => hdn_eq h.symm)
      have heq : e * (n * d * n⁻¹) = (d * e) * (d * (n * d * n⁻¹)) := by
        calc e * (n * d * n⁻¹) = e * (d * d) * (n * d * n⁻¹) := by rw [hdd, mul_one]
          _ = (e * d) * (d * (n * d * n⁻¹)) := by group
          _ = (d * e) * (d * (n * d * n⁻¹)) := by rw [hde_comm.eq.symm]
      have hprodN' : (d * e) * (d * (n * d * n⁻¹)) ∈ N := N.mul_mem hdeN hprodN
      have hprodN'' : e * (n * d * n⁻¹) ∈ N := heq ▸ hprodN'
      have hsup := isPGroup_zpowers_sup_conjClosure (c.hyp.setup.oddT.mul_self_eq_one hxD) hSK
      have hcommx : Commute (e * (n * d * n⁻¹)) x :=
        c.hyp.setup.oddT.commute_of_isPGroup hsup (c.subset_commSet hcomp'.1).1 hxD
          (Subgroup.mem_sup_right hprodN'') (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      have hrootE : e * (n * d * n⁻¹) ∈ rootSet D e :=
        (szComp_eq_rootSet_e c hQ).symm ▸ hcomp'
      exact hxe (((hrootE.2 x hxD).mp hcommx)).symm

private theorem exists_second_kind (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) :
    ∃ x ∈ D, ¬ Commute x d ∧ ¬ Commute x e ∧ orderOf (d * e * x) = 4 := by
  obtain ⟨x, hxD, hxd, hxe⟩ := c.exists_not_commute_both c.e_mem
  refine ⟨x, hxD, hxd, hxe, ?_⟩
  have htri := isTriangle_of_not_commute c hxD hxd hxe
  rcases htri.orderOf_cases c.hyp.setup.oddT c.hyp.setup.normal with h | h | h
  · exact absurd h.1 (not_first_kind_of_not_commute c hxD hxd hxe)
  · exact h
  · exact absurd h (not_third_kind_of_not_commute c hQ hxD hxd hxe)

private theorem secondKindStructure_of_order (c : SzCfg G D d E e n) (hQ : szQ E = ⊥)
    {x : G} (hxD : x ∈ D) (hxd : ¬ Commute x d) (hxe : ¬ Commute x e)
    (hord : orderOf (d * e * x) = 4) : SecondKindStructure d x e := by
  have htri := isTriangle_of_not_commute c hxD hxd hxe
  have hno : ∀ y ∈ D, y ∈ Subgroup.closure ({d, x} : Set G) → IsTriangle D d y e →
      ¬ IsThirdKind d y e := by
    intro y hy hyK htriy
    rcases htriy with ⟨-, -, -, -, -, hdy, hey⟩
    exact not_third_kind_of_not_commute c hQ hy (fun h => hdy h.symm) (fun h => hey h.symm)
  have hSK : OddTranspSecondKind := OddTransp.oddTranspSecondKind
  exact hSK (G := G) (D := D) c.hyp.setup.oddT c.hyp.setup.normal d x e htri hord hno

private theorem secondKind_commutator_d_le (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) {x : G}
    (hxD : x ∈ D) (hxd : ¬ Commute x d) (hxe : ¬ Commute x e)
    (hSK : SecondKindStructure d x e) :
    ⁅conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e), Subgroup.zpowers d⁆ ≤
      Subgroup.zpowers (d * e) := by
  have hdd : d * d = 1 := c.hyp.setup.oddT.mul_self_eq_one c.d_mem
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  rw [Subgroup.commutator_le]
  intro q hq k hk
  rcases CFSG.Timmesfeld.Bridge.eq_one_or_eq_of_mem_zpowers hdd hk with hk1 | hkd
  · rw [hk1]
    simpa [commutatorElement_def] using Subgroup.one_mem (Subgroup.zpowers (d * e))
  · rw [hkd]
    rcases secondKind_d_pow c hQ hxD hxd hxe hSK q hq with hdq | hdq
    · have h1 : ⁅q, d⁆ = 1 := by
        rw [commutatorElement_def, hdq, inv_eq_of_mul_eq_one_right hdd]
        exact hdd
      rw [h1]
      exact Subgroup.one_mem _
    · have h1 : ⁅q, d⁆ = d * e := by
        rw [commutatorElement_def, hdq, inv_eq_of_mul_eq_one_right hdd]
        exact hde_comm.eq.symm
      rw [h1]
      exact Subgroup.mem_zpowers (d * e)

private theorem secondKind_commutator_x_le (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) {x g : G}
    (hxD : x ∈ D) (hxd : ¬ Commute x d) (hxe : ¬ Commute x e)
    (hSK : SecondKindStructure d x e)
    (hgK : g ∈ Subgroup.closure ({d, x} : Set G)) (hgx : g * d * g⁻¹ = x) :
    ⁅conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e), Subgroup.zpowers x⁆ ≤
      Subgroup.zpowers (g * (d * e) * g⁻¹) := by
  have hKsub : Subgroup.closure ({d, x} : Set G) ≤ Subgroup.closure ({d, x, e} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  have hgK' : g ∈ Subgroup.closure ({d, x, e} : Set G) := hKsub hgK
  have hginvK' : g⁻¹ ∈ Subgroup.closure ({d, x, e} : Set G) := Subgroup.inv_mem _ hgK'
  have hbound := secondKind_commutator_d_le c hQ hxD hxd hxe hSK
  rw [Subgroup.commutator_le]
  intro q hq k hk
  rcases CFSG.Timmesfeld.Bridge.eq_one_or_eq_of_mem_zpowers
    (c.hyp.setup.oddT.mul_self_eq_one hxD) hk with hk1 | hkx
  · rw [hk1]
    simpa [commutatorElement_def] using
      Subgroup.one_mem (Subgroup.zpowers (g * (d * e) * g⁻¹))
  · rw [hkx]
    have hq' : g⁻¹ * q * g ∈ conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e) := by
      simpa using hSK.normal g⁻¹ hginvK' q hq
    have hcomm' := Subgroup.commutator_le.mp hbound (g⁻¹ * q * g) hq' d
      (Subgroup.mem_zpowers d)
    obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp hcomm'
    have hEq : ⁅q, x⁆ = g * ⁅g⁻¹ * q * g, d⁆ * g⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def, ← hgx]
      group
    rw [hEq, ← hk']
    exact Subgroup.mem_zpowers_iff.mpr ⟨k', by rw [conj_zpow]⟩

private theorem closure_pair_le_closure_triple {x : G} :
    Subgroup.closure ({d, x} : Set G) ≤ Subgroup.closure ({d, x, e} : Set G) := by
  apply Subgroup.closure_mono
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  tauto

private theorem secondKind_card_le (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) {x g : G}
    (hxD : x ∈ D) (hxd : ¬ Commute x d) (hxe : ¬ Commute x e)
    (hSK : SecondKindStructure d x e)
    (hgK : g ∈ Subgroup.closure ({d, x} : Set G)) (hgx : g * d * g⁻¹ = x) :
    Nat.card (conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e)) ≤ 4 := by
  let N : Subgroup G := conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e)
  have hdd : d * d = 1 := c.hyp.setup.oddT.mul_self_eq_one c.d_mem
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  have hdeN : d * e ∈ N := Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hvN : g * (d * e) * g⁻¹ ∈ N :=
    hSK.normal g (closure_pair_le_closure_triple hgK) (d * e) hdeN
  have hde2 : (d * e) * (d * e) = 1 := by
    calc (d * e) * (d * e) = d * (e * d) * e := by group
      _ = d * (d * e) * e := by rw [hde_comm.eq]
      _ = d * d * (e * e) := by group
      _ = 1 := by
        rw [hdd, c.hyp.setup.oddT.mul_self_eq_one heD, mul_one]
  have hv2 : (g * (d * e) * g⁻¹) * (g * (d * e) * g⁻¹) = 1 := by
    calc (g * (d * e) * g⁻¹) * (g * (d * e) * g⁻¹)
        = g * ((d * e) * (d * e)) * g⁻¹ := by group
      _ = 1 := by rw [hde2]; group
  have huv : Commute (d * e) (g * (d * e) * g⁻¹) :=
    hSK.comm (d * e) hdeN (g * (d * e) * g⁻¹) hvN
  have hle : N ≤ Subgroup.closure ({d * e, g * (d * e) * g⁻¹} : Set G) := by
    change conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e) ≤ _
    rw [hSK.eq_sup]
    exact sup_le
      ((secondKind_commutator_d_le c hQ hxD hxd hxe hSK).trans
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))))
      ((secondKind_commutator_x_le c hQ hxD hxd hxe hSK hgK hgx).trans
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))))
  exact (Subgroup.card_le_of_le hle).trans
    (CFSG.GF2Type.Widths1112.card_closure_pair_le_four hde2 hv2 huv.eq)

private theorem odd_and_three_not_dvd_orderOf_mul (c : SzCfg G D d E e n)
    {x : G} (hxD : x ∈ D) (hxd : ¬ Commute x d) :
    Odd (orderOf (d * x)) ∧ ¬ 3 ∣ orderOf (d * x) := by
  have hodd : Odd (orderOf (d * x)) :=
    c.hyp.setup.oddT.odd_of_not_commute c.d_mem hxD (fun h => hxd h.symm)
  obtain ⟨c₀, hc₀D, hc₀d, hc₀x⟩ :=
    commonNeighbour (G := G) (D := D) c.hyp.setup
      (fun a ha b hb => Classical.byContradiction fun h => c.hyp.conn ⟨a, ha, b, hb, h⟩) c.hyp.sq
      d c.d_mem x hxD (fun h => hxd h.symm)
  have hc₀E : c₀ ∈ E := by
    rcases (c.commute_d_iff hc₀D).mp hc₀d with hroot | hE
    · exfalso
      exact hxd ((hroot.2 x hxD).mp hc₀x).symm
    · exact hE
  have hdview : d ∈ viewE D c₀ := by
    refine ⟨c.d_mem, hc₀d.symm, ?_⟩
    intro hdroot
    exact hxd ((hdroot.2 x hxD).mpr hc₀x).symm
  have hxview : x ∈ viewE D c₀ := by
    refine ⟨hxD, hc₀x.symm, ?_⟩
    intro hxroot
    exact hxd ((hxroot.2 d c.d_mem).mpr hc₀d)
  obtain ⟨g, hg⟩ := isConj_iff.mp (c.hyp.setup.isConj c.d_mem hc₀D)
  have himg : viewE D c₀ = (fun y => g * y * g⁻¹) '' E := by
    have h := viewE_conj c.hyp.setup.normal g d
    rw [hg, c.viewE_eq] at h
    exact h
  have hdimg : d ∈ (fun y => g * y * g⁻¹) '' E := himg ▸ hdview
  have hximg : x ∈ (fun y => g * y * g⁻¹) '' E := himg ▸ hxview
  obtain ⟨a, haE, haeq⟩ := hdimg
  obtain ⟨b, hbE, hbeq⟩ := hximg
  have hda : g⁻¹ * d * g = a := by
    calc g⁻¹ * d * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [← haeq]
      _ = a := by group
  have hxb : g⁻¹ * x * g = b := by
    calc g⁻¹ * x * g = g⁻¹ * (g * b * g⁻¹) * g := by rw [← hbeq]
      _ = b := by group
  have hdxH : g⁻¹ * (d * x) * g ∈ Subgroup.closure E := by
    rw [show g⁻¹ * (d * x) * g = (g⁻¹ * d * g) * (g⁻¹ * x * g) by group, hda, hxb]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure haE) (Subgroup.subset_closure hbE)
  have hordconj : orderOf (g⁻¹ * (d * x) * g) = orderOf (d * x) := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (d * x)
    simpa [MulAut.conj_apply, mul_assoc] using h
  have h3H : ¬ 3 ∣ Nat.card ↥(Subgroup.closure E) := c.not_three_dvd
  have h3conj : ¬ 3 ∣ orderOf (g⁻¹ * (d * x) * g) := fun h =>
    h3H (h.trans (by
      rw [Subgroup.orderOf_coe
        (⟨g⁻¹ * (d * x) * g, hdxH⟩ : ↥(Subgroup.closure E))]
      exact orderOf_dvd_natCard _))
  refine ⟨hodd, ?_⟩
  rwa [hordconj] at h3conj

private theorem eq_one_of_dvd_factorial_of_dvd {k m n : ℕ} (hn : n ≤ 4) (hk : k ∣ n.factorial)
    (hkm : k ∣ m) (hm : Odd m) (h3 : ¬ 3 ∣ m) : k = 1 := by
  have h24 : k ∣ 2 ^ 3 * 3 := by
    have h := hk.trans (Nat.factorial_dvd_factorial hn)
    rwa [show (4 : ℕ).factorial = 2 ^ 3 * 3 by decide] at h
  have hcop : Nat.Coprime m (2 ^ 3 * 3) :=
    ((Nat.coprime_two_right.mpr hm).pow_right 3).mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  exact (Nat.Coprime.coprime_dvd_left hkm hcop).eq_one_of_dvd h24

private theorem false_of_szQ_eq_bot (c : SzCfg G D d E e n) (hQ : szQ E = ⊥) : False := by
  obtain ⟨x, hxD, hxd, hxe, hord⟩ := exists_second_kind c hQ
  have hSK : SecondKindStructure d x e := secondKindStructure_of_order c hQ hxD hxd hxe hord
  obtain ⟨g, hgK, hgx⟩ :=
    Asc72.IsOddTransp.exists_conj c.hyp.setup.oddT c.d_mem hxD (fun h => hxd h.symm)
  have hcard := secondKind_card_le c hQ hxD hxd hxe hSK hgK hgx
  let K : Subgroup G := Subgroup.closure ({d, x, e} : Set G)
  let N : Subgroup G := conjClosure (Subgroup.closure ({d, x} : Set G)) (d * e)
  have hhN : ∀ a ∈ K, ∀ b ∈ N, a * b * a⁻¹ ∈ N := hSK.normal
  have hdK : d ∈ K := Subgroup.subset_closure (by simp)
  have hxK : x ∈ K := Subgroup.subset_closure (by simp)
  have hdxK : d * x ∈ K := K.mul_mem hdK hxK
  have hdeN : d * e ∈ N :=
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hnorm : d * x ∈ Subgroup.normalizer (N : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨hhN _ hdxK b, fun hb => ?_⟩
    have hb' : b = (d * x)⁻¹ * ((d * x) * b * (d * x)⁻¹) * (d * x)⁻¹⁻¹ := by group
    rw [hb']
    exact hhN _ (K.inv_mem hdxK) _ hb
  let φ : Subgroup.normalizer (N : Set G) →* Equiv.Perm N :=
    (MulAut.toPerm N).comp N.normalizerMonoidHom
  let σ : Equiv.Perm N := φ ⟨d * x, hnorm⟩
  have hσperm : orderOf σ ∣ (Nat.card N).factorial := by
    simpa [Nat.card_perm] using orderOf_dvd_natCard σ
  have hdxpow : (⟨d * x, hnorm⟩ : Subgroup.normalizer (N : Set G)) ^ orderOf (d * x) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  have hσpow : σ ^ orderOf (d * x) = 1 := by
    change φ ⟨d * x, hnorm⟩ ^ orderOf (d * x) = 1
    rw [← map_pow, hdxpow, map_one]
  have h3odd := odd_and_three_not_dvd_orderOf_mul c hxD hxd
  have hσ1 : orderOf σ = 1 := eq_one_of_dvd_factorial_of_dvd hcard hσperm
    (orderOf_dvd_iff_pow_eq_one.mpr hσpow) h3odd.1 h3odd.2
  have hfix : σ ⟨d * e, hdeN⟩ = ⟨d * e, hdeN⟩ := by
    rw [show σ = 1 from orderOf_eq_one_iff.mp hσ1, Equiv.Perm.one_apply]
  have hconj : (d * x) * (d * e) * (d * x)⁻¹ = d * e := by
    have h := congrArg Subtype.val hfix
    change ((N.normalizerMonoidHom ⟨d * x, hnorm⟩) ⟨d * e, hdeN⟩ : G) = d * e at h
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  have hcomm : Commute (d * x) (d * e) := by
    show (d * x) * (d * e) = (d * e) * (d * x)
    calc (d * x) * (d * e) = (d * x) * (d * e) * (d * x)⁻¹ * (d * x) := by group
      _ = (d * e) * (d * x) := by rw [hconj]
  have hdd : d * d = 1 := c.hyp.setup.oddT.mul_self_eq_one c.d_mem
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  have hde_comm : Commute d e := (c.subset_commSet c.e_mem).2.1.symm
  have hde_ne : d ≠ e := fun h => c.d_not_mem (h ▸ c.e_mem)
  have hd_de : Commute d (d * e) := (Commute.refl d).mul_right hde_comm
  have hxde : Commute x (d * e) := by
    have h := hd_de.mul_left hcomm
    rwa [show d * (d * x) = x by rw [← mul_assoc, hdd, one_mul]] at h
  exact hxd ((c.hyp.setup.oddT.commute_mul_iff c.d_mem heD hxD hde_ne hde_comm).mp hxde).1

theorem SzCfg.exists_not_commute_szQ (c : SzCfg G D d E e n) :
    ∃ y ∈ szQ E, ∃ x ∈ E, ¬ Commute y x := by
  by_contra h
  have hcent : ∀ y ∈ szQ E, ∀ x ∈ E, Commute y x := by
    intro y hy x hx
    by_contra hc
    exact h ⟨y, hy, x, hx, hc⟩
  exact false_of_szQ_eq_bot c (szQ_eq_bot_of_forall_commute c hcent)

end CFSG.Timmesfeld.Bridge.OddRoot
