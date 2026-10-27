module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainBlock
import CFSG.Timmesfeld.Bridge.OddLocalBlock

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

@[expose] def szLineSet (D : Set G) (d e : G) : Set G :=
  {x | x ∈ D ∧ Commute x d ∧ Commute x e}

@[expose] def szLine (D : Set G) (d e : G) : Set (Set G) :=
  {X | ∃ a ∈ szLineSet D d e, X = rootSet D a}

@[expose] def szLineStab (D : Set G) (d e : G) : Subgroup G :=
  Subgroup.normalizer (szLineSet D d e) ⊓ Subgroup.normalizer D

theorem conj_mem_szLineSet (r : ↥(szLineStab D d e)) {a : G} (ha : a ∈ szLineSet D d e) :
    (r : G) * a * (r : G)⁻¹ ∈ szLineSet D d e :=
  (Subgroup.mem_set_normalizer_iff.mp r.2.1 a).mp ha

private theorem conjSet_mem_line (r : ↥(szLineStab D d e)) {X : Set G}
    (hX : X ∈ szLine D d e) : OddLocal.conjSet (r : G) X ∈ szLine D d e := by
  obtain ⟨a, ha, rfl⟩ := hX
  refine ⟨(r : G) * a * (r : G)⁻¹, conj_mem_szLineSet r ha, ?_⟩
  have himage : (MulAut.conj (r : G)) '' D = D :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp r.2.2
  have hfun : (⇑(MulAut.conj (r : G)) : G → G) = fun x => (r : G) * x * (r : G)⁻¹ :=
    funext (MulAut.conj_apply (r : G))
  have h := CFSG.Timmesfeld.rootSet_map (MulAut.conj (r : G)) (E := D) himage a
  have h' : (fun x => (r : G) * x * (r : G)⁻¹) '' rootSet D a =
      rootSet D ((r : G) * a * (r : G)⁻¹) := by simpa [hfun] using h.symm
  rw [OddLocal.conjSet]
  exact h'

def szLineHom (D : Set G) (d e : G) :
    ↥(szLineStab D d e) →* Equiv.Perm ↥(szLine D d e) where
  toFun r :=
    { toFun := fun X => ⟨OddLocal.conjSet (r : G) X.1, conjSet_mem_line r X.2⟩
      invFun := fun X => ⟨OddLocal.conjSet ((r : G)⁻¹) X.1,
        conjSet_mem_line (r⁻¹) X.2⟩
      left_inv := fun X => Subtype.ext (by
        ext x
        simp [OddLocal.conjSet, mul_assoc])
      right_inv := fun X => Subtype.ext (by
        ext x
        simp [OddLocal.conjSet, mul_assoc]) }
  map_one' := by
    apply Equiv.ext
    intro X
    apply Subtype.ext
    ext x
    simp [OddLocal.conjSet]
  map_mul' r s := by
    apply Equiv.ext
    intro X
    apply Subtype.ext
    ext x
    simp [OddLocal.conjSet, mul_assoc]

theorem szLineHom_apply (r : ↥(szLineStab D d e)) (X : ↥(szLine D d e)) :
    ((szLineHom D d e r X : ↥(szLine D d e)) : Set G) =
      (fun x => (r : G) * x * (r : G)⁻¹) '' (X : Set G) := by simp [szLineHom, OddLocal.conjSet]

@[expose] def szLinePt (D : Set G) (d e a : G) (ha : a ∈ szLineSet D d e) : ↥(szLine D d e) :=
  ⟨rootSet D a, a, ha, rfl⟩

theorem szLineHom_szLinePt (r : ↥(szLineStab D d e)) {a : G} (ha : a ∈ szLineSet D d e) :
    szLineHom D d e r (szLinePt D d e a ha) =
      szLinePt D d e ((r : G) * a * (r : G)⁻¹) (conj_mem_szLineSet r ha) := by
  apply Subtype.ext
  rw [szLineHom_apply]
  change (fun x => (r : G) * x * (r : G)⁻¹) '' rootSet D a =
    rootSet D ((r : G) * a * (r : G)⁻¹)
  have himage : (MulAut.conj (r : G)) '' D = D :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp r.2.2
  have hfun : (⇑(MulAut.conj (r : G)) : G → G) = fun x => (r : G) * x * (r : G)⁻¹ :=
    funext (MulAut.conj_apply (r : G))
  have h := CFSG.Timmesfeld.rootSet_map (MulAut.conj (r : G)) (E := D) himage a
  simpa [hfun] using h.symm

theorem szLinePt_eq_iff {a b : G} (ha : a ∈ szLineSet D d e) (hb : b ∈ szLineSet D d e) :
    szLinePt D d e a ha = szLinePt D d e b hb ↔ rootSet D a = rootSet D b :=
  Subtype.mk_eq_mk

theorem exists_szLinePt (X : ↥(szLine D d e)) :
    ∃ a, ∃ ha : a ∈ szLineSet D d e, X = szLinePt D d e a ha := by
  obtain ⟨a, ha, hX⟩ := X.2
  exact ⟨a, ha, Subtype.ext hX⟩

theorem SzCfg.d_mem_szLineSet (c : SzCfg G D d E e n) : d ∈ szLineSet D d e :=
  ⟨c.d_mem, Commute.refl d, ((c.subset_commSet c.e_mem).2.1).symm⟩

theorem SzCfg.e_mem_szLineSet (c : SzCfg G D d E e n) : e ∈ szLineSet D d e :=
  ⟨(c.subset_commSet c.e_mem).1, (c.subset_commSet c.e_mem).2.1, Commute.refl e⟩

private theorem mem_normalizer_D (c : SzCfg G D d E e n) (g : G) :
    g ∈ Subgroup.normalizer D := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · exact c.hyp.setup.normal g x
  · intro hx
    have h := c.hyp.setup.normal g⁻¹ (g * x * g⁻¹) hx
    simpa [mul_assoc] using h

private theorem closure_le_centralizer_d (c : SzCfg G D d E e n) :
    Subgroup.closure E ≤ Subgroup.centralizer ({d} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr (c.subset_commSet hx).2.1

theorem SzCfg.conj_d_eq_of_mem_closure (c : SzCfg G D d E e n) {h : G}
    (hh : h ∈ Subgroup.closure E) : h * d * h⁻¹ = d := by
  have hcomm : h * d = d * h :=
    Subgroup.mem_centralizer_singleton_iff.mp (closure_le_centralizer_d c hh)
  rw [hcomm]
  group

theorem SzCfg.szLineHom_fix_of_mem_closure (c : SzCfg G D d E e n) {r : ↥(szLineStab D d e)}
    (hr : (r : G) ∈ Subgroup.closure E) :
    szLineHom D d e r (szLinePt D d e d c.d_mem_szLineSet) =
      szLinePt D d e d c.d_mem_szLineSet := by
  apply Subtype.ext
  rw [szLineHom_apply]
  change (fun x => (r : G) * x * (r : G)⁻¹) '' rootSet D d = rootSet D d
  rw [← CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass (r : G) d,
    c.conj_d_eq_of_mem_closure hr]

theorem SzCfg.szLineSet_eq (c : SzCfg G D d E e n) :
    szLineSet D d e = rootSet D d ∪ szComp E e := by
  ext x
  constructor
  · rintro ⟨hxD, hxd, hxe⟩
    rcases (c.commute_d_iff hxD).mp hxd with hroot | hE
    · exact Or.inl hroot
    · exact Or.inr ⟨hE, hxe⟩
  · rintro (hxroot | hxcomp)
    · obtain ⟨hxD, hxd, hxsub⟩ :=
        (CFSG.Timmesfeld.mem_rootSet_iff c.hyp.setup.isClass c.d_mem).mp hxroot
      exact ⟨hxD, hxd.symm,
        hxsub e (c.subset_commSet c.e_mem).1 ((c.subset_commSet c.e_mem).2.1).symm⟩
    · exact ⟨(c.subset_commSet hxcomp.1).1, (c.subset_commSet hxcomp.1).2.1, hxcomp.2⟩

private theorem mem_normalizer_szLineSet_of_swap (c : SzCfg G D d E e n) {g : G}
    (hgd : g * d * g⁻¹ = e) (hge : g * e * g⁻¹ = d) :
    g ∈ Subgroup.normalizer (szLineSet D d e) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxD, hxd, hxe⟩
    refine ⟨c.hyp.setup.conj_mem g hxD, ?_, ?_⟩
    · have h := (Commute.conj_iff g).mpr hxe
      rwa [hge] at h
    · have h := (Commute.conj_iff g).mpr hxd
      rwa [hgd] at h
  · rintro ⟨hxD, hxd, hxe⟩
    refine ⟨?_, ?_, ?_⟩
    · have h := c.hyp.setup.conj_mem g⁻¹ hxD
      simpa [mul_assoc] using h
    · have h := (Commute.conj_iff g⁻¹).mpr hxe
      have hge' : g⁻¹ * e * (g⁻¹)⁻¹ = d := by rw [inv_inv, ← hgd]; group
      rw [hge'] at h
      simpa [mul_assoc] using h
    · have h := (Commute.conj_iff g⁻¹).mpr hxd
      have hgd' : g⁻¹ * d * (g⁻¹)⁻¹ = e := by rw [inv_inv, ← hge]; group
      rw [hgd'] at h
      simpa [mul_assoc] using h

private theorem exists_swap_szLineStab (c : SzCfg G D d E e n) :
    ∃ w : ↥(szLineStab D d e),
      szLineHom D d e w (szLinePt D d e d c.d_mem_szLineSet) =
        szLinePt D d e e c.e_mem_szLineSet := by
  obtain ⟨k, hk⟩ := isConj_iff.mp (c.hyp.setup.isConj c.d_mem (c.subset_commSet c.e_mem).1)
  have hke : k⁻¹ * e * k = d := by rw [← hk]; group
  have hkd : k⁻¹ * d * k ∈ E := by
    have hD : k⁻¹ * d * k ∈ D := by
      simpa [mul_assoc] using c.hyp.setup.conj_mem k⁻¹ c.d_mem
    have hcomm : Commute (k⁻¹ * d * k) d := by
      have hde : Commute d e := ((c.subset_commSet c.e_mem).2.1).symm
      have h := (Commute.conj_iff k⁻¹).mpr hde
      simp only [inv_inv] at h
      rwa [hke] at h
    rcases (c.commute_d_iff hD).mp hcomm with hroot | hE
    · exfalso
      have himage : rootSet D e = (fun x => k * x * k⁻¹) '' rootSet D d := by
        rw [← hk]
        exact CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass k d
      have hdmem : d ∈ (fun x => k * x * k⁻¹) '' rootSet D d := by
        exact ⟨k⁻¹ * d * k, hroot, by group⟩
      rw [← himage] at hdmem
      exact c.d_not_mem (c.rootSet_subset_of_mem c.e_mem hdmem)
    · exact hE
  obtain ⟨h0, hh0H, hh0⟩ := c.exists_conj c.e_mem hkd
  have hh0d : h0 * d * h0⁻¹ = d := c.conj_d_eq_of_mem_closure hh0H
  have hhe : (k * h0 * k⁻¹) * e * (k * h0 * k⁻¹)⁻¹ = e := by
    calc
      (k * h0 * k⁻¹) * e * (k * h0 * k⁻¹)⁻¹
          = k * h0 * (k⁻¹ * e * k) * h0⁻¹ * k⁻¹ := by group
      _ = k * (h0 * d * h0⁻¹) * k⁻¹ := by rw [hke]; group
      _ = k * d * k⁻¹ := by rw [hh0d]
      _ = e := hk
  have hhed : (k * h0 * k⁻¹) * (k * e * k⁻¹) * (k * h0 * k⁻¹)⁻¹ = d := by
    calc
      (k * h0 * k⁻¹) * (k * e * k⁻¹) * (k * h0 * k⁻¹)⁻¹
          = k * (h0 * e * h0⁻¹) * k⁻¹ := by group
      _ = k * (k⁻¹ * d * k) * k⁻¹ := by rw [hh0]
      _ = d := by group
  let g' : G := (k * h0 * k⁻¹) * k
  have hgd : g' * d * g'⁻¹ = e := by
    dsimp [g']
    calc
      ((k * h0 * k⁻¹) * k) * d * ((k * h0 * k⁻¹) * k)⁻¹
          = (k * h0 * k⁻¹) * (k * d * k⁻¹) * (k * h0 * k⁻¹)⁻¹ := by group
      _ = (k * h0 * k⁻¹) * e * (k * h0 * k⁻¹)⁻¹ := by rw [hk]
      _ = e := hhe
  have hge : g' * e * g'⁻¹ = d := by
    dsimp [g']
    calc
      ((k * h0 * k⁻¹) * k) * e * ((k * h0 * k⁻¹) * k)⁻¹
          = (k * h0 * k⁻¹) * (k * e * k⁻¹) * (k * h0 * k⁻¹)⁻¹ := by group
      _ = d := hhed
  let w : ↥(szLineStab D d e) :=
    ⟨g', mem_normalizer_szLineSet_of_swap c hgd hge, mem_normalizer_D c g'⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  rw [szLineHom_apply]
  change (fun x => (w : G) * x * (w : G)⁻¹) '' rootSet D d = rootSet D e
  rw [← CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass (w : G) d, hgd]

theorem SzCfg.szQ_le_szLineStab (c : SzCfg G D d E e n) : szQ E ≤ szLineStab D d e := by
  obtain ⟨P, hP⟩ := c.exists_szS c.e_mem
  intro q hq
  have hqH : q ∈ Subgroup.closure E := szQ_le_closure E hq
  have hqd : q * d * q⁻¹ = d := c.conj_d_eq_of_mem_closure hqH
  have himage_root : (fun x => q * x * q⁻¹) '' rootSet D d = rootSet D d := by
    rw [← CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass q d, hqd]
  have himage_comp : (fun x => q * x * q⁻¹) '' szComp E e = szComp E e := by
    have hqS : q ∈ szS E P := szQ_le_szS E P hq
    ext y
    constructor
    · rintro ⟨a, ⟨haE, hae⟩, rfl⟩
      have haS : a ∈ szS E P :=
        (c.mem_szS_iff_commute P c.e_mem haE hP).mpr hae
      have hconjS : q * a * q⁻¹ ∈ szS E P :=
        (szS E P).mul_mem ((szS E P).mul_mem hqS haS) ((szS E P).inv_mem hqS)
      have hconjE : q * a * q⁻¹ ∈ E := c.conj_mem hqH haE
      exact ⟨hconjE, (c.mem_szS_iff_commute P c.e_mem hconjE hP).mp hconjS⟩
    · rintro ⟨hyE, hye⟩
      have hyS : y ∈ szS E P :=
        (c.mem_szS_iff_commute P c.e_mem hyE hP).mpr hye
      have hqinvS : q⁻¹ ∈ szS E P := (szS E P).inv_mem hqS
      have hconjS : q⁻¹ * y * (q⁻¹)⁻¹ ∈ szS E P :=
        (szS E P).mul_mem ((szS E P).mul_mem hqinvS hyS) ((szS E P).inv_mem hqinvS)
      have hconjE : q⁻¹ * y * (q⁻¹)⁻¹ ∈ E :=
        c.conj_mem (Subgroup.inv_mem _ hqH) hyE
      refine ⟨q⁻¹ * y * (q⁻¹)⁻¹,
        ⟨hconjE, (c.mem_szS_iff_commute P c.e_mem hconjE hP).mp hconjS⟩, ?_⟩
      group
  have himage : (fun x => q * x * q⁻¹) '' szLineSet D d e = szLineSet D d e := by
    rw [c.szLineSet_eq, Set.image_union, himage_root, himage_comp]
  refine ⟨Subgroup.mem_normalizer_iff_conj_image_eq.mpr ?_, mem_normalizer_D c q⟩
  have hfun : (⇑(MulAut.conj q) : G → G) = fun x => q * x * q⁻¹ :=
    funext (MulAut.conj_apply q)
  rw [hfun]
  exact himage

theorem SzCfg.szN_le_szLineStab (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) : szN E P ≤ szLineStab D d e := by
  intro r hr
  have hrH : r ∈ Subgroup.closure E := szN_le_closure E P hr
  have hrd : r * d * r⁻¹ = d := c.conj_d_eq_of_mem_closure hrH
  have himage_root : (fun x => r * x * r⁻¹) '' rootSet D d = rootSet D d := by
    rw [← CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass r d, hrd]
  have himage_comp : (fun x => r * x * r⁻¹) '' szComp E e = szComp E e := by
    ext y
    constructor
    · rintro ⟨a, ⟨haE, hae⟩, rfl⟩
      have haS : a ∈ szS E P :=
        (c.mem_szS_iff_commute P c.e_mem haE hP).mpr hae
      have hconjS : r * a * r⁻¹ ∈ szS E P := conj_mem_szS hr haS
      have hconjE : r * a * r⁻¹ ∈ E := c.conj_mem hrH haE
      exact ⟨hconjE, (c.mem_szS_iff_commute P c.e_mem hconjE hP).mp hconjS⟩
    · rintro ⟨hyE, hye⟩
      have hyS : y ∈ szS E P :=
        (c.mem_szS_iff_commute P c.e_mem hyE hP).mpr hye
      have hrinv : r⁻¹ ∈ szN E P := (szN E P).inv_mem hr
      have hconjS : r⁻¹ * y * (r⁻¹)⁻¹ ∈ szS E P := conj_mem_szS hrinv hyS
      have hconjE : r⁻¹ * y * (r⁻¹)⁻¹ ∈ E :=
        c.conj_mem (szN_le_closure E P hrinv) hyE
      refine ⟨r⁻¹ * y * (r⁻¹)⁻¹,
        ⟨hconjE, (c.mem_szS_iff_commute P c.e_mem hconjE hP).mp hconjS⟩, ?_⟩
      group
  have himage : (fun x => r * x * r⁻¹) '' szLineSet D d e = szLineSet D d e := by
    rw [c.szLineSet_eq, Set.image_union, himage_root, himage_comp]
  refine ⟨Subgroup.mem_normalizer_iff_conj_image_eq.mpr ?_, mem_normalizer_D c r⟩
  have hfun : (⇑(MulAut.conj r) : G → G) = fun x => r * x * r⁻¹ :=
    funext (MulAut.conj_apply r)
  rw [hfun]
  exact himage

theorem SzCfg.szN_trans (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P)
    {β γ : ↥(szLine D d e)} (hβ : β ≠ szLinePt D d e d c.d_mem_szLineSet)
    (hγ : γ ≠ szLinePt D d e d c.d_mem_szLineSet) :
    ∃ h : ↥(szN E P), szLineHom D d e (Subgroup.inclusion (c.szN_le_szLineStab P hP) h) β = γ := by
  obtain ⟨a, ha, hβeq⟩ := exists_szLinePt β
  obtain ⟨b, hb, hγeq⟩ := exists_szLinePt γ
  have haComp : a ∈ szComp E e := by
    rw [c.szLineSet_eq] at ha
    rcases ha with hroot | hcomp
    · exfalso
      apply hβ
      rw [hβeq]
      exact (szLinePt_eq_iff _ c.d_mem_szLineSet).mpr (rootSet_eq_of_mem hroot)
    · exact hcomp
  have hbComp : b ∈ szComp E e := by
    rw [c.szLineSet_eq] at hb
    rcases hb with hroot | hcomp
    · exfalso
      apply hγ
      rw [hγeq]
      exact (szLinePt_eq_iff _ c.d_mem_szLineSet).mpr (rootSet_eq_of_mem hroot)
    · exact hcomp
  have haS : a ∈ szS E P := (c.mem_szS_iff_commute P c.e_mem haComp.1 hP).mpr haComp.2
  have hbS : b ∈ szS E P := (c.mem_szS_iff_commute P c.e_mem hbComp.1 hP).mpr hbComp.2
  obtain ⟨h, hhN, hconj⟩ := c.exists_szN_conj P haComp.1 hbComp.1 haS hbS
  refine ⟨⟨h, hhN⟩, ?_⟩
  rw [hβeq, hγeq]
  apply Subtype.ext
  rw [szLineHom_apply]
  simp only [Subgroup.coe_inclusion]
  change (fun x => h * x * h⁻¹) '' rootSet D a = rootSet D b
  rw [← CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass h a, hconj]

private theorem szLineHom_conj_apply (r s : ↥(szLineStab D d e)) (X : ↥(szLine D d e)) :
    szLineHom D d e (r * s * r⁻¹) X =
      szLineHom D d e r (szLineHom D d e s (szLineHom D d e r⁻¹ X)) := by
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

private theorem szLineHom_inv_apply (r : ↥(szLineStab D d e)) (X : ↥(szLine D d e)) :
    szLineHom D d e r⁻¹ (szLineHom D d e r X) = X := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem szLineHom_apply_inv_apply (r : ↥(szLineStab D d e)) (X : ↥(szLine D d e)) :
    szLineHom D d e r (szLineHom D d e r⁻¹ X) = X := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

private theorem szLineStab_trans (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P)
    (β γ : ↥(szLine D d e)) :
    ∃ r : ↥(szLineStab D d e), szLineHom D d e r β = γ := by
  let α := szLinePt D d e d c.d_mem_szLineSet
  let η := szLinePt D d e e c.e_mem_szLineSet
  obtain ⟨w, hw⟩ := exists_swap_szLineStab c
  have hηne : η ≠ α := by
    intro h
    have hroot : rootSet D e = rootSet D d :=
      (szLinePt_eq_iff c.e_mem_szLineSet c.d_mem_szLineSet).mp h
    have heroot : e ∈ rootSet D d := hroot ▸ mem_rootSet_self (c.subset_commSet c.e_mem).1
    exact (Set.disjoint_left.mp c.disjoint) heroot c.e_mem
  by_cases hβ : β = α
  · subst β
    by_cases hγ : γ = α
    · subst γ
      exact ⟨1, by rw [map_one]; rfl⟩
    · obtain ⟨h, hh⟩ := c.szN_trans P hP hηne hγ
      let nincl : ↥(szLineStab D d e) := Subgroup.inclusion (c.szN_le_szLineStab P hP) h
      have hnη : szLineHom D d e nincl η = γ := hh
      refine ⟨nincl * w, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, hw, hnη]
  · by_cases hγ : γ = α
    · subst γ
      obtain ⟨h, hh⟩ := c.szN_trans P hP hβ hηne
      let nincl : ↥(szLineStab D d e) := Subgroup.inclusion (c.szN_le_szLineStab P hP) h
      have hβη : szLineHom D d e nincl β = η := hh
      have hwinv : szLineHom D d e w⁻¹ η = α := by
        apply (szLineHom D d e w).injective
        rw [szLineHom_apply_inv_apply, hw]
      refine ⟨w⁻¹ * nincl, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, hβη, hwinv]
    · obtain ⟨h, hh⟩ := c.szN_trans P hP hβ hγ
      exact ⟨Subgroup.inclusion (c.szN_le_szLineStab P hP) h, hh⟩

theorem SzCfg.szLineHom_two_trans (c : SzCfg G D d E e n) {β γ β' γ' : ↥(szLine D d e)}
    (h : β ≠ γ) (h' : β' ≠ γ') :
    ∃ r : ↥(szLineStab D d e), szLineHom D d e r β = β' ∧ szLineHom D d e r γ = γ' := by
  obtain ⟨P, hP⟩ := c.exists_szS c.e_mem
  let α := szLinePt D d e d c.d_mem_szLineSet
  obtain ⟨r, hr⟩ := szLineStab_trans c P hP β β'
  have hne : szLineHom D d e r γ ≠ β' := by
    intro hconj
    have hγβ : γ = β := by
      apply (szLineHom D d e r).injective
      rw [hconj, hr]
    exact h hγβ.symm
  have hne' : γ' ≠ β' := fun hEq => h' hEq.symm
  obtain ⟨rα, hrα⟩ := szLineStab_trans c P hP α β'
  have hβn : szLineHom D d e rα⁻¹ (szLineHom D d e r γ) ≠ α := by
    intro hcon
    apply hne
    have h1 : szLineHom D d e rα (szLineHom D d e rα⁻¹ (szLineHom D d e r γ)) =
        szLineHom D d e r γ := szLineHom_apply_inv_apply rα (szLineHom D d e r γ)
    rw [hcon, hrα] at h1
    exact h1.symm
  have hγn : szLineHom D d e rα⁻¹ γ' ≠ α := by
    intro hcon
    apply hne'
    have h1 : szLineHom D d e rα (szLineHom D d e rα⁻¹ γ') = γ' :=
      szLineHom_apply_inv_apply rα γ'
    rw [hcon, hrα] at h1
    exact h1.symm
  obtain ⟨n, hn⟩ := c.szN_trans P hP hβn hγn
  let nincl : ↥(szLineStab D d e) := Subgroup.inclusion (c.szN_le_szLineStab P hP) n
  have hninclα : szLineHom D d e nincl α = α :=
    c.szLineHom_fix_of_mem_closure (szN_le_closure E P n.2)
  let s : ↥(szLineStab D d e) := rα * nincl * rα⁻¹
  have hs_fix : szLineHom D d e s β' = β' := by
    rw [show β' = szLineHom D d e rα α from hrα.symm]
    dsimp [s]
    rw [szLineHom_conj_apply, szLineHom_inv_apply, hninclα]
  have hs_move : szLineHom D d e s (szLineHom D d e r γ) = γ' := by
    dsimp [s]
    rw [szLineHom_conj_apply, hn, szLineHom_apply_inv_apply]
  refine ⟨s * r, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, hr, hs_fix]
  · rw [map_mul, Equiv.Perm.mul_apply, hs_move]

theorem SzCfg.conj_mem_szQ_of_fix (c : SzCfg G D d E e n) {r : ↥(szLineStab D d e)}
    (hr : szLineHom D d e r (szLinePt D d e d c.d_mem_szLineSet) =
      szLinePt D d e d c.d_mem_szLineSet)
    {y : G} (hy : y ∈ szQ E) : (r : G) * y * (r : G)⁻¹ ∈ szQ E := by
  have himage_root : (fun x => (r : G) * x * (r : G)⁻¹) '' rootSet D d = rootSet D d := by
    have h := congrArg (fun X : ↥(szLine D d e) => (X : Set G)) hr
    rw [szLineHom_apply] at h
    simpa [szLinePt] using h
  have hrdD : (r : G) * d * (r : G)⁻¹ ∈ D := c.hyp.setup.conj_mem (r : G) c.d_mem
  have hrd_root : (r : G) * d * (r : G)⁻¹ ∈ rootSet D d := by
    have h1 : rootSet D ((r : G) * d * (r : G)⁻¹) =
        (fun x => (r : G) * x * (r : G)⁻¹) '' rootSet D d :=
      CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass (r : G) d
    rw [himage_root] at h1
    rw [← h1]
    exact mem_rootSet_self hrdD
  have hcen : ∀ x : G, x ∈ D →
      (Commute x ((r : G) * d * (r : G)⁻¹) ↔ Commute x d) := by
    intro x hx
    have h := hrd_root.2 x hx
    constructor
    · intro hxc
      exact (h.mp hxc.symm).symm
    · intro hxd
      exact (h.mpr hxd.symm).symm
  have hCD : ∀ x : G, x ∈ D → Commute x d →
      (r : G) * x * (r : G)⁻¹ ∈ D ∧ Commute ((r : G) * x * (r : G)⁻¹) d := by
    intro x hxD hxd
    refine ⟨c.hyp.setup.conj_mem (r : G) hxD, ?_⟩
    have hconj : Commute ((r : G) * x * (r : G)⁻¹) ((r : G) * d * (r : G)⁻¹) :=
      (Commute.conj_iff (r : G)).mpr hxd
    exact (hcen ((r : G) * x * (r : G)⁻¹) (c.hyp.setup.conj_mem (r : G) hxD)).mp hconj
  have hCD_eq : {x : G | x ∈ D ∧ Commute x d} = rootSet D d ∪ E := by
    ext x
    constructor
    · intro hx
      exact (c.commute_d_iff hx.1).mp hx.2
    · rintro (hroot | hE)
      · exact ⟨hroot.1,
          ((CFSG.Timmesfeld.mem_rootSet_iff c.hyp.setup.isClass c.d_mem).mp hroot).2.1.symm⟩
      · exact ⟨(c.subset_commSet hE).1, (c.subset_commSet hE).2.1⟩
  have himageCD : (fun x => (r : G) * x * (r : G)⁻¹) '' {x : G | x ∈ D ∧ Commute x d} =
      {x : G | x ∈ D ∧ Commute x d} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hCD x hx.1 hx.2
    · intro hz
      refine ⟨(r : G)⁻¹ * z * (r : G), ⟨?_, ?_⟩, by group⟩
      · have h := c.hyp.setup.conj_mem (r : G)⁻¹ hz.1
        simpa [mul_assoc] using h
      · have hzr : Commute z ((r : G) * d * (r : G)⁻¹) := (hcen z hz.1).mpr hz.2
        have h := (Commute.conj_iff (r : G)⁻¹).mpr hzr
        simpa [mul_assoc] using h
  have hEeq : E = {x : G | x ∈ D ∧ Commute x d} \ rootSet D d := by
    rw [hCD_eq]
    ext x
    constructor
    · intro hxE
      exact ⟨Or.inr hxE, fun hxroot => (Set.disjoint_left.mp c.disjoint) hxroot hxE⟩
    · rintro ⟨hx | hx, hxnot⟩
      · exact absurd hx hxnot
      · exact hx
  have himageE : (fun x => (r : G) * x * (r : G)⁻¹) '' E = E := by
    rw [hEeq, Set.image_diff (fun x y hxy => by simpa [mul_assoc] using hxy),
      himageCD, himage_root]
  exact conj_mem_szQ himageE hy

end CFSG.Timmesfeld.Bridge.OddRoot
