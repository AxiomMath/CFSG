module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainLine
import CFSG.Timmesfeld.Bridge.OddRootOrbit
import CFSG.Timmesfeld.Bridge.OddRootSzMainCoset
import CFSG.Timmesfeld.Bridge.OddRootSzMainNotCentral
import CFSG.Timmesfeld.Bridge.OddRootSzMainQ

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

@[expose] def szLineT (D : Set G) (d e : G) (E : Set G) :
    Subgroup (Equiv.Perm ↥(szLine D d e)) :=
  ((szQ E).subgroupOf (szLineStab D d e)).map (szLineHom D d e)

@[expose] def szLineS (D : Set G) (d e : G) (E : Set G) (P : Sylow 2 (SzBar E)) :
    Subgroup (Equiv.Perm ↥(szLine D d e)) :=
  ((szS E P).subgroupOf (szLineStab D d e)).map (szLineHom D d e)

theorem SzCfg.szLineT_fix (c : SzCfg G D d E e n) :
    ∀ t ∈ szLineT D d e E, t (szLinePt D d e d c.d_mem_szLineSet) =
      szLinePt D d e d c.d_mem_szLineSet := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := Subgroup.mem_map.mp ht
  rw [← hrt]
  have hrQ : ((r : ↥(szLineStab D d e)) : G) ∈ szQ E := Subgroup.mem_subgroupOf.mp hr
  exact c.szLineHom_fix_of_mem_closure (szQ_le_closure E hrQ)

theorem SzCfg.szLineS_fix (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E)) :
    ∀ t ∈ szLineS D d e E P, t (szLinePt D d e d c.d_mem_szLineSet) =
      szLinePt D d e d c.d_mem_szLineSet := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := Subgroup.mem_map.mp ht
  rw [← hrt]
  have hrS : ((r : ↥(szLineStab D d e)) : G) ∈ szS E P := Subgroup.mem_subgroupOf.mp hr
  exact c.szLineHom_fix_of_mem_closure (szN_le_closure E P (szS_le_szN E P hrS))

private theorem szLineHom_eq_one_of_mem_szZ (c : SzCfg G D d E e n)
    {r : ↥(szLineStab D d e)} (hr : (r : G) ∈ szZ E) :
    szLineHom D d e r = 1 := by
  apply Equiv.ext
  intro X
  rw [Equiv.Perm.one_apply]
  obtain ⟨a, ha, hXa⟩ := exists_szLinePt X
  rw [hXa, szLineHom_szLinePt, szLinePt_eq_iff]
  rw [c.szLineSet_eq] at ha
  rcases ha with hroot | hcomp
  · have hroot' : rootSet D a = rootSet D d := rootSet_eq_of_mem hroot
    have hrd : (r : G) * d * (r : G)⁻¹ = d := c.conj_d_eq_of_mem_closure (szQ_le_closure E hr.1)
    rw [CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass (r : G) a, hroot']
    rw [← CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass (r : G) d, hrd]
  · have hcomm : Commute (r : G) a := by
      have h := Subgroup.mem_centralizer_iff.mp hr.2 a hcomp.1
      exact h.symm
    have hconj : (r : G) * a * (r : G)⁻¹ = a := by
      rw [show (r : G) * a = a * (r : G) from hcomm]
      group
    rw [hconj]

private theorem szLineT_commute (c : SzCfg G D d E e n)
    {x y : Equiv.Perm ↥(szLine D d e)}
    (hx : x ∈ szLineT D d e E) (hy : y ∈ szLineT D d e E) : x * y = y * x := by
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, hyb⟩ := Subgroup.mem_map.mp hy
  let A : ↥(szLineStab D d e) := a
  let B : ↥(szLineStab D d e) := b
  have hAQ : (A : G) ∈ szQ E := Subgroup.mem_subgroupOf.mp ha
  have hBQ : (B : G) ∈ szQ E := Subgroup.mem_subgroupOf.mp hb
  rw [← hxa, ← hyb]
  change szLineHom D d e A * szLineHom D d e B =
    szLineHom D d e B * szLineHom D d e A
  have hcomm : (A : G) * (B : G) * (A : G)⁻¹ * (B : G)⁻¹ ∈ szZ E :=
    c.commutator_mem_szZ hAQ hBQ
  have hker : szLineHom D d e (A * B * A⁻¹ * B⁻¹) = 1 :=
    szLineHom_eq_one_of_mem_szZ c (by simpa using hcomm)
  have hxy : szLineHom D d e A * szLineHom D d e B *
      (szLineHom D d e A)⁻¹ * (szLineHom D d e B)⁻¹ = 1 := by
    rw [← hker]
    simp
  calc szLineHom D d e A * szLineHom D d e B
      = (szLineHom D d e A * szLineHom D d e B * (szLineHom D d e A)⁻¹ *
          (szLineHom D d e B)⁻¹) * (szLineHom D d e B * szLineHom D d e A) := by group
    _ = szLineHom D d e B * szLineHom D d e A := by rw [hxy, one_mul]

private theorem szLineT_mul_self (c : SzCfg G D d E e n)
    {x : Equiv.Perm ↥(szLine D d e)} (hx : x ∈ szLineT D d e E) : x * x = 1 := by
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.mp hx
  let A : ↥(szLineStab D d e) := a
  have hAQ : (A : G) ∈ szQ E := Subgroup.mem_subgroupOf.mp ha
  have hsq : (A : G) * (A : G) ∈ szZ E := c.mul_self_mem_szZ hAQ
  have hker : szLineHom D d e (A * A) = 1 :=
    szLineHom_eq_one_of_mem_szZ c (by simpa using hsq)
  rw [← hxa]
  change szLineHom D d e A * szLineHom D d e A = 1
  rw [← map_mul]
  exact hker

theorem SzCfg.szLineT_normal (c : SzCfg G D d E e n) :
    ∀ x ∈ (szLineHom D d e).range, x (szLinePt D d e d c.d_mem_szLineSet) =
      szLinePt D d e d c.d_mem_szLineSet →
      ∀ t ∈ szLineT D d e E, x * t * x⁻¹ ∈ szLineT D d e E := by
  intro x hx hxfix t ht
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp ht
  rw [← hr] at hxfix ⊢
  rw [← hqt]
  have hqQ : ((q : ↥(szLineStab D d e)) : G) ∈ szQ E := Subgroup.mem_subgroupOf.mp hq
  have hconjQ : (r : G) * ((q : ↥(szLineStab D d e)) : G) * (r : G)⁻¹ ∈ szQ E :=
    c.conj_mem_szQ_of_fix hxfix hqQ
  refine Subgroup.mem_map.mpr ⟨r * (q : ↥(szLineStab D d e)) * r⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    simpa using hconjQ
  · simp

theorem SzCfg.szLineT_isElemAbelian (c : SzCfg G D d E e n) :
    CFSG.Open.IsElemAbelian 2 (szLineT D d e E) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    exact Subtype.ext (szLineT_commute c x.2 y.2)
  · intro x hx
    rw [pow_two]
    exact szLineT_mul_self c hx

theorem SzCfg.szLineS_orbit (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) {s : G} (hs : s ∈ szS E P) (β : ↥(szLine D d e)) :
    ∃ (y : G) (hy : y ∈ szQ E),
      szLineHom D d e ⟨s, c.szN_le_szLineStab P hP (szS_le_szN E P hs)⟩ β =
        szLineHom D d e ⟨y, c.szQ_le_szLineStab hy⟩ β := by
  obtain ⟨a, ha, hβ⟩ := exists_szLinePt β
  have hsH : s ∈ Subgroup.closure E := szN_le_closure E P (szS_le_szN E P hs)
  have haU : a ∈ rootSet D d ∪ szComp E e := by
    rw [← c.szLineSet_eq]
    exact ha
  rcases haU with hroot | hcomp
  · refine ⟨1, (szQ E).one_mem, ?_⟩
    have hpt : szLinePt D d e a ha = szLinePt D d e d c.d_mem_szLineSet :=
      (szLinePt_eq_iff ha c.d_mem_szLineSet).mpr (rootSet_eq_of_mem hroot)
    rw [hβ, hpt]
    have hone : (⟨(1 : G), c.szQ_le_szLineStab (szQ E).one_mem⟩ :
        ↥(szLineStab D d e)) = 1 := Subtype.ext rfl
    rw [hone, map_one, Equiv.Perm.one_apply]
    exact c.szLineHom_fix_of_mem_closure hsH
  · have haE : a ∈ E := hcomp.1
    have haP : a ∈ szS E P :=
      (c.mem_szS_iff_commute P c.e_mem haE hP).mpr hcomp.2
    have hbE : s * a * s⁻¹ ∈ E := c.conj_mem hsH haE
    have hq : a⁻¹ * (s * a * s⁻¹) ∈ szQ E := c.inv_mul_conj_mem_szQ P haE haP hs
    obtain ⟨y, hyQ, hyconj⟩ := c.exists_conj_of_inv_mul_mem haE hbE hq
    refine ⟨y, hyQ, ?_⟩
    rw [hβ]
    rw [szLineHom_szLinePt (r := ⟨s, c.szN_le_szLineStab P hP (szS_le_szN E P hs)⟩) ha]
    rw [szLineHom_szLinePt (r := ⟨y, c.szQ_le_szLineStab hyQ⟩) ha]
    apply Subtype.ext
    change rootSet D (s * a * s⁻¹) = rootSet D (y * a * y⁻¹)
    rw [hyconj]

theorem SzCfg.szLineHom_eq_one_iff (c : SzCfg G D d E e n) {y : G} (hy : y ∈ szQ E) :
    szLineHom D d e ⟨y, c.szQ_le_szLineStab hy⟩ = 1 ↔ Commute y e := by
  obtain ⟨P, heP⟩ := c.exists_szS c.e_mem
  have hyS : y ∈ szS E P := szQ_le_szS E P hy
  constructor
  · intro h1
    have hfix : szLineHom D d e ⟨y, c.szQ_le_szLineStab hy⟩
        (szLinePt D d e e c.e_mem_szLineSet) = szLinePt D d e e c.e_mem_szLineSet := by
      rw [h1, Equiv.Perm.one_apply]
    have himg : (fun x => y * x * y⁻¹) '' rootSet D e = rootSet D e := by
      have h := congrArg (fun X : ↥(szLine D d e) => (X : Set G)) hfix
      simpa [szLinePt, szLineHom_apply] using h
    have heD : e ∈ D := (c.subset_commSet c.e_mem).1
    have hroot : y * e * y⁻¹ ∈ rootSet D e := by
      rw [← himg]
      exact ⟨e, mem_rootSet_self heD, rfl⟩
    have heq : y * e * y⁻¹ = e :=
      c.eq_of_mem_rootSet c.e_mem hroot (c.inv_mul_conj_mem_szQ P c.e_mem heP hyS)
    show y * e = e * y
    calc y * e = (y * e * y⁻¹) * y := by group
      _ = e * y := by rw [heq]
  · intro hcomm
    apply Equiv.ext
    intro X
    rw [Equiv.Perm.one_apply]
    obtain ⟨a, ha, hXa⟩ := exists_szLinePt X
    rw [hXa]
    have haU : a ∈ rootSet D d ∪ szComp E e := by
      rw [← c.szLineSet_eq]
      exact ha
    rcases haU with hroot | hcomp
    · have hroot' : rootSet D a = rootSet D d := rootSet_eq_of_mem hroot
      have hyd : y * d * y⁻¹ = d := c.conj_d_eq_of_mem_closure (szQ_le_closure E hy)
      rw [szLineHom_szLinePt]
      apply Subtype.ext
      change rootSet D (y * a * y⁻¹) = rootSet D a
      rw [CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass y a, hroot']
      rw [← CFSG.Timmesfeld.rootSet_conj c.hyp.setup.isClass y d, hyd]
    · have hya : Commute y a :=
        (c.commute_iff_of_mem_comp c.e_mem hcomp hy).mp hcomm
      have hconj : y * a * y⁻¹ = a := by
        rw [show y * a = a * y from hya]
        group
      rw [szLineHom_szLinePt]
      apply Subtype.ext
      change rootSet D (y * a * y⁻¹) = rootSet D a
      rw [hconj]

theorem SzCfg.szLineT_semireg (c : SzCfg G D d E e n) :
    ∀ t ∈ szLineT D d e E, ∀ β : ↥(szLine D d e),
      β ≠ szLinePt D d e d c.d_mem_szLineSet → t β = β → t = 1 := by
  intro t ht β hβ hfix
  obtain ⟨r, hr, hrt⟩ := Subgroup.mem_map.mp ht
  rw [← hrt] at hfix ⊢
  have hrQ : ((r : ↥(szLineStab D d e)) : G) ∈ szQ E := Subgroup.mem_subgroupOf.mp hr
  obtain ⟨a, ha, hβa⟩ := exists_szLinePt β
  rw [hβa] at hβ hfix
  have haU : a ∈ rootSet D d ∪ szComp E e := by
    rw [← c.szLineSet_eq]
    exact ha
  have haComp : a ∈ szComp E e := by
    rcases haU with hroot | hcomp
    · exact absurd ((szLinePt_eq_iff ha c.d_mem_szLineSet).mpr (rootSet_eq_of_mem hroot)) hβ
    · exact hcomp
  have hpt : szLinePt D d e ((r : G) * a * (r : G)⁻¹) (conj_mem_szLineSet r ha) =
      szLinePt D d e a ha := by
    simpa only [szLineHom_szLinePt] using hfix
  have hroot : (r : G) * a * (r : G)⁻¹ ∈ rootSet D a := by
    have hbD : (r : G) * a * (r : G)⁻¹ ∈ D :=
      c.hyp.setup.conj_mem (r : G) (c.subset_commSet haComp.1).1
    have heq : rootSet D ((r : G) * a * (r : G)⁻¹) = rootSet D a :=
      (szLinePt_eq_iff _ ha).mp hpt
    exact heq ▸ mem_rootSet_self hbD
  obtain ⟨P, haP⟩ := c.exists_szS haComp.1
  have hrS : (r : G) ∈ szS E P := szQ_le_szS E P hrQ
  have heqa : (r : G) * a * (r : G)⁻¹ = a :=
    c.eq_of_mem_rootSet haComp.1 hroot (c.inv_mul_conj_mem_szQ P haComp.1 haP hrS)
  have hcomm : Commute (r : G) a := by
    show (r : G) * a = a * (r : G)
    calc (r : G) * a = ((r : G) * a * (r : G)⁻¹) * (r : G) := by group
      _ = a * (r : G) := by rw [heqa]
  have hcommE : Commute (r : G) e :=
    (c.commute_iff_of_mem_comp c.e_mem haComp hrQ).mpr hcomm
  exact (c.szLineHom_eq_one_iff hrQ).mpr hcommE

theorem SzCfg.exists_commute_not_mem_szZ (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    ∃ y ∈ szQ E, Commute y a ∧ y ∉ szZ E := by
  by_contra h
  push Not at h
  have hconjZ : ∀ y ∈ szQ E, ∀ b ∈ E, Commute y b → y ∈ szZ E := by
    intro y hy b hbE hyb
    obtain ⟨k, hkH, hkb⟩ := c.exists_conj hbE ha
    have himg : (fun z => k * z * k⁻¹) '' E = E :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp
        (closure_le_normalizer_of_isMaxOrbit c.hyp.setup c.maxOrbit hkH)
    have hkyQ : k * y * k⁻¹ ∈ szQ E := conj_mem_szQ himg hy
    have hkya : Commute (k * y * k⁻¹) a := by
      have hc := (Commute.conj_iff k).mpr hyb
      rwa [hkb] at hc
    have hz : k * y * k⁻¹ ∈ szZ E := h (k * y * k⁻¹) hkyQ hkya
    have hyEq : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [← hyEq]
    simpa using c.conj_mem_szZ (Subgroup.inv_mem _ hkH) hz
  obtain ⟨b, hbE, hbna⟩ := c.exists_not_commute ha
  have hba : ¬ Commute a b := fun hc => hbna hc.symm
  have hQZ : szQ E ≤ szZ E := by
    intro y hy
    obtain ⟨y1, hy1Q, hy1a, y2, hy2Q, hyEq⟩ := c.exists_mul_eq ha hbE hba hy
    have hy1Z : y1 ∈ szZ E := h y1 hy1Q hy1a
    have hy2b : Commute y2 b :=
      (c.commute_of_mem_commutator hbE ⟨hbE, Commute.refl b⟩ hy2Q).symm
    have hy2Q' : y2 ∈ szQ E := commutator_szQ_le E (Subgroup.subset_closure hbE) hy2Q
    have hy2Z : y2 ∈ szZ E := hconjZ y2 hy2Q' b hbE hy2b
    rw [hyEq]
    exact (szZ E).mul_mem hy1Z hy2Z
  obtain ⟨y, hyQ, x, hxE, hyx⟩ := c.exists_not_commute_szQ
  exact hyx (Subgroup.mem_centralizer_iff.mp (hQZ hyQ).2 x hxE).symm

end CFSG.Timmesfeld.Bridge.OddRoot
