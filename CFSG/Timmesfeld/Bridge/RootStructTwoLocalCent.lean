module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalPerfect
public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalIso

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace TwoLocalSetting

variable {G : Type*} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem exists_not_commute_three {d e₁ e₂ e₃ : G} (hd : d ∈ D)
    (he : ∀ e ∈ ({e₁, e₂, e₃} : Set G), e ∈ D ∧ Commute d e ∧ e ≠ d)
    (h4 : 4 ≤ (rootLines D d).ncard) :
    ∃ w ∈ D, Commute d w ∧ w ≠ d ∧ ¬ Commute w e₁ ∧ ¬ Commute w e₂ ∧ ¬ Commute w e₃ := by
  have := S.hyp.finite
  by_contra hno
  push Not at hno
  have hsub : rootLines D d ⊆ ((fun e => rootGroup D d ⊔ rootGroup D e) '' {e₁, e₂, e₃}) := by
    intro L hL
    obtain ⟨w, hw, hdw, hwd, rfl⟩ := (S.mem_rootLines_iff hd).1 hL
    have key : ∃ e ∈ ({e₁, e₂, e₃} : Set G), Commute w e := by
      by_cases h1 : Commute w e₁
      · exact ⟨e₁, by simp, h1⟩
      by_cases h2 : Commute w e₂
      · exact ⟨e₂, by simp, h2⟩
      exact ⟨e₃, by simp, hno w hw hdw hwd h1 h2⟩
    obtain ⟨e, heS, hwe⟩ := key
    obtain ⟨heD, hde, hed⟩ := he e heS
    refine ⟨e, heS, ?_⟩
    show rootGroup D d ⊔ rootGroup D e = rootGroup D d ⊔ rootGroup D w
    rcases (S.commute_iff_eq_or_eq_mul hd hw heD hdw hde hwd hed).1 hwe with h | h
    · rw [h]
    · rw [h, S.line_mul_eq hd hw (S.mul_mem_of_commute hd hw hdw (Ne.symm hwd))]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_image_le (f := fun e => rootGroup D d ⊔ rootGroup D e)
    (s := ({e₁, e₂, e₃} : Set G)) (Set.toFinite _)
  have h3 : ({e₁, e₂, e₃} : Set G).ncard ≤ 3 :=
    (Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
      (by rw [Set.ncard_singleton])))
  omega

end TwoLocalSetting

theorem TwoLocalSetting.exists_mem_lineGroup_conj_eq {G : Type} [Group G] {D : Set G}
    (S : TwoLocalSetting G D) {x y z : G} (hx : x ∈ D) (hy : y ∈ D) (hz : z ∈ D)
    (hxy : Commute x y) (hxz : Commute x z) (hyx : y ≠ x) (hzx : z ≠ x)
    (h5 : 5 ≤ (rootLines D x).ncard) : ∃ g ∈ lineGroup D x y, g * y * g⁻¹ = z := by
  have := S.hyp.finite
  have hL := S.lineSetting
  have hxyD : x * y ∈ D := S.mul_mem_of_commute hx hy hxy (Ne.symm hyx)
  have hyT : y ∉ rootSet D x := by
    rw [S.sing x hx]
    exact hyx
  obtain ⟨m, -, -, hMR, -, -, htr⟩ := rootLinesL2Step G D hL x hx y hy hxy hxyD hyT (by omega)
  have hLy : rootGroup D x ⊔ rootGroup D y ∈ rootLines D x :=
    (S.mem_rootLines_iff hx).2 ⟨y, hy, hxy, hyx, rfl⟩
  have hLz : rootGroup D x ⊔ rootGroup D z ∈ rootLines D x :=
    (S.mem_rootLines_iff hx).2 ⟨z, hz, hxz, hzx, rfl⟩
  have h3 : 3 ≤ (rootLines D x).ncard := by omega
  obtain ⟨L₂, hL₂, h₂, -⟩ := exists_mem_rootLines_ne_ne (L₁ := rootGroup D x ⊔ rootGroup D y)
    (L₂ := rootGroup D x ⊔ rootGroup D y) h3
  obtain ⟨L₃, hL₃, h₃, h₃₂⟩ := exists_mem_rootLines_ne_ne (L₁ := rootGroup D x ⊔ rootGroup D y)
    (L₂ := L₂) h3
  obtain ⟨L₂', hL₂', h₂', -⟩ := exists_mem_rootLines_ne_ne (L₁ := rootGroup D x ⊔ rootGroup D z)
    (L₂ := rootGroup D x ⊔ rootGroup D z) h3
  obtain ⟨L₃', hL₃', h₃', h₃₂'⟩ := exists_mem_rootLines_ne_ne
    (L₁ := rootGroup D x ⊔ rootGroup D z) (L₂ := L₂') h3
  obtain ⟨g, hg, hgL, -, -⟩ := htr _ hLy _ hL₂ _ hL₃ _ hLz _ hL₂' _ hL₃' (Ne.symm h₂) (Ne.symm h₃)
    (Ne.symm h₃₂) (Ne.symm h₂') (Ne.symm h₃') (Ne.symm h₃₂')
  have hgx : Commute g x :=
    Subgroup.mem_centralizer_singleton_iff.1 (lineGroup_le_centralizer D x y hg)
  have hmem : g * y * g⁻¹ ∈ rootGroup D x ⊔ rootGroup D z := by
    rw [← hgL]
    exact ⟨y, Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self hy)), rfl⟩
  rcases (S.mem_line_iff hx hz hxz (S.conj_mem g hy)).1 hmem with h | h | h
  · refine absurd ?_ hyx
    have : g⁻¹ * (g * y * g⁻¹) * g = g⁻¹ * x * g := by rw [h]
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group, mul_assoc, ← hgx.eq, ← mul_assoc,
      inv_mul_cancel, one_mul] at this
    exact this
  · exact ⟨g, hg, h⟩
  ·
    obtain ⟨e, he, hxe, hex, hez⟩ := S.exists_not_commute hx hz hxz hzx (by omega)
    have heR : e ∈ lineGroup D x y := hMR (S.mem_nCore hx he hxe.symm)
    refine ⟨e * g, (lineGroup D x y).mul_mem heR hg, ?_⟩
    have hez' : e * z * e⁻¹ = x * z := S.conj_eq_mul_of_not_commute hx he hz hxe hxz hex hzx hez
    calc e * g * y * (e * g)⁻¹ = e * (g * y * g⁻¹) * e⁻¹ := by group
      _ = x * (e * z * e⁻¹) := by rw [h, ← mul_assoc e x z, ← hxe.eq]; group
      _ = z := by rw [hez', ← mul_assoc, S.root.mul_self_eq_one hx, one_mul]

theorem TwoLocalSetting.eq_one_of_mem_centralizer {G : Type} [Group G] {D : Set G}
    (S : TwoLocalSetting G D) {p q c : G} (hp : p ∈ D) (hq : q ∈ D) (hpq : Commute p q)
    (hqp : q ≠ p) (h5 : 5 ≤ (rootLines D p).ncard)
    (hcp : c ∈ Subgroup.centralizer (nCore D p : Set G))
    (hcq : c ∈ Subgroup.centralizer (nCore D q : Set G)) : c = 1 := by
  have := S.hyp.finite
  have hL := S.lineSetting
  have hD := S.root
  have hclass := S.hyp.isClass
  have h5' : ∀ x ∈ D, 5 ≤ (rootLines D x).ncard := fun x hx => by
    rw [ncard_rootLines_eq hclass hp hx]
    exact h5
  have step : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, Commute x y → y ≠ x → Commute x z → z ≠ x →
      c ∈ Subgroup.centralizer (nCore D x : Set G) →
      c ∈ Subgroup.centralizer (nCore D y : Set G) →
      c ∈ Subgroup.centralizer (nCore D z : Set G) := by
    intro x hx y hy z hz hxy hyx hxz hzx hcx hcy
    obtain ⟨g, hg, hgy⟩ := S.exists_mem_lineGroup_conj_eq hx hy hz hxy hxz hyx hzx (h5' x hx)
    have hgc : Commute g c := S.commute_of_mem_lineGroup hx hy hxy hyx (h5' x hx) hcx hg
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hm' : g⁻¹ * m * g⁻¹⁻¹ ∈ nCore D y := by
      have h1 := conj_mem_nCore_conj hclass hm g⁻¹
      rwa [show g⁻¹ * z * g⁻¹⁻¹ = y by rw [← hgy]; group] at h1
    have h2 : Commute c (g⁻¹ * m * g⁻¹⁻¹) := (Subgroup.mem_centralizer_iff.1 hcy _ hm').symm
    have e : m = g * (g⁻¹ * m * g⁻¹⁻¹) * g⁻¹ := by group
    rw [e]
    exact (((hgc.symm.mul_right h2).mul_right hgc.symm.inv_right).symm).eq
  have hall : D ⊆ {x | x ∈ D ∧ c ∈ Subgroup.centralizer (nCore D x : Set G) ∧
      ∃ y ∈ D, Commute x y ∧ y ≠ x ∧ c ∈ Subgroup.centralizer (nCore D y : Set G)} := by
    refine hL.conn _ (fun x hx => hx.1) ⟨p, hp, hcp, q, hq, hpq, hqp, hcq⟩ ?_
    rintro x ⟨hx, hcx, y, hy, hxy, hyx, hcy⟩ z hz hxz hxzD
    have hzx : z ≠ x := by
      rintro rfl
      rw [hD.mul_self_eq_one hz] at hxzD
      exact hD.ne_one hxzD rfl
    exact ⟨hz, step x hx y hy z hz hxy hyx hxz hzx hcx hcy, x, hx, hxz.symm, Ne.symm hzx, hcx⟩
  have hcen : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure D := by rw [S.hyp.gen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      exact Subgroup.mem_centralizer_iff.1 (hall hx).2.1 x (self_mem_nCore hD hx)
    | one => simp
    | mul x y _ _ ihx ihy => rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
    | inv x _ ihx => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ihx, mul_assoc, mul_inv_cancel,
        mul_one]
  rw [S.hyp.center_eq_bot] at hcen
  exact Subgroup.mem_bot.1 hcen

theorem TwoLocalSetting.centralizer_nCore {G : Type} [Group G] {D : Set G}
    (S : TwoLocalSetting G D) {a : G} (ha : a ∈ D) (h5 : 5 ≤ (rootLines D a).ncard) :
    Subgroup.centralizer (nCore D a : Set G) = Subgroup.zpowers a := by
  have := S.hyp.finite
  have hL := S.lineSetting
  have hD := S.root
  have hclass := S.hyp.isClass
  refine le_antisymm ?_ ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_iff.2 fun m hm =>
    (commute_of_mem_nCore hm).eq))
  intro c hc
  obtain ⟨T, hT⟩ := hL.exists_mem_rootLines ha
  obtain ⟨d, hd, had, hda, -⟩ := (S.mem_rootLines_iff ha).1 hT
  have hkd : (rootLines D d).ncard = (rootLines D a).ncard := ncard_rootLines_eq hclass ha hd
  obtain ⟨y, hy, hdy, hyd, hya⟩ := S.exists_not_commute hd ha had.symm (Ne.symm hda)
    (by omega)
  have haM : a ∈ nCore D d := S.mem_nCore hd ha had
  have hyM : y ∈ nCore D d := S.mem_nCore hd hy hdy.symm
  have hP : ∀ c' ∈ Subgroup.centralizer (nCore D a : Set G), ∀ m ∈ nCore D d, Commute m a →
      Commute c' m := by
    intro c' hc' m hm hma
    exact (S.commute_of_mem_lineGroup ha hd had hda h5 hc'
      (inf_le_lineGroup D a d ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 hma.eq⟩)).symm
  have hfin : ∀ c' ∈ Subgroup.centralizer (nCore D a : Set G), Commute c' y →
      c' = 1 := by
    intro c' hc' hc'y
    have hc'd : c' ∈ Subgroup.centralizer (nCore D d : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun m hm =>
        ((S.commute_of_commute_of_commute_mul hd haM hyM (fun h => hya h) (hP c' hc')
          hc'y) m hm).symm.eq
    exact S.eq_one_of_mem_centralizer ha hd had hda h5 hc' hc'd
  have hca : Commute c a := (Subgroup.mem_centralizer_iff.1 hc a (S.self_mem ha)).symm
  have hcd : Commute c d := (Subgroup.mem_centralizer_iff.1 hc d (S.mem_nCore ha hd had.symm)).symm
  set u := c * y * c⁻¹ with hu
  have huD : u ∈ D := S.conj_mem c hy
  have hdu : Commute d u := by
    rw [hu]
    have := (Commute.conj_iff c).2 hdy
    rwa [show c * d * c⁻¹ = d by rw [hcd.eq, mul_inv_cancel_right]] at this
  have hud : u ≠ d := fun h => hyd (by
    have : c⁻¹ * u * c = c⁻¹ * d * c := by rw [h]
    rwa [hu, show c⁻¹ * (c * y * c⁻¹) * c = y by group, mul_assoc, ← hcd.eq, ← mul_assoc,
      inv_mul_cancel, one_mul] at this)
  have huM : u ∈ nCore D d := S.mem_nCore hd huD hdu.symm
  have hum : ∀ m ∈ nCore D d, Commute m a → (Commute u m ↔ Commute y m) := by
    intro m hm hma
    have hcm := hP c hc m hm hma
    have e : u * m * u⁻¹ * m⁻¹ = c * (y * m * y⁻¹ * m⁻¹) * c⁻¹ := by
      have h1 : c⁻¹ * m * c = m := by rw [mul_assoc, ← hcm.eq, ← mul_assoc, inv_mul_cancel,
        one_mul]
      have h2 : c⁻¹ * m⁻¹ * c = m⁻¹ := by rw [mul_assoc, ← hcm.inv_right.eq, ← mul_assoc,
        inv_mul_cancel, one_mul]
      calc u * m * u⁻¹ * m⁻¹ = c * y * (c⁻¹ * m * c) * y⁻¹ * c⁻¹ * m⁻¹ := by rw [hu]; group
        _ = c * y * m * y⁻¹ * (c⁻¹ * m⁻¹ * c) * c⁻¹ := by rw [h1]; group
        _ = c * (y * m * y⁻¹ * m⁻¹) * c⁻¹ := by rw [h2]; group
    have e' : c * (y * m * y⁻¹ * m⁻¹) * c⁻¹ = y * m * y⁻¹ * m⁻¹ := by
      rcases S.commutator_eq hd hyM hm with h | h <;> rw [h]
      · group
      · rw [hcd.eq, mul_inv_cancel_right]
    rw [commutatorElement_eq_one_iff_commute.symm, commutatorElement_eq_one_iff_commute.symm]
    change u * m * u⁻¹ * m⁻¹ = 1 ↔ y * m * y⁻¹ * m⁻¹ = 1
    rw [e, e']
  have hg : ∀ m ∈ nCore D d, Commute m a → Commute (u * y) m := by
    intro m hm hma
    rw [S.commute_mul_left_iff hd huM hyM hm]
    exact hum m hm hma
  rcases S.forall_commute_or_forall_commute_mul hd haM ((nCore D d).mul_mem huM hyM) hg with
    hcen | hcen
  ·
    have h1 := hcen y hyM
    rw [S.commute_mul_left_iff hd huM hyM hyM] at h1
    have huy : Commute y u := (h1.2 (Commute.refl y)).symm
    rcases (S.commute_iff_eq_or_eq_mul hd hy huD hdy hdu hyd hud).1 huy with h | h
    ·
      have hcy : Commute c y := by
        rw [Commute, SemiconjBy]
        calc c * y = c * y * c⁻¹ * c := by group
          _ = y * c := by rw [← hu, h]
      rw [hfin c hc hcy]
      exact Subgroup.one_mem _
    ·
      have hay' : a * y * a⁻¹ = d * y :=
        S.conj_eq_mul_of_not_commute hd ha hy had.symm hdy (Ne.symm hda) hyd fun h => hya h.symm
      have hcay : Commute (c * a) y := by
        rw [Commute, SemiconjBy]
        have hcdy : c * (d * y) * c⁻¹ = d * (c * y * c⁻¹) := by
          calc c * (d * y) * c⁻¹ = c * d * y * c⁻¹ := by group
            _ = d * c * y * c⁻¹ := by rw [hcd.eq]
            _ = d * (c * y * c⁻¹) := by group
        calc c * a * y = c * (a * y * a⁻¹) * c⁻¹ * (c * a) := by group
          _ = d * (c * y * c⁻¹) * (c * a) := by rw [hay', hcdy]
          _ = y * (c * a) := by rw [← hu, h, ← mul_assoc d d y, hD.mul_self_eq_one hd, one_mul]
      have hca' : c * a ∈ Subgroup.centralizer (nCore D a : Set G) :=
        Subgroup.mul_mem _ hc (Subgroup.mem_centralizer_iff.2 fun m hm =>
          (commute_of_mem_nCore hm).eq)
      have h1 := hfin _ hca' hcay
      have : c = a⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this, hD.inv_eq ha]
      exact Subgroup.mem_zpowers a
  ·
    exfalso
    have hiff : ∀ m ∈ nCore D d, (Commute u m ↔ (Commute y m ↔ Commute a m)) := by
      intro m hm
      have h1 := hcen m hm
      rw [S.commute_mul_left_iff hd ((nCore D d).mul_mem huM hyM) haM hm,
        S.commute_mul_left_iff hd huM hyM hm] at h1
      tauto
    have hua : ¬ Commute u a := by
      have := hiff a haM
      have hya' : ¬ Commute y a := hya
      have haa : Commute a a := Commute.refl a
      tauto
    have huy : ¬ Commute u y := by
      have := hiff y hyM
      have hay : ¬ Commute a y := fun h => hya h.symm
      have hyy : Commute y y := Commute.refl y
      tauto
    obtain ⟨w, hw, hdw, hwd, hwa, hwy, hwu⟩ := S.exists_not_commute_three hd
      (e₁ := a) (e₂ := y) (e₃ := u)
      (by
        rintro e (rfl | rfl | rfl)
        · exact ⟨ha, had.symm, Ne.symm hda⟩
        · exact ⟨hy, hdy, hyd⟩
        · exact ⟨huD, hdu, hud⟩)
      (by omega)
    have := hiff w (S.mem_nCore hd hw hdw.symm)
    have h1 : ¬ Commute y w := fun h => hwy h.symm
    have h2 : ¬ Commute a w := fun h => hwa h.symm
    have h3 : ¬ Commute u w := fun h => hwu h.symm
    tauto

end CFSG.Timmesfeld.Bridge
