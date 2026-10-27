module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.Quasithin.Background.B19Normal
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem forall_unique_of_unique (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {U : Subgroup W} (hU : U ∈ irrSet H)
    (huniq : ∀ X ∈ conjSet L Y, ¬ commSub U X ≤ fixV H → X = L) :
    ∀ I ∈ irrSet H, ∀ X ∈ conjSet L Y, ∀ X' ∈ conjSet L Y,
      ¬ commSub I X ≤ fixV H → ¬ commSub I X' ≤ fixV H → X = X' := by
  obtain ⟨h1, -, hHY, hn, hnorm, hne⟩ := h_facts hL hH
  have htrans := ((w4Lem12_5_holds W hW Y hO hB H hne hHY hnorm).2 L hL h1).1.2
  intro I hI
  obtain ⟨g, hg, hsec⟩ := htrans U hU I hI
  have hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H := hn g hg
  have hgH' : ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
    intro x hx
    simpa using hn g⁻¹ (Y.inv_mem hg) x hx
  have key : ∀ X ∈ conjSet L Y, ¬ commSub I X ≤ fixV H →
      X = L.map (MulAut.conj g).toMonoidHom := by
    intro X hX hXI
    obtain ⟨-, hXH, -⟩ := conjSet_facts hL hH hX
    have hC : fixV H ≤ fixV X := fun w hw x hx => hw x (hXH hx)
    have hXUg : ¬ commSub (U.map g.toMonoidHom) X ≤ fixV H := by
      intro hle
      apply hXI
      have h2 : commSub (U.map g.toMonoidHom ⊔ fixV H) X ≤ fixV H := by
        rw [CFSG.Quasithin.commSub_sup_fixV hC]
        exact hle
      have h3 := secIsoOn_commSub_le hsec hXH h2
      rwa [CFSG.Quasithin.commSub_sup_fixV hC] at h3
    have hX'mem : X.map (MulAut.conj g⁻¹).toMonoidHom ∈ conjSet L Y := by
      obtain ⟨n, hn', rfl⟩ := hX
      exact ⟨g⁻¹ * n, Y.mul_mem (Y.inv_mem hg) hn', CFSG.Quasithin.B19.map_conj_map_conj L _ _⟩
    have hXX' : (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
      rw [CFSG.Quasithin.B19.map_conj_map_conj, mul_inv_cancel]
      ext x
      simp
    have hX'U : ¬ commSub U (X.map (MulAut.conj g⁻¹).toMonoidHom) ≤ fixV H := by
      intro hle
      apply hXUg
      have h4 := Subgroup.map_mono (f := g.toMonoidHom) hle
      rwa [← commSub_map_conj, hXX', map_fixV_of_normalizes hgH hgH'] at h4
    have h5 := huniq _ hX'mem hX'U
    rw [← hXX', h5]
  intro X hX X' hX' hXI hX'I
  rw [key X hX hXI, key X' hX' hX'I]

@[expose] def trivMod (X' : Subgroup (MulAut W)) (C : Subgroup W) : Subgroup W where
  carrier := {w | ∀ x ∈ X', x w * w⁻¹ ∈ C}
  one_mem' := fun x _ => by simp
  mul_mem' := by
    intro a b ha hb x hx
    have he : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [he]
    exact C.mul_mem (ha x hx) (hb x hx)
  inv_mem' := by
    intro a ha x hx
    have he : x a⁻¹ * a⁻¹⁻¹ = (x a * a⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
    rw [he]
    exact C.inv_mem (ha x hx)

omit [Finite W] in
theorem mem_trivMod {X' : Subgroup (MulAut W)} {C : Subgroup W} {w : W} :
    w ∈ trivMod X' C ↔ ∀ x ∈ X', x w * w⁻¹ ∈ C := Iff.rfl

omit [Finite W] in
theorem commSub_le_iff_le_trivMod {A : Subgroup W} {X' : Subgroup (MulAut W)} {C : Subgroup W} :
    commSub A X' ≤ C ↔ A ≤ trivMod X' C := by
  constructor
  · intro h a ha x hx
    exact h (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
  · intro h
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, a, ha, rfl⟩
    exact h ha x hx

theorem exists_conj_not_le {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {I : Subgroup W} (hI : I ∈ irrSet H) :
    ∃ X ∈ conjSet L Y, ¬ commSub I X ≤ fixV H := by
  by_contra hall
  push Not at hall
  apply not_le_fixV_of_mem_irrSet hI
  have hP : ∀ x ∈ H, ∀ u ∈ I, x u * u⁻¹ ∈ I ⊓ fixV H := by
    intro x hx
    rw [hH, iSup_subtype'] at hx
    refine Subgroup.iSup_induction (fun X : conjSet L Y => (X : Subgroup (MulAut W)))
      (C := fun x => ∀ u ∈ I, x u * u⁻¹ ∈ I ⊓ fixV H) hx ?_ ?_ ?_
    · intro X y hy u hu
      have hXH : (X : Subgroup (MulAut W)) ≤ H := (conjSet_facts hL hH X.2).2.1
      exact ⟨I.mul_mem (hI.2.2.1 y (hXH hy) u hu) (I.inv_mem hu),
        hall X X.2 (Subgroup.subset_closure ⟨y, hy, u, hu, rfl⟩)⟩
    · intro u _
      simp
    · intro a b ha hb u hu
      have hbu : b u ∈ I := by
        have h2 := I.mul_mem (hb u hu).1 hu
        simpa using h2
      have h3 := (I ⊓ fixV H).mul_mem (ha (b u) hbu) (hb u hu)
      have he : a (b u) * (b u)⁻¹ * (b u * u⁻¹) = (a * b) u * u⁻¹ := by
        rw [MulAut.mul_apply]
        group
      rwa [he] at h3
  have hle : commSub I H ≤ I ⊓ fixV H := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    exact hP x hx u hu
  rw [hI.1] at hle
  exact hle.trans inf_le_right

theorem commV_le_trivMod (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    (huniq : ∀ I ∈ irrSet H, ∀ X ∈ conjSet L Y, ∀ X' ∈ conjSet L Y,
      ¬ commSub I X ≤ fixV H → ¬ commSub I X' ≤ fixV H → X = X')
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hX' : X' ∈ conjSet L Y) (hne : X ≠ X') :
    commV X ≤ trivMod X' (fixV H) := by
  obtain ⟨h1, -, hHY, -, hnorm, hne'⟩ := h_facts hL hH
  have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
    ((w4Lem12_5_holds W hW Y hO hB H hne' hHY hnorm).2 L hL h1).1.1
  obtain ⟨-, hXH, -⟩ := conjSet_facts hL hH hX
  obtain ⟨-, hX'H, -⟩ := conjSet_facts hL hH hX'
  rw [commV_eq_commSub, ← htop, commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  rw [iSup_subtype'] at hv
  refine Subgroup.iSup_induction (fun I : irrSet H => (I : Subgroup W))
    (C := fun v => x v * v⁻¹ ∈ trivMod X' (fixV H)) hv ?_ ?_ ?_
  · intro I v hv
    by_cases hXI : commSub (I : Subgroup W) X ≤ fixV H
    · have hc : x v * v⁻¹ ∈ fixV H := hXI (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩)
      intro y hy
      rw [hc y (hX'H hy), mul_inv_cancel]
      exact (fixV H).one_mem
    · have hX'I : commSub (I : Subgroup W) X' ≤ fixV H := by
        by_contra h
        exact hne (huniq I I.2 X hX X' hX' hXI h)
      have hmem : x v * v⁻¹ ∈ (I : Subgroup W) :=
        (I : Subgroup W).mul_mem (I.2.2.2.1 x (hXH hx) v hv) ((I : Subgroup W).inv_mem hv)
      exact commSub_le_iff_le_trivMod.mp hX'I hmem
  · intro y _
    simp
  · intro a b ha hb
    have he : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [he]
    exact (trivMod X' (fixV H)).mul_mem ha hb

theorem isDirSumOver_of_unique (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    (huniq : ∀ I ∈ irrSet H, ∀ X ∈ conjSet L Y, ∀ X' ∈ conjSet L Y,
      ¬ commSub I X ≤ fixV H → ¬ commSub I X' ≤ fixV H → X = X') :
    IsDirSumOver (conjSet L Y) (fun X => commV (autQuot X (fixV H))) := by
  obtain ⟨h1, -, hHY, hn, hnorm, hne'⟩ := h_facts hL hH
  have hn' := hn
  set C := fixV H with hC
  have hstab : Y ≤ stabSub C := le_stabSub_fixV hn
  have hXstab : ∀ X ∈ conjSet L Y, X ≤ stabSub C := fun X hX =>
    ((conjSet_facts hL hH hX).2.1.trans hHY).trans hstab
  have hfixmap : ∀ X' : Subgroup (MulAut W), X' ≤ stabSub C →
      (trivMod X' C).map (QuotientGroup.mk' C) ≤ fixV (autQuot X' C) := by
    rintro X' - _ ⟨w, hw, rfl⟩ φ hφ
    obtain ⟨g, hgX, rfl⟩ := mem_autQuot.mp hφ
    rw [QuotientGroup.mk'_apply, quotHom_mk, mk_eq_mk_iff]
    exact hw g.1 hgX
  have hallfix : ∀ w : W, (∀ X ∈ conjSet L Y, w ∈ trivMod X C) →
      (QuotientGroup.mk' C w : W ⧸ C) = 1 := by
    intro w hw
    have hQ : ∀ h ∈ H, (∀ c ∈ C, h c ∈ C) ∧ h w * w⁻¹ ∈ C := by
      intro h hh
      rw [hH, iSup_subtype'] at hh
      refine Subgroup.iSup_induction (fun X : conjSet L Y => (X : Subgroup (MulAut W)))
        (C := fun h => (∀ c ∈ C, h c ∈ C) ∧ h w * w⁻¹ ∈ C) hh ?_ ?_ ?_
      · intro X x hx
        have hXH : (X : Subgroup (MulAut W)) ≤ H := (conjSet_facts hL hH X.2).2.1
        exact ⟨fun c hc => by rw [hc x (hXH hx)]; exact hc, hw X X.2 x hx⟩
      · exact ⟨fun c hc => hc, by simp⟩
      · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun c hc => ha1 _ (hb1 c hc), ?_⟩
        have hbw : b w = (b w * w⁻¹) * w := (inv_mul_cancel_right (b w) w).symm
        rw [MulAut.mul_apply, hbw, map_mul, mul_assoc]
        exact C.mul_mem (ha1 _ hb2) ha2
    have hmem : (QuotientGroup.mk' C w : W ⧸ C) ∈ fixV (autQuot H C) :=
      hfixmap H (hHY.trans hstab) ⟨w, fun h hh => (hQ h hh).2, rfl⟩
    rw [fixV_autQuot_eq_bot hL hH] at hmem
    exact hmem
  have hS : ∀ X ∈ conjSet L Y, ∀ X' ∈ conjSet L Y, X ≠ X' →
      commV (autQuot X C) ≤ fixV (autQuot X' C) := by
    intro X hX X' hX' hne
    rw [commV_autQuot (hXstab X hX)]
    exact (Subgroup.map_mono (commV_le_trivMod hW hO hB hL hH huniq hX hX' hne)).trans
      (hfixmap X' (hXstab X' hX'))
  have hfix_iff : ∀ (X : Subgroup (MulAut W)) (w : W), X ≤ stabSub C →
      ((QuotientGroup.mk' C w : W ⧸ C) ∈ fixV (autQuot X C) ↔ w ∈ trivMod X C) := by
    intro X w hX
    rw [QuotientGroup.mk'_apply, mk_mem_fixV_autQuot]
    exact ⟨fun h x hx => h x hx (hX hx), fun h x hx _ => h x hx⟩
  refine ⟨?_, ?_⟩
  · intro X
    rw [disjoint_iff, eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective C v
    rw [Subgroup.mem_bot]
    refine hallfix w fun X'' hX'' => (hfix_iff X'' w (hXstab X'' hX'')).mp ?_
    by_cases hXX : X'' = X
    · subst hXX
      have hle : (⨆ (j : ↥(conjSet L Y)) (_ : j ≠ X), commV (autQuot (j : Subgroup (MulAut W)) C)) ≤
          fixV (autQuot (X : Subgroup (MulAut W)) C) :=
        iSup₂_le fun j hj => hS j j.2 X X.2 fun h => hj (Subtype.ext h)
      exact hle hv2
    · exact hS X X.2 X'' hX'' (fun h => hXX h.symm) hv1
  · rw [eq_top_iff]
    intro v _
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective C v
    have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
      ((w4Lem12_5_holds W hW Y hO hB H hne' hHY hnorm).2 L hL h1).1.1
    have hw : w ∈ ⨆ I ∈ irrSet H, I := by rw [htop]; trivial
    have hle : (⨆ I ∈ irrSet H, I).map (QuotientGroup.mk' C) ≤
        ⨆ X : ↥(conjSet L Y), commV (autQuot (X : Subgroup (MulAut W)) C) := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun I => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hI => ?_
      obtain ⟨X, hX, hXI⟩ := exists_conj_not_le hL hH hI
      obtain ⟨-, hXH, hXn⟩ := conjSet_facts hL hH hX
      have hirr := isIrrOn_sup_fixV hI
      have hJs : StableUnder H (commSub I X ⊔ C) :=
        stableUnder_sup (stableUnder_commSub hXn hI.2.2.1)
          (stableUnder_fixV fun y hy h hh => hn' y (hHY hy) h hh)
      have hJle : commSub I X ⊔ C ≤ I ⊔ C :=
        sup_le_sup_right (commSub_le_of_invariant fun x hx u hu => hI.2.2.1 x (hXH hx) u hu) C
      have hJeq : commSub I X ⊔ C = I ⊔ C := by
        rcases hirr.2.2.2 _ hJs le_sup_right hJle with h | h
        · exact absurd (le_sup_left.trans h.le) hXI
        · exact h
      calc I.map (QuotientGroup.mk' C) ≤ (I ⊔ C).map (QuotientGroup.mk' C) :=
            Subgroup.map_mono le_sup_left
        _ = (commSub I X).map (QuotientGroup.mk' C) := by
            rw [← hJeq, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
        _ ≤ (commV X).map (QuotientGroup.mk' C) :=
            Subgroup.map_mono (by rw [commV_eq_commSub]; exact commSub_mono le_top le_rfl)
        _ = commV (autQuot X C) := (commV_autQuot (hXstab X hX)).symm
        _ ≤ ⨆ X : ↥(conjSet L Y), commV (autQuot (X : Subgroup (MulAut W)) C) :=
            le_iSup_of_le ⟨X, hX⟩ le_rfl
    exact hle ⟨w, hw, rfl⟩


end CFSG.LocalAnalysis.WeakClosure81
