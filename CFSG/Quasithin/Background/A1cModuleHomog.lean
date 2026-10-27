module

public import CFSG.Quasithin.Background.A1cModuleBridge

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace XMod

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

theorem commOf_eq_of_iso {L L' : Subgroup Q} (hL : IsIrr A L) (hL' : IsIrr A L')
    (hi : Iso A L' L) (h : commOf A L = L) : commOf A L' = L' := by
  rcases hL'.2.2 (commOf A L') (isInv_commOf L') bot_le (commOf_le_of_isInv hL'.1) with h0 | h1
  · exfalso
    have hfix' : L' ≤ fixed A ⊤ := commOf_eq_bot_iff.1 h0
    obtain ⟨φ, hφ⟩ := hi
    have hfixL : L ≤ fixed A ⊤ := by
      intro l hl
      refine ⟨trivial, fun a => ?_⟩
      set x : ↥L' := φ.symm ⟨l, hl⟩ with hx
      have h1 : a • (x : Q) = (x : Q) := (hfix' x.2).2 a
      have h2 := hφ a x x h1
      have h3 : ((φ x : ↥L) : Q) = l := by rw [hx, MulEquiv.apply_symm_apply]
      rw [h3] at h2
      exact h2
    have : commOf A L = ⊥ := commOf_eq_bot_iff.2 hfixL
    exact hL.2.1.ne (h.symm.trans this).symm
  · exact h1

end XMod

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]
  {X T : Subgroup G} {W : Subgroup V}

theorem smul_mem_modFix (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) {t : G} (ht : t ∈ T) {c : V}
    (hc : c ∈ modFix X W) : t • c ∈ modFix X W := by
  refine ⟨hW t ht c hc.1, fun x => ?_⟩
  change (x : G) • t • c = t • c
  rw [smul_smul_conj t (x : G) c]
  have h1 : (t⁻¹ * (x : G) * t) • c = c := hc.2 ⟨_, inv_conj_mem_of_mem_normalizer (hTX ht) x.2⟩
  rw [h1]

@[expose] noncomputable def quotSmulHom (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) (t : T) :
    V ⧸ modFix X W →* V ⧸ modFix X W :=
  QuotientGroup.map (modFix X W) (modFix X W) (MulDistribMulAction.toMonoidHom V (t : G))
    (fun _ hc => smul_mem_modFix hTX hW t.2 hc)

@[expose, instance_reducible] noncomputable def quotAct (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) : MulDistribMulAction ↥T (V ⧸ modFix X W) where
  smul t q := quotSmulHom hTX hW t q
  one_smul q := QuotientGroup.induction_on q fun x => by
    change QuotientGroup.mk ((1 : G) • x) = _
    rw [one_smul]
  mul_smul s t q := QuotientGroup.induction_on q fun x => by
    change QuotientGroup.mk (((s : G) * (t : G)) • x) = QuotientGroup.mk ((s : G) • (t : G) • x)
    rw [mul_smul]
  smul_mul t p q := QuotientGroup.induction_on p fun x => QuotientGroup.induction_on q fun y => by
    change quotSmulHom hTX hW t (QuotientGroup.mk x * QuotientGroup.mk y) =
      quotSmulHom hTX hW t (QuotientGroup.mk x) * quotSmulHom hTX hW t (QuotientGroup.mk y)
    exact map_mul _ _ _
  smul_one t := map_one _

theorem quotAct_smul_mk (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) (t : T) (v : V) :
    (letI := quotAct hTX hW; t • (QuotientGroup.mk v : V ⧸ modFix X W)) =
      QuotientGroup.mk ((t : G) • v) := rfl

theorem normalizes_quot (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) :
    letI := quotAct hTX hW
    XMod.Normalizes ↥X ↥T (V ⧸ modFix X W) := by
  let := quotAct hTX hW
  intro t a
  refine ⟨⟨(t : G) * a * (t : G)⁻¹, conj_mem_of_mem_normalizer (hTX t.2) a.2⟩, fun q => ?_⟩
  refine QuotientGroup.induction_on q fun v => ?_
  change (QuotientGroup.mk ((t : G) • (a : G) • v) : V ⧸ modFix X W) =
    QuotientGroup.mk (((t : G) * a * (t : G)⁻¹) • (t : G) • v)
  rw [smul_smul, smul_smul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

theorem mem_tilde_iff {I : Subgroup V} {q : V ⧸ modFix X W} :
    q ∈ tilde X W I ↔ ∃ v ∈ I, (QuotientGroup.mk v : V ⧸ modFix X W) = q := by
  unfold tilde
  rw [Subgroup.mem_map]
  rfl

theorem comap_tilde (I : Subgroup V) :
    (tilde X W I).comap (QuotientGroup.mk' (modFix X W)) = I ⊔ modFix X W := by
  unfold tilde
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem tilde_mono {I I' : Subgroup V} (h : I ≤ I') : tilde X W I ≤ tilde X W I' :=
  Subgroup.map_mono h

theorem tilde_smul (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) (t : T) (I : Subgroup V) :
    (letI := quotAct hTX hW; t • tilde X W I) = tilde X W ((t : G) • I) := by
  let := quotAct hTX hW
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_tilde_iff, mem_tilde_iff]
  constructor
  · rintro ⟨v, hv, hvq⟩
    refine ⟨(t : G) • v, Subgroup.smul_mem_pointwise_smul _ _ _ hv, ?_⟩
    rw [← quotAct_smul_mk hTX hW t v, hvq, smul_inv_smul]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(t : G)⁻¹ • v, Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hv, ?_⟩
    change (QuotientGroup.mk ((t : G)⁻¹ • v) : V ⧸ modFix X W) = (t⁻¹ : T) • _
    change _ = quotSmulHom hTX hW t⁻¹ _
    rfl

theorem tilde_biSup (T : Subgroup G) (I : Subgroup V) :
    tilde X W (⨆ y ∈ T, y • I) = ⨆ t : T, tilde X W ((t : G) • I) := by
  simp only [tilde, Subgroup.map_iSup]
  exact (iSup_subtype (p := (· ∈ T))
    (f := fun t : T => ((t : G) • I).map (QuotientGroup.mk' (modFix X W)))).symm

theorem isInv_tilde {I : Subgroup V} (hI : IsModInv X I) : XMod.IsInv ↥X (tilde X W I) := by
  intro a l hl
  obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hl
  exact mem_tilde_iff.2 ⟨a • v, hI a v hv, rfl⟩

theorem fixed_le_modFix {I : Subgroup V} (hIW : I ≤ W) : XMod.fixed ↥X I ≤ modFix X W :=
  XMod.fixed_mono hIW

theorem inf_modFix_le_fixed (I : Subgroup V) : I ⊓ modFix X W ≤ XMod.fixed ↥X I :=
  fun _ hi => ⟨hi.1, hi.2.2⟩

theorem modFix_le_fixed_top : modFix X W ≤ XMod.fixed ↥X (⊤ : Subgroup V) :=
  XMod.fixed_mono le_top

theorem commOf_tilde (I : Subgroup V) :
    XMod.commOf ↥X (tilde X W I) = tilde X W (modComm X I) := by
  show XMod.commOf ↥X (I.map (QuotientGroup.mk' (modFix X W))) =
    (XMod.commOf ↥X I).map (QuotientGroup.mk' (modFix X W))
  unfold XMod.commOf
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hl
    exact ⟨_, ⟨a, i, hi, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, i, hi, rfl⟩, rfl⟩
    exact ⟨a, _, Subgroup.mem_map_of_mem _ hi, rfl⟩

theorem tilde_eq_bot_iff {I : Subgroup V} : tilde X W I = ⊥ ↔ I ≤ modFix X W := by
  unfold tilde
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem isIrr_tilde {I : Subgroup V} (hI : I ∈ IrrPlus X W) :
    XMod.IsIrr ↥X (tilde X W I) ∧ XMod.commOf ↥X (tilde X W I) = tilde X W I := by
  obtain ⟨hIW, hinv, hcomm, hlt, hirr⟩ := hI
  have hcomm' : XMod.commOf ↥X (tilde X W I) = tilde X W I := by
    rw [commOf_tilde]
    exact congrArg (tilde X W) hcomm
  refine ⟨⟨isInv_tilde hinv, ?_, fun J hJ _ hJL => ?_⟩, hcomm'⟩
  · refine bot_lt_iff_ne_bot.2 fun h => hlt.ne ?_
    have hle : I ≤ modFix X W := tilde_eq_bot_iff.1 h
    exact le_antisymm (XMod.fixed_le I) (fun i hi => ⟨hi, (hle hi).2⟩)
  · set π := QuotientGroup.mk' (modFix X W) with hπ
    have hinvJ : XMod.IsInv ↥X (J.comap π ⊓ I) := by
      refine XMod.IsInv.inf ?_ hinv
      intro a x hx
      rw [Subgroup.mem_comap] at hx ⊢
      exact hJ a _ hx
    have hfJ : XMod.fixed ↥X I ≤ J.comap π ⊓ I := by
      intro i hi
      refine ⟨?_, hi.1⟩
      show π i ∈ J
      have : π i = 1 := (QuotientGroup.eq_one_iff i).2 (fixed_le_modFix hIW hi)
      rw [this]
      exact J.one_mem
    rcases hirr _ hinvJ hfJ inf_le_right with h | h
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨i, hi, rfl⟩ := mem_tilde_iff.1 (hJL hq)
      have h1 : i ∈ J.comap π ⊓ I := ⟨hq, hi⟩
      rw [h] at h1
      exact (QuotientGroup.eq_one_iff i).2 (fixed_le_modFix hIW h1)
    · right
      refine le_antisymm hJL ?_
      rintro _ hl
      obtain ⟨i, hi, rfl⟩ := mem_tilde_iff.1 hl
      have : i ∈ J.comap π ⊓ I := by rw [h]; exact hi
      exact this.1

theorem lift_mem_irrPlus {L' : Subgroup (V ⧸ modFix X W)} (hL' : XMod.IsIrr ↥X L')
    (hcomm : XMod.commOf ↥X L' = L') (hle : L' ≤ tilde X W W) :
    modComm X (L'.comap (QuotientGroup.mk' (modFix X W))) ∈ IrrPlus X W ∧
      tilde X W (modComm X (L'.comap (QuotientGroup.mk' (modFix X W)))) = L' := by
  set π := QuotientGroup.mk' (modFix X W) with hπ
  set P := L'.comap π with hPdef
  have hPinv : IsModInv X P := by
    intro a x hx
    rw [hPdef, Subgroup.mem_comap] at hx ⊢
    exact hL'.1 a _ hx
  have hPW : P ≤ W := by
    intro v hv
    have h1 : v ∈ (tilde X W W).comap π := hle hv
    rw [comap_tilde, sup_eq_left.2 (XMod.fixed_le W)] at h1
    exact h1
  have hCP : modFix X W ≤ P := by
    intro c hc
    rw [hPdef, Subgroup.mem_comap]
    have : π c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    rw [this]
    exact L'.one_mem
  have hπP : tilde X W P = L' :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L'
  set I' := modComm X P with hI'def
  have hI'P : I' ≤ P := XMod.commOf_le_of_isInv hPinv
  have hI'inv : IsModInv X I' := XMod.isInv_commOf P
  have htI'inv : XMod.IsInv ↥X (tilde X W I') := isInv_tilde hI'inv
  have htI'le : tilde X W I' ≤ L' := hπP ▸ tilde_mono hI'P
  have hcommL' : XMod.commOf ↥X L' = tilde X W I' := by
    calc XMod.commOf ↥X L' = XMod.commOf ↥X (tilde X W P) := by rw [hπP]
      _ = tilde X W (modComm X P) := commOf_tilde P
  have htI' : tilde X W I' = L' := by
    rcases hL'.2.2 _ htI'inv bot_le htI'le with h0 | h1
    · exfalso
      rw [h0] at hcommL'
      exact hL'.2.1.ne (hcomm.symm.trans hcommL').symm
    · exact h1
  have hsup : I' ⊔ modFix X W = P := by
    rw [← comap_tilde, htI']
  have hI'comm : modComm X I' = I' := by
    calc modComm X I' = modComm X (I' ⊔ modFix X W) :=
          (XMod.commOf_sup_eq_of_le_fixed modFix_le_fixed_top).symm
      _ = modComm X P := by rw [hsup]
  have hI'W : I' ≤ W := hI'P.trans hPW
  refine ⟨⟨hI'W, hI'inv, hI'comm, ?_, ?_⟩, htI'⟩
  · refine lt_of_le_of_ne (XMod.fixed_le I') fun h => ?_
    have hle' : I' ≤ modFix X W := by
      intro i hi
      have : i ∈ XMod.fixed ↥X I' := by rw [h]; exact hi
      exact fixed_le_modFix hI'W this
    have : tilde X W I' = ⊥ := tilde_eq_bot_iff.2 hle'
    rw [htI'] at this
    exact hL'.2.1.ne this.symm
  · intro J hJ hfJ hJI
    have htJ : tilde X W J ≤ L' := htI' ▸ tilde_mono hJI
    rcases hL'.2.2 _ (isInv_tilde hJ) bot_le htJ with h0 | h1
    · left
      have hJC : J ≤ modFix X W := tilde_eq_bot_iff.1 h0
      exact le_antisymm ((le_inf hJI hJC).trans (inf_modFix_le_fixed I')) hfJ
    · right
      have h2 : J ⊔ modFix X W = I' ⊔ modFix X W := by
        rw [← comap_tilde, ← comap_tilde, h1, htI']
      refine le_antisymm hJI fun i hi => ?_
      have hi' : i ∈ J ⊔ modFix X W := by rw [h2]; exact Subgroup.mem_sup_left hi
      obtain ⟨j, hj, c, hc, rfl⟩ := Subgroup.mem_sup.1 hi'
      have hcI : c ∈ I' := by
        have := I'.mul_mem (I'.inv_mem (hJI hj)) hi
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact J.mul_mem hj (hfJ (inf_modFix_le_fixed I' ⟨hcI, hc⟩))

@[expose] def classStab (X : Subgroup G) (W : Subgroup V) (T : Subgroup G) (I : Subgroup V) :
    Set G :=
  {t | t ∈ T ∧ XMod.Iso ↥X (tilde X W ((t : G) • I)) (tilde X W I)}

theorem tilde_biSup_smul (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) (I : Subgroup V) :
    letI := quotAct hTX hW
    tilde X W (⨆ y ∈ T, y • I) = ⨆ t : T, t • tilde X W I := by
  let := quotAct hTX hW
  rw [tilde_biSup]
  exact iSup_congr fun t => (tilde_smul hTX hW t I).symm

theorem mem_irrPlusOn_iff (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) {I : Subgroup V} :
    letI := quotAct hTX hW
    I ∈ IrrPlusOn X W T ↔ I ∈ IrrPlus X W ∧
      XMod.IsHomComp ↥X (⨆ t : T, t • tilde X W I) (tilde X W I) := by
  let := quotAct hTX hW
  show (I ∈ IrrPlus X W ∧ XMod.IsHomComp ↥X (tilde X W (⨆ y ∈ T, y • I)) (tilde X W I)) ↔ _
  rw [tilde_biSup_smul hTX hW]

theorem smul_eq_of_tilde_eq (hTX : T ≤ Subgroup.normalizer (X : Set G)) {I : Subgroup V}
    (hI : modComm X I = I) {t : G} (ht : t ∈ T) (h : tilde X W (t • I) = tilde X W I) :
    t • I = I := by
  have hsup : t • I ⊔ modFix X W = I ⊔ modFix X W := by
    rw [← comap_tilde, ← comap_tilde, h]
  calc t • I = t • modComm X I := by rw [hI]
    _ = modComm X (t • I) := smul_modComm (hTX ht) I
    _ = modComm X (t • I ⊔ modFix X W) :=
        (XMod.commOf_sup_eq_of_le_fixed modFix_le_fixed_top).symm
    _ = modComm X (I ⊔ modFix X W) := by rw [hsup]
    _ = modComm X I := XMod.commOf_sup_eq_of_le_fixed modFix_le_fixed_top
    _ = I := hI

theorem forall_smul_eq_iff_mem_irrPlusOn (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) {I : Subgroup V} (hI : I ∈ IrrPlus X W) :
    (∀ t ∈ classStab X W T I, t • I = I) ↔ I ∈ IrrPlusOn X W T := by
  let := quotAct hTX hW
  have hnorm := normalizes_quot hTX hW
  obtain ⟨hirr, hcomm⟩ := isIrr_tilde hI
  rw [mem_irrPlusOn_iff hTX hW, ← XMod.forall_iso_smul_eq_iff_isHomComp hnorm hirr]
  refine ⟨fun h => ⟨hI, fun t hiso => ?_⟩, fun h t ⟨ht, hiso⟩ => ?_⟩
  · have e := tilde_smul hTX hW t I
    rw [e] at hiso ⊢
    rw [h (t : G) ⟨t.2, hiso⟩]
  · refine smul_eq_of_tilde_eq (W := W) hTX hI.2.2.1 ht ?_
    have e := tilde_smul hTX hW ⟨t, ht⟩ I
    have h1 := h.2 ⟨t, ht⟩ (by rw [e]; exact hiso)
    rw [e] at h1
    exact h1

theorem tilde_smul_eq_of_iso_of_mem_irrPlusOn (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) {I : Subgroup V} (hI : I ∈ IrrPlusOn X W T) {t r : G}
    (ht : t ∈ T) (hr : r ∈ T)
    (h : XMod.Iso ↥X (tilde X W (t • I)) (tilde X W (r • I))) :
    tilde X W (t • I) = tilde X W (r • I) := by
  let := quotAct hTX hW
  have hnorm := normalizes_quot hTX hW
  obtain ⟨hirr, -⟩ := isIrr_tilde hI.1
  have hS := ((mem_irrPlusOn_iff hTX hW).1 hI).2
  have e1 := tilde_smul hTX hW ⟨t, ht⟩ I
  have e2 := tilde_smul hTX hW ⟨r, hr⟩ I
  have h' := XMod.eq_of_iso_smul_of_isHomComp hnorm hirr hS (t := ⟨t, ht⟩) (r := ⟨r, hr⟩)
    (by rw [e1, e2]; exact h)
  rw [e1, e2] at h'
  exact h'

theorem sSupIndep_tilde_smul_of_mem_irrPlusOn (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) {I : Subgroup V} (hI : I ∈ IrrPlusOn X W T) :
    sSupIndep {c : Subgroup (V ⧸ modFix X W) | ∃ t ∈ T, c = tilde X W (t • I)} ∧
      sSup {c : Subgroup (V ⧸ modFix X W) | ∃ t ∈ T, c = tilde X W (t • I)} =
        tilde X W (⨆ y ∈ T, y • I) := by
  let := quotAct hTX hW
  have hnorm := normalizes_quot hTX hW
  obtain ⟨hirr, -⟩ := isIrr_tilde hI.1
  have hS := ((mem_irrPlusOn_iff hTX hW).1 hI).2
  have hset : {c : Subgroup (V ⧸ modFix X W) | ∃ t ∈ T, c = tilde X W (t • I)} =
      Set.range fun t : T => t • tilde X W I := by
    ext c
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (tilde_smul hTX hW ⟨t, ht⟩ I)⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, tilde_smul hTX hW t I⟩
  rw [hset]
  refine ⟨XMod.sSupIndep_smul_of_isHomComp hnorm hirr hS, ?_⟩
  rw [tilde_biSup_smul hTX hW, sSup_range]

theorem le_biSup_smul (T : Subgroup G) (I : Subgroup V) {y : G} (hy : y ∈ T) :
    y • I ≤ ⨆ y ∈ T, y • I :=
  le_iSup₂_of_le y hy le_rfl

theorem smul_mem_biSup_smul {T : Subgroup G} {I : Subgroup V} {t : G} (ht : t ∈ T) {w : V}
    (hw : w ∈ ⨆ y ∈ T, y • I) : t • w ∈ ⨆ y ∈ T, y • I := by
  have hW₁eq : (⨆ y ∈ T, y • I) = ⨆ r : T, (r : G) • I :=
    (iSup_subtype (p := (· ∈ T)) (f := fun r : T => (r : G) • I)).symm
  rw [hW₁eq] at hw ⊢
  refine Subgroup.iSup_induction (fun r : T => (r : G) • I)
    (C := fun x => t • x ∈ ⨆ r : T, (r : G) • I) hw (fun r x hx => ?_) ?_ ?_
  · have h1 := Subgroup.smul_mem_pointwise_smul x t _ hx
    rw [smul_smul] at h1
    exact (le_iSup (fun r : T => (r : G) • I) ⟨t * r, T.mul_mem ht r.2⟩) h1
  · rw [smul_one]
    exact one_mem _
  · intro x y hx hy
    rw [smul_mul']
    exact mul_mem hx hy

theorem irrPlusOn_nonempty [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hT2 : IsPGroup 2 ↥T) {I : Subgroup V}
    (hI : I ∈ IrrPlus X W) : (IrrPlusOn X (⨆ y ∈ T, y • I) T).Nonempty := by
  set W₁ := ⨆ y ∈ T, y • I with hW₁
  have hW₁T : ∀ t ∈ T, ∀ w ∈ W₁, t • w ∈ W₁ := fun t ht w hw => smul_mem_biSup_smul ht hw
  have hI₁ : I ∈ IrrPlus X W₁ := by
    refine ⟨?_, hI.2⟩
    have := le_biSup_smul T I T.one_mem
    rwa [one_smul] at this
  let := quotAct hTX hW₁T
  have hnorm := normalizes_quot hTX hW₁T
  obtain ⟨hirr, hcomm⟩ := isIrr_tilde hI₁
  have hQ : ∀ q : V ⧸ modFix X W₁, q ^ 2 = 1 := by
    intro q
    refine QuotientGroup.induction_on q fun v => ?_
    rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]
  obtain ⟨L', hL'le, hL'irr, hL'iso, hL'H⟩ :=
    XMod.exists_isHomComp_of_isIrr hQ hnorm hT2 hirr
  have hL'comm : XMod.commOf ↥X L' = L' := XMod.commOf_eq_of_iso hirr hL'irr hL'iso hcomm
  have hLsup : tilde X W₁ W₁ = ⨆ t : T, t • tilde X W₁ I := tilde_biSup_smul hTX hW₁T I
  obtain ⟨hI'mem, hI'tilde⟩ := lift_mem_irrPlus hL'irr hL'comm (hLsup ▸ hL'le)
  refine ⟨_, (mem_irrPlusOn_iff hTX hW₁T).2 ⟨hI'mem, ?_⟩⟩
  rw [hI'tilde]
  exact hL'H

end CFSG.Quasithin
