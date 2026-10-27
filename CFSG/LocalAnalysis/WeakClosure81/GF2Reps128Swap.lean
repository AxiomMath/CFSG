module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Uniq
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W]

@[expose] def secStab (C : Subgroup W) (I : Subgroup (W ⧸ C)) : Subgroup ↥(stabSub C) :=
  (stabSub I).comap (quotHom C)

@[expose] def secHom (C : Subgroup W) (I : Subgroup (W ⧸ C)) : ↥(secStab C I) →* MulAut ↥I :=
  (resHom I).comp (((quotHom C).comp (secStab C I).subtype).codRestrict (stabSub I)
    fun g => g.2)

theorem secHom_apply (C : Subgroup W) (I : Subgroup (W ⧸ C)) (g : ↥(secStab C I)) (v : ↥I) :
    ((secHom C I g v : ↥I) : W ⧸ C) = quotHom C g.1 v := rfl

theorem mem_autSub_autQuot {X : Subgroup (MulAut W)} {C : Subgroup W} {I : Subgroup (W ⧸ C)}
    {ψ : MulAut ↥I} :
    ψ ∈ autSub (autQuot X C) I ↔
      ∃ g : ↥(secStab C I), ((g : stabSub C) : MulAut W) ∈ X ∧ secHom C I g = ψ := by
  rw [mem_autSub]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := mem_autQuot.mp hy
    have hxI : x ∈ secStab C I := by
      show quotHom C x ∈ stabSub I
      rw [hxy]
      exact y.2
    refine ⟨⟨x, hxI⟩, hx, ?_⟩
    have hy' : (((quotHom C).comp (secStab C I).subtype).codRestrict (stabSub I) fun g => g.2)
        ⟨x, hxI⟩ = y := Subtype.ext hxy
    simp only [secHom, MonoidHom.coe_comp, Function.comp_apply, hy']
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨quotHom C g.1, g.2⟩, mem_autQuot.mpr ⟨g.1, hg, rfl⟩, rfl⟩

theorem autSub_autQuot_sup {A B : Subgroup (MulAut W)} {C : Subgroup W} {I : Subgroup (W ⧸ C)}
    (hA : A ≤ (secStab C I).map (stabSub C).subtype)
    (hB : B ≤ (secStab C I).map (stabSub C).subtype) :
    autSub (autQuot (A ⊔ B) C) I = autSub (autQuot A C) I ⊔ autSub (autQuot B C) I := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub_autQuot.mp hψ
    set R := autSub (autQuot A C) I ⊔ autSub (autQuot B C) I with hR
    set Q : Subgroup (MulAut W) :=
      ((R.comap (secHom C I)).map (secStab C I).subtype).map (stabSub C).subtype with hQ
    have hXQ : ∀ {X : Subgroup (MulAut W)}, X ≤ (secStab C I).map (stabSub C).subtype →
        autSub (autQuot X C) I ≤ R → X ≤ Q := by
      intro X hX hXR a ha
      obtain ⟨y, hy, rfl⟩ := hX ha
      exact ⟨y, ⟨⟨y, hy⟩, hXR (mem_autSub_autQuot.mpr ⟨⟨y, hy⟩, ha, rfl⟩), rfl⟩, rfl⟩
    obtain ⟨y, ⟨z, hz, hzy⟩, hyg⟩ := sup_le (hXQ hA le_sup_left) (hXQ hB le_sup_right) hg
    have hzg : z = g := Subtype.ext (hzy.trans (Subtype.ext hyg))
    rw [← hzg]
    exact hz
  · refine sup_le (fun ψ hψ => ?_) (fun ψ hψ => ?_)
    · obtain ⟨g, hg, rfl⟩ := mem_autSub_autQuot.mp hψ
      exact mem_autSub_autQuot.mpr ⟨g, le_sup_left (α := Subgroup (MulAut W)) hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := mem_autSub_autQuot.mp hψ
      exact mem_autSub_autQuot.mpr ⟨g, le_sup_right (α := Subgroup (MulAut W)) hg, rfl⟩

theorem autSub_autQuot_map_conj {X : Subgroup (MulAut W)} {C : Subgroup W}
    {I : Subgroup (W ⧸ C)} (t₀ : ↥(secStab C I)) :
    autSub (autQuot (X.map (MulAut.conj ((t₀ : stabSub C) : MulAut W)).toMonoidHom) C) I =
      (autSub (autQuot X C) I).map (MulAut.conj (secHom C I t₀)).toMonoidHom := by
  ext ψ
  rw [mem_autSub_autQuot]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨x, hx, hxg⟩ := hg
    refine ⟨secHom C I (t₀⁻¹ * g * t₀), mem_autSub_autQuot.mpr ⟨t₀⁻¹ * g * t₀, ?_, rfl⟩, ?_⟩
    · have e : (((t₀⁻¹ * g * t₀ : ↥(secStab C I)) : stabSub C) : MulAut W) = x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hxg]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      group
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub_autQuot.mp hφ
    refine ⟨t₀ * g * t₀⁻¹, ⟨_, hg, ?_⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem autSub_autQuot_zpowers {C : Subgroup W} {I : Subgroup (W ⧸ C)} (t₀ : ↥(secStab C I)) :
    autSub (autQuot (Subgroup.zpowers ((t₀ : stabSub C) : MulAut W)) C) I =
      Subgroup.zpowers (secHom C I t₀) := by
  ext ψ
  rw [mem_autSub_autQuot]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgk : g = t₀ ^ k := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [Subgroup.coe_zpow, Subgroup.coe_zpow]
      exact hk.symm
    rw [hgk, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  · intro hψ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
    refine ⟨t₀ ^ k, ?_, map_zpow _ _ _⟩
    rw [Subgroup.coe_zpow, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers _ k

theorem autSub_autQuot_commute {X X' : Subgroup (MulAut W)} {C : Subgroup W}
    {I : Subgroup (W ⧸ C)} (h : ∀ x ∈ X, ∀ x' ∈ X', x * x' = x' * x) :
    ∀ φ ∈ autSub (autQuot X C) I, ∀ φ' ∈ autSub (autQuot X' C) I, φ * φ' = φ' * φ := by
  intro φ hφ φ' hφ'
  obtain ⟨g, hg, rfl⟩ := mem_autSub_autQuot.mp hφ
  obtain ⟨g', hg', rfl⟩ := mem_autSub_autQuot.mp hφ'
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subtype.ext (h _ hg _ hg'))

@[expose] def secRes {X : Subgroup (MulAut W)} {C : Subgroup W} {I : Subgroup (W ⧸ C)}
    (hXC : X ≤ stabSub C) (hXS : ∀ x (hx : x ∈ X), (⟨x, hXC hx⟩ : stabSub C) ∈ secStab C I) :
    ↥X →* ↥(autSub (autQuot X C) I) :=
  ((secHom C I).comp ((Subgroup.inclusion hXC).codRestrict (secStab C I)
    fun x => hXS x.1 x.2)).codRestrict (autSub (autQuot X C) I)
    fun x => mem_autSub_autQuot.mpr ⟨_, x.2, rfl⟩

theorem secRes_apply {X : Subgroup (MulAut W)} {C : Subgroup W} {I : Subgroup (W ⧸ C)}
    (hXC : X ≤ stabSub C) (hXS : ∀ x (hx : x ∈ X), (⟨x, hXC hx⟩ : stabSub C) ∈ secStab C I)
    (x : ↥X) (v : ↥I) :
    ((((secRes hXC hXS x : ↥(autSub (autQuot X C) I)) : MulAut ↥I) v : ↥I) : W ⧸ C) =
      quotHom C ⟨x.1, hXC x.2⟩ v := rfl

theorem secRes_surjective {X : Subgroup (MulAut W)} {C : Subgroup W} {I : Subgroup (W ⧸ C)}
    (hXC : X ≤ stabSub C) (hXS : ∀ x (hx : x ∈ X), (⟨x, hXC hx⟩ : stabSub C) ∈ secStab C I) :
    Function.Surjective (secRes hXC hXS) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub_autQuot.mp hψ
  exact ⟨⟨_, hg⟩, rfl⟩

variable [Finite W]

omit [Finite W] in
theorem mem_secStab_of_mem {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {I : Subgroup W} (hI : I ∈ irrSet H) {h : MulAut W}
    (hh : h ∈ H) (hhC : h ∈ stabSub (fixV H)) :
    (⟨h, hhC⟩ : stabSub (fixV H)) ∈ secStab (fixV H) (I.map (QuotientGroup.mk' (fixV H))) := by
  obtain ⟨-, -, hHY, hn, -, -⟩ := h_facts hL hH
  have hHstab : H ≤ stabSub (fixV H) := hHY.trans (le_stabSub_fixV hn)
  exact B1.le_stabSub_of_invariant (map_mk_stable_irr hHstab hI).1
    (mem_autQuot.mpr ⟨_, hh, rfl⟩)

theorem mem_secStab_of_map_eq {C : Subgroup W} {I : Subgroup W} {t : MulAut W}
    (htC : t ∈ stabSub C) (hIt : I.map t.toMonoidHom = I) :
    (⟨t, htC⟩ : stabSub C) ∈ secStab C (I.map (QuotientGroup.mk' C)) := by
  show quotHom C ⟨t, htC⟩ ∈ stabSub (I.map (QuotientGroup.mk' C))
  refine mem_stabSub_of_forall_mem ?_
  rintro _ ⟨i, hi, rfl⟩
  refine ⟨t i, ?_, rfl⟩
  rw [← hIt]
  exact ⟨i, hi, rfl⟩

theorem isQuasisimple_autSub {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {I : Subgroup W} (hI : I ∈ irrSet H)
    (hLI : ¬ commSub I L ≤ fixV H) :
    autSub (autQuot L (fixV H)) (I.map (QuotientGroup.mk' (fixV H))) ≠ ⊥ ∧
      CFSG.Open.IsQuasisimple ↥(autSub (autQuot L (fixV H)) (I.map (QuotientGroup.mk' (fixV H))))
      ∧ dMinDeg ↥L ≤ dMinDeg ↥(autSub (autQuot L (fixV H)) (I.map (QuotientGroup.mk' (fixV H)))) := by
  obtain ⟨-, hLH, hHY, hn, -, -⟩ := h_facts hL hH
  have hLC : L ≤ stabSub (fixV H) := (hLH.trans hHY).trans (le_stabSub_fixV hn)
  have hLS := fun l (hl : l ∈ L) => mem_secStab_of_mem hL hH hI (hLH hl) (hLC hl)
  set C := fixV H with hC
  set I' := I.map (QuotientGroup.mk' C) with hI'
  have hne : autSub (autQuot L C) I' ≠ ⊥ := by
    intro h
    apply hLI
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, i, hi, rfl⟩
    have h1 : secHom C I' ⟨⟨l, hLC hl⟩, hLS l hl⟩ = 1 := by
      have hmem : secHom C I' ⟨⟨l, hLC hl⟩, hLS l hl⟩ ∈ autSub (autQuot L C) I' :=
        mem_autSub_autQuot.mpr ⟨_, hl, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    have h2 := congrArg (fun φ : MulAut ↥I' => ((φ ⟨_, i, hi, rfl⟩ : ↥I') : W ⧸ C)) h1
    simp only [secHom_apply, MulAut.one_apply, QuotientGroup.mk'_apply, quotHom_mk] at h2
    exact (mk_eq_mk_iff _ _).mp h2
  have : Nontrivial ↥(autSub (autQuot L C) I') := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have : Finite (MulAut ↥I') := MulEquiv.finite_left
  refine ⟨hne, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22br4_isQuasisimple_of_surjective hL.2.2
      (secRes hLC hLS) (secRes_surjective hLC hLS)
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.dMinDeg_le_of_surjective (secRes hLC hLS)
      (secRes_surjective hLC hLS)

theorem not_commSub_zpowers_le_of_map_ne {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {t : MulAut W} (ht : t ∈ Y)
    (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) {I : Subgroup W} (hI : I ∈ irrSet H)
    (hIt : I.map t.toMonoidHom = I) (hLI : ¬ commSub I L ≤ fixV H) :
    ¬ commSub I (Subgroup.zpowers t) ≤ fixV H := by
  intro htI
  obtain ⟨-, -, hHY, hn, -, -⟩ := h_facts hL hH
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  have hLtcomp := (conjSet_facts hL hH hLt).1
  have hc := B69.components_mul_comm_of_ne hL hLtcomp (Ne.symm hmove)
  obtain ⟨-, hq, -⟩ := isQuasisimple_autSub hL hH hI hLI
  have htC : t ∈ stabSub (fixV H) := le_stabSub_fixV hn ht
  set C := fixV H with hC
  set t₀ : ↥(secStab C (I.map (QuotientGroup.mk' C))) := ⟨⟨t, htC⟩, mem_secStab_of_map_eq htC hIt⟩
  have ht₁ : secHom C (I.map (QuotientGroup.mk' C)) t₀ = 1 := by
    refine MulEquiv.ext fun v => Subtype.ext ?_
    obtain ⟨i, hi, hiv⟩ := v.2
    rw [secHom_apply, MulAut.one_apply, ← hiv, QuotientGroup.mk'_apply, quotHom_mk,
      mk_eq_mk_iff]
    exact htI (Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, i, hi, rfl⟩)
  have hconj : autSub (autQuot (L.map (MulAut.conj t).toMonoidHom) C) (I.map (QuotientGroup.mk' C))
      = (autSub (autQuot L C) (I.map (QuotientGroup.mk' C))).map
        (MulAut.conj (secHom C (I.map (QuotientGroup.mk' C)) t₀)).toMonoidHom :=
    autSub_autQuot_map_conj t₀
  rw [ht₁] at hconj
  apply not_commute_of_isQuasisimple hq
  intro a ha b hb
  have hb' : b ∈ autSub (autQuot (L.map (MulAut.conj t).toMonoidHom) C)
      (I.map (QuotientGroup.mk' C)) := by
    rw [hconj]
    refine ⟨b, hb, ?_⟩
    simp
  exact autSub_autQuot_commute (fun x hx x' hx' => (hc x' hx' x hx).symm) a ha b hb'

theorem exists_o4_of_map_ne (hD : W4Lem6_3Swap) (hW : ∀ w : W, w ^ 2 = 1)
    {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L)
    (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) {I : Subgroup W} (hI : I ∈ irrSet H)
    (hIt : I.map t.toMonoidHom = I) (hLI : ¬ commSub I L ≤ fixV H) :
    ∃ e : ℕ,
      dMinDeg ↥(autSub (autQuot L (fixV H)) (I.map (QuotientGroup.mk' (fixV H)))) = 2 * e ∧
      IsNaturalO4Plus (autSub (autQuot (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔
        Subgroup.zpowers t) (fixV H)) (I.map (QuotientGroup.mk' (fixV H)))) e ∧
      rkIdx (fixV (autSub (autQuot (Subgroup.zpowers t) (fixV H))
        (I.map (QuotientGroup.mk' (fixV H))))) = e ∧
      ∀ s : ↥(secStab (fixV H) (I.map (QuotientGroup.mk' (fixV H)))), s * s = 1 →
        L.map (MulAut.conj ((s : stabSub (fixV H)) : MulAut W)).toMonoidHom =
          L.map (MulAut.conj t).toMonoidHom →
        rkIdx (fixV (Subgroup.zpowers (secHom (fixV H) (I.map (QuotientGroup.mk' (fixV H))) s))) =
          e →
        secHom (fixV H) (I.map (QuotientGroup.mk' (fixV H))) s ∈
          autSub (autQuot (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) (fixV H))
            (I.map (QuotientGroup.mk' (fixV H))) := by
  have htI := not_commSub_zpowers_le_of_map_ne hL hH ht hmove hI hIt hLI
  obtain ⟨-, hLH, hHY, hn, -, -⟩ := h_facts hL hH
  have hstab : Y ≤ stabSub (fixV H) := le_stabSub_fixV hn
  have hHstab : H ≤ stabSub (fixV H) := hHY.trans hstab
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  obtain ⟨hLtcomp, hLtH, -⟩ := conjSet_facts hL hH hLt
  have huniq : ∀ X ∈ conjSet L Y, X ≠ L → X ≠ L.map (MulAut.conj t).toMonoidHom →
      commSub I X ≤ fixV H := fun X hX hXL hXLt =>
    commSub_le_of_ne_of_ne hW hL hH ht ht2 hm hI hIt hLI htI hX hXL hXLt
  have hcLLt := B69.components_mul_comm_of_ne hL hLtcomp (Ne.symm hmove)
  obtain ⟨hL₁ne, hL₁q, hdL₁⟩ := isQuasisimple_autSub hL hH hI hLI
  have hirrI := map_mk_stable_irr hHstab hI
  have hHS := fun h (hh : h ∈ H) => mem_secStab_of_mem hL hH hI hh (hHstab hh)
  have htC : t ∈ stabSub (fixV H) := hstab ht
  have htS := mem_secStab_of_map_eq htC hIt
  set C := fixV H with hC
  set I' := I.map (QuotientGroup.mk' C) with hI'
  have hI'H : autQuot H C ≤ stabSub I' := B1.le_stabSub_of_invariant hirrI.1
  have hI'ne : I' ≠ ⊥ := by
    intro h
    apply not_le_fixV_of_mem_irrSet hI
    have h2 : I ≤ (QuotientGroup.mk' C).ker := by
      rw [← Subgroup.map_eq_bot_iff, ← hI', h]
    rwa [QuotientGroup.ker_mk'] at h2
  have hV : ∀ v : W ⧸ C, v ^ 2 = 1 := by
    intro v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective C v
    rw [← map_pow, hW, map_one]
  have hV₁ : ∀ v : ↥I', v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV v)
  have : Finite (MulAut ↥I') := MulEquiv.finite_left
  set t₀ : ↥(secStab C I') := ⟨⟨t, htC⟩, htS⟩ with ht₀
  set t₁ := secHom C I' t₀ with ht₁
  set L₁ := autSub (autQuot L C) I' with hL₁
  set L₁t := autSub (autQuot (L.map (MulAut.conj t).toMonoidHom) C) I' with hL₁t
  have hconj : L₁t = L₁.map (MulAut.conj t₁).toMonoidHom := autSub_autQuot_map_conj t₀
  have hT₁ : autSub (autQuot (Subgroup.zpowers t) C) I' = Subgroup.zpowers t₁ :=
    autSub_autQuot_zpowers t₀
  have hcomm₁ : ∀ x ∈ L₁, ∀ y ∈ L₁t, x * y = y * x :=
    autSub_autQuot_commute (fun x hx x' hx' => (hcLLt x' hx' x hx).symm)
  have hLC : L ≤ stabSub C := hLH.trans hHstab
  have hLS : ∀ l (hl : l ∈ L), (⟨l, hLC hl⟩ : stabSub C) ∈ secStab C I' :=
    fun l hl => hHS l (hLH hl)
  have ht0sq : t₀ * t₀ = 1 := by
    have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
    exact Subtype.ext (Subtype.ext ht2')
  have ht₁sq : t₁ * t₁ = 1 := by rw [ht₁, ← map_mul, ht0sq, map_one]
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁sq
  have ht₁ne : t₁ ≠ 1 := by
    intro h1
    apply htI
    have hK : t ∈ secKer I C := by
      refine ⟨?_, fun u hu => ?_⟩
      · intro u
        constructor
        · intro hu
          rw [← hIt] at hu
          obtain ⟨v, hv, hvu⟩ := hu
          have hvu' : t v = t u := hvu
          rwa [← t.injective hvu']
        · intro hu
          rw [← hIt]
          exact ⟨u, hu, rfl⟩
      · have h2 := congrArg (fun φ : MulAut ↥I' => ((φ ⟨_, u, hu, rfl⟩ : ↥I') : W ⧸ C)) h1
        simp only [ht₁, secHom_apply, MulAut.one_apply, QuotientGroup.mk'_apply, quotHom_mk] at h2
        exact (mk_eq_mk_iff _ _).mp h2
    have hle : Subgroup.zpowers t ≤ secKer I C := Subgroup.zpowers_le.mpr hK
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    exact (hle hx).2 u hu
  have ht₁2 : orderOf t₁ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ht₁sq) ht₁ne
  have hrk₁ : rkIdx (fixV (Subgroup.zpowers t₁)) ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    set τ := quotHom C ⟨t, htC⟩ with hτ
    have hτI : τ ∈ stabSub I' := htS
    have hzI : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ I', x w ∈ I' := fun x hx w hw =>
      (((Subgroup.zpowers_le.mpr hτI) hx) w).mpr hw
    have h1 : rk ↥(commV (Subgroup.zpowers t₁)) = rk ↥(commSub I' (Subgroup.zpowers τ)) :=
      rk_commV_resHom hτI hzI
    have h2 : rk ↥(commSub I' (Subgroup.zpowers τ)) ≤ rk ↥(commV (Subgroup.zpowers τ)) := by
      refine rk_mono ?_
      rw [commV_eq_commSub (Subgroup.zpowers τ)]
      exact commSub_mono le_top le_rfl
    have h3 := rk_commV_add_rk_fixV τ
    have h4 := rk_add_rkIdx (fixV (Subgroup.zpowers τ))
    have h5 := rk_commV_add_rk_fixV t₁
    have h6 := rk_add_rkIdx (fixV (Subgroup.zpowers t₁))
    have h7 := rkIdx_fixV_quotHom_le htC
    rw [← hτ] at h7
    omega
  have hmove₁ : L₁.map (MulAut.conj t₁).toMonoidHom ≠ L₁ := by
    rw [← hconj]
    intro h
    apply not_commute_of_isQuasisimple hL₁q
    intro a ha b hb
    exact hcomm₁ a ha b (h ▸ hb)
  have hcommutator₁ : ⁅L₁, L₁.map (MulAut.conj t₁).toMonoidHom⁆ = ⊥ := by
    rw [← hconj, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm₁ x hx y hy).symm
  have hirr₁ : IsIrrOn (L₁ ⊔ L₁.map (MulAut.conj t₁).toMonoidHom) ⊤ ⊥ := by
    rw [← hconj]
    refine ⟨?_, fun _ _ _ _ => trivial, ?_, ?_⟩
    · have : Nontrivial ↥I' := (Subgroup.nontrivial_iff_ne_bot I').mpr hI'ne
      exact bot_lt_top
    · intro x _ u hu
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    · intro J hJ _ _
      set J' := J.map I'.subtype with hJ'
      have hJ'I : J' ≤ I' := by
        rintro _ ⟨v, -, rfl⟩
        exact v.2
      have hgen : ∀ {X : Subgroup (MulAut W)}, X ≤ H → autSub (autQuot X C) I' ≤ L₁ ⊔ L₁t →
          autQuot X C ≤ stabSub J' := by
        intro X hXH hXR
        apply B1.le_stabSub_of_invariant
        intro φ hφ w hw
        obtain ⟨v, hv, rfl⟩ := hw
        have hφI : φ ∈ stabSub I' := hI'H (autQuot_mono hXH C hφ)
        have hres : resHom I' ⟨φ, hφI⟩ ∈ L₁ ⊔ L₁t := hXR (mem_autSub.mpr ⟨⟨φ, hφI⟩, hφ, rfl⟩)
        exact ⟨resHom I' ⟨φ, hφI⟩ v, hJ _ hres v hv, rfl⟩
      have hX : ∀ X ∈ conjSet L Y, autQuot X C ≤ stabSub J' := by
        intro X hX
        obtain ⟨-, hXH, -⟩ := conjSet_facts hL hH hX
        by_cases hXL : X = L
        · rw [hXL]
          exact hgen hLH le_sup_left
        · by_cases hXLt : X = L.map (MulAut.conj t).toMonoidHom
          · rw [hXLt]
            exact hgen hLtH le_sup_right
          · have hXI := huniq X hX hXL hXLt
            refine le_trans ?_ (centSub_le_stabSub J')
            intro φ hφ w hw
            obtain ⟨g, hgX, rfl⟩ := mem_autQuot.mp hφ
            obtain ⟨v, -, rfl⟩ := hw
            obtain ⟨i, hi, hiv⟩ := v.2
            show quotHom C g (v : W ⧸ C) = v
            rw [← hiv, QuotientGroup.mk'_apply, quotHom_mk, mk_eq_mk_iff]
            exact hXI (Subgroup.subset_closure ⟨g.1, hgX, i, hi, rfl⟩)
      have hHJ : autQuot H C ≤ stabSub J' := by
        rw [autQuot_le_iff hHstab, hH]
        refine iSup₂_le fun X hXc => ?_
        obtain ⟨-, hXH, -⟩ := conjSet_facts hL hH hXc
        exact (autQuot_le_iff (hXH.trans hHstab)).mp (hX X hXc)
      rcases hirrI.2 J' (fun φ hφ w hw => ((hHJ hφ) w).mpr hw) hJ'I with h | h
      · left
        rwa [hJ', Subgroup.map_eq_bot_iff_of_injective _ I'.subtype_injective] at h
      · right
        rw [eq_top_iff]
        intro v _
        have hv : (v : W ⧸ C) ∈ J' := by rw [h]; exact v.2
        obtain ⟨v', hv', hv'v⟩ := hv
        rwa [← Subtype.ext hv'v]
  have hdiag₁ : ∀ x ∈ L₁, ∀ w ∈ commV (Subgroup.zpowers t₁), (x * (t₁ * x * t₁⁻¹)) w = w := by
    have hxt : ∀ x ∈ L₁, t₁ * x * t₁⁻¹ ∈ L₁t := fun x hx => by rw [hconj]; exact ⟨x, hx, rfl⟩
    let δ : ↥L₁ →* MulAut ↥I' := MonoidHom.mk'
      (fun x => (x : MulAut ↥I') * (t₁ * (x : MulAut ↥I') * t₁⁻¹)) (by
        intro x y
        have h := hcomm₁ y y.2 _ (hxt x x.2)
        simp only [Subgroup.coe_mul]
        calc (x : MulAut ↥I') * y * (t₁ * (x * y) * t₁⁻¹)
            = x * (y * (t₁ * x * t₁⁻¹)) * (t₁ * y * t₁⁻¹) := by group
          _ = x * ((t₁ * x * t₁⁻¹) * y) * (t₁ * y * t₁⁻¹) := by rw [h]
          _ = x * (t₁ * x * t₁⁻¹) * (y * (t₁ * y * t₁⁻¹)) := by group)
    have hδt : ∀ g ∈ δ.range, g * t₁ = t₁ * g := by
      rintro _ ⟨x, rfl⟩
      have hc := hcomm₁ x x.2 _ (hxt x x.2)
      show (x : MulAut ↥I') * (t₁ * x * t₁⁻¹) * t₁ = t₁ * (x * (t₁ * x * t₁⁻¹))
      rw [ht₁inv] at hc ⊢
      calc (x : MulAut ↥I') * (t₁ * x * t₁) * t₁ = (t₁ * x * t₁) * x * t₁ := by rw [hc]
        _ = t₁ * (x * (t₁ * x * t₁)) := by group
    have hΔS : StableUnder δ.range (commV (Subgroup.zpowers t₁)) := by
      intro g hg w hw
      refine B69.commV_invariant_of_commute (fun s hs => ?_) w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact (Commute.zpow_right (hδt g hg) k).eq
    intro x hx w hw
    by_cases hΔ : δ.range = ⊥
    · have h1 : δ ⟨x, hx⟩ = 1 := by
        have : δ ⟨x, hx⟩ ∈ δ.range := ⟨⟨x, hx⟩, rfl⟩
        rw [hΔ, Subgroup.mem_bot] at this
        exact this
      have h2 : (x * (t₁ * x * t₁⁻¹) : MulAut ↥I') = 1 := h1
      rw [h2]
      rfl
    · have : Nontrivial ↥δ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hΔ
      have hd : dMinDeg ↥L ≤ dMinDeg ↥δ.range :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.dMinDeg_le_of_surjective
          (δ.rangeRestrict.comp (secRes hLC hLS))
          (δ.rangeRestrict_surjective.comp (secRes_surjective hLC hLS))
      have hbot : StableUnder δ.range (⊥ : Subgroup ↥I') := by
        intro y _ u hu
        rw [Subgroup.mem_bot] at hu ⊢
        rw [hu, map_one]
      have h5 := rk_commV_add_rk_fixV t₁
      have h6 := rk_add_rkIdx (fixV (Subgroup.zpowers t₁))
      have hle := Inputs1719.commSub_le_of_rk_lt_dMinDeg hV₁ bot_le hΔS hbot
        (by rw [rk_bot, zero_add]; omega)
      have hmem : (δ ⟨x, hx⟩) w * w⁻¹ ∈ commSub (commV (Subgroup.zpowers t₁)) δ.range :=
        Subgroup.subset_closure ⟨_, MonoidHom.mem_range.mpr ⟨_, rfl⟩, w, hw, rfl⟩
      have h7 := hle hmem
      rw [Subgroup.mem_bot, mul_inv_eq_one] at h7
      exact h7
  rcases hD ↥I' hV₁ L₁ t₁ hL₁q ht₁2 hmove₁ hcommutator₁ hirr₁ hdiag₁ with
    h | ⟨e, hnat, hrke, hde, hsw⟩
  · exfalso
    omega
  · have hR : autSub (autQuot (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) C) I'
        = L₁ ⊔ L₁.map (MulAut.conj t₁).toMonoidHom ⊔ Subgroup.zpowers t₁ := by
      have hHS' : H ≤ (secStab C I').map (stabSub C).subtype := fun h hh =>
        ⟨⟨h, hHstab hh⟩, hHS h hh, rfl⟩
      have htS' : Subgroup.zpowers t ≤ (secStab C I').map (stabSub C).subtype :=
        Subgroup.zpowers_le.mpr ⟨⟨t, htC⟩, htS, rfl⟩
      rw [autSub_autQuot_sup (sup_le (hLH.trans hHS') (hLtH.trans hHS')) htS',
        autSub_autQuot_sup (hLH.trans hHS') (hLtH.trans hHS'), hT₁, ← hconj]
    refine ⟨e, hde, ?_, ?_, ?_⟩
    · rw [hR]
      exact hnat
    · rw [hT₁]
      exact hrke
    · intro s hs2 hLs hrks
      rw [hR]
      have hs2' : secHom C I' s * secHom C I' s = 1 := by rw [← map_mul, hs2, map_one]
      have hLs' : L₁.map (MulAut.conj (secHom C I' s)).toMonoidHom =
          L₁.map (MulAut.conj t₁).toMonoidHom := by
        have h1 : autSub (autQuot (L.map (MulAut.conj ((s : stabSub C) : MulAut W)).toMonoidHom)
            C) I' = L₁.map (MulAut.conj (secHom C I' s)).toMonoidHom := autSub_autQuot_map_conj s
        rw [← h1, hLs, ← hconj]
      exact hsw _ hs2' hLs' hrks

end CFSG.LocalAnalysis.WeakClosure81
