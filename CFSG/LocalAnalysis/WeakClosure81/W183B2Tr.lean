module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2TrAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem w183b2_card_ge_of_mOf {D B : Subgroup (LGL 2 V)} (hB : B ≤ D)
    (h : 3 ≤ mOf D B) : 8 ≤ Nat.card D := by
  have hcard : 0 < Nat.card ↥D := Finite.card_pos_iff.2 ⟨⟨1, D.one_mem⟩⟩
  have h1 : (B.subgroupOf D).index ≤ Nat.card ↥D :=
    Nat.le_of_dvd hcard (Subgroup.index_dvd_card (H := B.subgroupOf D))
  have h2 : 3 ≤ Nat.log 2 (Nat.card ↥D) := le_trans h (Nat.log_mono_right h1)
  have h3 : 2 ^ 3 ≤ Nat.card ↥D := Nat.pow_le_of_le_log hcard.ne' h2
  norm_num at h3 ⊢
  exact h3

theorem w183b2_no_mixed_section_of_quasi
    {L₁ L₂ D : Subgroup (LGL 2 V)} (hq₁ : CFSG.Open.IsQuasisimple ↥L₁)
    (hq₂ : CFSG.Open.IsQuasisimple ↥L₂) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hD₁ : ∀ d ∈ D, ∀ a ∈ L₁, d * a * d⁻¹ ∈ L₁) (hD₂ : ∀ d ∈ D, ∀ b ∈ L₂, d * b * d⁻¹ ∈ L₂)
    (hDe : IsElemAbelian 2 D) (hDq : commSpace D (commSub D) = ⊥)
    (hcent : ∀ d ∈ D, (∀ a ∈ L₁, d * a = a * d) → (∀ b ∈ L₂, d * b = b * d) → d = 1)
    (hDn₁ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hDn₂ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
    (hrk : 3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))))
    (hAbs : AbsIrrOverF4 ↥L₁)
    {R' R : Submodule (ZMod 2) V} (hlt : R' < R)
    (hR'₁ : ∀ l ∈ L₁, ∀ u ∈ R', l u ∈ R') (hR'₂ : ∀ l ∈ L₂, ∀ u ∈ R', l u ∈ R')
    (hR'D : ∀ d ∈ D, ∀ u ∈ R', d u ∈ R')
    (hR₁ : ∀ l ∈ L₁, ∀ u ∈ R, l u ∈ R) (hR₂ : ∀ l ∈ L₂, ∀ u ∈ R, l u ∈ R)
    (hRD : ∀ d ∈ D, ∀ u ∈ R, d u ∈ R)
    (hirr : ∀ W : Submodule (ZMod 2) V, R' ≤ W → W ≤ R →
      (∀ l ∈ L₁, ∀ u ∈ W, l u ∈ W) → (∀ l ∈ L₂, ∀ u ∈ W, l u ∈ W) →
      (∀ d ∈ D, ∀ u ∈ W, d u ∈ W) → W = R' ∨ W = R) :
    commSpace L₁ R ≤ R' ∨ commSpace L₂ R ≤ R' := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnot₁, hnot₂⟩ := hcon
  let Gs : Subgroup (LGL 2 V) := L₁ ⊔ L₂ ⊔ D
  let A₁ : Subgroup ↥Gs := L₁.subgroupOf Gs
  let A₂ : Subgroup ↥Gs := L₂.subgroupOf Gs
  let Δ : Subgroup ↥Gs := D.subgroupOf Gs
  have hL₁Gs : L₁ ≤ Gs := le_sup_left.trans le_sup_left
  have hL₂Gs : L₂ ≤ Gs := le_sup_right.trans le_sup_left
  have hL₁₂Gs : L₁ ⊔ L₂ ≤ Gs := le_sup_left
  have hDGs : D ≤ Gs := le_sup_right
  let Stab : Subgroup (LGL 2 V) :=
    { carrier := {g | (∀ u ∈ R, g u ∈ R) ∧ (∀ u ∈ R, g⁻¹ u ∈ R) ∧
                      (∀ u ∈ R', g u ∈ R') ∧ (∀ u ∈ R', g⁻¹ u ∈ R')}
      mul_mem' := by
        rintro g h ⟨hgR, hgRi, hgR', hgR'i⟩ ⟨hhR, hhRi, hhR', hhR'i⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro u hu
          exact hgR _ (hhR u hu)
        · intro u hu
          have h2 : h⁻¹ (g⁻¹ u) ∈ R := hhRi _ (hgRi u hu)
          simpa [mul_inv_rev] using h2
        · intro u hu
          exact hgR' _ (hhR' u hu)
        · intro u hu
          have h2 : h⁻¹ (g⁻¹ u) ∈ R' := hhR'i _ (hgR'i u hu)
          simpa [mul_inv_rev] using h2
      one_mem' := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu <;> simpa using hu
      inv_mem' := by
        rintro g ⟨hgR, hgRi, hgR', hgR'i⟩
        refine ⟨hgRi, ?_, hgR'i, ?_⟩
        · intro u hu
          simpa using hgR u hu
        · intro u hu
          simpa using hgR' u hu }
  have hL₁Stab : L₁ ≤ Stab := by
    intro l hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hR₁ l hl
    · intro u hu
      exact hR₁ l⁻¹ (L₁.inv_mem hl) u hu
    · exact hR'₁ l hl
    · intro u hu
      exact hR'₁ l⁻¹ (L₁.inv_mem hl) u hu
  have hL₂Stab : L₂ ≤ Stab := by
    intro l hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hR₂ l hl
    · intro u hu
      exact hR₂ l⁻¹ (L₂.inv_mem hl) u hu
    · exact hR'₂ l hl
    · intro u hu
      exact hR'₂ l⁻¹ (L₂.inv_mem hl) u hu
  have hDStab : D ≤ Stab := by
    intro d hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hRD d hd
    · intro u hu
      exact hRD d⁻¹ (D.inv_mem hd) u hu
    · exact hR'D d hd
    · intro u hu
      exact hR'D d⁻¹ (D.inv_mem hd) u hu
  have hGsStab : Gs ≤ Stab := sup_le (sup_le hL₁Stab hL₂Stab) hDStab
  have hRinv : ∀ g ∈ Gs, ∀ u ∈ R, g u ∈ R := fun g hg => (hGsStab hg).1
  have hR'inv : ∀ g ∈ Gs, ∀ u ∈ R', g u ∈ R' := fun g hg => (hGsStab hg).2.2.1
  let stdRep : Representation (ZMod 2) ↥Gs V :=
    { toFun := fun g => (g : LGL 2 V)
      map_one' := by ext x; rfl
      map_mul' := by intro g h; ext x; rfl }
  let Rsub : Subrepresentation stdRep :=
    { toSubmodule := R
      apply_mem_toSubmodule := fun g x hx => hRinv g g.2 x hx }
  let ρ_R : Representation (ZMod 2) ↥Gs ↥R := Rsub.toRepresentation
  let p : Submodule (ZMod 2) ↥R := R'.comap R.subtype
  let R'sub_R : Subrepresentation ρ_R :=
    { toSubmodule := p
      apply_mem_toSubmodule := fun g x hx => by
        show (ρ_R g x : V) ∈ R'
        exact hR'inv g g.2 x.1 hx }
  let ρ : Representation (ZMod 2) ↥Gs (↥R ⧸ p) := R'sub_R.quotient
  haveI : Finite (↥R ⧸ p) := Quotient.finite (Submodule.quotientRel p)
  have hqd : ∀ (g : ↥Gs) (x : ↥R), ρ g (Submodule.mkQ p x) = Submodule.mkQ p (ρ_R g x) :=
    fun g x => Subrepresentation.quotient_apply_mk R'sub_R g x
  have hρirr : ρ.IsIrreducible := by
    rw [ComponentInitial.PairedTensorOrbits.isIrreducible_iff]
    refine ⟨?_, ?_⟩
    · rw [Submodule.Quotient.nontrivial_iff]
      intro htop
      have hle : R ≤ R' := fun x hx => by
        have hx' : (⟨x, hx⟩ : ↥R) ∈ p := by rw [htop]; trivial
        exact hx'
      exact (not_le_of_gt hlt) hle
    · intro U hU
      let W' : Submodule (ZMod 2) V := (U.comap (Submodule.mkQ p)).map R.subtype
      have hR'W' : R' ≤ W' := by
        intro u hu
        have huR : u ∈ R := hlt.le hu
        refine Submodule.mem_map.mpr ⟨⟨u, huR⟩, ?_, rfl⟩
        rw [Submodule.mem_comap]
        have hzero : Submodule.mkQ p ⟨u, huR⟩ = 0 :=
          (Submodule.Quotient.mk_eq_zero p).mpr (Submodule.mem_comap.mpr hu)
        rw [hzero]
        exact U.zero_mem
      have hW'R : W' ≤ R := by
        rintro x ⟨y, -, rfl⟩
        exact y.2
      have hW'₁ : ∀ l ∈ L₁, ∀ u ∈ W', l u ∈ W' := by
        intro l hl u hu
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hu
        have hL : l ∈ Gs := hL₁Gs hl
        refine Submodule.mem_map.mpr ⟨ρ_R ⟨l, hL⟩ y, ?_, rfl⟩
        rw [Submodule.mem_comap, ← hqd ⟨l, hL⟩ y]
        exact hU ⟨l, hL⟩ (Submodule.mkQ p y) (Submodule.mem_comap.mp hy)
      have hW'₂ : ∀ l ∈ L₂, ∀ u ∈ W', l u ∈ W' := by
        intro l hl u hu
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hu
        have hL : l ∈ Gs := hL₂Gs hl
        refine Submodule.mem_map.mpr ⟨ρ_R ⟨l, hL⟩ y, ?_, rfl⟩
        rw [Submodule.mem_comap, ← hqd ⟨l, hL⟩ y]
        exact hU ⟨l, hL⟩ (Submodule.mkQ p y) (Submodule.mem_comap.mp hy)
      have hW'D : ∀ d ∈ D, ∀ u ∈ W', d u ∈ W' := by
        intro d hd u hu
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hu
        have hD : d ∈ Gs := hDGs hd
        refine Submodule.mem_map.mpr ⟨ρ_R ⟨d, hD⟩ y, ?_, rfl⟩
        rw [Submodule.mem_comap, ← hqd ⟨d, hD⟩ y]
        exact hU ⟨d, hD⟩ (Submodule.mkQ p y) (Submodule.mem_comap.mp hy)
      rcases hirr W' hR'W' hW'R hW'₁ hW'₂ hW'D with h | h
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p y
        have hx : x ∈ U.comap (Submodule.mkQ p) := Submodule.mem_comap.mpr hy
        have hxR' : (x : V) ∈ R' := by
          have hxW' : R.subtype x ∈ W' := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
          rw [h] at hxW'
          exact hxW'
        rw [Submodule.mem_bot]
        exact (Submodule.Quotient.mk_eq_zero p).mpr hxR'
      · right
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p y
        have hx : x ∈ U.comap (Submodule.mkQ p) := by
          have hxR : R.subtype x ∈ W' := by rw [h]; exact x.2
          obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hxR
          have hzx' : z = x := Subtype.ext hzx
          rwa [hzx'] at hz
        exact Submodule.mem_comap.mp hx
  have hgen : A₁ ⊔ A₂ ⊔ Δ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hL₁Gs hL₂Gs, ← Subgroup.subgroupOf_sup hL₁₂Gs hDGs]
    exact Subgroup.subgroupOf_self Gs
  have hcomm' : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hcomm a.1 (Subgroup.mem_subgroupOf.mp ha) b.1
      (Subgroup.mem_subgroupOf.mp hb))
  have hn₁' : ∀ d ∈ Δ, ∀ a ∈ A₁, d * a * d⁻¹ ∈ A₁ := by
    intro d hd a ha
    exact Subgroup.mem_subgroupOf.mpr
      (hD₁ d.1 (Subgroup.mem_subgroupOf.mp hd) a.1 (Subgroup.mem_subgroupOf.mp ha))
  have hn₂' : ∀ d ∈ Δ, ∀ b ∈ A₂, d * b * d⁻¹ ∈ A₂ := by
    intro d hd b hb
    exact Subgroup.mem_subgroupOf.mpr
      (hD₂ d.1 (Subgroup.mem_subgroupOf.mp hd) b.1 (Subgroup.mem_subgroupOf.mp hb))
  have helem' : IsElemAbelian 2 Δ := by
    let e := Subgroup.subgroupOfEquivOfLe hDGs
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro x y
      exact e.injective (by
        rw [map_mul, map_mul]
        exact isMulCommutative_iff.mp hDe.1 (e x) (e y))
    · intro x hx
      apply Subtype.ext
      exact hDe.2 (e ⟨x, hx⟩) (e ⟨x, hx⟩).2
  have hquad' : ∀ d ∈ Δ, ∀ d' ∈ Δ, ∀ w : ↥R ⧸ p,
      ρ d (ρ d' w - w) = ρ d' w - w := by
    intro d hd d' hd' w
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p w
    have hdD : (d : LGL 2 V) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hd'D : (d' : LGL 2 V) ∈ D := Subgroup.mem_subgroupOf.mp hd'
    have hquadV : ∀ v : V,
        (d : LGL 2 V) ((d' : LGL 2 V) v - v) = (d' : LGL 2 V) v - v := by
      intro v
      exact (commSpace_eq_bot_iff.mp hDq) (d : LGL 2 V) hdD ((d' : LGL 2 V) v - v)
        (by
          rw [← commSpace_top_eq_commSub]
          exact sub_mem_commSpace hd'D Submodule.mem_top)
    have h1 : ρ_R d (ρ_R d' x) - ρ_R d x = ρ_R d' x - x := by
      apply Subtype.ext
      show (d : LGL 2 V) ((d' : LGL 2 V) x.1) - (d : LGL 2 V) x.1
        = (d' : LGL 2 V) x.1 - x.1
      rw [← map_sub]
      exact hquadV x.1
    have h3 : ρ_R d (ρ_R d' x - x) = ρ_R d' x - x := by
      rw [map_sub]
      exact h1
    have hd'x : Submodule.mkQ p (ρ_R d' x - x)
        = Submodule.mkQ p (ρ_R d' x) - Submodule.mkQ p x :=
      (Submodule.mkQ p).map_sub _ _
    rw [hqd d' x, ← hd'x, hqd d (ρ_R d' x - x), h3]
  have hnt₁' : ∃ a ∈ A₁, ∃ w : ↥R ⧸ p, ρ a w ≠ w := by
    rw [commSpace_le_iff] at hnot₁
    obtain ⟨l, hnot⟩ := not_forall.mp hnot₁
    rw [not_imp] at hnot
    obtain ⟨hl, hnot⟩ := hnot
    obtain ⟨u, hnot⟩ := not_forall.mp hnot
    rw [not_imp] at hnot
    obtain ⟨hu, hnotu⟩ := hnot
    have hL : l ∈ Gs := hL₁Gs hl
    refine ⟨⟨l, hL⟩, Subgroup.mem_subgroupOf.mpr hl, Submodule.mkQ p ⟨u, hu⟩, ?_⟩
    intro heq
    apply hnotu
    have h2 : Submodule.mkQ p (ρ_R ⟨l, hL⟩ ⟨u, hu⟩) = Submodule.mkQ p ⟨u, hu⟩ := by
      rw [← hqd ⟨l, hL⟩ ⟨u, hu⟩]
      exact heq
    have hmem : ρ_R ⟨l, hL⟩ ⟨u, hu⟩ - ⟨u, hu⟩ ∈ p := (Submodule.Quotient.eq p).mp h2
    have hmem' : (ρ_R ⟨l, hL⟩ ⟨u, hu⟩ : V) - u ∈ R' := by
      simpa using Submodule.mem_comap.mp hmem
    have hval : (ρ_R ⟨l, hL⟩ ⟨u, hu⟩ : V) = l u := rfl
    rwa [hval] at hmem'
  have hnt₂' : ∃ a ∈ A₂, ∃ w : ↥R ⧸ p, ρ a w ≠ w := by
    rw [commSpace_le_iff] at hnot₂
    obtain ⟨l, hnot⟩ := not_forall.mp hnot₂
    rw [not_imp] at hnot
    obtain ⟨hl, hnot⟩ := hnot
    obtain ⟨u, hnot⟩ := not_forall.mp hnot
    rw [not_imp] at hnot
    obtain ⟨hu, hnotu⟩ := hnot
    have hL : l ∈ Gs := hL₂Gs hl
    refine ⟨⟨l, hL⟩, Subgroup.mem_subgroupOf.mpr hl, Submodule.mkQ p ⟨u, hu⟩, ?_⟩
    intro heq
    apply hnotu
    have h2 : Submodule.mkQ p (ρ_R ⟨l, hL⟩ ⟨u, hu⟩) = Submodule.mkQ p ⟨u, hu⟩ := by
      rw [← hqd ⟨l, hL⟩ ⟨u, hu⟩]
      exact heq
    have hmem : ρ_R ⟨l, hL⟩ ⟨u, hu⟩ - ⟨u, hu⟩ ∈ p := (Submodule.Quotient.eq p).mp h2
    have hmem' : (ρ_R ⟨l, hL⟩ ⟨u, hu⟩ : V) - u ∈ R' := by
      simpa using Submodule.mem_comap.mp hmem
    have hval : (ρ_R ⟨l, hL⟩ ⟨u, hu⟩ : V) = l u := rfl
    rwa [hval] at hmem'
  have hq₁' : CFSG.Open.IsQuasisimple ↥A₁ :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hL₁Gs) hq₁
  have hq₂' : CFSG.Open.IsQuasisimple ↥A₂ :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hL₂Gs) hq₂
  have hAbs' : AbsIrrOverF4 ↥A₁ :=
    w183b2_absIrrOverF4_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL₁Gs) hAbs
  have hcent' : ∀ d ∈ Δ, (∀ a ∈ A₁, d * a = a * d) →
      (∀ b ∈ A₂, d * b = b * d) → d = 1 := by
    intro d hd h1 h2
    apply Subtype.ext
    exact hcent d.1 (Subgroup.mem_subgroupOf.mp hd)
      (fun a ha => by
        have h := congrArg Subtype.val
          (h1 ⟨a, hL₁Gs ha⟩ (Subgroup.mem_subgroupOf.mpr ha))
        simpa using h)
      (fun b hb => by
        have h := congrArg Subtype.val
          (h2 ⟨b, hL₂Gs hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
        simpa using h)
  have htwo₁' : ¬ Δ ≤ Subgroup.centralizer (A₂ : Set ↥Gs) := by
    intro hle
    apply hDn₁
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hd' : (⟨d, hDGs hd⟩ : ↥Gs) ∈ Subgroup.centralizer (A₂ : Set ↥Gs) := hle hd
    have hbA₂ : (⟨b, hL₂Gs hb⟩ : ↥Gs) ∈ A₂ := Subgroup.mem_subgroupOf.mpr hb
    have h := (Subgroup.mem_centralizer_iff.mp hd') ⟨b, hL₂Gs hb⟩ hbA₂
    exact congrArg Subtype.val h
  have htwo₂' : ¬ Δ ≤ Subgroup.centralizer (A₁ : Set ↥Gs) := by
    intro hle
    apply hDn₂
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hd' : (⟨d, hDGs hd⟩ : ↥Gs) ∈ Subgroup.centralizer (A₁ : Set ↥Gs) := hle hd
    have haA₁ : (⟨a, hL₁Gs ha⟩ : ↥Gs) ∈ A₁ := Subgroup.mem_subgroupOf.mpr ha
    have h := (Subgroup.mem_centralizer_iff.mp hd') ⟨a, hL₁Gs ha⟩ haA₁
    exact congrArg Subtype.val h
  have hcard_le : Nat.card ↥Δ ≤ 4 :=
    w183b2_no_mixed_abstract_of_quasi ρ hρirr hgen hcomm' hn₁' hn₂' helem' hquad'
      hq₁' hq₂' hnt₁' hnt₂' hcent' htwo₁' htwo₂' hAbs'
  have hcard_eq : Nat.card ↥Δ = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDGs).toEquiv
  rcases hrk with hrk | hrk
  · have h8 : 8 ≤ Nat.card ↥D := w183b2_card_ge_of_mOf inf_le_left hrk
    omega
  · have h8 : 8 ≤ Nat.card ↥D := w183b2_card_ge_of_mOf inf_le_left hrk
    omega

end CFSG.LocalAnalysis.WeakClosure81

end
