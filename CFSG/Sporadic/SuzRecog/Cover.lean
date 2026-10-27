module

public import CFSG.Sporadic.SuzRecog.NativeType
public import CFSG.Sporadic.SuzRecog.TwistCert
public import CFSG.LieType.Multipliers.U42
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2OmegaPts
public import CFSG.Sporadic.Co1Patterson.TwistModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.LieType.Multipliers CFSG.CosetTable
open scoped commutatorElement

@[expose] noncomputable def cPerm (k : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 (cTab k)

theorem rep_cPerm {k : ℕ} (hk : k < 10) :
    Rep 1782 (cTab k) (cPerm k) :=
  rep_permOK (b0_parts.2.2.2.1 k hk).1

theorem cPerm_mem {k : ℕ}
    (hk : k < 10) : cPerm k ∈ invE 1 := by
  obtain ⟨g, hg, hrep⟩ := rep_gen hk
  rw [(rep_cPerm hk).unique hrep]
  exact subset_closure hg

@[expose] noncomputable def wPerm (w : List ℕ) : Equiv.Perm (Fin 1782) := (w.map cPerm).prod

theorem wPerm_nil : wPerm [] = 1 := rfl

theorem wPerm_cons (k : ℕ) (w : List ℕ) : wPerm (k :: w) = cPerm k * wPerm w := by
  simp [wPerm]

theorem wPerm_mem :
    ∀ {w : List ℕ}, (∀ k ∈ w, k < 10) → wPerm w ∈ invE 1
  | [], _ => one_mem _
  | k :: w, hw => by
    rw [wPerm_cons]
    exact mul_mem (cPerm_mem (hw k List.mem_cons_self))
      (wPerm_mem fun j hj => hw j (List.mem_cons_of_mem k hj))

theorem rep_cWord :
    ∀ {w : List ℕ}, (∀ k ∈ w, k < 10) → Rep 1782 (cWord w) (wPerm w)
  | [], _ => by
    rw [cWord, List.foldr_nil, wPerm_nil]
    exact rep_idTab
  | k :: w, hw => by
    have h := rep_compA (rep_cPerm (hw k List.mem_cons_self))
      (rep_cWord fun j hj => hw j (List.mem_cons_of_mem k hj))
    rw [cWord] at h ⊢
    rw [List.foldr_cons, wPerm_cons]
    exact h

@[expose] noncomputable def wElt
    (w : List ℕ) (hw : ∀ k ∈ w, k < 10) : ↥(invE 1) :=
  ⟨wPerm w, wPerm_mem hw⟩


theorem tabRep_matWord : ∀ {w : List ℕ} (hw : ∀ k ∈ w, k < 10),
    TabRep (matWord w) (kappa (rho1 (wElt w hw)))
  | [], hw => by
    have e : wElt [] hw = 1 := rfl
    rw [e, map_one, map_one, show matWord [] = idTab 64 from rfl]
    exact TabRep.idTab
  | k :: w, hw => by
    have hk : k < 10 := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 10 := fun j hj => hw j (List.mem_cons_of_mem k hj)
    have e : wElt (k :: w) hw = ⟨cPerm k, cPerm_mem hk⟩ * wElt w hw' :=
      Subtype.ext (wPerm_cons k w)
    rw [e, map_mul, map_mul, show matWord (k :: w) = comp 64 matTabs[k]! (matWord w) from rfl]
    exact TabRep.comp (tabRep_gen hk _ (rep_cPerm hk)) (tabRep_matWord hw')

@[expose] noncomputable def kapL : Lm →* Equiv.Perm (Fin 64) := kappa.comp Lm.subtype

theorem kapL_injective : Function.Injective kapL :=
  kappa_injective.comp Subtype.val_injective

theorem kapL_phi0 (c : ↥(invE 1)) : kapL (phi0 c) = kappa (rho1 c) := rfl

@[expose] noncomputable def aL : Lm := phi0 (wElt [1] (by decide))

@[expose] noncomputable def bL : Lm := phi0 (wElt [6, 4] (by decide))

@[expose] noncomputable def gL (i : Fin 2) : Lm := if i = 0 then aL else bL

theorem tabRep_aL : TabRep aTab (kapL aL) := tabRep_matWord (w := [1]) (by decide)

theorem tabRep_bL : TabRep bTab (kapL bL) := tabRep_matWord (w := [6, 4]) (by decide)

theorem abCheck_parts :
    aInv.size = 64 ∧ comp 64 aInv aTab = idTab 64 ∧ bInv.size = 64 ∧
      comp 64 bInv bTab = idTab 64 ∧
      (∀ r ∈ CFSG.LieType.Multipliers.U42.rels, wordTab64 r = idTab 64) ∧
      wordTab64 (commWords (CFSG.LieType.Multipliers.U42.coverPairs 0) ++ [(0, false)]) =
        idTab 64 ∧
      wordTab64 (commWords (CFSG.LieType.Multipliers.U42.coverPairs 1) ++ [(1, false)]) =
        idTab 64 ∧
      genWords.length = 10 ∧ ∀ k < 10, wordTab64 (genWords.getD k []) = matTabs[k]! := by
  have h := twistAB_check
  simp only [abCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, allBelow_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem tabRep_aInv : TabRep aInv (kapL aL)⁻¹ :=
  tabRep_aL.inv abCheck_parts.1 abCheck_parts.2.1

theorem tabRep_bInv : TabRep bInv (kapL bL)⁻¹ :=
  tabRep_bL.inv abCheck_parts.2.2.1 abCheck_parts.2.2.2.1

theorem tabRep_letterTab64 (l : Fin 2 × Bool) :
    TabRep (letterTab64 l) (kapL (cond l.2 (gL l.1) (gL l.1)⁻¹)) := by
  obtain ⟨i, s⟩ := l
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl <;> cases s
  · show TabRep aInv (kapL aL⁻¹)
    rw [map_inv]
    exact tabRep_aInv
  · exact tabRep_aL
  · show TabRep bInv (kapL bL⁻¹)
    rw [map_inv]
    exact tabRep_bInv
  · exact tabRep_bL

theorem tabRep_wordTab64 :
    ∀ v : List (Fin 2 × Bool), TabRep (wordTab64 v) (kapL (FreeGroup.lift gL (FreeGroup.mk v)))
  | [] => by
    rw [show wordTab64 [] = idTab 64 from rfl, show FreeGroup.mk ([] : List (Fin 2 × Bool)) = 1
      from rfl, map_one, map_one]
    exact TabRep.idTab
  | l :: v => by
    rw [show wordTab64 (l :: v) = comp 64 (letterTab64 l) (wordTab64 v) from rfl, FreeGroup.lift_mk,
      List.map_cons, List.prod_cons, map_mul, ← FreeGroup.lift_mk]
    exact TabRep.comp (tabRep_letterTab64 l) (tabRep_wordTab64 v)

theorem lift_eq_one_of_wordTab64 {v : List (Fin 2 × Bool)}
    (h : wordTab64 v = idTab 64) : FreeGroup.lift gL (FreeGroup.mk v) = 1 := by
  apply kapL_injective
  rw [map_one]
  have h1 := tabRep_wordTab64 v
  rw [h] at h1
  exact h1.perm_eq TabRep.idTab

theorem rels_eval {r : List (Fin 2 × Bool)}
    (hr : r ∈ CFSG.LieType.Multipliers.U42.rels) : FreeGroup.lift gL (FreeGroup.mk r) = 1 :=
  lift_eq_one_of_wordTab64 (abCheck_parts.2.2.2.2.1 r hr)

theorem commWords_eval (i : Fin 2) :
    FreeGroup.lift gL (FreeGroup.mk (commWords (CFSG.LieType.Multipliers.U42.coverPairs i))) =
      gL i := by
  have h : wordTab64 (commWords (CFSG.LieType.Multipliers.U42.coverPairs i) ++ [(i, false)]) =
      idTab 64 := by
    fin_cases i
    · exact abCheck_parts.2.2.2.2.2.1
    · exact abCheck_parts.2.2.2.2.2.2.1
  have h1 := lift_eq_one_of_wordTab64 h
  rw [← FreeGroup.mul_mk, map_mul, mul_eq_one_iff_eq_inv] at h1
  rw [h1, FreeGroup.lift_mk]
  simp

theorem closure_range_gL : closure (Set.range gL) = ⊤ := by
  set S₀ : Set (Equiv.Perm (Fin 1782)) := {g | g ∈ (invInnerChain 1).original.toList} with hS₀
  have htop : closure (((↑) : ↥(invE 1) → Equiv.Perm (Fin 1782)) ⁻¹' S₀) = ⊤ :=
    closure_closure_coe_preimage
  have hgen : ∀ c ∈ (((↑) : ↥(invE 1) → Equiv.Perm (Fin 1782)) ⁻¹' S₀),
      phi0 c ∈ closure (Set.range gL) := by
    intro c hc
    obtain ⟨k, hk, hrep⟩ := gen_rep hc
    have hck : c = ⟨cPerm k, cPerm_mem hk⟩ := Subtype.ext (hrep.unique (rep_cPerm hk))
    have hw : kapL (phi0 c) = kapL (FreeGroup.lift gL (FreeGroup.mk (genWords.getD k []))) := by
      have h1 := tabRep_wordTab64 (genWords.getD k [])
      rw [abCheck_parts.2.2.2.2.2.2.2.2 k hk] at h1
      rw [hck, kapL_phi0]
      exact (tabRep_gen hk _ (rep_cPerm hk)).perm_eq h1
    rw [kapL_injective hw, ← FreeGroup.range_lift_eq_closure]
    exact ⟨_, rfl⟩
  rw [eq_top_iff]
  rintro l -
  obtain ⟨c, rfl⟩ := phi0_surjective l
  have hc : c ∈ closure (((↑) : ↥(invE 1) → Equiv.Perm (Fin 1782)) ⁻¹' S₀) := htop ▸ mem_top c
  induction hc using closure_induction with
  | mem c hc => exact hgen c hc
  | one => rw [map_one]; exact one_mem _
  | mul c d _ _ hc hd => rw [map_mul]; exact mul_mem hc hd
  | inv c _ hc => rw [map_inv]; exact inv_mem hc

@[expose] noncomputable def lB : Lm := FreeGroup.lift gL (FreeGroup.mk lBWord)

theorem tabRep_lB : TabRep lBTab (kapL lB) :=
  tabRep_wordTab64 lBWord

theorem relZ_eq : CFSG.LieType.Multipliers.U42.relZ = lBWord ++ lBWord := rfl

theorem relZ_mem : CFSG.LieType.Multipliers.U42.relZ ∈ CFSG.LieType.Multipliers.U42.rels := by
  simp [CFSG.LieType.Multipliers.U42.rels]

theorem lB_mul_self : lB * lB = 1 := by
  have h := rels_eval relZ_mem
  rw [relZ_eq, ← FreeGroup.mul_mk, map_mul] at h
  exact h

abbrev PCov : Type :=
  PG 2 (coverWords CFSG.LieType.Multipliers.U42.rels fun i =>
    commWords (CFSG.LieType.Multipliers.U42.coverPairs i))

theorem pCov_facts :
    Finite PCov ∧ Nat.card PCov ≤ 51840 ∧
      PresentedGroup.mk _ (FreeGroup.mk CFSG.LieType.Multipliers.U42.relZ) ≠ (1 : PCov) := by
  obtain ⟨hfin, hle, hord⟩ := CFSG.LieType.Multipliers.U42.cover_bounds
  refine ⟨hfin, hle, fun h1 => ?_⟩
  change 2 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk CFSG.LieType.Multipliers.U42.relZ) :
    PCov) at hord
  rw [h1, orderOf_one] at hord
  norm_num at hord

theorem toGroup_mk' {α G : Type*} [Group G] {rels : Set (FreeGroup α)} {f : α → G}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (x : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels x) = FreeGroup.lift f x := rfl

theorem eq_on_commutator {F E L : Type*} [Group F] [Group E] [Group L] (π : E →* L)
    (hker : ∀ e, π e = 1 → e ∈ center E) (φ φ' : F →* E) (h : π.comp φ = π.comp φ') {x : F}
    (hx : x ∈ commutator F) : φ x = φ' x := by
  have hc : ∀ y, (φ y)⁻¹ * φ' y ∈ center E := fun y => hker _ <| by
    rw [map_mul, map_inv, ← MonoidHom.comp_apply, h, MonoidHom.comp_apply, inv_mul_cancel]
  have hle : commutator F ≤ MonoidHom.eqLocus φ φ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change φ ⁅a, b⁆ = φ' ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha : φ' a = φ a * ((φ a)⁻¹ * φ' a) := by group
    have hb : φ' b = φ b * ((φ b)⁻¹ * φ' b) := by group
    rw [ha, hb, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc a) (hc b)]
  exact hle hx

theorem sq_eq_of_perfect
    {E : Type*} [Group E] [Finite E] (hE : commutator E = ⊤) (π : E →* Lm)
    (hπ : Function.Surjective π) {ζ : E} (hζc : ζ ∈ center E)
    (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) (hζ1 : ζ ≠ 1) {e : E} (he : π e = lB) :
    e * e = ζ := by
  have hcen : ∀ x, π x = 1 → x ∈ center E := fun x hx => by
    rcases (hker x).1 hx with rfl | rfl
    · exact one_mem _
    · exact hζc
  set eh : Fin 2 → E := fun i => Function.surjInv hπ (gL i) with heh
  have hπeh : π.comp (FreeGroup.lift eh) = FreeGroup.lift gL :=
    FreeGroup.ext_hom _ _ fun i => by simp [heh, Function.surjInv_eq hπ]
  set eg : Fin 2 → E := fun i => FreeGroup.lift eh
    (FreeGroup.mk (commWords (CFSG.LieType.Multipliers.U42.coverPairs i))) with heg
  have hπeg : π.comp (FreeGroup.lift eg) = FreeGroup.lift gL := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, heg]
    change (π.comp (FreeGroup.lift eh)) _ = _
    rw [hπeh, commWords_eval]
  have hπw : ∀ x, π (FreeGroup.lift eg x) = FreeGroup.lift gL x := fun x =>
    DFunLike.congr_fun hπeg x
  have hrel : ∀ r ∈ wordSet (coverWords CFSG.LieType.Multipliers.U42.rels fun i =>
      commWords (CFSG.LieType.Multipliers.U42.coverPairs i)), FreeGroup.lift eg r = 1 := by
    rw [← coverRelators_wordSet]
    refine lift_coverRelators_eq_one_iff.mpr ⟨fun i r hr => ?_, fun i => ?_⟩
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      have hc := hcen _ ((hπw _).trans (rels_eval hr'))
      exact (commutatorElement_eq_one_iff_mul_comm).mpr (mem_center_iff.mp hc _)
    · refine eq_on_commutator π hcen _ _ (hπeg.trans hπeh.symm) (mk_commWords_mem_commutator _)
  set f : PCov →* E := PresentedGroup.toGroup hrel with hf
  have hfs : Function.Surjective f := by
    have : Group.IsPerfect E := ⟨hE⟩
    have hdec : ∀ x : E, ∃ p : PCov, (f p)⁻¹ * x ∈ center E := by
      intro x
      have hx : π x ∈ closure (Set.range gL) := closure_range_gL ▸ mem_top _
      rw [← FreeGroup.range_lift_eq_closure] at hx
      obtain ⟨u, hu⟩ := hx
      refine ⟨PresentedGroup.mk _ u, hcen _ ?_⟩
      rw [map_mul, map_inv, hf, toGroup_mk', hπw, hu, inv_mul_cancel]
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hE, _root_.commutator_def,
      Subgroup.commutator_le]
    intro x₁ _ x₂ _
    obtain ⟨p₁, hp₁⟩ := hdec x₁
    obtain ⟨p₂, hp₂⟩ := hdec x₂
    have e₁ : x₁ = f p₁ * ((f p₁)⁻¹ * x₁) := by group
    have e₂ : x₂ = f p₂ * ((f p₂)⁻¹ * x₂) := by group
    rw [e₁, e₂, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ hp₁ hp₂,
      ← map_commutatorElement]
    exact ⟨_, rfl⟩
  obtain ⟨hPfin, hPle, hz⟩ := pCov_facts
  have hEcard : Nat.card E = 51840 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv,
      CFSG.Sporadic.Co1Patterson.card_ker_eq_two π hker hζ1, Lm,
      Sec2Omega.card_timmesfeldOmega] at h1
    omega
  have hfb : Function.Bijective f := hfs.bijective_of_nat_card_le (by rw [hEcard]; exact hPle)
  set y : E := FreeGroup.lift eg (FreeGroup.mk lBWord) with hy
  have hπy : π y = lB := hπw _
  have hyy : y * y ≠ 1 := by
    intro h1
    apply hz
    apply hfb.1
    rw [map_one, hf, toGroup_mk', relZ_eq, ← FreeGroup.mul_mk, map_mul]
    exact h1
  have hk : π (y⁻¹ * e) = 1 := by rw [map_mul, map_inv, hπy, he, inv_mul_cancel]
  have hkc := hcen _ hk
  have hkk : (y⁻¹ * e) * (y⁻¹ * e) = 1 := by
    rcases (hker _).1 hk with h | h
    · rw [h, mul_one]
    · rw [h]
      rcases (hker (ζ * ζ)).1 (by rw [map_mul, (hker ζ).2 (Or.inr rfl), mul_one]) with h2 | h2
      · exact h2
      · exact absurd (by simpa using h2) hζ1
  have hee : e * e = y * y := by
    have hkc' := mem_center_iff.mp hkc
    calc e * e = y * ((y⁻¹ * e) * y) * (y⁻¹ * e) := by group
      _ = y * (y * (y⁻¹ * e)) * (y⁻¹ * e) := by rw [← hkc' y]
      _ = y * y * ((y⁻¹ * e) * (y⁻¹ * e)) := by group
      _ = y * y := by rw [hkk, mul_one]
  have hπee : π (e * e) = 1 := by rw [map_mul, he, lB_mul_self]
  rcases (hker _).1 hπee with h | h
  · exact absurd (hee ▸ h) hyy
  · exact h

theorem sq_eq_of_conj
    {E : Type*} [Group E] [Finite E] (hE : commutator E = ⊤) (π : E →* Lm)
    (hπ : Function.Surjective π) {ζ : E} (hζc : ζ ∈ center E)
    (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) (hζ1 : ζ ≠ 1) {e : E} {γ : Lm}
    (he : π e * γ = γ * lB) : e * e = ζ := by
  obtain ⟨g, rfl⟩ := hπ γ
  have h1 : π (g⁻¹ * e * g) = lB := by
    rw [map_mul, map_mul, map_inv, mul_assoc, he]
    group
  have h2 := sq_eq_of_perfect hE π hπ hζc hker hζ1 h1
  have h3 : e * e = g * ((g⁻¹ * e * g) * (g⁻¹ * e * g)) * g⁻¹ := by group
  rw [h3, h2, mem_center_iff.mp hζc g, mul_inv_cancel_right]

end CFSG.Sporadic.SuzRecog
