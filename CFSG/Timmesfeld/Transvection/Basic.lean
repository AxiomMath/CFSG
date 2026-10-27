module

public import CFSG.Timmesfeld.Transvection.Defs
public import CFSG.Timmesfeld.ARS.BasicLines

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace Aux

theorem conjSub_conjSub_inv (X : Subgroup G) (g : G) : conjSub (conjSub X g) g⁻¹ = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem commuting_conjSub_iff {X Y : Subgroup G} (g : G) :
    Commuting (conjSub X g) (conjSub Y g) ↔ Commuting X Y := by
  refine ⟨fun h => ?_, fun h => h.conjSub g⟩
  have := h.conjSub g⁻¹
  rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

theorem conjSub_eq_of_commute {H : Subgroup G} {g : G} (hg : ∀ h ∈ H, Commute g h) :
    conjSub H g = H :=
  conjSub_of_forall_commute hg

theorem conjSub_eq_of_conjSub_eq_of_mul_self {X Y : Subgroup G} {w : G} (hw : w * w = 1)
    (h : conjSub X w = Y) : conjSub Y w = X := by
  rw [← h, ← conjSub_mul, hw, conjSub_one]

theorem coxeter_w_sq {c e : G} (hcc : c * c = 1) (hee : e * e = 1) :
    c * e * c * (c * e * c) = 1 := by
  calc c * e * c * (c * e * c) = c * e * (c * c) * e * c := by group
    _ = 1 := by rw [hcc, mul_one, mul_assoc c, hee, mul_one, hcc]

theorem coxeter_sq {a c e : G} (haa : a * a = 1) (hcc : c * c = 1) (hee : e * e = 1) :
    c * e * c * a * (c * e * c) * (c * e * c * a * (c * e * c)) = 1 := by
  calc c * e * c * a * (c * e * c) * (c * e * c * a * (c * e * c)) =
        c * e * c * a * (c * e * c * (c * e * c)) * a * (c * e * c) := by group
    _ = c * e * c * (a * a) * (c * e * c) := by rw [coxeter_w_sq hcc hee]; group
    _ = 1 := by rw [haa, mul_one, coxeter_w_sq hcc hee]

theorem coxeter_conj {a c e : G} (haa : a * a = 1) (hee : e * e = 1) (hcc : c * c = 1)
    (hac : a * c = c * a) (hbra : e * a * e = a * e * a) (hbrc : e * c * e = c * e * c) :
    e * (c * e * c * a * (c * e * c)) * a * (c * e * c * a * (c * e * c) * e) = c := by
  have hcac : c * a * c = a := by rw [← hac, mul_assoc, hcc, mul_one]
  have hu : c * e * c * a * (c * e * c) = c * (e * a * e) * c := by
    calc c * e * c * a * (c * e * c) = c * e * (c * a * c) * e * c := by group
      _ = c * (e * a * e) * c := by rw [hcac]; group
  have hxax : e * a * e * a * (e * a * e) = e := by
    calc e * a * e * a * (e * a * e) = a * e * a * a * (a * e * a) := by rw [hbra]
      _ = a * e * (a * a) * a * e * a := by group
      _ = a * (e * a * e) * a := by rw [haa]; group
      _ = a * (a * e * a) * a := by rw [hbra]
      _ = (a * a) * e * (a * a) := by group
      _ = e := by rw [haa]; group
  calc e * (c * e * c * a * (c * e * c)) * a * (c * e * c * a * (c * e * c) * e) =
        e * (c * (e * a * e) * c) * a * (c * (e * a * e) * c * e) := by rw [hu]
    _ = e * c * (e * a * e * (c * a * c) * (e * a * e)) * c * e := by group
    _ = e * c * (e * a * e * a * (e * a * e)) * c * e := by rw [hcac]
    _ = e * c * e * c * e := by rw [hxax]
    _ = c * e * c * c * e := by rw [hbrc]
    _ = c * e * (c * c) * e := by group
    _ = c := by rw [hcc, mul_one, mul_assoc, hee, mul_one]

end Aux

open Aux

namespace IsTransvectionClass

variable (hΔ : IsTransvectionClass Δ)
include hΔ

theorem mul_self {A : Subgroup G} (hA : A ∈ Δ) {a : G} (ha : a ∈ A) : a * a = 1 :=
  hΔ.root.mul_self A hA a ha

theorem inf_eq_bot (hiso : NoIsolated Δ) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hAB : A ≠ B) : A ⊓ B = ⊥ :=
  ARS.inf_eq_bot hΔ.root hiso hA hB hAB

theorem eq_of_mem_of_mem (hiso : NoIsolated Δ) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) (hx1 : x ≠ 1) : A = B := by
  by_contra hne
  have hx : x ∈ A ⊓ B := ⟨hxA, hxB⟩
  rw [hΔ.inf_eq_bot hiso hA hB hne, Subgroup.mem_bot] at hx
  exact hx1 hx

theorem commuting_of_commute (hiso : NoIsolated Δ) {A B : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ B) (hb1 : b ≠ 1)
    (hab : Commute a b) : Commuting A B := by
  by_cases hAB : A = B
  · subst hAB
    exact hΔ.root.commuting_self hA
  rcases hΔ.commuting_or_opposite hA hB hAB with h | h
  · exact h
  ·
    have hconj : conjSub A b = A := by
      by_contra hne
      have hx : a ∈ conjSub A b := by
        have := conj_mem_conjSub b ha
        rwa [hab.symm.eq, mul_inv_cancel_right] at this
      exact hne (hΔ.eq_of_mem_of_mem hiso (hΔ.root.conjSub_mem hA b) hA hx ha ha1)
    exact absurd (h.symm.eq_one_of_conjSub_eq hb hconj) hb1

end IsTransvectionClass

@[expose] noncomputable def partner (E A : Subgroup G) (e : G) : G :=
  haveI := Classical.propDecidable (Opposite E A ∧ e ∈ E ∧ e ≠ 1)
  if h : Opposite E A ∧ e ∈ E ∧ e ≠ 1 then
    (h.1.existsUnique_conjSub_eq h.2.1 h.2.2).exists.choose
  else 1

section Partner

variable {E A : Subgroup G} (hEA : Opposite E A) {e : G} (he : e ∈ E) (he1 : e ≠ 1)
include hEA he he1

theorem partner_spec : partner E A e ∈ A ∧ conjSub E (partner E A e) = conjSub A e := by
  have h : Opposite E A ∧ e ∈ E ∧ e ≠ 1 := ⟨hEA, he, he1⟩
  unfold partner
  split_ifs
  exact (hEA.existsUnique_conjSub_eq he he1).exists.choose_spec

theorem partner_mem : partner E A e ∈ A := (partner_spec hEA he he1).1

theorem conjSub_partner : conjSub E (partner E A e) = conjSub A e :=
  (partner_spec hEA he he1).2

theorem eq_partner {a : G} (ha : a ∈ A) (hae : conjSub E a = conjSub A e) :
    a = partner E A e :=
  (hEA.existsUnique_conjSub_eq he he1).unique ⟨ha, hae⟩ (partner_spec hEA he he1)

theorem partner_ne_one : partner E A e ≠ 1 := by
  intro h1
  have h := conjSub_partner hEA he he1
  rw [h1, conjSub_one] at h
  have : A = E := by
    rw [← conjSub_conjSub_inv A e, ← h, conjSub_of_mem (E.inv_mem he)]
  exact hEA.ne this.symm

end Partner

theorem partner_braid [Finite G] (hΔ : IsTransvectionClass Δ) {E A : Subgroup G} (hE : E ∈ Δ)
    (hEA : Opposite E A) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    e * partner E A e * e = partner E A e * e * partner E A e :=
  hEA.mul_mul_eq (hΔ.root.mul_self E hE) he he1 (partner_mem hEA he he1)
    (conjSub_partner hEA he he1)

theorem partner_conj {E A : Subgroup G} (hEA : Opposite E A) {e : G} (he : e ∈ E) (he1 : e ≠ 1)
    (g : G) :
    partner (conjSub E g) (conjSub A g) (g * e * g⁻¹) = g * partner E A e * g⁻¹ := by
  have hEA' := hEA.conj g
  have he' : g * e * g⁻¹ ∈ conjSub E g := conj_mem_conjSub g he
  have he1' : g * e * g⁻¹ ≠ 1 := fun h => he1 (conj_eq_one_iff.1 h)
  refine (eq_partner hEA' he' he1' (conj_mem_conjSub g (partner_mem hEA he he1)) ?_).symm
  rw [← conjSub_mul, show g * partner E A e * g⁻¹ * g = g * partner E A e by group,
    conjSub_mul, conjSub_partner hEA he he1, ← conjSub_mul, ← conjSub_mul,
    show g * e * g⁻¹ * g = g * e by group]

theorem partner_conj_of_conjSub_eq {E A : Subgroup G} (hEA : Opposite E A) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) {g : G} (hgE : conjSub E g = E) (hgA : conjSub A g = A) :
    partner E A (g * e * g⁻¹) = g * partner E A e * g⁻¹ := by
  have := partner_conj hEA he he1 g
  rwa [hgE, hgA] at this

theorem eq_of_partner_eq {E A : Subgroup G} (hEA : Opposite E A) {e e' : G} (he : e ∈ E)
    (he1 : e ≠ 1) (he' : e' ∈ E) (he1' : e' ≠ 1) (h : partner E A e = partner E A e') :
    e = e' := by
  have h1 := conjSub_partner hEA he he1
  have h2 := conjSub_partner hEA he' he1'
  rw [h, h2] at h1
  have hn : conjSub A (e⁻¹ * e') = A := by
    rw [conjSub_mul, h1, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have := hEA.eq_one_of_conjSub_eq (E.mul_mem (E.inv_mem he) he') hn
  rw [inv_mul_eq_one] at this
  exact this

theorem commute_of_commute_partner {E A : Subgroup G} (hEA : Opposite E A) {g : G}
    (hgE : conjSub E g = E) (hgA : ∀ a ∈ A, Commute g a) {e : G} (he : e ∈ E) :
    Commute g e := by
  by_cases he1 : e = 1
  · rw [he1]
    exact Commute.one_right g
  have he' : g * e * g⁻¹ ∈ E := by
    rw [← hgE]
    exact conj_mem_conjSub g he
  have he1' : g * e * g⁻¹ ≠ 1 := fun h => he1 (conj_eq_one_iff.1 h)
  have hp := partner_conj_of_conjSub_eq hEA he he1 hgE (conjSub_of_forall_commute hgA)
  rw [(hgA _ (partner_mem hEA he he1)).eq, mul_inv_cancel_right] at hp
  have := eq_of_partner_eq hEA he' he1' he he1 hp
  calc g * e = g * e * g⁻¹ * g := by group
    _ = e * g := by rw [this]

theorem commute_of_commute_mul [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    {X A B : Subgroup G} (hX : X ∈ Δ) (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : A ≠ B)
    (hcAB : Commuting A B) {x a b : G} (hx : x ∈ X) (hx1 : x ≠ 1) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ B) (hc : Commute x (a * b)) : Commute x a := by
  by_contra hxa
  have hXA : X ≠ A := by
    rintro rfl
    exact hxa (hΔ.root.commute hX hx ha)
  have hoXA : Opposite X A :=
    (hΔ.commuting_or_opposite hX hA hXA).resolve_left fun h => hxa (h x hx a ha)
  have hxb : ¬ Commute x b := by
    intro h
    apply hxa
    have : a = a * b * b⁻¹ := by group
    rw [this]
    exact hc.mul_right h.inv_right
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hxb (Commute.one_right x)
  set g := a * b with hg
  have hgA : ∀ a' ∈ A, Commute g a' := fun a' ha' =>
    (hΔ.root.commute hA ha ha').mul_left (hcAB a' ha' b hb).symm
  have hgX : conjSub X g = X := by
    have hx' : x ∈ conjSub X g := by
      have := conj_mem_conjSub g hx
      rwa [hc.symm.eq, mul_inv_cancel_right] at this
    exact hΔ.eq_of_mem_of_mem hiso (hΔ.root.conjSub_mem hX g) hX hx' hx hx1
  have hgX' : ∀ y ∈ X, Commute g y := fun y hy => commute_of_commute_partner hoXA hgX hgA hy
  have hcent : g ∈ Subgroup.centralizer ((A ⊔ X : Subgroup G) : Set G) := by
    have hle : A ⊔ X ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun a' ha' => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact hgA a' ha'
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact hgX' y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.1 (hle hh) g rfl).symm
  have hg1 : g ≠ 1 := by
    intro h1
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hbA : b ∈ A ⊓ B := ⟨hb' ▸ A.inv_mem ha, hb⟩
    rw [hΔ.inf_eq_bot hiso hA hB hAB, Subgroup.mem_bot] at hbA
    exact hb1 hbA
  have hgAX : g ∉ A ⊔ X := fun hgm =>
    hg1 (hoXA.symm.eq_one_of_mem_centralizer (hΔ.root.mul_self A hA) hgm hcent)
  have hgab : g * a = b := by
    rw [hg, mul_assoc, ← (hcAB a ha b hb).eq, ← mul_assoc, hΔ.root.mul_self A hA a ha, one_mul]
  have hroot : g * a ∈ rootElts Δ := ⟨B, hB, hgab ▸ hb, hgab ▸ hb1⟩
  exact ha1 (eq_one_of_mul_mem_rootElts hΔ.root hA hoXA.symm hcent hgAX
    (Subgroup.mem_sup_left ha) hroot)

theorem commute_mul_iff [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    {X A B : Subgroup G} (hX : X ∈ Δ) (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : A ≠ B)
    (hcAB : Commuting A B) {x a b : G} (hx : x ∈ X) (hx1 : x ≠ 1) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ B) (hb1 : b ≠ 1) : Commute x (a * b) ↔ Commute x a ∧ Commute x b := by
  refine ⟨fun hc => ?_, fun h => h.1.mul_right h.2⟩
  have hxa := commute_of_commute_mul hΔ hiso hX hA hB hAB hcAB hx hx1 ha ha1 hb hc
  have hab : a * b = b * a := (hcAB a ha b hb).eq
  have hxb := commute_of_commute_mul hΔ hiso hX hB hA hAB.symm hcAB.symm hx hx1 hb hb1 ha
    (hab ▸ hc)
  exact ⟨hxa, hxb⟩

noncomputable def trElt (A E B : Subgroup G) (e : G) : G :=
  e * (partner E B e * e * partner E B e * partner E A e *
    (partner E B e * e * partner E B e))

section Triangle

variable [Finite G] (hΔ : IsTransvectionClass Δ) {A B E : Subgroup G} {e : G}
include hΔ

omit [Finite G] in
theorem conjSub_wElt (hE : E ∈ Δ) (hEB : Opposite E B) (he : e ∈ E) (he1 : e ≠ 1) :
    conjSub E (partner E B e * e * partner E B e) = B := by
  have hc := partner_mem hEB he he1
  have h1 : conjSub E (partner E B e * e * partner E B e) =
      conjSub (conjSub (conjSub E (partner E B e)) e) (partner E B e) := by
    rw [conjSub_mul, conjSub_mul]
  rw [h1, conjSub_partner hEB he he1, ← conjSub_mul B e e, hΔ.root.mul_self E hE e he,
    conjSub_one, conjSub_of_mem hc]

omit [Finite G] in
theorem commuting_conjSub_wElt (hB : B ∈ Δ) (hE : E ∈ Δ) (hcAB : Commuting A B)
    (hEB : Opposite E B) (he : e ∈ E) (he1 : e ≠ 1) :
    Commuting (conjSub A (partner E B e * e * partner E B e)) E := by
  have hww := Aux.coxeter_w_sq (hΔ.root.mul_self B hB _ (partner_mem hEB he he1))
    (hΔ.root.mul_self E hE e he)
  have h := hcAB.conjSub (partner E B e * e * partner E B e)
  rwa [Aux.conjSub_eq_of_conjSub_eq_of_mul_self hww (conjSub_wElt hΔ hE hEB he he1)] at h

omit [Finite G] in
theorem commute_uElt (hB : B ∈ Δ) (hE : E ∈ Δ) (hcAB : Commuting A B)
    (hEA : Opposite E A) (hEB : Opposite E B) (he : e ∈ E) (he1 : e ≠ 1) {y : G} (hy : y ∈ E) :
    Commute (partner E B e * e * partner E B e * partner E A e *
      (partner E B e * e * partner E B e)) y := by
  have hww := Aux.coxeter_w_sq (hΔ.root.mul_self B hB _ (partner_mem hEB he he1))
    (hΔ.root.mul_self E hE e he)
  have huD : partner E B e * e * partner E B e * partner E A e *
      (partner E B e * e * partner E B e) ∈
      conjSub A (partner E B e * e * partner E B e) := by
    have := conj_mem_conjSub (partner E B e * e * partner E B e) (partner_mem hEA he he1)
    rwa [inv_eq_of_mul_eq_one_right hww] at this
  exact commuting_conjSub_wElt hΔ hB hE hcAB hEB he he1 _ huD y hy

omit [Finite G] in
theorem commute_trElt (hB : B ∈ Δ) (hE : E ∈ Δ) (hcAB : Commuting A B)
    (hEA : Opposite E A) (hEB : Opposite E B) (he : e ∈ E) (he1 : e ≠ 1) {y : G} (hy : y ∈ E) :
    Commute (trElt A E B e) y :=
  (hΔ.root.commute hE he hy).mul_left (commute_uElt hΔ hB hE hcAB hEA hEB he he1 hy)

theorem trElt_spec (hA : A ∈ Δ) (hB : B ∈ Δ) (hE : E ∈ Δ) (hcAB : Commuting A B)
    (hEA : Opposite E A) (hEB : Opposite E B) (he : e ∈ E) (he1 : e ≠ 1) :
    trElt A E B e * trElt A E B e = 1 ∧
      trElt A E B e * partner E A e * (trElt A E B e)⁻¹ = partner E B e := by
  have ha := partner_mem hEA he he1
  have hc := partner_mem hEB he he1
  have haa : partner E A e * partner E A e = 1 := hΔ.root.mul_self A hA _ ha
  have hcc : partner E B e * partner E B e = 1 := hΔ.root.mul_self B hB _ hc
  have hee : e * e = 1 := hΔ.root.mul_self E hE e he
  have hac := (hcAB _ ha _ hc).eq
  have hbra := partner_braid hΔ hE hEA he he1
  have hbrc := partner_braid hΔ hE hEB he he1
  have huu := Aux.coxeter_sq haa hcc hee
  have hue := (commute_uElt hΔ hB hE hcAB hEA hEB he he1 he).eq
  have htinv : (trElt A E B e)⁻¹ = partner E B e * e * partner E B e * partner E A e *
      (partner E B e * e * partner E B e) * e := by
    rw [trElt, mul_inv_rev, inv_eq_of_mul_eq_one_right huu, inv_eq_of_mul_eq_one_right hee]
  refine ⟨?_, ?_⟩
  · rw [trElt]
    calc e * (partner E B e * e * partner E B e * partner E A e *
            (partner E B e * e * partner E B e)) *
          (e * (partner E B e * e * partner E B e * partner E A e *
            (partner E B e * e * partner E B e))) =
        e * ((partner E B e * e * partner E B e * partner E A e *
            (partner E B e * e * partner E B e)) * e) *
          (partner E B e * e * partner E B e * partner E A e *
            (partner E B e * e * partner E B e)) := by group
      _ = e * e * ((partner E B e * e * partner E B e * partner E A e *
            (partner E B e * e * partner E B e)) *
          (partner E B e * e * partner E B e * partner E A e *
            (partner E B e * e * partner E B e))) := by rw [hue]; group
      _ = 1 := by rw [hee, huu, one_mul]
  · rw [htinv, trElt]
    exact Aux.coxeter_conj haa hee hcc hac hbra hbrc

theorem conjSub_trElt (hiso : NoIsolated Δ) (hA : A ∈ Δ) (hB : B ∈ Δ) (hE : E ∈ Δ)
    (hcAB : Commuting A B) (hEA : Opposite E A) (hEB : Opposite E B) (he : e ∈ E)
    (he1 : e ≠ 1) : conjSub A (trElt A E B e) = B := by
  obtain ⟨-, hconj⟩ := trElt_spec hΔ hA hB hE hcAB hEA hEB he he1
  have hmem : partner E B e ∈ conjSub A (trElt A E B e) := by
    rw [← hconj]
    exact conj_mem_conjSub _ (partner_mem hEA he he1)
  exact hΔ.eq_of_mem_of_mem hiso (hΔ.root.conjSub_mem hA _) hB hmem (partner_mem hEB he he1)
    (partner_ne_one hEB he he1)

end Triangle

end CFSG.Timmesfeld.Transvection
