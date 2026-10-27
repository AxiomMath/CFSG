module

public import CFSG.Timmesfeld.Transvection.Triangle

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

structure IsTriangle (Δ : Set (Subgroup G)) (A E B : Subgroup G) : Prop where
  memA : A ∈ Δ
  memE : E ∈ Δ
  memB : B ∈ Δ
  ne : A ≠ B
  comm : Commuting A B
  oppA : Opposite E A
  oppB : Opposite E B

theorem IsTriangle.swap {A E B : Subgroup G} (h : IsTriangle Δ A E B) : IsTriangle Δ B E A :=
  ⟨h.memB, h.memE, h.memA, h.ne.symm, h.comm.symm, h.oppB, h.oppA⟩

theorem Opposite.conjSub_eq_or_eq_conjSub {P Q : Subgroup G} (hsq : ∀ a ∈ P, a * a = 1)
    (h : Opposite P Q) {x : G} (hx : x ∈ P ⊔ Q) :
    conjSub P x = P ∨ ∃ y ∈ P, conjSub P x = conjSub Q y := by
  have hr := h.isElemAbRankOne_of_mul_self hsq
  rcases hr.map_conj_cases ⟨x, hx⟩ with h1 | ⟨y, hy, h2⟩
  · left
    rw [map_conj_subgroupOf_mk hx] at h1
    exact (subgroupOf_inj_of_le (Opposite.conjSub_le_sup hx) le_sup_left).1 h1
  · right
    refine ⟨y, Subgroup.mem_subgroupOf.1 hy, ?_⟩
    rw [map_conj_subgroupOf_mk hx, map_conj_subgroupOf] at h2
    exact (subgroupOf_inj_of_le (Opposite.conjSub_le_sup hx)
      (conjSub_le le_sup_right y.2)).1 h2

theorem conjSub_eq_or_conjSub_eq (hΔ : IsTransvectionClass Δ) {A E : Subgroup G}
    (hE : E ∈ Δ) (hEA : Opposite E A) {x : G} (hx : x ∈ A ⊔ E) :
    conjSub A x = E ∨ ∃ e ∈ E, conjSub A x = conjSub A e := by
  obtain ⟨e₁, he₁, he₁1⟩ := hΔ.root.exists_ne_one hE
  have ha₁ : partner E A e₁ ∈ A := partner_mem hEA he₁ he₁1
  have hAE : A = conjSub E (e₁⁻¹ * partner E A e₁) := by
    rw [conjSub_mul, conjSub_partner hEA he₁ he₁1, Aux.conjSub_conjSub_inv]
  have hg : x * (e₁⁻¹ * partner E A e₁) ∈ E ⊔ A := by
    rw [sup_comm] at hx
    exact Subgroup.mul_mem _ hx (Subgroup.mul_mem _ (Subgroup.mem_sup_left (E.inv_mem he₁))
      (Subgroup.mem_sup_right ha₁))
  have hconj : conjSub A x = conjSub E (x * (e₁⁻¹ * partner E A e₁)) := by
    conv_lhs => rw [hAE]
    rw [← conjSub_mul]
  rw [hconj]
  exact Opposite.conjSub_eq_or_eq_conjSub (hΔ.root.mul_self E hE) hEA hg

theorem commute_of_mem_graph (hΔ : IsTransvectionClass Δ) {A E B : Subgroup G}
    (hT : IsTriangle Δ A E B) {t : G} (htA : conjSub A t = B) {f : G} (hf : f ∈ graph A t)
    {y : G} (hy : y ∈ A ∨ y ∈ B) : Commute f y := by
  have hAg : Commuting A (conjSub A t) := htA ▸ hT.comm
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff hAg).1 hf
  have hb : t * a * t⁻¹ ∈ B := htA ▸ conj_mem_conjSub t ha
  rcases hy with hy | hy
  · exact (hΔ.root.commute hT.memA ha hy).mul_left (hT.comm y hy _ hb).symm
  · exact (hT.comm a ha y hy).mul_left (hΔ.root.commute hT.memB hb hy)

theorem mul_self_of_mem_graph (hΔ : IsTransvectionClass Δ) {A E B : Subgroup G}
    (hT : IsTriangle Δ A E B) {t : G} (htA : conjSub A t = B) {f : G} (hf : f ∈ graph A t) :
    f * f = 1 := by
  have hAg : Commuting A (conjSub A t) := htA ▸ hT.comm
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff hAg).1 hf
  have hb : t * a * t⁻¹ ∈ B := htA ▸ conj_mem_conjSub t ha
  have hc : Commute a (t * a * t⁻¹) := hT.comm a ha _ hb
  calc a * (t * a * t⁻¹) * (a * (t * a * t⁻¹)) = a * (t * a * t⁻¹ * a) * (t * a * t⁻¹) := by
        group
    _ = a * (a * (t * a * t⁻¹)) * (t * a * t⁻¹) := by rw [hc.symm.eq]
    _ = (a * a) * ((t * a * t⁻¹) * (t * a * t⁻¹)) := by group
    _ = 1 := by rw [hΔ.mul_self hT.memA ha, hΔ.mul_self hT.memB hb, one_mul]

theorem commuting_conjSub_commutator (hΔ : IsTransvectionClass Δ) {A E B : Subgroup G}
    (hT : IsTriangle Δ A E B) {t : G} (ht : t * t = 1) (htE : ∀ y ∈ E, Commute t y)
    (htA : conjSub A t = B) {f e : G} (hf : f ∈ graph A t) (he : e ∈ E) :
    Commuting (conjSub A (e * f * e * f)) B := by
  have hAg : Commuting A (conjSub A t) := htA ▸ hT.comm
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hee : e * e = 1 := hΔ.mul_self hT.memE he
  have hfA : conjSub A f = A := Aux.conjSub_eq_of_commute fun y hy =>
    commute_of_mem_graph hΔ hT htA hf (Or.inl hy)
  rw [conjSub_mul, hfA]
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff hAg).1 hf
  set b := t * a * t⁻¹ with hb_def
  have hb : b ∈ B := htA ▸ conj_mem_conjSub t ha
  set y := e * a * e with hy_def
  set y' := e * b * e with hy'_def
  have hy'y : y' = t * y * t⁻¹ := by
    rw [hy'_def, hy_def, hb_def]
    have hte := (htE e he).eq
    calc e * (t * a * t⁻¹) * e = (e * t) * a * (t⁻¹ * e) := by group
      _ = (t * e) * a * (e * t⁻¹) := by
          rw [← hte, show t⁻¹ * e = e * t⁻¹ by
            rw [htinv]; exact (htE e he).eq]
      _ = t * (e * a * e) * t⁻¹ := by group
  have hefe : e * (a * b) * e = y' * y := by
    have hab : a * b = b * a := (hT.comm a ha b hb).eq
    rw [hy'_def, hy_def, hab]
    calc e * (b * a) * e = e * b * (e * e) * a * e := by rw [hee]; group
      _ = e * b * e * (e * a * e) := by group
  rw [hefe, conjSub_mul]
  have hy'y' : y' * y' = 1 := by
    rw [hy'_def]
    calc e * b * e * (e * b * e) = e * b * (e * e) * b * e := by group
      _ = 1 := by rw [hee, mul_one, mul_assoc e b b, hΔ.mul_self hT.memB hb, mul_one, hee]
  have hB : B = conjSub (conjSub B y') y' := by
    rw [← conjSub_mul, hy'y', conjSub_one]
  rw [hB, Aux.commuting_conjSub_iff]
  have hBt : conjSub B y' = conjSub (conjSub A y) t := by
    rw [← htA, ← conjSub_mul, ← conjSub_mul, hy'y, htinv]
    congr 1
    rw [mul_assoc, ht, mul_one]
  rw [hBt]
  have hyX : y ∈ A ⊔ E := by
    rw [hy_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right he)
      (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right he)
  rcases conjSub_eq_or_conjSub_eq hΔ hT.memE hT.oppA hyX with hP | ⟨e', he', hP⟩
  · rw [hP, Aux.conjSub_eq_of_commute htE]
    exact hΔ.root.commuting_self hT.memE
  · rw [hP, ← conjSub_mul, show t * e' = e' * t from (htE e' he').eq, conjSub_mul, htA]
    exact hT.comm.conjSub e'

theorem graph_eq_graph_conjSub {A E B : Subgroup G} (hT : IsTriangle Δ A E B) {t : G}
    (ht : t * t = 1) (htA : conjSub A t = B) : graph A t = graph B t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hAg : Commuting A (conjSub A t) := htA ▸ hT.comm
  have htB : conjSub B t = A := by rw [← htA, ← conjSub_mul, ht, conjSub_one]
  have hBg : Commuting B (conjSub B t) := htB ▸ hT.comm.symm
  have key : ∀ {P Q : Subgroup G}, Commuting P Q → conjSub P t = Q → ∀ a ∈ P,
      a * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by
    intro P Q hPQ hPt a ha
    have hb : t * a * t⁻¹ ∈ Q := hPt ▸ conj_mem_conjSub t ha
    have hta : t * (t * a * t⁻¹) * t⁻¹ = a := by
      rw [htinv]
      calc t * (t * a * t) * t = (t * t) * a * (t * t) := by simp only [mul_assoc]
        _ = a := by rw [ht, one_mul, mul_one]
    rw [hta]
    exact (hPQ a ha _ hb).eq
  ext x
  rw [mem_graph_iff hAg, mem_graph_iff hBg]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨t * a * t⁻¹, htA ▸ conj_mem_conjSub t ha, key hT.comm htA a ha⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨t * b * t⁻¹, htB ▸ conj_mem_conjSub t hb, key hT.comm.symm htB b hb⟩

theorem commuting_conjSub_of_mem_graph [Finite G] (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) {A E B : Subgroup G} (hT : IsTriangle Δ A E B) {t : G}
    (htE : ∀ y ∈ E, Commute t y) (htA : conjSub A t = B) {τ : G} (hτ : τ ∈ graph A t) :
    Commuting (conjSub E τ) E := by
  have hAg : Commuting A (conjSub A t) := htA ▸ hT.comm
  have hne : A ≠ conjSub A t := htA ▸ hT.ne
  have := commuting_conjSub_graph hΔ hiso hT.memA hT.memE hAg hne hT.oppA htE hτ
    (Subgroup.one_mem _)
  rwa [conjSub_one] at this

theorem commutator_mul_self [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    {A E B : Subgroup G} (hT : IsTriangle Δ A E B) {t : G} (htE : ∀ y ∈ E, Commute t y)
    (htA : conjSub A t = B) {e f : G} (he : e ∈ E) (hf : f ∈ graph A t) :
    e * f * e * f * (e * f * e * f) = 1 := by
  have hff := mul_self_of_mem_graph hΔ hT htA hf
  have hee := hΔ.mul_self hT.memE he
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hmem : f * e * f ∈ conjSub E f := by
    have := conj_mem_conjSub f he
    rwa [hfinv] at this
  have hc : Commute (f * e * f) e :=
    commuting_conjSub_of_mem_graph hΔ hiso hT htE htA hf _ hmem e he
  calc e * f * e * f * (e * f * e * f) = e * ((f * e * f) * e) * (f * e * f) := by group
    _ = e * (e * (f * e * f)) * (f * e * f) := by rw [hc.eq]
    _ = (e * e) * (f * e * (f * f) * e * f) := by group
    _ = 1 := by rw [hee, hff, mul_one, one_mul, mul_assoc f e e, hee, mul_one, hff]

theorem commuting_conjSub_commutator_self [Finite G] (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) {A E B : Subgroup G} (hT : IsTriangle Δ A E B) {t : G}
    (htE : ∀ y ∈ E, Commute t y) (htA : conjSub A t = B) {P : Subgroup G} (hP : P ∈ Δ)
    (hEP : Opposite E P) {e f : G} (he : e ∈ E) (hf : f ∈ graph A t)
    (hfP : ∀ y ∈ P, Commute f y) : Commuting P (conjSub P (e * f * e * f)) := by
  have hff := mul_self_of_mem_graph hΔ hT htA hf
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hEf : Commuting E (conjSub E f) :=
    (commuting_conjSub_of_mem_graph hΔ hiso hT htE htA hf).symm
  by_cases hne : E = conjSub E f
  ·
    have hfe : Commute f e := commute_of_commute_partner hEP hne.symm hfP he
    have h1 : e * f * e * f = 1 := by
      rw [show e * f * e * f = e * (f * e) * f by group, hfe.eq]
      calc e * (e * f) * f = (e * e) * (f * f) := by group
        _ = 1 := by rw [hΔ.mul_self hT.memE he, hff, one_mul]
    rw [h1, conjSub_one]
    exact hΔ.root.commuting_self hP
  · have hx : e * f * e * f ∈ graph E f := by
      rw [mem_graph_iff hEf]
      exact ⟨e, he, by rw [hfinv]; group⟩
    have := commuting_conjSub_graph hΔ hiso hT.memE hP hEf hne hEP.symm hfP
      (Subgroup.one_mem _) hx
    rwa [conjSub_one] at this

theorem commute_commutator_mul [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    {A E B : Subgroup G} (hT : IsTriangle Δ A E B) {t : G} (ht : t * t = 1)
    (htE : ∀ y ∈ E, Commute t y) (htA : conjSub A t = B) {e f f' : G} (he : e ∈ E)
    (hf : f ∈ graph A t) (hf' : f' ∈ graph A t) {y : G} (hy : y ∈ A ∨ y ∈ E ∨ y ∈ B) :
    Commute (e * f * e * f * f' * (e * f * e * f) * f') y := by
  have hAg : Commuting A (conjSub A t) := htA ▸ hT.comm
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hff := mul_self_of_mem_graph hΔ hT htA hf
  have hf'f' := mul_self_of_mem_graph hΔ hT htA hf'
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hf'inv : f'⁻¹ = f' := inv_eq_of_mul_eq_one_right hf'f'
  set x := e * f * e * f with hx_def
  have hxx : x * x = 1 := commutator_mul_self hΔ hiso hT htE htA he hf
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  rcases hy with hy | hy | hy
  rotate_left
  ·
    have hz : x * f' * x * f' =
        e * (f * e * f⁻¹) * (f' * e * f'⁻¹) * ((f' * f) * e * (f' * f)⁻¹) := by
      rw [hx_def, hfinv, hf'inv, mul_inv_rev, hfinv, hf'inv]
      calc e * f * e * f * f' * (e * f * e * f) * f' =
            e * f * e * f * f' * e * 1 * f * e * f * f' := by group
        _ = e * f * e * f * f' * e * (f' * f') * f * e * f * f' := by rw [hf'f']
        _ = e * (f * e * f) * (f' * e * f') * (f' * f * e * (f * f')) := by group
    rw [hz]
    have hc : ∀ τ ∈ graph A t, Commute (τ * e * τ⁻¹) y := fun τ hτ =>
      commuting_conjSub_of_mem_graph hΔ hiso hT htE htA hτ _ (conj_mem_conjSub τ he) y hy
    refine (((hΔ.root.commute hT.memE he hy).mul_left (hc f hf)).mul_left
      (hc f' hf')).mul_left (hc _ (Subgroup.mul_mem _ hf' hf))
  all_goals
    obtain ⟨a, ha, rfl⟩ := (mem_graph_iff hAg).1 hf'
    have hb : t * a * t⁻¹ ∈ B := htA ▸ conj_mem_conjSub t ha
    have hz : x * (a * (t * a * t⁻¹)) * x * (a * (t * a * t⁻¹)) =
        (x * a * x⁻¹) * (x * (t * a * t⁻¹) * x⁻¹) * a * (t * a * t⁻¹) := by
      rw [hxinv]
      calc x * (a * (t * a * t⁻¹)) * x * (a * (t * a * t⁻¹)) =
            x * a * 1 * (t * a * t⁻¹) * x * (a * (t * a * t⁻¹)) := by group
        _ = x * a * (x * x) * (t * a * t⁻¹) * x * (a * (t * a * t⁻¹)) := by rw [hxx]
        _ = x * a * x * (x * (t * a * t⁻¹) * x) * a * (t * a * t⁻¹) := by group
    rw [hz]
    have hxa : x * a * x⁻¹ ∈ conjSub A x := conj_mem_conjSub x ha
    have hxb : x * (t * a * t⁻¹) * x⁻¹ ∈ conjSub B x := conj_mem_conjSub x hb
  ·
    have h1 : Commute (x * a * x⁻¹) y :=
      commuting_conjSub_commutator hΔ hT ht htE htA hf he _ hxa y hy
    have h2 := (commuting_conjSub_commutator_self hΔ hiso hT htE htA hT.memB hT.oppB he hf
      fun y hy => commute_of_mem_graph hΔ hT htA hf (Or.inr hy)) y hy _ hxb
    exact ((h1.mul_left h2.symm).mul_left (hT.comm a ha y hy)).mul_left
      (hΔ.root.commute hT.memB hb hy)
  ·
    have h1 := (commuting_conjSub_commutator_self hΔ hiso hT htE htA hT.memA hT.oppA he hf
      fun y hy => commute_of_mem_graph hΔ hT htA hf (Or.inl hy)) y hy _ hxa
    have h2 : Commute (x * (t * a * t⁻¹) * x⁻¹) y := by
      have hT' := hT.swap
      have htB : conjSub B t = A := by rw [← htA, ← conjSub_mul, ht, conjSub_one]
      have hf₂ : f ∈ graph B t := graph_eq_graph_conjSub hT ht htA ▸ hf
      exact commuting_conjSub_commutator hΔ hT' ht htE htB hf₂ he _ hxb y hy
    exact ((h1.symm.mul_left h2).mul_left (hΔ.root.commute hT.memA ha hy)).mul_left
      (hT.comm y hy _ hb).symm

end CFSG.Timmesfeld.Transvection
