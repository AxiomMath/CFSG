module

public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

namespace OddLocal

theorem mem_normalizer_closure {S : Set G} {g : G} (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (h2 : ∀ s ∈ S, g⁻¹ * s * g ∈ S) : g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ k : G, (∀ s ∈ S, k * s * k⁻¹ ∈ S) → ∀ h ∈ Subgroup.closure S,
      k * h * k⁻¹ ∈ Subgroup.closure S := by
    intro k hk h hh
    induction hh using Subgroup.closure_induction with
    | mem s hs => exact Subgroup.subset_closure (hk s hs)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : k * (a * b) * k⁻¹ = k * a * k⁻¹ * (k * b * k⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g h1 h
  · intro hh
    have := key g⁻¹ (by simpa using h2) _ hh
    simpa [mul_assoc] using this

theorem le_normalizer_conj {A : Subgroup G} {x : G} (hx : x * x = 1)
    (h : A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.normalizer (A.map (MulAut.conj x).toMonoidHom : Set G) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hmem : ∀ {g : G}, g ∈ A.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ A := by
    intro g
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [mul_assoc] using ha
    · intro hg
      exact ⟨x⁻¹ * g * x, hg, by group⟩
  have key : ∀ a ∈ A, ∀ b : G, b ∈ A.map (MulAut.conj x).toMonoidHom →
      a * b * a⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom := by
    intro a ha b hb
    rw [hmem] at hb ⊢
    have hxa : x⁻¹ * a * x ∈ A.map (MulAut.conj x).toMonoidHom := by
      rw [hmem]
      have e : x⁻¹ * (x⁻¹ * a * x) * x = a := by
        rw [hxi, show x * (x * a * x) * x = (x * x) * a * (x * x) by group, hx, one_mul,
          mul_one]
      rw [e]
      exact ha
    have h1 := (Subgroup.mem_normalizer_iff.mp (h hxa) _).mp hb
    have e : x⁻¹ * a * x * (x⁻¹ * b * x) * (x⁻¹ * a * x)⁻¹ = x⁻¹ * (a * b * a⁻¹) * x := by
      group
    rwa [e] at h1
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact key a ha b
  · intro hb
    have := key a⁻¹ (A.inv_mem ha) _ hb
    simpa [mul_assoc] using this

theorem mem_closure_conj {d x : G} (hd : d * d = 1) (hx : x * x = 1)
    (hodd : Odd (orderOf (d * x))) : x ∈ Subgroup.closure {d, x * d * x⁻¹} := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  set K := Subgroup.closure ({d, x * d * x⁻¹} : Set G)
  have hdK : d ∈ K := Subgroup.subset_closure (by simp)
  have hsq : (d * x) ^ 2 ∈ K := by
    have : d * (x * d * x⁻¹) = (d * x) ^ 2 := by rw [hxi, pow_two]; group
    rw [← this]
    exact K.mul_mem hdK (Subgroup.subset_closure (by simp))
  obtain ⟨k, hk⟩ := hodd
  have hρ : d * x = ((d * x) ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf (d * x) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hρK : d * x ∈ K := by
    rw [hρ]
    exact K.pow_mem hsq _
  have : x = d⁻¹ * (d * x) := by group
  rw [this]
  exact K.mul_mem (K.inv_mem hdK) hρK

theorem commutator_closure_le {S T : Set G} {N : Subgroup G}
    (hS : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G))
    (hT : Subgroup.closure T ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ s ∈ S, ∀ t ∈ T, ⁅s, t⁆ ∈ N) : ⁅Subgroup.closure S, Subgroup.closure T⁆ ≤ N := by
  have hconj : ∀ k ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N :=
    fun k hk n hn => (Subgroup.mem_normalizer_iff.mp hk n).mp hn
  have step1 : ∀ t ∈ T, ∀ g ∈ Subgroup.closure S, ⁅g, t⁆ ∈ N := by
    intro t ht g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact h s hs t ht
    | one => simp
    | mul a b ha hb iha ihb =>
      have e : ⁅a * b, t⁆ = a * ⁅b, t⁆ * a⁻¹ * ⁅a, t⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem (hconj a (hS ha) _ ihb) iha
    | inv a ha iha =>
      have e : ⁅a⁻¹, t⁆ = a⁻¹ * ⁅a, t⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj _ (hS (Subgroup.inv_mem _ ha)) _ (N.inv_mem iha)
  rw [Subgroup.commutator_le]
  intro g hg k hk
  induction hk using Subgroup.closure_induction with
  | mem t ht => exact step1 t ht g hg
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem iha (hconj a (hT ha) _ ihb)
  | inv a ha iha =>
    have e : ⁅g, a⁻¹⁆ = a⁻¹ * ⁅g, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj _ (hT (Subgroup.inv_mem _ ha)) _ (N.inv_mem iha)

theorem commute_of_mem_closure_pairwise {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    {g h : G} (hg : g ∈ Subgroup.closure S) (hh : h ∈ Subgroup.closure S) : Commute g h := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hS b hb a ha).eq
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer {g} := by
    rw [Subgroup.closure_le]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h1 hg) a ha)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hh)).symm

section Root

variable {d x : G}

theorem not_commute_of_mem_rootSet (hdx : ¬ Commute d x) (hx : x ∈ D) {e : G}
    (he : e ∈ rootSet D d) : ¬ Commute e x := fun h => hdx ((he.2 x hx).mp h)

theorem commute_mul_iff_of_mem_rootSet (hD : IsOddTransp D) (hd : d ∈ D) {a b : G}
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) {f : G} (hf : f ∈ D) :
    Commute f (a * b) ↔ Commute f d := by
  rw [hD.commute_mul_iff ha.1 hb.1 hf hab (commute_of_mem_rootSet hd ha hb)]
  have h1 := (ha.2 f hf)
  have h2 := (hb.2 f hf)
  constructor
  · rintro ⟨h, -⟩
    exact (h1.mp h.symm).symm
  · intro h
    exact ⟨(h1.mpr h.symm).symm, (h2.mpr h.symm).symm⟩

theorem conj_mem_rootSet_of_commute (hN : IsNormalSet D) {u y : G}
    (hu : ∀ f ∈ D, Commute f u ↔ Commute f d) (hyu : Commute y u) {e : G}
    (he : e ∈ rootSet D d) : y * e * y⁻¹ ∈ rootSet D d := by
  refine ⟨hN y e he.1, fun f hf => ?_⟩
  set f' := y⁻¹ * f * y with hf'
  have hf'D : f' ∈ D := by simpa using hN y⁻¹ f hf
  have hff' : f = y * f' * y⁻¹ := by rw [hf']; group
  have hyuy : y * u * y⁻¹ = u := by rw [hyu.eq, mul_inv_cancel_right]
  have step1 : Commute (y * e * y⁻¹) f ↔ Commute e f' := by
    rw [hff', Commute.conj_iff]
  rw [step1, he.2 f' hf'D]
  constructor
  · intro h
    have h1 : Commute f' u := (hu f' hf'D).mpr h.symm
    have h2 : Commute f u := by
      have := h1.conj y
      rwa [← hff', hyuy] at this
    exact ((hu f hf).mp h2).symm
  · intro h
    have h1 : Commute f u := (hu f hf).mpr h.symm
    have h2 : Commute f' u := by
      have := h1.conj y⁻¹
      have e1 : y⁻¹ * f * y⁻¹⁻¹ = f' := by rw [hf', inv_inv]
      have e2 : y⁻¹ * u * y⁻¹⁻¹ = u := by rw [inv_inv, hyu.inv_left.eq, inv_mul_cancel_right]
      rwa [e1, e2] at this
    exact ((hu f' hf'D).mp h2).symm

theorem mem_normalizer_rootSet_of_commute (hN : IsNormalSet D) {u y : G}
    (hu : ∀ f ∈ D, Commute f u ↔ Commute f d) (hyu : Commute y u) :
    y ∈ Subgroup.normalizer (rootSet D d) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro e
  constructor
  · exact conj_mem_rootSet_of_commute hN hu hyu
  · intro he
    have := conj_mem_rootSet_of_commute hN hu hyu.inv_left he
    simpa [mul_assoc] using this

theorem normalizer_rootSet_le (hN : IsNormalSet D) (d : G) :
    Subgroup.normalizer (rootSet D d) ≤ Subgroup.normalizer (qd D d : Set G) := by
  intro g hg
  have hgE := Subgroup.mem_set_normalizer_iff.mp hg
  have hgE' := Subgroup.mem_set_normalizer_iff.mp (Subgroup.inv_mem _ hg)
  refine mem_normalizer_closure ?_ ?_
  · rintro _ ⟨a, ha, b, hb, hab, rfl⟩
    refine ⟨g * a * g⁻¹, (hgE a).mp ha, g * b * g⁻¹, (hgE b).mp hb, fun h => hab ?_, by group⟩
    have := hN g⁻¹ _ h
    simpa [mul_assoc] using this
  · rintro _ ⟨a, ha, b, hb, hab, rfl⟩
    refine ⟨g⁻¹ * a * g, by simpa using (hgE' a).mp ha, g⁻¹ * b * g, by simpa using (hgE' b).mp hb,
      fun h => hab ?_, by group⟩
    have := hN g _ h
    simpa [mul_assoc] using this

theorem qd_le_closure : qd D d ≤ Subgroup.closure (rootSet D d) := by
  rw [qd, Subgroup.closure_le]
  rintro _ ⟨a, ha, b, hb, -, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ha) (Subgroup.subset_closure hb)

theorem commute_of_mem_closure_rootSet (hd : d ∈ D) {g h : G}
    (hg : g ∈ Subgroup.closure (rootSet D d)) (hh : h ∈ Subgroup.closure (rootSet D d)) :
    Commute g h :=
  commute_of_mem_closure_pairwise (fun _ ha _ hb => commute_of_mem_rootSet hd ha hb) hg hh

theorem mem_normalizer_of_forall_commute {S : Set G} {c : G} (h : ∀ s ∈ S, Commute c s) :
    c ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [(h y hy).eq, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := (h _ hy).eq
    have e : c * y * c⁻¹ = y := by
      have h2 : c * (c * y * c⁻¹) = c * y := by rw [h1]; group
      exact mul_left_cancel h2
    rw [← e]
    exact hy

end Root

theorem map_map_conj {x : G} (hx2 : x * x = 1) (K : Subgroup G) :
    (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : ((MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom) = MonoidHom.id G := by
    ext g
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    rw [show x * (x * g * x⁻¹) * x⁻¹ = (x * x) * g * (x * x)⁻¹ by group, hx2, one_mul, inv_one,
      mul_one]
  rw [this, Subgroup.map_id]

theorem image_conj (x : G) (S : Set G) :
    ((MulAut.conj x).toMonoidHom : G → G) '' S = (fun e => x * e * x⁻¹) '' S := by
  ext
  simp [MulAut.conj_apply]

theorem closure_conj_le_rootGen (d x : G) :
    Subgroup.closure ((fun e => x * e * x⁻¹) '' rootSet D d) ≤ rootGen D d x := by
  rw [Subgroup.closure_le]
  rintro _ ⟨e, he, rfl⟩
  have hxX : x ∈ rootGen D d x := Subgroup.subset_closure (Set.mem_insert x _)
  have heX : e ∈ rootGen D d x := Subgroup.subset_closure (Set.mem_insert_of_mem x he)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxX heX) (Subgroup.inv_mem _ hxX)

theorem qdx_le_closure_conj (d x : G) :
    (qd D d).map (MulAut.conj x).toMonoidHom ≤
      Subgroup.closure ((fun e => x * e * x⁻¹) '' rootSet D d) := by
  have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) (qd_le_closure (D := D) (d := d))
  rwa [MonoidHom.map_closure, image_conj] at h

section Proof

variable [Finite G] (hD : IsOddTransp D) (hN : IsNormalSet D) {d x : G} (hd : d ∈ D)
  (hx : x ∈ D) (hdx : ¬ Commute d x)
  (hno : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, IsTriangle D a x b → ¬ IsThirdKind a x b)
include hD hN hd hx hdx hno

theorem orderOf_mul_mul_eq_four {a b : G} (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d)
    (hab : a ≠ b) (habD : a * b ∉ D) : orderOf (a * b * x) = 4 := by
  have htri : IsTriangle D a x b := ⟨ha.1, hb.1, hx, hab, commute_of_mem_rootSet hd ha hb,
    not_commute_of_mem_rootSet hdx hx ha, not_commute_of_mem_rootSet hdx hx hb⟩
  rcases htri.orderOf_cases hD hN with ⟨hodd, -⟩ | h4 | h3
  · exact absurd (htri.mul_mem_of_odd hD hN hodd) habD
  · exact h4
  · exact absurd h3 (hno a ha b hb htri)

omit [Finite G] hN hd hdx hno in
theorem commute_conj_of_orderOf_eq_four {u : G} (hu : u * u = 1) (h4 : orderOf (u * x) = 4) :
    Commute u (x * u * x⁻¹) := by
  have hx2 : x * x = 1 := hD.mul_self_eq_one hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hp : (u * x) ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one _
  have e1 : u * (x * u * x⁻¹) = (u * x) ^ 2 := by rw [hxi, pow_two]; group
  have hsq : (u * (x * u * x⁻¹)) * (u * (x * u * x⁻¹)) = 1 := by
    rw [e1, ← pow_add]
    exact hp
  have hy2 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
    rw [hxi, show x * u * x * (x * u * x) = x * (u * (x * x) * u) * x by group, hx2, mul_one, hu,
      mul_one, hx2]
  have hyi : (x * u * x⁻¹)⁻¹ = x * u * x⁻¹ := inv_eq_of_mul_eq_one_right hy2
  show u * (x * u * x⁻¹) = x * u * x⁻¹ * u
  calc u * (x * u * x⁻¹) = (u * (x * u * x⁻¹))⁻¹ := (inv_eq_of_mul_eq_one_right hsq).symm
    _ = x * u * x⁻¹ * u := by rw [mul_inv_rev, hyi, hui]

theorem conj_gen_mem_normalizer {a b : G} (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d)
    (habD : a * b ∉ D) : x * (a * b) * x⁻¹ ∈ Subgroup.normalizer (rootSet D d) := by
  by_cases hab : a = b
  · rw [hab, hD.mul_self_eq_one hb.1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have h4 := orderOf_mul_mul_eq_four hD hN hd hx hdx hno ha hb hab habD
    have hu : a * b * (a * b) = 1 := by
      rw [show a * b * (a * b) = a * (b * a) * b by group,
        ← (commute_of_mem_rootSet hd ha hb).eq, show a * (a * b) * b = (a * a) * (b * b) by group,
        hD.mul_self_eq_one ha.1, hD.mul_self_eq_one hb.1, one_mul]
    exact mem_normalizer_rootSet_of_commute hN
      (fun f hf => commute_mul_iff_of_mem_rootSet hD hd ha hb hab hf)
      (commute_conj_of_orderOf_eq_four hD hx hu h4).symm

theorem qdx_le_normalizer :
    (qd D d).map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (rootSet D d) := by
  rw [Subgroup.map_le_iff_le_comap, qd, Subgroup.closure_le]
  rintro _ ⟨a, ha, b, hb, habD, rfl⟩
  exact conj_gen_mem_normalizer hD hN hd hx hdx hno ha hb habD

theorem qdx_le_normalizer_qd :
    (qd D d).map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (qd D d : Set G) :=
  (qdx_le_normalizer hD hN hd hx hdx hno).trans (normalizer_rootSet_le hN d)

theorem qd_le_normalizer_qdx :
    qd D d ≤ Subgroup.normalizer ((qd D d).map (MulAut.conj x).toMonoidHom : Set G) :=
  le_normalizer_conj (hD.mul_self_eq_one hx) (qdx_le_normalizer_qd hD hN hd hx hdx hno)

theorem commutator_qd_qdx_le :
    ⁅qd D d, (qd D d).map (MulAut.conj x).toMonoidHom⁆ ≤
      qd D d ⊓ (qd D d).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp (qdx_le_normalizer_qd hD hN hd hx hdx hno h₂)
      g₁⁻¹).mp (Subgroup.inv_mem _ h₁)
    have e : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h₁ h
  · have h := (Subgroup.mem_normalizer_iff.mp (qd_le_normalizer_qdx hD hN hd hx hdx hno h₁)
      g₂).mp h₂
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ h₂)

theorem commutatorElement_gen_mem_qd {a b : G} (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d)
    (habD : a * b ∉ D) {e : G} (he : e ∈ rootSet D d) : ⁅x * (a * b) * x⁻¹, e⁆ ∈ qd D d := by
  by_cases hab : a = b
  · rw [hab, hD.mul_self_eq_one hb.1, mul_one, mul_inv_cancel, commutatorElement_one_left]
    exact Subgroup.one_mem _
  set y := x * (a * b) * x⁻¹ with hy
  have hx2 : x * x = 1 := hD.mul_self_eq_one hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hab2 : a * b * (a * b) = 1 := by
    rw [show a * b * (a * b) = a * (b * a) * b by group,
      ← (commute_of_mem_rootSet hd ha hb).eq, show a * (a * b) * b = (a * a) * (b * b) by group,
      hD.mul_self_eq_one ha.1, hD.mul_self_eq_one hb.1, one_mul]
  have hy2 : y * y = 1 := by
    rw [hy, show x * (a * b) * x⁻¹ * (x * (a * b) * x⁻¹) = x * (a * b * (a * b)) * x⁻¹ by group,
      hab2, mul_one, mul_inv_cancel]
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyN := conj_gen_mem_normalizer hD hN hd hx hdx hno ha hb habD
  set e' := y * e * y⁻¹ with he'
  have he'E : e' ∈ rootSet D d := (Subgroup.mem_set_normalizer_iff.mp hyN e).mp he
  have hcomm : ⁅y, e⁆ = e' * e := by
    rw [commutatorElement_def, he', hD.inv_eq he.1]
  rw [hcomm]
  by_cases hee : e' = e
  · rw [hee, hD.mul_self_eq_one he.1]
    exact Subgroup.one_mem _
  by_cases hD' : e' * e ∈ D
  · exfalso
    have hfE : e' * e ∈ rootSet D d :=
      ⟨hD', fun g hg => by
        rw [Commute.symm_iff (a := e' * e), commute_mul_iff_of_mem_rootSet hD hd he'E he hee hg,
          Commute.symm_iff]⟩
    have hyf : Commute y (e' * e) := by
      have h1 : y * e' * y⁻¹ = e := by
        rw [he', hyi, show y * (y * e * y) * y = (y * y) * e * (y * y) by group, hy2, one_mul,
          mul_one]
      show y * (e' * e) = e' * e * y
      calc y * (e' * e) = y * e' * y⁻¹ * (y * e * y⁻¹) * y := by group
        _ = e * e' * y := by rw [h1, ← he']
        _ = e' * e * y := by rw [(commute_of_mem_rootSet hd he he'E).eq]
    have hyc : ∀ g ∈ rootSet D d, Commute y (x * g * x⁻¹) := by
      intro g hg
      have h1 : Commute (a * b) g :=
        ((commute_of_mem_rootSet hd ha hg).mul_left (commute_of_mem_rootSet hd hb hg))
      exact h1.conj x
    have hodd : Odd (orderOf (e' * e * x)) :=
      hD.odd_of_not_commute hfE.1 hx (not_commute_of_mem_rootSet hdx hx hfE)
    have hxmem := mem_closure_conj (hD.mul_self_eq_one hfE.1) hx2 hodd
    have hle : Subgroup.closure {e' * e, x * (e' * e) * x⁻¹} ≤ Subgroup.centralizer {y} := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyf.eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyc _ hfE).eq.symm
    have hxy : Commute x y := Subgroup.mem_centralizer_singleton_iff.mp (hle hxmem)
    have habx : Commute (a * b) x := by
      have := hxy.symm.conj x⁻¹
      simpa [hy, mul_assoc] using this
    have h4 := orderOf_mul_mul_eq_four hD hN hd hx hdx hno ha hb hab habD
    have hsq : (a * b * x) ^ 2 = 1 := by
      rw [pow_two, show a * b * x * (a * b * x) = a * b * (x * (a * b)) * x by group,
        ← habx.eq, show a * b * (a * b * x) * x = (a * b * (a * b)) * (x * x) by group, hab2,
        hx2, one_mul]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [h4] at this
    exact absurd this (by norm_num)
  · exact Subgroup.subset_closure ⟨e', he'E, e, he, hD', rfl⟩

theorem commutator_qdx_closure_le :
    ⁅(qd D d).map (MulAut.conj x).toMonoidHom, Subgroup.closure (rootSet D d)⁆ ≤ qd D d := by
  have hQx := qdx_le_normalizer_qd hD hN hd hx hdx hno
  rw [qd, MonoidHom.map_closure] at hQx ⊢
  refine commutator_closure_le hQx ?_ ?_
  · rw [Subgroup.closure_le]
    intro e he
    refine mem_normalizer_of_forall_commute fun q hq => ?_
    exact commute_of_mem_closure_rootSet hd (Subgroup.subset_closure he) (qd_le_closure hq)
  · rintro _ ⟨_, ⟨a, ha, b, hb, habD, rfl⟩, rfl⟩ e he
    exact commutatorElement_gen_mem_qd hD hN hd hx hdx hno ha hb habD he

theorem commutator_qd_closure_conj_le :
    ⁅qd D d, Subgroup.closure ((fun e => x * e * x⁻¹) '' rootSet D d)⁆ ≤
      (qd D d).map (MulAut.conj x).toMonoidHom := by
  have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom)
    (commutator_qdx_closure_le hD hN hd hx hdx hno)
  rwa [Subgroup.map_commutator, map_map_conj (hD.mul_self_eq_one hx), MonoidHom.map_closure,
    image_conj] at h

theorem rootGen_le_normalizer_sup :
    rootGen D d x ≤ Subgroup.normalizer
      ((qd D d ⊔ (qd D d).map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  set Q := qd D d
  set Qx := Q.map (MulAut.conj x).toMonoidHom
  have hx2 : x * x = 1 := hD.mul_self_eq_one hx
  have key : ∀ g : G, g * g = 1 → (Q ⊔ Qx).map (MulAut.conj g).toMonoidHom ≤ Q ⊔ Qx →
      g ∈ Subgroup.normalizer ((Q ⊔ Qx : Subgroup G) : Set G) := by
    intro g hg hle
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hle ⟨h, hh, rfl⟩
    · intro hh
      have := hle ⟨_, hh, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rwa [hgi, show g * (g * h * g) * g = (g * g) * h * (g * g) by group, hg, one_mul,
        mul_one] at this
  rw [rootGen, Subgroup.closure_le]
  rintro g (rfl | hg)
  · refine key g hx2 ?_
    rw [Subgroup.map_sup, map_map_conj hx2, sup_comm]
  · refine key g (hD.mul_self_eq_one hg.1) ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro q hq
      have hc := commute_of_mem_closure_rootSet hd (Subgroup.subset_closure hg) (qd_le_closure hq)
      show g * q * g⁻¹ ∈ Q ⊔ Qx
      rw [hc.eq, mul_inv_cancel_right]
      exact Subgroup.mem_sup_left hq
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      have hc : ⁅y, g⁆ ∈ Q := commutator_qdx_closure_le hD hN hd hx hdx hno
        (Subgroup.commutator_mem_commutator hy (Subgroup.subset_closure hg))
      show g * y * g⁻¹ ∈ Q ⊔ Qx
      have e : g * y * g⁻¹ = ⁅y, g⁆⁻¹ * y := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Q.inv_mem hc)) (Subgroup.mem_sup_right hy)

omit [Finite G] hN in
theorem commute_of_mem_inf {z : G} (hz : z ∈ qd D d ⊓ (qd D d).map (MulAut.conj x).toMonoidHom)
    {g : G} (hg : g ∈ rootGen D d x) : Commute z g := by
  have hzE : z ∈ Subgroup.closure (rootSet D d) := qd_le_closure hz.1
  have hzEx := qdx_le_closure_conj d x hz.2
  have hpair : ∀ a ∈ (fun e => x * e * x⁻¹) '' rootSet D d,
      ∀ b ∈ (fun e => x * e * x⁻¹) '' rootSet D d, Commute a b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (commute_of_mem_rootSet hd ha hb).conj x
  have hle : rootGen D d x ≤ Subgroup.centralizer {z} := by
    rw [rootGen, Subgroup.closure_le]
    rintro g (rfl | hg)
    · have hd' : d ∈ rootSet D d := mem_rootSet_self hd
      have h1 : Subgroup.closure {d, g * d * g⁻¹} ≤ Subgroup.centralizer {z} := by
        rw [Subgroup.closure_le]
        rintro k (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (commute_of_mem_closure_rootSet hd (Subgroup.subset_closure hd') hzE).eq
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_closure_pairwise hpair
            (Subgroup.subset_closure ⟨d, hd', rfl⟩) hzEx).eq
      exact h1 (mem_closure_conj (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hx)
        (hD.odd_of_not_commute hd hx hdx))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_mem_closure_rootSet hd (Subgroup.subset_closure hg) hzE).eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm

end Proof

end OddLocal

open OddLocal in
theorem qd_lemma [Finite G] (hD : IsOddTransp D) (hN : IsNormalSet D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hno : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, IsTriangle D a x b → ¬ IsThirdKind a x b) :
    (qd D d ⊓ (qd D d).map (MulAut.conj x).toMonoidHom ≤ rootGen D d x ∧
      ∀ z ∈ qd D d ⊓ (qd D d).map (MulAut.conj x).toMonoidHom, ∀ g ∈ rootGen D d x,
        Commute z g) ∧
    (qd D d ≤ rootGen D d x ∧ (qd D d).map (MulAut.conj x).toMonoidHom ≤ rootGen D d x ∧
      ⁅qd D d, (qd D d).map (MulAut.conj x).toMonoidHom⁆ ≤
        qd D d ⊓ (qd D d).map (MulAut.conj x).toMonoidHom ∧
      (∀ g ∈ rootGen D d x, ∀ q ∈ qd D d ⊔ (qd D d).map (MulAut.conj x).toMonoidHom,
        g * q * g⁻¹ ∈ qd D d ⊔ (qd D d).map (MulAut.conj x).toMonoidHom) ∧
      ⁅qd D d, Subgroup.closure ((fun e => x * e * x⁻¹) '' rootSet D d)⁆ ≤
        (qd D d).map (MulAut.conj x).toMonoidHom ∧
      ⁅(qd D d).map (MulAut.conj x).toMonoidHom, Subgroup.closure (rootSet D d)⁆ ≤ qd D d) := by
  have hQX : qd D d ≤ rootGen D d x := (qd_le_closure (D := D) (d := d)).trans
    (Subgroup.closure_mono (Set.subset_insert x _))
  refine ⟨⟨inf_le_left.trans hQX, fun z hz g hg => commute_of_mem_inf hD hd hx hdx hno hz hg⟩,
    hQX, (qdx_le_closure_conj d x).trans (closure_conj_le_rootGen d x),
    commutator_qd_qdx_le hD hN hd hx hdx hno, fun g hg q hq => ?_,
    commutator_qd_closure_conj_le hD hN hd hx hdx hno,
    commutator_qdx_closure_le hD hN hd hx hdx hno⟩
  exact (Subgroup.mem_normalizer_iff.mp (rootGen_le_normalizer_sup hD hN hd hx hdx hno hg) q).mp hq

end CFSG.Timmesfeld.Bridge
