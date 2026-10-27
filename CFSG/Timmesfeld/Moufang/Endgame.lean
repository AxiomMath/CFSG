module

public import CFSG.Timmesfeld.Moufang.Exceptional
public import CFSG.Timmesfeld.Closure.Reduction

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Blueprint

variable {G : Type*} [Group G] {D : Set G}

structure LineConfig {n : ℕ} (d c : G) (x : Fin n → G) : Prop where
  d_sq : d * d = 1
  c_sq : c * c = 1
  x_sq : ∀ i, x i * x i = 1
  dc_pow : (d * c) ^ 5 = 1
  d_comm : ∀ i, Commute d (x i)
  sq_eq : ∀ i j, i ≠ j → (x i * x j) ^ 2 = d
  cx_pow : ∀ i, (c * x i) ^ 3 = 1
  cdx_pow : ∀ i, (c * (d * x i)) ^ 5 = 1

@[expose] def A6Endgame : Prop :=
  ∀ (H : Type) [Group H] (d c : H) (x : Fin 2 → H), LineConfig d c x → d * c ≠ 1 →
    Subgroup.closure (insert d (insert c (Set.range x))) = ⊤ →
    (∀ i, IsConj d (x i) ∧ IsConj d (d * x i)) ∧
      (Subgroup.center H = ⊥ → Nonempty (H ≃* alternatingGroup (Fin 6)))

@[expose] def J2Endgame : Prop :=
  ∀ (H : Type) [Group H] (d c : H) (x : Fin 5 → H), LineConfig d c x →
    x 0 * x 1 * x 2 * x 3 * x 4 = 1 → d * c ≠ 1 →
    Subgroup.closure (insert d (insert c (Set.range x))) = ⊤ →
    (∀ i, IsConj d (x i) ∧ IsConj d (d * x i)) ∧ NativeSporadic.IsSporadic H .J2

structure LinesAt (D : Set G) (d c : G) {n : ℕ} (x : Fin n → G) : Prop where
  mem : ∀ i, x i ∈ D
  comm : ∀ i, Commute d (x i)
  mul_mem : ∀ i, d * x i ∈ D
  ne : ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ d * x i
  order_three : ∀ i, orderOf (c * x i) = 3
  centralizer : ∀ f ∈ D, Commute d f → f = d ∨ ∃ i, f = x i ∨ f = d * x i

@[expose] def LineCount (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, orderOf (d * c) = 5 →
    (∃ x : Fin 2 → G, LinesAt D d c x) ∨
      (∃ x : Fin 5 → G, LinesAt D d c x ∧ x 0 * x 1 * x 2 * x 3 * x 4 = 1)

theorem LineConfig.subgroup {n : ℕ} {d c : G} {x : Fin n → G} (hcfg : LineConfig d c x)
    {H : Subgroup G} (hd : d ∈ H) (hc : c ∈ H) (hx : ∀ i, x i ∈ H) :
    LineConfig (⟨d, hd⟩ : H) ⟨c, hc⟩ (fun i => ⟨x i, hx i⟩) where
  d_sq := Subtype.ext (by simp [hcfg.d_sq])
  c_sq := Subtype.ext (by simp [hcfg.c_sq])
  x_sq i := Subtype.ext (by simp [hcfg.x_sq i])
  dc_pow := Subtype.ext (by simp [hcfg.dc_pow])
  d_comm i := Subtype.ext (by simpa using (hcfg.d_comm i).eq)
  sq_eq i j hij := Subtype.ext (by simpa using hcfg.sq_eq i j hij)
  cx_pow i := Subtype.ext (by simp [hcfg.cx_pow i])
  cdx_pow i := Subtype.ext (by simp [hcfg.cdx_pow i])

theorem lineConfig_of_linesAt (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) (hL : LL5 D) (hNP : NoPolar D) {n : ℕ} {d c : G} {x : Fin n → G}
    (hd : d ∈ D) (hc : c ∈ D) (h5 : orderOf (d * c) = 5) (hx : LinesAt D d c x) :
    LineConfig d c x := by
  have hD := h.root
  have hd2 := hD.mul_self_eq_one hd
  have hdc : ¬ Commute d c := fun hdc => by
    have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hd2
      (hD.mul_self_eq_one hc)).1 hdc)
    rw [h5] at this
    exact absurd this (by norm_num)
  have hodd : Odd (orderOf (d * c)) := by rw [h5]; decide
  refine ⟨hd2, hD.mul_self_eq_one hc, fun i => hD.mul_self_eq_one (hx.mem i),
    by rw [← h5]; exact pow_orderOf_eq_one _, hx.comm, fun i j hij => ?_,
    fun i => by rw [← hx.order_three i]; exact pow_orderOf_eq_one _, fun i => ?_⟩
  · exact (special_of_ne_line h hsing hQ hL hNP hd hc h5 (hx.mem i) (hx.comm i) (hx.mul_mem i)
      (hx.mem j) (hx.comm j) (hx.mul_mem j) (hx.ne i j hij).1 (hx.ne i j hij).2).2
  · obtain ⟨n1, o1⟩ :=
      opposite_of_collinear_of_five h hsing hQ hd hc h5 (hx.mem i) (hx.comm i) (hx.mul_mem i)
    have hddx : Commute d (d * x i) := (Commute.refl d).mul_right (hx.comm i)
    have hddxD : d * (d * x i) ∈ D := by
      rw [← mul_assoc, hd2, one_mul]; exact hx.mem i
    obtain ⟨n2, o2⟩ := opposite_of_collinear_of_five h hsing hQ hd hc h5 (hx.mul_mem i) hddx hddxD
    have L := hL d hd (x i) (hx.mem i) c hc (hx.comm i) (hx.mul_mem i) hdc hodd n1 o1 n2 o2
    have h3 : orderOf (x i * c) = 3 := by rw [orderOf_mul_comm_eq]; exact hx.order_three i
    rw [h5, h3] at L
    have h5' : orderOf (d * x i * c) = 5 := by omega
    have h5'' : orderOf (c * (d * x i)) = 5 := by rw [orderOf_mul_comm_eq]; exact h5'
    rw [← h5'']
    exact pow_orderOf_eq_one _

theorem closure_eq_top_of_isConj (h : Hyp G D) (hconn : Closure.CommConnected D) {n : ℕ}
    {d c : G} {x : Fin n → G} (hd : d ∈ D) (hx : LinesAt D d c x)
    (hconj : ∀ i, (∃ g ∈ Subgroup.closure (insert d (insert c (Set.range x))),
        g * d * g⁻¹ = x i) ∧
      ∃ g ∈ Subgroup.closure (insert d (insert c (Set.range x))), g * d * g⁻¹ = d * x i) :
    Subgroup.closure (insert d (insert c (Set.range x))) = ⊤ := by
  set H := Subgroup.closure (insert d (insert c (Set.range x))) with hH
  have hdH : d ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  set T : Set G := {y | ∃ g ∈ H, g * d * g⁻¹ = y} with hT
  have hTD : T ⊆ D := by
    rintro y ⟨g, -, rfl⟩
    exact h.conj_mem g hd
  have hclosed : ∀ y ∈ T, ∀ f ∈ D, Commute y f → f ∈ T := by
    rintro y ⟨g, hg, rfl⟩ f hf hyf
    have hf' : g⁻¹ * f * g ∈ D := by
      simpa using h.conj_mem g⁻¹ hf
    have hdf' : Commute d (g⁻¹ * f * g) := by
      have := (Commute.conj_iff g⁻¹).2 hyf
      simpa [mul_assoc] using this
    have key : ∃ k ∈ H, k * d * k⁻¹ = g⁻¹ * f * g := by
      rcases hx.centralizer _ hf' hdf' with he | ⟨i, he | he⟩
      · exact ⟨1, H.one_mem, by rw [← he]; group⟩
      · obtain ⟨k, hk, hke⟩ := (hconj i).1
        exact ⟨k, hk, by rw [hke, he]⟩
      · obtain ⟨k, hk, hke⟩ := (hconj i).2
        exact ⟨k, hk, by rw [hke, he]⟩
    obtain ⟨k, hk, hke⟩ := key
    refine ⟨g * k, H.mul_mem hg hk, ?_⟩
    calc g * k * d * (g * k)⁻¹ = g * (k * d * k⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * f * g) * g⁻¹ := by rw [hke]
      _ = f := by group
  have hDT := hconn T hTD ⟨d, 1, H.one_mem, by group⟩ hclosed
  rw [eq_top_iff, ← h.gen, Subgroup.closure_le]
  intro y hy
  obtain ⟨g, hg, rfl⟩ := hDT hy
  exact H.mul_mem (H.mul_mem hg hdH) (H.inv_mem hg)

theorem closure_subtype_eq_top {n : ℕ} {d c : G} {x : Fin n → G}
    (hdH : d ∈ Subgroup.closure (insert d (insert c (Set.range x))))
    (hcH : c ∈ Subgroup.closure (insert d (insert c (Set.range x))))
    (hxH : ∀ i, x i ∈ Subgroup.closure (insert d (insert c (Set.range x)))) :
    Subgroup.closure (insert (⟨d, hdH⟩ : ↥(Subgroup.closure (insert d (insert c (Set.range x)))))
      (insert ⟨c, hcH⟩ (Set.range fun i => ⟨x i, hxH i⟩))) = ⊤ := by
  rw [← Subgroup.closure_closure_coe_preimage (k := insert d (insert c (Set.range x)))]
  congr 1
  ext y
  simp only [Set.mem_insert_iff, Set.mem_range, Set.mem_preimage]
  constructor
  · rintro (rfl | rfl | ⟨i, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · rintro (h1 | h1 | ⟨i, h1⟩)
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Or.inl (Subtype.ext h1))
    · exact Or.inr (Or.inr ⟨i, Subtype.ext h1⟩)

theorem exists_mem_of_isConj {H : Subgroup G} {a b : H} (hab : IsConj a b) :
    ∃ g ∈ H, g * (a : G) * g⁻¹ = b := by
  obtain ⟨⟨g, hg⟩, hge⟩ := isConj_iff.1 hab
  exact ⟨g, hg, by simpa using congrArg Subtype.val hge⟩

theorem exceptionalInput_at {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hsing : ∀ d ∈ D, rootSet D d = {d})
    (hex : ∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3)
    (hloc : CommLambda D ∧ LL5 D ∧ NoPolar D ∧ LineCount D) (hconnG : Closure.CommConnected D)
    (hA6 : A6Endgame) (hJ2 : J2Endgame) :
    Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ NativeSporadic.IsSporadic G .J2 := by
  obtain ⟨hQ, hL, hNP, hLC⟩ := hloc
  obtain ⟨d, hd, c, hc, hdc, hodd, h3⟩ := hex
  have h5 : orderOf (d * c) = 5 :=
    (orderOf_eq_three_or_five h hsing hQ hL hd hc hdc hodd).resolve_left h3
  have hdc1 : d * c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h5
    exact absurd h5 (by norm_num)
  have sub : ∀ {n : ℕ} (x : Fin n → G),
      d ∈ Subgroup.closure (insert d (insert c (Set.range x))) ∧
      c ∈ Subgroup.closure (insert d (insert c (Set.range x))) ∧
      ∀ i, x i ∈ Subgroup.closure (insert d (insert c (Set.range x))) := fun x =>
    ⟨Subgroup.subset_closure (Set.mem_insert _ _),
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
      fun i => Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))⟩
  have hdc' : ∀ {n : ℕ} (x : Fin n → G),
      (⟨d, (sub x).1⟩ : ↥(Subgroup.closure (insert d (insert c (Set.range x))))) *
        ⟨c, (sub x).2.1⟩ ≠ 1 := fun x h1 => hdc1 (by simpa using congrArg Subtype.val h1)
  rcases hLC d hd c hc h5 with ⟨x, hx⟩ | ⟨x, hx, hov⟩
  · have hcfg := lineConfig_of_linesAt h hsing hQ hL hNP hd hc h5 hx
    obtain ⟨hdH, hcH, hxH⟩ := sub x
    have key := (hA6 _ _ _ _ (hcfg.subgroup hdH hcH hxH) (hdc' x)
      (closure_subtype_eq_top hdH hcH hxH)).1
    have htop := closure_eq_top_of_isConj h hconnG hd hx fun i =>
      ⟨exists_mem_of_isConj (key i).1, exists_mem_of_isConj (key i).2⟩
    exact .inl ((hA6 G d c x hcfg hdc1 htop).2 h.center_eq_bot)
  · have hcfg := lineConfig_of_linesAt h hsing hQ hL hNP hd hc h5 hx
    obtain ⟨hdH, hcH, hxH⟩ := sub x
    have hov' : (fun i => (⟨x i, hxH i⟩ : ↥(Subgroup.closure (insert d (insert c
        (Set.range x)))))) 0 * (fun i => (⟨x i, hxH i⟩ : ↥(Subgroup.closure (insert d
        (insert c (Set.range x)))))) 1 * (fun i => (⟨x i, hxH i⟩ : ↥(Subgroup.closure
        (insert d (insert c (Set.range x)))))) 2 * (fun i => (⟨x i, hxH i⟩ :
        ↥(Subgroup.closure (insert d (insert c (Set.range x)))))) 3 * (fun i => (⟨x i, hxH i⟩ :
        ↥(Subgroup.closure (insert d (insert c (Set.range x)))))) 4 = 1 :=
      Subtype.ext (by simpa using hov)
    have key := (hJ2 _ _ _ _ (hcfg.subgroup hdH hcH hxH) hov' (hdc' x)
      (closure_subtype_eq_top hdH hcH hxH)).1
    have htop := closure_eq_top_of_isConj h hconnG hd hx fun i =>
      ⟨exists_mem_of_isConj (key i).1, exists_mem_of_isConj (key i).2⟩
    exact .inr (hJ2 G d c x hcfg hov hdc1 htop).2

end CFSG.Timmesfeld.Moufang
