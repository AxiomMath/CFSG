module

public import CFSG.RankThree.GF2n.Stroth80.Sec117Config

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

variable {X Y : Type*} [Group X] [Group Y]

private theorem symm_mem_centralizer_singleton {t : X} (e : X ≃* Y) {c : Y}
    (hc : c ∈ Subgroup.centralizer {e t}) : e.symm c ∈ Subgroup.centralizer {t} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  apply e.injective
  simpa using hc

private theorem map_mul_conj (e : X ≃* Y) (t g : X) :
    e t * (e g * e t * (e g)⁻¹) = e (t * (g * t * g⁻¹)) := by
  simp [map_mul, map_inv]

theorem IsStrothInvolution.map {t : X} {a : ℕ} (h : IsStrothInvolution t a) (e : X ≃* Y) :
    IsStrothInvolution (e t) a where
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  orderOf_mul_conj g := by
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [map_mul_conj, MulEquiv.orderOf_eq]
    exact h.orderOf_mul_conj g
  isConj_sq g hg := by
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [map_mul_conj, MulEquiv.orderOf_eq] at hg
    rw [map_mul_conj, ← map_pow]
    exact e.toMonoidHom.map_isConj (h.isConj_sq g hg)
  dvd_of_inv g y hy hg hinv := by
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [MulEquiv.orderOf_eq] at hg
    refine h.dvd_of_inv g y hy hg (e.injective ?_)
    simpa only [map_mul, map_inv] using hinv

private theorem IsA2PlaneKernel.card_dvd_of_inf_map_eq_bot {t : X} {a : ℕ} {N : Subgroup X}
    (h : IsA2PlaneKernel t a N) (e : X ≃* Y) {L : Subgroup Y}
    (hL : L ≤ Subgroup.centralizer {e t}) (hLN : L ⊓ N.map e.toMonoidHom = ⊥) :
    Nat.card L ∣ 2 ^ a * (2 ^ a - 1) * (2 ^ (2 * a) - 1) := by
  have hL' : L.map e.symm.toMonoidHom ≤ Subgroup.centralizer {t} := by
    rintro _ ⟨l, hl, rfl⟩
    exact symm_mem_centralizer_singleton e (hL hl)
  have hLN' : L.map e.symm.toMonoidHom ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨l, hl, rfl⟩, hlN⟩
    have hl' : l ∈ L ⊓ N.map e.toMonoidHom := ⟨hl, Subgroup.mem_map_equiv.mpr hlN⟩
    rw [hLN, Subgroup.mem_bot] at hl'
    simp [hl']
  have h1 := h.card_dvd _ hL' hLN'
  rwa [Subgroup.card_map_of_injective e.symm.injective] at h1

theorem IsA2PlaneKernel.map {t : X} {a : ℕ} {N : Subgroup X} (h : IsA2PlaneKernel t a N)
    (e : X ≃* Y) : IsA2PlaneKernel (e t) a (N.map e.toMonoidHom) where
  le_centralizer y hy := by
    rw [Subgroup.mem_map_equiv] at hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hy)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    simpa using congrArg e h1
  conj_mem c hc y hy := by
    rw [Subgroup.mem_map_equiv] at hy ⊢
    simpa using h.conj_mem _ (symm_mem_centralizer_singleton e hc) _ hy
  radical S P R hS hPS hPt hRP hRn hR := by
    have hS' : ∀ s ∈ e.symm '' S, ∃ k : ℕ, s ^ 2 ^ k = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, hk⟩ := hS s hs
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hPS' : Subgroup.closure (e.symm '' S) = P.map e.symm.toMonoidHom := by
      rw [← hPS, MonoidHom.map_closure]
      rfl
    have hPt' : P.map e.symm.toMonoidHom ≤ Subgroup.centralizer {t} := by
      rintro _ ⟨p, hp, rfl⟩
      exact symm_mem_centralizer_singleton e (hPt hp)
    have hRn' : ∀ p ∈ P.map e.symm.toMonoidHom, ∀ r ∈ R.map e.symm.toMonoidHom,
        p * r * p⁻¹ ∈ R.map e.symm.toMonoidHom := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨r, hr, rfl⟩
      exact ⟨p * r * p⁻¹, hRn p hp r hr, by simp⟩
    rcases h.radical _ _ _ hS' hPS' hPt' (Subgroup.map_mono hRP) hRn' (hR.map _) with h1 | h1
    · refine Or.inl fun r hr => ?_
      rw [Subgroup.mem_map_equiv]
      exact h1 ⟨r, hr, rfl⟩
    · refine Or.inr fun c hc => ?_
      rw [← Subgroup.map_commutator] at h1
      rw [Subgroup.mem_map_equiv]
      exact h1 ⟨c, hc, rfl⟩
  card_dvd _ hL hLN := h.card_dvd_of_inf_map_eq_bot e hL hLN

theorem IsKLConfig.map {t : X} {a : ℕ} {N A : Subgroup X} (h : IsKLConfig t a N A) (e : X ≃* Y) :
    IsKLConfig (e t) a (N.map e.toMonoidHom) (A.map e.toMonoidHom) where
  involution := h.involution.map e
  kernel := h.kernel.map e
  isPGroup := h.isPGroup.map _
  comm x hx y hy := by
    rw [Subgroup.mem_map_equiv] at hx hy
    apply e.symm.injective
    simpa using h.comm _ hx _ hy
  mem := ⟨t, h.mem, rfl⟩
  conj_mem g hg x hx := by
    rw [Subgroup.mem_map_equiv] at hg hx ⊢
    simpa using h.conj_mem _ hg _ hx
  eq_one g hg hodd hcomm := by
    rw [Subgroup.mem_map_equiv] at hg
    have h1 : e.symm g = 1 := h.eq_one _ hg (by rwa [MulEquiv.orderOf_eq]) fun x hx => by
      apply e.injective
      simpa using hcomm (e x) ⟨x, hx, rfl⟩
    simpa using congrArg e h1

private theorem conj_mul_conj_eq (t g k : X) :
    g * t * g⁻¹ * (k * t * k⁻¹) = g * (t * (g⁻¹ * k * t * (g⁻¹ * k)⁻¹)) * g⁻¹ := by
  group

theorem IsStrothInvolution.orderOf_mul_ne_six {t : X} {a : ℕ} (h : IsStrothInvolution t a)
    {x y : X} (hx : IsConj t x) (hy : IsConj t y) : orderOf (x * y) ≠ 6 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hy
  have ho := MulEquiv.orderOf_eq (MulAut.conj g) (t * (g⁻¹ * k * t * (g⁻¹ * k)⁻¹))
  rw [MulAut.conj_apply, ← conj_mul_conj_eq] at ho
  rw [ho]
  intro h6
  rcases h.orderOf_mul_conj (g⁻¹ * k) with h4 | h4 <;> rw [h6] at h4
  · norm_num at h4
  · exact (by decide : ¬ Odd 6) h4

theorem IsStrothInvolution.isConj_sq_of_orderOf_eq_four {t : X} {a : ℕ}
    (h : IsStrothInvolution t a) {x y : X} (hx : IsConj t x) (hy : IsConj t y)
    (h4 : orderOf (x * y) = 4) : IsConj ((x * y) ^ 2) t := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hy
  have ho := MulEquiv.orderOf_eq (MulAut.conj g) (t * (g⁻¹ * k * t * (g⁻¹ * k)⁻¹))
  rw [MulAut.conj_apply, ← conj_mul_conj_eq, h4] at ho
  rw [conj_mul_conj_eq, conj_pow]
  exact (isConj_iff.mpr ⟨g⁻¹, by group⟩).trans (h.isConj_sq _ ho.symm)

theorem IsA2PlaneKernel.commutator_le_of_isPGroup {t : X} {a : ℕ} {N P : Subgroup X}
    (hN : IsA2PlaneKernel t a N) (hP : P ≤ Subgroup.centralizer {t}) (hP2 : IsPGroup 2 P) :
    ⁅P, P⁆ ≤ N := by
  have hS : ∀ s ∈ (P : Set X), ∃ k : ℕ, s ^ 2 ^ k = 1 := fun s hs => by
    obtain ⟨k, hk⟩ := hP2 ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hPP : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  rcases hN.radical _ P P hS (Subgroup.closure_eq P) hP le_rfl
    (fun p hp r hr => P.mul_mem (P.mul_mem hp hr) (P.inv_mem hp)) hP2 with h | h
  · exact hPP.trans h
  · exact h

private theorem eq_one_of_odd_orderOf_of_pow_two_pow {z : X} (hz : Odd (orderOf z)) {k : ℕ}
    (hk : z ^ 2 ^ k = 1) : z = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hz)) (orderOf_dvd_of_pow_eq_one hk)
    dvd_rfl)

theorem IsA2PlaneKernel.le_of_forall_normal {t : X} {a : ℕ} {N L S : Subgroup X}
    (hN : IsA2PlaneKernel t a N) (hL : L ≤ Subgroup.centralizer {t})
    (hLn : ∀ H : Subgroup X, H ≤ L → (∀ l ∈ L, ∀ h ∈ H, l * h * l⁻¹ ∈ H) →
      H ≤ Subgroup.centralizer (L : Set X) ∨ L ≤ H)
    (hLz : ∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set X) → Odd (orderOf z))
    (hSL : S ≤ L) (hS : IsPGroup 2 S) (hSc : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) : L ≤ N := by
  have hSN : ⁅S, S⁆ ≤ N := hN.commutator_le_of_isPGroup (hSL.trans hL) hS
  rcases hLn (N ⊓ L) inf_le_right fun l hl h hh =>
      ⟨hN.conj_mem l (hL hl) h hh.1, L.mul_mem (L.mul_mem hl hh.2) (L.inv_mem hl)⟩ with hc | hc
  · obtain ⟨x, hx, y, hy, hxy⟩ := hSc
    have hcS : ⁅x, y⁆ ∈ S := by
      rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
    have hcNL : ⁅x, y⁆ ∈ N ⊓ L := ⟨hSN (Subgroup.commutator_mem_commutator hx hy), hSL hcS⟩
    obtain ⟨k, hk⟩ := hS ⟨_, hcS⟩
    refine absurd (commutatorElement_eq_one_iff_mul_comm.mp ?_) hxy
    exact eq_one_of_odd_orderOf_of_pow_two_pow (hLz _ hcNL.2 (hc hcNL))
      (by simpa using congrArg Subtype.val hk)
  · exact hc.trans inf_le_left

theorem IsA2PlaneKernel.le_of_isSimpleGroup [Finite X] {t : X} {a : ℕ} {N L : Subgroup X}
    (hN : IsA2PlaneKernel t a N) (hL : L ≤ Subgroup.centralizer {t}) [IsSimpleGroup L] {ℓ : ℕ}
    (_hℓ : ℓ.Prime) (hℓL : ℓ ∣ Nat.card L)
    (hℓq : ¬ ℓ ∣ 2 ^ a * (2 ^ a - 1) * (2 ^ (2 * a) - 1)) : L ≤ N := by
  have : (N.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN.conj_mem g (hL g.2) n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf L) with h | h
  · have hLN : L ⊓ N = ⊥ := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h).symm
    exact absurd (hℓL.trans (hN.card_dvd L hL hLN)) hℓq
  · exact Subgroup.subgroupOf_eq_top.mp h

private theorem two_dvd_card_quotient_subgroupOf_of_not_le [Finite X] {A Z₀ : Subgroup X}
    (hA2 : IsPGroup 2 A) (hAZ : ¬ A ≤ Z₀) : 2 ∣ Nat.card (A ⧸ Z₀.subgroupOf A) := by
  obtain ⟨k, hk⟩ := hA2.index (Z₀.subgroupOf A)
  rw [← Subgroup.index_eq_card, hk]
  rcases k with _ | k
  · rw [pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hk
    exact absurd hk hAZ
  · exact dvd_pow_self 2 (Nat.succ_ne_zero k)

private theorem conj_inv_mul_conj_mem_of_inv_mul_mem {Z₀ : Subgroup X} {u x y : X}
    (hu : ∀ z ∈ Z₀, u * z * u⁻¹ ∈ Z₀) (h : x⁻¹ * y ∈ Z₀) :
    (u * x * u⁻¹)⁻¹ * (u * y * u⁻¹) ∈ Z₀ := by
  have e : (u * x * u⁻¹)⁻¹ * (u * y * u⁻¹) = u * (x⁻¹ * y) * u⁻¹ := by group
  rw [e]
  exact hu _ h

private theorem exists_mem_not_mem_of_not_le [Finite X] {A Z₀ U : Subgroup X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : IsPGroup 2 A) (hU : IsPGroup 2 U)
    (hUA : ∀ u ∈ U, ∀ x ∈ A, u * x * u⁻¹ ∈ A) (hUZ : ∀ u ∈ U, ∀ z ∈ Z₀, u * z * u⁻¹ ∈ Z₀)
    (hAZ : ¬ A ≤ Z₀) : ∃ x ∈ A, x ∉ Z₀ ∧ ∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ Z₀ := by
  classical
  let f : U → A → A := fun u x => ⟨u * x * u⁻¹, hUA u u.2 x x.2⟩
  have hf : ∀ (u : U) (x y : A), x⁻¹ * y ∈ Z₀.subgroupOf A →
      (f u x)⁻¹ * f u y ∈ Z₀.subgroupOf A := fun u x y h => by
    simp only [Subgroup.mem_subgroupOf, f, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    exact conj_inv_mul_conj_mem_of_inv_mul_mem (hUZ u u.2) h
  let : MulAction U (A ⧸ Z₀.subgroupOf A) :=
    { smul := fun u => Quotient.map' (f u) fun x y h => by
        rw [QuotientGroup.leftRel_apply] at h ⊢
        exact hf u x y h
      one_smul := fun q => QuotientGroup.induction_on q fun x => by
        change (QuotientGroup.mk (f 1 x) : A ⧸ Z₀.subgroupOf A) = x
        exact congrArg _ (Subtype.ext (by simp [f]))
      mul_smul := fun u v q => QuotientGroup.induction_on q fun x => by
        change (QuotientGroup.mk (f (u * v) x) : A ⧸ Z₀.subgroupOf A) =
          QuotientGroup.mk (f u (f v x))
        exact congrArg _ (Subtype.ext (by simp [f, mul_assoc])) }
  have hfix1 : (QuotientGroup.mk 1 : A ⧸ Z₀.subgroupOf A) ∈
      MulAction.fixedPoints U (A ⧸ Z₀.subgroupOf A) := fun u => by
    change (QuotientGroup.mk (f u 1) : A ⧸ Z₀.subgroupOf A) = QuotientGroup.mk 1
    exact congrArg _ (Subtype.ext (by simp [f]))
  have hcard := two_dvd_card_quotient_subgroupOf_of_not_le hA2 hAZ
  obtain ⟨b, hb, hb1⟩ :=
    hU.exists_fixed_point_of_prime_dvd_card_of_fixed_point (A ⧸ Z₀.subgroupOf A) hcard hfix1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, x.2, fun hx => hb1 ?_, fun u hu => ?_⟩
  · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hx
  · have h := hb ⟨u, hu⟩
    change (QuotientGroup.mk (f ⟨u, hu⟩ x) : A ⧸ Z₀.subgroupOf A) = QuotientGroup.mk x at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have h1 : ((u : X) * x * u⁻¹)⁻¹ * x ∈ Z₀ := by simpa [f] using h
    rw [hA _ (hUA u hu x x.2) _ (A.inv_mem x.2)]
    simpa using Z₀.inv_mem h1

theorem le_of_fixed_of_ne_commute [Finite X] {A Z₀ U U' : Subgroup X} {V V' : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : IsPGroup 2 A)
    (_hAZ : ∀ x ∈ A, ∀ z ∈ Z₀, x * z * x⁻¹ ∈ Z₀)
    (hU : IsPGroup 2 U) (hUA : ∀ u ∈ U, ∀ x ∈ A, u * x * u⁻¹ ∈ A)
    (hUZ : ∀ u ∈ U, ∀ z ∈ Z₀, u * z * u⁻¹ ∈ Z₀)
    (hU' : IsPGroup 2 U') (hU'A : ∀ u ∈ U', ∀ x ∈ A, u * x * u⁻¹ ∈ A)
    (hU'Z : ∀ u ∈ U', ∀ z ∈ Z₀, u * z * u⁻¹ ∈ Z₀)
    (hV : ∀ x ∈ A, (∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ Z₀) → x ∈ V)
    (hV' : ∀ x ∈ A, (∀ u ∈ U', u * x * u⁻¹ * x⁻¹ ∈ Z₀) → x ∈ V')
    (hVV' : ∀ v ∈ V, ∀ v' ∈ V', v ∉ Z₀ → v' ∉ Z₀ → v * v' ≠ v' * v) : A ≤ Z₀ := by
  by_contra hAZ0
  obtain ⟨v, hvA, hvZ, hvU⟩ := exists_mem_not_mem_of_not_le hA hA2 hU hUA hUZ hAZ0
  obtain ⟨v', hv'A, hv'Z, hv'U⟩ := exists_mem_not_mem_of_not_le hA hA2 hU' hU'A hU'Z hAZ0
  exact hVV' v (hV v hvA hvU) v' (hV' v' hv'A hv'U) hvZ hv'Z (hA v hvA v' hv'A)

private theorem conj_comm_of_comm {J : Subgroup X} {s' c : X} (hs' : ∀ j ∈ J, s' * j = j * s')
    (hc : ∀ j ∈ J, c * j = j * c) (j : X) (hj : j ∈ J) :
    c⁻¹ * s' * c * j = j * (c⁻¹ * s' * c) := by
  have hcj : c⁻¹ * j = j * c⁻¹ := by
    calc c⁻¹ * j = c⁻¹ * (j * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * j) * c⁻¹ := by rw [hc j hj]
      _ = j * c⁻¹ := by group
  calc c⁻¹ * s' * c * j = c⁻¹ * s' * (c * j) := by group
    _ = c⁻¹ * (s' * j) * c := by rw [hc j hj]; group
    _ = c⁻¹ * j * s' * c := by rw [hs' j hj]; group
    _ = j * (c⁻¹ * s' * c) := by rw [hcj]; group

theorem orderOf_mul_conj_eq_six {J : Subgroup X} {s s' g c : X} (hs : s ∈ J) (hg : g ∈ J)
    (hs' : ∀ j ∈ J, s' * j = j * s') (hc : ∀ j ∈ J, c * j = j * c) (hs'2 : orderOf s' = 2)
    (h3 : orderOf (s * (g⁻¹ * s * g)) = 3) (hne : c⁻¹ * s' * c ≠ s')
    (hcomm : s' * (c⁻¹ * s' * c) = c⁻¹ * s' * c * s') :
    orderOf (s * s' * ((g * c)⁻¹ * (s * s') * (g * c))) = 6 := by
  have hw : g⁻¹ * s * g ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hg) hs) hg
  have hsw : s * (g⁻¹ * s * g) ∈ J := J.mul_mem hs hw
  have h1 : s' * g = g * s' := hs' g hg
  have h2 : c * (g⁻¹ * s * g) = g⁻¹ * s * g * c := hc _ hw
  have h3' : s' * (g⁻¹ * s * g) = g⁻¹ * s * g * s' := hs' _ hw
  have key : s * s' * ((g * c)⁻¹ * (s * s') * (g * c)) =
      s * (g⁻¹ * s * g) * (s' * (c⁻¹ * s' * c)) := by
    calc s * s' * ((g * c)⁻¹ * (s * s') * (g * c))
        = s * s' * (c⁻¹ * (g⁻¹ * s * (s' * g)) * c) := by group
      _ = s * s' * (c⁻¹ * (g⁻¹ * s * g * c) * c⁻¹ * s' * c) := by rw [h1]; group
      _ = s * (s' * (g⁻¹ * s * g)) * (c⁻¹ * s' * c) := by rw [← h2]; group
      _ = s * (g⁻¹ * s * g) * (s' * (c⁻¹ * s' * c)) := by rw [h3']; group
  have hsq : s' * s' = 1 := by rw [← sq, ← hs'2]; exact pow_orderOf_eq_one s'
  have hb : orderOf (s' * (c⁻¹ * s' * c)) = 2 := by
    refine orderOf_eq_prime ?_ fun hb1 => hne ?_
    · calc (s' * (c⁻¹ * s' * c)) ^ 2 = s' * (c⁻¹ * s' * c * s') * (c⁻¹ * s' * c) := by
            rw [sq]; group
        _ = s' * (s' * (c⁻¹ * s' * c)) * (c⁻¹ * s' * c) := by rw [← hcomm]
        _ = s' * s' * (c⁻¹ * (s' * s') * c) := by group
        _ = 1 := by rw [hsq]; group
    · calc c⁻¹ * s' * c = s' * (s' * (c⁻¹ * s' * c)) := by rw [← mul_assoc, hsq, one_mul]
        _ = s' := by rw [hb1, mul_one]
  have hab : Commute (s * (g⁻¹ * s * g)) (s' * (c⁻¹ * s' * c)) :=
    Commute.mul_right (hs' _ hsw).symm (conj_comm_of_comm hs' hc _ hsw).symm
  rw [key, hab.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [h3, hb]; norm_num), h3, hb]

end CFSG.RankThree.GF2n.Stroth80
