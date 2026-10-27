module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow2Alg
public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private lemma s1614_rp_not_isCyclic_of_finset {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {s : Finset G} (hcard : 3 < s.card) (h3 : ∀ x ∈ s, x ^ 3 = 1) : ¬ IsCyclic G := by
  intro hc
  have hle : (Finset.univ.filter (fun x : G => x ^ 3 = 1)).card ≤ 3 := by
    have := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
    simpa using this
  have hsub : s ⊆ Finset.univ.filter (fun x : G => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h3 x hx
  have := Finset.card_le_card hsub
  omega

private lemma s1614_rp_exists_fix_pointwise {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) {E : Subgroup (MulAut W)} (hE3 : IsElemAbelian 3 E)
    (hE9 : 9 ≤ Nat.card ↥E) {X : Subgroup W} (hX : Nat.card ↥X = 4)
    (hEX : ∀ e ∈ E, X.map e.toMonoidHom = X) {a : W} (ha : a ∈ X) (ha1 : a ≠ 1) :
    ∃ h ∈ E, h ≠ 1 ∧ ∀ x ∈ X, h x = x := by
  classical
  haveI : Fintype ↥E := Fintype.ofFinite _
  haveI : Fintype ↥X := Fintype.ofFinite _
  haveI : Nontrivial ↥X := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_eq_nat_card, hX]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : IsKleinFour ↥X := by
    refine ⟨hX, ?_⟩
    rw [Monoid.exponent_eq_prime_iff (show Nat.Prime 2 by norm_num)]
    intro g hg
    apply orderOf_eq_prime _ hg
    apply Subtype.ext
    simpa [pow_two] using hW (g : W)
  let f : ↥E → ↥X := fun e => ⟨(e : MulAut W) a, by
    have := hEX (e : MulAut W) e.2
    exact this ▸ ⟨a, ha, rfl⟩⟩
  have hcard : Fintype.card ↥X < Fintype.card ↥E := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hX]
    omega
  obtain ⟨e₁, e₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hval : (e₁ : MulAut W) a = (e₂ : MulAut W) a := by
    dsimp only [f] at heq
    exact congrArg Subtype.val heq
  let h : MulAut W := (e₂ : MulAut W)⁻¹ * (e₁ : MulAut W)
  have hhE : h ∈ E := by
    dsimp only [h]
    exact E.mul_mem (E.inv_mem e₂.2) e₁.2
  have hh1 : h ≠ 1 := by
    intro hh
    apply hne
    apply Subtype.ext
    have h1 : (e₁ : MulAut W) = e₂ := by
      have h2 := congrArg (fun z : MulAut W => (e₂ : MulAut W) * z) hh
      dsimp only [h] at h2
      simpa [mul_assoc] using h2
    exact h1
  have hha : h a = a := by
    dsimp only [h]
    rw [MulAut.mul_apply, MulAut.inv_apply, hval, MulEquiv.symm_apply_apply]
  refine ⟨h, hhE, hh1, ?_⟩
  intro x hx
  by_contra hxh
  have hx1 : x ≠ 1 := fun hx0 => hxh (by rw [hx0, map_one])
  have hxa : x ≠ a := fun hx0 => hxh (by rw [hx0, hha])
  have hhxX : h x ∈ X := by
    have := hEX h hhE
    exact this ▸ ⟨x, hx, rfl⟩
  have hhx1 : h x ≠ 1 := by
    intro hx0
    apply hx1
    apply h.injective
    rw [hx0, map_one]
  have hhxa : h x ≠ a := by
    intro hx0
    apply hxa
    apply h.injective
    rw [hx0, hha]
  have hmul : (⟨h x, hhxX⟩ : ↥X) = (⟨a, ha⟩ : ↥X) * (⟨x, hx⟩ : ↥X) :=
    IsKleinFour.eq_mul_of_ne_all (x := (⟨a, ha⟩ : ↥X)) (y := (⟨x, hx⟩ : ↥X))
      (z := (⟨h x, hhxX⟩ : ↥X))
      (by simpa using ha1) (by simpa using hx1) (by simpa using hxa.symm)
      (by simpa using hhx1) (by simpa using hhxa) (by simpa using hxh)
  have hmulW : h x = a * x := by
    simpa using congrArg Subtype.val hmul
  have h2 : h (h x) = x := by
    rw [hmulW, map_mul, hha, hmulW, ← mul_assoc, hW a, one_mul]
  have h3 : h * h * h = 1 := by
    rw [← pow_three']
    exact hE3.2 h hhE
  have hxeq : h x = x := by
    have hcong := congrArg (fun f : MulAut W => f x) h3
    simp only [MulAut.mul_apply, MulAut.one_apply] at hcong
    rw [show h (h (h x)) = h x from by rw [h2]] at hcong
    exact hcong
  exact hxh hxeq

theorem s1614_row2_pick {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    {Mb E : Subgroup (MulAut W)} (hE : E ≤ Mb) (hE3 : IsElemAbelian 3 E)
    (hE9 : 9 ≤ Nat.card ↥E) {X : Subgroup W} (hX : Nat.card ↥X = 4)
    (hEX : ∀ e ∈ E, X.map e.toMonoidHom = X) {y : MulAut W} (hyM : y ∈ Mb)
    (hy3 : y * y * y = 1) (hyE : ∀ e ∈ E, y * e = e * y) (hyE' : y ∉ E)
    (hyfpf : ∀ x : W, y x = x → x = 1) (hXy : X ⊓ X.map y.toMonoidHom = ⊥)
    {S : Subgroup W} (hS : S ≤ X ⊔ X.map y.toMonoidHom) (h3 : 3 ≤ rk ↥S) :
    ∃ z ∈ S, z ≠ 1 ∧ ∃ B : Subgroup (MulAut W), B ≤ Mb ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      z ∈ fixV B := by
  classical
  haveI : Fintype ↥E := Fintype.ofFinite _
  haveI : Fintype ↥X := Fintype.ofFinite _
  have hW' : ∀ x : W, x ^ 2 = 1 := fun x => by rw [pow_two]; exact hW x
  have hEall : ∀ a : ↥E, a ^ 3 = 1 := fun a => by
    apply Subtype.ext
    simpa using hE3.2 (a : MulAut W) a.2
  have hEpg : IsPGroup 3 ↥E := fun a => ⟨1, by simpa using hEall a⟩
  have hrkX : rk ↥X = 2 := by
    have h : 2 ^ rk ↥X = 2 ^ 2 := by
      rw [← card_eq_two_pow hW' X, hX]
      norm_num
    exact Nat.pow_right_injective le_rfl h
  have hrkXy : rk ↥(X.map y.toMonoidHom) = rk ↥X := by
    unfold rk
    rw [Subgroup.card_map_of_injective (f := y.toMonoidHom) y.injective]
  have hrkQ : rk ↥(X ⊔ X.map y.toMonoidHom) = 4 := by
    have h := rk_sup_add_rk_inf X (X.map y.toMonoidHom)
    rw [hXy, rk_bot] at h
    omega
  have hSne : S ≠ ⊥ := by
    intro h
    rw [h, rk_bot] at h3
    omega
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSne
  have hzS : (z₀ : W) ∈ S := z₀.2
  have hz1 : (z₀ : W) ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  by_cases hA : ∀ e ∈ E, ∀ x ∈ X, e x = x
  · refine ⟨z₀, hzS, hz1, E, hE, hEpg, ?_, ?_⟩
    · apply s1614_rp_not_isCyclic_of_finset (s := Finset.univ)
      · rw [Finset.card_univ, Fintype.card_eq_nat_card]
        omega
      · intro x _
        exact hEall x
    · have hQfix : X ⊔ X.map y.toMonoidHom ≤ fixV E := by
        apply sup_le
        · intro x hx
          rw [mem_fixV]
          intro e he
          exact hA e he x hx
        · rintro _ ⟨x, hx, rfl⟩
          rw [mem_fixV]
          intro e he
          change e (y x) = y x
          have h1 : e (y x) = y (e x) := by
            have := congrArg (fun f : MulAut W => f x) (hyE e he)
            simpa [MulAut.mul_apply] using this.symm
          rw [h1, hA e he x hx]
      exact hQfix (hS hzS)
  · have hA' : ∃ g ∈ E, ∃ x ∈ X, g x ≠ x := by
      by_contra h
      apply hA
      intro e he x hx
      by_contra hne
      exact h ⟨e, he, x, hx, hne⟩
    obtain ⟨g, hgE, x₀, hx₀X, hgx₀⟩ := hA'
    have hg3 : g * g * g = 1 := by
      rw [← pow_three']
      exact hE3.2 g hgE
    have hyg : y * g = g * y := hyE g hgE
    have hgX : X.map g.toMonoidHom = X := hEX g hgE
    obtain ⟨R, hRQ, hRrk, hRfix⟩ :=
      s1614_row2_fixed hW hy3 hyfpf hg3 hyg hX hgX ⟨x₀, hx₀X, hgx₀⟩ hXy
    have hSR : 1 ≤ rk ↥(S ⊓ R) := by
      have h1 := rk_sup_add_rk_inf S R
      have h2 : rk ↥(S ⊔ R) ≤ 4 := by
        calc rk ↥(S ⊔ R) ≤ rk ↥(X ⊔ X.map y.toMonoidHom) := rk_mono (sup_le hS hRQ)
          _ = 4 := hrkQ
      omega
    have hSRne : S ⊓ R ≠ ⊥ := by
      intro h
      rw [h, rk_bot] at hSR
      omega
    obtain ⟨w₀, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSRne
    let w : W := (w₀ : W)
    have hwS : w ∈ S := w₀.2.1
    have hwR : w ∈ R := w₀.2.2
    have hw1 : w ≠ 1 := fun h => hw₀1 (Subtype.ext h)
    have hygw : (y * g) w = w := hRfix w hwR
    have hx₀1 : x₀ ≠ 1 := by
      intro h
      rw [h, map_one] at hgx₀
      exact hgx₀ rfl
    obtain ⟨h, hhE, hh1, hhX⟩ := s1614_rp_exists_fix_pointwise hW hE3 hE9 hX hEX hx₀X hx₀1
    have hQfixh : X ⊔ X.map y.toMonoidHom ≤ fixV (Subgroup.zpowers h) := by
      apply sup_le
      · intro x hx
        rw [mem_fixV_zpowers_iff_apply]
        exact hhX x hx
      · rintro _ ⟨x, hx, rfl⟩
        rw [mem_fixV_zpowers_iff_apply]
        change h (y x) = y x
        have h1 : h (y x) = y (h x) := by
          have := congrArg (fun f : MulAut W => f x) (hyE h hhE)
          simpa [MulAut.mul_apply] using this.symm
        rw [h1, hhX x hx]
    have hhw : h w = w := mem_fixV_zpowers_iff_apply.1 (hQfixh (hS hwS))
    let a₀ : MulAut W := y * g
    let B : Subgroup (MulAut W) := Subgroup.closure {a₀, h}
    have hy3pow : y ^ 3 = 1 := by rw [pow_three']; exact hy3
    have hg3pow : g ^ 3 = 1 := by rw [pow_three']; exact hg3
    have ha₀3 : a₀ ^ 3 = 1 := by
      dsimp only [a₀]
      rw [Commute.mul_pow (show Commute y g from hyg) 3, hy3pow, hg3pow, mul_one]
    have ha₀1 : a₀ ≠ 1 := by
      intro hh
      apply hyE'
      have hh' : y * g = 1 := by simpa only [a₀] using hh
      rw [eq_inv_of_mul_eq_one_left hh']
      exact E.inv_mem hgE
    have ha₀21 : a₀ ^ 2 ≠ 1 := by
      intro hh
      apply ha₀1
      have h3' : a₀ ^ 3 = a₀ := by
        rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, hh, mul_one]
      rw [← h3', ha₀3]
    have ha₀2a : a₀ ^ 2 ≠ a₀ := by
      intro hh
      apply ha₀1
      have h' : a₀ * a₀ = a₀ * 1 := by rw [mul_one, ← pow_two, hh]
      exact mul_left_cancel h'
    have ha₀h : a₀ ≠ h := by
      intro hh
      apply hyE'
      have hh' : y * g = h := by simpa only [a₀] using hh
      have h1 : y = h * g⁻¹ := by
        rw [← hh', mul_assoc, mul_inv_cancel, mul_one]
      rw [h1]
      exact E.mul_mem hhE (E.inv_mem hgE)
    have ha₀2h : a₀ ^ 2 ≠ h := by
      intro hh
      apply hyE'
      have ha₀2 : a₀ ^ 2 = y ^ 2 * g ^ 2 := by
        dsimp only [a₀]
        rw [Commute.mul_pow (show Commute y g from hyg) 2]
      have hh' : y ^ 2 * g ^ 2 = h := by rw [← ha₀2]; exact hh
      have hy2 : y ^ 2 = h * (g ^ 2)⁻¹ := by
        have h1 : y ^ 2 * g ^ 2 * (g ^ 2)⁻¹ = h * (g ^ 2)⁻¹ := by rw [hh']
        rwa [mul_assoc, mul_inv_cancel, mul_one] at h1
      have hy2E : y ^ 2 ∈ E := by
        rw [hy2]
        exact E.mul_mem hhE (E.inv_mem (E.pow_mem hgE 2))
      have hy4 : y = (y ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hy3pow, one_mul, pow_one]
      rw [hy4]
      exact E.pow_mem hy2E 2
    have ha₀23 : (a₀ ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, ha₀3, one_pow]
    have ha₀A : a₀ ∈ Subgroup.zpowers y ⊔ E := by
      dsimp only [a₀]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers y) hgE
    have hzp : IsPGroup 3 ↥(Subgroup.zpowers y) := by
      apply IsPGroup.of_card_dvd_pow (n := 1)
      rw [pow_one, Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.2 hy3pow
    have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer E := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 : y * x * y⁻¹ = x := by
          rw [hyE x hx, mul_assoc, mul_inv_cancel, mul_one]
        rwa [h1]
      · intro hx
        have hcomm : y⁻¹ * (y * x * y⁻¹) * y = y * x * y⁻¹ := by
          rw [mul_assoc, ← hyE (y * x * y⁻¹) hx, ← mul_assoc, inv_mul_cancel, one_mul]
        have hx' : x = y⁻¹ * (y * x * y⁻¹) * y := by group
        rwa [hx', hcomm]
    have hApg : IsPGroup 3 ↥(Subgroup.zpowers y ⊔ E) :=
      IsPGroup.to_sup_of_normal_right' hzp hEpg hnorm
    have hBA : B ≤ Subgroup.zpowers y ⊔ E := by
      dsimp only [B]
      rw [Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact ha₀A
      · exact Subgroup.mem_sup_right hhE
    have hBpg : IsPGroup 3 ↥B := hApg.to_le hBA
    have ha₀M : a₀ ∈ Mb := by
      dsimp only [a₀]
      exact Mb.mul_mem hyM (hE hgE)
    have hBM : B ≤ Mb := by
      dsimp only [B]
      rw [Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact ha₀M
      · exact hE hhE
    have hzB : w ∈ fixV B := by
      rw [mem_fixV]
      intro u hu
      refine Subgroup.closure_induction (p := fun u _ => u w = w) ?_ ?_ ?_ ?_ hu
      · intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact hygw
        · exact hhw
      · simp
      · intro u v _ _ hu hv
        rw [MulAut.mul_apply, hv, hu]
      · intro u _ hu
        rw [MulAut.inv_apply]
        exact (congrArg u.symm hu).symm.trans (MulEquiv.symm_apply_apply u w)
    have ha₀B : a₀ ∈ B := Subgroup.subset_closure (by simp)
    have ha₀2B : a₀ ^ 2 ∈ B := B.pow_mem ha₀B 2
    have hhB : h ∈ B := Subgroup.subset_closure (by simp)
    have h1B : (1 : MulAut W) ∈ B := B.one_mem
    haveI : Fintype ↥B := Fintype.ofFinite _
    have hBnc : ¬ IsCyclic ↥B := by
      apply s1614_rp_not_isCyclic_of_finset
        (s := ({⟨1, h1B⟩, ⟨a₀, ha₀B⟩, ⟨a₀ ^ 2, ha₀2B⟩, ⟨h, hhB⟩} : Finset ↥B))
      · have hcard : ({⟨1, h1B⟩, ⟨a₀, ha₀B⟩, ⟨a₀ ^ 2, ha₀2B⟩, ⟨h, hhB⟩} : Finset ↥B).card = 4 := by
          rw [Finset.card_eq_four]
          exact ⟨⟨1, h1B⟩, ⟨a₀, ha₀B⟩, ⟨a₀ ^ 2, ha₀2B⟩, ⟨h, hhB⟩,
            fun hh => ha₀1 (congrArg Subtype.val hh).symm,
            fun hh => ha₀21 (congrArg Subtype.val hh).symm,
            fun hh => hh1 (congrArg Subtype.val hh).symm,
            fun hh => ha₀2a (congrArg Subtype.val hh).symm,
            fun hh => ha₀h (congrArg Subtype.val hh),
            fun hh => ha₀2h (congrArg Subtype.val hh), rfl⟩
        rw [hcard]
        norm_num
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact ha₀3)
        · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact ha₀23)
        · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3.2 h hhE)
    exact ⟨w, hwS, hw1, B, hBM, hBpg, hBnc, hzB⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
