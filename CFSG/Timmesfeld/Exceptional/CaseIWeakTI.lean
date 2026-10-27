module

public import CFSG.Timmesfeld.Exceptional.CaseIRoot
public import CFSG.Timmesfeld.Exceptional.CaseIPlane
public import CFSG.Timmesfeld.Exceptional.CaseSplit

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem collinear_of_isWeakTILine [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D) {a b n : G} (ha : a ∈ D) (hb : b ∈ D)
    (hn : n ∈ D) (hW : ∀ y ∈ D, Commute b y → y * a * y = a ∨ y * a * y = a * b)
    (han : Commute a n) (hanD : a * n ∈ D) (hbn : Commute b n) (hnb : n ≠ b) : b * n ∈ D := by
  by_contra hbnD
  have hnQ : n ∉ twoCore b := hPQ b hb n hn hbn hnb hbnD
  obtain ⟨n', hn', hnn', hodd, -, hbn'⟩ := exists_levi_of_not_mem_twoCore hclass hD hn hbn.symm hnQ
  have ha2 := hD.mul_self_eq_one ha
  rcases hW n' hn' hbn' with h | h
  ·
    have han' : Commute a n' := by
      rw [Commute, SemiconjBy]
      calc a * n' = n' * (n' * a * n') := by
            rw [show n' * (n' * a * n') = (n' * n') * a * n' by group, hD.mul_self_eq_one hn',
              one_mul]
        _ = n' * a := by rw [h]
    exact mul_not_mem_of_levi hD hn' ha hnn' hodd han han' (by rw [← han.eq]; exact hanD)
  ·
    have hsq : (a * n') ^ 2 = b := by
      rw [pow_two, show a * n' * (a * n') = a * (n' * a * n') by group, h, ← mul_assoc, ha2,
        one_mul]
    have h4 : orderOf (a * n') = 4 := by
      rcases commute_or_orderOf_mul_eq_four_or_odd hD ha hn' with hc | h4 | ⟨hodd', -⟩
      · exfalso
        apply hD.ne_one hb
        rw [← hsq, (commute_iff_mul_sq_eq_one ha2 (hD.mul_self_eq_one hn')).1 hc]
      · exact h4
      · exfalso
        have h41 : (a * n') ^ 4 = 1 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two, hD.mul_self_eq_one hb]
        have hdvd := orderOf_dvd_of_pow_eq_one h41
        have h1 : orderOf (a * n') = 1 := by
          have : orderOf (a * n') ∣ 2 ^ 2 := hdvd
          obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
          interval_cases k
          · exact hk'
          · rw [hk'] at hodd'; exact absurd hodd' (by decide)
          · rw [hk'] at hodd'; exact absurd hodd' (by decide)
        apply hD.ne_one hb
        rw [← hsq, orderOf_eq_one_iff.1 h1, one_pow]
    have h4' : orderOf (n' * a) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
    have hn'bD : n' * b ∈ D := by
      have := mul_sq_mem_of_orderOf_eq_four hclass hD hn' ha h4'
      rwa [Bridge.mul_sq_comm_of_orderOf_eq_four hD ha hn' h4, hsq] at this
    exact mul_not_mem_of_levi hD hn hb (fun h => hnn' h.symm) (by rwa [orderOf_mul_comm_eq])
      hbn' hbn hn'bD

theorem mul_mem_of_conj_eq_mul (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {s a b : G} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D)
    (hab : Commute a b) (h : s * b * s = a * b) : s * a ∈ D := by
  have hb2 := hD.mul_self_eq_one hb
  have hsq : (b * s) ^ 2 = a := by
    rw [pow_two, show b * s * (b * s) = b * (s * b * s) by group, h, ← mul_assoc, ← hab.eq,
      mul_assoc, hb2, mul_one]
  have h4 : orderOf (b * s) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hb hs with hc | h4 | ⟨hodd, -⟩
    · exfalso
      apply hD.ne_one ha
      rw [← hsq, (commute_iff_mul_sq_eq_one hb2 (hD.mul_self_eq_one hs)).1 hc]
    · exact h4
    · exfalso
      have h41 : (b * s) ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two, hD.mul_self_eq_one ha]
      have h1 : orderOf (b * s) = 1 := by
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
          (show orderOf (b * s) ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one h41)
        interval_cases k
        · exact hk'
        · rw [hk'] at hodd; exact absurd hodd (by decide)
        · rw [hk'] at hodd; exact absurd hodd (by decide)
      apply hD.ne_one ha
      rw [← hsq, orderOf_eq_one_iff.1 h1, one_pow]
  have h4' : orderOf (s * b) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
  have := mul_sq_mem_of_orderOf_eq_four hclass hD hs hb h4'
  rwa [Bridge.mul_sq_comm_of_orderOf_eq_four hD hb hs h4, hsq] at this

theorem plane_of_isWeakTILine [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D) {a b u v w : G} (ha : a ∈ D) (hb : b ∈ D)
    (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) (hab : Commute a b) (habD : a * b ∈ D)
    (hW : IsWeakTILine D a b) (huv : ¬ Commute u v) (h3 : orderOf (u * v) = 3)
    (hau : Commute a u) (hav : Commute a v) (huw : Commute u w) (huwD : u * w ∈ D)
    (haw : Commute a w) (hawD : a * w ∈ D) :
    ∃ n ∈ D, Commute a n ∧ Commute b n ∧ a * n ∈ D ∧ b * n ∈ D ∧ a * b * n ∈ D := by
  have hodd : Odd (orderOf (u * v)) := by rw [h3]; decide
  have ha2 := hD.mul_self_eq_one ha
  have hw2 := hD.mul_self_eq_one hw
  have hfix : ∀ s ∈ D, Commute a s → s * a ∉ D → s * b * s = b := fun s hs has hsa =>
    (hW.1 s hs has).resolve_right fun h => hsa (mul_mem_of_conj_eq_mul hclass hD hs ha hb hab h)
  have hvb : v * b * v = b :=
    hfix v hv hav (mul_not_mem_of_levi hD hu ha (fun h => huv h.symm)
      (by rwa [orderOf_mul_comm_eq]) hav hau)
  have hvb' : Commute v b := by
    rw [Commute, SemiconjBy]
    calc v * b = v * b * v * v := by rw [mul_assoc (v * b), hD.mul_self_eq_one hv, mul_one]
      _ = b * v := by rw [hvb]
  have hva : Commute v a := hav.symm
  obtain ⟨hz1D, haz1, hwz1, hwz1D, haz1D, hawz1D⟩ :=
    plane_of_levi hclass hD hu hv ha hw h3 hau hav huw huwD haw hawD
  have hz1b : v * w * v * b * (v * w * v) = w * b * w := by
    calc v * w * v * b * (v * w * v) = v * (w * (v * b * v) * w) * v := by group
      _ = v * (w * b * w) * v := by rw [hvb]
      _ = w * b * w := by
        rcases hW.1 w hw haw with h | h
        · rw [h, hvb]
        · rw [h, (hva.mul_right hvb').eq, mul_assoc, hD.mul_self_eq_one hv, mul_one]
  generalize hz1def : v * w * v = z₁ at hz1D haz1 hwz1 hwz1D haz1D hawz1D hz1b
  have hn := hwz1D
  have han : Commute a (w * z₁) := haw.mul_right haz1
  have hanD : a * (w * z₁) ∈ D := by rw [← mul_assoc]; exact hawz1D
  have hnb : (w * z₁) * b * (w * z₁) = b := by
    calc (w * z₁) * b * (w * z₁) = (w * z₁) * b * (z₁ * w) := by rw [hwz1.eq]
      _ = w * (z₁ * b * z₁) * w := by group
      _ = b := by rw [hz1b, show w * (w * b * w) * w = (w * w) * b * (w * w) by group, hw2,
          one_mul, mul_one]
  have hbn : Commute b (w * z₁) := by
    have hn2 := hD.mul_self_eq_one hn
    show b * (w * z₁) = (w * z₁) * b
    calc b * (w * z₁) = ((w * z₁) * b * (w * z₁)) * (w * z₁) := by rw [hnb]
      _ = (w * z₁) * b * ((w * z₁) * (w * z₁)) := by group
      _ = (w * z₁) * b := by rw [hn2, mul_one]
  by_cases hnb' : w * z₁ = b
  · refine ⟨w, hw, haw, ?_, hawD, ?_, ?_⟩
    · rw [← hnb']; exact ((Commute.refl w).mul_right hwz1).symm
    · rw [← hnb', show w * z₁ * w = z₁ by rw [hwz1.eq, mul_assoc, hw2, mul_one]]; exact hz1D
    · rw [← hnb', show a * (w * z₁) * w = a * z₁ by rw [hwz1.eq, mul_assoc, mul_assoc, hw2,
        mul_one]]; exact haz1D
  by_cases hnab : w * z₁ = a * b
  · have hb' : b = a * (w * z₁) := by rw [hnab, ← mul_assoc, ha2, one_mul]
    refine ⟨w, hw, haw, ?_, hawD, ?_, ?_⟩
    · rw [hb']; exact haw.mul_left ((Commute.refl w).mul_left hwz1.symm)
    · rw [hb', show a * (w * z₁) * w = a * z₁ by rw [hwz1.eq, mul_assoc, mul_assoc, hw2,
        mul_one]]; exact haz1D
    · rw [hb', show a * (a * (w * z₁)) * w = z₁ by
        rw [← mul_assoc, ha2, one_mul, hwz1.eq, mul_assoc, hw2, mul_one]]; exact hz1D
  have hbnD := collinear_of_isWeakTILine hclass hD hPQ ha hb hn hW.2.1 han hanD hbn hnb'
  refine ⟨_, hn, han, hbn, hanD, hbnD, ?_⟩
  have hbQ : b ∈ twoCore a := mem_map_pCore_centralizer hclass hD ha hb hab.symm
    (Or.inl (by rw [← hab.eq]; exact habD))
  have hnQ : w * z₁ ∈ twoCore a := mem_map_pCore_centralizer hclass hD ha hn han.symm
    (Or.inl (by rw [← han.eq]; exact hanD))
  have hbnQ := (twoCore a).mul_mem hbQ hnQ
  by_contra habnD
  refine hPQ a ha _ hbnD (hab.mul_right han) ?_ (by rwa [mul_assoc] at habnD) hbnQ
  intro h
  apply hnab
  rw [← h, hbn.eq, mul_assoc, hD.mul_self_eq_one hb, mul_one]

theorem tiLinePlane_of_collConnected [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D) (hC : ExcCollConnected D) (hP1 : ExcP1 D)
    (hNL : ¬ NoLevi D) : ExcTILinePlane D := by
  intro c hc z hz hcz hczD hW
  simp only [NoLevi, not_forall, not_not, exists_prop] at hNL
  obtain ⟨x, hx, y, hy, hxy, hodd, b, hb, hbx, hby⟩ := hNL
  obtain ⟨a', ha', b', hb', v', hv', z', hz', hab', hodd', hva', hvb', haz', haz'D, hvz', hvz'D⟩ :=
    exists_levi_collinear_of_collConnected hclass hD hPQ hC hx hy hb hxy hodd hbx hby
  obtain ⟨u, hu, v, hv, w, hw, huv, hoddu, hcu, hcv, huw, huwD, hcw, hcwD⟩ :=
    exists_levi_conj hclass ha' hb' hv' hz' hc hab' hodd' hva' hvb' haz' haz'D hvz' hvz'D
  have h3 := leviOrderThree_of_collConnected hclass hD hPQ hC hP1 u hu v hv huv hoddu c hc hcu hcv
  exact plane_of_isWeakTILine hclass hD hPQ hc hz hu hv hw hcz hczD hW huv h3 hcu hcv huw huwD hcw
    hcwD

theorem exceptionalLeviStep_of_commInput (hI : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH
    G → (∀ d ∈ D, rootSet D d = {d}) → (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧
    orderOf (d * c) ≠ 3) → ¬ NoLevi D → CommLambda D ∧ ExcPQ D ∧ ExcCollConnected
    D) : ExceptionalLeviStep := by
  intro G _ D h IH hsing hex
  by_contra hNL
  obtain ⟨hQ, hPQ, hC⟩ := hI G D h IH hsing hex hNL
  have := h.finite
  have hP1 := p1_of_commLambda h hsing hQ
  have hPL := planeLine_of_tiLinePlane h.isClass h.root hPQ
    (tiLinePlane_of_collConnected h.isClass h.root hPQ hC hP1 hNL)
  obtain ⟨d, hd, c, hc, hdc, hodd, h3⟩ := hex
  exact h3 (orderOf_eq_three_of_planeLine h.isClass h.root hsing hQ hP1 hC hPL hd hc hdc hodd)

end CFSG.Timmesfeld.Moufang
