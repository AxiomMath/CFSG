module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H55
public import CFSG.Quasithin.Vol2.Ch10SecB3Aut

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv

open CFSG.Quasithin
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem le_centralizer_of_card_le {q : ℕ} [hq : Fact q.Prime] {K W : Subgroup Y}
    (hKp : ⁅K, K⁆ = K) (hKW : K ≤ Subgroup.normalizer (W : Set Y)) (hW : Nat.card W ≤ q)
    (hWq : IsPGroup q ↥W) : K ≤ Subgroup.centralizer (W : Set Y) := by
  by_cases hW1 : W = ⊥
  · intro k _
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [hW1] at hh
    rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
  obtain ⟨⟨u, huW⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hWu : W = Subgroup.zpowers u := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWq
    have hk1 : k ≤ 1 := by
      by_contra h
      have : q ^ 2 ≤ q ^ k := Nat.pow_le_pow_right hq.out.pos (by omega)
      have h2 : q < q ^ 2 := by
        have := hq.out.two_le
        nlinarith
      omega
    have hle : Subgroup.zpowers u ≤ W := Subgroup.zpowers_le.mpr huW
    have hcu : Nat.card (Subgroup.zpowers u) ≠ 1 := by
      rw [Nat.card_zpowers]
      exact fun h => hu1' (orderOf_eq_one_iff.mp h)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hk] at hdvd ⊢
    interval_cases k
    · rw [pow_zero, Nat.dvd_one] at hdvd
      exact absurd hdvd hcu
    · rw [pow_one] at hdvd ⊢
      rcases (Nat.dvd_prime hq.out).mp hdvd with h | h
      · exact absurd h hcu
      · exact h.ge
  have hpow : ∀ k ∈ K, ∃ a : ℤ, k * u * k⁻¹ = u ^ a := by
    intro k hk
    have h := (Subgroup.mem_normalizer_iff.mp (hKW hk) u).mp huW
    rw [hWu] at h
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h
    exact ⟨a, ha.symm⟩
  have hconj : ∀ (k : Y) (a : ℤ), k * u ^ a * k⁻¹ = (k * u * k⁻¹) ^ a := fun k a =>
    (conj_zpow).symm
  have hconj' : ∀ (k : Y) (a : ℤ), k⁻¹ * u ^ a * k = (k⁻¹ * u * k) ^ a := fun k a => by
    have h := (conj_zpow (a := k⁻¹) (b := u) (i := a)).symm
    rwa [inv_inv] at h
  have hcomm : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ⁅k₁, k₂⁆ * u = u * ⁅k₁, k₂⁆ := by
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨a₁, ha₁⟩ := hpow k₁ hk₁
    obtain ⟨a₂, ha₂⟩ := hpow k₂ hk₂
    obtain ⟨b₁, hb₁⟩ := hpow k₁⁻¹ (K.inv_mem hk₁)
    obtain ⟨b₂, hb₂⟩ := hpow k₂⁻¹ (K.inv_mem hk₂)
    rw [inv_inv] at hb₁ hb₂
    have h₁ : u ^ (a₁ * b₁) = u := by
      have h := congrArg (fun x => k₁ * x * k₁⁻¹) hb₁
      rw [hconj, ha₁, ← zpow_mul] at h
      rw [← h]
      group
    have h₂ : u ^ (a₂ * b₂) = u := by
      have h := congrArg (fun x => k₂ * x * k₂⁻¹) hb₂
      rw [hconj, ha₂, ← zpow_mul] at h
      rw [← h]
      group
    have hc : ⁅k₁, k₂⁆ * u * ⁅k₁, k₂⁆⁻¹ = u := by
      have e : ⁅k₁, k₂⁆ * u * ⁅k₁, k₂⁆⁻¹ =
          k₁ * (k₂ * (k₁⁻¹ * (k₂⁻¹ * u * k₂) * k₁) * k₂⁻¹) * k₁⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e, hb₂, hconj', hb₁, ← zpow_mul, hconj, ha₂, ← zpow_mul, hconj, ha₁, ← zpow_mul]
      calc u ^ (a₁ * (a₂ * (b₁ * b₂))) = (u ^ (a₁ * b₁)) ^ (a₂ * b₂) := by
            rw [← zpow_mul]
            congr 1
            ring
        _ = u := by rw [h₁, h₂]
    calc ⁅k₁, k₂⁆ * u = ⁅k₁, k₂⁆ * u * ⁅k₁, k₂⁆⁻¹ * ⁅k₁, k₂⁆ := by group
      _ = u * ⁅k₁, k₂⁆ := by rw [hc]
  calc K = ⁅K, K⁆ := hKp.symm
    _ ≤ Subgroup.centralizer (W : Set Y) := by
      rw [Subgroup.commutator_le]
      intro k₁ hk₁ k₂ hk₂
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [hWu] at hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left (hcomm k₁ hk₁ k₂ hk₂).symm n)).eq

theorem mem_pCore_of_mem_fitting (hnil : Group.IsNilpotent ↥(CFSG.fittingSubgroup Y)) {r : ℕ}
    [Fact r.Prime] {x : Y} (hx : x ∈ CFSG.fittingSubgroup Y) {i : ℕ} (hxo : orderOf x = r ^ i) :
    x ∈ CFSG.pCore r Y := by
  set N := CFSG.fittingSubgroup Y with hN
  have hNn : N.Normal := CFSG.fittingSubgroup_normal
  have hp : IsPGroup r (Subgroup.zpowers (⟨x, hx⟩ : ↥N)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hxo])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  exact Sylow.map_le_pCore hNn hnil r S ⟨_, hS (Subgroup.mem_zpowers _), rfl⟩

omit [Finite Y] in
theorem eq_one_of_case_three (h3 : A36Case3 Y) {w : Y} (hw2 : w * w = 1)
    (hwF : w ∉ CFSG.fittingSubgroup Y) {f : Y} (hf : f ∈ CFSG.fittingSubgroup Y)
    (hwf : w * f = f * w) : f = 1 := by
  obtain ⟨p, hp, hp3, -, -, e, ψ, -, hker, hact⟩ := h3
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
      omega
    exact_mod_cast h
  have hψ1 : ψ w ≠ 1 := fun h => hwF (hker ▸ MonoidHom.mem_ker.mpr h)
  have hψ2 : ψ w ^ 2 = 1 := by rw [pow_two, ← map_mul, hw2, map_one]
  have hm := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (ψ w) hψ2 hψ1
  have hc : MulAut.conjNormal w (⟨f, hf⟩ : ↥(CFSG.fittingSubgroup Y)) = ⟨f, hf⟩ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply, hwf, mul_inv_cancel_right])
  have h := hact w ⟨f, hf⟩
  rw [hc, hm, Matrix.neg_mulVec, Matrix.one_mulVec] at h
  have hv : Multiplicative.toAdd (e ⟨f, hf⟩) = 0 := by
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_ofAdd] at h'
    funext i
    have hi := congrFun h' i
    simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
    have h2i : (2 : ZMod p) * Multiplicative.toAdd (e ⟨f, hf⟩) i = 0 := by
      linear_combination hi
    exact (mul_eq_zero.mp h2i).resolve_left h2
  have he : e ⟨f, hf⟩ = 1 := by
    rw [← ofAdd_toAdd (e ⟨f, hf⟩), hv, ofAdd_zero]
  simpa using congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).mp he)

theorem commute_of_case_four (h4 : A36Case4 Y) (hE : A36Extra Y) {K : Subgroup Y}
    (hKF : K ⊓ CFSG.fittingSubgroup Y = ⊥) (hKp : ⁅K, K⁆ = K) {k₁ k₂ : Y} (hk₁ : k₁ ∈ K)
    (hk₂ : k₂ ∈ K) (hk : k₁ * k₂ ≠ k₂ * k₁) {w : Y} (hw2 : w * w = 1)
    (hwF : w ∉ CFSG.fittingSubgroup Y) (hwK : ∀ k ∈ K, k * w = w * k) {f : Y}
    (hf : f ∈ CFSG.fittingSubgroup Y) (hwf : w * f = f * w) :
    (∀ k ∈ K, f * k = k * f) ∧
      ∀ f' ∈ CFSG.fittingSubgroup Y, w * f' = f' * w → f * f' = f' * f := by
  obtain ⟨-, hnil, -, hprimes⟩ := h4
  set F := CFSG.fittingSubgroup Y with hFdef
  have hW : ∀ r : ℕ, r.Prime → r ∣ Nat.card F →
      Nat.card ↥(CFSG.pCore r Y ⊓ Subgroup.centralizer ({w} : Set Y)) ≤ r := by
    intro r hr hrF
    have : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      rcases (hprimes 2 hr hrF).1 with h | h | h <;> omega
    obtain ⟨P, hsc, -, hPt, hker⟩ := hE r hr hrF
    have hinv := mul_conj_mem_frattiniIn hr2 hsc hPt hker hKF hk₁ hk₂ hk hw2 hwF
      (hwK k₁ hk₁) (hwK k₂ hk₂)
    exact card_inf_centralizer_le hr2 hsc hPt (hprimes r hr hrF).2 hinv
  have hpart : ∀ x ∈ F, w * x = x * w → ∀ j : ℕ, IsPrimePow (orderOf (x ^ j)) →
      ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card F ∧
        x ^ j ∈ CFSG.pCore r Y ⊓ Subgroup.centralizer ({w} : Set Y) := by
    intro x hx hwx j hj
    obtain ⟨r, i, hr, hi, hri⟩ := hj
    have hr' : r.Prime := Nat.prime_iff.mpr hr
    have : Fact r.Prime := ⟨hr'⟩
    have hxj : x ^ j ∈ F := F.pow_mem hx j
    refine ⟨r, hr', ?_, Subgroup.mem_inf.mpr ⟨mem_pCore_of_mem_fitting hnil hxj hri.symm, ?_⟩⟩
    · refine (dvd_pow_self r hi.ne').trans ?_
      rw [hri]
      exact Subgroup.orderOf_dvd_natCard F hxj
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Commute.pow_right (show Commute w x from hwx) j)).eq.symm
  have hKW : ∀ r : ℕ, r.Prime → r ∣ Nat.card F →
      K ≤ Subgroup.centralizer
        ((CFSG.pCore r Y ⊓ Subgroup.centralizer ({w} : Set Y) : Subgroup Y) : Set Y) := by
    intro r hr hrF
    have : Fact r.Prime := ⟨hr⟩
    refine le_centralizer_of_card_le hKp ?_ (hW r hr hrF)
      (CFSG.pCore_isPGroup.to_le inf_le_left)
    intro k hk
    have hN : Subgroup.normalizer ((CFSG.pCore r Y : Subgroup Y) : Set Y) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨by rw [hN]; exact Subgroup.mem_top k, ?_⟩
    exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hwK k hk))
  have hWab : ∀ r : ℕ, r.Prime → r ∣ Nat.card F →
      ∀ a ∈ CFSG.pCore r Y ⊓ Subgroup.centralizer ({w} : Set Y),
      ∀ b ∈ CFSG.pCore r Y ⊓ Subgroup.centralizer ({w} : Set Y), a * b = b * a := by
    intro r hr hrF a ha b hb
    have : Fact r.Prime := ⟨hr⟩
    set W := CFSG.pCore r Y ⊓ Subgroup.centralizer ({w} : Set Y)
    have hcard := hW r hr hrF
    have hWq : IsPGroup r ↥W := CFSG.pCore_isPGroup.to_le inf_le_left
    by_cases ha1 : a = 1
    · rw [ha1, one_mul, mul_one]
    have hza : Subgroup.zpowers a ≤ W := Subgroup.zpowers_le.mpr ha
    have hzW : Subgroup.zpowers a = W := by
      refine Subgroup.eq_of_le_of_card_ge hza ?_
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWq
      have hdvd := Subgroup.card_dvd_of_le hza
      rw [hk] at hdvd hcard ⊢
      have hk1 : k ≤ 1 := by
        by_contra h
        have : r ^ 2 ≤ r ^ k := Nat.pow_le_pow_right hr.pos (by omega)
        have h2 : r < r ^ 2 := by
          have := hr.two_le
          nlinarith
        omega
      have hca : Nat.card (Subgroup.zpowers a) ≠ 1 := by
        rw [Nat.card_zpowers]
        exact fun h => ha1 (orderOf_eq_one_iff.mp h)
      interval_cases k
      · rw [pow_zero, Nat.dvd_one] at hdvd
        exact absurd hdvd hca
      · rw [pow_one] at hdvd ⊢
        rcases (Nat.dvd_prime hr).mp hdvd with h | h
        · exact absurd h hca
        · exact h.ge
    rw [← hzW] at hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (Commute.refl a) n).eq
  refine ⟨fun k hk => ?_, fun f' hf' hwf' => ?_⟩
  ·
    have hmem : f ∈ Subgroup.centralizer (K : Set Y) := by
      refine mem_of_forall_primePow (isOfFinOrder_of_finite f) fun j hj => ?_
      obtain ⟨r, hr, hrF, hfr⟩ := hpart f hf hwf j hj
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      exact (Subgroup.mem_centralizer_iff.mp (hKW r hr hrF hk') _ hfr).symm
    exact (Subgroup.mem_centralizer_iff.mp hmem k hk).symm
  ·
    have hmem : f ∈ Subgroup.centralizer ({f'} : Set Y) := by
      refine mem_of_forall_primePow (isOfFinOrder_of_finite f) fun j hj => ?_
      obtain ⟨r, hr, hrF, hfr⟩ := hpart f hf hwf j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hmem' : f' ∈ Subgroup.centralizer ({f ^ j} : Set Y) := by
        refine mem_of_forall_primePow (isOfFinOrder_of_finite f') fun j' hj' => ?_
        obtain ⟨r', hr', hrF', hfr'⟩ := hpart f' hf' hwf' j' hj'
        rw [Subgroup.mem_centralizer_singleton_iff]
        by_cases hrr : r = r'
        · subst hrr
          exact (hWab r hr hrF _ hfr _ hfr').symm
        · have : Fact r.Prime := ⟨hr⟩
          have : Fact r'.Prime := ⟨hr'⟩
          have hdis : Disjoint (CFSG.pCore r Y) (CFSG.pCore r' Y) :=
            IsPGroup.disjoint_of_ne r r' hrr _ _ CFSG.pCore_isPGroup CFSG.pCore_isPGroup
          exact (Subgroup.commute_of_normal_of_disjoint _ _ CFSG.pCore_normal CFSG.pCore_normal
            hdis _ _ hfr.1 hfr'.1).eq.symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp hmem').symm
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem

theorem commute_props (h34 : A36Case3 Y ∨ A36Case4 Y) (hE : A36Extra Y) {K : Subgroup Y}
    (hKF : K ⊓ CFSG.fittingSubgroup Y = ⊥) (hKp : ⁅K, K⁆ = K) {k₁ k₂ : Y} (hk₁ : k₁ ∈ K)
    (hk₂ : k₂ ∈ K) (hk : k₁ * k₂ ≠ k₂ * k₁) {w : Y} (hw2 : w * w = 1)
    (hwF : w ∉ CFSG.fittingSubgroup Y) (hwK : ∀ k ∈ K, k * w = w * k) {f : Y}
    (hf : f ∈ CFSG.fittingSubgroup Y) (hwf : w * f = f * w) :
    (∀ k ∈ K, f * k = k * f) ∧
      ∀ f' ∈ CFSG.fittingSubgroup Y, w * f' = f' * w → f * f' = f' * f := by
  rcases h34 with h3 | h4
  · have hf1 := eq_one_of_case_three h3 hw2 hwF hf hwf
    subst hf1
    exact ⟨fun k _ => by rw [one_mul, mul_one], fun f' _ _ => by rw [one_mul, mul_one]⟩
  · exact commute_of_case_four h4 hE hKF hKp hk₁ hk₂ hk hw2 hwF hwK hf hwf

end CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv
