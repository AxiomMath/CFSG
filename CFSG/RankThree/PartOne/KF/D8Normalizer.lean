module

public import CFSG.RankThree.PartOne.KF.D8Module
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K]

theorem eq_bot_or_eq_top_of_d8Invariant (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (B : Subgroup (D8Mod p K))
    (hB : ∀ (w : DihedralGroup 4), ∀ d ∈ B, d8Act w d ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have : Fact p.Prime := ⟨hp⟩
  have hμ : Nat.card (rootsOfUnity p K) = p := card_rootsOfUnity_eq' hp.pos hζ
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨d, hdB⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hy : ∃ y : rootsOfUnity p K, y ≠ 1 ∧ ((1 : rootsOfUnity p K), y) ∈ B := by
    by_cases hb : d.2 = 1
    · have ha : d.1 ≠ 1 := fun ha => hd1' (Prod.ext ha hb)
      refine ⟨d.1⁻¹, inv_ne_one.mpr ha, ?_⟩
      have := hB (DihedralGroup.r 1) d hdB
      rw [d8Act_r_one, hb] at this
      exact this
    · refine ⟨d.2 * d.2, fun h => hb (eq_one_of_sq_eq_one_of_odd hpodd (by rwa [pow_two])), ?_⟩
      have h1 := hB (DihedralGroup.sr 0) d hdB
      rw [d8Act_sr_zero] at h1
      have h2 := B.mul_mem hdB h1
      have : d * (d.1⁻¹, d.2) = ((1 : rootsOfUnity p K), d.2 * d.2) :=
        Prod.ext (mul_inv_cancel _) rfl
      rwa [this] at h2
  obtain ⟨y, hy1, hyB⟩ := hy
  have hline : ∀ z : rootsOfUnity p K, ((1 : rootsOfUnity p K), z) ∈ B := by
    intro z
    obtain ⟨k, rfl⟩ := mem_zpowers_of_prime_card hμ hy1 (g' := z)
    have : ((1 : rootsOfUnity p K), y ^ k) = ((1 : rootsOfUnity p K), y) ^ k := by
      ext <;> simp
    rw [this]
    exact B.zpow_mem hyB k
  have hline' : ∀ z : rootsOfUnity p K, (z, (1 : rootsOfUnity p K)) ∈ B := by
    intro z
    have := hB (DihedralGroup.r 1) _ (hline z)
    rw [d8Act_r_one] at this
    simpa using this
  rw [eq_top_iff]
  intro d _
  have : d = (d.1, 1) * (1, d.2) := Prod.ext (mul_one _).symm (one_mul _).symm
  rw [this]
  exact B.mul_mem (hline' _) (hline _)

theorem movedV_conj {V : Type*} [Group V] (φ ψ : MulAut V) :
    movedV (φ * ψ * φ⁻¹) = (movedV ψ).map φ.toMonoidHom := by
  unfold movedV
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨ψ (φ⁻¹ v) * (φ⁻¹ v)⁻¹, ⟨φ⁻¹ v, rfl⟩, ?_⟩
    simp
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨φ u, by simp⟩

theorem card_movedV_sr (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (i : ZMod 4) : Nat.card (movedV (d8Act (p := p) (K := K) (DihedralGroup.sr i))) = p := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl
  · exact card_movedV_sr_zero hp hp2 hζ
  · exact card_movedV_sr_one hp hp2 hζ
  · exact card_movedV_sr_two hp hp2 hζ
  · exact card_movedV_sr_three hp hζ

theorem perm_zmod_four_eq_one_of_pow_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (π : Equiv.Perm (ZMod 4)) (hπ : π ^ p = 1) : π = 1 := by
  have h1 : orderOf π ∣ p := orderOf_dvd_of_pow_eq_one hπ
  have h2 : orderOf π ∣ 24 := by
    have h24 : Nat.card (Equiv.Perm (ZMod 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ZMod.card]
      simp [Nat.factorial]
    rw [← h24]
    exact orderOf_dvd_natCard π
  have hcop : Nat.Coprime p 24 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
    have hle : p ≤ 24 := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> first | omega | (norm_num at hp)
  have h3 : orderOf π ∣ Nat.gcd p 24 := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem exists_sr_conj (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (φ : MulAut (D8Mod p K))
    (hnorm : ∀ w : DihedralGroup 4, ∃ w' : DihedralGroup 4,
      φ * d8Act w * φ⁻¹ = d8Act w') (i : ZMod 4) :
    ∃ j : ZMod 4, φ * d8Act (DihedralGroup.sr i) * φ⁻¹ = d8Act (DihedralGroup.sr j) := by
  have hinj : Function.Injective (d8Act : DihedralGroup 4 →* MulAut (D8Mod p K)) :=
    d8Act_injective hp hp2 hζ
  obtain ⟨w', hw'⟩ := hnorm (DihedralGroup.sr i)
  have hR : (d8Act (DihedralGroup.sr i) : MulAut (D8Mod p K)) *
      d8Act (DihedralGroup.sr i) = 1 := by
    rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
  have hw2 : w' * w' = 1 := by
    apply hinj
    rw [map_mul, ← hw', map_one]
    calc φ * d8Act (DihedralGroup.sr i) * φ⁻¹ * (φ * d8Act (DihedralGroup.sr i) * φ⁻¹) =
        φ * (d8Act (DihedralGroup.sr i) * d8Act (DihedralGroup.sr i)) * φ⁻¹ := by group
      _ = 1 := by rw [hR]; group
  have hw1 : w' ≠ 1 := by
    intro h
    rw [h, map_one] at hw'
    have h1 : (d8Act (DihedralGroup.sr i) : MulAut (D8Mod p K)) = 1 := by
      have := congrArg (fun m => φ⁻¹ * m * φ) hw'
      simpa [mul_assoc] using this
    have := hinj (h1.trans (map_one _).symm)
    rw [DihedralGroup.one_def] at this
    cases this
  have hc : Nat.card (movedV (d8Act (p := p) (K := K) w')) = p := by
    rw [← hw', movedV_conj, Subgroup.card_map_of_injective φ.injective]
    exact card_movedV_sr hp hp2 hζ i
  obtain ⟨j, rfl⟩ := exists_sr_of_card_moved hp hp2 hζ hw2 hw1 hc
  exact ⟨j, hw'⟩


theorem commutes_reflections_of_normalizes (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ : MulAut (D8Mod p K)) (hφp : φ ^ p = 1)
    (hnorm : ∀ w : DihedralGroup 4, ∃ w' : DihedralGroup 4, φ * d8Act w * φ⁻¹ = d8Act w')
    (i : ZMod 4) : φ * d8Act (DihedralGroup.sr i) = d8Act (DihedralGroup.sr i) * φ := by
  have hinj : Function.Injective (d8Act : DihedralGroup 4 →* MulAut (D8Mod p K)) :=
    d8Act_injective hp hp2 hζ
  have hex := exists_sr_conj hp hp2 hζ φ hnorm
  choose c hc using hex
  have hcinj : Function.Injective c := by
    intro i i' h
    have h1 : φ * d8Act (DihedralGroup.sr i) * φ⁻¹ = φ * d8Act (DihedralGroup.sr i') * φ⁻¹ := by
      rw [hc i, hc i', h]
    have h2 : (d8Act (DihedralGroup.sr i) : MulAut (D8Mod p K)) = d8Act (DihedralGroup.sr i') :=
      mul_left_cancel (mul_right_cancel h1)
    exact DihedralGroup.sr.inj (hinj h2)
  let π : Equiv.Perm (ZMod 4) := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hcinj)
  have hπ : ∀ k : ℕ, ∀ i, φ ^ k * d8Act (DihedralGroup.sr i) * (φ ^ k)⁻¹ =
      d8Act (DihedralGroup.sr ((π ^ k) i)) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      calc φ ^ (k + 1) * d8Act (DihedralGroup.sr i) * (φ ^ (k + 1))⁻¹ =
          φ * (φ ^ k * d8Act (DihedralGroup.sr i) * (φ ^ k)⁻¹) * φ⁻¹ := by group
        _ = φ * d8Act (DihedralGroup.sr ((π ^ k) i)) * φ⁻¹ := by rw [ih]
        _ = d8Act (DihedralGroup.sr (c ((π ^ k) i))) := hc _
        _ = d8Act (DihedralGroup.sr ((π ^ (k + 1)) i)) := by
          rw [pow_succ', Equiv.Perm.mul_apply]; rfl
  have hπp : π ^ p = 1 := by
    refine Equiv.ext fun j => ?_
    have h1 := hπ p j
    rw [hφp] at h1
    have h2 : (d8Act (DihedralGroup.sr j) : MulAut (D8Mod p K)) =
        d8Act (DihedralGroup.sr ((π ^ p) j)) := by simpa using h1
    exact (DihedralGroup.sr.inj (hinj h2)).symm
  have hπ1 := perm_zmod_four_eq_one_of_pow_prime hp h5 π hπp
  have hci : c i = i := by
    have := congrArg (fun σ : Equiv.Perm (ZMod 4) => σ i) hπ1
    simpa [π] using this
  have h1 := hc i
  rw [hci] at h1
  calc φ * d8Act (DihedralGroup.sr i) = φ * d8Act (DihedralGroup.sr i) * φ⁻¹ * φ := by group
    _ = d8Act (DihedralGroup.sr i) * φ := by rw [h1]


theorem eq_one_of_commutes_reflections (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ : MulAut (D8Mod p K)) (hφp : φ ^ p = 1)
    (h2 : φ * d8Act (DihedralGroup.sr 2) = d8Act (DihedralGroup.sr 2) * φ)
    (h3 : φ * d8Act (DihedralGroup.sr 3) = d8Act (DihedralGroup.sr 3) * φ) : φ = 1 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hμ : Nat.card (rootsOfUnity p K) = p := card_rootsOfUnity_eq' hp.pos hζ
  have hfin : Finite (rootsOfUnity p K) :=
    Nat.finite_of_card_ne_zero (by rw [hμ]; exact hp.ne_zero)
  have hA : ∀ a : rootsOfUnity p K, (φ (a, 1)).2 = 1 := by
    intro a
    have := congrArg (fun m : MulAut (D8Mod p K) => m (a, 1)) h2
    simp only [MulAut.mul_apply, d8Act_sr_two, inv_one] at this
    exact eq_one_of_inv_eq_self hpodd (congrArg Prod.snd this).symm
  have hC : ∀ a : rootsOfUnity p K, φ (1, a) = (1, (φ (a, 1)).1) := by
    intro a
    have := congrArg (fun m : MulAut (D8Mod p K) => m (a, 1)) h3
    simp only [MulAut.mul_apply, d8Act_sr_three] at this
    rw [this, hA]
  let g : rootsOfUnity p K →* rootsOfUnity p K :=
    (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp (MonoidHom.inl _ _))
  have hg : ∀ a, φ (a, 1) = (g a, 1) := fun a => Prod.ext rfl (hA a)
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 : φ (a, 1) = φ (b, 1) := by rw [hg, hg, hab]
    exact congrArg Prod.fst (φ.injective h1)
  let g' : MulAut (rootsOfUnity p K) :=
    MulEquiv.ofBijective g ⟨hginj, Finite.injective_iff_surjective.mp hginj⟩
  have hgk : ∀ k : ℕ, ∀ a, (φ ^ k) (a, 1) = ((g' ^ k) a, 1) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih, hg]
      rfl
  have hg'p : g' ^ p = 1 := by
    refine MulEquiv.ext fun a => ?_
    have := hgk p a
    rw [hφp] at this
    exact (congrArg Prod.fst this).symm
  have hg'1 : g' = 1 := by
    have h1 : orderOf g' ∣ p := orderOf_dvd_of_pow_eq_one hg'p
    have h2 : orderOf g' ∣ p - 1 := by
      have := orderOf_dvd_natCard g'
      rwa [IsCyclic.card_mulAut, hμ, Nat.totient_prime hp] at this
    have hcop : Nat.Coprime p (p - 1) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
      have h1 : 0 < p - 1 := by have := hp.two_le; omega
      exact Nat.not_dvd_of_pos_of_lt h1 (by have := hp.two_le; omega) hd
    have h3 : orderOf g' ∣ Nat.gcd p (p - 1) := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hgid : ∀ a, g a = a := fun a => by
    have := congrArg (fun m : MulAut (rootsOfUnity p K) => m a) hg'1
    exact this
  refine MulEquiv.ext fun v => ?_
  have hv : v = (v.1, 1) * (1, v.2) := Prod.ext (mul_one _).symm (one_mul _).symm
  rw [hv, map_mul, hg, hC, hg, hgid, hgid]
  rfl


theorem eq_one_of_normalizes_d8 (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ : MulAut (D8Mod p K)) (hφp : φ ^ p = 1)
    (hnorm : ∀ w : DihedralGroup 4, ∃ w' : DihedralGroup 4, φ * d8Act w * φ⁻¹ = d8Act w') :
    φ = 1 :=
  eq_one_of_commutes_reflections hp hp2 hζ φ hφp
    (commutes_reflections_of_normalizes hp hp2 h5 hζ φ hφp hnorm 2)
    (commutes_reflections_of_normalizes hp hp2 h5 hζ φ hφp hnorm 3)

end CFSG.RankThree.PartOne.KFU
