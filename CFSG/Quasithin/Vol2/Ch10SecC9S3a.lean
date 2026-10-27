module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_of_forall_primePow {M Y : Subgroup G} {N : ℕ}
    (hY : ∀ p : ℕ, p.Prime → p ∣ N → ∀ y ∈ M, ∀ k : ℕ, y ^ p ^ k = 1 → y ∈ Y) :
    ∀ x ∈ M, orderOf x ∣ N → x ∈ Y := by
  intro x
  induction h : orderOf x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    intro hx hm
    by_cases hm1 : m = 1
    · rw [hm1, orderOf_eq_one_iff] at h
      rw [h]
      exact Y.one_mem
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hm0 : m ≠ 0 := by rw [← h]; exact (orderOf_pos x).ne'
    obtain ⟨a, m', hm', hma⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
    have hcop : Nat.Coprime (p ^ a) m' :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm')
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · exfalso
        rw [ha, pow_zero, one_mul] at hma
        exact hm' (hma ▸ hpm)
      · exact ha
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (p ^ a : ℕ) + v * m' = 1 := by
      refine ⟨Nat.gcdA (p ^ a) m', Nat.gcdB (p ^ a) m', ?_⟩
      have := Nat.gcd_eq_gcd_ab (p ^ a) m'
      rw [hcop.gcd_eq_one] at this
      push_cast at this ⊢
      linarith
    have hxm : ∀ w : ℤ, x ^ (w * (m : ℤ)) = 1 := fun w => by
      rw [mul_comm w, zpow_mul, zpow_natCast, ← h, pow_orderOf_eq_one, one_zpow]
    have hx1 : x = x ^ (u * (p ^ a : ℕ)) * x ^ (v * m') := by
      rw [← zpow_add, huv, zpow_one]
    rw [hx1]
    refine Y.mul_mem ?_ ?_
    ·
      have hord : orderOf (x ^ (u * (p ^ a : ℕ))) ∣ m' := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← zpow_natCast, ← zpow_mul]
        have e : u * ((p ^ a : ℕ) : ℤ) * (m' : ℤ) = u * (m : ℤ) := by
          rw [hma]; push_cast; ring
        rw [e, hxm]
      have hm'pos : 0 < m' := Nat.pos_of_ne_zero fun h0 => hm0 (by rw [hma, h0, mul_zero])
      have hlt : orderOf (x ^ (u * (p ^ a : ℕ))) < m := by
        refine lt_of_le_of_lt (Nat.le_of_dvd hm'pos hord) ?_
        rw [hma]
        calc m' = 1 * m' := (one_mul _).symm
          _ < p ^ a * m' := Nat.mul_lt_mul_of_pos_right (Nat.one_lt_pow ha.ne' hp.one_lt) hm'pos
      exact ih _ hlt _ rfl (M.zpow_mem hx _)
        (hord.trans ((Dvd.intro_left _ hma.symm).trans hm))
    ·
      refine hY p hp (hpm.trans hm) _ (M.zpow_mem hx _) a ?_
      rw [← zpow_natCast, ← zpow_mul]
      have e : v * (m' : ℤ) * ((p ^ a : ℕ) : ℤ) = v * (m : ℤ) := by
        rw [hma]; push_cast; ring
      rw [e, hxm]

theorem le_fsuL0_of_dvd (hyp : Hyp10 G T L I) (h1013 : Stmt10_1_3) {X : Subgroup G}
    (hXM : X ≤ fsuM T L) {N : ℕ} (hXN : Nat.card X ∣ N)
    (hN : ∀ p : ℕ, p.Prime → p ∣ N → p ≠ 2 ∧ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    X ≤ fsuL0 T L := by
  intro x hx
  have hord : orderOf x ∣ N := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥X)
    rw [Subgroup.orderOf_mk] at this
    exact this.trans hXN
  refine mem_of_forall_primePow (M := X) (fun p hp hpN y hy k hyk => ?_) x hx hord
  obtain ⟨hp2, hpL⟩ := hN p hp hpN
  rw [← h1013 G T L I hyp p hp hp2 hpL]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hyk)
  exact Subgroup.subset_closure ⟨hXM hy, j, hj⟩

theorem fsuM_inf_centralizer_le (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {w : G}
    (hwW : w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hwV1 : w ∉ fsuUL T L I) :
    fsuM T L ⊓ Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  rintro s ⟨hs, hsw⟩
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn hs with h | h
  · exact SecA.conjugate_eq_self_iff.mp h
  · exfalso
    have hsw' : s * w * s⁻¹ = w := mul_conj_eq_of_mem_centralizer hsw
    have key : w ∈ ⁅fsuVM T L I, CFSG.conjugate L s⁆ := by
      rw [h]
      exact hwW
    rw [← SecA.conjugate_commutator_fsuVM (I := I) hs, SecA.mem_conjugate_iff, hsw'] at key
    exact hwV1 key

theorem le_centralizer_of_le_fsuL0
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {X : Subgroup G}
    (hXL0 : X ≤ fsuL0 T L) (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ fsuUL T L I) :
    X ≤ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, -, -⟩ := hdec t ht htn
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hVL : fsuVM T L I ≤ Subgroup.normalizer (L : Set G) :=
    (fsuVM_le_Q hyp).trans (Q_le_T1 h37 h38 hyp h1011) |>.trans inf_le_right
  have hV1L : fsuUL T L I ≤ L := by
    rw [fsuUL, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer hVL
  have hO : fsuUL T L I ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hV1L (le_normalizer_fsuUL T L I)
      ((SecA.isPGroup_fsuVM hyp).to_le hV1V)
  intro x hx
  have hx' : x ∈ (↑(L ⊔ CFSG.conjugate L t) : Set G) := by
    rw [← SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact hXL0 hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (conjugate_le_normalizer hyp ht)] at hx'
  obtain ⟨l, hl, l', hl', hll'⟩ := hx'
  have hll'' : l * l' = x := hll'
  have hlc : ∀ y ∈ L, ⁅l, y⁆ ∈ pCoreOf 2 L := by
    intro y hy
    have h1 := hO (hXL x hx y hy)
    have h2 : l' * y * l'⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
      have := (SecA.commutator_conjugate_le h37 hyp ht htn
        (Subgroup.commutator_mem_commutator hy hl')).1
      have h3 := (pCoreOf 2 L).inv_mem this
      rwa [commutatorElement_inv, commutatorElement_def] at h3
    have e : ⁅l, y⁆ = (l * (l' * y * l'⁻¹ * y⁻¹) * l⁻¹)⁻¹ * (x * y * x⁻¹ * y⁻¹) := by
      rw [← hll'', commutatorElement_def]
      group
    rw [e]
    refine (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem ?_) h1
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) _).mp h2
  have hlO := mem_pCoreOf_of_commutator_mem hl hsimp
    (nonabelian_of_isQuasisimple hyp.fsu.quasisimple) hlc
  have hlV := pCoreOf_L_le_centralizer hyp h1011 hlO
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← hll'']
  have h4 : l * v = v * l := (Subgroup.mem_centralizer_iff.mp hlV v (hV1V hv)).symm
  have h5 : l' * v = v * l' := Subgroup.mem_centralizer_iff.mp (hV1 hv) l' hl'
  calc v * (l * l') = l * v * l' := by rw [← mul_assoc, ← h4]
    _ = l * l' * v := by rw [mul_assoc, ← h5, ← mul_assoc]

end CFSG.Quasithin.Vol2.Ch10.SecC
