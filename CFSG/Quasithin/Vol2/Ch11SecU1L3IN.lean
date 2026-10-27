module

public import CFSG.Quasithin.EmptyFaithful.E22PL2PglC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.GorensteinWalter
open scoped Pointwise
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange outerTorusOrder
  outerTorusOrder_mod_four six_le_outerTorusOrder outer_involution_centralizer
  zpowers_le_normalizer_of_inverting odd_card_of_isOddPrimePower pslRange_normal
  pslRange_index_eq_two)

section Dihedral

variable {G : Type*} [Group G] {U : Subgroup G} {w : G}

theorem eq_mul_of_mem_sup_zpowers (hww : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    {y : G} (hy : y ∈ U ⊔ Subgroup.zpowers w) (hyU : y ∉ U) : ∃ u ∈ U, y = u * w := by
  have hnorm := zpowers_le_normalizer_of_inverting hww hwinv
  have hymul : y ∈ (U : Set G) * (Subgroup.zpowers w : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U _ hnorm]
    exact hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hymul
  rcases E22L2.e22pl2pgl_mem_zpowers_involution hww hv with h | h
  · exact absurd (by rw [h, mul_one]; exact hu) hyU
  · exact ⟨u, hu, by rw [h]⟩

theorem inverts_of_mem_sup_zpowers (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hww : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) {y : G}
    (hy : y ∈ U ⊔ Subgroup.zpowers w) (hyU : y ∉ U) : ∀ x ∈ U, y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := eq_mul_of_mem_sup_zpowers hww hwinv hy hyU
  intro x hx
  have h1 : u * w * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
  rw [h1, hwinv x hx, hcomm u hu x⁻¹ (U.inv_mem hx)]
  group

theorem mem_normalizer_zpowers_pow {γ c : G} (hc : c ∈ Subgroup.normalizer
    ((Subgroup.zpowers γ : Subgroup G) : Set G)) (d : ℕ) :
    c ∈ Subgroup.normalizer ((Subgroup.zpowers (γ ^ d) : Subgroup G) : Set G) := by
  have key : ∀ c' ∈ Subgroup.normalizer ((Subgroup.zpowers γ : Subgroup G) : Set G),
      ∀ h ∈ Subgroup.zpowers (γ ^ d), c' * h * c'⁻¹ ∈ Subgroup.zpowers (γ ^ d) := by
    intro c' hc' h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hc' γ).mp (Subgroup.mem_zpowers γ))
    have h1 : c' * (γ ^ d) ^ j * c'⁻¹ = ((c' * γ * c'⁻¹) ^ d) ^ j := by
      rw [conj_pow, conj_zpow]
    rw [h1, ← hk]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k * j, ?_⟩
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key c hc h, fun hh => ?_⟩
  have := key c⁻¹ (Subgroup.inv_mem _ hc) _ hh
  simpa [mul_assoc] using this

end Dihedral

variable {K : Type} [Field K] [Finite K]

theorem mem_pslRange_of_pow_eq_one (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {g : PGL2 K} {r : ℕ} (hr : Odd r) (hg : g ^ r = 1) : g ∈ pslRange K := by
  have := pslRange_normal hK hcard
  have h2 : g ^ 2 ∈ pslRange K := by
    have := Subgroup.pow_index_mem (pslRange K) g
    rwa [pslRange_index_eq_two hK] at this
  obtain ⟨k, rfl⟩ := hr
  have : g = (g ^ 2) ^ (k + 1) := by
    calc g = g ^ (2 * k + 1) * g := by rw [hg, one_mul]
      _ = (g ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_succ]; ring_nf
  rw [this]
  exact Subgroup.pow_mem _ h2 _

omit [Finite K] in
theorem sq_eq_one_of_isPGroup_of_card_mod_four {U : Subgroup (PGL2 K)} [Finite U]
    (hU : Nat.card U % 4 = 2) {q : PGL2 K} (hqU : q ∈ U) {n : ℕ} (hq : q ^ 2 ^ n = 1) :
    q ^ 2 = 1 := by
  have h1 : orderOf q ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hq
  obtain ⟨i, hi, hiq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf q ∣ Nat.card U := by
    rw [← Subgroup.orderOf_mk q hqU]
    exact orderOf_dvd_natCard _
  rw [hiq] at h2
  have hi1 : i ≤ 1 := by
    by_contra hcon
    have : 4 ∣ Nat.card U := (pow_dvd_pow 2 (by omega : 2 ≤ i)).trans h2
    omega
  have : orderOf q ∣ 2 := by
    rw [hiq]
    exact pow_dvd_pow 2 hi1 |>.trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem exists_odd_torus_of_outer_involution (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {x : PGL2 K} (hx : x ^ 2 = 1) (hxJ : x ∉ pslRange K)
    {Q : Subgroup (PGL2 K)} (hQ : IsPGroup 2 Q)
    (hQx : Q ≤ Subgroup.centralizer ({x} : Set (PGL2 K))) :
    ∃ P : Subgroup (PGL2 K), P ≤ pslRange K ∧ (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
      Q ≤ Subgroup.normalizer (P : Set (PGL2 K)) ∧
      ¬ P ≤ Subgroup.centralizer ({x} : Set (PGL2 K)) := by
  classical
  have := E22L2.e22pl2pgl_finite K
  have hqodd := odd_card_of_isOddPrimePower hK
  have h5 : 5 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hJn := pslRange_normal hK hcard
  have hx1 : x ≠ 1 := fun h => hxJ (h ▸ (pslRange K).one_mem)
  obtain ⟨U, w, hUc, hUcard, hxU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard hx hxJ
  have hU4 : Nat.card U % 4 = 2 := by rw [hUcard]; exact outerTorusOrder_mod_four hqodd
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have h2U : ∀ q ∈ U, q ∈ Q → q = 1 ∨ q = x := by
    intro q hqU hqQ
    obtain ⟨n, hn⟩ := hQ ⟨q, hqQ⟩
    have hq2 := sq_eq_one_of_isPGroup_of_card_mod_four hU4 hqU
      (by simpa using congrArg Subtype.val hn)
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · exact Or.inr (E22L2.e22pl2pgl_involution_unique hUc hqU hxU hq2 hx hq1 hx1)
  obtain ⟨w', hw'C, hw'U, hw'w', hxw', hQV⟩ : ∃ w' : PGL2 K,
      w' ∈ U ⊔ Subgroup.zpowers w ∧ w' ∉ U ∧ w' * w' = 1 ∧ x * w' = w' * x ∧
      ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = w' ∨ q = x * w' := by
    have hinv := fun {y : PGL2 K} (hy : y ∈ U ⊔ Subgroup.zpowers w) (hyU : y ∉ U) =>
      inverts_of_mem_sup_zpowers hUcomm hww hwinv hy hyU
    have hprops : ∀ y ∈ U ⊔ Subgroup.zpowers w, y ∉ U → y * y = 1 ∧ x * y = y * x := by
      intro y hy hyU
      obtain ⟨u, hu, rfl⟩ := eq_mul_of_mem_sup_zpowers hww hwinv hy hyU
      refine ⟨?_, ?_⟩
      · calc u * w * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
          _ = 1 := by rw [hwinv u hu, hww, mul_one, mul_inv_cancel]
      · have h1 := hinv hy hyU x hxU
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)
        rw [hxinv] at h1
        calc x * (u * w) = (u * w * x * (u * w)⁻¹) * (u * w) := by rw [h1]
          _ = u * w * x := by group
    by_cases hQU : Q ≤ U
    · refine ⟨w, Subgroup.mem_sup_right (Subgroup.mem_zpowers w), hwU,
        (hprops w (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)) hwU).1,
        (hprops w (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)) hwU).2, fun q hq => ?_⟩
      rcases h2U q (hQU hq) hq with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨q₀, hq₀Q, hq₀U⟩ := Set.not_subset.mp hQU
      have hq₀C : q₀ ∈ U ⊔ Subgroup.zpowers w := by
        rw [← hC]
        exact hQx hq₀Q
      refine ⟨q₀, hq₀C, hq₀U, (hprops q₀ hq₀C hq₀U).1, (hprops q₀ hq₀C hq₀U).2,
        fun q hq => ?_⟩
      by_cases hqU : q ∈ U
      · rcases h2U q hqU hq with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have hqC : q ∈ U ⊔ Subgroup.zpowers w := by
          rw [← hC]
          exact hQx hq
        obtain ⟨u, hu, rfl⟩ := eq_mul_of_mem_sup_zpowers hww hwinv hqC hqU
        obtain ⟨u₀, hu₀, rfl⟩ := eq_mul_of_mem_sup_zpowers hww hwinv hq₀C hq₀U
        have hmem : u * u₀⁻¹ ∈ U := U.mul_mem hu (U.inv_mem hu₀)
        have hmemQ : u * u₀⁻¹ ∈ Q := by
          have := Q.mul_mem hq (Q.inv_mem hq₀Q)
          simpa [mul_assoc] using this
        rcases h2U _ hmem hmemQ with h | h
        · refine Or.inr (Or.inr (Or.inl ?_))
          rw [mul_inv_eq_one] at h
          rw [h]
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [mul_inv_eq_iff_eq_mul] at h
          rw [h, mul_assoc]
  have hw'1 : w' ≠ 1 := fun h => hw'U (h ▸ U.one_mem)
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx
  obtain ⟨u, huJ, hu2, hux, huQ, hu1⟩ : ∃ u : PGL2 K, u ∉ pslRange K ∧ u ^ 2 = 1 ∧
      x * u = u * x ∧ Q ≤ Subgroup.centralizer ({u} : Set (PGL2 K)) ∧ u ≠ x := by
    have hcx : Commute x w' := hxw'
    have hcomm4 : ∀ v : PGL2 K, (v = w' ∨ v = x * w') → ∀ q ∈ Q, q * v = v * q := by
      intro v hv q hq
      have hcv : Commute x v ∧ Commute w' v ∧ Commute (x * w') v := by
        rcases hv with h' | h' <;> rw [h']
        · exact ⟨hcx, Commute.refl w', hcx.mul_left (Commute.refl w')⟩
        · exact ⟨(Commute.refl x).mul_right hcx, hcx.symm.mul_right (Commute.refl w'),
            Commute.refl _⟩
      rcases hQV q hq with h | h | h | h <;> rw [h]
      · exact (Commute.one_left v).eq
      · exact hcv.1.eq
      · exact hcv.2.1.eq
      · exact hcv.2.2.eq
    by_cases hw'J : w' ∈ pslRange K
    · refine ⟨x * w', fun h => hxJ ?_, ?_, ?_, fun q hq => ?_, fun h => hw'1 ?_⟩
      · have := (pslRange K).mul_mem h ((pslRange K).inv_mem hw'J)
        simpa using this
      · calc (x * w') ^ 2 = x * (w' * x) * w' := by rw [pow_two]; group
          _ = 1 := by rw [← hxw', ← mul_assoc, hxx, one_mul, hw'w']
      · exact ((Commute.refl x).mul_right hcx).eq
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm4 _ (Or.inr rfl) q hq)
      · calc w' = x⁻¹ * (x * w') := by group
          _ = 1 := by rw [h, inv_mul_cancel]
    · refine ⟨w', hw'J, by rw [pow_two]; exact hw'w', hxw', fun q hq => ?_,
        fun h => hw'U (h ▸ hxU)⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm4 _ (Or.inl rfl) q hq)
  obtain ⟨U', w'', hU'c, hU'card, huU', hw''U', hw''w'', hw''inv, hC'⟩ :=
    outer_involution_centralizer hK hcard hu2 huJ
  have hU'comm : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have huu1 : u ≠ 1 := fun h => huJ (h ▸ (pslRange K).one_mem)
  have hxC' : x ∈ U' ⊔ Subgroup.zpowers w'' := by
    rw [← hC']
    exact Subgroup.mem_centralizer_singleton_iff.mpr hux
  have hxU' : x ∉ U' := fun h =>
    hu1 (E22L2.e22pl2pgl_involution_unique hU'c huU' h hu2 hx huu1 hx1)
  have hxinv := inverts_of_mem_sup_zpowers hU'comm hw''w'' hw''inv hxC' hxU'
  obtain ⟨r, hr, hr2, hrU⟩ := E22L2.e22pl2pgl_exists_odd_prime (n := Nat.card U')
    (by rw [hU'card]; exact outerTorusOrder_mod_four hqodd)
    (by rw [hU'card]; exact six_le_outerTorusOrder hqodd h5)
  obtain ⟨γ, hγ⟩ := hU'c.exists_generator
  have hγo : orderOf γ = Nat.card U' := orderOf_eq_card_of_forall_mem_zpowers hγ
  set g : PGL2 K := (γ : PGL2 K) ^ (Nat.card U' / r) with hg
  have hgo : orderOf g = r := by
    rw [hg, ← Subgroup.coe_pow, Subgroup.orderOf_coe, ← hγo]
    exact orderOf_pow_orderOf_div (by rw [hγo]; exact Nat.card_pos.ne') (hγo ▸ hrU)
  have hgU' : g ∈ U' := U'.pow_mem γ.2 _
  have hU'eq : Subgroup.zpowers (γ : PGL2 K) = U' := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr γ.2
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨y, hy⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
        have := congrArg Subtype.val hk
        simpa using this⟩
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  refine ⟨Subgroup.zpowers g, ?_, by rw [Nat.card_zpowers, hgo]; exact hr,
    by rw [Nat.card_zpowers, hgo]; exact hr2, fun q hq => ?_, fun hle => ?_⟩
  · exact Subgroup.zpowers_le.mpr
      (mem_pslRange_of_pow_eq_one hK hcard hrodd (by rw [← hgo]; exact pow_orderOf_eq_one g))
  · have hqN : q ∈ Subgroup.normalizer ((Subgroup.zpowers (γ : PGL2 K) : Subgroup (PGL2 K)) :
        Set (PGL2 K)) := by
      rw [hU'eq]
      have hqC : q ∈ U' ⊔ Subgroup.zpowers w'' := by
        rw [← hC']
        exact huQ hq
      exact (sup_le Subgroup.le_normalizer (zpowers_le_normalizer_of_inverting hw''w'' hw''inv))
        hqC
    exact mem_normalizer_zpowers_pow hqN _
  · have hgx := Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_zpowers g))
    have h1 := hxinv g hgU'
    have hg2 : g * g = 1 := by
      have h2 : g⁻¹ = g := by
        rw [← h1]
        calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [hgx]
          _ = g := by group
      calc g * g = g * g⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel g
    have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    rw [hgo] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    have := hr.two_le
    omega

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
