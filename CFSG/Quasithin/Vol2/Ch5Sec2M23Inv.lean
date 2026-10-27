module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Setting
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_commute_mem_coset {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) {x g : G}
    (hx3 : orderOf x = 3) (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hxg : g⁻¹ * (x * g * x⁻¹) ∈ Q) : ∃ q ∈ Q, x * (g * q) * x⁻¹ = g * q := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ k : ℤ, ∀ q ∈ Q, g⁻¹ * (x ^ k * (g * q) * (x ^ k)⁻¹) ∈ Q := by
    have hxQ' : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun q hq =>
      (Subgroup.mem_normalizer_iff.mp hxQ q).mp hq
    have hxQ'' : ∀ q ∈ Q, x⁻¹ * q * x ∈ Q := fun q hq => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxQ) q).mp hq
      simpa using this
    have hstep : ∀ q ∈ Q, g⁻¹ * (x * (g * q) * x⁻¹) ∈ Q := fun q hq => by
      have e : g⁻¹ * (x * (g * q) * x⁻¹) = (g⁻¹ * (x * g * x⁻¹)) * (x * q * x⁻¹) := by group
      rw [e]
      exact Q.mul_mem hxg (hxQ' q hq)
    have hstep' : ∀ q ∈ Q, g⁻¹ * (x⁻¹ * (g * q) * x) ∈ Q := fun q hq => by
      have h1 : g⁻¹ * (x⁻¹ * g * x) ∈ Q := by
        have h2 := hxQ'' _ hxg
        have e : g⁻¹ * (x⁻¹ * g * x) = (x⁻¹ * (g⁻¹ * (x * g * x⁻¹)) * x)⁻¹ := by group
        rw [e]
        exact Q.inv_mem h2
      have e : g⁻¹ * (x⁻¹ * (g * q) * x) = (g⁻¹ * (x⁻¹ * g * x)) * (x⁻¹ * q * x) := by group
      rw [e]
      exact Q.mul_mem h1 (hxQ'' q hq)
    intro k
    induction k using Int.induction_on with
    | zero => intro q hq; simpa using hq
    | succ k ih =>
      intro q hq
      have h1 := ih q hq
      have e : g⁻¹ * (x ^ ((k : ℤ) + 1) * (g * q) * (x ^ ((k : ℤ) + 1))⁻¹) =
          g⁻¹ * (x * (g * (g⁻¹ * (x ^ (k : ℤ) * (g * q) * (x ^ (k : ℤ))⁻¹))) * x⁻¹) := by
        rw [zpow_add_one]
        group
      rw [e]
      exact hstep _ h1
    | pred k ih =>
      intro q hq
      have h1 := ih q hq
      have e : g⁻¹ * (x ^ (-(k : ℤ) - 1) * (g * q) * (x ^ (-(k : ℤ) - 1))⁻¹) =
          g⁻¹ * (x⁻¹ * (g * (g⁻¹ * (x ^ (-(k : ℤ)) * (g * q) * (x ^ (-(k : ℤ)))⁻¹))) * x) := by
        rw [zpow_sub_one]
        group
      rw [e]
      exact hstep' _ h1
  let act : Subgroup.zpowers x → Q → Q := fun c q =>
    ⟨g⁻¹ * ((c : G) * (g * q) * (c : G)⁻¹), by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.2
      rw [← hk]
      exact hmem k q q.2⟩
  let _ : MulAction (Subgroup.zpowers x) Q :=
    { smul := act
      one_smul := fun q => by
        apply Subtype.ext
        change g⁻¹ * ((1 : G) * (g * q) * (1 : G)⁻¹) = q
        group
      mul_smul := fun c d q => by
        apply Subtype.ext
        change g⁻¹ * (((c : G) * d) * (g * q) * ((c : G) * d)⁻¹) =
          g⁻¹ * ((c : G) * (g * (g⁻¹ * ((d : G) * (g * q) * (d : G)⁻¹))) * (c : G)⁻¹)
        group }
  have hP : IsPGroup 3 (Subgroup.zpowers x) := by
    have : Nat.card (Subgroup.zpowers x) = 3 ^ 1 := by rw [Nat.card_zpowers, hx3]; norm_num
    exact IsPGroup.of_card this
  have hmod := hP.card_modEq_card_fixedPoints ↥Q
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hQ2
  rw [he] at hmod
  have hne : (MulAction.fixedPoints (Subgroup.zpowers x) ↥Q).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Nat.card_coe_set_eq, Set.ncard_empty] at hmod
    have h1 : 3 ∣ 2 ^ e := (Nat.modEq_zero_iff_dvd.mp hmod)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    norm_num at this
  obtain ⟨q, hq⟩ := hne
  refine ⟨q, q.2, ?_⟩
  have h1 := congrArg Subtype.val (hq ⟨x, Subgroup.mem_zpowers x⟩)
  change g⁻¹ * (x * (g * q) * x⁻¹) = q at h1
  calc x * (g * q) * x⁻¹ = g * (g⁻¹ * (x * (g * q) * x⁻¹)) := by group
    _ = g * q := by rw [h1]

theorem exists_involution_commute_of_coset {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) {x g : G}
    (hx3 : orderOf x = 3) (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hgN : g ∈ Subgroup.normalizer (Q : Set G)) (hxg : g⁻¹ * (x * g * x⁻¹) ∈ Q) (hgQ : g ∉ Q)
    (hg2 : g * g ∈ Q) : ∃ i : G, orderOf i = 2 ∧ i * x = x * i := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq, hxq⟩ := exists_commute_mem_coset hQ2 hx3 hxQ hxg
  set y := g * q with hy
  have hyQ : y ∉ Q := fun h => hgQ (by
    have := Q.mul_mem h (Q.inv_mem hq)
    rwa [hy, mul_inv_cancel_right] at this)
  have hyy : y * y ∈ Q := by
    have hgq : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hgN q).mp hq
    have e : y * y = (g * q * g⁻¹) * (g * g) * q := by rw [hy]; group
    rw [e]
    exact Q.mul_mem (Q.mul_mem hgq hg2) hq
  have hyx : y * x = x * y := by
    calc y * x = x * y * x⁻¹ * x := by rw [hxq]
      _ = x * y := by group
  obtain ⟨k, hk⟩ := hQ2 ⟨y * y, hyy⟩
  have hk' : y ^ 2 ^ (k + 1) = 1 := by
    have h1 : (y * y) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [pow_succ', pow_mul, sq]
    exact h1
  obtain ⟨m, hm, hmy⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have hy1 : y ≠ 1 := fun h => hyQ (h ▸ Q.one_mem)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hmy
    exact hy1 hmy
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨y ^ 2 ^ m', ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul, ← pow_succ, ← hmy, pow_orderOf_eq_one]
    · apply pow_ne_one_of_lt_orderOf (by positivity)
      rw [hmy]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exact (Commute.pow_left hyx _).eq

theorem exists_involution_commute_of_mem_centralizerModO2 {L : Subgroup G} {n : ℕ}
    (hLin : IsLin2Type L n) {x : G} (hx3 : orderOf x = 3) (hxC : x ∈ centralizerModO2 L) :
    ∃ i : G, orderOf i = 2 ∧ i * x = x * i := by
  obtain ⟨hxN, hxQ, hxc⟩ := hxC
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := hLin
  have h2F : (2 : F) = 0 := by
    have h4 := FiniteField.cast_card_eq_zero F
    rw [hF] at h4
    have h4' : (2 : F) ^ n = 0 := by exact_mod_cast h4
    exact pow_eq_zero_iff (by
      rintro rfl
      rw [pow_zero] at hF
      have := Fintype.one_lt_card (α := F)
      omega) |>.mp h4'
  let A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have hA2 : A * A = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2F]
  have hA1 : A ≠ 1 := by
    intro h
    have := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) F =>
      (B : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [A] at this
  obtain ⟨g, hg⟩ := hαs A
  have hQ2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hmemQ : ∀ y : ↥L, α y = 1 → (y : G) ∈ pCoreOf 2 L := by
    intro y hy
    have h1 : y ∈ CFSG.pCore 2 ↥L := by rw [← hαk]; exact hy
    exact ⟨y, h1, rfl⟩
  have hgN : (g : G) ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)) g.2
  have hgQ : (g : G) ∉ pCoreOf 2 L := by
    intro h
    apply hA1
    rw [← hg]
    have h1 : g ∈ CFSG.pCore 2 ↥L := by
      obtain ⟨y, hy, hyg⟩ := h
      have : y = g := Subtype.ext hyg
      rwa [← this]
    rw [← hαk] at h1
    exact h1
  have hg2 : (g : G) * g ∈ pCoreOf 2 L := hmemQ (g * g) (by rw [map_mul, hg, hA2])
  have hxg : (g : G)⁻¹ * (x * g * x⁻¹) ∈ pCoreOf 2 L := by
    have h1 := hxc g g.2
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp h1
    have e : (g : G)⁻¹ * (x * g * x⁻¹) = (g : G)⁻¹ * (x * g * x⁻¹ * (g : G)⁻¹) * (g : G)⁻¹⁻¹ := by
      group
    rw [e]
    exact h2
  exact exists_involution_commute_of_coset hQ2 hx3 hxQ hgN hxg hgQ hg2


theorem cycleType_eq_three_of_card_support_lt {σ : Equiv.Perm (Fin 7)} (h3 : orderOf σ = 3)
    (hs : σ.support.card < 6) : σ.cycleType = {3} := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (h3.symm ▸ Nat.prime_three)
  rw [h3] at hn
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hn] at hsum
  simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hn0 : n = 0 := by omega
  rw [hn, hn0]
  rfl

theorem cycleType_eq_three_of_smul_eq {σ : Equiv.Perm (Fin 7)} (h3 : orderOf σ = 3)
    (hp : σ • ({5, 6} : Set (Fin 7)) = {5, 6}) : σ.cycleType = {3} := by
  have hσ3 : σ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one σ
  rw [smul_pair_set_eq_iff] at hp
  have hfix : σ 5 = 5 ∧ σ 6 = 6 := by
    rcases hp with h | ⟨h5, h6⟩
    · exact h
    · exfalso
      have e : (σ ^ 3) 5 = 6 := by
        rw [pow_succ, Equiv.Perm.mul_apply, h5, sq, Equiv.Perm.mul_apply, h6, h5]
      rw [hσ3] at e
      exact absurd e (by decide)
  refine cycleType_eq_three_of_card_support_lt h3 ?_
  have hsupp : σ.support ⊆ ((Finset.univ : Finset (Fin 7)).erase 5).erase 6 := by
    intro x hx
    rw [Equiv.Perm.mem_support] at hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hx (by rw [h]; exact hfix.2), fun h => hx (by rw [h]; exact hfix.1)⟩
  have h5 : (((Finset.univ : Finset (Fin 7)).erase 5).erase 6).card = 5 := by decide
  have := Finset.card_le_card hsupp
  omega

theorem exists_fixed_of_commute {A U : Type} [Group A] [Group U] [Finite U]
    (ρ : A →* MulAut U) (hU : Nat.card U = 16) {a b : A} (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Commute a b)
    (hfa : ∀ c ∈ Subgroup.zpowers a, c ≠ 1 → ∀ u : U, ρ c u = u → u = 1)
    (hfb : ∀ d ∈ Subgroup.zpowers b, d ≠ 1 → ∀ u : U, ρ d u = u → u = 1) :
    ∃ c ∈ Subgroup.zpowers a, ∃ d ∈ Subgroup.zpowers b, c ≠ 1 ∧ d ≠ 1 ∧
      ∃ u : U, u ≠ 1 ∧ ρ (c * d) u = u := by
  classical
  by_contra hcon
  have hcon' : ∀ c ∈ Subgroup.zpowers a, ∀ d ∈ Subgroup.zpowers b, c ≠ 1 → d ≠ 1 →
      ∀ u : U, ρ (c * d) u = u → u = 1 := by
    intro c hc d hd hc1 hd1 u hu
    by_contra hu1
    exact hcon ⟨c, hc, d, hd, hc1, hd1, u, hu1, hu⟩
  have hcomm : ∀ (c : Subgroup.zpowers a) (d : Subgroup.zpowers b),
      Commute ((Subgroup.zpowers a).subtype c) ((Subgroup.zpowers b).subtype d) := by
    rintro ⟨c, hc⟩ ⟨d, hd⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact hab.zpow_zpow i j
  let _ : MulAction (Subgroup.zpowers a × Subgroup.zpowers b) U :=
    MulAction.compHom U (ρ.comp (MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype
      (Subgroup.zpowers b).subtype hcomm))
  have hact : ∀ (c : Subgroup.zpowers a) (d : Subgroup.zpowers b) (u : U),
      (c, d) • u = ρ ((c : A) * d) u := fun c d u => rfl
  have hfin : ∀ x : A, orderOf x = 3 → Finite (Subgroup.zpowers x) := fun x hx =>
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hx]; norm_num)
  have := hfin a ha
  have := hfin b hb
  have : Fintype U := Fintype.ofFinite U
  have : Fintype (Subgroup.zpowers a × Subgroup.zpowers b) := Fintype.ofFinite _
  have : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers a × Subgroup.zpowers b) U)) :=
    Fintype.ofFinite _
  have hP : Fintype.card (Subgroup.zpowers a × Subgroup.zpowers b) = 9 := by
    rw [Fintype.card_eq_nat_card, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha, hb]
  have hfix1 : Fintype.card (MulAction.fixedBy U (1 : Subgroup.zpowers a × Subgroup.zpowers b)) =
      16 := by
    rw [Fintype.card_eq_nat_card, MulAction.fixedBy_one_eq_univ, Nat.card_univ, hU]
  have hfixne : ∀ p : Subgroup.zpowers a × Subgroup.zpowers b, p ≠ 1 →
      Fintype.card (MulAction.fixedBy U p) = 1 := by
    intro p hp
    have hsub : MulAction.fixedBy U p = {1} := by
      ext u
      rw [MulAction.mem_fixedBy, Set.mem_singleton_iff]
      obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := p
      rw [hact]
      constructor
      · intro hu
        by_cases hc1 : c = 1
        · subst hc1
          rw [one_mul] at hu
          have hd1 : d ≠ 1 := fun h => hp (by subst h; rfl)
          exact hfb d hd hd1 u hu
        · by_cases hd1 : d = 1
          · subst hd1
            rw [mul_one] at hu
            exact hfa c hc hc1 u hu
          · exact hcon' c hc d hd hc1 hd1 u hu
      · rintro rfl
        exact map_one _
    rw [Fintype.card_eq_nat_card, hsub]
    simp
  have hsum := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Subgroup.zpowers a × Subgroup.zpowers b) U
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Subgroup.zpowers a × Subgroup.zpowers b)),
    hfix1, Finset.sum_congr rfl (fun p hp => hfixne p (Finset.ne_of_mem_erase hp)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hP] at hsum
  simp only [smul_eq_mul, mul_one] at hsum
  omega

end CFSG.Quasithin.H13
