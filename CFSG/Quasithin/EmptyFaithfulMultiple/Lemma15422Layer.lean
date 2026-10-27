module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Sym
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Nine

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6 Matrix

namespace L15422

section Residual

variable {H : Type*} [Group H] [Finite H]

theorem isPGroup_two_of_forall_odd {C : Subgroup H} (h : ∀ y ∈ C, Odd (orderOf y) → y = 1) :
    IsPGroup 2 C := by
  apply IsPGroup.of_card (n := (Nat.card C).primeFactorsList.length)
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro q hq hdvd
  by_contra hne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hyodd : Odd (orderOf (y : H)) := by
    rw [Subgroup.orderOf_coe, hy]
    exact hq.odd_of_ne_two hne
  have hy1 : (y : H) = 1 := h y y.2 hyodd
  have horder : orderOf y = 1 := by
    rw [← Subgroup.orderOf_coe y, hy1, orderOf_one]
  exact hq.ne_one (hy.symm.trans horder)

omit [Finite H] in
theorem oTwoUpper_top_normal : (oTwoUpper (⊤ : Subgroup H)).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_oTwoUpper ⊤))

theorem isPGroup_quotient_of_oTwoUpper_le {K : Subgroup H} [K.Normal]
    (hK : oTwoUpper (⊤ : Subgroup H) ≤ K) : IsPGroup 2 (H ⧸ K) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup H) (Subgroup.mem_top x)
  exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hK hk⟩

theorem le_oTwoUpper_of_perfect {K : Subgroup H} (hK : ⁅K, K⁆ = K) :
    K ≤ oTwoUpper (⊤ : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (oTwoUpper (⊤ : Subgroup H)).Normal := oTwoUpper_top_normal
  set R := oTwoUpper (⊤ : Subgroup H)
  have hP : IsPGroup 2 (H ⧸ R) := isPGroup_quotient_of_oTwoUpper_le le_rfl
  have : Group.IsNilpotent (H ⧸ R) := hP.isNilpotent
  set K' := K.map (QuotientGroup.mk' R)
  have hK' : ⁅K', K'⁆ = K' := by rw [← Subgroup.map_commutator, hK]
  by_contra hle
  have hne : K' ≠ ⊥ := by
    intro hb
    apply hle
    rw [← QuotientGroup.ker_mk' R, ← Subgroup.map_eq_bot_iff]
    exact hb
  exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hK'

end Residual

theorem exists_alternatingGroup
    {H : Type} [Group H] [Finite H] {N : Subgroup H} [hN : N.Normal]
    (hQN : IsSylowIn 2 (Open.pCore 2 H) N) (hN3 : Nat.Coprime (Nat.card N) 3)
    (hO : ∀ B : Subgroup H, B.Normal → Odd (Nat.card B) → B = ⊥)
    (hnc : ¬ Subgroup.centralizer (Open.pCore 2 H : Set H) ≤ Open.pCore 2 H)
    (hQD : Open.pCore 2 (H ⧸ N) = ⊥) {T₀ : Subgroup H} (hT₀ : IsPGroup 2 T₀)
    (hT₀i : ¬ 2 ∣ T₀.index) {u : H} (huT : u ∈ T₀) (huc : ∀ t ∈ T₀, t * u = u * t)
    (hu2 : u ^ 2 = 1) (hu1 : QuotientGroup.mk' N u ≠ 1)
    (huO : QuotientGroup.mk' N u ∈ oTwoUpper (⊤ : Subgroup (H ⧸ N)))
    (huC : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer ({u} : Set H)))
    (h3 : oTwoUpper (⊤ : Subgroup H) ≤ Subgroup.closure {y : H | y ^ 3 = 1})
    (hD : IsCaseEight15422 (H ⧸ N)) :
    ∃ K : Subgroup H, K = oTwoUpper ⊤ ∧ K ⊔ T₀ = ⊤ ∧ Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
      ∃ φ : H →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
        φ.ker = Subgroup.centralizer (K : Set H) ∧ φ.ker ≤ T₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  rcases hD with hS | ⟨p, hp, hp2, hL⟩
  · exact (false_of_isHatSym hQN hO hnc hS).elim
  by_cases hp3 : p ≠ 3
  · exact (false_of_isL2FieldExt hQN hO hnc hQD hu2 hu1 huO huC hp2 hp3 hL).elim
  push Not at hp3
  subst hp3
  obtain ⟨Θ⟩ := nonempty_mulEquiv_perm_six hQD hL
  obtain ⟨-, F, hF, hFin, hcardF, N₀, hidx, ⟨e⟩⟩ := exists_psl_of_isL2FieldExt hL
  have hF9 : Fintype.card F = 9 := by rw [hcardF]; norm_num
  have hcard4 : 4 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hF9]; norm_num
  have hsimp : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4
  have hN₀s : IsSimpleGroup N₀ := e.isSimpleGroup
  have hDcard : Nat.card (H ⧸ N) = 720 := by
    rw [Nat.card_congr Θ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hN₀card : Nat.card N₀ = 360 := by
    have h := N₀.index_mul_card
    rw [hidx, hDcard] at h
    omega
  have hN₀nab : ∃ a b : N₀, a * b ≠ b * a :=
    exists_mul_ne_of_simple (by rw [hN₀card]; norm_num) (by rw [hN₀card]; norm_num)
  obtain ⟨K, hKn, hKmap, hKN, hKC, hKp, hNK⟩ := exists_layer hQN hO hnc hQD hidx hN₀s hN₀nab
  have huN₀ : π u ∈ N₀ := oTwoUpper_le_of_index_eq_two hidx huO
  have hKN1 : K ⊓ N = ⊥ :=
    inf_eq_bot_of_psl_nine hQN hKn hKmap hKN hKC hKp hNK hF9 e hT₀ hT₀i huT huc hu2 huN₀ hu1
  have hΘN₀ : N₀.map Θ.toMonoidHom = alternatingGroup (Fin 6) := by
    refine Equiv.Perm.eq_alternatingGroup_of_index_eq_two ?_
    have h := (N₀.map Θ.toMonoidHom).card_mul_index
    rw [Subgroup.card_map_of_injective Θ.injective, hN₀card, Nat.card_perm, Nat.card_fin] at h
    have h720 : Nat.factorial 6 = 360 * 2 := by decide
    rw [h720] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hmemA : ∀ k ∈ K, Θ (π k) ∈ alternatingGroup (Fin 6) := fun k hk => by
    rw [← hΘN₀]
    exact ⟨π k, hKmap ▸ Subgroup.mem_map_of_mem π hk, rfl⟩
  let ψ : K →* alternatingGroup (Fin 6) :=
    (Θ.toMonoidHom.comp (π.comp K.subtype)).codRestrict _ fun k => hmemA k k.2
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have h1 : Θ (π k) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    have h2 : π k = 1 := Θ.injective (h1.trans Θ.map_one.symm)
    have h4 : (k : H) ∈ K ⊓ N := ⟨k.2, (QuotientGroup.eq_one_iff _).mp h2⟩
    rw [hKN1, Subgroup.mem_bot] at h4
    exact Subgroup.mem_bot.mpr (Subtype.ext h4)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨σ, hσ⟩
    rw [← hΘN₀] at hσ
    obtain ⟨n, hn, rfl⟩ := hσ
    rw [← hKmap] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    exact ⟨⟨k, hk⟩, rfl⟩
  set φ : H →* Equiv.Perm (Fin 6) := Θ.toMonoidHom.comp π with hφ
  have hφsurj : Function.Surjective φ := Θ.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : ∀ x : H, x ∈ φ.ker ↔ x ∈ N := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h2 : π x = 1 := Θ.injective (h.trans Θ.map_one.symm)
      exact (QuotientGroup.eq_one_iff x).mp h2
    · intro h
      have h2 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr h
      change Θ (π x) = 1
      rw [h2, map_one]
  have hN3' : ∀ n ∈ N, n ^ 3 = 1 → n = 1 := by
    intro n hn hn3
    have h1 : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one hn3
    have h2 : orderOf n ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hN3 h2 h1)
  have hcube : ∀ y : H, y ^ 3 = 1 → y ∈ K := by
    intro y hy3
    have hyN₀ : π y ∈ N₀ := by
      refine oTwoUpper_le_of_index_eq_two hidx (mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_)
      have : orderOf (π y) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy3, map_one])
      exact Odd.of_dvd_nat (by decide) this
    rw [← hKmap] at hyN₀
    obtain ⟨k, hk, hky⟩ := hyN₀
    obtain ⟨n, hn⟩ : ∃ n, n = k⁻¹ * y := ⟨_, rfl⟩
    have hnN : n ∈ N := by
      have : π n = 1 := by rw [hn, map_mul, map_inv, hky, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff n).mp this
    have hkn : k * n = n * k := (Subgroup.mem_centralizer_iff.mp (hNK hnN)) k hk
    have hy : y = k * n := by rw [hn]; group
    have hn3K : n ^ 3 ∈ K := by
      have h1 : (k * n) ^ 3 = k ^ 3 * n ^ 3 := Commute.mul_pow hkn 3
      rw [← hy, hy3] at h1
      have h2 : n ^ 3 = (k ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
      rw [h2]
      exact K.inv_mem (K.pow_mem hk 3)
    have hn3 : n ^ 3 = 1 := by
      have h4 : n ^ 3 ∈ K ⊓ N := ⟨hn3K, N.pow_mem hnN 3⟩
      rw [hKN1] at h4
      exact Subgroup.mem_bot.mp h4
    rw [hy, hN3' n hnN hn3, mul_one]
    exact hk
  have hOK : oTwoUpper (⊤ : Subgroup H) ≤ K :=
    h3.trans ((Subgroup.closure_le K).mpr fun y hy => hcube y hy)
  have hN2 : IsPGroup 2 N := isPGroup_two_of_forall_odd fun n hn hno => by
    have h2 : n ∈ K ⊓ N := ⟨hOK (mem_oTwoUpper_of_odd (Subgroup.mem_top n) hno), hn⟩
    rw [hKN1] at h2
    exact Subgroup.mem_bot.mp h2
  have hNT : N ≤ T₀ := by
    have := hN2.le_sylow_of_normal (hT₀.toSylow hT₀i)
    simpa using this
  have hsup : K ⊔ T₀ = ⊤ := by
    have hP : IsPGroup 2 (H ⧸ K) := isPGroup_quotient_of_oTwoUpper_le hOK
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
    have h1 : (K ⊔ T₀).index ∣ 2 ^ m := by
      rw [← hm, ← Subgroup.index_eq_card]
      exact Subgroup.index_dvd_of_le le_sup_left
    have h2 : (K ⊔ T₀).index ∣ T₀.index := Subgroup.index_dvd_of_le le_sup_right
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hb0 : b = 0 := by
      by_contra hb0
      exact hT₀i ((hb ▸ dvd_pow_self 2 hb0).trans h2)
    rw [hb0, pow_zero] at hb
    exact Subgroup.index_eq_one.mp hb
  have hkerC : φ.ker = Subgroup.centralizer (K : Set H) := by
    apply le_antisymm
    · intro x hx
      exact hNK ((hker x).mp hx)
    · intro x hx
      have hc : ∀ τ ∈ alternatingGroup (Fin 6), Θ (π x) * τ = τ * Θ (π x) := by
        intro τ hτ
        rw [← hΘN₀] at hτ
        obtain ⟨n, hn, rfl⟩ := hτ
        rw [← hKmap] at hn
        obtain ⟨k, hk, rfl⟩ := hn
        have hkx : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hx) k hk
        change Θ (π x) * Θ (π k) = Θ (π k) * Θ (π x)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hkx]
      have h1 := perm_six_eq_one_of_forall_commute hc
      have h2 : π x = 1 := Θ.injective (h1.trans Θ.map_one.symm)
      exact (hker x).mpr ((QuotientGroup.eq_one_iff x).mp h2)
  exact ⟨K, le_antisymm (le_oTwoUpper_of_perfect hKp) hOK, hsup,
    ⟨MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩⟩, φ, hφsurj, hkerC,
    fun x hx => hNT ((hker x).mp hx)⟩

end L15422

end CFSG.Quasithin.EmptyFaithfulMultiple
