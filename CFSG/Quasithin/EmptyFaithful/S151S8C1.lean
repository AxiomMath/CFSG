module

public import CFSG.Quasithin.EmptyFaithful.S151WF
public import CFSG.Quasithin.EmptyFaithful.S151S8B
public import CFSG.Quasithin.EmptyFaithful.S151S6B

public section

namespace CFSG.Quasithin.S151S8C

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_evenWeight_three : Nat.card (Multiplicative ↥(evenWeight 3)) = 4 := by
  have h : Nat.card ↥(evenWeight 3) = Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} := rfl
  rw [Nat.card_congr Multiplicative.toAdd, h, Nat.card_eq_fintype_card]
  decide

theorem inf_pCoreOf_le [Finite G] {M J : Subgroup G} (hJM : J ≤ M) :
    J ⊓ pCoreOf 2 M ≤ pCoreOf 2 J :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _j hj => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hJM hj)⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)

omit [Group G] in
theorem eq_one_of_commutator_cube {G : Type} [Group G] {x q d : G} (hx3 : x ^ 3 = 1)
    (hd2 : d ^ 2 = 1) (hxd : x * d = d * x) (hq : q * x * q⁻¹ * x⁻¹ = d) : d = 1 := by
  have h1 : q * x * q⁻¹ = d * x := by rw [← hq]; group
  have h2 : (q * x * q⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  rw [h1, Commute.mul_pow (show Commute d x from hxd.symm), hx3, mul_one] at h2
  calc d = d ^ 2 * d := by rw [hd2, one_mul]
    _ = d ^ 3 := by group
    _ = 1 := h2

omit [Group G] in
theorem comm_of_sq_eq_one {G : Type} [Group G] {U : Subgroup G} (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    {u v : G} (hu : u ∈ U) (hv : v ∈ U) : u * v = v * u := by
  have hu' : u * u = 1 := by simpa [pow_two] using hU2 u hu
  have hv' : v * v = 1 := by simpa [pow_two] using hU2 v hv
  have huv : u * v * (u * v) = 1 := by simpa [pow_two] using hU2 _ (U.mul_mem hu hv)
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu'
  have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv'
  have h : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huv
  rw [← h, mul_inv_rev, hu_inv, hv_inv]

omit [Group G] in
theorem exists_commutator_of_mem {G : Type} [Group G] {R U : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hcU : ∀ q ∈ R, ∀ u ∈ U, q * u = u * q)
    (hRU : ∀ r ∈ R, ⁅r, x⁆ ∈ U) (hU2 : ∀ u ∈ U, u ^ 2 = 1) {d : G}
    (hd : d ∈ ⁅R, Subgroup.zpowers x⁆) : ∃ q ∈ R, ⁅q, x⁆ = d := by
  have hmul : ∀ q₁ ∈ R, ∀ q₂ ∈ R, ⁅q₁ * q₂, x⁆ = ⁅q₁, x⁆ * ⁅q₂, x⁆ := by
    intro q₁ hq₁ q₂ hq₂
    have h1 : ⁅q₁ * q₂, x⁆ = (q₁ * ⁅q₂, x⁆ * q₁⁻¹) * ⁅q₁, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have h2 : q₁ * ⁅q₂, x⁆ * q₁⁻¹ = ⁅q₂, x⁆ := by
      rw [hcU q₁ hq₁ _ (hRU q₂ hq₂)]; group
    rw [h2]
    exact comm_of_sq_eq_one hU2 (hRU q₂ hq₂) (hRU q₁ hq₁)
  have hone : ⁅(1 : G), x⁆ = 1 := by simp [commutatorElement_def]
  have hinv : ∀ q ∈ R, ⁅q⁻¹, x⁆ = ⁅q, x⁆⁻¹ := by
    intro q hq
    have h := hmul q hq q⁻¹ (R.inv_mem hq)
    rw [mul_inv_cancel, hone] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  rw [Subgroup.commutator_def] at hd
  induction hd using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r, hr, g₂, hg₂, rfl⟩ := hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
    have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    rw [zpow_eq_zpow_emod j hx3']
    have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj with h | h | h <;> rw [h]
    · exact ⟨1, R.one_mem, by simp [commutatorElement_def]⟩
    · exact ⟨r, hr, by simp⟩
    · refine ⟨r * (x * r * x⁻¹), R.mul_mem hr (hxR r hr), ?_⟩
      rw [hmul r hr _ (hxR r hr)]
      have hx2 : x ^ (2 : ℤ) = x * x := by rw [zpow_two]
      rw [hx2]
      simp only [commutatorElement_def]
      group
  | one => exact ⟨1, R.one_mem, hone⟩
  | mul a b _ _ ha hb =>
    obtain ⟨q₁, hq₁, rfl⟩ := ha
    obtain ⟨q₂, hq₂, rfl⟩ := hb
    exact ⟨q₁ * q₂, R.mul_mem hq₁ hq₂, hmul q₁ hq₁ q₂ hq₂⟩
  | inv a _ ha =>
    obtain ⟨q, hq, rfl⟩ := ha
    exact ⟨q⁻¹, R.inv_mem hq, hinv q hq⟩

theorem false_of_involution_quotient [Finite G] {Q K : Subgroup G} (hKQ : K ≤ Q)
    (h3 : ∀ x ∈ Q, ∃ k : ℕ, x ^ 3 ^ k ∈ pCoreOf 2 Q) {X : Type} [Group X]
    (α : ↥K →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K)
    (t : X) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) : False := by
  obtain ⟨k₀, hk₀⟩ := hα t
  obtain ⟨m, hm⟩ := h3 (k₀ : G) (hKQ k₀.2)
  have hmemP : (k₀ : G) ^ 3 ^ m ∈ pCoreOf 2 K := inf_pCoreOf_le hKQ ⟨K.pow_mem k₀.2 _, hm⟩
  have hker' : k₀ ^ 3 ^ m ∈ α.ker := by
    rw [hker, ← pCoreOf_subgroupOf K, Subgroup.mem_subgroupOf]
    exact hmemP
  have h1 : t ^ 3 ^ m = 1 := by
    have := MonoidHom.mem_ker.mp hker'
    rwa [map_pow, hk₀] at this
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdvd : 2 ∣ 3 ^ m := hord ▸ orderOf_dvd_of_pow_eq_one h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  omega

theorem not_lin2_of_three_group [Finite G] {Q K : Subgroup G} (hKQ : K ≤ Q)
    (h3 : ∀ x ∈ Q, ∃ k : ℕ, x ^ 3 ^ k ∈ pCoreOf 2 Q) {n : ℕ} (hn : 1 < n)
    (h : IsLin2Type K n) : False := by
  obtain ⟨F, hF, hFin, hcard, α, hα, hker, -⟩ := h
  have h2 : (2 : F) = 0 := by
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [hcard] at h0
    have h0' : (2 : F) ^ n = 0 := by exact_mod_cast h0
    exact (pow_eq_zero_iff (by omega)).mp h0'
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [t] at this
  have ht2 : t ^ 2 = 1 := by
    have key : ((t ^ 2 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_pow]
      have ht : (t : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
      rw [ht, pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
    exact Subtype.ext key
  exact false_of_involution_quotient hKQ h3 α hα hker t ht1 ht2

theorem not_alt5_of_three_group [Finite G] {Q K : Subgroup G} (hKQ : K ≤ Q)
    (h3 : ∀ x ∈ Q, ∃ k : ℕ, x ^ 3 ^ k ∈ pCoreOf 2 Q) (h : IsAltType K 5) : False := by
  obtain ⟨α, hα, hker, -⟩ := h
  have hmem : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  let t : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, hmem⟩
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun a : alternatingGroup (Fin 5) => (a : Equiv.Perm (Fin 5)) 0) h
    simp [t] at this
    exact absurd this (by decide)
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    show (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ^ 2 = 1
    decide
  exact false_of_involution_quotient hKQ h3 α hα hker t ht1 ht2

end CFSG.Quasithin.S151S8C

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def NumC126 (H : Subgroup G) : Prop :=
  (∀ x ∈ twoResidual H, ∃ k : ℕ, x ^ 3 ^ k ∈ pCoreOf 2 (twoResidual H)) ∧
    ∀ x ∈ twoResidual H, orderOf x = 3 →
      4 < Nat.card ↥⁅pCoreOf 2 (twoResidual H), Subgroup.zpowers x⁆

theorem not_c126Third_of_num [Finite G] {H T : Subgroup G} (hN : NumC126 H) :
    ¬ C126Third H T := by
  rintro ⟨r, K, hr, hK, hcomm, hQ, -, -⟩
  obtain ⟨i0⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨⟨hshort, -, -⟩, htype⟩ := (hK i0).1
  set Q := twoResidual H with hQdef
  set K₀ := K i0 with hK₀def
  have hKQ : K₀ ≤ Q := by rw [hQ]; exact le_iSup K i0
  have hCT : CharTwo K₀ := hshort.2.1
  have hU : blockU K₀ ≤ blockQ K₀ ⊓ Subgroup.centralizer (blockQ K₀ : Set G) ∧
      ∀ u ∈ blockU K₀, u ^ 2 = 1 := hshort.2.2.1
  have hA3 : IsAltType K₀ 3 := by
    rcases htype with ⟨n, hn, hlin⟩ | h3 | h5
    · exact (S151S8C.not_lin2_of_three_group hKQ hN.1 hn hlin).elim
    · exact h3
    · exact (S151S8C.not_alt5_of_three_group hKQ hN.1 h5).elim
  obtain ⟨α, hα, hαker, β, hβ, hβker, -⟩ := hA3
  have hcard3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h3dvd : 3 ∣ Nat.card ↥K₀ := by
    have := Subgroup.card_dvd_of_surjective hα
    rwa [hcard3] at this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hxK₀ : (x' : G) ∈ K₀ := x'.2
  have hx3ord : orderOf (x' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx'
  have hx3 : (x' : G) ^ 3 = 1 := by rw [← hx3ord]; exact pow_orderOf_eq_one _
  have hxQ : (x' : G) ∈ Q := hKQ hxK₀
  set K' : Subgroup G := ⨆ i, ⨆ (_ : i ≠ i0), K i with hK'def
  have hQsup : Q = K₀ ⊔ K' := by rw [hQ]; exact iSup_split_single K i0
  have hcomm' : ∀ a ∈ K₀, ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    have hle : K' ≤ Subgroup.centralizer ({a} : Set G) := by
      refine iSup_le fun i => iSup_le fun hi => fun b hb => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hle0 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i0 i (Ne.symm hi))
      exact (Subgroup.mem_centralizer_iff.mp (hle0 ha) b hb).symm
    exact Subgroup.mem_centralizer_iff.mp (hle hb) a rfl
  have hRQ : pCoreOf 2 Q ≤ Q := CFSG.LieType.BorelTits.pCoreOf_le 2 Q
  have hnormQ : Q ≤ Subgroup.normalizer (pCoreOf 2 Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Q
  have hxR : ∀ r ∈ pCoreOf 2 Q, (x' : G) * r * (x' : G)⁻¹ ∈ pCoreOf 2 Q := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hnormQ hxQ) r).mp hr
  have hdecomp : ∀ r ∈ pCoreOf 2 Q, ∃ k₀ ∈ pCoreOf 2 K₀, ∃ k' ∈ K', r = k₀ * k' := by
    intro r hr
    obtain ⟨k₀, hk₀, k', hk', hrk⟩ := S151S8.mem_sup_comm hcomm' (hQsup ▸ hRQ hr)
    subst hrk
    refine ⟨k₀, ?_, k', hk', rfl⟩
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Q) ⟨k₀ * k', hr⟩
    have hm' : (k₀ * k') ^ 2 ^ m = 1 := congrArg Subtype.val hm
    rw [Commute.mul_pow (hcomm' k₀ hk₀ k' hk')] at hm'
    have hc : k₀ ^ 2 ^ m = (k' ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm'
    have hcK' : k₀ ^ 2 ^ m ∈ K' := by rw [hc]; exact K'.inv_mem (K'.pow_mem hk' _)
    have hcP : k₀ ^ 2 ^ m ∈ pCoreOf 2 K₀ := by
      refine hCT ⟨K₀.pow_mem hk₀ _, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
      exact hcomm' p (CFSG.LieType.BorelTits.pCoreOf_le 2 K₀ hp) _ hcK'
    have h1 : α ⟨k₀, hk₀⟩ ^ 2 ^ m = 1 := by
      have : (⟨k₀, hk₀⟩ : ↥K₀) ^ 2 ^ m ∈ α.ker := by
        rw [hαker, ← pCoreOf_subgroupOf K₀, Subgroup.mem_subgroupOf]
        exact hcP
      rw [← map_pow]
      exact MonoidHom.mem_ker.mp this
    have h2 : α ⟨k₀, hk₀⟩ ^ 3 = 1 := by
      have := pow_card_eq_one' (G := alternatingGroup (Fin 3)) (x := α ⟨k₀, hk₀⟩)
      rwa [hcard3] at this
    have h3 : α ⟨k₀, hk₀⟩ = 1 :=
      (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right m (by norm_num))).mp ⟨h2, h1⟩
    have h4 : (⟨k₀, hk₀⟩ : ↥K₀) ∈ α.ker := h3
    rw [hαker, ← pCoreOf_subgroupOf K₀, Subgroup.mem_subgroupOf] at h4
    exact h4
  have hUK₀ : blockU K₀ ≤ K₀ := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have ha' : a ∈ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀ ha
    show a * b * a⁻¹ * b⁻¹ ∈ K₀
    exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem ha' hb) (K₀.inv_mem ha')) (K₀.inv_mem hb)
  have hRU' : ∀ r ∈ pCoreOf 2 Q, ∀ y ∈ K₀, ⁅r, y⁆ ∈ blockU K₀ := by
    intro r hr y hy
    obtain ⟨k₀, hk₀, k', hk', rfl⟩ := hdecomp r hr
    have hk'y : k' * y = y * k' := (hcomm' y hy k' hk').symm
    have h1 : k' * y * k'⁻¹ = y := by rw [hk'y]; group
    have h2 : ⁅k₀ * k', y⁆ = ⁅k₀, y⁆ := by
      simp only [commutatorElement_def]
      calc k₀ * k' * y * (k₀ * k')⁻¹ * y⁻¹ = k₀ * (k' * y * k'⁻¹) * k₀⁻¹ * y⁻¹ := by group
        _ = k₀ * y * k₀⁻¹ * y⁻¹ := by rw [h1]
    rw [h2]
    exact Subgroup.commutator_mem_commutator hk₀ hy
  have hcU : ∀ q ∈ pCoreOf 2 Q, ∀ u ∈ blockU K₀, q * u = u * q := by
    intro q hq u hu
    obtain ⟨k₀, hk₀, k', hk', rfl⟩ := hdecomp q hq
    have h1 : k₀ * u = u * k₀ := Subgroup.mem_centralizer_iff.mp (hU.1 hu).2 k₀ hk₀
    have h2 : k' * u = u * k' := (hcomm' u (hUK₀ hu) k' hk').symm
    calc k₀ * k' * u = k₀ * (k' * u) := by rw [mul_assoc]
      _ = k₀ * (u * k') := by rw [h2]
      _ = (k₀ * u) * k' := by rw [← mul_assoc]
      _ = u * k₀ * k' := by rw [h1]
      _ = u * (k₀ * k') := by rw [mul_assoc]
  have hRU : ∀ r ∈ pCoreOf 2 Q, ⁅r, (x' : G)⁆ ∈ blockU K₀ := fun r hr => hRU' r hr _ hxK₀
  have hDU : ⁅pCoreOf 2 Q, Subgroup.zpowers (x' : G)⁆ ≤ blockU K₀ := by
    refine Subgroup.commutator_le.mpr fun r hr g hg => hRU' r hr g ?_
    exact (Subgroup.zpowers_le.mpr hxK₀) hg
  let βD : ↥⁅pCoreOf 2 Q, Subgroup.zpowers (x' : G)⁆ →* Multiplicative ↥(evenWeight 3) :=
    β.comp (Subgroup.inclusion hDU)
  have hinj : Function.Injective βD := by
    refine (injective_iff_map_eq_one βD).mpr fun d hd => ?_
    have h1 : Subgroup.inclusion hDU d ∈ β.ker := MonoidHom.mem_ker.mpr hd
    rw [hβker, Subgroup.mem_subgroupOf] at h1
    have h2 : (d : G) ∈ Subgroup.centralizer (K₀ : Set G) := h1.2
    have h3 : (x' : G) * (d : G) = (d : G) * (x' : G) :=
      Subgroup.mem_centralizer_iff.mp h2 _ hxK₀
    obtain ⟨q, hqR, hq⟩ := S151S8C.exists_commutator_of_mem hx3 hxR hcU hRU hU.2 d.2
    simp only [commutatorElement_def] at hq
    have hd2 : (d : G) ^ 2 = 1 := hU.2 (d : G) (hDU d.2)
    exact Subtype.ext (S151S8C.eq_one_of_commutator_cube hx3 hd2 h3 hq)
  have hcard : Nat.card ↥⁅pCoreOf 2 Q, Subgroup.zpowers (x' : G)⁆ ≤ 4 := by
    have := Nat.card_le_card_of_injective βD hinj
    rwa [S151S8C.card_evenWeight_three] at this
  exact absurd (hN.2 _ hxQ hx3ord) (not_lt.mpr hcard)

@[expose] def Input15122ThreeDLocN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L) →
    CFSG.Open.IsQuasisimple ↥L → IsPGroup 2 ↥(Subgroup.center ↥L) → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
    ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) →
      ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
        ¬ P ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧ CharTwo P ∧
        IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
        oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P

theorem input15122ThreeDLoc_of_num (h : Input15122ThreeDLocN) : Input15122ThreeDLoc := by
  intro G _ _ L S h1 h2 h3 h4 h5 h6 h7
  obtain ⟨P, hPL, hSP, hSN, hnc, hchar, hmin, hnum, hoP⟩ := h G L S h1 h2 h3 h4 h5 h6 h7
  exact ⟨P, hPL, hSP, hSN, hnc, hchar, hmin, not_c126Third_of_num hnum, hoP⟩

end CFSG.Quasithin
