module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiSingerU

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_w (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) {ℓ : K}
    (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ w ∈ slPi π 3 (p ^ f) K,
      (w : Matrix (Fin 3) (Fin 3) K) * y = τ • ((y : Matrix (Fin 3) (Fin 3) K) * w) := by
  cases π
  · exact exists_w_unitary hK hq hτ hτ1 hyH hℓ hy
  · obtain ⟨w, hwdet, -, hwy⟩ := exists_w_linear hτ hτ1 hℓ hy
    exact ⟨w, (mem_slPi_true _).mpr hwdet, hwy⟩

theorem card_centralizer_glPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    Nat.card ↥(glPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) = qSubPi π ((p ^ f) ^ 3) := by
  cases π
  · exact card_centralizer_glPi_false hK hq hyH hℓ hy
  · have := hK.finite
    rw [show glPi true 3 (p ^ f) K = ⊤ from rfl, top_inf_eq, (centralizer_cyclic_card hℓ hy).2,
      hK.card]
    rfl

theorem centralizer_slPi_cyclic (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    IsCyclic ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ∧
      Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) =
        qSubPi π ((p ^ f) ^ 3) / qSubPi π (p ^ f) := by
  have := hK.finite
  refine ⟨?_, ?_⟩
  · have hcyc := (centralizer_cyclic_card hℓ hy).1
    have hle : slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} ≤ Subgroup.centralizer {y} :=
      inf_le_right
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  · rw [← card_centralizer_glPi hK hq hyH hℓ hy, ← card_centralizer_slPi_mul hK hq hyH hℓ hy,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (qSubPi_ne_zero hK hq))]

theorem exists_pow_three_eq {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]
    (h3 : 3 ∣ Nat.card G) {t : G} (ht : t ^ (Nat.card G / 3) = 1) : ∃ s : G, s ^ 3 = t := by
  by_contra hne
  push Not at hne
  have hR := eq_top_of_cube_le (R := (powMonoidHom (Nat.card G / 3) : G →* G).ker)
    (fun g => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul, Nat.mul_div_cancel' h3,
        pow_card_eq_one'])
    (g₀ := t) (by rwa [MonoidHom.mem_ker, powMonoidHom_apply]) hne
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  have hγR : γ ∈ (powMonoidHom (Nat.card G / 3) : G →* G).ker := hR ▸ Subgroup.mem_top γ
  rw [MonoidHom.mem_ker, powMonoidHom_apply] at hγR
  have hord : orderOf γ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hγ
  have hdvd := orderOf_dvd_of_pow_eq_one hγR
  rw [hord] at hdvd
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h1 : Nat.card G / 3 < Nat.card G := Nat.div_lt_self hpos (by norm_num)
  have h2 : 0 < Nat.card G / 3 := Nat.div_pos (Nat.le_of_dvd hpos h3) (by norm_num)
  exact absurd (Nat.le_of_dvd h2 hdvd) (by omega)

theorem three_dvd_qSubPi {q : ℕ} (hq : ModThree π q) : 3 ∣ qSubPi π q := by
  cases π
  · change q % 3 = 2 at hq
    change 3 ∣ q + 1
    omega
  · change q % 3 = 1 at hq
    change 3 ∣ q - 1
    omega

theorem qSubPi_cube_eq {q : ℕ} (hq : ModThree π q) :
    qSubPi π (q ^ 3) = qSubPi π q * (3 * (3 * (q / 3) ^ 2 + 3 * (q / 3) + 1)) := by
  cases π
  · change q % 3 = 2 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
    have ht : (3 * t + 2) / 3 = t := by omega
    change (3 * t + 2) ^ 3 + 1 = (3 * t + 2 + 1) * _
    rw [ht]
    ring
  · change q % 3 = 1 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
    have ht : (3 * t + 1) / 3 = t := by omega
    change (3 * t + 1) ^ 3 - 1 = (3 * t + 1 - 1) * _
    rw [ht, show 3 * t + 1 - 1 = 3 * t by omega]
    apply Nat.sub_eq_of_eq_add
    ring

theorem ordProj_qSubPi_cube {q : ℕ} (hq : ModThree π q) (h0 : qSubPi π q ≠ 0) :
    ordProj[3] (qSubPi π (q ^ 3)) = 3 * ordProj[3] (qSubPi π q) := by
  rw [qSubPi_cube_eq hq]
  set A := (q / 3) ^ 2
  set B := q / 3
  have hr : ¬ 3 ∣ 3 * A + 3 * B + 1 := by omega
  have hr0 : 3 * A + 3 * B + 1 ≠ 0 := by omega
  rw [Nat.factorization_mul h0 (by omega), Finsupp.add_apply,
    Nat.factorization_mul (by norm_num) hr0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd hr,
    add_zero, pow_add, pow_one, mul_comm]

theorem scalar_injective_three :
    Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
  intro a b h
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at this
  exact Units.ext this

theorem irreducible_case (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K) {c : Kˣ}
    (hx3 : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) c) (hc : ∀ μ : K, μ ^ 3 ≠ c) :
    ∃ y : GL (Fin 3) K, (∃ z ∈ zPi π 3 (p ^ f) K, y = x * z) ∧
      orderOf y = ordProj[3] (qSubPi π ((p ^ f) ^ 3)) ∧
      (∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      IsCyclic ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ∧
      Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) =
        qSubPi π ((p ^ f) ^ 3) / qSubPi π (p ^ f) ∧
      ∃ w ∈ slPi π 3 (p ^ f) K, orderOf w = 3 ∧
        w ∉ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} ∧
        centMod (slPi π 3 (p ^ f) K) y =
          (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ⊔ Subgroup.zpowers w ∧
        Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K))) =
          3 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  have hxm : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hn : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  have hm3 : Nat.Coprime 3 (ordCompl[3] (orderOf x)) := Nat.coprime_ordCompl Nat.prime_three hn
  have hmn := Nat.ordProj_mul_ordCompl_eq_self (orderOf x) 3
  set m := ordCompl[3] (orderOf x) with hmdef
  set e := (orderOf x).factorization 3 with hedef
  obtain ⟨k, hk⟩ : ∃ k, m ^ 2 = 3 * k + 1 := by
    have h3m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hm3
    have hm2 : m ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h | h <;> rw [h]
    exact ⟨m ^ 2 / 3, by omega⟩
  set z := (x ^ 3) ^ k with hzdef
  set y := x * z with hydef
  have hyx : y = x ^ (3 * k + 1) := by rw [hydef, hzdef, ← pow_mul, ← pow_succ']
  have hzZ : z ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    refine pow_mem (Subgroup.mem_inf.mpr ⟨pow_mem hxH 3, ?_⟩) k
    rw [hx3]
    exact ⟨c, rfl⟩
  have hyH : y ∈ glPi π 3 (p ^ f) K :=
    mul_mem hxH ((Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hzZ)).1)
  set ℓ := ((c ^ (3 * k + 1) : Kˣ) : K) with hℓdef
  have hy3 : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) (c ^ (3 * k + 1)) := by
    rw [hyx, ← pow_mul, mul_comm, pow_mul, hx3, ← map_pow]
  have hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1 := by
    rw [← Units.val_pow_eq_pow_val, hy3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ := by
    intro μ hμ
    apply hc (μ / (c : K) ^ k)
    have hc0 : ((c : K) ^ k) ^ 3 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ c.ne_zero)
    rw [div_pow, hμ, hℓdef, Units.val_pow_eq_pow_val, div_eq_iff hc0]
    ring
  have hy3e : y ^ 3 ^ e = 1 := by
    rw [hyx, ← pow_mul, ← hk]
    calc x ^ (m ^ 2 * 3 ^ e) = (x ^ (3 ^ e * m)) ^ m := by rw [← pow_mul]; ring_nf
      _ = 1 := by rw [hmn, pow_orderOf_eq_one, one_pow]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3e)
  have hyC : y ∈ glPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} :=
    Subgroup.mem_inf.mpr ⟨hyH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hdvdC : orderOf y ∣ qSubPi π ((p ^ f) ^ 3) := by
    rw [← card_centralizer_glPi hK hq hyH hℓ hy]
    have := orderOf_dvd_natCard (⟨y, hyC⟩ : ↥(glPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}))
    rwa [Subgroup.orderOf_mk] at this
  set N := qSubPi π (p ^ f) with hNdef
  have hN0 : N ≠ 0 := qSubPi_ne_zero hK hq
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  have hN30 : qSubPi π ((p ^ f) ^ 3) ≠ 0 := by
    rw [qSubPi_cube_eq hq]
    exact mul_ne_zero hN0 (by positivity)
  set v := N.factorization 3 with hvdef
  have hv1 : 1 ≤ v :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hN0).mp
      (by rw [pow_one]; exact three_dvd_qSubPi hq)
  have hproj : ordProj[3] (qSubPi π ((p ^ f) ^ 3)) = 3 ^ (v + 1) := by
    rw [ordProj_qSubPi_cube hq hN0, pow_succ, mul_comm]
  have hfac : (qSubPi π ((p ^ f) ^ 3)).factorization 3 = v + 1 :=
    Nat.pow_right_injective (a := 3) (by norm_num) hproj
  have hjle : j ≤ v + 1 :=
    hfac ▸ (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hN30).mp (hj ▸ hdvdC)
  have hjge : v + 1 ≤ j := by
    by_contra hlt
    push Not at hlt
    have hyv : y ^ 3 ^ v = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hj]
      exact Nat.pow_dvd_pow 3 (by omega)
    have hcv : (c ^ (3 * k + 1)) ^ 3 ^ (v - 1) = 1 := by
      apply scalar_injective_three
      rw [map_pow, ← hy3, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hv1, hyv, map_one]
    have hdetY : GeneralLinearGroup.det y = c ^ (3 * k + 1) := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, det_eq_of_cube hℓ hy]
    have : NeZero N := ⟨hN0⟩
    have := rootsOfUnity.isCyclic K N
    have hTcard : Nat.card (rootsOfUnity N K) = N := card_rootsOfUnity_qSubPi hK hq
    set t : rootsOfUnity N K := ⟨GeneralLinearGroup.det y, det_mem_rootsOfUnity hK hyH⟩ with htdef
    have htv : t ^ 3 ^ (v - 1) = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      change (GeneralLinearGroup.det y) ^ 3 ^ (v - 1) = 1
      rw [hdetY, hcv]
    have h1 : 3 * 3 ^ (v - 1) ∣ N := by
      rw [← pow_succ', Nat.sub_add_cancel hv1]
      exact Nat.ordProj_dvd N 3
    obtain ⟨r, hr⟩ := Nat.dvd_div_of_mul_dvd h1
    have ht : t ^ (Nat.card (rootsOfUnity N K) / 3) = 1 := by
      rw [hTcard, hr, pow_mul, htv, one_pow]
    obtain ⟨s, hs⟩ := exists_pow_three_eq (by rw [hTcard]; exact three_dvd_qSubPi hq) ht
    apply hℓ ((s : Kˣ) : K)
    have := congrArg (fun u : rootsOfUnity N K => ((u : Kˣ) : K)) hs
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val] at this
    rw [this]
    change ((GeneralLinearGroup.det y : Kˣ) : K) = ℓ
    rw [hdetY]
  have hord : orderOf y = ordProj[3] (qSubPi π ((p ^ f) ^ 3)) := by
    rw [hj, hproj, le_antisymm hjle hjge]
  obtain ⟨hcyc, hcard⟩ := centralizer_slPi_cyclic hK hq hyH hℓ hy
  obtain ⟨w, hwL, hwy⟩ := exists_w hK hq hτ hτ1 hyH hℓ hy
  obtain ⟨hwo, hwC, hcent, hcard3⟩ := irreducible_centMod_structure hK hq hτ hτ1 hℓ hy hwL hwy
  exact ⟨y, ⟨z, hzZ, rfl⟩, hord, fun W hW => eq_bot_or_eq_top_of_invariant hc hxm hW,
    fun W hW => eq_bot_or_eq_top_of_invariant hℓ hy hW, hcyc, hcard, w, hwL, hwo, hwC, hcent,
    hcard3⟩

end CFSG.RankThree.PartTwo.Sec4
