module

public import CFSG.Walter.ReeOrder.WardLocal.Blocks2
public import CFSG.Walter.ReeOrder.WardLocal.XiZ

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

theorem cY_arith {q m a c N : ℤ} {j n : ℕ} (hc : c = 3 ^ j) (hqn : q = 3 ^ n)
    (hm : q = 3 * m ^ 2) (hmodd : Odd m) (hm0 : 0 < m) (hjn : n + 1 ≤ j)
    (hN : c * N = q + 6 * m * a) (hN0 : 0 ≤ N) (hb : 1 + 4 * a ^ 2 ≤ c) : j = n + 1 ∧ a = m := by
  set k₀ : ℤ := 3 ^ (j - n) with hk₀
  have hck : c = k₀ * q := by
    rw [hc, hqn, hk₀, ← pow_add]; congr 1; omega
  have hk3 : 3 ≤ k₀ := by
    rw [hk₀]
    calc (3 : ℤ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (j - n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2a : 2 * a = m * (k₀ * N - 1) := by
    have h1 : 3 * m * (2 * a) = 3 * m * (m * (k₀ * N - 1)) := by
      rw [hck, hm] at hN; linear_combination -hN
    exact mul_left_cancel₀ (by positivity) h1
  obtain ⟨t, ht⟩ : Even (k₀ * N - 1) := by
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    have h1 : Odd (m * (k₀ * N - 1)) := hmodd.mul hodd
    rw [← h2a] at h1
    exact (Int.not_odd_iff_even.mpr (even_two_mul a)) h1
  have ha : a = m * t := by
    have : 2 * a = 2 * (m * t) := by rw [h2a, ht]; ring
    linarith
  have hkN : k₀ * N = 1 + 2 * t := by linarith [ht]
  have hN1 : 1 ≤ N := by
    rcases (show N = 0 ∨ 1 ≤ N by omega) with h | h
    · rw [h, mul_zero] at hkN; omega
    · exact h
  have hbt : 4 * t ^ 2 < 3 * k₀ := by
    rw [ha, hck, hm] at hb
    have hm2 : 0 < m ^ 2 := by positivity
    by_contra h
    push Not at h
    nlinarith
  have hk : k₀ ≤ 1 + 2 * t := by nlinarith
  have hjn' : j - n = 1 := by
    by_contra hne
    have h2 : 2 ≤ j - n := by omega
    have h9 : 9 ≤ k₀ := by
      rw [hk₀]
      calc (9 : ℤ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (j - n) := pow_le_pow_right₀ (by norm_num) h2
    nlinarith
  have hk03 : k₀ = 3 := by rw [hk₀, hjn']; norm_num
  rw [hk03] at hbt hkN
  have ht1 : t = 1 := by
    have : t ≤ 1 := by nlinarith
    have : 1 ≤ t := by omega
    omega
  exact ⟨by omega, by rw [ha, ht1, mul_one]⟩

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

omit [Group G] [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
theorem conj_conj (χ : G → ℂ) : starRingEnd ℂ ∘ (starRingEnd ℂ ∘ χ) = χ := by
  funext x; simp

omit [CharP K 3] in
theorem conj5_S3 : starRingEnd ℂ ∘ B.ξ₅ ∈ S.S3 := by
  refine mem_supp.mpr ⟨irr_conj B.irr_5, ?_⟩
  rw [S.conj_d3 B.irr_5]
  simp only [↓reduceIte, B.d2_5]
  norm_num

omit [CharP K 3] in
theorem conj6_S3 : starRingEnd ℂ ∘ B.ξ₆ ∈ S.S3 := by
  refine mem_supp.mpr ⟨irr_conj B.irr_6, ?_⟩
  rw [S.conj_d3 B.irr_6]
  simp only [↓reduceIte, B.d2_6]
  norm_num

omit [Group G] [Fintype G] [CharP K 3] in
theorem conj_ne {χ ψ : G → ℂ} (h : χ ≠ ψ) : starRingEnd ℂ ∘ χ ≠ starRingEnd ℂ ∘ ψ := by
  intro h'
  apply h
  rw [← conj_conj χ, h', conj_conj]

omit [CharP K 3] in
theorem n3c5 : B.ξ₃ ≠ starRingEnd ℂ ∘ B.ξ₅ := by
  intro h; apply B.n35; rw [← conj_conj B.ξ₅, ← h, B.real_3]
omit [CharP K 3] in
theorem n3c6 : B.ξ₃ ≠ starRingEnd ℂ ∘ B.ξ₆ := by
  intro h; apply B.n36; rw [← conj_conj B.ξ₆, ← h, B.real_3]
omit [CharP K 3] in
theorem n4c5 : B.ξ₄ ≠ starRingEnd ℂ ∘ B.ξ₅ := by
  intro h; apply B.n45; rw [← conj_conj B.ξ₅, ← h, B.real_4]
omit [CharP K 3] in
theorem n4c6 : B.ξ₄ ≠ starRingEnd ℂ ∘ B.ξ₆ := by
  intro h; apply B.n46; rw [← conj_conj B.ξ₆, ← h, B.real_4]

omit [CharP K 3] in
theorem hS3 : S.S3 = {B.ξ₃, B.ξ₄, starRingEnd ℂ ∘ B.ξ₅, starRingEnd ℂ ∘ B.ξ₆} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl | rfl
    · exact B.ξ₃_S3
    · exact B.ξ₄_S3
    · exact B.conj5_S3
    · exact B.conj6_S3
  · rw [S.card_S3, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (conj_ne B.n56)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨B.n4c5, B.n4c6⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨B.n34, B.n3c5, B.n3c6⟩

omit [CharP K 3] in
theorem sum_S3 {M : Type*} [AddCommMonoid M] (f : (G → ℂ) → M) :
    ∑ χ ∈ S.S3, f χ = f B.ξ₃ + f B.ξ₄ + f (starRingEnd ℂ ∘ B.ξ₅) + f (starRingEnd ℂ ∘ B.ξ₆) :=
  sum_four B.hS3 B.n34 B.n3c5 B.n3c6 B.n4c5 B.n4c6 (conj_ne B.n56) f

omit [CharP K 3] in
theorem d3_3 : S.d3 B.ξ₃ = 1 := by
  rw [← S.agree13 (show B.ξ₃ ∈ S.S1 by rw [B.hS1]; simp) B.ξ₃_S3, B.d1_3]
omit [CharP K 3] in
theorem d3_4 : S.d3 B.ξ₄ = -1 := by
  rw [← S.agree13 (show B.ξ₄ ∈ S.S1 by rw [B.hS1]; simp) B.ξ₄_S3, B.d1_4]
omit [CharP K 3] in
theorem d3_c5 : S.d3 (starRingEnd ℂ ∘ B.ξ₅) = -1 := by
  rw [S.conj_d3 B.irr_5]; simp only [↓reduceIte, B.d2_5]
omit [CharP K 3] in
theorem d3_c6 : S.d3 (starRingEnd ℂ ∘ B.ξ₆) = 1 := by
  rw [S.conj_d3 B.irr_6]; simp only [↓reduceIte, B.d2_6]

end Block

namespace Block

include hq hG hPc in
omit [Fintype K] [DecidableEq K] [CharP K 3] in
theorem mem_P_of_three {z : G} (hzN : z ∈ Subgroup.normalizer (P : Set G)) {a : ℕ}
    (hz : orderOf z = 3 ^ a) : z ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hz])
  have hsup := hzp.to_sup_of_normal_right' (isPGroup_P hq hPc)
    (Subgroup.zpowers_le.mpr hzN)
  obtain ⟨Q, hQ⟩ := hsup.exists_le_sylow
  have hle : P ≤ Subgroup.zpowers z ⊔ P := le_sup_right
  have heq : P = Subgroup.zpowers z ⊔ P := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hPc, ← card_sylow3 hq hG Q]; exact Subgroup.card_le_of_le hQ)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)

include hq hPc in
omit [CharP K 3] in
theorem exists_conj_J {u : G} (hu : u ∈ P) (huJ : S.J * u * S.J = u⁻¹) :
    ∃ v ∈ P, u * S.J = v * S.J * v⁻¹ := by
  have hodd : Odd (orderOf u) := by
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨u, hu⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  obtain ⟨s, hs⟩ := hodd
  refine ⟨u ^ (s + 1), P.pow_mem hu _, ?_⟩
  have hvv : u ^ (s + 1) * u ^ (s + 1) = u := by
    rw [← pow_add, show s + 1 + (s + 1) = orderOf u + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hvJ : S.J * u ^ (s + 1) * S.J = (u ^ (s + 1))⁻¹ := by
    rw [conj_pow_of_mul_self S.J_mul, huJ, inv_pow]
  have hvJ' : S.J * (u ^ (s + 1))⁻¹ * S.J = u ^ (s + 1) := by
    calc S.J * (u ^ (s + 1))⁻¹ * S.J = (S.J * u ^ (s + 1) * S.J)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, S.J_inv]; group
      _ = u ^ (s + 1) := by rw [hvJ, inv_inv]
  calc u * S.J = u ^ (s + 1) * u ^ (s + 1) * S.J := by rw [hvv]
    _ = u ^ (s + 1) * (S.J * (u ^ (s + 1))⁻¹ * S.J) * S.J := by rw [hvJ']
    _ = u ^ (s + 1) * S.J * (u ^ (s + 1))⁻¹ * (S.J * S.J) := by group
    _ = u ^ (s + 1) * S.J * (u ^ (s + 1))⁻¹ := by rw [S.J_mul, mul_one]

include B hq hK hG hP1P hPc hPn hN1c in
theorem mem_normalizer_of_commute {y z : G} (hy : y ∈ P) (hy1 : y ≠ 1) (hzy : z * y = y * z) :
    z ∈ Subgroup.normalizer (P : Set G) := by
  have hQ : ∀ x, x ∈ P ↔ (1 : G)⁻¹ * x * 1 ∈ P := fun x => by simp
  rcases B.inf_conj hq hK hG hP1P hPc hPn hN1c hQ z⁻¹ with h | h
  · exfalso
    have hmem : y ∈ P ⊓ (MulAut.conj z⁻¹ • P) := by
      refine Subgroup.mem_inf.mpr ⟨hy, ?_⟩
      rw [mem_conj_smul_iff, inv_inv, hzy, mul_inv_cancel_right]
      exact hy
    rw [h, Subgroup.mem_bot] at hmem
    exact hy1 hmem
  · have hle : P ≤ MulAut.conj z⁻¹ • P :=
      calc P = P ⊓ MulAut.conj z⁻¹ • P := h.symm
        _ ≤ _ := inf_le_right
    have heq : MulAut.conj z⁻¹ • P = P := (Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Nat.card_congr (Subgroup.equivSMul (MulAut.conj z⁻¹) P).toEquiv).symm)).symm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx : x ∈ MulAut.conj z⁻¹ • P ↔ x ∈ P := by rw [heq]
    rw [mem_conj_smul_iff, inv_inv] at hx
    exact hx.symm

include B hq hK hG hP1P hPc hPn hN1c in
theorem centralizer_outer_le {y : G} (hy : y ∈ P) (hyP1 : y ∉ PP1 S) :
    Subgroup.centralizer ({y} : Set G) ≤ P := by
  have hcT := B.hcT hq hK hG
  have hy1 : y ≠ 1 := fun h => hyP1 (h ▸ (PP1 S).one_mem)
  intro z hz
  have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hz
  have hzN := B.mem_normalizer_of_commute hq hK hG hP1P hPc hPn hN1c hy hy1 hzy
  by_contra hzP
  have ho : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨e, b, hb3, hzb⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho 3 (by norm_num)
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [mul_one] at hzb
    exact hzP (mem_P_of_three hq hG hPc hzN hzb)
  set r := b.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime hb1
  have hrb : r ∣ b := Nat.minFac_dvd b
  have hr3 : r ≠ 3 := fun h => hb3 (h ▸ hrb)
  have hro : r ∣ orderOf z := hzb ▸ Dvd.dvd.mul_left hrb _
  set z₀ := z ^ (orderOf z / r) with hz₀
  have hz₀o : orderOf z₀ = r := by
    rw [hz₀, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos z) hro) hrp.pos).ne'
      (Nat.div_dvd_of_dvd hro), Nat.div_div_self hro ho]
  have hz₀N : z₀ ∈ Subgroup.normalizer (P : Set G) := Subgroup.pow_mem _ hzN _
  have hz₀y : z₀ * y = y * z₀ := (Commute.pow_left hzy _).eq
  have hz₀P : z₀ ∉ P := by
    intro h
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨z₀, h⟩
    rw [Subgroup.orderOf_mk, hz₀o] at hN
    have := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).mp
      (hrp.dvd_of_dvd_pow (hN ▸ dvd_refl r : r ∣ 3 ^ N))
    exact hr3 this
  obtain ⟨himg, -⟩ := B.image_mul_eq hq hK hG hP1P hPc hPn hN1c
  have hz₀' : z₀ ∈ Finset.univ.filter (· ∈ Subgroup.normalizer (P : Set G)) := by simp [hz₀N]
  rw [← himg] at hz₀'
  obtain ⟨⟨u, w⟩, huw, hz₀uw⟩ := Finset.mem_image.mp hz₀'
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at huw
  obtain ⟨hu, hw⟩ := huw
  simp only at hz₀uw
  have hw1 : w ≠ 1 := by
    rintro rfl; rw [mul_one] at hz₀uw; exact hz₀P (hz₀uw ▸ hu)
  by_cases hwJ : w = S.J
  · subst hwJ
    have hJN := B.J_mem_normalizer hq hK hG hPn
    have hsq : z₀ ^ 2 ∈ P := by
      rw [← hz₀uw, sq, show u * S.J * (u * S.J) = u * (S.J * u * S.J) by group]
      have := (Subgroup.mem_normalizer_iff.mp hJN u).mp hu
      rw [S.J_inv] at this
      exact P.mul_mem hu this
    have hsq1 : z₀ ^ 2 = 1 := by
      obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨_, hsq⟩
      rw [Subgroup.orderOf_mk] at hN
      have hdvd : orderOf (z₀ ^ 2) ∣ r := hz₀o ▸ orderOf_pow_dvd 2
      rw [hN] at hdvd
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0, pow_zero, orderOf_eq_one_iff] at hN; exact hN
      · exfalso
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hrp).mp
          ((dvd_pow_self 3 h0.ne').trans hdvd)
        exact hr3 this.symm
    have huJ : S.J * u * S.J = u⁻¹ := by
      rw [← hz₀uw, sq] at hsq1
      have := congrArg (fun t => u⁻¹ * t) hsq1
      simp only [mul_one] at this
      rw [← this]; group
    obtain ⟨v, hv, hvJ⟩ := exists_conj_J hq hPc hu huJ
    rw [← hz₀uw, hvJ] at hz₀y
    have hv' : v⁻¹ * y * v ∈ P ⊓ Subgroup.centralizer ({S.J} : Set G) := by
      refine ⟨P.mul_mem (P.mul_mem (P.inv_mem hv) hy) hv,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc v⁻¹ * y * v * S.J = v⁻¹ * (y * (v * S.J * v⁻¹)) * v := by group
        _ = v⁻¹ * ((v * S.J * v⁻¹) * y) * v := by rw [hz₀y]
        _ = S.J * (v⁻¹ * y * v) := by group
    rw [inf_centralizer_J hq hK hcT hP1P hPc] at hv'
    apply hyP1
    have := B.PP1_normal hq hK hG hP1P hPc hPn hN1c hv (FF_le_PP1 hq hcT hv')
    simpa [mul_assoc] using this
  ·
    have hwN := (WW_le_normalizer hq hK hcT hG (B.card_AA hq hK hG)
      (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c) hw
    have : Finite P := inferInstance
    obtain ⟨v, hv, hvw⟩ := exists_conj_of_inf_eq_bot hwN
      (inf_centralizer_WW hq hK hPc hw hw1 hwJ) hu
    rw [← hz₀uw, hvw] at hz₀y
    have hv' : v⁻¹ * y * v ∈ P ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine ⟨P.mul_mem (P.mul_mem (P.inv_mem hv) hy) hv,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc v⁻¹ * y * v * w = v⁻¹ * (y * (v * w * v⁻¹)) * v := by group
        _ = v⁻¹ * ((v * w * v⁻¹) * y) * v := by rw [hz₀y]
        _ = w * (v⁻¹ * y * v) := by group
    rw [inf_centralizer_WW hq hK hPc hw hw1 hwJ, Subgroup.mem_bot] at hv'
    apply hy1
    have := congrArg (fun t => v * t * v⁻¹) hv'
    simpa [mul_assoc] using this

end Block

namespace Block

include B hq hK hG hP1P hPc hPn in
theorem centralizer_zcen {X : G} (hX : X ∈ zcen P) (hX1 : X ≠ 1) :
    Subgroup.centralizer ({X} : Set G) = P := by
  have hXA := B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hX hX1
  have hcX := (centralizer_AA hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hXA).2
  have hle : P ≤ Subgroup.centralizer ({X} : Set G) := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact ((mem_zcen.mp hX).2 p hp).symm
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcX, hPc])).symm

include B hq hK hG hP1P hPc hPn hN1c in
theorem card_centralizer_J_dvd {Y X : G} (hY : Y ∈ P) (hYP1 : Y ∉ PP1 S) (hX : X ∈ zcen P)
    (hX1 : X ≠ 1) :
    Nat.card (Subgroup.centralizer ({S.J} : Set G)) ∣
      ((cls Y ×ˢ cls X).filter fun p => p.1 * p.2 = S.J).card := by
  set Sol := (cls Y).filter fun a => a⁻¹ * S.J ∈ cls X with hSol
  have hcard : ((cls Y ×ˢ cls X).filter fun p => p.1 * p.2 = S.J).card = Sol.card := by
    refine Finset.card_nbij' (fun p => p.1) (fun a => (a, a⁻¹ * S.J)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, hSol] at hp ⊢
      refine ⟨hp.1.1, ?_⟩
      rw [← hp.2]; simpa using hp.1.2
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, hSol] at ha ⊢
      exact ⟨⟨ha.1, ha.2⟩, by group⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
      ext
      · rfl
      · simp only; rw [← hp.2]; group
    · intro a _; rfl
  rw [hcard]
  apply card_dvd_card_of_free
  · intro g hg a ha
    simp only [hSol, Finset.mem_filter] at ha ⊢
    refine ⟨cls_invariant Y a ha.1 g, ?_⟩
    have hgJ : g * S.J = S.J * g := (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have : (g * a * g⁻¹)⁻¹ * S.J = g * (a⁻¹ * S.J) * g⁻¹ := by
      have hg' : g⁻¹ * S.J = S.J * g⁻¹ := by
        calc g⁻¹ * S.J = g⁻¹ * (S.J * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * S.J) * g⁻¹ := by rw [hgJ]
          _ = S.J * g⁻¹ := by group
      calc (g * a * g⁻¹)⁻¹ * S.J = g * a⁻¹ * (g⁻¹ * S.J) := by group
        _ = g * a⁻¹ * (S.J * g⁻¹) := by rw [hg']
        _ = g * (a⁻¹ * S.J) * g⁻¹ := by group
    rw [this]
    exact cls_invariant X _ ha.2 g
  · intro g hg hg1 a ha hga
    simp only [hSol, Finset.mem_filter, mem_cls] at ha
    obtain ⟨h, hh⟩ := isConj_iff.mp ha.1
    obtain ⟨h', hh'⟩ := isConj_iff.mp ha.2
    have hgJ : g * S.J = S.J * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hga' : g * a = a * g := by
      calc g * a = g * a * g⁻¹ * g := by group
        _ = a * g := by rw [hga]
    have hgb : g * (a⁻¹ * S.J) = (a⁻¹ * S.J) * g := by
      have : g * a⁻¹ = a⁻¹ * g := by
        calc g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹ := by group
          _ = a⁻¹ * (g * a) * a⁻¹ := by rw [hga']
          _ = a⁻¹ * g := by group
      calc g * (a⁻¹ * S.J) = (g * a⁻¹) * S.J := by group
        _ = a⁻¹ * (g * S.J) := by rw [this]; group
        _ = a⁻¹ * S.J * g := by rw [hgJ]; group
    have hg₁ : h * g * h⁻¹ ∈ P := by
      apply B.centralizer_outer_le hq hK hG hP1P hPc hPn hN1c hY hYP1
      rw [Subgroup.mem_centralizer_singleton_iff, ← hh]
      calc h * g * h⁻¹ * (h * a * h⁻¹) = h * (g * a) * h⁻¹ := by group
        _ = h * (a * g) * h⁻¹ := by rw [hga']
        _ = h * a * h⁻¹ * (h * g * h⁻¹) := by group
    have hg₂ : h' * g * h'⁻¹ ∈ P := by
      rw [← B.centralizer_zcen hq hK hG hP1P hPc hPn hX hX1, Subgroup.mem_centralizer_singleton_iff,
        ← hh']
      calc h' * g * h'⁻¹ * (h' * (a⁻¹ * S.J) * h'⁻¹) = h' * (g * (a⁻¹ * S.J)) * h'⁻¹ := by group
        _ = h' * ((a⁻¹ * S.J) * g) * h'⁻¹ := by rw [hgb]
        _ = h' * (a⁻¹ * S.J) * h'⁻¹ * (h' * g * h'⁻¹) := by group
    set Q : Subgroup G := MulAut.conj h⁻¹ • P with hQdef
    have hQ : ∀ x, x ∈ Q ↔ h⁻¹⁻¹ * x * h⁻¹ ∈ P := fun x => mem_conj_smul_iff
    set c := h'⁻¹ * h with hc
    have hcQ : ∀ x, x ∈ MulAut.conj c • Q ↔ h' * x * h'⁻¹ ∈ P := by
      intro x
      rw [mem_conj_smul_iff, hQ, hc]
      constructor <;> intro hx <;> convert hx using 1 <;> group
    rcases B.inf_conj hq hK hG hP1P hPc hPn hN1c hQ c with hbot | hQQ
    · have hmem : g ∈ Q ⊓ MulAut.conj c • Q :=
        Subgroup.mem_inf.mpr ⟨(hQ g).mpr (by simpa using hg₁), (hcQ g).mpr hg₂⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hg1 hmem
    · have hle : Q ≤ MulAut.conj c • Q :=
        calc Q = Q ⊓ MulAut.conj c • Q := hQQ.symm
          _ ≤ _ := inf_le_right
      have heq : MulAut.conj c • Q = Q := (Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Nat.card_congr (Subgroup.equivSMul (MulAut.conj c) Q).toEquiv).symm)).symm
      have haQ : a ∈ Q := (hQ a).mpr (by rw [inv_inv, hh]; exact hY)
      have hbQ : a⁻¹ * S.J ∈ Q := by
        rw [← heq, hcQ, hh']; exact (mem_zcen.mp hX).1
      have hJQ : S.J ∈ Q := by
        have := Q.mul_mem haQ hbQ
        simpa using this
      have hJP : h * S.J * h⁻¹ ∈ P := by simpa using (hQ _).mp hJQ
      obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨_, hJP⟩
      rw [Subgroup.orderOf_mk, show h * S.J * h⁻¹ = MulAut.conj h S.J from rfl,
        MulEquiv.orderOf_eq, S.orderOf_J] at hN
      have h2 : (2 : ℕ) ∣ 3 ^ N := hN ▸ dvd_refl 2
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)

end Block

theorem sum_YX_alg {q m a A5 A6 D5 D6 : ℂ} (hqm : q = 3 * m ^ 2) (hm : m ≠ 0)
    (h1 : 3 * m ^ 2 - 1 ≠ 0) (h2 : 3 * m ^ 2 + 1 + 3 * m ≠ 0) (h3 : 3 * m ^ 2 + 1 - 3 * m ≠ 0)
    (hA5 : 2 * A5 = -(q + m)) (hA6 : 2 * A6 = q - m) (hD5 : 2 * D5 = (q - 1) * m * (q + 1 + 3 * m))
    (hD6 : 2 * D6 = (q - 1) * m * (q + 1 - 3 * m)) :
    (1 - (1 - q) / (q ^ 2 - q + 1)) + (q - 1) / 2 *
      ((-(a * A5 / D5) + a * A6 / D6) + (-(a * A5 / D5) + a * A6 / D6)) =
      q * (q + 6 * m * a) / (q ^ 2 - q + 1) := by
  have eA5 : A5 = -(q + m) / 2 := by linear_combination hA5 / 2
  have eA6 : A6 = (q - m) / 2 := by linear_combination hA6 / 2
  have eD5 : D5 = (q - 1) * m * (q + 1 + 3 * m) / 2 := by linear_combination hD5 / 2
  have eD6 : D6 = (q - 1) * m * (q + 1 - 3 * m) / 2 := by linear_combination hD6 / 2
  rw [eA5, eA6, eD5, eD6, hqm]
  have h5 : (3 * m ^ 2) ^ 2 - 3 * m ^ 2 + 1 =
      (3 * m ^ 2 + 1 + 3 * m) * (3 * m ^ 2 + 1 - 3 * m) := by ring
  rw [h5]
  field_simp
  ring

namespace Block

include B hq hK hG hP1P hPc hPn hN1c in
theorem sum_YX (hm : q = 3 * m ^ 2) {Y X : G} (hY : Y ∈ P) (hYP1 : Y ∉ PP1 S)
    (hYJ : S.J * Y * S.J = Y⁻¹) (hX : X ∈ zcen P) (hX1 : X ≠ 1) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, χ Y * χ X * starRingEnd ℂ (χ S.J) / χ 1 =
      (q : ℂ) * (q + 6 * m * B.ξ₅ Y) / ((q : ℂ) ^ 2 - q + 1) := by
  have hcT := B.hcT hq hK hG
  have hq27 : 27 ≤ q := S.q_ge
  have hm3 : 3 ≤ m := by
    by_contra h
    have : m ≤ 2 := by omega
    have : q ≤ 12 := by rw [hm]; nlinarith
    omega
  have hZP1 := B.zcen_le_PP1 hq hK hG hP1P hPc hPn
  have hY1 : Y ≠ 1 := fun h => hYP1 (h ▸ (PP1 S).one_mem)
  have hY3 : 3 ∣ orderOf Y := three_dvd_of_mem (isPGroup_P hq hPc) hY hY1
  have hodd : ∀ {x : G}, x ∈ P → Odd (orderOf x) := fun {x} hx => by
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  have hXP : X ∈ P := (mem_zcen.mp hX).1
  have hX3 : 3 ∣ orderOf X := three_dvd_of_mem (isPGroup_P hq hPc) hXP hX1
  obtain ⟨h2Y, h4Y⟩ := B.xi2_outer hq hK hG hP1P hPc hPn hN1c hY hYP1
  have h3Y : B.ξ₃ Y = 0 := B.xi3_eq_zero hq hG hY3
  have h6Y : B.ξ₆ Y = B.ξ₅ Y := by
    have := B.col_d2 (hodd hY); rw [h3Y, h4Y] at this; linear_combination this
  have hYreal : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → starRingEnd ℂ (χ Y) = χ Y := by
    intro χ hχ
    rw [← inv_eq_conj hχ, ← hYJ, show S.J * Y * S.J = S.J * Y * S.J⁻¹ by rw [S.J_inv],
      irr_class hχ]
  have hXA := B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hX hX1
  have h2X : B.ξ₂ X = 1 - q := by
    rw [B.xi2_PP1 hq hK hG (hZP1 hX) hX1]; simp [hXA]
  have h3X : B.ξ₃ X = 0 := B.xi3_eq_zero hq hG hX3
  have h4X : B.ξ₄ X = q := by
    have := (B.eta_eq_one hq hG (hodd hXP) hX3 S.i₀).2.2
    rw [h2X] at this; linear_combination this
  obtain ⟨h5X, h6X⟩ := B.xi56_zcen hq hK hG hP1P hPc hPn hm hX hX1
  have h5Xr : starRingEnd ℂ (B.ξ₅ X) = B.ξ₅ X := by
    have : B.ξ₅ X = -((q : ℂ) + m) / 2 := by linear_combination h5X / 2
    rw [this]; simp [map_div₀, map_ofNat]
  have h6Xr : starRingEnd ℂ (B.ξ₆ X) = B.ξ₆ X := by
    have : B.ξ₆ X = ((q : ℂ) - m) / 2 := by linear_combination h6X / 2
    rw [this]; simp [map_div₀, map_ofNat]
  have hd5 : 2 * B.ξ₅ 1 = ((q : ℂ) - 1) * m * (q + 1 + 3 * m) := by
    rw [← deg_eq B.irr_5]
    have := B.deg_5
    have h' : ((2 * deg B.ξ₅ : ℤ) : ℂ) = ((((q : ℤ) - 1) * m * (q + 1 + 3 * m) : ℤ) : ℂ) := by
      rw [this]
    push_cast at h'; exact h'
  have hd6 : 2 * B.ξ₆ 1 = ((q : ℂ) - 1) * m * (q + 1 - 3 * m) := by
    rw [← deg_eq B.irr_6]
    have := B.deg_6
    have h' : ((2 * deg B.ξ₆ : ℤ) : ℂ) = ((((q : ℤ) - 1) * m * (q + 1 - 3 * m) : ℤ) : ℂ) := by
      rw [this]
    push_cast at h'; exact h'
  have h5r : starRingEnd ℂ (B.ξ₅ 1) = B.ξ₅ 1 := by rw [← deg_eq B.irr_5]; simp
  have h6r : starRingEnd ℂ (B.ξ₆ 1) = B.ξ₆ 1 := by rw [← deg_eq B.irr_6]; simp
  obtain ⟨hξ21, hξ31, hξ41⟩ := B.xi_one
  rw [B.sum_J hq hK hG hP1P hPc hPn hN1c (hodd hY) (hodd hXP)]
  have hsplit : ∀ χ : G → ℂ, (χ Y * χ X / χ 1) *
      ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) =
      (χ Y * χ X / χ 1) * S.d1 χ + ((q : ℂ) - 1) / 2 *
        ((χ Y * χ X / χ 1) * S.d2 χ + (χ Y * χ X / χ 1) * S.d3 χ) := fun χ => by ring
  rw [Finset.sum_congr rfl fun χ _ => hsplit χ, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib,
    sum_irr_eq_sum_of_vanish (supp_sub S.d1) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van1 hχ hnot]; simp),
    sum_irr_eq_sum_of_vanish (supp_sub S.d2) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van2 hχ hnot]; simp),
    sum_irr_eq_sum_of_vanish (supp_sub S.d3) _ (fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ; rw [S.van3 hχ hnot]; simp)]
  rw [show supp S.d1 = S.S1 from rfl, show supp S.d2 = S.S2 from rfl,
    show supp S.d3 = S.S3 from rfl, B.sum_S1, B.sum_S2, B.sum_S3]
  simp only [Function.comp_apply, Pi.one_apply, S.one_row.1, B.d1_2, B.d1_3, B.d1_4, B.d2_3,
    B.d2_4, B.d2_5, B.d2_6, B.d3_3, B.d3_4, B.d3_c5, B.d3_c6, hYreal B.irr_5,
    h5Xr, h6Xr, h5r, h6r, h2Y, h3Y, h4Y, h6Y, h2X, h3X, h4X, hξ21, hξ31, hξ41]
  push_cast
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hqm : (q : ℂ) = 3 * (m : ℂ) ^ 2 := by rw [hm]; push_cast; ring
  have hne : ∀ z : ℤ, z ≠ 0 → (z : ℂ) ≠ 0 := fun z hz => by exact_mod_cast hz
  have h1 : 3 * (m : ℂ) ^ 2 - 1 ≠ 0 := by
    have := hne (3 * (m : ℤ) ^ 2 - 1) (by nlinarith); push_cast at this; exact this
  have h2 : 3 * (m : ℂ) ^ 2 + 1 + 3 * m ≠ 0 := by
    have := hne (3 * (m : ℤ) ^ 2 + 1 + 3 * m) (by positivity); push_cast at this; exact this
  have h3 : 3 * (m : ℂ) ^ 2 + 1 - 3 * m ≠ 0 := by
    have := hne (3 * (m : ℤ) ^ 2 + 1 - 3 * m) (by nlinarith); push_cast at this; exact this
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqq : (q : ℂ) ^ 2 - q + 1 ≠ 0 := by
    have := hne ((q : ℤ) ^ 2 - q + 1) (by nlinarith); push_cast at this; exact this
  have halg := sum_YX_alg (a := B.ξ₅ Y) hqm hm0 h1 h2 h3 h5X h6X hd5 hd6
  rw [← halg]
  field_simp
  ring

end Block

namespace Block

include B hq hK hG hP1P hPc hPn hN1c in
theorem centralizer_inv_outer (hm : q = 3 * m ^ 2) {Y : G} (hY : Y ∈ P) (hYP1 : Y ∉ PP1 S)
    (hYJ : S.J * Y * S.J = Y⁻¹) :
    Nat.card (Subgroup.centralizer ({Y} : Set G)) = 3 * q ∧ B.ξ₅ Y = m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcT := B.hcT hq hK hG
  have hq27 : 27 ≤ q := S.q_ge
  have hm3 : 3 ≤ m := by
    by_contra h
    have : m ≤ 2 := by omega
    have : q ≤ 12 := by rw [hm]; nlinarith
    omega
  have hZP1 := B.zcen_le_PP1 hq hK hG hP1P hPc hPn
  have hY1 : Y ≠ 1 := fun h => hYP1 (h ▸ (PP1 S).one_mem)
  obtain ⟨X, hX, hX1⟩ : ∃ X ∈ zcen P, X ≠ 1 := by
    have h := B.card_zcen hq hK hG hP1P hPc hPn
    by_contra hall
    push Not at hall
    have : zcen P = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [this, Subgroup.card_bot] at h
    omega
  have hXA := B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hX hX1
  have hcX := (centralizer_AA hq hK hcT hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hXA).2
  set N := ((cls Y ×ˢ cls X).filter fun p => p.1 * p.2 = S.J).card with hNdef
  have hcm := class_mult Y X S.J
  rw [B.sum_YX hq hK hG hP1P hPc hPn hN1c hm hY hYP1 hYJ hX hX1, hcX, hG] at hcm
  set cY := Nat.card (Subgroup.centralizer ({Y} : Set G)) with hcYdef
  set a := B.ξ₅ Y with ha
  obtain ⟨N', hN'⟩ := B.card_centralizer_J_dvd hq hK hG hP1P hPc hPn hN1c hY hYP1 hX hX1
  have hCJ := S.card_C
  have hq1 : (1 : ℕ) ≤ q := by omega
  have hqq : (q : ℂ) ^ 2 - q + 1 ≠ 0 := by
    have : ((q : ℤ) ^ 2 - q + 1 : ℤ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq1' : (q : ℂ) ^ 2 - 1 ≠ 0 := by
    have : ((q : ℤ) ^ 2 - 1 : ℤ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hcm2 : (N : ℂ) * cY * (q : ℂ) ^ 3 =
      (q : ℂ) ^ 4 * ((q : ℂ) ^ 2 - 1) * ((q : ℂ) + 6 * m * a) := by
    have h := hcm
    push_cast [Nat.cast_sub hq1] at h
    rw [h]
    have e : ((q : ℂ) ^ 3 + 1) = ((q : ℂ) + 1) * ((q : ℂ) ^ 2 - q + 1) := by ring
    rw [e]
    calc (q : ℂ) ^ 3 * (((q : ℂ) + 1) * ((q : ℂ) ^ 2 - q + 1)) * ((q : ℂ) - 1) *
          ((q : ℂ) * ((q : ℂ) + 6 * m * a) / ((q : ℂ) ^ 2 - q + 1))
        = (q : ℂ) ^ 3 * ((q : ℂ) + 1) * ((q : ℂ) - 1) * ((q : ℂ) * ((q : ℂ) + 6 * m * a)) *
          (((q : ℂ) ^ 2 - q + 1) / ((q : ℂ) ^ 2 - q + 1)) := by ring
      _ = (q : ℂ) ^ 4 * ((q : ℂ) ^ 2 - 1) * ((q : ℂ) + 6 * m * a) := by
          rw [div_self hqq]; ring
  have hNc : (N : ℂ) = (q : ℂ) * ((q : ℂ) ^ 2 - 1) * N' := by
    rw [hNdef, hN']; push_cast; rw [hCJ]
  have hkey : (N' : ℂ) * cY = q + 6 * m * a := by
    rw [hNc] at hcm2
    have hfac : (q : ℂ) ^ 4 * ((q : ℂ) ^ 2 - 1) ≠ 0 := mul_ne_zero (pow_ne_zero 4 hq0) hq1'
    apply mul_left_cancel₀ hfac
    linear_combination hcm2
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  obtain ⟨a', ha'⟩ := exists_int_of_isIntegral (isIntegral_irr B.irr_5 Y)
    (r := ((N' : ℚ) * cY - q) / (6 * m)) (by
      push_cast
      rw [← ha]
      field_simp
      linear_combination -hkey)
  rw [← ha] at ha'
  have hCP := B.centralizer_outer_le hq hK hG hP1P hPc hPn hN1c hY hYP1
  have hCp : IsPGroup 3 (Subgroup.centralizer ({Y} : Set G)) := (isPGroup_P hq hPc).to_le hCP
  obtain ⟨j, hj⟩ := hCp.exists_card_eq
  rw [← hcYdef] at hj
  have hlt : q < cY := by
    have hle : zcen P ≤ Subgroup.centralizer ({Y} : Set G) := fun c hc => by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact (mem_zcen.mp hc).2 Y hY
    have hne : zcen P ≠ Subgroup.centralizer ({Y} : Set G) := by
      intro h
      have : Y ∈ zcen P := by rw [h]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      exact hYP1 (hZP1 this)
    rw [← B.card_zcen hq hK hG hP1P hPc hPn]
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
  have hjn : 2 * k + 1 + 1 ≤ j := by
    rw [hj, hq] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hb : 1 + 4 * a' ^ 2 ≤ (cY : ℤ) := by
    set X5 : Finset (G → ℂ) := insert 1 (S.S2 ∪ S.S3) with hX5
    have hsub : X5 ⊆ (irreducibles_finite G).toFinset := by
      intro χ hχ
      rw [Finset.mem_insert, Finset.mem_union] at hχ
      rcases hχ with rfl | h | h
      · rw [Set.Finite.mem_toFinset]; exact one_mem_blocksIrr G
      · exact supp_sub _ h
      · exact supp_sub _ h
    have hbound := sum_normSq_le Y hsub
    have h1n : (1 : G → ℂ) ∉ S.S2 ∪ S.S3 := by
      rw [Finset.mem_union, not_or]; exact ⟨S.one_not_S2, S.one_not_S3⟩
    rw [hX5, Finset.sum_insert h1n] at hbound
    have hU := Finset.sum_union_inter (s₁ := S.S2) (s₂ := S.S3)
      (f := fun χ => Complex.normSq (χ Y))
    have hinter : ∑ χ ∈ S.S2 ∩ S.S3, Complex.normSq (χ Y) = 0 := by
      refine Finset.sum_eq_zero fun χ hχ => ?_
      rw [Finset.mem_inter] at hχ
      have h2 := hχ.1
      rw [B.hS2] at h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      rcases h2 with rfl | rfl | rfl | rfl
      · rw [B.xi3_eq_zero hq hG (three_dvd_of_mem (isPGroup_P hq hPc) hY hY1)]; simp
      · rw [(B.xi2_outer hq hK hG hP1P hPc hPn hN1c hY hYP1).2]; simp
      · exact absurd hχ.2 B.ξ₅_S3
      · exact absurd hχ.2 B.ξ₆_S3
    rw [hinter, add_zero] at hU
    rw [hU, B.sum_S2, B.sum_S3] at hbound
    have h3Y : B.ξ₃ Y = 0 := B.xi3_eq_zero hq hG (three_dvd_of_mem (isPGroup_P hq hPc) hY hY1)
    have h4Y := (B.xi2_outer hq hK hG hP1P hPc hPn hN1c hY hYP1).2
    have hodd : Odd (orderOf Y) := by
      obtain ⟨M, hM⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨Y, hY⟩
      rw [Subgroup.orderOf_mk] at hM
      rw [hM]; exact Odd.pow (by decide)
    have h6Y : B.ξ₆ Y = B.ξ₅ Y := by
      have := B.col_d2 hodd; rw [h3Y, h4Y] at this; linear_combination this
    simp only [Function.comp_apply, Pi.one_apply, h3Y, h4Y, h6Y, ← ha, ha',
      Complex.normSq_conj, Complex.normSq_intCast, Complex.normSq_one, map_zero] at hbound
    have : ((1 + 4 * a' ^ 2 : ℤ) : ℝ) ≤ ((cY : ℤ) : ℝ) := by push_cast at hbound ⊢; linarith
    exact_mod_cast this
  have hmodd : Odd (m : ℤ) := by
    have h1 : m ^ 2 = (3 ^ k) ^ 2 := by
      have : 3 * m ^ 2 = 3 * (3 ^ k) ^ 2 := by rw [← hm, hq, ← pow_mul, pow_succ']; ring_nf
      omega
    have h2 : m = 3 ^ k := Nat.pow_left_injective (by norm_num) h1
    rw [h2]; push_cast; exact Odd.pow (by decide)
  have hkeyZ : (cY : ℤ) * N' = q + 6 * m * a' := by
    have : (((cY : ℤ) * N' : ℤ) : ℂ) = ((q + 6 * m * a' : ℤ) : ℂ) := by
      push_cast; rw [← ha']; linear_combination hkey
    exact_mod_cast this
  obtain ⟨hj1, ham⟩ := cY_arith (q := (q : ℤ)) (m := (m : ℤ)) (a := a') (c := (cY : ℤ))
    (N := (N' : ℤ)) (j := j) (n := 2 * k + 1) (by rw [hj]; push_cast; ring)
    (by rw [hq]; push_cast; ring) (by rw [hm]; push_cast; ring) hmodd
    (by exact_mod_cast (show 0 < m by omega)) hjn hkeyZ (by positivity) hb
  refine ⟨?_, ?_⟩
  · rw [hj, hj1, pow_succ, hq]; ring
  · rw [ha', ham]; push_cast; ring

end Block

end CFSG.Walter.WardLocal
