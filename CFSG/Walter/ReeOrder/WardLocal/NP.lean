module

public import CFSG.Walter.ReeOrder.WardLocal.N1b

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {k : ℕ} (hq : q = 3 ^ (2 * k + 1))
  (hK : Fintype.card K = q) (hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1)) (hA : (AA S).card = q - 1)
  (hC1 : ∀ x : G, Odd (orderOf x) → 3 ∣ orderOf x →
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 2 * q ^ 3)
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

omit [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
include hq hPc in
theorem isPGroup_P : IsPGroup 3 P :=
  IsPGroup.of_card (n := 3 * (2 * k + 1)) (by rw [hPc, hq, ← pow_mul, mul_comm])

noncomputable def sylP (hq : q = 3 ^ (2 * k + 1)) (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
    (hPc : Nat.card P = q ^ 3) : Sylow 3 G :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard P (by rw [hPc, Block.three_part hq hG])

omit [Fintype K] [DecidableEq K] [CharP K 3] in
theorem coe_sylP : ((sylP hq hG hPc : Sylow 3 G) : Subgroup G) = P := by
  rw [sylP, Sylow.coe_ofCard]

omit [CharP K 3] in
include hPn in
theorem NN1_le_normalizer : NN1 S ≤ Subgroup.normalizer (P : Set G) := fun n hn =>
  mem_normalizer_of_conj_mem (fun x hx => hPn n hn x hx)

omit [Fintype G] in
theorem conj_mem_zcen {P : Subgroup G} {n z : G} (hn : n ∈ Subgroup.normalizer (P : Set G))
    (hz : z ∈ zcen P) : n * z * n⁻¹ ∈ zcen P := by
  obtain ⟨hzP, hzc⟩ := mem_zcen.mp hz
  refine mem_zcen.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn z).mp hzP, fun p hp => ?_⟩
  have hp' : n⁻¹ * p * n ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) p).mp hp
    simpa using this
  have h := hzc _ hp'
  calc n * z * n⁻¹ * p = n * (z * (n⁻¹ * p * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * p * n) * z) * n⁻¹ := by rw [h]
    _ = p * (n * z * n⁻¹) := by group

omit [Fintype G] in
theorem normalizer_le_normalizer_zcen {P : Subgroup G} :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (zcen P : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨conj_mem_zcen hn, fun h => ?_⟩
  have := conj_mem_zcen (Subgroup.inv_mem _ hn) h
  simpa [mul_assoc] using this

include hq hK hcT hG hA hP1P hPc in
theorem zcen_le_CC : zcen P ≤ CC S hq hK hcT hG := by
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; exact Subgroup.one_mem _
  have hFF := FF_le_PP1 (S := S) hq hcT
  have hP'P := coe_sylP hq hG hPc
  have hz' : z ∈ zcen ((sylP hq hG hPc : Sylow 3 G) : Subgroup G) := by rw [hP'P]; exact hz
  have hzP1 : z ∈ PP1 S :=
    zcen_le_PP1 hq hcT (P := sylP hq hG hPc) (by rw [hP'P]; exact hP1P) hFF hz'
  have hle : P ≤ Subgroup.centralizer ({z} : Set G) := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact ((mem_zcen.mp hz).2 p hp).symm
  have hcz := Subgroup.card_le_of_le hle
  rw [hPc] at hcz
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  refine AA_subset_CC hq hK hcT hG hA (mem_AA.mpr ⟨hzP1, hz1, fun t ht h =>
    zcen_no_involution hq hK hcT hG hz' hz1 ht h, ?_⟩)
  calc q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    _ ≤ _ := hcz

include hq hcT hPn in
omit [CharP K 3] in
theorem RR_le_normalizer_P : RR S ≤ Subgroup.normalizer (P : Set G) :=
  fun _ hd => NN1_le_normalizer hPn (RR_le_normalizer_PP1 hq hcT hd)

include hq hK hcT hG hA hP1P hPc hPn in
theorem zcen_eq_CC : zcen P = CC S hq hK hcT hG := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := zcen_le_CC hq hK hcT hG hA hP1P hPc
  have hZp : IsPGroup 3 (zcen P) := (isPGroup_P hq hPc).to_le (Subgroup.map_subtype_le _)
  obtain ⟨t, ht⟩ := card_RR_invariant hq hK hZp
    ((RR_le_normalizer_P hq hcT hPn).trans normalizer_le_normalizer_zcen)
  have hcle := Subgroup.card_le_of_le hle
  rw [card_CC hq hK hcT hG hA, ht] at hcle
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hPc' : 1 < Nat.card (sylP hq hG hPc : Sylow 3 G) := by
    rw [coe_sylP, hPc]
    calc 1 < 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
  obtain ⟨z, hz, hz1⟩ := exists_zcen_ne_one _ hPc'
  rw [coe_sylP] at hz
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      rw [h0, pow_zero] at ht
      have := (Subgroup.card_eq_one.mp ht)
      rw [this] at hz
      exact hz1 ((Subgroup.mem_bot).mp hz)
    · exact h0
  have ht' : t = 1 := by
    by_contra h
    have : q ^ 1 < q ^ t := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [pow_one] at this
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_CC hq hK hcT hG hA, ht, ht', pow_one])

include hq hK hcT hG hA hC1 hP1P hPc hPn hN1c in
theorem normalizer_eq_NN1 : Subgroup.normalizer (P : Set G) = NN1 S := by
  have hle := NN1_le_normalizer hPn (S := S)
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  obtain ⟨x, hx⟩ : (AA S).Nonempty := by rw [← Finset.card_pos, hA]; omega
  have hZ := zcen_eq_CC hq hK hcT hG hA hP1P hPc hPn
  have hinv : ∀ n ∈ Subgroup.normalizer (P : Set G), ∀ y ∈ AA S, n * y * n⁻¹ ∈ AA S := by
    intro n hn y hy
    have hyC : y ∈ zcen P := by rw [hZ]; exact AA_subset_CC hq hK hcT hG hA hy
    have h1 := conj_mem_zcen hn hyC
    rw [hZ] at h1
    refine mem_AA_of_mem_CC hq hK hcT hG hA h1 (fun h => (mem_AA.mp hy).2.1 ?_)
    have := congrArg (fun t => n⁻¹ * t * n) h
    simpa [mul_assoc] using this
  have htrans : ∀ y ∈ AA S, ∀ z ∈ AA S, ∃ n ∈ Subgroup.normalizer (P : Set G), n * y * n⁻¹ = z := by
    intro y hy z hz
    obtain ⟨w, hw, hwz⟩ := AA_transitive hq hK hcT hG hA hy hz
    exact ⟨w, hle (WW_le_normalizer_PP1 hq hcT hw), hwz⟩
  have hcard := card_eq_card_mul_centralizer _ _ hinv htrans hx
  rw [hA] at hcard
  have hcx := (centralizer_AA hq hK hcT hG hA hC1 hx).2
  have hstab : Nat.card (Subgroup.normalizer (P : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ q ^ 3 := by
    rw [← hcx]; exact Subgroup.card_le_of_le inf_le_right
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hN1c, hcard, mul_comm (q ^ 3)]
  exact Nat.mul_le_mul_left _ hstab

include hq hK hcT hG hA hC1 hP1P hPc hPn hN1c in
theorem card_normalizer : Nat.card (Subgroup.normalizer (P : Set G)) = q ^ 3 * (q - 1) := by
  rw [normalizer_eq_NN1 hq hK hcT hG hA hC1 hP1P hPc hPn hN1c, hN1c]

include hq hK hcT hG hA hC1 hP1P hPc hPn hN1c in
theorem conj_mem_PP1 {n x : G} (hn : n ∈ Subgroup.normalizer (P : Set G)) (hx : x ∈ PP1 S) :
    n * x * n⁻¹ ∈ PP1 S := by
  rw [normalizer_eq_NN1 hq hK hcT hG hA hC1 hP1P hPc hPn hN1c] at hn
  exact (Subgroup.mem_normalizer_iff.mp hn x).mp hx

include hq hK hcT hG hA hC1 hP1P hPc hPn hN1c in
theorem WW_le_normalizer : WW S ≤ Subgroup.normalizer (P : Set G) := by
  rw [normalizer_eq_NN1 hq hK hcT hG hA hC1 hP1P hPc hPn hN1c]
  exact WW_le_normalizer_PP1 hq hcT

omit [Fintype K] [DecidableEq K] [CharP K 3] in
include hq in
theorem coprime_q3 : Nat.Coprime (q ^ 3) (q - 1) := by
  have h3 : ¬ 3 ∣ q - 1 := by
    have : 3 ∣ q := hq ▸ dvd_pow_self 3 (by omega)
    have : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [show q ^ 3 = 3 ^ (3 * (2 * k + 1)) by rw [hq, ← pow_mul, mul_comm]]
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)

include hq hK hPc in
omit [CharP K 3] in
theorem inf_WW : P ⊓ WW S = ⊥ :=
  disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
    (by rw [hPc, card_WW hq hK]; exact coprime_q3 hq))

include hq hK hcT hG hA hC1 hP1P hPc hPn hN1c in
theorem sup_WW : P ⊔ WW S = Subgroup.normalizer (P : Set G) := by
  have hle : P ⊔ WW S ≤ Subgroup.normalizer (P : Set G) :=
    sup_le Subgroup.le_normalizer (WW_le_normalizer hq hK hcT hG hA hC1 hP1P hPc hPn hN1c)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_normalizer hq hK hcT hG hA hC1 hP1P hPc hPn hN1c]
  have h1 : Nat.card P ∣ Nat.card (P ⊔ WW S : Subgroup G) := Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card (WW S) ∣ Nat.card (P ⊔ WW S : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  rw [hPc] at h1
  rw [card_WW hq hK] at h2
  exact Nat.le_of_dvd Nat.card_pos ((coprime_q3 hq).mul_dvd_of_dvd_of_dvd h1 h2)

include hq hK hcT hP1P hPc in
theorem inf_centralizer_J : P ⊓ Subgroup.centralizer ({S.J} : Set G) = FF S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKq : Fintype.card K = 3 ^ (2 * k + 1) := hK.trans hq
  have hFle : FF S ≤ P ⊓ Subgroup.centralizer ({S.J} : Set G) := fun x hx =>
    ⟨hP1P (FF_le_PP1 hq hcT hx), Subgroup.mem_centralizer_singleton_iff.mpr (FF_comm_J hx)⟩
  refine le_antisymm ?_ hFle
  set H := P ⊓ Subgroup.centralizer ({S.J} : Set G) with hH
  have hHp : IsPGroup 3 H := (isPGroup_P hq hPc).to_le inf_le_left
  set H' := H.comap S.κ with hH'
  have hH'p : IsPGroup 3 H' := hHp.comap_of_injective S.κ S.κ_inj
  have hEH' : pslE K ≤ H' := fun y hy => by
    obtain ⟨c, rfl⟩ := mem_pslE_iff.mp hy
    exact hFle (mem_FF.mpr ⟨c, rfl⟩)
  obtain ⟨Q, hQ⟩ := hH'p.exists_le_sylow
  have hEQ : pslE K = Q := by
    refine Subgroup.eq_of_le_of_card_ge (hEH'.trans hQ) ?_
    have h1 := Sylow.card_eq_multiplicity Q
    have h2 := Sylow.card_eq_multiplicity (sylowE hKq)
    rw [coe_sylowE hKq] at h2
    rw [h1, h2]
  intro x hx
  have hxJ : x * S.J = S.J * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hodd : Odd (orderOf x) := by
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp hHp) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  obtain ⟨y, rfl⟩ := S.odd_mem_κ hxJ hodd
  have hyE : y ∈ pslE K := by rw [hEQ]; exact hQ hx
  obtain ⟨c, rfl⟩ := mem_pslE_iff.mp hyE
  exact mem_FF.mpr ⟨c, rfl⟩

include hq hK hPc in
omit [CharP K 3] in
theorem inf_centralizer_RR {r : G} (hr : r ∈ RR S) (hr1 : r ≠ 1) :
    P ⊓ Subgroup.centralizer ({r} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hxP, hxr⟩
  rw [Subgroup.mem_bot]
  have hxr' : x * r = r * x := Subgroup.mem_centralizer_singleton_iff.mp hxr
  have h3 := not_three_dvd_of_commute_RR hK hq hr hr1 hxr'
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hN
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hN; exact hN
  · exact absurd (hN ▸ dvd_pow_self 3 h0.ne') h3

omit [CharP K 3] in
theorem sq_mem_RR {w : G} (hw : w ∈ WW S) : w ^ 2 ∈ RR S := by
  obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hw)
  simp only
  rw [← pow_mul, wgen_pow, mul_comm i 2, pow_mul S.J 2 i, sq S.J, S.J_mul, one_pow, one_mul]
  exact mem_RR.mpr ⟨2 * i, by rw [map_pow]⟩

omit [CharP K 3] in
theorem mem_RR_of_mem_WW {w : G} (hw : w ∈ WW S) (hodd : Odd (orderOf w)) : w ∈ RR S := by
  obtain ⟨t, ht⟩ := hodd
  have h2 := sq_mem_RR hw
  have : w = (w ^ 2) ^ (t + 1) := by
    rw [← pow_mul, show 2 * (t + 1) = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact Subgroup.pow_mem _ h2 _

include hq hK in
omit [CharP K 3] in
theorem sq_ne_one_of_mem_WW {w : G} (hw : w ∈ WW S) (hw1 : w ≠ 1) (hwJ : w ≠ S.J) :
    w ^ 2 ≠ 1 := fun h => by
  rcases WW_sq_eq_one hq hK hw h with h' | h'
  · exact hw1 h'
  · exact hwJ h'

include hq hK hPc in
omit [CharP K 3] in
theorem inf_centralizer_WW {w : G} (hw : w ∈ WW S) (hw1 : w ≠ 1) (hwJ : w ≠ S.J) :
    P ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hxP, hxw⟩
  have hxw' : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hxw
  have hx2 : x ∈ P ⊓ Subgroup.centralizer ({w ^ 2} : Set G) := by
    refine ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [sq]
    calc x * (w * w) = (x * w) * w := by group
      _ = (w * x) * w := by rw [hxw']
      _ = w * (x * w) := by group
      _ = w * (w * x) := by rw [hxw']
      _ = w * w * x := by group
  rw [inf_centralizer_RR hq hK hPc (sq_mem_RR hw) (sq_ne_one_of_mem_WW hq hK hw hw1 hwJ)] at hx2
  exact hx2

end CFSG.Walter.WardLocal
