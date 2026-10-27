module

public import CFSG.Walter.ReeOrder.WardLocal.Hall
public import CFSG.Walter.ReeOrder.WardLocal.Main

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ti_of_centralizer {M : Subgroup G}
    (hcen : ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) (g : G) :
    M ⊓ (MulAut.conj g • M) = ⊥ ∨ M ⊓ (MulAut.conj g • M) = M := by
  by_cases h : M ⊓ (MulAut.conj g • M) = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  obtain ⟨hxM, hxg⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conj_smul_iff] at hxg
  have hy1 : g⁻¹ * x * g ≠ 1 := fun h' => hx1' (by
    have := congrArg (fun t => g * t * g⁻¹) h'
    simpa [mul_assoc] using this)
  have h1 := hcen x hxM hx1'
  have h2 := hcen _ hxg hy1
  have key : ∀ z, z ∈ M ↔ g⁻¹ * z * g ∈ M := fun z => by
    conv_lhs => rw [← h1]
    conv_rhs => rw [← h2]
    exact mem_centralizer_conj
  have heq : MulAut.conj g • M = M := by
    ext z
    rw [mem_conj_smul_iff, ← key]
  rw [heq, inf_idem]

theorem exists_sylow_le {p : ℕ} [hp : Fact p.Prime] (H : Subgroup G)
    (hH : p ^ (Nat.card G).factorization p ∣ Nat.card H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H := by
  let P : Sylow p H := default
  let P' : Subgroup G := (P : Subgroup H).map H.subtype
  have hP'card : Nat.card P' = p ^ (Nat.card G).factorization p := by
    have h1 : Nat.card P' = Nat.card P := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
    rw [h1, P.card_eq_multiplicity]
    have hle : (Nat.card H).factorization p ≤ (Nat.card G).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card H) p
    have hge : (Nat.card G).factorization p ≤ (Nat.card H).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp.out Nat.card_pos.ne').mp hH
    rw [le_antisymm hle hge]
  refine ⟨Sylow.ofCard P' hP'card, ?_⟩
  rw [Sylow.coe_ofCard]
  exact Subgroup.map_subtype_le _

theorem normalizer_eq_of_sylow {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hcen : ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) (Q : Sylow p G)
    (hQM : (Q : Subgroup G) ≤ M) (hQ1 : (Q : Subgroup G) ≠ ⊥) :
    Subgroup.normalizer ((Q : Subgroup G) : Set G) = Subgroup.normalizer (M : Set G) := by
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQ1
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  apply le_antisymm
  · intro g hg
    apply mem_normalizer_of_conj_mem
    intro y hy
    have hgx : g * x₀ * g⁻¹ ∈ (Q : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hg x₀).mp hx₀
    have hgx1 : g * x₀ * g⁻¹ ≠ 1 := fun h => hx₀1' (by
      have := congrArg (fun t => g⁻¹ * t * g) h
      simpa [mul_assoc] using this)
    rw [← hcen _ (hQM hgx) hgx1, Subgroup.mem_centralizer_singleton_iff]
    have hyx : y * x₀ = x₀ * y := hcomm y hy x₀ (hQM hx₀)
    calc g * y * g⁻¹ * (g * x₀ * g⁻¹) = g * (y * x₀) * g⁻¹ := by group
      _ = g * (x₀ * y) * g⁻¹ := by rw [hyx]
      _ = g * x₀ * g⁻¹ * (g * y * g⁻¹) := by group
  · intro g hg
    apply mem_normalizer_of_conj_mem
    intro y hy
    have hgy : g * y * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hg y).mp (hQM hy)
    have hyp : IsPGroup p (Subgroup.zpowers (g * y * g⁻¹)) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨y, hy⟩
      rw [Subgroup.orderOf_mk] at hn
      apply IsPGroup.of_card (n := n)
      rw [Nat.card_zpowers, show g * y * g⁻¹ = MulAut.conj g y from rfl, MulEquiv.orderOf_eq, hn]
    have hle : Subgroup.zpowers (g * y * g⁻¹) ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      apply mem_normalizer_of_conj_mem
      intro z hz
      rw [hcomm _ hgy z (hQM hz), mul_inv_cancel_right]
      exact hz
    have hsup := hyp.to_sup_of_normal_right' Q.isPGroup' hle
    have heq := Q.is_maximal' hsup le_sup_right
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

end General

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

include B hq hK hG hP1P hPc hPn hN1c in
theorem exists_minus (hm : q = 3 * m ^ 2) :
    ∃ M : Subgroup G, Nat.card M = q + 1 - 3 * m ∧ (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) ∧
      ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M := by
  have hq27 : 27 ≤ q := S.q_ge
  have hm3 : 3 ≤ m := by nlinarith
  have ha1 : q + 1 - 3 * m ≠ 1 := by
    have : 3 * m + 3 ≤ q + 1 := by rw [hm]; nlinarith
    omega
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  have : Fact p.Prime := ⟨hp⟩
  have hpG : p ∣ Nat.card G := by rw [card_G_hall hq hG hm]; exact Dvd.dvd.mul_right hpa _
  obtain ⟨V, hV⟩ := exists_prime_orderOf_dvd_card' p hpG
  have hp2 := (prime_minus hq hm hp hpa).2.2.2.2
  have hVodd : Odd (orderOf V) := by rw [hV]; exact hp.odd_of_ne_two hp2
  obtain ⟨hc, hcomm⟩ := B.centralizer_minus hq hK hG hP1P hPc hPn hN1c hm hVodd hp hpa
    (by rw [hV])
  refine ⟨Subgroup.centralizer ({V} : Set G), hc, hcomm, fun x hx hx1 => ?_⟩
  have hdvd : orderOf x ∣ q + 1 - 3 * m := hc ▸ Subgroup.orderOf_dvd_natCard _ hx
  have hx1' : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p', hp', hp'x⟩ := Nat.exists_prime_and_dvd hx1'
  have hodd : Odd (orderOf x) := by
    have hoddn : Odd (q + 1 - 3 * m) := by
      have := (hall_coprime hm (m_odd hq hm)).2.2.2.1
      rw [Nat.coprime_two_right] at this
      exact Nat.Odd.of_mul_left this
    exact Odd.of_dvd_nat hoddn hdvd
  obtain ⟨hcx, -⟩ := B.centralizer_minus hq hK hG hP1P hPc hPn hN1c hm hodd hp' (hp'x.trans hdvd)
    hp'x
  have hle : Subgroup.centralizer ({V} : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy x hx)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcx, hc])).symm

include B hq hK hG hP1P hPc hPn hN1c in
theorem exists_plus (hm : q = 3 * m ^ 2) :
    ∃ M : Subgroup G, Nat.card M = q + 1 + 3 * m ∧ (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) ∧
      ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M := by
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd (show q + 1 + 3 * m ≠ 1 by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hpG : p ∣ Nat.card G := by
    rw [card_G_hall hq hG hm]; exact Dvd.dvd.mul_left (dvd_mul_of_dvd_right hpb _) _
  obtain ⟨V, hV⟩ := exists_prime_orderOf_dvd_card' p hpG
  have hp2 := (prime_plus hq hm hp hpb).2.2.2.2
  have hVodd : Odd (orderOf V) := by rw [hV]; exact hp.odd_of_ne_two hp2
  obtain ⟨hc, hcomm⟩ := B.centralizer_plus hq hK hG hP1P hPc hPn hN1c hm hVodd hp hpb
    (by rw [hV])
  refine ⟨Subgroup.centralizer ({V} : Set G), hc, hcomm, fun x hx hx1 => ?_⟩
  have hdvd : orderOf x ∣ q + 1 + 3 * m := hc ▸ Subgroup.orderOf_dvd_natCard _ hx
  have hx1' : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p', hp', hp'x⟩ := Nat.exists_prime_and_dvd hx1'
  have hodd : Odd (orderOf x) := by
    have hoddn : Odd (q + 1 + 3 * m) := by
      have := (hall_coprime hm (m_odd hq hm)).2.2.2.1
      rw [Nat.coprime_two_right] at this
      exact Nat.Odd.of_mul_right this
    exact Odd.of_dvd_nat hoddn hdvd
  obtain ⟨hcx, -⟩ := B.centralizer_plus hq hK hG hP1P hPc hPn hN1c hm hodd hp' (hp'x.trans hdvd)
    hp'x
  have hle : Subgroup.centralizer ({V} : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy x hx)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcx, hc])).symm

omit [Fintype G] [CharP K 3] in
include hq hG in
theorem coprime_index_minus (hm : q = 3 * m ^ 2) {M : Subgroup G}
    (hMc : Nat.card M = q + 1 - 3 * m) : Nat.Coprime (Nat.card M) M.index ∧
      M.index = q ^ 3 * (q - 1) * (q + 1) * (q + 1 + 3 * m) := by
  have h := M.card_mul_index
  rw [hMc, card_G_hall hq hG hm] at h
  have hlt : 3 * m < q + 1 := by
    have hm1 : 1 ≤ m := by rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
    rw [hm]; nlinarith
  have hidx := Nat.eq_of_mul_eq_mul_left (by omega) h
  refine ⟨?_, hidx⟩
  rw [hMc, hidx]
  obtain ⟨c1, c2, c3, -, c5, -⟩ := hall_coprime hm (m_odd hq hm)
  have hdvd : q + 1 - 3 * m ∣ (q + 1 - 3 * m) * (q + 1 + 3 * m) := dvd_mul_right _ _
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right
    (Nat.Coprime.pow_right 3 (Nat.Coprime.coprime_dvd_left hdvd c1))
    (Nat.Coprime.coprime_dvd_left hdvd c2)) (Nat.Coprime.coprime_dvd_left hdvd c3)) c5

omit [Fintype G] [CharP K 3] in
include hq hG in
theorem coprime_index_plus (hm : q = 3 * m ^ 2) {M : Subgroup G}
    (hMc : Nat.card M = q + 1 + 3 * m) : Nat.Coprime (Nat.card M) M.index ∧
      M.index = q ^ 3 * (q - 1) * (q + 1) * (q + 1 - 3 * m) := by
  have h := M.card_mul_index
  have hcard : Nat.card G = (q + 1 + 3 * m) * (q ^ 3 * (q - 1) * (q + 1) * (q + 1 - 3 * m)) := by
    rw [card_G_hall hq hG hm]; ring
  rw [hMc, hcard] at h
  have hidx := Nat.eq_of_mul_eq_mul_left (by omega) h
  refine ⟨?_, hidx⟩
  rw [hMc, hidx]
  obtain ⟨c1, c2, c3, -, c5, -⟩ := hall_coprime hm (m_odd hq hm)
  have hdvd : q + 1 + 3 * m ∣ (q + 1 - 3 * m) * (q + 1 + 3 * m) := dvd_mul_left _ _
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right
    (Nat.Coprime.pow_right 3 (Nat.Coprime.coprime_dvd_left hdvd c1))
    (Nat.Coprime.coprime_dvd_left hdvd c2)) (Nat.Coprime.coprime_dvd_left hdvd c3)) c5.symm

omit [CharP K 3] in
theorem exists_pow_orderOf_eq {x : G} {p : ℕ} (hp : p.Prime) (hpx : p ∣ orderOf x) :
    orderOf (x ^ (orderOf x / p)) = p := by
  have ho : orderOf x ≠ 0 := (orderOf_pos x).ne'
  rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos x) hpx) hp.pos).ne'
    (Nat.div_dvd_of_dvd hpx), Nat.div_div_self hpx ho]

omit [CharP K 3] in
include hq hG in
theorem exists_conj_mem_of_hall {M : Subgroup G} (hm : q = 3 * m ^ 2) {n : ℕ}
    (hn : n = q + 1 - 3 * m ∨ n = q + 1 + 3 * m) (hMc : Nat.card M = n)
    (hcen : ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) {x : G} {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hpx : p ∣ orderOf x) : ∃ g : G, g⁻¹ * x * g ∈ M := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ : ∃ y, y = x ^ (orderOf x / p) := ⟨_, rfl⟩
  have hyo : orderOf y = p := by rw [hy]; exact exists_pow_orderOf_eq hp hpx
  have hH : p ^ (Nat.card G).factorization p ∣ Nat.card M := by
    rw [hMc]
    rcases hn with rfl | rfl
    · exact ppart_minus hq hG hm hp hpn
    · exact ppart_plus hq hG hm hp hpn
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hyo, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_full M hH hyp
  have hg1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    have : y = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  refine ⟨g, ?_⟩
  rw [← hcen _ hg hg1, Subgroup.mem_centralizer_singleton_iff]
  have hxy : x * y = y * x := by rw [hy]; exact (Commute.self_pow x _).eq
  calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
    _ = g⁻¹ * (y * x) * g := by rw [hxy]
    _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group

omit [CharP K 3] in
include hq in
theorem seven_le_of_dvd (hm : q = 3 * m ^ 2) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ q + 1 - 3 * m ∨ p ∣ q + 1 + 3 * m) : 7 ≤ p := by
  have hpq : ¬ p ∣ q ∧ p ≠ 2 := by
    rcases hpN with h | h
    · obtain ⟨h1, -, -, -, h5⟩ := prime_minus hq hm hp h; exact ⟨h1, h5⟩
    · obtain ⟨h1, -, -, -, h5⟩ := prime_plus hq hm hp h; exact ⟨h1, h5⟩
  have hN : p ∣ q ^ 2 - q + 1 := by
    rw [hall_mul hm]
    rcases hpN with h | h
    · exact dvd_mul_of_dvd_right h _
    · exact dvd_mul_of_dvd_left h _
  have h3 : p ≠ 3 := by
    rintro rfl; exact hpq.1 (hq ▸ dvd_pow_self 3 (by omega))
  have h5 : p ≠ 5 := by
    rintro rfl
    have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    have h0 : ((q ^ 2 - q + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hN
    push_cast [hq2] at h0
    have hq5 : (q : ZMod 5) = 3 * (-1) ^ k := by
      rw [hq, pow_succ, pow_mul]; push_cast
      rw [show (9 : ZMod 5) = -1 by decide]; ring
    rw [hq5] at h0
    rcases neg_one_pow_eq_or (ZMod 5) k with h | h <;> rw [h] at h0 <;> revert h0 <;> decide
  have h2 := hp.two_le
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | omega | exact absurd hp (by decide)

omit [CharP K 3] in
include hq hG in
theorem relIndex_mod {M : Subgroup G} (hm : q = 3 * m ^ 2) {n : ℕ}
    (hn : n = q + 1 - 3 * m ∨ n = q + 1 + 3 * m) (hMc : Nat.card M = n)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hcen : ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) : ((M.relIndex (Subgroup.normalizer (M : Set G)) : ℕ) : ZMod p) = 6 := by
  have : Fact p.Prime := ⟨hp⟩
  have hH : p ^ (Nat.card G).factorization p ∣ Nat.card M := by
    rw [hMc]
    rcases hn with rfl | rfl
    · exact ppart_minus hq hG hm hp hpn
    · exact ppart_plus hq hG hm hp hpn
  obtain ⟨Q, hQM⟩ := exists_sylow_le M hH
  have hpG : p ∣ Nat.card G := by
    rw [card_G_hall hq hG hm]
    rcases hn with rfl | rfl
    · exact Dvd.dvd.mul_right hpn _
    · exact Dvd.dvd.mul_left (dvd_mul_of_dvd_right hpn _) _
  have hQ1 : (Q : Subgroup G) ≠ ⊥ := by
    intro h
    have hc := Q.card_eq_multiplicity
    rw [h, Subgroup.card_bot] at hc
    have hv : 0 < (Nat.card G).factorization p :=
      hp.factorization_pos_of_dvd Nat.card_pos.ne' hpG
    have : 1 < p ^ (Nat.card G).factorization p := Nat.one_lt_pow hv.ne' hp.one_lt
    omega
  have hN := normalizer_eq_of_sylow hcomm hcen Q hQM hQ1
  have hsyl := card_sylow_modEq_one p G
  have hN' : Subgroup.normalizer (Q : Set G) = Subgroup.normalizer (M : Set G) := hN
  rw [Sylow.card_eq_index_normalizer Q, hN'] at hsyl
  have hidx : M.relIndex (Subgroup.normalizer (M : Set G)) *
      (Subgroup.normalizer (M : Set G)).index = M.index :=
    Subgroup.relIndex_mul_index Subgroup.le_normalizer
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hle := hall_le hm
  have hN0 : ((q ^ 2 - q + 1 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff, hall_mul hm]
    rcases hn with rfl | rfl
    · exact dvd_mul_of_dvd_right hpn _
    · exact dvd_mul_of_dvd_left hpn _
  push_cast [hq2] at hN0
  have hI : ((Subgroup.normalizer (M : Set G)).index : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' _ 1 p).mpr hsyl
    rwa [Nat.cast_one] at this
  have hcast := congrArg (fun t : ℕ => (t : ZMod p)) hidx
  simp only [Nat.cast_mul, hI, mul_one] at hcast
  rw [hcast]
  rcases hn with rfl | rfl
  · rw [(coprime_index_minus hq hG hm hMc).2]
    have hB : ((q + 1 - 3 * m : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpn
    push_cast [hle, hq1] at hB ⊢
    linear_combination ((q : ZMod p) ^ 3 * ((q : ZMod p) - 1) * ((q : ZMod p) + 1)) * (-hB) +
      (2 * (q : ZMod p) ^ 4 + 4 * (q : ZMod p) ^ 3 - 6 * q - 6) * hN0
  · rw [(coprime_index_plus hq hG hm hMc).2]
    have hB : ((q + 1 + 3 * m : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpn
    push_cast [hle, hq1] at hB ⊢
    linear_combination ((q : ZMod p) ^ 3 * ((q : ZMod p) - 1) * ((q : ZMod p) + 1)) * (-hB) +
      (2 * (q : ZMod p) ^ 4 + 4 * (q : ZMod p) ^ 3 - 6 * q - 6) * hN0

omit [CharP K 3] in
include hq hG in
theorem six_le_relIndex {M : Subgroup G} (hm : q = 3 * m ^ 2) {n : ℕ}
    (hn : n = q + 1 - 3 * m ∨ n = q + 1 + 3 * m) (hMc : Nat.card M = n)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hcen : ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) (hn1 : n ≠ 1) :
    6 ≤ M.relIndex (Subgroup.normalizer (M : Set G)) := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  have h6 := relIndex_mod hq hG hm hn hMc hcomm hcen hp hpn
  have h7 : 7 ≤ p := seven_le_of_dvd hq hm hp (by rcases hn with rfl | rfl <;> simp_all)
  have h := (ZMod.natCast_eq_natCast_iff' _ 6 p).mp (by rw [h6]; push_cast; ring)
  rw [Nat.mod_eq_of_lt (show 6 < p by omega)] at h
  have := Nat.mod_le (M.relIndex (Subgroup.normalizer (M : Set G))) p
  omega

end Block

end CFSG.Walter.WardLocal
