module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Tab
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank

namespace AutM12Recog

section Data

variable {K : Type} [Group K] {T : Type} [Group T]

noncomputable def embed (Q : Subgroup K) (N : Subgroup T) (hQN : Nonempty (↥Q ≃* ↥N)) :
    ↥Q →* T :=
  N.subtype.comp hQN.some.toMonoidHom

theorem embed_injective (Q : Subgroup K) (N : Subgroup T) (hQN : Nonempty (↥Q ≃* ↥N)) :
    Function.Injective (embed Q N hQN) :=
  N.subtype_injective.comp hQN.some.injective

theorem card_mul_two_pow (hT : TProps T) (Q : Subgroup K) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥Q ≃* ↥N)) (hc : Nat.card T = Nat.card N * 2 ^ n) :
    Nat.card Q * 2 ^ n = 2 ^ 7 := by
  rw [← hT.card, hc, Nat.card_congr hQN.some.toEquiv]

end Data

theorem Excl.of_equiv {K' : Type} [Group K'] [Finite K'] (h : Excl K') {K : Type} [Group K]
    [Finite K] (e : K ≃* K') : Excl K :=
  Excl.of_mulEquiv e h

theorem excl_of_hasTwoE16 {S : Type} [Group S] [Finite S]
    (h : ∀ Q : Sylow 2 S, HasTwoE16 ↥(Q : Subgroup S)) : Excl S := by
  intro T _ _ hT Q n N hQN hcard hA
  exact hT.not_hasTwoE16 (embed (Q : Subgroup S) N hQN) (embed_injective _ N hQN) (h Q)

theorem excl_of_aut_le {K : Type} [Group K] [Finite K] {a c : ℕ}
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ a * m) (ha : a ≤ 7) (hc : c < 2 ^ (7 - a))
    (hAut : ∀ n : ℕ, Nat.card K * 2 ^ n ∣ Nat.card (MulAut K) → 2 ^ n ≤ c) : Excl K := by
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨m, hm, hK⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(Q : Subgroup K) = 2 ^ (Nat.card K).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : (Nat.card K).factorization 2 = a := by
    rw [hK, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hm.not_two_dvd_nat)]
    simp
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hcard
  rw [h1, h2, ← pow_add] at h3
  have h4 : a + n = 7 := Nat.pow_right_injective le_rfl h3
  have h5 : n = 7 - a := by omega
  have h6 : 2 ^ n ≤ c := hAut n hA
  rw [h5] at h6
  omega

theorem excl_of_outer_le {K : Type} [Group K] [Finite K] {a c : ℕ}
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ a * m) (ha : a ≤ 7) (hc : c < 2 ^ (7 - a))
    (hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ≤ c) : Excl K := by
  refine excl_of_aut_le hK ha hc fun n h => ?_
  have : Finite (MulAut K) := inferInstance
  have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
    Nat.card_pos
  exact (Nat.le_of_dvd hpos (dvd_card_outer_of_dvd_card_mulAut h)).trans hOut

theorem excl_alternating {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) : Excl (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hc : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card]
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (alternatingGroup (Fin n))) ≤ 4 := by
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl
    · exact (Nat.le_of_dvd (by norm_num)
        (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (Or.inl rfl)).2).trans
        (by norm_num)
    · exact CFSG.Sporadic.SchreierLemmas.outer_alternating_six.1
    · exact (Nat.le_of_dvd (by norm_num)
        (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (Or.inr le_rfl)).2).trans
        (by norm_num)
  rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl
  · exact excl_of_outer_le (a := 2) ⟨15, by decide, by rw [hc]; decide⟩ (by norm_num)
      (by norm_num) hout
  · exact excl_of_outer_le (a := 3) ⟨45, by decide, by rw [hc]; decide⟩ (by norm_num)
      (by norm_num) hout
  · exact excl_of_outer_le (a := 3) ⟨315, by decide, by rw [hc]; decide⟩ (by norm_num)
      (by norm_num) hout

theorem excl_of_dihedral_sylow {K : Type} [Group K] [Finite K]
    (hD : ∀ Q : Sylow 2 K, ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(Q : Subgroup K) ≃* DihedralGroup (2 ^ m)))
    (hAut : ∀ n : ℕ, Nat.card K * 2 ^ n ∣ Nat.card (MulAut K) → 2 ^ n ≤ 4) : Excl K := by
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨m, hm1, ⟨θ⟩⟩ := hD Q
  have hn := hAut n hA
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hcard
  have hQc : Nat.card ↥(Q : Subgroup K) = 2 ^ (m + 1) := by
    rw [Nat.card_congr θ.toEquiv, DihedralGroup.nat_card]
    ring
  by_cases hm4 : 4 ≤ m
  ·
    set g : ↥(Q : Subgroup K) := θ.symm (DihedralGroup.r 1) with hg
    have hord : orderOf g = 2 ^ m := by
      rw [hg, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have h8 : g ^ 8 = 1 := hT.pow_eight_eq_one (embed _ N hQN) (embed_injective _ N hQN) g
    have := orderOf_dvd_of_pow_eq_one h8
    rw [hord] at this
    have h16 : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
    have := Nat.le_of_dvd (by norm_num) this
    omega
  ·
    have hm3 : m + 1 ≤ 4 := by omega
    have h16 : 2 ^ (m + 1) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hm3
    rw [hQc] at h3
    have : 2 ^ (m + 1) * 2 ^ n ≤ 2 ^ 4 * 4 := Nat.mul_le_mul h16 hn
    omega

theorem TProps.exists_elemAbelian_eight {T : Type} [Group T] [Finite T] (hT : TProps T)
    (N : Subgroup T)
    (hN : Nat.card T = Nat.card N * 2) :
    ∃ E : Subgroup T, E ≤ N ∧ IsElemAbelian 2 E ∧ 8 ≤ Nat.card E := by
  obtain ⟨B, hB, hc⟩ := hT.hasE16
  have hindex : N.index = 2 := by
    have h := N.card_mul_index
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [hN] at h
    exact (Nat.mul_left_cancel hpos h).symm ▸ rfl
  have : N.Normal := Subgroup.normal_of_index_eq_two hindex
  refine ⟨N ⊓ B, inf_le_left, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨x, hxN, hxB⟩ ⟨y, hyN, hyB⟩
    apply Subtype.ext
    show x * y = y * x
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hxB⟩ ⟨y, hyB⟩)
  · intro x hx
    exact hB.2 x hx.2
  · have h1 : N.relIndex B * Nat.card (N ⊓ B :) = Nat.card B :=
      Subgroup.relIndex_mul_card N B
    have h2 : N.relIndex B ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N B
    rw [hindex] at h2
    have h3 : N.relIndex B ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    rw [hc] at h1
    have h4 : 0 < Nat.card (N ⊓ B :) := Nat.card_pos
    nlinarith

theorem exists_elemAbelian_of_embed {K T : Type} [Group K] [Group T] (Q : Subgroup K)
    (f : ↥Q →* T) (hf : Function.Injective f) {E : Subgroup T} (hE : E ≤ f.range)
    (hEa : IsElemAbelian 2 E) :
    ∃ E' : Subgroup K, E' ≤ Q ∧ IsElemAbelian 2 E' ∧ Nat.card E' = Nat.card E := by
  refine ⟨(E.comap f).map Q.subtype, Subgroup.map_subtype_le _, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show (a : K) * b = b * a
    have h := hEa.1.is_comm.comm ⟨f a, ha⟩ ⟨f b, hb⟩
    have h' : f (a * b) = f (b * a) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h
    exact congrArg Subtype.val (hf h')
  · rintro _ ⟨a, ha, rfl⟩
    have h := hEa.2 (f a) ha
    have h' : f (a ^ 2) = f 1 := by rw [map_pow, map_one]; exact h
    have := hf h'
    show (a : K) ^ 2 = 1
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    have h1 : (E.comap f).map f = E := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hE
    have h2 := Subgroup.card_map_of_injective hf (K := E.comap f)
    rw [h1] at h2
    exact h2.symm

theorem excl_of_rank_le_four {K : Type} [Group K] [Finite K]
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ 6 * m)
    (hr : ∀ (Q : Sylow 2 K) (E : Subgroup K), E ≤ Q → IsElemAbelian 2 E → Nat.card E ≤ 4) :
    Excl K := by
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨m, hm, hK⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(Q : Subgroup K) = 2 ^ (Nat.card K).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : (Nat.card K).factorization 2 = 6 := by
    rw [hK, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hm.not_two_dvd_nat)]
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hcard
  rw [h1, h2] at h3
  have hn : n = 1 := by
    have h4 : 2 ^ 6 * 2 ^ n = 2 ^ 7 := h3
    rw [← pow_add] at h4
    have := Nat.pow_right_injective le_rfl h4
    omega
  have hNc : Nat.card T = Nat.card N * 2 := by rw [hcard, hn, pow_one]
  obtain ⟨E, hEN, hEa, hE8⟩ := hT.exists_elemAbelian_eight N hNc
  have hrange : (embed (Q : Subgroup K) N hQN).range = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (hQN.some y).2
    · intro hx
      exact ⟨hQN.some.symm ⟨x, hx⟩, by simp [embed]⟩
  obtain ⟨E', hE'Q, hE'a, hE'c⟩ := exists_elemAbelian_of_embed (Q : Subgroup K)
    (embed (Q : Subgroup K) N hQN) (embed_injective _ N hQN) (hEN.trans hrange.ge) hEa
  have := hr Q E' hE'Q hE'a
  omega

end AutM12Recog

end CFSG.Quasithin.F6
