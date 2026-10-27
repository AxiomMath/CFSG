module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowCore
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter AutM12Recog

namespace M12Sylow

theorem psl2_dihedral {K : Type} [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K))
    (Q : Sylow 2 (StatedProj (StatedSL 2 K))) :
    ∃ m : ℕ, 1 ≤ m ∧
      Nonempty (↥(Q : Subgroup (StatedProj (StatedSL 2 K))) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm Q
  obtain ⟨m, hm, ⟨d⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd Q'
  exact ⟨m, hm, ⟨ι.trans d⟩⟩

theorem dihedral_data64 {K : Type} [Group K] [Finite K]
    (hD : ∀ Q : Sylow 2 K,
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(Q : Subgroup K) ≃* DihedralGroup (2 ^ m)))
    {T : Type} [Group T] (hT : TProps64 T) (Q : Sylow 2 K) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥(Q : Subgroup K) ≃* ↥N)) (hcard : Nat.card T = Nat.card N * 2 ^ n) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 3 ∧ Nat.card ↥(Q : Subgroup K) = 2 ^ (m + 1) ∧ m + 1 + n = 6 := by
  obtain ⟨m, hm1, ⟨θ⟩⟩ := hD Q
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hcard
  have hQc : Nat.card ↥(Q : Subgroup K) = 2 ^ (m + 1) := by
    rw [Nat.card_congr θ.toEquiv, DihedralGroup.nat_card]
    ring
  have hmn : m + 1 + n = 6 := by
    rw [hQc, ← pow_add] at h3
    exact Nat.pow_right_injective le_rfl h3
  refine ⟨m, hm1, ?_, hQc, hmn⟩
  by_contra hm4
  have hm4' : 4 ≤ m := by omega
  set g : ↥(Q : Subgroup K) := θ.symm (DihedralGroup.r 1) with hg
  have hord : orderOf g = 2 ^ m := by
    rw [hg, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have h8 : g ^ 8 = 1 := by
    have := hT.exp (embed (Q : Subgroup K) N hQN g)
    rw [← map_pow] at this
    exact embed_injective _ N hQN (by rw [this, map_one])
  have h1 := orderOf_dvd_of_pow_eq_one h8
  rw [hord] at h1
  have h16 : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4'
  have h2 := Nat.le_of_dvd (by norm_num) h1
  omega

theorem excl64_psl_two_prime {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p) : Excl64 (StatedProj (StatedSL 2 K)) := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨m, -, hm3, -, hmn⟩ := dihedral_data64 (psl2_dihedral hodd) hT Q n N hQN hcard
  rw [card_mulAut_psl_two_prime K hp5 hK] at hA
  have hpos : 0 < Nat.card (StatedProj (StatedSL 2 K)) := Nat.card_pos
  have h2 : 2 ^ n ∣ 2 := by
    rw [mul_comm 2] at hA
    exact (Nat.mul_dvd_mul_iff_left hpos).mp hA
  have hn : 2 ^ n ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have hn1 : n ≤ 1 := by
    by_contra hlt
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

theorem l2sq_data64 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) {T : Type} [Group T] (hT : TProps64 T)
    (Q : Sylow 2 (StatedProj (StatedSL 2 K))) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥(Q : Subgroup (StatedProj (StatedSL 2 K))) ≃* ↥N))
    (hcard : Nat.card T = Nat.card N * 2 ^ n)
    (hA : Nat.card (StatedProj (StatedSL 2 K)) * 2 ^ n ∣
      Nat.card (MulAut (StatedProj (StatedSL 2 K)))) :
    n = 2 ∧ Nat.card ↥(Q : Subgroup (StatedProj (StatedSL 2 K))) = 16 := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp.out, hp.out.odd_of_ne_two hp2, by norm_num, hK⟩
  obtain ⟨m, -, hm3, hQc, hmn⟩ := dihedral_data64 (psl2_dihedral hodd) hT Q n N hQN hcard
  rw [card_mulAut_psl_two_sq K hp2 hK] at hA
  have hpos : 0 < Nat.card (StatedProj (StatedSL 2 K)) := Nat.card_pos
  have h4 : 2 ^ n ∣ 4 := by
    rw [mul_comm 4] at hA
    exact (Nat.mul_dvd_mul_iff_left hpos).mp hA
  have hn : 2 ^ n ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm : m = 3 := by omega
  have hn' : n = 2 := by omega
  refine ⟨hn', ?_⟩
  rw [hQc, hm]
  norm_num

theorem excl64_psl_two_odd_prime {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSL 2 p 1) : Excl64 S := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, -, hadm⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hp5 : 5 ≤ p := by
    have h3 : (2, p ^ 1) ≠ (2, 3) := hadm.2.2
    have hp1 := hp.two_le
    by_contra hlt
    have h34 : p = 3 ∨ p = 4 := by omega
    rcases h34 with h34 | h34
    · exact h3 (by rw [h34]; norm_num)
    · exact absurd hp (by rw [h34]; norm_num)
  have hX : Excl64 (StatedProj (StatedSL 2 K)) := excl64_psl_two_prime hp5 (by rw [hK, pow_one])
  have : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv S e.toEquiv
  exact Excl64.of_equiv hX e

theorem l2sq_data64_of_model {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSL 2 p 2) {T : Type} [Group T]
    (hT : TProps64 T) (Q : Sylow 2 S) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥(Q : Subgroup S) ≃* ↥N)) (hcard : Nat.card T = Nat.card N * 2 ^ n)
    (hA : Nat.card S * 2 ^ n ∣ Nat.card (MulAut S)) :
    n = 2 ∧ Nat.card ↥(Q : Subgroup S) = 16 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv S e.toEquiv
  obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv e Q
  have hA' : Nat.card (StatedProj (StatedSL 2 K)) * 2 ^ n ∣
      Nat.card (MulAut (StatedProj (StatedSL 2 K))) := by
    rwa [← Nat.card_congr e.toEquiv, ← Nat.card_congr (MulAut.congr e).toEquiv]
  obtain ⟨hn, hQ'⟩ := l2sq_data64 hp2 hK hT Q' n N ⟨ι.symm.trans hQN.some⟩ hcard hA'
  exact ⟨hn, by rw [Nat.card_congr ι.toEquiv, hQ']⟩

theorem card_le_eight_of_exp_two {T : Type} [Group T] (hT : TProps64 T) {Q : Type} [Group Q]
    (f : Q →* T) (hf : Function.Injective f) (hc : ∀ x y : Q, x * y = y * x)
    (hsq : ∀ x : Q, x ^ 2 = 1) : Nat.card Q ≤ 8 := by
  have hB : IsElemAbelian 2 (⊤ : Subgroup Q) :=
    ⟨⟨⟨fun a b => Subtype.ext (hc a b)⟩⟩, fun x _ => hsq x⟩
  have h1 := hT.rank ((⊤ : Subgroup Q).map f) (isElemAbelian_map _ hB)
  rwa [Subgroup.card_map_of_injective hf, Subgroup.card_top] at h1

theorem excl64_psl_two_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSL 2 2 f) : Excl64 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField S 2 2 f h
  have hf0 : f ≠ 0 := by omega
  by_cases hf4 : 4 ≤ f
  ·
    intro T _ _ hT Q n N hQN hcard hA
    obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv ε Q
    obtain ⟨hel, hQc⟩ := CFSG.Walter.psl2_even_sylow_two hf Q'
    let g := (embed (Q : Subgroup S) N hQN).comp ι.symm.toMonoidHom
    have hg : Function.Injective g := (embed_injective _ N hQN).comp ι.symm.injective
    have h8 := card_le_eight_of_exp_two hT g hg
      (fun x y => by
        have := hel.toIsMulCommutative.is_comm.comm x y
        exact this)
      (fun x => orderOf_dvd_iff_pow_eq_one.mp
        (dvd_trans (Monoid.order_dvd_exponent x) hel.exponent_dvd_p))
    rw [hQc] at h8
    have : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    omega
  ·
    have hf3 : f ≤ 3 := by omega
    have hcardK : Nat.card S = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr ε.toEquiv]
      exact CFSG.Walter.psl2_even_card hf0
    have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = f := by
      let e1 : S ≃* CFSG.RankThree.PartOne.KCRootAxis.SL₂ (GaloisField 2 f) :=
        ε.trans (CFSG.RankThree.PartOne.KCRootAxis.slEquivPSL _).symm
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e1).toEquiv]
      exact CFSG.RankThree.PartOne.KCRootAxis.natCard_out_sl2 (by omega)
        (GaloisField.card 2 f hf0)
    interval_cases f
    · exact excl64_of_outer_le (a := 2) ⟨15, by decide, by rw [hcardK]; norm_num⟩ (by norm_num)
        (by norm_num) hout.le
    · exact excl64_of_outer_le (a := 3) ⟨63, by decide, by rw [hcardK]; norm_num⟩ (by norm_num)
        (by norm_num) hout.le

end M12Sylow

end CFSG.Quasithin.F6
