module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Fam
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

namespace AutM12Recog

theorem excl_psl_two_prime {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p) : Excl (StatedProj (StatedSL 2 K)) := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  refine excl_of_dihedral_sylow (fun Q => ?_) (fun n hn => ?_)
  · obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm Q
    obtain ⟨m, hm, ⟨d⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd Q'
    exact ⟨m, hm, ⟨ι.trans d⟩⟩
  · rw [card_mulAut_psl_two_prime K hp5 hK] at hn
    have hpos : 0 < Nat.card (StatedProj (StatedSL 2 K)) := Nat.card_pos
    have h2 : 2 ^ n ∣ 2 := by
      rw [mul_comm 2] at hn
      exact (Nat.mul_dvd_mul_iff_left hpos).mp hn
    exact (Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)

theorem excl_psl_two_sq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) : Excl (StatedProj (StatedSL 2 K)) := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp.out, hp.out.odd_of_ne_two hp2, by norm_num, hK⟩
  refine excl_of_dihedral_sylow (fun Q => ?_) (fun n hn => ?_)
  · obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm Q
    obtain ⟨m, hm, ⟨d⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd Q'
    exact ⟨m, hm, ⟨ι.trans d⟩⟩
  · rw [card_mulAut_psl_two_sq K hp2 hK] at hn
    have hpos : 0 < Nat.card (StatedProj (StatedSL 2 K)) := Nat.card_pos
    have h4 : 2 ^ n ∣ 4 := by
      rw [mul_comm 4] at hn
      exact (Nat.mul_dvd_mul_iff_left hpos).mp hn
    exact Nat.le_of_dvd (by norm_num) h4

theorem excl_psl_two_odd {S : Type} [Group S] [Finite S] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f = 1 ∨ f = 2) (h : StatedClassicalModel S .PSL 2 p f) : Excl S := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, -, hadm⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hX : Excl (StatedProj (StatedSL 2 K)) := by
    rcases hf with rfl | rfl
    · refine excl_psl_two_prime ?_ (by rw [hK, pow_one])
      have h3 : (2, p ^ 1) ≠ (2, 3) := hadm.2.2
      have hp1 := hp.two_le
      by_contra hlt
      have h34 : p = 3 ∨ p = 4 := by omega
      rcases h34 with h34 | h34
      · exact h3 (by rw [h34]; norm_num)
      · exact absurd hp (by rw [h34]; norm_num)
    · exact excl_psl_two_sq hp2 hK
  have : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv S e.toEquiv
  exact Excl.of_mulEquiv e hX

theorem card_le_sixteen_of_exp_two {T : Type} [Group T] (hT : TProps T) {Q : Type} [Group Q]
    (f : Q →* T) (hf : Function.Injective f) (hc : ∀ x y : Q, x * y = y * x)
    (hsq : ∀ x : Q, x ^ 2 = 1) : Nat.card Q ≤ 16 := by
  have hB : IsElemAbelian 2 (⊤ : Subgroup Q) :=
    ⟨⟨⟨fun a b => Subtype.ext (hc a b)⟩⟩, fun x _ => hsq x⟩
  have := hT.card_le_sixteen f hf ⊤ hB
  rwa [Subgroup.card_top] at this

theorem excl_psl_two_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSL 2 2 f) : Excl S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField S 2 2 f h
  have hf0 : f ≠ 0 := by omega
  by_cases hf5 : 5 ≤ f
  ·
    intro T _ _ hT Q n N hQN hcard hA
    obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv ε Q
    obtain ⟨hel, hQc⟩ := CFSG.Walter.psl2_even_sylow_two hf Q'
    let g := (embed (Q : Subgroup S) N hQN).comp ι.symm.toMonoidHom
    have hg : Function.Injective g := (embed_injective _ N hQN).comp ι.symm.injective
    have h16 := card_le_sixteen_of_exp_two hT g hg
      (fun x y => by
        have := hel.toIsMulCommutative.is_comm.comm x y
        exact this)
      (fun x => orderOf_dvd_iff_pow_eq_one.mp
        (dvd_trans (Monoid.order_dvd_exponent x) hel.exponent_dvd_p))
    rw [hQc] at h16
    have : 2 ^ 5 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf5
    omega
  ·
    have hf4 : f ≤ 4 := by omega
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
    · exact excl_of_outer_le (a := 2) ⟨15, by decide, by rw [hcardK]; norm_num⟩ (by norm_num)
        (by norm_num) hout.le
    · exact excl_of_outer_le (a := 3) ⟨63, by decide, by rw [hcardK]; norm_num⟩ (by norm_num)
        (by norm_num) hout.le
    · exact excl_of_outer_le (a := 4) ⟨255, by decide, by rw [hcardK]; norm_num⟩ (by norm_num)
        (by norm_num) hout.le

end AutM12Recog

end CFSG.Quasithin.F6
