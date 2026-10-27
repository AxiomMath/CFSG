module

public import CFSG.Quasithin.Vol2.Ch11SecJDick3
public import CFSG.Quasithin.Vol2.Ch11SecJFacts
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.Quasithin.Vol2.Ch11SecJDick2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open Matrix
open scoped Matrix

theorem odd_card_sub_one {F : Type*} [Field F] [Finite F] [CharP F 2] :
    Odd (Nat.card F - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩) odd_one

theorem factDicksonGL2_holds : FactDicksonGL2 := by
  intro F _ _ _ Y g h10 hdiag hnorm hcop
  classical
  by_contra hY
  obtain ⟨p, hp, hpY, hpodd⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card Y ∧ Odd p := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card Y) with ⟨k, hk⟩ | h
    · exact absurd (IsPGroup.of_card hk) hY
    · exact h
  have hpq : Nat.Coprime p (Nat.card F - 1) := Nat.Coprime.coprime_dvd_left hpY hcop
  obtain ⟨r, e, m, hr, hrq, hord, h10', hd'⟩ := exists_pow_prime_power h10 hdiag
  have hrY : ¬ r ∣ Nat.card Y := fun h =>
    hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop h hrq)
  have hrodd : Odd r := Odd.of_dvd_nat odd_card_sub_one hrq
  have hgN : g ^ m ∈ Subgroup.normalizer (Y : Set (GL (Fin 2) F)) := by
    have hmap : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
      rintro _ ⟨y, hy, rfl⟩
      exact hnorm y hy
    have hcard : Nat.card ↥(Y.map (MulAut.conj g).toMonoidHom) = Nat.card Y :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hg := Subgroup.mem_normalizer_iff_map_conj_eq.2
      (Subgroup.eq_of_le_of_card_ge hmap hcard.ge)
    exact Subgroup.pow_mem _ hg m
  have hQN : Subgroup.zpowers (g ^ m) ≤ Subgroup.normalizer (Y : Set (GL (Fin 2) F)) :=
    (Subgroup.zpowers_le).2 hgN
  have hQr : IsPGroup r ↥(Subgroup.zpowers (g ^ m)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hord])
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨P, hP⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime r p
    hQr hrY (Y.normalizerMonoidHom.comp (Subgroup.inclusion hQN))
  have hPp : IsPGroup p ↥(P : Subgroup ↥Y) := P.isPGroup'
  have : Nontrivial ↥(P : Subgroup ↥Y) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (P.ne_bot_of_dvd_card hpY)
  have hZ : Nontrivial (Subgroup.center ↥(P : Subgroup ↥Y)) := hPp.center_nontrivial
  have hdvd : p ∣ Nat.card (Subgroup.center ↥(P : Subgroup ↥Y)) := by
    rcases (hPp.to_subgroup _).card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card (α := ↥(Subgroup.center ↥(P : Subgroup ↥Y)))).ne'
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set y : GL (Fin 2) F := (((z : ↥(P : Subgroup ↥Y)) : ↥Y) : GL (Fin 2) F) with hydef
  have hyord : orderOf y = p := by
    simp only [hydef, Subgroup.orderOf_coe, hz]
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    exact hp.one_lt.ne' hyord.symm
  have hya : IsAniso y := fun a b hab =>
    det_ne_zero_of_orderOf hy1 (hyord ▸ hpodd) (hyord ▸ hpq) hab
  have hy' : (g ^ m) * y * (g ^ m)⁻¹ * y = y * ((g ^ m) * y * (g ^ m)⁻¹) := by
    have hmem : (Y.normalizerMonoidHom ⟨g ^ m, hgN⟩) (z : ↥(P : Subgroup ↥Y)) ∈
        (P : Subgroup ↥Y) := by
      have h1 := hP ⟨g ^ m, Subgroup.mem_zpowers _⟩
      have h2 : (Y.normalizerMonoidHom ⟨g ^ m, hgN⟩) (z : ↥(P : Subgroup ↥Y)) ∈
          (P : Subgroup ↥Y).map ((Y.normalizerMonoidHom.comp (Subgroup.inclusion hQN))
            ⟨g ^ m, Subgroup.mem_zpowers _⟩).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (z : ↥(P : Subgroup ↥Y)).2
      rwa [h1] at h2
    have hcomm := Subgroup.mem_center_iff.1 z.2 ⟨_, hmem⟩
    have h2 := congrArg (fun w : ↥(P : Subgroup ↥Y) => ((w : ↥Y) : GL (Fin 2) F)) hcomm
    simpa only [Subgroup.coe_mul, Subgroup.normalizerMonoidHom_apply_apply_coe] using h2
  have hodd' : Odd (orderOf (g ^ m)) := hord ▸ hrodd.pow
  exact hya.not_commute_upper h10' hd' (commute_of_conj_commute hya hodd' hy')

end CFSG.Quasithin.Vol2.Ch11.SecJ
