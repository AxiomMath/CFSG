module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Cross
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Three
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Def
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Val4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2

public section

namespace CFSG.Quasithin.A312U3

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

theorem QuatPair.of_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {c d : G} (h : QuatPair (f c) (f d)) : QuatPair c d := by
  obtain ⟨h4, h2, hd, hcd⟩ := h
  refine ⟨hf (by rw [map_pow, map_one]; exact h4), fun e => h2 (by rw [← map_pow, e, map_one]),
    hf (by rw [map_pow, map_pow]; exact hd),
    hf (by rw [map_mul, map_mul, map_inv, map_inv]; exact hcd)⟩

theorem su3_not_psl2_nine {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)}
    {H : Subgroup (GL (Fin 3) K)} (h : QCtx p K M H) {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 9) (e : H ⧸ Subgroup.center H ≃* StatedProj (StatedSL 2 K')) :
    False := by
  have hp2 : p ≠ 2 := by omega
  have h5 : (5 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_five (by omega)
  have hodd : IsOddPrimePower (Nat.card K') :=
    ⟨3, 2, Nat.prime_three, by decide, by norm_num, by rw [hK']; norm_num⟩
  have hcard : 3 < Nat.card K' := by rw [hK']; norm_num
  obtain ⟨c, d, hcd⟩ := exists_quaternion_pair hp2 hK M h.odd
  have hpair := quatPair_qAct hK h hcd
  have hq : QuatPair (MulAut.congr (toPSL2 e) (qAct h c)) (MulAut.congr (toPSL2 e) (qAct h d)) :=
    hpair.map (MulAut.congr (toPSL2 e)).toMonoidHom (MulAut.congr (toPSL2 e)).injective
  have hinn : ∀ g : ↥M, ∃ A : PGL2 K', pgl2InnerAutPSL2 K' hodd hcard A =
      MulAut.congr (toPSL2 e) (qAct h g) := fun g =>
    valentiner_inner h5 h.det h.center hK' hodd hcard e
      (g := ((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K))
      (fun x hx => h.norm _ ⟨g, g.2, rfl⟩ x hx) (qAct h g) (qAct_apply_mk h g)
  obtain ⟨Ac, hAc⟩ := hinn c
  obtain ⟨Ad, hAd⟩ := hinn d
  rw [← hAc, ← hAd] at hq
  exact no_quatPair_pgl2 _ _
    (QuatPair.of_map (pgl2InnerAutPSL2 K' hodd hcard)
      (pgl2InnerAutPSL2_injective K' hodd hcard) hq)

theorem su3NoPSL2_holds : SU3NoPSL2 := by
  intro p hpf hp7 K _ _ hK M H h r f hr hr2 hf hadm K' _ _ hK' e
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hq3 : r ^ f ≠ 3 := fun h3 => hadm.2.2.2.2 (by rw [h3])
  by_cases hrp : r = p
  · subst hrp
    have hf1 := su3_psl2_defining_f hp2 hK h hf hK' e
    subst hf1
    rw [pow_one] at hK'
    exact su3_not_psl2_prime hp2 hK h hr (by omega) hK' e
  · by_cases hr3 : r = 3
    · subst hr3
      have h3 : (3 : K) ≠ 0 := by
        exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_three hrp
      have := linear_two_three_f h3 h.scalar h.det h.center hf hq3 hK' e
      rw [this.1] at hK'
      exact su3_not_psl2_nine hp7 hK h (by simpa using hK') e
    · have hrK : (r : K) ≠ 0 := natCast_ne_zero_of_card_sq hK hr hrp
      have hf1 := linear_two_cross_f h.det h.center hr hr2 hr3 hrK hf hK' e
      subst hf1
      rw [pow_one] at hK'
      exact su3_not_psl2_prime hp2 hK h hr (hr.five_le_of_ne_two_of_ne_three hr2 hr3) hK' e

end CFSG.Quasithin.A312U3
