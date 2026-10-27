module

public import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen
public import CFSG.Quasithin.Vol2.Ch1Sec3A5Trace
public import CFSG.Quasithin.Background.DicksonPerfectPSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG.Quasithin.L139A5

open CFSG.GorensteinWalter CFSG.Quasithin.Dickson

variable {p : ℕ} [hp : Fact p.Prime]

theorem isOddPrimePower_card_zmod (hp2 : p ≠ 2) : IsOddPrimePower (Nat.card (ZMod p)) :=
  ⟨p, 1, hp.out, hp.out.odd_of_ne_two hp2, le_rfl, by rw [Nat.card_zmod, pow_one]⟩

theorem p_dvd_card_psl2 (hp2 : p ≠ 2) : p ∣ Nat.card (PSL2 (ZMod p)) := by
  have hc := psl2_card_formula (ZMod p) (isOddPrimePower_card_zmod hp2)
  rw [Nat.card_zmod] at hc
  have h2 : 2 ∣ p ^ 2 - 1 :=
    even_iff_two_dvd.mp (Nat.Odd.sub_odd (hp.out.odd_of_ne_two hp2).pow odd_one)
  rw [hc, Nat.mul_div_assoc _ h2]
  exact dvd_mul_right p _

theorem eq_bot_of_psl2 {X : Type*} [Group X] [Finite X]
    (hp5 : 5 < p) (ι : X ≃* PSL2 (ZMod p)) {A N : Subgroup X} [(N.subgroupOf A).Normal]
    (hNA : N ≤ A) (hN2 : IsPGroup 2 N)
    (eA : (↥A ⧸ N.subgroupOf A) ≃* alternatingGroup (Fin 5)) : N = ⊥ := by
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card A = 60 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A),
      Nat.card_congr eA.toEquiv, card_alt_five,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv]
  have hAι : Nat.card (A.map ι.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective ι.injective
  rcases dickson_prime_cases hp2 (A.map ι.toMonoidHom) with hs | htop | ⟨⟨e5⟩, -⟩
  · exfalso
    have hAs : Group.IsSolvable A :=
      Group.isSolvable_of_isSolvable_injective
        (f := (A.equivMapOfInjective ι.toMonoidHom ι.injective).toMonoidHom) (MulEquiv.injective _)
    exact not_isSolvable_alt_five
      (Group.isSolvable_of_isSolvable_injective (f := eA.symm.toMonoidHom) eA.symm.injective)
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    have hpA : p ∣ Nat.card A := by
      rw [← hAι, htop, Subgroup.card_top]
      exact p_dvd_card_psl2 hp2
    rw [hcard, hk] at hpA
    rcases (Nat.Prime.dvd_mul hp.out).mp hpA with h | h
    · have h60 : p ∣ 2 ^ 2 * 3 * 5 := by norm_num; exact h
      rcases (Nat.Prime.dvd_mul hp.out).mp h60 with h' | h'
      · rcases (Nat.Prime.dvd_mul hp.out).mp h' with h'' | h''
        · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h'')
          omega
        · have := Nat.le_of_dvd (by norm_num) h''
          omega
      · have := Nat.le_of_dvd (by norm_num) h'
        omega
    · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h)
      omega
  · have h60 : Nat.card A = 60 := by rw [← hAι, Nat.card_congr e5.toEquiv, card_alt_five]
    exact Subgroup.eq_bot_of_card_eq N (by omega)

theorem psl2_aut_ne_sq (hp5 : 5 < p) (γ : MulAut (PSL2 (ZMod p))) {u : PSL2 (ZMod p)}
    (hu1 : u ≠ 1) (hu5 : u ^ 5 = 1) : γ u ≠ u ^ 2 := by
  intro hγ
  have hK := isOddPrimePower_card_zmod (p := p) (by omega)
  have hcard : 3 < Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  have hKcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod p) hKcard hK hcard γ
  have hr : x.right = 1 := Subsingleton.elim _ _
  rw [← SemidirectProduct.inl_left_mul_inr_right x, hr, map_one, mul_one,
    pGammaL2ToMulAutPSL2_inl] at hx
  have h1 := toPGL_pgl2InnerAutPSL2_apply (ZMod p) hK hcard x.left u
  rw [hx, hγ, map_pow] at h1
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_five).mp h'
    omega
  refine false_of_conj_eq_sq h5 (u := Matrix.ProjectiveSpecialLinearGroup.toPGL u) (h := x.left)
    ?_ ?_ h1.symm
  · rw [← map_pow, hu5, map_one]
  · intro h
    apply hu1
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [h, map_one]

theorem a5SecInner_of_equiv_psl2 {X : Type*} [Group X] [Finite X]
    (hp5 : 5 < p) (ι : X ≃* PSL2 (ZMod p)) : A5SecInner X := by
  intro A N _ hNA hN2 hA5 β hβA hβN
  obtain ⟨eA⟩ := hA5
  obtain rfl := eq_bot_of_psl2 hp5 ι hNA hN2 eA
  refine exists_inner_sec eA hNA (mem_stb_of_maps hβA hβN) ?_
  intro γ _ a _ ha1 ha5 hc
  rw [Subgroup.mem_bot] at ha1 ha5 hc
  have hu1 : ι a ≠ 1 := by rwa [Ne, MulEquiv.map_eq_one_iff]
  have hu5 : ι a ^ 5 = 1 := by rw [← map_pow, ha5, map_one]
  apply psl2_aut_ne_sq hp5 (ι.symm.trans (γ.trans ι)) hu1 hu5
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [inv_mul_eq_one.mp hc, map_pow]

end CFSG.Quasithin.L139A5
