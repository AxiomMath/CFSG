module

public import CFSG.Quasithin.H13.NQCatLieCartanTools
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan.F4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.LieType.Ree.LargeReeCover (torusPair torusPair_conj_pinnedX torusWeight
  torusWeight_apply torusExp0 torusExp1 f4i)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem torusConcl_f4
    {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    TorusConcl ↥(ReeTag.F4.reeGamma K a) False := by
  have : Fact (Nat.Prime ReeTag.F4.prime) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have hUC : ReeTag.F4.reeFixedPosUnipotent K a ≤ ReeTag.F4.reeGamma K a :=
    reeFixedPosUnipotent_le_reeGamma
  have hHC : ReeTag.F4.reeFixedTorus K a ≤ ReeTag.F4.reeGamma K a := inf_le_right
  have hU : IsSylowTwoOf (ReeTag.F4.reeFixedPosUnipotent K a) (ReeTag.F4.reeGamma K a) :=
    ⟨hUC, isPGroup_reeFixedPosUnipotent_subgroupOf.of_equiv (Subgroup.subgroupOfEquivOfLe hUC),
      not_dvd_index_reeFixedPosUnipotent⟩
  have hBN : ReeTag.F4.reeFixedBorel K a ≤
      Subgroup.normalizer (ReeTag.F4.reeFixedPosUnipotent K a : Set (ModGL ReeTag.F4.tag K)) := by
    rw [← reeGamma_inf_normalizer_reeFixedPosUnipotent]
    exact inf_le_right
  have hHeq : ReeTag.F4.reeFixedTorus K a = (torusPair (K := K) a).range := by
    refine le_antisymm (fun h hh => ?_) ?_
    · obtain ⟨u, v, huv⟩ := LargeReeInvolution.rankOne_exists_torusPair_eq hK hh
      exact ⟨(u, v), huv⟩
    · rintro _ ⟨⟨u, v⟩, rfl⟩
      exact LargeReeInvolution.rankOne_torusPair_mem_reeFixedTorus hK u v
  refine torusConcl_of_le hUC hHC hU (reeFixedTorus_le_reeFixedBorel.trans hBN) ?_ ?_
    (fun g hg g' hg' => reeFixedTorus_mul_comm hg hg') ?_
  · rw [reeGamma_inf_normalizer_reeFixedPosUnipotent, reeFixedBorel_eq_sup, sup_comm]
  ·
    rw [hHeq]
    have hdvd := Subgroup.card_range_dvd (torusPair (K := K) a)
    rw [Nat.card_prod, Nat.card_units, hK] at hdvd
    refine Odd.of_dvd_nat ?_ hdvd
    have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    have hodd : Odd (2 ^ (2 * a + 1) - 1) := Nat.odd_iff.2 (by omega)
    exact hodd.mul hodd
  intro E hEU hE hE16 hEC
  have hc : ∀ x : E, ∃ c : K, (x : ModGL ReeTag.F4.tag K) = LargeReeInvolution.centralZ K a c := by
    intro x
    have hx : (x : ModGL ReeTag.F4.tag K) ∈ ((Subgroup.center
        (ReeTag.F4.reeFixedPosUnipotent K a)).map (ReeTag.F4.reeFixedPosUnipotent K a).subtype :
          Set (ModGL ReeTag.F4.tag K)) := by
      refine ⟨⟨x, hEU x.2⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.1 (hEC x.2) g g.2
    rw [LargeReeInvolution.coe_center_eq_range_centralZ ha hK] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, hc.symm⟩
  choose β hβ using hc
  have hβinj : Function.Injective β := fun x y hxy => Subtype.ext (by rw [hβ x, hβ y, hxy])
  have h16 : 16 ≤ Nat.card K := by
    rw [← hE16]
    exact Nat.card_le_card_of_injective β hβinj
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE16]; norm_num)
    exact exists_ne 1
  have hc₀ : β x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply Subtype.ext
    rw [hβ x₀, h0, LargeReeInvolution.centralZ_zero, Subgroup.coe_one]
  have hfix : ∀ u v : Kˣ, torusPair a (u, v) ∈
      Subgroup.centralizer (E : Set (ModGL ReeTag.F4.tag K)) → (u : K) ^ 2 ^ a = 1 := by
    intro u v huv
    have h1 := Subgroup.mem_centralizer_iff.1 huv (x₀ : ModGL ReeTag.F4.tag K) x₀.2
    rw [hβ x₀] at h1
    have h2 : torusPair a (u, v) * LargeReeInvolution.centralZ K a (β x₀) *
        (torusPair a (u, v))⁻¹ = LargeReeInvolution.centralZ K a (β x₀) := by
      rw [← h1]
      group
    rw [LargeReeInvolution.torusPair_conj_centralZ hK] at h2
    exact (mul_left_eq_self₀.1 (LargeReeInvolution.centralZ_injective h2)).resolve_right hc₀
  have hroot : ∀ (u : K), u ^ 2 ^ a = 1 → u = 1 := by
    intro u hu
    have h1 : (u - 1) ^ 2 ^ a = 0 := by
      rw [sub_pow_char_pow (p := 2), hu, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h1)
  refine ⟨lt_of_lt_of_le ?_ (card_le_relIndex_of_hom
    ((torusPair (K := K) a).comp (MonoidHom.inl Kˣ Kˣ)) (fun u => by
      rw [hHeq]
      exact ⟨_, rfl⟩) fun u hu => Units.ext (hroot _ (hfix u 1 hu))), fun h0 => ?_⟩
  · rw [Nat.card_units]
    omega
  ·
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    have hmem : torusPair a (1, g) ∈ ReeTag.F4.reeFixedTorus K a ⊓
        Subgroup.centralizer (E : Set (ModGL ReeTag.F4.tag K)) := by
      refine ⟨LargeReeInvolution.rankOne_torusPair_mem_reeFixedTorus hK 1 g,
        Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      rw [show w = LargeReeInvolution.centralZ K a (β ⟨w, hw⟩) from hβ ⟨w, hw⟩]
      have h1 := LargeReeInvolution.torusPair_conj_centralZ hK 1 g (β ⟨w, hw⟩)
      rw [Units.val_one, one_pow, one_mul] at h1
      calc LargeReeInvolution.centralZ K a (β ⟨w, hw⟩) * torusPair a (1, g) =
          (torusPair a (1, g) * LargeReeInvolution.centralZ K a (β ⟨w, hw⟩) *
            (torusPair a (1, g))⁻¹) * torusPair a (1, g) := by rw [h1]
        _ = torusPair a (1, g) * LargeReeInvolution.centralZ K a (β ⟨w, hw⟩) := by group
    rw [h0, Subgroup.mem_bot] at hmem
    have hα : IsRoot ReeTag.F4.tag (Pi.single (f4i 2) 1) := isRoot_single _ _
    have h1 := torusPair_conj_pinnedX a (1, g) hα (1 : K)
    rw [hmem, one_mul, inv_one, mul_one, mul_one] at h1
    have h2 := pinnedX_injective ReeTag.F4.tag K _ h1
    have hE : torusExp1 (2 ^ a) (Pi.single (f4i 2) 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        2 * 2 ^ a - 1 := by
      simp only [torusExp1]
      rw [show ReeTag.F4.cartanPair (f4i 1) (Pi.single (f4i 2) 1) = -1 by decide,
        show ReeTag.F4.cartanPair (f4i 2) (Pi.single (f4i 2) 1) = 2 by decide]
      ring
    have h3 : g ^ (2 * (2 : ℤ) ^ a - 1) = 1 := by
      rw [torusWeight_apply, one_zpow, one_mul, hE] at h2
      exact Units.ext (by simpa using h2.symm)
    rw [← orderOf_dvd_iff_zpow_eq_one, hg, Nat.card_units, hK,
      Nat.cast_sub Nat.one_le_two_pow] at h3
    have hpos : 0 < 2 * (2 : ℤ) ^ a - 1 := by
      have : (1 : ℤ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
      linarith
    have hlt : 2 * (2 : ℤ) ^ a - 1 < ((2 ^ (2 * a + 1) : ℕ) : ℤ) - 1 := by
      push_cast
      have : (2 : ℤ) ^ a < 2 ^ (2 * a) := pow_lt_pow_right₀ (by norm_num) (by omega)
      rw [pow_succ]
      linarith
    exact absurd (Int.le_of_dvd hpos h3) (not_le.2 (by push_cast at hlt ⊢; linarith))

end CFSG.Quasithin.H13.NQCat.LieCartan.F4
