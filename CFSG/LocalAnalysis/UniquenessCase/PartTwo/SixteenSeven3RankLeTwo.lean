module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrCaseThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrCaseEleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_padic_le_two_of_le_four {n : ℕ} (hpos : 0 < n) (h4 : n ≤ 4) :
    padicValNat 2 n ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ padicValNat 2 n := not_le.1 h
  have hdvd : 2 ^ 3 ∣ n := (padicValNat_dvd_iff_le (p := 2) hpos.ne').mpr h3
  have h8 : 8 ≤ n := by simpa using Nat.le_of_dvd hpos hdvd
  omega

theorem s16c167_vtil_mul_self {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    ∀ x : Vtil ⊥ V hV, x * x = 1 := by
  intro x
  obtain ⟨y, rfl⟩ := mkTil_surjective ⊥ V hV x
  rw [← map_mul, ← sq, IntMod.sq_eq_one y, map_one]

theorem s16c167_card_le_four_of_le_normalizer_lbar {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) {X : Subgroup (MulAut W)}
    (hXn : X ≤ Subgroup.normalizer (L : Set (MulAut W))) (hX : IsElemAbelian2 X) :
    Nat.card X ≤ 4 := by
  classical
  haveI hExt : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥L
  let κ : ↥X →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hXn)
  have hκ_apply : ∀ (t : ↥X) (x : ↥L),
      ((κ t) x : MulAut W) = (t : MulAut W) * (x : MulAut W) * (t : MulAut W)⁻¹ := by
    intro t x
    simpa only [κ, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
      Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hXn t) x
  let ρ : ↥X →* MulAut ↥(Subgroup.center ↥L) :=
    (MulAut.characteristic (Subgroup.center ↥L)).comp κ
  have hρ_apply : ∀ (t : ↥X) (x : ↥(Subgroup.center ↥L)),
      (((ρ t) x : ↥(Subgroup.center ↥L)) : ↥L) = (κ t) (x : ↥L) := by
    intro t x
    simp only [ρ, MonoidHom.comp_apply, MulAut.characteristic_apply_apply_coe]
  have hdich : ∀ t : ↥X, ρ t = 1 ∨ ∀ x : ↥(Subgroup.center ↥L), (ρ t) x = x⁻¹ :=
    fun t => CFSG.GorensteinWalter.mulAut_eq_one_or_apply_eq_inv_of_card_eq_three hZcard (ρ t)
  have hmul : ∀ s t : ↥X, s ∉ ρ.ker → t ∉ ρ.ker → s * t ∈ ρ.ker := by
    intro s t hs ht
    rw [MonoidHom.mem_ker] at hs ht ⊢
    have hs' := (hdich s).resolve_left hs
    have ht' := (hdich t).resolve_left ht
    refine MulEquiv.ext fun x => ?_
    rw [map_mul, MulAut.mul_apply, ht' x, hs' x⁻¹, inv_inv]
    rfl
  have hindex : ρ.ker.index ≤ 2 := by
    by_cases htop : ρ.ker = ⊤
    · rw [htop, Subgroup.index_top]
      norm_num
    · obtain ⟨s, hs⟩ : ∃ s : ↥X, s ∉ ρ.ker := by
        by_contra h
        push Not at h
        exact htop (eq_top_iff.2 fun x _ => h x)
      refine le_of_eq (Subgroup.index_eq_two_iff.2 ⟨s, fun b => ?_⟩)
      by_cases hb : b ∈ ρ.ker
      · refine Or.inr ⟨hb, fun hbs => hs ?_⟩
        simpa using ρ.ker.mul_mem (ρ.ker.inv_mem hb) hbs
      · exact Or.inl ⟨hmul b s hb hs, hb⟩
  have hKcard : Nat.card ρ.ker ≤ 2 := by
    by_contra hK
    push Not at hK
    have hKp : IsPGroup 2 ↥ρ.ker := by
      intro x
      refine ⟨1, ?_⟩
      have h2 := hX.2 ((x : ↥X) : MulAut W) (x : ↥X).2
      have h2' : ((x : ↥X) : MulAut W) ^ 2 = 1 := h2
      apply Subtype.ext
      apply Subtype.ext
      simpa using h2'
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hKp
    have hn2 : 2 ≤ n := by
      by_contra h
      push Not at h
      have h2n : 2 ^ n ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    obtain ⟨EK, hEK⟩ := Sylow.exists_subgroup_card_pow_prime (p := 2) (n := 2) (G := ↥ρ.ker)
      (by rw [hn]; exact pow_dvd_pow 2 hn2)
    let E : Subgroup (MulAut W) := (EK.map ρ.ker.subtype).map X.subtype
    have hEX : E ≤ X := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    have hEcard : Nat.card E = 4 := by
      change Nat.card ((EK.map ρ.ker.subtype).map X.subtype) = 4
      rw [Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.card_map_of_injective ρ.ker.subtype_injective, hEK]
      norm_num
    have hEel : IsElemAbelian2 E :=
      ⟨fun a ha b hb => hX.1 a (hEX ha) b (hEX hb), fun a ha => hX.2 a (hEX ha)⟩
    obtain ⟨z, c, d, hzL, hz1, hzc, hcE, hdE, hc1, hcz, hdz⟩ :=
      s16c167_klein_pair hW hcard hL (hEX.trans hXn) hEel hEcard
    obtain ⟨y, hy, hyd⟩ := Subgroup.mem_map.1 hdE
    obtain ⟨k, -, hky⟩ := Subgroup.mem_map.1 hy
    have hkρ : ρ (k : ↥X) = 1 := k.2
    have hdk : d = ((k : ↥X) : MulAut W) := by
      rw [← hyd, ← hky]
      rfl
    have hzcen : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g.1 g.2)
    have hdz' : d * z = z * d := by
      have h1 : (ρ (k : ↥X)) ⟨⟨z, hzL⟩, hzcen⟩ = ⟨⟨z, hzL⟩, hzcen⟩ := by
        rw [hkρ]
        rfl
      have h2 := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : MulAut W)) h1
      simp only at h2
      rw [hρ_apply, hκ_apply] at h2
      rw [hdk]
      calc ((k : ↥X) : MulAut W) * z
          = (((k : ↥X) : MulAut W) * z * ((k : ↥X) : MulAut W)⁻¹) * ((k : ↥X) : MulAut W) := by
            group
        _ = z * ((k : ↥X) : MulAut W) := by rw [h2]
    have hz3 : z * z * z = 1 := by
      have h := congrArg Subtype.val (hL.2.2 ⟨z, hzL⟩)
      simpa [pow_succ, mul_assoc] using h
    have hzz : z = z⁻¹ := mul_right_cancel (hdz'.symm.trans hdz)
    have hz2 : z * z = 1 := by
      calc z * z = z * z⁻¹ := by rw [← hzz]
        _ = 1 := mul_inv_cancel z
    apply hz1
    calc z = z * z * z * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; simp
  calc Nat.card X = ρ.ker.index * Nat.card ρ.ker := (Subgroup.index_mul_card ρ.ker).symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hindex hKcard
    _ = 4 := by norm_num

theorem s16c167_rk_le_two_of_case168_3 (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h3 : Case168_3 D ⊥ V hV L)
    {X : Subgroup (MulAut (Vtil ⊥ V hV))} (hXM : X ≤ Mbar D.M ⊥ V hV)
    (hX : IsElemAbelian2 X) : rk ↥X ≤ 2 := by
  have hEn : X ≤ normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) :=
    hXM.trans (s16c167_mbar_le_normalizer_lbar D hV hc h3)
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := s16c167_vtil_mul_self hV
  have hWcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
    have hp : IsPGroup 2 (Vtil ⊥ V hV) := by
      intro x
      refine ⟨1, ?_⟩
      simpa [pow_two] using hWsq x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    unfold rk at h6
    rw [Subgroup.card_top, hn, padicValNat.prime_pow] at h6
    rw [hn, h6]
  have h4 := s16c167_card_le_four_of_le_normalizer_lbar hWsq hWcard h3.1 hEn hX
  rw [rk]
  exact s16c167_padic_le_two_of_le_four Nat.card_pos h4

theorem s16c167_rk_le_two_of_case168_11 (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h : Case168_11 D ⊥ V hV L)
    {X : Subgroup (MulAut (Vtil ⊥ V hV))} (hXM : X ≤ Mbar D.M ⊥ V hV)
    (hX : IsElemAbelian2 X) : rk ↥X ≤ 2 :=
  (s16c167_rk_le_one_of_case168_11 D hV hc h hXM hX).trans (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
