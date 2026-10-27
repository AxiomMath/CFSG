module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Long
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Seven
public import CFSG.Quasithin.Background.SmithB45TorD4W
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.Quasithin.Background.SmithB42D4Main
import CFSG.Quasithin.Background.SmithB42D4Weyl
import CFSG.Quasithin.Background.FixVLattice
import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Quasithin.B42D4 CFSG.Quasithin.B45Tor
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Open CFSG.Timmesfeld.ExceptionalOrders
open scoped Pointwise

section Perp

variable {V : Type*} [CommGroup V]

theorem conj_mem_perpSub {g y m : MulAut V} (hm : m ∈ perpSub y) :
    g * m * g⁻¹ ∈ perpSub (g * y * g⁻¹) := by
  rw [mem_perpSub]
  intro v
  obtain ⟨h1, h2⟩ := mem_perpSub.1 hm (g⁻¹ v)
  have e : ∀ w : V, g w * v⁻¹ = g (w * (g⁻¹ v)⁻¹) := fun w => by
    rw [map_mul, map_inv, MulAut.apply_inv_self]
  simp only [MulAut.mul_apply]
  rw [e, e, MulAut.inv_apply_self, MulAut.inv_apply_self, h1, h2]
  exact ⟨rfl, rfl⟩

variable [Finite V]

theorem eq_one_of_mem_perpSub_of_mem_zpowers (hV : ∀ v : V, v ^ 2 = 1) {s t : MulAut V}
    (hs : Odd (orderOf s)) (ht : t ∈ perpSub s) (hts : t ∈ Subgroup.zpowers s) : t = 1 := by
  have hmul := index_fixV_mul_of_mem_perpSub hV hs ht
  have hle : (fixV (Subgroup.zpowers (s * t))).index ≤ (fixV (Subgroup.zpowers s)).index := by
    refine Subgroup.index_antitone fun v hv => mem_fixV.2 fun x hx => ?_
    exact mem_fixV.1 hv x (Subgroup.zpowers_le.2 (mul_mem (Subgroup.mem_zpowers s) hts) hx)
  have hpos : 0 < (fixV (Subgroup.zpowers s)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hone : (fixV (Subgroup.zpowers t)).index = 1 := by
    have h1 : (fixV (Subgroup.zpowers t)).index ≤ 1 := by
      rw [hmul] at hle
      exact Nat.le_of_mul_le_mul_left (by rw [mul_one]; exact hle) hpos
    exact le_antisymm h1 (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  exact eq_one_of_fixV_eq_top (Subgroup.index_eq_one.1 hone)

end Perp

theorem factorization_ordTrialityD4_two_seven : (ordTrialityD4 (2 ^ 1)).factorization 7 = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ (by norm_num),
    show ordTrialityD4 (2 ^ 1) = (2 ^ 12 * 3 ^ 4 * 13) * 7 ^ 2 by norm_num [ordTrialityD4],
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num), zero_add]

section LongTwo

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 1))

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "kk" => trialityFixedField K σ.toRingHom

include hK hσ in
theorem two_pow_six_le_index_long_two {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (φ : ↥L ≃* ↥C₀) {y : ↥L}
    (hy : ConjC σ ((φ y : C₀) : ModGL TwistTag.D4.tag K) (Xr d4H 1)) :
    2 ^ (6 * 1) ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index := by
  classical
  refine two_pow_six_mul_le_index_of_long σ φ hy fun ψ hψ hlong => ?_
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : Nat.card ↥C₀ = ordTrialityD4 (2 ^ 1) :=
    card_graphFixedRootGroup_D4_two le_rfl hK σ.toRingHom hσ
  have : Finite ↥C₀ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num [ordTrialityD4])
  have hψconj : ∀ g x : ↥C₀, (fixV (Subgroup.zpowers (ψ (g * x * g⁻¹)))).index =
      (fixV (Subgroup.zpowers (ψ x))).index := fun g x => by
    rw [map_mul, map_mul, map_inv, FixVLat.index_fixV_zpowers_conj]
  have hidx1 : ∀ x : ↥C₀, (fixV (Subgroup.zpowers (ψ x))).index = 1 → x = 1 := fun x h =>
    hψ (by rw [eq_one_of_fixV_eq_top (Subgroup.index_eq_one.1 h), map_one])
  have hodd : ∀ x : ↥C₀, x ^ 7 = 1 → Odd (orderOf (ψ x)) := fun x hx => by
    rw [orderOf_injective ψ hψ]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx)
  have hHmem : Xr d4H 1 ∈ C₀ := Xr_H_mem_C0 σ hσ3 (map_one σ)
  have hnW0 : nW0 K * Xr d4H 1 * (nW0 K)⁻¹ = Xr (-d4H) 1 := by
    rw [nW0_conj (by decide +kernel), w0_neg (by simp)]
  have hnHmem : Xr (-d4H) 1 ∈ C₀ := by
    rw [← hnW0]
    exact mul_mem (mul_mem (nW0_mem σ) hHmem) (inv_mem (nW0_mem σ))
  set yH : ↥C₀ := ⟨Xr d4H 1, hHmem⟩ with hyHdef
  set ynH : ↥C₀ := ⟨Xr (-d4H) 1, hnHmem⟩ with hynHdef
  have hyH : ConjC σ (yH : ModGL TwistTag.D4.tag K) (Xr d4H 1) :=
    ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩
  have hynH : ConjC σ (ynH : ModGL TwistTag.D4.tag K) (Xr d4H 1) :=
    ⟨(nW0 K)⁻¹, inv_mem (nW0_mem σ), by
      show (nW0 K)⁻¹ * Xr (-d4H) 1 * (nW0 K)⁻¹⁻¹ = Xr d4H 1
      rw [← hnW0]
      group⟩
  set R0 := orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ with hR0
  set M : Subgroup (MulAut V) := (R0.range.subgroupOf C₀).map ψ with hMdef
  have hcommH : ∀ g ∈ R0.range, Commute (yH : ModGL TwistTag.D4.tag K) g := fun g hg =>
    commute_of_mem_orbitRankOneHom_zero σ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 1 hg
  have hcommnH : ∀ g ∈ R0.range, Commute (ynH : ModGL TwistTag.D4.tag K) g := fun g hg =>
    commute_of_mem_orbitRankOneHom_zero σ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 1 hg
  have hMH : M ≤ perpSub (ψ yH) :=
    map_orbitRankOneHom_le_perpSub hK σ hσ le_rfl hV ψ hψ hlong hyH hcommH
  have hMnH : M ≤ perpSub (ψ ynH) :=
    map_orbitRankOneHom_le_perpSub hK σ hσ le_rfl hV ψ hψ hlong hynH hcommnH
  have hcardK : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]; norm_num
  obtain ⟨a, ha1⟩ : ∃ a : Kˣ, a ≠ 1 := by
    have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcardK]; norm_num)
    exact exists_ne 1
  set z : ↥C₀ := ⟨trialityTorusHom σ (a, 1), torus_mem σ hσ3 _⟩ with hzdef
  have hzR0 : (z : ModGL TwistTag.D4.tag K) ∈ R0.range := by
    show trialityTorusHom σ (a, 1) ∈ R0.range
    rw [trialityTorusHom_eq_orbitH hσ3' a 1]
    have e : trialityMiddleParam (σ := σ) 1 = 1 := Units.ext rfl
    rw [e, orbitH_one', mul_one, ← orbitRankOneHom_HSL]
    exact ⟨_, rfl⟩
  have hzM : ψ z ∈ M := ⟨z, Subgroup.mem_subgroupOf.2 hzR0, rfl⟩
  have hz1 : z ≠ 1 := by
    intro h
    have hT : trialityTorusHom σ (a, 1) = trialityTorusHom σ 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    exact ha1 (congrArg Prod.fst (trialityTorusHom_injective hT))
  have hz7 : z ^ 7 = 1 := by
    refine Subtype.ext ?_
    show trialityTorusHom σ (a, 1) ^ 7 = 1
    rw [← map_pow, Prod.pow_mk, one_pow, ← hcardK, pow_card_eq_one']
    exact map_one _
  have hzord : orderOf z = 7 := orderOf_eq_prime hz7 hz1
  have hkk : ∀ u : kkˣ, u = 1 := by
    have hcardk : Nat.card kkˣ = 1 := by
      rw [Nat.card_units, card_fixedField le_rfl hK σ hσ]
      norm_num
    have : Subsingleton kkˣ := (Nat.card_eq_one_iff_unique.1 hcardk).1
    exact fun u => Subsingleton.elim u 1
  set nb : ↥C₀ := ⟨nB K, nB_mem σ⟩ with hnbdef
  set g₁ : ↥C₀ := ⟨nB K * nA K, mul_mem (nB_mem σ) (nA_mem σ)⟩ with hg₁def
  have hBz : nb * z * nb⁻¹ = z := by
    refine Subtype.ext ?_
    show nB K * trialityTorusHom σ (a, 1) * (nB K)⁻¹ = trialityTorusHom σ (a, 1)
    rw [nB_conj_trialityTorusHom hσ3', hkk (trialityNorm σ hσ3' a * 1⁻¹)]
  have hg₁z : g₁ * z * g₁⁻¹ = z⁻¹ := by
    refine Subtype.ext ?_
    show nB K * nA K * trialityTorusHom σ (a, 1) * (nB K * nA K)⁻¹ = (trialityTorusHom σ (a, 1))⁻¹
    have e : nB K * nA K * trialityTorusHom σ (a, 1) * (nB K * nA K)⁻¹ =
        nB K * (nA K * trialityTorusHom σ (a, 1) * (nA K)⁻¹) * (nB K)⁻¹ := by group
    rw [e, nA_conj_trialityTorusHom, map_one, mul_one, nB_conj_trialityTorusHom hσ3',
      hkk (trialityNorm σ hσ3' a⁻¹ * 1⁻¹), ← map_inv, Prod.inv_mk, inv_one]
  have key : ∀ (g x₀ w : ↥C₀), ψ w ∈ perpSub (ψ x₀) → Commute w x₀ → g * z * g⁻¹ = w →
      ψ (g⁻¹ * x₀ * g) ∈ perpSub (ψ z) ∧ Commute z (g⁻¹ * x₀ * g) := by
    intro g x₀ w hw hc hgz
    have hz : z = g⁻¹ * w * g := by rw [← hgz]; group
    refine ⟨mem_perpSub_comm.1 ?_, ?_⟩
    · have h := conj_mem_perpSub (g := (ψ g)⁻¹) hw
      rw [hz, map_mul, map_mul, map_mul, map_mul, map_inv]
      simpa only [inv_inv] using h
    · have h := hc.map (MulAut.conj g⁻¹)
      simp only [MulAut.conj_apply, inv_inv] at h
      rw [hz]
      exact h
  have hzH : Commute z yH :=
    (Commute.symm (hcommH _ hzR0) : Commute (z : ModGL TwistTag.D4.tag K) yH) |> fun h =>
      Subtype.ext h.eq
  have hznH : Commute z ynH :=
    (Commute.symm (hcommnH _ hzR0) : Commute (z : ModGL TwistTag.D4.tag K) ynH) |> fun h =>
      Subtype.ext h.eq
  obtain ⟨hP, hcP⟩ := key nb yH z (hMH hzM) hzH hBz
  obtain ⟨hnP, hcnP⟩ := key nb ynH z (hMnH hzM) hznH hBz
  obtain ⟨hC, hcC⟩ := key g₁ yH z⁻¹ (by rw [map_inv]; exact hMH (inv_mem hzM)) hzH.inv_left hg₁z
  obtain ⟨hnC, hcnC⟩ :=
    key g₁ ynH z⁻¹ (by rw [map_inv]; exact hMnH (inv_mem hzM)) hznH.inv_left hg₁z
  set c : ↥C₀ := (nb⁻¹ * yH * nb) * (g₁⁻¹ * yH * g₁) * (g₁⁻¹ * ynH * g₁) * (nb⁻¹ * ynH * nb)
    with hcdef
  have hcperp : ψ c ∈ perpSub (ψ z) := by
    rw [hcdef, map_mul, map_mul, map_mul]
    exact mul_mem (mul_mem (mul_mem hP hC) hnC) hnP
  have hcz : Commute z c := ((hcP.mul_right hcC).mul_right hcnC).mul_right hcnP
  have hc7 : 7 ∣ orderOf c := by
    have hcoe : (c : ModGL TwistTag.D4.tag K) =
        Xr d4P 1 * Xr d4C 1 * Xr (-d4C) 1 * Xr (-d4P) 1 := by
      have hP' : (nB K)⁻¹ * Xr d4H 1 * nB K = Xr d4P 1 := by rw [← nB_P]; group
      have hnP' : (nB K)⁻¹ * Xr (-d4H) 1 * nB K = Xr (-d4P) 1 := by
        have e1 : Xr (-d4H) 1 = nB K * Xr (-d4P) 1 * (nB K)⁻¹ := by
          rw [nB_conj (by decide +kernel), smul_neg, rB_P]
        rw [e1]
        group
      have hC' : (nB K * nA K)⁻¹ * Xr d4H 1 * (nB K * nA K) = Xr d4C 1 := by
        rw [← nB_P, ← nA_C]; group
      have hnC' : (nB K * nA K)⁻¹ * Xr (-d4H) 1 * (nB K * nA K) = Xr (-d4C) 1 := by
        have e1 : Xr (-d4H) 1 = nB K * Xr (-d4P) 1 * (nB K)⁻¹ := by
          rw [nB_conj (by decide +kernel), smul_neg, rB_P]
        have e2 : Xr (-d4P) 1 = nA K * Xr (-d4C) 1 * (nA K)⁻¹ := by
          rw [nA_conj (by decide +kernel), smul_neg, rA_C]
        rw [e1, e2]
        group
      simp only [hcdef, Subgroup.coe_mul, Subgroup.coe_inv, hnbdef, hg₁def, hyHdef, hynHdef]
      rw [hP', hnP', hC', hnC']
    rw [← Subgroup.orderOf_coe, hcoe]
    exact seven_dvd_orderOf_longA2
  set c' : ↥C₀ := c ^ (orderOf c / 7) with hc'def
  have hc'ord : orderOf c' = 7 := orderOf_pow_orderOf_div (orderOf_pos c).ne' hc7
  have hc'7 : c' ^ 7 = 1 := by rw [← hc'ord]; exact pow_orderOf_eq_one c'
  have hc'P : ψ c' ∈ perpSub (ψ z) := by rw [hc'def, map_pow]; exact pow_mem hcperp _
  have hzc' : Commute z c' := hcz.pow_right _
  have hc'1 : c' ≠ 1 := fun h => by rw [h, orderOf_one] at hc'ord; omega
  set Z := Subgroup.zpowers z with hZdef
  set Cc := Subgroup.zpowers c' with hCcdef
  have hZcard : Nat.card Z = 7 := by rw [Nat.card_zpowers, hzord]
  have hCcard : Nat.card Cc = 7 := by rw [Nat.card_zpowers, hc'ord]
  have hZC : ∀ u ∈ Z, ∀ v ∈ Cc, Commute u v := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hzc'.zpow_zpow i j
  have hCnorm : Cc ≤ Subgroup.normalizer (Z : Set ↥C₀) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun u hu =>
      (hZC u hu c' (Subgroup.mem_zpowers c')).eq)
  have hmemR : ∀ x ∈ Z ⊔ Cc, ∃ u ∈ Z, ∃ v ∈ Cc, x = u * v := by
    intro x hx
    have hx' : x ∈ ((Z ⊔ Cc : Subgroup ↥C₀) : Set ↥C₀) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Z Cc hCnorm] at hx'
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.1 hx'
    exact ⟨u, hu, v, hv, huv.symm⟩
  have hpow7 : ∀ x ∈ Z ⊔ Cc, x ^ 7 = 1 := by
    intro x hx
    obtain ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩ := hmemR x hx
    rw [(hzc'.zpow_zpow i j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm, zpow_mul, mul_comm (j : ℤ), zpow_mul, zpow_natCast, zpow_natCast, hz7, hc'7,
      one_zpow, one_zpow, one_mul]
  have hc'Z : c' ∉ Z := by
    intro h
    have hmem : ψ c' ∈ Subgroup.zpowers (ψ z) := by
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem ψ h
    exact hc'1 (hψ (by rw [eq_one_of_mem_perpSub_of_mem_zpowers hV (hodd z hz7) hc'P hmem,
      map_one]))
  have hfac : (Nat.card ↥C₀).factorization 7 = 2 := by
    rw [hcard]; exact factorization_ordTrialityD4_two_seven
  have hpg : IsPGroup 7 ↥(Z ⊔ Cc) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hpow7 x x.2)⟩
  obtain ⟨S, hRS⟩ := hpg.exists_le_sylow
  have hScard : Nat.card S = 49 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  have hRcard : Nat.card ↥(Z ⊔ Cc) = 49 := by
    have h1 : 7 ∣ Nat.card ↥(Z ⊔ Cc) := hZcard ▸ Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card ↥(Z ⊔ Cc) ∣ 49 := hScard ▸ Subgroup.card_dvd_of_le hRS
    have h3 : Nat.card ↥(Z ⊔ Cc) ≠ 7 := fun h => hc'Z (by
      have hEq : Z = Z ⊔ Cc := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hZcard])
      rw [hEq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c'))
    have h4 : Nat.card ↥(Z ⊔ Cc) ∈ Nat.divisors 49 := Nat.mem_divisors.2 ⟨h2, by norm_num⟩
    have h5 : Nat.divisors 49 = {1, 7, 49} := by decide
    rw [h5] at h4
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    rcases h4 with h | h | h
    · rw [h] at h1; norm_num at h1
    · exact absurd h h3
    · exact h
  have hRS' : Z ⊔ Cc = S := Subgroup.eq_of_le_of_card_ge hRS (by rw [hScard, hRcard])
  obtain ⟨R, i, j, h, -, hRp, hRcard49, hq, -, -⟩ :=
    exists_threeSix_q8 (f := 1) le_rfl hK σ hσ (ε := 1) (Or.inl rfl) (d := 7) (by norm_num)
      (p := 7) (by norm_num) (by norm_num) (dvd_refl 7)
  set RS : Sylow 7 ↥C₀ := Sylow.ofCard R (by rw [hRcard49, hfac]) with hRSdef
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C₀ S RS
  have hRg : ∀ x : ↥C₀, x ∈ R ↔ g⁻¹ * x * g ∈ Z ⊔ Cc := by
    intro x
    have e : (R : Subgroup ↥C₀) = MulAut.conj g • (S : Subgroup ↥C₀) := by
      rw [← Sylow.coe_subgroup_smul, hg, hRSdef, Sylow.coe_ofCard]
    rw [e, hRS', Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
  have hK₀R : conjSub g Z ≤ R := fun x hx => by
    rw [hRg]
    have := mem_conjSub.1 hx
    exact Subgroup.mem_sup_left this
  have hK₀card : Nat.card (conjSub g Z) = 7 := by rw [card_conjSub, hZcard]
  obtain ⟨S₄, hS₄, hS₄'⟩ := four_le_orbit (p := 7) (by norm_num) hRp hq hK₀R hK₀card
  have hNR : Subgroup.closure ({i, j, h} : Set ↥C₀) ≤ Subgroup.normalizer (R : Set ↥C₀) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact hq.mem_i
    · exact hq.mem_j
    · exact hq.mem_h
  have hline : ∀ v : ↥C₀, conjSub v Z ≤ Z ⊔ Cc → conjSub v Z = Z ∨ conjSub v Z = Cc := by
    intro v hv
    have hw : v * z * v⁻¹ ∈ Z ⊔ Cc := by
      apply hv
      rw [mem_conjSub, show v⁻¹ * (v * z * v⁻¹) * v = z by group]
      exact Subgroup.mem_zpowers z
    have hconjZ : conjSub v Z = Subgroup.zpowers (v * z * v⁻¹) := by
      show (Subgroup.zpowers z).map (MulAut.conj v).toMonoidHom = _
      rw [MonoidHom.map_zpowers]
      rfl
    have hwo : orderOf (v * z * v⁻¹) = 7 := by
      rw [← hzord]
      exact (SemiconjBy.orderOf_eq v (SemiconjBy.conj_mk v z)).symm
    obtain ⟨u, hu, t, ht, hut⟩ := hmemR _ hw
    have hgen : ∀ (x : ↥C₀) (H : Subgroup ↥C₀), x ∈ H → Nat.card H = 7 → orderOf x = 7 →
        Subgroup.zpowers x = H := fun x H hx hH hxo =>
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx) (by rw [hH, Nat.card_zpowers, hxo])
    by_cases ht1 : t = 1
    · left
      rw [hconjZ]
      exact hgen _ Z (by rw [hut, ht1, mul_one]; exact hu) hZcard hwo
    by_cases hu1 : u = 1
    · right
      rw [hconjZ]
      exact hgen _ Cc (by rw [hut, hu1, one_mul]; exact ht) hCcard hwo
    exfalso
    have hu7 : u ^ 7 = 1 := hpow7 u (Subgroup.mem_sup_left hu)
    have huo : orderOf u = 7 := orderOf_eq_prime hu7 hu1
    have hZu : Subgroup.zpowers u = Z := hgen u Z hu hZcard huo
    have hidxu : (fixV (Subgroup.zpowers (ψ u))).index = (fixV (Subgroup.zpowers (ψ z))).index := by
      rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, hZu]
    have htP : ψ t ∈ perpSub (ψ u) := by
      have h1 : ψ t ∈ perpSub (ψ z) := by
        obtain ⟨k, rfl⟩ := ht
        rw [map_zpow]
        exact zpow_mem hc'P k
      have h2 : ψ u ∈ perpSub (ψ t) := by
        obtain ⟨k, rfl⟩ := hu
        rw [map_zpow]
        exact zpow_mem (mem_perpSub_comm.1 h1) k
      exact mem_perpSub_comm.1 h2
    have hmul := index_fixV_mul_of_mem_perpSub hV (hodd u hu7) htP
    rw [← map_mul, ← hut, show v * z * v⁻¹ = v * z * v⁻¹ from rfl, hψconj, hidxu] at hmul
    have hpos : 0 < (fixV (Subgroup.zpowers (ψ z))).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hone : (fixV (Subgroup.zpowers (ψ t))).index = 1 :=
      (Nat.eq_of_mul_eq_mul_left hpos (hmul.symm.trans (mul_one _).symm))
    exact ht1 (hidx1 t hone)
  have himg : S₄.image (conjSub g⁻¹) ⊆ {Z, Cc} := by
    intro X hX
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨u, hu, rfl⟩ := hS₄' K' hK'
    have hle : conjSub u (conjSub g Z) ≤ R := conjSub_le (hNR hu) hK₀R
    have e : conjSub g⁻¹ (conjSub u (conjSub g Z)) = conjSub (g⁻¹ * u * g) Z := by
      rw [conjSub_mul, conjSub_mul]
    have hv : conjSub (g⁻¹ * u * g) Z ≤ Z ⊔ Cc := by
      rw [← e]
      intro x hx
      have hx' := mem_conjSub.1 hx
      rw [inv_inv] at hx'
      have := (hRg _).1 (hle hx')
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    rw [e]
    rcases hline _ hv with h' | h' <;> rw [h']
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hinj : Function.Injective (conjSub g⁻¹ : Subgroup ↥C₀ → Subgroup ↥C₀) := fun _ _ h' =>
    conjSub_injective g⁻¹ h'
  have h4 : 4 ≤ (S₄.image (conjSub g⁻¹)).card := by
    rw [Finset.card_image_of_injective _ hinj]
    exact hS₄
  have h2 : (S₄.image (conjSub g⁻¹)).card ≤ 2 :=
    (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
  omega

end LongTwo

section Long

variable {f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

include hK hσ in
theorem two_pow_six_mul_le_index_long_of_one_le (hf : 1 ≤ f) {V : Type*} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (φ : ↥L ≃* ↥C₀) {y : ↥L}
    (hy : ConjC σ ((φ y : C₀) : ModGL TwistTag.D4.tag K) (Xr d4H 1)) :
    2 ^ (6 * f) ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index := by
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
  · exact two_pow_six_le_index_long_two hK σ hσ hV φ hy
  · exact two_pow_six_mul_le_index_long hK σ hσ hf2 hV φ hy

end Long

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
