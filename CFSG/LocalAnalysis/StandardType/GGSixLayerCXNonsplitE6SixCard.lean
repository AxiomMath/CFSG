module

public import CFSG.RankThree.PartOne.KE6.Phi6A2A2Case
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl
public import CFSG.CharacterTheory.BrauerLinearThree.LocalRecognition

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open Matrix
open scoped Matrix MatrixGroups Pointwise commutatorElement

namespace NonsplitLayers

theorem dvd_pow_three_add_one_of_dvd_sq_sub_add_one {p q : ℕ}
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 - q + 1) : p ∣ q ^ 3 + 1 := by
  have h1 : ((q ^ 3 + 1 : ℕ) : ℤ) = ((q : ℤ) + 1) * ((q : ℤ) ^ 2 - q + 1) := by
    push_cast
    ring
  have : (p : ℤ) ∣ ((q ^ 3 + 1 : ℕ) : ℤ) := by
    rw [h1]
    exact Dvd.dvd.mul_left h _
  exact_mod_cast this

theorem dvd_pow_six_sub_one_of_dvd_sq_sub_add_one {p q : ℕ} (hq1 : 1 ≤ q)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 - q + 1) : p ∣ q ^ 6 - 1 := by
  have h3 := dvd_pow_three_add_one_of_dvd_sq_sub_add_one h
  have hq : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have h1 : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have h6 : q ^ 6 = (q ^ 3) ^ 2 := by ring
    rw [h6]
    zify [hq, Nat.one_le_pow 2 (q ^ 3) hq]
    ring
  rw [h1]
  exact Dvd.dvd.mul_left h3 _


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem phi6_A2_layer_card {K : Type} [Field K] [Finite K] [Algebra K Ω] [IsAlgClosure K Ω]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    p ∣ Nat.card ↥(phi6Qθ Ω Fr (torusRootKernel x)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi6TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁, π, hθ⟩ := phi6_A2_transport hp3 hFr hζ hr hxT hx1 hA2
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta hFrs
    (phi6ThetaConj Ω Fr w) (phi6ThetaConj_injective w) π hθ
  obtain ⟨e, -⟩ := exists_mulEquiv_fixSubgroup6 hQ₁ hmaps Φ hΦ₀
  obtain ⟨-, ⟨H', hH'⟩, -, -, -⟩ := sln_root_permuting_frobenius_fixed_unitary hℓ hf hK
    (le_refl 3) π Φ b (fun i j hij t => by rw [hΦt, hFr])
  have hcard : Nat.card ↥(phi6Qθ Ω Fr (torusRootKernel x)) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
    have hQe : Nat.card ↥(phi6Qθ Ω Fr (torusRootKernel x)) = Nat.card ↥(fixSubgroup Φ) :=
      Nat.card_congr e.toEquiv
    rw [hQe, CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_card_eq_of_conj
      (fixSubgroup Φ) (unitarySet (ℓ ^ f) 3) (fun Y hY => hY.2.1) H' hH',
      CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_card_unitarySet_three hf]
  rw [hcard]
  exact Dvd.dvd.mul_left (dvd_pow_three_add_one_of_dvd_sq_sub_add_one hpq) _

theorem phi6_A2A2_layer_card {K : Type} [Field K] [Finite K] [Algebra K Ω] [IsAlgClosure K Ω]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    p ∣ Nat.card ↥(phi6P Ω Fr (torusRootKernel x)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi6TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁₂, π, π', h12, h21⟩ := phi6_A2A2_transport hp3 hFr hζ hr hxT hx1 hA2A2
  obtain ⟨θ, hθ, a, b, hab⟩ := exists_exchanged_layer_pos hFrs (phi6ThetaConj Ω Fr w)
    (phi6ThetaConj_injective w) π π' h12 h21
  obtain ⟨k₂, hk₂, h₁, h₂, ψ, -, hψfix, -, -, -, hkercard, ⟨hquot⟩, -, -, -, hder9⟩ := CFSG.RankThree.Classical.SteinbergBY.exchanged_sl3_central_product_frobenius_full_fixed_layer hℓ hf hK Fr
    hFr twoA2MulSup twoA2MulSup_surjective (fun xy => twoA2MulSup_eq_one_iff xy.1 xy.2) θ a b hab
  set Y := phi6Qθ Ω Fr (torusRootKernel x) with hYdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hYF : Y.map (MulAut.conj n).toMonoidHom =
      (fixSubgroup θ).map (subsystemGroup Tag.E6 Ω support13 ⊔
        subsystemGroup Tag.E6 Ω support56).subtype :=
    map_conj_phi6Qθ hQ₁₂ θ hθ
  let F : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ModGL Tag.E6 Ω := (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _)
  have hF : Function.Injective F := (MulAut.conj n).symm.injective.comp Subtype.val_injective
  have hFapp : ∀ y, F y = n⁻¹ * (y : ModGL Tag.E6 Ω) * n := fun y => by
    simp [F, MulAut.conj_symm_apply]
  have hYf : (fixSubgroup θ).map F = Y := by
    have hid : (MulAut.conj n).symm.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun y => by simp
    rw [show F = (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _) from rfl,
      ← Subgroup.map_map, ← hYF, Subgroup.map_map, hid, Subgroup.map_id]
  set ψ' : SL(3, k₂) →* ModGL Tag.E6 Ω := F.comp ψ with hψ'def
  have hder' : ⁅fixSubgroup θ, fixSubgroup θ⁆ = ψ.range := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hψfix, ← hder9, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hrange : ψ'.range = ⁅Y, Y⁆ := by
    rw [← hYf, ← Subgroup.map_commutator, hder', MonoidHom.range_comp]
  have hψ'1 : ∀ A, ψ' A = 1 ↔ ψ A = 1 := fun A => map_eq_one_iff F hF
  let E : ↥ψ.range ≃* ↥⁅Y, Y⁆ := (Subgroup.equivMapOfInjective ψ.range F hF).trans
    (MulEquiv.subgroupCongr (by rw [← MonoidHom.range_comp]; exact hrange))
  obtain ⟨K', hK'card, hK'mem⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_exists_subfield (Ω := Ω) (ℓ := ℓ) hf
  have hk₂K' : k₂ = K' := Subfield.ext fun c => (hk₂ c).trans (hK'mem c).symm
  have hk₂card : Nat.card k₂ = (ℓ ^ f) ^ 2 := by rw [hk₂K']; exact hK'card
  have : Finite k₂ := Nat.finite_of_card_ne_zero (by
    rw [hk₂card]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hmul : Nat.card SL(3, ↥k₂) = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, Nat.card_congr hquot.toEquiv]
  have hdvdSL : p ∣ Nat.card SL(3, ↥k₂) := by
    rw [CFSG.BrauerLinearThree.card_SL_three, hk₂card, ← pow_mul]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left
      (dvd_pow_six_sub_one_of_dvd_sq_sub_add_one (Nat.one_le_pow _ _ hℓ.pos) hpq) _) _
  have hker : ¬ p ∣ Nat.card ψ.ker := fun h => by
    rw [hkercard] at h
    have h3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left _ _)
    exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
  have hrange : p ∣ Nat.card ψ.range := by
    rw [hmul] at hdvdSL
    exact ((Nat.Prime.dvd_mul hp).1 hdvdSL).resolve_right hker
  change p ∣ Nat.card ↥⁅Y, Y⁆
  rwa [← Nat.card_congr E.toEquiv]

end NonsplitLayers

end CFSG.RankThree.PartOne.KE6
