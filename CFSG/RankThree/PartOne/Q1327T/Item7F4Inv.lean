module

public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.RankThree.PartOne.K128.ReeShape
import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import CFSG.RankThree.PartOne.Q1327T.Item7Basic

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.K128
  CFSG.RankThree.Chevalley

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

theorem weyl_mul_comm_of_neg {τ : Tag} {w₀ : WeylGroup τ} (hw₀ : ∀ v : Fin τ.rank → ℤ, w₀ • v = -v)
    (w : WeylGroup τ) : w * w₀ = w₀ * w := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, hw₀, hw₀, smul_neg]

theorem canonicalRep_longest_mem_twistedFixed (D : ReeFrameData K L a)
    {w₀ : WeylGroup ReeTag.F4.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.F4.tag).length w ≤ (coxeterSystem ReeTag.F4.tag).length w₀)
    (w : WeylGroup ReeTag.F4.tag) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
  have hneg : ∀ v : Fin ReeTag.F4.tag.rank → ℤ, w₀ • v = -v := ReeTag.smul_longest hw₀
  refine ⟨canonicalRep_mem_adjointGroup _ L w₀, ?_⟩
  have hΓ : canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀ ∈ ReeTag.F4.reeGamma K a :=
    (Subgroup.mem_inf.1
      (ReeTag.canonicalRep_longest_mem_reeFixedMonomial (t := ReeTag.F4) (K := K) (a := a)
        hw₀)).2
  have hFn : Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ := by
    have h := D.fext_theta ⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀, hΓ⟩
    rw [thetaGamma_apply] at h
    rwa [baseChangeGL_canonicalRep (algebraMap K L)] at h
  rw [hFn]
  have hcomm : canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ *
        canonicalRep (coxeterSystem ReeTag.F4.tag) L w := by
    rw [← canonicalRep_mul_charTwo, ← canonicalRep_mul_charTwo, weyl_mul_comm_of_neg hneg]
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_hom_reeGamma_inv (D : ReeFrameData K L a) (w : WeylGroup ReeTag.F4.tag)
    {G₀ : Type*} [Group G₀] (φ : G₀ →* ModGL ReeTag.F4.tag L) (hφ : Function.Injective φ)
    (hφT : φ.range ≤ torusGroup ReeTag.F4.tag L)
    (hφF : φ.range ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ∃ Ψ : G₀ →* ReeTag.F4.reeGamma K a, Function.Injective Ψ ∧
      ∃ z : ReeTag.F4.reeGamma K a, ∀ x, z * Ψ x * z⁻¹ = (Ψ x)⁻¹ := by
  classical
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  have hθ : ∀ z, ∃ γ : ReeTag.F4.reeGamma K a, thetaGamma L a γ = g₀ * φ z * g₀⁻¹ := by
    intro z
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ (hφF ⟨z, rfl⟩)
    exact D.exists_theta_of_fixed hadj hfix
  choose ψ hψ using hθ
  have hinjθ := thetaGamma_injective (K := K) L (a := a)
  let Ψ : G₀ →* ReeTag.F4.reeGamma K a :=
    { toFun := ψ
      map_one' := by
        apply hinjθ
        rw [hψ, map_one, map_one]
        group
      map_mul' := fun z z' => by
        apply hinjθ
        rw [map_mul (thetaGamma L a) (ψ z) (ψ z'), hψ (z * z'), hψ z, hψ z', map_mul φ z z']
        group }
  have hΨinj : Function.Injective Ψ := fun z z' hzz => by
    have h1 : g₀ * φ z * g₀⁻¹ = g₀ * φ z' * g₀⁻¹ := by
      rw [← hψ z, ← hψ z']
      exact congrArg _ hzz
    have h2 : φ z = φ z' := mul_left_cancel (mul_right_cancel h1)
    exact hφ h2
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.F4.tag).length
  have hneg : ∀ v : Fin ReeTag.F4.tag.rank → ℤ, w₀ • v = -v := ReeTag.smul_longest hw₀
  have hn₀ := canonicalRep_longest_mem_twistedFixed D hw₀ w
  obtain ⟨hadj', hfix'⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ hn₀
  obtain ⟨z, hz⟩ := D.exists_theta_of_fixed hadj' hfix'
  refine ⟨Ψ, hΨinj, z, fun x => ?_⟩
  apply hinjθ
  rw [map_mul, map_mul, map_inv, map_inv, hz]
  change _ * thetaGamma L a (ψ x) * _ = (thetaGamma L a (ψ x))⁻¹
  rw [hψ x]
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hφT ⟨x, rfl⟩)
  have hinv : canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ * φ x *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀)⁻¹ = (φ x)⁻¹ := by
    rw [hl]
    exact SteinbergBT.TrialityPlane.canonicalRep_conj_rootDiagUnit_of_neg hneg l
  calc g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ * g₀⁻¹ * (g₀ * φ x * g₀⁻¹) *
        (g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ * g₀⁻¹)⁻¹
      = g₀ * (canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ * φ x *
          (canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀)⁻¹) * g₀⁻¹ := by group
    _ = (g₀ * φ x * g₀⁻¹)⁻¹ := by rw [hinv]; group

end Frame

section Sylow

theorem exists_inv_of_rootsOfUnity_pi {p e : ℕ} (hp : p.Prime) {L : Type*} [Field L]
    [IsAlgClosed L] (hpL : (p : L) ≠ 0) {Γ : Type} [Group Γ] [Finite Γ]
    (Ψ : (rootsOfUnity (p ^ e) L) × (rootsOfUnity (p ^ e) L) →* Γ) (hΨ : Function.Injective Ψ)
    (hle : (Nat.card Γ).factorization p ≤ 2 * e) (z : Γ) (hz : ∀ x, z * Ψ x * z⁻¹ = (Ψ x)⁻¹)
    {E : Subgroup Γ} (hE : IsPGroup p E) : ∃ g : Γ, ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card Ψ.range = p ^ (2 * e) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv, Nat.card_prod,
      card_rootsOfUnity_pow hpL, ← pow_add]
    ring_nf
  have hge : 2 * e ≤ (Nat.card Γ).factorization p := by
    have hdvd : p ^ (2 * e) ∣ Nat.card Γ := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  have hS : Nat.card Ψ.range = p ^ (Nat.card Γ).factorization p := by
    rw [hcard, le_antisymm hle hge]
  refine exists_inv_of_sylow (Sylow.ofCard Ψ.range hS) (g₀ := z) (fun y hy => ?_) hE
  rw [Sylow.coe_ofCard] at hy
  obtain ⟨x, rfl⟩ := hy
  exact hz x

end Sylow

section Shapes

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_inv_reeGamma_phi1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) - 1) {E : Subgroup (ReeTag.F4.reeGamma K a)}
    (hE : IsPGroup p E) : ∃ g : ReeTag.F4.reeGamma K a, ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd : Odd (p ^ (2 ^ (2 * a + 1) - 1).factorization p) :=
    (hp.odd_of_ne_two (by omega)).pow
  have hmM : ((p ^ (2 ^ (2 * a + 1) - 1).factorization p : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 1 := by
    have := int_dvd_sub_one' hq1 (Nat.ordProj_dvd (2 ^ (2 * a + 1) - 1) p)
    exact_mod_cast this
  obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi1 (L := AlgebraicClosure K) D.isFrob hodd hmM
  obtain ⟨Ψ, hΨ, z, hz⟩ := exists_hom_reeGamma_inv D wPhi1 Φ hΦ hΦT hΦF
  exact exists_inv_of_rootsOfUnity_pi hp (natCast_ne_zero_algebraicClosure hp (by omega)) Ψ hΨ
    (le_two_mul_of_pow_dvd_sq hp (by omega)
      (pow_factorization_card_reeGamma_dvd_phi1 hK hp (by omega) hpq)) z hz hE

theorem exists_inv_reeGamma_phi2 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) + 1) {E : Subgroup (ReeTag.F4.reeGamma K a)}
    (hE : IsPGroup p E) : ∃ g : ReeTag.F4.reeGamma K a, ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd : Odd (p ^ (2 ^ (2 * a + 1) + 1).factorization p) :=
    (hp.odd_of_ne_two (by omega)).pow
  have hmM : ((p ^ (2 ^ (2 * a + 1) + 1).factorization p : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 1 := by
    have := Int.natCast_dvd_natCast.2 (Nat.ordProj_dvd (2 ^ (2 * a + 1) + 1) p)
    exact_mod_cast this
  obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi2 (L := AlgebraicClosure K) D.isFrob hodd hmM
  obtain ⟨Ψ, hΨ, z, hz⟩ := exists_hom_reeGamma_inv D wPhi2 Φ hΦ hΦT hΦF
  exact exists_inv_of_rootsOfUnity_pi hp (natCast_ne_zero_algebraicClosure hp (by omega)) Ψ hΨ
    (le_two_mul_of_pow_dvd_sq hp (by omega)
      (pow_factorization_card_reeGamma_dvd_phi2 hK hp (by omega) hpq)) z hz hE

theorem exists_inv_reeGamma_phi4 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1) {E : Subgroup (ReeTag.F4.reeGamma K a)}
    (hE : IsPGroup p E) : ∃ g : ReeTag.F4.reeGamma K a, ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set e := ((2 ^ (2 * a + 1)) ^ 2 + 1).factorization p with he
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two (by omega)).pow
  have hpe : p ^ e ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := Nat.ordProj_dvd _ p
  have hLE : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ 2 * e :=
    le_two_mul_of_pow_dvd_sq hp (by omega)
      (pow_factorization_card_reeGamma_dvd_four hK hp (by omega) hpq)
  have hpL := natCast_ne_zero_algebraicClosure (K := K) hp (by omega : p ≠ 2)
  rcases dvd_phi4_cases hp (by omega) hpq with ⟨hp1, hnd⟩ | ⟨hp1, hnd⟩
  · have hdiv : p ^ e ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
      have h1 : p ^ e ∣ (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) *
          (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by rw [phi4_factor a]; exact hpe
      exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_right
        h1
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
      have := Int.natCast_dvd_natCast.2 hdiv
      exact_mod_cast this
    obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi4p (L := AlgebraicClosure K) D.isFrob hodd hmM
    obtain ⟨Ψ, hΨ, z, hz⟩ := exists_hom_reeGamma_inv D wPhi4p Φ hΦ hΦT hΦF
    exact exists_inv_of_rootsOfUnity_pi hp hpL Ψ hΨ hLE z hz hE
  · have hdiv : p ^ e ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      have h1 : p ^ e ∣ (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) *
          (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by rw [phi4_factor a]; exact hpe
      exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_left
        h1
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      exact int_dvd_sub_add_one' hle hdiv |> fun h => by exact_mod_cast h
    obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi4m (L := AlgebraicClosure K) D.isFrob hodd hmM
    obtain ⟨Ψ, hΨ, z, hz⟩ := exists_hom_reeGamma_inv D wPhi4m Φ hΦ hΦT hΦF
    exact exists_inv_of_rootsOfUnity_pi hp hpL Ψ hΨ hLE z hz hE

theorem exists_inv_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) {d : ℕ}
    (hd : d = 1 ∨ d = 2 ∨ d = 4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ phiF4 d (2 ^ (2 * a + 1))) {E : Subgroup (ReeTag.F4.reeGamma K a)}
    (hE : IsPGroup p E) : ∃ g : ReeTag.F4.reeGamma K a, ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  rcases hd with rfl | rfl | rfl
  · exact exists_inv_reeGamma_phi1 hK hp hp5 hpd hE
  · exact exists_inv_reeGamma_phi2 hK hp hp5 hpd hE
  · exact exists_inv_reeGamma_phi4 hK hp hp5 hpd hE

end Shapes

end CFSG.RankThree.PartOne.Q1327T
