module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTvAModel
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTvAKey
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTvALinAlg
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv

public section

namespace CFSG.StandardType.LinTvA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.Assembly TableB TypeA TypeANbrDvd

@[expose] def pairVecZ {d : ℕ} (a b k : Fin d) : ℤ :=
  (if k = a then 1 else 0) - (if k = b then 1 else 0)

theorem pairVec_eq_cast (p : ℕ) {d : ℕ} (a b k : Fin d) :
    pairVec p a b k = ((pairVecZ a b k : ℤ) : ZMod p) := by
  simp only [pairVec, pairVecZ]
  push_cast
  rfl

section Field

variable {d : ℕ} {K : Type} [Field K] {ζ : K}

theorem rootT_eq_zpow {a b : Fin d} (hab : a ≠ b) (k : Fin d) :
    rootT ζ a b k = ζ ^ pairVecZ a b k := by
  unfold rootT pairVecZ
  by_cases hka : k = a
  · subst hka
    simp [hab]
  · by_cases hkb : k = b
    · subst hkb
      simp [hka]
    · simp [hka, hkb]

theorem zpow_sub_eq_one (hζ0 : ζ ≠ 0) {m n : ℤ} (h : ζ ^ m = ζ ^ n) : ζ ^ (n - m) = 1 := by
  rw [zpow_sub₀ hζ0, ← h, div_self (zpow_ne_zero _ hζ0)]

theorem zpow_inv_mul_pow (hζ0 : ζ ≠ 0) (m n : ℤ) (e : ℕ) :
    (ζ ^ m)⁻¹ * (ζ ^ n) ^ e = ζ ^ (n * e - m) := by
  rw [← _root_.zpow_neg, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ hζ0]
  congr 1
  ring

theorem isRat_heartElt {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    [CharP K 2] (hζ0 : ζ ≠ 0) {a b : Fin d} (hab : a ≠ b) :
    IsRat φ' (heartElt φ' hζ0 hab) fun k l => ζ ^ (pairVecZ a b k - pairVecZ a b l) := by
  refine ⟨rootT ζ a b, heartElt_actsDiag hζ0 hab, fun k l => ?_⟩
  beta_reduce
  rw [rootT_eq_zpow hab, rootT_eq_zpow hab, zpow_sub₀ hζ0, div_eq_mul_inv]

theorem zmod_eq_zero_of_zpow {p : ℕ} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) {N : ℤ}
    (h : ζ ^ N = 1) : ((N : ℤ) : ZMod p) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd N p).mpr ((hζ.zpow_eq_one_iff_dvd N).mp h)

end Field

section Main

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {L' : Type} [Group L']
  {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem ratio_identity (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    {α : MulAut L'} (hαN : ∀ b ∈ A, α * b * α⁻¹ ∈ A) {π : Equiv.Perm (Fin d)} {e : ℕ}
    (hRA : RatAct φ' A α π e) {E : MulAut L'} (hE : E ∈ A) {r : Fin d → Fin d → K}
    (hr : IsRat φ' E r) (hT1 : α * (E⁻¹ * (α * E * α⁻¹)) * α⁻¹ = E⁻¹ * (α * E * α⁻¹))
    (k l : Fin d) :
    (r k l)⁻¹ * r (π k) (π l) ^ e =
      ((r (π k) (π l))⁻¹ * r (π (π k)) (π (π l)) ^ e) ^ e := by
  have h1 := hRA E hE r hr
  have h2 := hr.inv.mul h1
  have hu : E⁻¹ * (α * E * α⁻¹) ∈ A := A.mul_mem (A.inv_mem hE) (hαN E hE)
  have h3 := hRA _ hu _ h2
  rw [hT1] at h3
  have h4 := IsRat.unique hφker h2 h3
  have h5 := congrFun (congrFun h4 k) l
  beta_reduce at h5
  exact h5

theorem pairVec_identity (hp : p.Prime) (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} {α : MulAut L'} (hαN : ∀ b ∈ A, α * b * α⁻¹ ∈ A)
    {π : Equiv.Perm (Fin d)} {e : ℕ} (hRA : RatAct φ' A α π e) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hζ0 : ζ ≠ 0) {a b : Fin d} {E : MulAut L'} (hE : E ∈ A)
    (hr : IsRat φ' E fun k l => ζ ^ (pairVecZ a b k - pairVecZ a b l))
    (hT1 : α * (E⁻¹ * (α * E * α⁻¹)) * α⁻¹ = E⁻¹ * (α * E * α⁻¹)) (k l : Fin d) :
    (e : ZMod p) ^ 2 * (pairVec p a b (π (π k)) - pairVec p a b (π (π l))) -
      2 * (e : ZMod p) * (pairVec p a b (π k) - pairVec p a b (π l)) +
      (pairVec p a b k - pairVec p a b l) = 0 := by
  have h := ratio_identity hφker hαN hRA hE hr hT1 k l
  beta_reduce at h
  rw [zpow_inv_mul_pow hζ0, zpow_inv_mul_pow hζ0, ← zpow_natCast, ← _root_.zpow_mul] at h
  have h2 := zmod_eq_zero_of_zpow hp hζ (zpow_sub_eq_one hζ0 h)
  push_cast at h2
  simp only [← pairVec_eq_cast] at h2
  linear_combination h2

theorem pairVec_identity_pow (hp : p.Prime) (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} {α : MulAut L'} {π : Equiv.Perm (Fin d)} {e : ℕ}
    (hRAp : RatAct φ' A (α ^ p) (π ^ p) (e ^ p)) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hζ0 : ζ ≠ 0) {a b : Fin d} {E : MulAut L'} (hE : E ∈ A)
    (hr : IsRat φ' E fun k l => ζ ^ (pairVecZ a b k - pairVecZ a b l))
    (hcomm : α ^ p * E * (α ^ p)⁻¹ = E) (k l : Fin d) :
    (e : ZMod p) ^ p * (pairVec p a b ((π ^ p) k) - pairVec p a b ((π ^ p) l)) =
      pairVec p a b k - pairVec p a b l := by
  have h1 := hRAp E hE _ hr
  rw [hcomm] at h1
  have h3 := congrFun (congrFun (IsRat.unique hφker hr h1) k) l
  beta_reduce at h3
  rw [← zpow_natCast, ← _root_.zpow_mul] at h3
  have h2 := zmod_eq_zero_of_zpow hp hζ (zpow_sub_eq_one hζ0 h3)
  push_cast at h2
  simp only [← pairVec_eq_cast] at h2
  linear_combination h2

theorem noTransvectionSCr_PSL (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) :
    GGNoTransvectionSCr p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc α hα hT
  obtain ⟨φα, hφα⟩ := hα
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one hpK
  obtain ⟨A₀, φ', hφ's, hφker, hcompat, hdiag⟩ :=
    exists_model_compat hp hpK hd hψ hker hperf hA hAI hr h3
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  have hαN : ∀ b ∈ A, (α : MulAut L') * b * (α : MulAut L')⁻¹ ∈ A := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp α.2 b).mp hb
  have hA0 : 0 < Nat.card A := lt_of_lt_of_le (pow_pos hp.pos 3) h3
  obtain ⟨hT1, b₀, hb₀, hb₀ne⟩ := transvection_data hp hA0 hT
  obtain ⟨π, e, hRA⟩ :=
    exists_ratAct hp hpK (by omega) hψ hφ's hφker hcompat hAp hdiag hsc hαN hφα
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hdpos : 0 < d := by omega
  have hvec : ∀ a b : Fin d, a ≠ b → ∀ k l,
      (e : ZMod p) ^ 2 * (pairVec p a b (π (π k)) - pairVec p a b (π (π l))) -
        2 * (e : ZMod p) * (pairVec p a b (π k) - pairVec p a b (π l)) +
        (pairVec p a b k - pairVec p a b l) = 0 := fun a b hab =>
    pairVec_identity hp hφker hαN hRA hζ hζ0 (heartElt_mem hsc hdiag hζ0 hζ.pow_eq_one hab)
      (isRat_heartElt hζ0 hab) (hT1 _ (heartElt_mem hsc hdiag hζ0 hζ.pow_eq_one hab))
  have hvecp : ∀ a b : Fin d, a ≠ b → ∀ k l,
      (e : ZMod p) ^ p * (pairVec p a b ((π ^ p) k) - pairVec p a b ((π ^ p) l)) =
        pairVec p a b k - pairVec p a b l := fun a b hab =>
    pairVec_identity_pow hp hφker (hRA.pow hαN p) hζ hζ0
      (heartElt_mem hsc hdiag hζ0 hζ.pow_eq_one hab) (isRat_heartElt hζ0 hab)
      (conj_pow_prime_eq hAp hαN (heartElt_mem hsc hdiag hζ0 hζ.pow_eq_one hab)
        (hT1 _ (heartElt_mem hsc hdiag hζ0 hζ.pow_eq_one hab)))
  obtain ⟨hep, hπp⟩ := eq_one_of_pairVec hd hvecp
  have he1 : (e : ZMod p) = 1 := (ZMod.pow_card (e : ZMod p)).symm.trans hep
  by_cases hπ1 : π = 1
  ·
    subst hπ1
    apply hb₀ne
    obtain ⟨t, ht⟩ := hdiag b₀ hb₀
    have hrat : IsRat φ' b₀ fun k l => t k * (t l)⁻¹ := ⟨t, ht, fun _ _ => rfl⟩
    obtain ⟨t', ht', hrt'⟩ := hRA b₀ hb₀ _ hrat
    have he' : e % p = 1 := by
      have h1 : ((e : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using he1
      rw [(ZMod.natCast_eq_natCast_iff' e 1 p).mp h1, Nat.mod_eq_of_lt hp.one_lt]
    refine IsRat.eq hdpos hφ's (r := fun k l => t k * (t l)⁻¹) ⟨t', ht', fun k l => ?_⟩ hrat
    rw [← hrt' k l]
    beta_reduce
    simp only [Equiv.Perm.one_apply]
    have hx : (t k * (t l)⁻¹) ^ p = 1 := ht.ratio_pow hφker (hAp b₀ hb₀) k l
    have hxe : (t k * (t l)⁻¹) ^ e = t k * (t l)⁻¹ := by
      rw [← Nat.div_add_mod e p, pow_add, pow_mul, hx, one_pow, one_mul, he', pow_one]
    exact hxe.symm
  · exact false_of_pairVec_transvection hp2 hd hπp hπ1 fun a b hab k l => by
      have h := hvec a b hab k l
      rw [he1] at h
      linear_combination h

end Main

end CFSG.StandardType.LinTvA

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTypeADvdNoTransvectionInput_holds : GGTypeADvdNoTransvectionInput :=
  fun _ _ _ _ _ _ hd hp hpK _ => LinTvA.noTransvectionSCr_PSL hp hpK hd

end CFSG.StandardType

end
