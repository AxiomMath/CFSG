module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.CharTwoLocal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped commutatorElement
open Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem w183l313_mem_sylowCenter_subgroupOf {Q S : Subgroup Γ} (hSQ : S ≤ Q) {x : ↥Q} :
    x ∈ sylowCenter (S.subgroupOf Q) ↔ (x : Γ) ∈ sylowCenter S := by
  rw [mem_sylowCenter, mem_sylowCenter]
  constructor
  · rintro ⟨hxS, hxc⟩
    refine ⟨hxS, fun t ht => ?_⟩
    exact Subtype.ext_iff.mp (hxc ⟨t, hSQ ht⟩ (by rwa [Subgroup.mem_subgroupOf]))
  · rintro ⟨hxS, hxc⟩
    refine ⟨by rwa [Subgroup.mem_subgroupOf], fun y hy => ?_⟩
    apply Subtype.ext
    exact hxc (y : Γ) (by rwa [Subgroup.mem_subgroupOf] at hy)

theorem w183l313_odd_conj_eq {S D : Subgroup Γ} (hDodd : Odd (Nat.card D)) {d s : Γ}
    (hd : d ∈ D) (hdN : d ∈ Subgroup.normalizer (S : Set Γ)) (hs : s ∈ S)
    (hP : IsPGroup 2 S) (h : ∀ t ∈ S, d * t * d⁻¹ = s⁻¹ * t * s) :
    ∀ t ∈ S, d * t * d⁻¹ = t := by
  have hodd_d : Odd (orderOf d) := hDodd.of_dvd_nat (D.orderOf_dvd_natCard hd)
  let dN : Subgroup.normalizer (S : Set Γ) := ⟨d, hdN⟩
  let sN : Subgroup.normalizer (S : Set Γ) := ⟨s⁻¹, Subgroup.le_normalizer (S.inv_mem hs)⟩
  let φ : Subgroup.normalizer (S : Set Γ) →* MulAut ↥S :=
    Subgroup.normalizerMonoidHom (H := S)
  have heq : φ dN = φ sN := by
    ext u
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp only [dN, sN]
    simpa using h u u.2
  obtain ⟨a, ha⟩ := hP ⟨s, hs⟩
  have ha' : s ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hdm : φ dN ^ orderOf d = 1 := by
    rw [← map_pow, ← map_one φ]
    congr 1
    apply Subtype.ext
    exact pow_orderOf_eq_one d
  have hsm : φ sN ^ 2 ^ a = 1 := by
    rw [← map_pow, ← map_one φ]
    congr 1
    apply Subtype.ext
    show (s⁻¹) ^ 2 ^ a = 1
    rw [inv_pow, ha', inv_one]
  have hdm' : φ dN ^ 2 ^ a = 1 := by rw [heq, hsm]
  have horder : orderOf (φ dN) = 1 := by
    have h1 : orderOf (φ dN) ∣ orderOf d := orderOf_dvd_iff_pow_eq_one.mpr hdm
    have h2 : orderOf (φ dN) ∣ 2 ^ a := orderOf_dvd_iff_pow_eq_one.mpr hdm'
    have hcop : Nat.Coprime (orderOf d) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd_d)
    have h3 : orderOf (φ dN) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact Nat.dvd_one.mp h3
  have hphi1 : φ dN = 1 := orderOf_eq_one_iff.mp horder
  have hmem : dN ∈ φ.ker := MonoidHom.mem_ker.mpr hphi1
  rw [Subgroup.normalizerMonoidHom_ker] at hmem
  have hdC : d ∈ Subgroup.centralizer (S : Set Γ) := Subgroup.mem_subgroupOf.mp hmem
  intro t ht
  have hct : t * d = d * t := Subgroup.mem_centralizer_iff.mp hdC t ht
  rw [← hct]; group


lemma w183l313_conj_commutator_self {f s : Γ} (hf : f * f = 1) :
    f * (f * s * f⁻¹ * s⁻¹) * f⁻¹ = (f * s * f⁻¹ * s⁻¹)⁻¹ := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  rw [show f * (f * s * f⁻¹ * s⁻¹) * f⁻¹ = s * f * s⁻¹ * f by
        rw [hfi]
        rw [show f * (f * s * f * s⁻¹) * f = (f * f) * s * f * s⁻¹ * f by group, hf, one_mul]]
  rw [show (f * s * f⁻¹ * s⁻¹)⁻¹ = s * f * s⁻¹ * f by
        rw [show (f * s * f⁻¹ * s⁻¹)⁻¹ = s * f * s⁻¹ * f⁻¹ by group, hfi]]

end CFSG.LocalAnalysis.WeakClosure81

end
