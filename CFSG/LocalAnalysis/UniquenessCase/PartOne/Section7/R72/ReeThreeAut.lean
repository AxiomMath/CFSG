module

public import CFSG.Walter.PSL2Facts.Even
import CFSG.LocalAnalysis.ComponentClassification.AS81SL2Rigid
import CFSG.Timmesfeld.Bridge.SchurNarrowTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open Subgroup
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]

theorem isMulCommutative_sylow_two_of_psl28 (e : K ≃* PSL(2, GaloisField 2 3)) (hidx : K.index = 3)
    (S : Sylow 2 X) : IsMulCommutative (S : Subgroup X) := by
  have hSK : (S : Subgroup X) ≤ K :=
    CFSG.Timmesfeld.Bridge.sylow_le_of_odd_index (by rw [hidx]; decide) S
  have hp : IsPGroup 2 (((S : Subgroup X).subgroupOf K).map e.toMonoidHom) :=
    (S.isPGroup'.comap_of_injective K.subtype K.subtype_injective).map e.toMonoidHom
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨hPel, -⟩ := CFSG.Walter.psl2_even_sylow_two (f := 3) (by norm_num) P
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha : e ⟨a, hSK a.2⟩ ∈ (P : Subgroup PSL(2, GaloisField 2 3)) := hP ⟨⟨a, hSK a.2⟩, a.2, rfl⟩
  have hb : e ⟨b, hSK b.2⟩ ∈ (P : Subgroup PSL(2, GaloisField 2 3)) := hP ⟨⟨b, hSK b.2⟩, b.2, rfl⟩
  have hc : e ⟨a, hSK a.2⟩ * e ⟨b, hSK b.2⟩ = e ⟨b, hSK b.2⟩ * e ⟨a, hSK a.2⟩ :=
    congrArg Subtype.val (hPel.toIsMulCommutative.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  rw [← map_mul, ← map_mul] at hc
  simpa using congrArg Subtype.val (e.injective hc)

theorem exists_involution_of_psl28 (e : K ≃* PSL(2, GaloisField 2 3)) (hidx : K.index = 3)
    (hKc : centralizer (K : Set X) = ⊥) :
    ∃ t σ : X, orderOf t = 2 ∧ t ∈ K ∧ Nat.card (centralizer ({t} : Set X)) = 24 ∧
      Nat.card ↥(K ⊓ centralizer ({t} : Set X)) = 8 ∧
      (∀ u ∈ K ⊓ centralizer ({t} : Set X), u * u = 1) ∧
      (∀ a ∈ K ⊓ centralizer ({t} : Set X), ∀ b ∈ K ⊓ centralizer ({t} : Set X), a * b = b * a) ∧
      σ ∈ centralizer ({t} : Set X) ∧ orderOf σ = 3 ∧
      ∃ u ∈ K ⊓ centralizer ({t} : Set X), σ * u * σ⁻¹ ≠ u := by
  classical
  obtain ⟨UL⟩ := (inferInstance : Nonempty (Sylow 2 PSL(2, GaloisField 2 3)))
  obtain ⟨hUel, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two (f := 3) (by norm_num) UL
  haveI := hUel
  have hUbot : (UL : Subgroup PSL(2, GaloisField 2 3)) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hUcard
    norm_num at hUcard
  obtain ⟨⟨tL, htLU⟩, htL1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUbot
  have htL1' : tL ≠ 1 := fun h => htL1 (Subtype.ext h)
  have htLo : orderOf tL = 2 :=
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) tL htLU) htL1'
  have hCL : centralizer ({tL} : Set PSL(2, GaloisField 2 3)) = UL :=
    CFSG.Walter.psl2_even_centralizer_involution (f := 3) (by norm_num) UL htLU htL1'
  set t : X := ((e.symm tL : K) : X) with ht
  have htK : t ∈ K := (e.symm tL).2
  have hto : orderOf t = 2 := by rw [ht, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htLo]
  have hmem : ∀ k : K, (k : X) ∈ centralizer ({t} : Set X) ↔
      e k ∈ (UL : Subgroup PSL(2, GaloisField 2 3)) := by
    intro k
    rw [← hCL, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : k * e.symm tL = e.symm tL * k := Subtype.ext h
      simpa using congrArg e h'
    · intro h
      have h' : e.symm (e k * tL) = e.symm (tL * e k) := congrArg e.symm h
      simp only [map_mul, MulEquiv.symm_apply_apply] at h'
      exact congrArg Subtype.val h'
  have hUeq : K ⊓ centralizer ({t} : Set X) =
      (UL : Subgroup PSL(2, GaloisField 2 3)).map (K.subtype.comp e.symm.toMonoidHom) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hxK, hxC⟩
      exact ⟨e ⟨x, hxK⟩, (hmem ⟨x, hxK⟩).mp hxC, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(e.symm v).2, (hmem (e.symm v)).mpr (by simpa using hv)⟩
  have hU8 : Nat.card ↥(K ⊓ centralizer ({t} : Set X)) = 8 := by
    rw [hUeq, Subgroup.card_map_of_injective
      (fun a b h => e.symm.injective (K.subtype_injective h)), hUcard]
    norm_num
  have hU2 : ∀ u ∈ K ⊓ centralizer ({t} : Set X), u * u = 1 := by
    intro u hu
    rw [hUeq] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hv2 : v * v = 1 := by
      rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
    rw [← map_mul, hv2, map_one]
  have hUc : ∀ a ∈ K ⊓ centralizer ({t} : Set X), ∀ b ∈ K ⊓ centralizer ({t} : Set X),
      a * b = b * a := by
    intro a ha b hb
    rw [hUeq] at ha hb
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨w, hw, rfl⟩ := hb
    have hvw : v * w = w * v :=
      congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
    rw [← map_mul, ← map_mul, hvw]
  obtain ⟨x, hxK⟩ : ∃ x : X, x ∉ K := by
    by_contra! h
    have hK : K = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [hK, Subgroup.index_top] at hidx
    norm_num at hidx
  have hyK : x * t * x⁻¹ ∈ K := ‹K.Normal›.conj_mem t htK x
  have hyo : orderOf (e ⟨x * t * x⁻¹, hyK⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ← hto]
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj x) t
  obtain ⟨l, hl⟩ := isConj_iff.mp
    (CFSG.Walter.psl2_even_isConj_of_orderOf_eq_two (f := 3) (by norm_num) hyo htLo)
  have hk : ((e.symm l : K) : X) * (x * t * x⁻¹) * ((e.symm l : K) : X)⁻¹ = t := by
    have h1 : e.symm (l * e ⟨x * t * x⁻¹, hyK⟩ * l⁻¹) = e.symm tL := congrArg e.symm hl
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    exact congrArg Subtype.val h1
  have hcC : ((e.symm l : K) : X) * x ∈ centralizer ({t} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((e.symm l : K) : X) * x * t
        = ((e.symm l : K) : X) * (x * t * x⁻¹) * ((e.symm l : K) : X)⁻¹ *
          (((e.symm l : K) : X) * x) := by group
      _ = t * (((e.symm l : K) : X) * x) := by rw [hk]
  have hcK : ((e.symm l : K) : X) * x ∉ K := fun h =>
    hxK (by simpa using K.mul_mem (K.inv_mem (e.symm l).2) h)
  have hsup : K ⊔ centralizer ({t} : Set X) = ⊤ := by
    have h1 := Subgroup.relIndex_mul_index (le_sup_left : K ≤ K ⊔ centralizer ({t} : Set X))
    rw [hidx] at h1
    have h2 : K.relIndex (K ⊔ centralizer ({t} : Set X)) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => hcK (h (le_sup_right (a := K) hcC))
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (Dvd.intro_left _ h1) with hb | hb
    · exact Subgroup.index_eq_one.mp hb
    · rw [hb] at h1
      omega
  have hrel : K.relIndex (centralizer ({t} : Set X)) = 3 := by
    rw [← Subgroup.relIndex_sup_right, sup_comm, hsup, Subgroup.relIndex_top_right, hidx]
  have hC24 : Nat.card (centralizer ({t} : Set X)) = 24 := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := centralizer ({t} : Set X))
    rw [hrel, hU8] at h
    omega
  obtain ⟨⟨σ, hσC⟩, hσ'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer ({t} : Set X))) 3
    (by rw [hC24]; norm_num)
  have hσ3 : orderOf σ = 3 := (Subgroup.orderOf_mk σ hσC).symm.trans hσ'
  have hσ3' : σ ^ 3 = 1 := by
    rw [← hσ3]
    exact pow_orderOf_eq_one σ
  refine ⟨t, σ, hto, htK, hC24, hU8, hU2, hUc, hσC, hσ3, ?_⟩
  by_contra! hfix
  have hα3 : (MulAut.congr e (MulAut.conjNormal σ)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hσ3', map_one, map_one]
  have hαU : ∀ v ∈ (UL : Subgroup PSL(2, GaloisField 2 3)),
      MulAut.congr e (MulAut.conjNormal σ) v = v := by
    intro v hv
    have hvU : ((e.symm v : K) : X) ∈ K ⊓ centralizer ({t} : Set X) := by
      rw [hUeq]
      exact ⟨v, hv, rfl⟩
    have h1 : MulAut.conjNormal σ (e.symm v) = e.symm v :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hfix _ hvU)
    simp [h1]
  have hα1 := CFSG.ComponentClassification.AS81.psl2_aut_eq_one_of_fix (n := 3) (by norm_num) hUcard
    (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα3)) hαU
  have hσK : σ ∈ centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 : MulAut.congr e (MulAut.conjNormal σ) (e ⟨k, hk⟩) = e ⟨k, hk⟩ := by
      rw [hα1]
      rfl
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    rw [MulAut.conjNormal_apply] at h2
    calc k * σ = σ * k * σ⁻¹ * σ := by rw [h2]
      _ = σ * k := by group
  rw [hKc, Subgroup.mem_bot] at hσK
  rw [hσK, orderOf_one] at hσ3
  norm_num at hσ3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
