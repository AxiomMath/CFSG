module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenBig

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

section Certified


theorem exists_normalizer_conj_of_hyp711 (hTim : TimmesfeldTIRootInput) (h : Hyp711 V H E)
    {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hbig : 2 < Nat.card (barSub (kSub V H E) φ V)) {s t : X}
    (hs : s ∈ barSub (kSub V H E) φ V) (ht : t ∈ barSub (kSub V H E) φ V)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    ∃ m : ↥(kSub V H E), (m : G) ∈ Subgroup.normalizer (V : Set G) ∧
      t = φ m * s * (φ m)⁻¹ := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let S : Subgroup X := barSub (kSub V H E) φ V
  have hsS : s ∈ S := hs
  have htS : t ∈ S := ht
  have hbigS : 2 < Nat.card S := hbig
  have hroot : CFSG.Timmesfeld.IsRootInvolutionSet
      (Group.conjugatesOfSet ((S : Set X) \ {1})) := by
    have hrootSet := isRootInvolutionSet_barSet h.toHyp73 hφ
    rw [barSet_dSet_eq h.toHyp73 h.transitive hφ] at hrootSet
    exact hrootSet
  have hcomm : ∀ g : X, IsPGroup 2 ↥(S ⊔ conjSubgroup S g) →
      ∀ a ∈ S, ∀ b ∈ conjSubgroup S g, a * b = b * a :=
    fun g hg => commute_of_isPGroup_barSub_sup_conj h hφ g hg
  obtain ⟨hconj, -⟩ := hTim X S (isElemAbelian_barSub h.elemAbelian φ) hbigS
    (isTI_barSub h hφ) (normalClosure_barSub_eq_top h hφ) (pCore_eq_bot_of_isBarMap hφ)
    (fusionOddCore_le_center_of_two_lt_card h hφ hbig) hroot hcomm
  obtain ⟨c, hc⟩ := hconj s hsS t htS hs1 ht1
  have hc' : (c : X) * s = t * (c : X) := hc
  have hx : t = (c : X) * s * (c : X)⁻¹ := by
    rw [hc']
    group
  have hti : IsTI S := isTI_barSub h hφ
  have ht_conj : t ∈ CFSG.CGT.Timmesfeld75.conjSubgroup (c : X) S := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have hcs : (c : X)⁻¹ * t * (c : X) = s := by rw [hx]; group
    rw [hcs]
    exact hsS
  have ht_inf : t ∈ S ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (c : X) S := ⟨htS, ht_conj⟩
  have hneinf : S ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (c : X) S ≠ ⊥ := by
    intro hbot
    rw [hbot] at ht_inf
    exact ht1 (Subgroup.mem_bot.mp ht_inf)
  rcases hti (c : X) with hbot | hEq
  · exact absurd hbot hneinf
  · have hle : S ≤ CFSG.CGT.Timmesfeld75.conjSubgroup (c : X) S := by
      intro y hy
      exact (Subgroup.mem_inf.mp (hEq ▸ hy)).2
    have hcard : Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup (c : X) S) ≤ Nat.card S := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup,
        Subgroup.card_map_of_injective (K := S) (f := (MulAut.conj (c : X)).toMonoidHom)
          (MulAut.conj (c : X)).injective]
    have hceq : CFSG.CGT.Timmesfeld75.conjSubgroup (c : X) S = S :=
      (Subgroup.eq_of_le_of_card_ge hle hcard).symm
    have hxnorm : (c : X) ∈ Subgroup.normalizer (S : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hceq
    obtain ⟨k, hk⟩ := hφ.surjective (c : X)
    have hkS : φ k ∈ Subgroup.normalizer (barSub (kSub V H E) φ V : Set X) := by
      rw [hk]
      exact hxnorm
    have hk_comap : k ∈ (Subgroup.normalizer (barSub (kSub V H E) φ V : Set X)).comap φ :=
      Subgroup.mem_comap.mpr hkS
    have hker : φ.ker = (pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E) := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hφ.ker_iff y
    have hVleK : V ≤ kSub V H E := le_kSub h.mem
    have hJleK : pCoreOf 2 (kSub V H E) ≤ kSub V H E :=
      CFSG.LieType.BorelTits.pCoreOf_le (r := 2) _
    have hcomap : (barSub (kSub V H E) φ V).comap φ =
        (V ⊔ pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E) := by
      rw [barSub, Subgroup.comap_map_eq φ (V.subgroupOf (kSub V H E))]
      rw [hker, ← Subgroup.subgroupOf_sup hVleK hJleK]
    have hk_comap2 : k ∈ Subgroup.normalizer ((barSub (kSub V H E) φ V).comap φ) := by
      rwa [Subgroup.comap_normalizer_eq_of_surjective (barSub (kSub V H E) φ V)
        hφ.surjective] at hk_comap
    have hk_sub : k ∈ Subgroup.normalizer
        ((V ⊔ pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E)) := by
      rwa [hcomap] at hk_comap2
    have hk_norm : (k : G) ∈ Subgroup.normalizer
        (V ⊔ pCoreOf 2 (kSub V H E) : Subgroup G) := by
      rw [← Subgroup.mem_subgroupOf,
        Subgroup.subgroupOf_normalizer_eq (H := V ⊔ pCoreOf 2 (kSub V H E))
          (N := kSub V H E) (sup_le hVleK hJleK)]
      exact hk_sub
    obtain ⟨m, hm, j, hjJ, hmj⟩ :=
      seven_three_four_normalizer (V := V) (H := H) (E := E)
        (J := pCoreOf 2 (kSub V H E))
        h.elemAbelian h.ti h.abelian h.le h.normal h.mem h.omega_le
        h.pcore_le h.jnormal h.iSub_le (kSub_le_of_forall_le h.omega_le k.2) hk_norm
    have hmK : m ∈ kSub V H E := by
      have hm_eq : m = k * j⁻¹ := by rw [hmj]; group
      rw [hm_eq]
      exact (kSub V H E).mul_mem k.2 ((kSub V H E).inv_mem (hJleK hjJ))
    have hphi_m : φ ⟨m, hmK⟩ = φ k := by
      have hj1 : φ ⟨j, hJleK hjJ⟩ = 1 := (hφ.ker_iff _).mpr hjJ
      have hmj' : (⟨m, hmK⟩ : ↥(kSub V H E)) = k * ⟨j, hJleK hjJ⟩⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        rw [hmj]
        group
      rw [hmj', map_mul, map_inv, hj1, inv_one, mul_one]
    refine ⟨⟨m, hmK⟩, hm.2, ?_⟩
    rw [hphi_m, hk]
    exact hx

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
