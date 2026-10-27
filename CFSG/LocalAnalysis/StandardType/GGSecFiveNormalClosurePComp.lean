module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompPCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallImage

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section PComp

variable {G : Type} [Group G] [Finite G]

theorem largeEvenPPrimeCoreOf_inf_le {p : ℕ} [Fact p.Prime] {H J : Subgroup G} (hJH : J ≤ H) :
    LargeEvenPPrimeCoreOf p H ⊓ J ≤ LargeEvenPPrimeCoreOf p J := by
  refine ggLe_pPrimeCoreOf inf_le_right (fun g hg => ggMem_normalizer_inf_of ?_
    (Subgroup.le_normalizer hg)) ?_
  · exact ggNormalizer_le_normalizer_pPrimeCoreOf p H (Subgroup.le_normalizer (hJH hg))
  · exact (ggPPrimeCoreOf_coprime H).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)

theorem eq_one_of_mem_largeEvenPPrimeCoreOf {p : ℕ} [Fact p.Prime] {H : Subgroup G} {u : G}
    (hu : u ∈ LargeEvenPPrimeCoreOf p H) (hup : u ^ p = 1) : u = 1 := by
  have h1 : orderOf u ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hup
  have h2 : orderOf u ∣ Nat.card (LargeEvenPPrimeCoreOf p H) :=
    (LargeEvenPPrimeCoreOf p H).orderOf_dvd_natCard hu
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (ggPPrimeCoreOf_coprime H) h1 h2)

theorem inf_largeEvenPPrimeCoreOf_eq_bot {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) (H : Subgroup G) : E ⊓ LargeEvenPPrimeCoreOf p H = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨huE, huO⟩ := Subgroup.mem_inf.mp hu
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_largeEvenPPrimeCoreOf huO (hE.2 u huE))

theorem eq_iSup_conj_of_pComponent {p : ℕ} [Fact p.Prime] {H X J : Subgroup G}
    (hX : LargeEvenPComponent p H X) (hJX : J ≤ X) (hJ : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J) :
    X = ⨆ (a : G) (_ : a ∈ X), J.map (MulAut.conj a⁻¹).toMonoidHom := by
  have hXH : X ≤ H := hX.1
  have hJH : J ≤ H := hJX.trans hXH
  set N : Subgroup G := ⨆ (a : G) (_ : a ∈ X), J.map (MulAut.conj a⁻¹).toMonoidHom with hN
  have hJN : J ≤ N := by
    rw [hN]
    have h : J.map (MulAut.conj (1 : G)⁻¹).toMonoidHom ≤
        ⨆ (a : G) (_ : a ∈ X), J.map (MulAut.conj a⁻¹).toMonoidHom :=
      le_iSup₂ (f := fun (a : G) (_ : a ∈ X) => J.map (MulAut.conj a⁻¹).toMonoidHom) 1
        (X.one_mem)
    have h1 : J.map (MulAut.conj (1 : G)⁻¹).toMonoidHom = J := by
      rw [inv_one, map_one]
      exact Subgroup.map_id J
    rwa [h1] at h
  have hNX : N ≤ X := by
    rw [hN]
    refine iSup₂_le fun a ha => ?_
    exact (Subgroup.map_mono hJX).trans (le_of_eq (map_conj_eq_of_mem (X.inv_mem ha)))
  have hNnorm : X ≤ Subgroup.normalizer (N : Set G) := by
    refine le_normalizer_of_map_conj_le fun b hb => ?_
    rw [hN]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    refine iSup_le fun ha => ?_
    rw [map_conj_map_conj]
    have hba : b * a⁻¹ = (a * b⁻¹)⁻¹ := by group
    rw [hba]
    exact le_iSup₂ (f := fun (a : G) (_ : a ∈ X) => J.map (MulAut.conj a⁻¹).toMonoidHom)
      (a * b⁻¹) (X.mul_mem ha (X.inv_mem hb))
  have hNsub : IsSubnormal N H :=
    IsSubnormal.step hNX ((Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hNnorm) hX.2.1
  by_contra hne
  have hNXlt : N < X := lt_of_le_of_ne hNX (Ne.symm hne)
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore p ↥H) with hπ
  have hmin : (N.subgroupOf H).map π ≠ (X.subgroupOf H).map π := hX.2.2.2 N hNXlt hNsub
  have hNbar_le : (N.subgroupOf H).map π ≤ (X.subgroupOf H).map π :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hNX)
  have hXbar_norm : (X.subgroupOf H).map π ≤ Subgroup.normalizer
      (((N.subgroupOf H).map π : Subgroup (↥H ⧸ LargeEvenPPrimeCore p ↥H)) :
        Set (↥H ⧸ LargeEvenPPrimeCore p ↥H)) :=
    ggMap_le_normalizer_map p hNnorm
  have hXbar_qs : CFSG.Assembly.IsQuasisimple ↥((X.subgroupOf H).map π) := hX.2.2.1.2.2
  rcases ggLe_center_or_eq_of_normalized hXbar_qs hNbar_le hXbar_norm with hcent | heq
  · have hJbar_le_N : (J.subgroupOf H).map π ≤ (N.subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono H hJN)
    have hJbar_le_X : (J.subgroupOf H).map π ≤ (X.subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono H hJX)
    have hcomm : ⁅(J.subgroupOf H).map π, (J.subgroupOf H).map π⁆ = ⊥ := by
      have h1 : ⁅(J.subgroupOf H).map π, (J.subgroupOf H).map π⁆ ≤
          ⁅(N.subgroupOf H).map π, (X.subgroupOf H).map π⁆ :=
        Subgroup.commutator_mono hJbar_le_N hJbar_le_X
      have h2 : ⁅(N.subgroupOf H).map π, (X.subgroupOf H).map π⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
      rw [h2] at h1
      exact le_bot_iff.mp h1
    have himgJJ : ⁅(J.subgroupOf H).map π, (J.subgroupOf H).map π⁆ = (J.subgroupOf H).map π := by
      rw [← Subgroup.map_commutator, ← ggSubgroupOf_commutator hJH hJH, hJ]
    have hJbot : (J.subgroupOf H).map π = ⊥ := by
      rw [← himgJJ]
      exact hcomm
    have hJW : J ≤ LargeEvenPPrimeCoreOf p H := ggLe_pPrimeCoreOf_of_map_eq_bot p hJH hJbot
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
      ((ggPPrimeCoreOf_coprime H).coprime_dvd_right (Subgroup.card_dvd_of_le hJW)) hpJ
  · exact hmin heq

theorem le_iSup_conj_pLayer_of_pComponent {p : ℕ} [Fact p.Prime] {H X J : Subgroup G}
    (hX : LargeEvenPComponent p H X) (hJX : J ≤ X) (hJ : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J) :
    X ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p H), J.map (MulAut.conj a⁻¹).toMonoidHom := by
  have hXP : X ≤ LargeEvenPLayer p H := by
    unfold LargeEvenPLayer
    exact le_sSup hX
  rw [eq_iSup_conj_of_pComponent hX hJX hJ hpJ]
  refine iSup₂_le fun a ha => ?_
  exact le_iSup₂ (f := fun (a : G) (_ : a ∈ LargeEvenPLayer p H) =>
    J.map (MulAut.conj a⁻¹).toMonoidHom) a (hXP ha)

end PComp

end CFSG.StandardType
