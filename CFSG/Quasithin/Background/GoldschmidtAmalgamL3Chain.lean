module

public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Card

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V) {L : Subgroup D}

include h

theorem conjClosure_conjClosure_le_pCoreOf_left (hL : L ≤ A) :
    conjClosure (conjClosure V B) L ≤ pCoreOf 2 A := by
  refine conjClosure_le fun k hk y hy => ?_
  have hkA : k ∈ A := hL hk
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hkA) y).mp
    (h.conjClosure_le_pCoreOf_left hy)

theorem commutator_conjSub_eq_bot (hL : L ≤ A)
    (hQ : conjClosure (conjClosure V B) L ≤ pCoreOf 2 B) {k : D}
    (hk : k ∈ L) : ⁅conjClosure V B, conjSub k (conjClosure V B)⁆ = ⊥ := by
  have hkA : k ∈ A := hL hk
  by_cases hkT : k ∈ A ⊓ B
  · rw [F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V B hkT.2)]
    exact commutator_self_eq_bot h.abelian
  · refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun u hu w hw => ?_)
    rw [Subgroup.mem_bot]
    have hwQ : w ∈ pCoreOf 2 B := hQ (HypF91.conjSub_le_conjClosure hk hw)
    have h1 : u * w * u⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := h.commutator_mem u hu w hwQ
    have hy : k⁻¹ * w * k ∈ conjClosure V B := mem_conjSub.mp hw
    have hu' : k⁻¹ * u * k ∈ pCoreOf 2 B := by
      have hmem : k⁻¹ * u * k⁻¹⁻¹ ∈ conjSub k⁻¹ (conjClosure V B) := mul_mem_conjSub hu
      rw [inv_inv] at hmem
      exact hQ (HypF91.conjSub_le_conjClosure (Subgroup.inv_mem _ hk) hmem)
    have h2 := h.commutator_mem _ hy _ hu'
    have h2' : k * ((k⁻¹ * w * k) * (k⁻¹ * u * k) * (k⁻¹ * w * k)⁻¹ * (k⁻¹ * u * k)⁻¹) * k⁻¹ ∈
        Subgroup.zpowers (k * z * k⁻¹) := by
      rw [← conjSub_zpowers]
      exact mul_mem_conjSub h2
    have e : k * ((k⁻¹ * w * k) * (k⁻¹ * u * k) * (k⁻¹ * w * k)⁻¹ * (k⁻¹ * u * k)⁻¹) * k⁻¹ =
        w * u * w⁻¹ * u⁻¹ := by group
    rw [e] at h2'
    have h3 : u * w * u⁻¹ * w⁻¹ ∈ Subgroup.zpowers (k * z * k⁻¹) := by
      have := Subgroup.inv_mem _ h2'
      have e' : (w * u * w⁻¹ * u⁻¹)⁻¹ = u * w * u⁻¹ * w⁻¹ := by group
      rwa [e'] at this
    by_contra hne
    have hz1 : u * w * u⁻¹ * w⁻¹ = z := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
      rcases zpow_eq_one_or_self h.natural.z_sq m with e1 | e1
      · exact absurd (hm.symm.trans e1) hne
      · exact hm.symm.trans e1
    have hz2 : u * w * u⁻¹ * w⁻¹ = k * z * k⁻¹ := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h3
      have hsq : (k * z * k⁻¹) ^ 2 = 1 := by
        rw [conj_pow, h.natural.z_sq]; group
      rcases zpow_eq_one_or_self hsq m with e1 | e1
      · exact absurd (hm.symm.trans e1) hne
      · exact hm.symm.trans e1
    have hcomm : k * z * k⁻¹ = z := hz2.symm.trans hz1
    exact hkT (inf_normalizer_zpowers_le h.gold h.natural
      ⟨hkA, mem_normalizer_zpowers_of_mul_comm (mul_eq_of_conj_eq hcomm)⟩)

theorem isElemAbelian_of_le_pCoreOf_right (hL : L ≤ A)
    (hQ : conjClosure (conjClosure V B) L ≤ pCoreOf 2 B) :
    IsElemAbelian 2 (conjClosure (conjClosure V B) L) :=
  HypF91.isElemAbelian_conjClosure_of_forall h.abelian fun _ hk =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h.commutator_conjSub_eq_bot hL hQ hk)

theorem le_coreIn_of_isElemAbelian (hL : L ≤ A)
    (hab : IsElemAbelian 2 (conjClosure (conjClosure V B) L)) :
    conjClosure (conjClosure V B) L ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  rw [← h.pCoreOf_inf_centralizer_eq_coreIn]
  intro w hw
  have hwA : w ∈ pCoreOf 2 A := h.conjClosure_conjClosure_le_pCoreOf_left hL hw
  have hwB : w ∈ B := (h.gold.pCoreOf_left_le hwA).2
  have hcomm : ∀ u ∈ conjClosure V B, u * w = w * u := fun u hu =>
    isElemAbelian_comm hab (le_conjClosure (conjClosure V B) L hu) hw
  have hQ : w ∈ pCoreOf 2 B := by
    rw [h.pCoreOf_eq_centralizerMod]
    refine ⟨hwB, mem_normalizer_zpowers_of_mul_comm (mul_eq_of_conj_eq (h.central w hwB)),
      fun u hu => ?_⟩
    have : w * u * w⁻¹ * u⁻¹ = 1 := by
      rw [← hcomm u hu]; group
    rw [this]; exact Subgroup.one_mem _
  exact ⟨hQ, Subgroup.mem_centralizer_iff.mpr fun u hu => hcomm u hu⟩

theorem conjClosure_conjClosure_tfae (hL : L ≤ A) :
    List.TFAE [conjClosure (conjClosure V B) L ≤ pCoreOf 2 B,
      IsElemAbelian 2 (conjClosure (conjClosure V B) L),
      conjClosure (conjClosure V B) L ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B] := by
  tfae_have 1 → 2 := h.isElemAbelian_of_le_pCoreOf_right hL
  tfae_have 2 → 3 := h.le_coreIn_of_isElemAbelian hL
  tfae_have 3 → 1 := fun hle => hle.trans
    ((coreIn_le_right _ _).trans inf_le_right)
  tfae_finish

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
