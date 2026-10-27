module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPBar
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

private theorem wc85om_exists_mul_eq_of_mem_sup_of_le_normalizer {S N : Subgroup G}
    (hN : S ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ S ⊔ N) :
    ∃ s ∈ S, ∃ n ∈ N, s * n = x := by
  have hx' : x ∈ (↑(S ⊔ N) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S N hN, Set.mem_mul] at hx'
  exact hx'

private theorem wc85om_conjSubgroup_zpowers (t g : X) :
    conjSubgroup (Subgroup.zpowers t) g = Subgroup.zpowers (g⁻¹ * t * g) := by
  change (Subgroup.zpowers t).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  congr 1
  simp [MulAut.conj_apply]

theorem exists_conjSubgroup_eq_of_mem_omegaHIn (s : TailSetup V H T φ) {U : Subgroup G}
    (hU : U ∈ omegaHIn V H) : ∃ k : ↥(kGenIn V H), U = conjSubgroup V (k : G) := by
  rw [omegaHIn] at hU
  obtain ⟨h, hhH, rfl⟩ := hU
  have hTN : T ≤ Subgroup.normalizer (kGenIn V H : Set G) :=
    le_trans s.hyp83.T_le_H (s.hyp83.le_normalizer_kGenIn_of_eq_sup s.eq_sup)
  have hh : h ∈ T ⊔ kGenIn V H := by
    rw [sup_comm, ← s.eq_sup]
    exact hhH
  obtain ⟨t₀, ht₀T, k, hkK, htk⟩ :=
    wc85om_exists_mul_eq_of_mem_sup_of_le_normalizer hTN hh
  have hconj : conjSubgroup V h = conjSubgroup V k := by
    rw [htk.symm, ← conjSubgroup_conjSubgroup V t₀ k,
      conjSubgroup_eq_iff_mem_normalizer.mpr (s.hyp83.T_le_normalizer ht₀T)]
  exact ⟨⟨k, hkK⟩, hconj⟩

theorem kGenIn_le_centralizer_of_comm_omegaHIn (hVH : V ≤ H) {U : Subgroup G}
    (hU : ∀ W ∈ omegaHIn V H, ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) :
    kGenIn V H ≤ Subgroup.centralizer (U : Set G) := by
  refine iSup₂_le fun k hk => ?_
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact hU (conjSubgroup V k) ⟨k, conjClosure_le_of_le_H hVH hk, rfl⟩ u hu w hw

theorem conjSubgroup_le_T_iff_mem_symT (s : TailSetup V H T φ) {t : X}
    (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t) {P : Sylow 2 X}
    (hP : (P : Subgroup X) = barSub (kGenIn V H) φ T) (k : ↥(kGenIn V H)) :
    conjSubgroup V (k : G) ≤ T ↔ (φ k)⁻¹ * t * φ k ∈ symT t (P : Subgroup X) := by
  rw [conjSubgroup_le_iff_barSub_le s (kGenIn_le_H s.hyp83.le_H k.2)]
  rw [barSub_conjSubgroup φ V k, ht, ← hP, symT, Set.mem_inter_iff, Set.mem_setOf_eq,
    wc85om_conjSubgroup_zpowers, Subgroup.zpowers_le]
  constructor
  · intro hmem
    exact ⟨isConj_iff.mpr ⟨(φ k)⁻¹, by rw [inv_inv]⟩, hmem⟩
  · rintro ⟨_, hmem⟩
    exact hmem

end CFSG.LocalAnalysis.WeakClosure81

end
