module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Inversion
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.SignalizerFunctorTheorem.NonLocalExc

private theorem map_injective_of_injective {G N : Type*} [Group G] [Group N]
    (f : G →* N) (hf : Function.Injective f) {H K : Subgroup G}
    (h : H.map f = K.map f) : H = K := by
  apply le_antisymm
  · intro x hx
    exact (Subgroup.mem_map_iff_mem hf).mp (h ▸ Subgroup.mem_map_of_mem f hx)
  · intro x hx
    exact (Subgroup.mem_map_iff_mem hf).mp (h.symm ▸ Subgroup.mem_map_of_mem f hx)

private theorem conj_comp {G : Type*} [Group G] (a b : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem pl_all_check :
    Pl.all (fun g => decide (g = 1) || decide (∀ i : Fin 28, g i = i → i = 0)) = true := by
  decide +kernel

private theorem pl_fixed_eq_zero :
    ∀ g ∈ Pl, g ≠ 1 → ∀ i : Fin 28, g i = i → i = 0 := by
  intro g hg hg1 i hi
  have h := List.all_eq_true.mp pl_all_check g hg
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (of_decide_eq_true h) hg1
  · exact of_decide_eq_true h i hi

theorem sylowCenterWeaklyClosed_of_exists_sylow {Y : Type} [Group Y] [Finite Y]
    (Q₀ : Sylow 3 Y)
    (h : ∀ Z : Subgroup Y, Z ≤ (Q₀ : Subgroup Y) →
      Z ≤ Subgroup.centralizer ((Q₀ : Subgroup Y) : Set Y) → Nat.card Z = 3 →
      ∀ g : Y, CFSG.conjugate Z g ≤ (Q₀ : Subgroup Y) → CFSG.conjugate Z g = Z) :
    SylowCenterWeaklyClosed Y := by
  classical
  unfold SylowCenterWeaklyClosed
  intro Q Z hZQ hZc hZcard g hconj
  obtain ⟨h0, hh0⟩ := MulAction.exists_smul_eq Y Q₀ Q
  have hQ : (Q : Subgroup Y) = (Q₀ : Subgroup Y).map (MulAut.conj h0).toMonoidHom := by
    rw [← hh0, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  let x : Y := h0⁻¹
  have hQc : (Q : Subgroup Y) = CFSG.conjugate (Q₀ : Subgroup Y) x := by
    rw [hQ]
    simp [x, CFSG.conjugate]
  have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
      MonoidHom.id Y := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hQx : (Q : Subgroup Y).map (MulAut.conj x).toMonoidHom = (Q₀ : Subgroup Y) := by
    rw [hQc, CFSG.conjugate, Subgroup.map_map, hcomp, Subgroup.map_id]
  let Z0 : Subgroup Y := Z.map (MulAut.conj x).toMonoidHom
  have hZ0conj : Z0 = CFSG.conjugate Z x⁻¹ := by
    simp [Z0, CFSG.conjugate]
  let g' : Y := x * g * x⁻¹
  have hZ0Q0 : Z0 ≤ (Q₀ : Subgroup Y) := by
    have h1 : Z0 ≤ (Q : Subgroup Y).map (MulAut.conj x).toMonoidHom :=
      Subgroup.map_mono hZQ
    rwa [hQx] at h1
  have hZ0c : Z0 ≤ Subgroup.centralizer ((Q₀ : Subgroup Y) : Set Y) := by
    intro z hz
    obtain ⟨z₀, hz₀Z, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : x⁻¹ * y * x ∈ (Q : Subgroup Y) := by
      rw [hQc]
      show x⁻¹ * y * x ∈ (Q₀ : Subgroup Y).map (MulAut.conj x⁻¹).toMonoidHom
      rw [Subgroup.mem_map]
      exact ⟨y, hy, by simp⟩
    have hcomm : (x⁻¹ * y * x) * z₀ = z₀ * (x⁻¹ * y * x) :=
      Subgroup.mem_centralizer_iff.mp (hZc hz₀Z) (x⁻¹ * y * x) hyQ
    have hconj := congrArg (fun t => x * t * x⁻¹) hcomm
    simpa [MulAut.conj_apply, mul_assoc] using hconj
  have hZ0card : Nat.card Z0 = 3 := by
    have hZ0 : Z0 = Z.map (MulAut.conj x).toMonoidHom := rfl
    rw [hZ0, Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective, hZcard]
  have harg : g'⁻¹ * x = x * g⁻¹ := by
    simp only [g']
    group
  have hstep : CFSG.conjugate Z0 g' =
      (CFSG.conjugate Z g).map (MulAut.conj x).toMonoidHom := by
    have hZ0 : Z0 = Z.map (MulAut.conj x).toMonoidHom := rfl
    rw [hZ0, CFSG.conjugate, CFSG.conjugate, Subgroup.map_map, Subgroup.map_map,
      conj_comp, conj_comp, harg]
  have hg' : CFSG.conjugate Z0 g' ≤ (Q₀ : Subgroup Y) := by
    rw [hstep]
    have h2 : (CFSG.conjugate Z g).map (MulAut.conj x).toMonoidHom ≤
        (Q : Subgroup Y).map (MulAut.conj x).toMonoidHom := Subgroup.map_mono hconj
    rwa [hQx] at h2
  have hres : CFSG.conjugate Z0 g' = Z0 := h Z0 hZ0Q0 hZ0c hZ0card g' hg'
  have hkey : CFSG.conjugate (CFSG.conjugate Z x⁻¹) g' = CFSG.conjugate Z x⁻¹ := by
    rw [← hZ0conj]
    exact hres
  rw [CFSG.conjugate_conjugate] at hkey
  have hfinal := congrArg (fun H : Subgroup Y => CFSG.conjugate H x) hkey
  rw [CFSG.conjugate_conjugate, CFSG.conjugate_conjugate] at hfinal
  have harg2 : (x⁻¹ * g') * x = g := by
    simp only [g']
    group
  rw [harg2, inv_mul_cancel, CFSG.conjugate_one] at hfinal
  exact hfinal

theorem sylowCenterWeaklyClosed_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] [Finite Y]
    [Finite Y'] (e : Y ≃* Y') (h : SylowCenterWeaklyClosed Y') : SylowCenterWeaklyClosed Y := by
  classical
  unfold SylowCenterWeaklyClosed at h ⊢
  intro Q Z hZQ hZc hZcard g hconj
  let Q' : Sylow 3 Y' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hQ' : (Q' : Subgroup Y') = (Q : Subgroup Y).map e.toMonoidHom := by
    simp [Q']
  let Z' : Subgroup Y' := Z.map e.toMonoidHom
  let g' : Y' := e g
  have hZ'Q' : Z' ≤ (Q' : Subgroup Y') := by
    rw [hQ']
    exact Subgroup.map_mono hZQ
  have hZ'c : Z' ≤ Subgroup.centralizer ((Q' : Subgroup Y') : Set Y') := by
    rw [hQ']
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    have hcomm := Subgroup.mem_centralizer_iff.mp (hZc hz) q hq
    calc e.toMonoidHom q * e.toMonoidHom z = e.toMonoidHom (q * z) :=
          (map_mul e.toMonoidHom q z).symm
      _ = e.toMonoidHom (z * q) := by rw [hcomm]
      _ = e.toMonoidHom z * e.toMonoidHom q := map_mul e.toMonoidHom z q
  have hZ'card : Nat.card Z' = 3 := by
    have hZ'map : Z' = Z.map e.toMonoidHom := rfl
    rw [hZ'map, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hZcard]
  have hconj'_eq : CFSG.conjugate Z' g' = (CFSG.conjugate Z g).map e.toMonoidHom := by
    simpa [Z', g'] using (CFSG.map_conjugate e.toMonoidHom Z g).symm
  have hconj' : CFSG.conjugate Z' g' ≤ (Q' : Subgroup Y') := by
    rw [hconj'_eq, hQ']
    exact Subgroup.map_mono hconj
  have hres : CFSG.conjugate Z' g' = Z' := h Q' Z' hZ'Q' hZ'c hZ'card g' hconj'
  have hmap : (CFSG.conjugate Z g).map e.toMonoidHom = Z.map e.toMonoidHom := by
    rw [← hconj'_eq, hres]
  exact map_injective_of_injective e.toMonoidHom e.injective hmap

theorem sylowCenterWeaklyClosed_of_lieModel_psu3
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Blueprint.LieModel Y .PSU 3 3 1) :
    SylowCenterWeaklyClosed Y := by
  classical
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hY
  refine sylowCenterWeaklyClosed_of_mulEquiv e ?_
  let P : Subgroup (Equiv.Perm (Fin 28)) := CFSG.GH74.KGroups.U33.QP.originalSubgroup
  have hPcard : Nat.card P = 6048 := by
    rw [show P = CFSG.GH74.KGroups.U33.QP.originalSubgroup from rfl]
    rw [CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.U33.QP
      CFSG.GH74.KGroups.U33.QP_ok]
    exact (CFSG.GH74.KGroups.U33.QP_valid).2
  have hPsub_le : Psub ≤ P := by
    intro gp hgp
    exact (mem_Psub.mp hgp).1
  let Qsub : Subgroup ↥P := Psub.subgroupOf P
  have hQsub_card : Nat.card Qsub = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPsub_le).toEquiv]
    exact card_Psub
  have hQsub_p : IsPGroup 3 Qsub := IsPGroup.of_card (n := 3) (by rw [hQsub_card]; norm_num)
  have hQsub_index : ¬ 3 ∣ Qsub.index := by
    rw [Subgroup.index_eq_card_div, hQsub_card, hPcard]
    norm_num
  let Q0 : Sylow 3 ↥P := hQsub_p.toSylow hQsub_index
  have hQ0_coe : (Q0 : Subgroup ↥P) = Qsub := rfl
  refine sylowCenterWeaklyClosed_of_exists_sylow Q0 ?_
  intro Z hZQ hZc hZcard g hconj
  have hZbar_sub : Z.map P.subtype ≤ Psub := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hzQ : z ∈ Qsub := hQ0_coe ▸ hZQ hz
    exact Subgroup.mem_subgroupOf.mp hzQ
  have hZbar_cent : Z.map P.subtype ≤
      Subgroup.centralizer (Psub : Set (Equiv.Perm (Fin 28))) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpQ : (⟨p, hPsub_le hp⟩ : ↥P) ∈ (Q0 : Subgroup ↥P) :=
      hQ0_coe.symm ▸ Subgroup.mem_subgroupOf.mpr hp
    have hcomm := Subgroup.mem_centralizer_iff.mp (hZc hz)
      (⟨p, hPsub_le hp⟩ : ↥P) hpQ
    simpa using congrArg Subtype.val hcomm
  have hZbar_card : Nat.card (Z.map P.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hZcard]
  have hZcenter : Z.map P.subtype = Subgroup.zpowers U33Inversion.u33z := by
    have hle : Z.map P.subtype ≤ Subgroup.zpowers U33Inversion.u33z := by
      rw [← U33Inversion.u33_center_eq]
      exact le_inf hZbar_sub hZbar_cent
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hZbar_card, Nat.card_zpowers,
      orderOf_eq_prime U33Inversion.u33_z_cube U33Inversion.u33_z_ne_one]
  have hu33z_mem : U33Inversion.u33z ∈ Z.map P.subtype := by
    rw [hZcenter]
    exact Subgroup.mem_zpowers U33Inversion.u33z
  obtain ⟨z0, hz0Z, hz0val⟩ := Subgroup.mem_map.mp hu33z_mem
  have hu33z_center : U33Inversion.u33z ∈
      Psub ⊓ Subgroup.centralizer (Psub : Set (Equiv.Perm (Fin 28))) := by
    rw [U33Inversion.u33_center_eq]
    exact Subgroup.mem_zpowers U33Inversion.u33z
  let γ : Equiv.Perm (Fin 28) := g
  let w : Equiv.Perm (Fin 28) := MulAut.conj γ⁻¹ U33Inversion.u33z
  have hw_Q0 : g⁻¹ * z0 * g ∈ (Q0 : Subgroup ↥P) := by
    have hh := hconj (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hz0Z)
    simpa [MulAut.conj_apply] using hh
  have hu33z_Pl : U33Inversion.u33z ∈ Pl :=
    mem_Pl.mpr (mem_Psub.mp U33Inversion.u33_z_mem_Psub)
  have hw_sub : w ∈ Psub := by
    have h1 : ((g⁻¹ * z0 * g : ↥P) : Equiv.Perm (Fin 28)) ∈ Psub := by
      apply Subgroup.mem_subgroupOf.mp
      exact hw_Q0
    have hval : ((g⁻¹ * z0 * g : ↥P) : Equiv.Perm (Fin 28)) = w := by
      have hz0val' : (z0 : Equiv.Perm (Fin 28)) = U33Inversion.u33z := hz0val
      simp [w, γ, hz0val', MulAut.conj_apply]
    rwa [hval] at h1
  have hw0 : w 0 = 0 := (mem_Psub.mp hw_sub).2.1
  have hg0 : (g : Equiv.Perm (Fin 28)) 0 = 0 := by
    have hfix : U33Inversion.u33z (γ 0) = γ 0 := by
      have h1 : γ⁻¹ (U33Inversion.u33z (γ 0)) = 0 := by
        simpa [w, γ, MulAut.conj_apply, Equiv.Perm.mul_apply] using hw0
      have h2 := congrArg γ h1
      simpa using h2
    exact pl_fixed_eq_zero U33Inversion.u33z hu33z_Pl U33Inversion.u33_z_ne_one (γ 0) hfix
  have hgB : (g : Equiv.Perm (Fin 28)) ∈ Bsub := by
    rw [mem_Bsub]
    exact ⟨g.2, hg0⟩
  have hPl_of_Psub : ∀ {p : Equiv.Perm (Fin 28)}, p ∈ Psub → p ∈ Pl :=
    fun hp => mem_Pl.mpr (mem_Psub.mp hp)
  have hPsub_of_Pl : ∀ {p : Equiv.Perm (Fin 28)}, p ∈ Pl → p ∈ Psub :=
    fun hp => mem_Psub.mpr (mem_Pl.mp hp)
  have hBl_of_Bsub : ∀ {x : Equiv.Perm (Fin 28)}, x ∈ Bsub → x ∈ Bl :=
    fun hx => mem_Bl.mpr (mem_Bsub.mp hx)
  have hnorm : ∀ p ∈ Psub, γ * p * γ⁻¹ ∈ Psub := fun p hp =>
    hPsub_of_Pl (Bl_norm γ (hBl_of_Bsub hgB) p (hPl_of_Psub hp))
  have hw_cent : w ∈ Subgroup.centralizer (Psub : Set (Equiv.Perm (Fin 28))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hgp : γ * p * γ⁻¹ ∈ Psub := hnorm p hp
    have hcomm : (γ * p * γ⁻¹) * U33Inversion.u33z =
        U33Inversion.u33z * (γ * p * γ⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hu33z_center.2 (γ * p * γ⁻¹) hgp
    have hconj := congrArg (fun t => γ⁻¹ * t * γ) hcomm
    simpa [w, MulAut.conj_apply, mul_assoc] using hconj
  have hw_zpow : w ∈ Subgroup.zpowers U33Inversion.u33z := by
    rw [← U33Inversion.u33_center_eq]
    exact ⟨hw_sub, hw_cent⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← Subgroup.mem_map_iff_mem P.subtype_injective]
    rw [hZcenter]
    have hz_mem : (z : Equiv.Perm (Fin 28)) ∈ Subgroup.zpowers U33Inversion.u33z := by
      rw [← hZcenter]
      exact Subgroup.mem_map_of_mem P.subtype hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz_mem
    have hx_conj : P.subtype ((MulAut.conj g⁻¹).toMonoidHom z) =
        (MulAut.conj γ⁻¹).toMonoidHom (P.subtype z) := by
      simp [γ]
    have hk' : U33Inversion.u33z ^ k = P.subtype z := hk
    have hx_eq : P.subtype ((MulAut.conj g⁻¹).toMonoidHom z) = w ^ k := by
      rw [hx_conj, ← hk']
      simp only [w]
      exact map_zpow (MulAut.conj γ⁻¹).toMonoidHom U33Inversion.u33z k
    rw [hx_eq]
    exact Subgroup.zpow_mem (K := Subgroup.zpowers U33Inversion.u33z) hw_zpow k
  · rw [show CFSG.conjugate Z g = Z.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective]

theorem sylowCenterInverted_of_lieModel_psu3
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Blueprint.LieModel Y .PSU 3 3 1) :
    SylowCenterInverted Y := by
  unfold SylowCenterInverted
  intro Q z hzQ hzc hz3
  obtain ⟨t, -, ht⟩ := u33_inverting_of_lieModel hY Q hzQ hzc hz3
  exact ⟨t, ht⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
