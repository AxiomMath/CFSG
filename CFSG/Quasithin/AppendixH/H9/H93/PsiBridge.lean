module

public import CFSG.Quasithin.AppendixH.H9.H93.TvDictionary
public import CFSG.Quasithin.AppendixH.H9.ConjTransport
public import CFSG.Quasithin.AppendixH.H9.H93.S8Defs

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem card_imgPermOf (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {A : Subgroup (MulAut (PairN 4))}
    (hA : A ≤ Mg 4) : Nat.card (imgPermOf ψ A) = Nat.card A := by
  unfold imgPermOf
  rw [Subgroup.card_map_of_injective ψ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem le_Lg_iff_imgPermOf_le_alt (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) :
    A ≤ Lg 4 ↔ imgPermOf ψ A ≤ alternatingGroup (Fin 8) := by
  constructor
  · intro h x hx
    obtain ⟨g, hg, hgA, rfl⟩ := (mem_imgPermOf ψ).1 hx
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 := (mem_Lg_iff_sign ψ hg).1 (h hgA)
    rwa [psiExt_of_mem ψ hg] at h1
  · intro h g hgA
    have hg := hA hgA
    rw [mem_Lg_iff_sign ψ hg, psiExt_of_mem ψ hg]
    exact Equiv.Perm.mem_alternatingGroup.1 (h ((mem_imgPermOf ψ).2 ⟨g, hg, hgA, rfl⟩))

theorem isElemAbelian2_iff_imgPermOf (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) :
    IsElemAbelian2 A ↔ IsElemAb2 (imgPermOf ψ A) := by
  constructor
  · rintro ⟨hcomm, hsq⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      obtain ⟨g, hg, hgA, rfl⟩ := (mem_imgPermOf ψ).1 ha
      obtain ⟨h, hh, hhA, rfl⟩ := (mem_imgPermOf ψ).1 hb
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hcomm g hgA h hhA))
    · intro a ha
      obtain ⟨g, hg, hgA, rfl⟩ := (mem_imgPermOf ψ).1 ha
      rw [← map_pow]
      have h1 : (⟨g, hg⟩ : ↥(Mg 4)) ^ 2 = 1 := Subtype.ext (hsq g hgA)
      rw [h1, map_one]
  · rintro ⟨hcomm, hsq⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      have h1 := hcomm (ψ ⟨a, hA ha⟩) ((mem_imgPermOf ψ).2 ⟨a, hA ha, ha, rfl⟩)
        (ψ ⟨b, hA hb⟩) ((mem_imgPermOf ψ).2 ⟨b, hA hb, hb, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (ψ.injective h1)
    · intro a ha
      have h1 := hsq (ψ ⟨a, hA ha⟩) ((mem_imgPermOf ψ).2 ⟨a, hA ha, ha, rfl⟩)
      rw [← map_pow] at h1
      exact congrArg Subtype.val (ψ.injective (h1.trans (map_one ψ).symm))

theorem conjAut_le_Mg {g : MulAut (PairN 4)} (hg : g ∈ Mg 4) {A : Subgroup (MulAut (PairN 4))}
    (hA : A ≤ Mg 4) : conjAut g A ≤ Mg 4 := by
  rintro _ ⟨a, ha, rfl⟩
  exact mul_mem (mul_mem hg (hA ha)) (inv_mem hg)

theorem imgPermOf_conjAut (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {g : MulAut (PairN 4)}
    (hg : g ∈ Mg 4) {A : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) :
    imgPermOf ψ (conjAut g A) =
      (imgPermOf ψ A).map (MulAut.conj (ψ ⟨g, hg⟩)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨k, hk, hkc, rfl⟩ := (mem_imgPermOf ψ).1 hx
    obtain ⟨a, ha, hak⟩ : ∃ a : MulAut (PairN 4), a ∈ A ∧ g * a * g⁻¹ = k := hkc
    subst hak
    refine ⟨ψ ⟨a, hA ha⟩, (mem_imgPermOf ψ).2 ⟨a, hA ha, ha, rfl⟩, ?_⟩
    show ψ ⟨g, hg⟩ * ψ ⟨a, hA ha⟩ * (ψ ⟨g, hg⟩)⁻¹ = ψ ⟨g * a * g⁻¹, hk⟩
    have key : (⟨g * a * g⁻¹, hk⟩ : ↥(Mg 4)) = ⟨g, hg⟩ * ⟨a, hA ha⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [key, map_mul, map_mul, map_inv]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, haA, rfl⟩ := (mem_imgPermOf ψ).1 hy
    have hk : g * a * g⁻¹ ∈ Mg 4 := mul_mem (mul_mem hg ha) (inv_mem hg)
    refine (mem_imgPermOf ψ).2 ⟨g * a * g⁻¹, hk, conj_mem_conjAut haA, ?_⟩
    show ψ ⟨g * a * g⁻¹, hk⟩ = ψ ⟨g, hg⟩ * ψ ⟨a, ha⟩ * (ψ ⟨g, hg⟩)⁻¹
    have key : (⟨g * a * g⁻¹, hk⟩ : ↥(Mg 4)) = ⟨g, hg⟩ * ⟨a, ha⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [key, map_mul, map_mul, map_inv]

private theorem le_of_imgPermOf_le (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A B : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4)
    (h : imgPermOf ψ A ≤ imgPermOf ψ B) : A ≤ B := by
  intro x hx
  have hxM := hA hx
  obtain ⟨y, hy, hyB, hyx⟩ := (mem_imgPermOf ψ).1 (h ((mem_imgPermOf ψ).2 ⟨x, hxM, hx, rfl⟩))
  have h1 : y = x := congrArg Subtype.val (ψ.injective hyx)
  exact h1 ▸ hyB

theorem exists_conjAut_of_imgPermOf_conj (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A B : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) (hB : B ≤ Mg 4) {g' : Equiv.Perm (Fin 8)}
    (h : (imgPermOf ψ A).map (MulAut.conj g').toMonoidHom = imgPermOf ψ B) :
    ∃ g ∈ Mg 4, conjAut g A = B := by
  have hg : ((ψ.symm g' : ↥(Mg 4)) : MulAut (PairN 4)) ∈ Mg 4 := (ψ.symm g').2
  have h1 : ψ ⟨((ψ.symm g' : ↥(Mg 4)) : MulAut (PairN 4)), hg⟩ = g' := ψ.apply_symm_apply g'
  refine ⟨_, hg, ?_⟩
  have h2 : imgPermOf ψ (conjAut ((ψ.symm g' : ↥(Mg 4)) : MulAut (PairN 4)) A) =
      imgPermOf ψ B := by
    rw [imgPermOf_conjAut ψ hg hA, h1]
    exact h
  exact le_antisymm (le_of_imgPermOf_le ψ (conjAut_le_Mg hg hA) h2.le)
    (le_of_imgPermOf_le ψ hB h2.ge)

theorem ncard_isTvElt_inter_eq (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) :
    Set.ncard {g : MulAut (PairN 4) | g ∈ A ∧ IsTvElt g} =
      Set.ncard {x : Equiv.Perm (Fin 8) | x ∈ imgPermOf ψ A ∧ x.cycleType = {2, 2, 2, 2}} := by
  refine Set.ncard_congr (fun g _ => psiExt ψ g) ?_ ?_ ?_
  · rintro g ⟨hgA, htv⟩
    have hg := hA hgA
    refine ⟨?_, (isTvElt_iff_cycleType ψ hg).1 htv⟩
    rw [psiExt_of_mem ψ hg]
    exact (mem_imgPermOf ψ).2 ⟨g, hg, hgA, rfl⟩
  · rintro g g' ⟨hgA, -⟩ ⟨hgA', -⟩ h
    have hg := hA hgA
    have hg' := hA hgA'
    rw [psiExt_of_mem ψ hg, psiExt_of_mem ψ hg'] at h
    exact congrArg Subtype.val (ψ.injective h)
  · rintro x ⟨hx, hcyc⟩
    obtain ⟨g, hg, hgA, rfl⟩ := (mem_imgPermOf ψ).1 hx
    refine ⟨g, ⟨hgA, (isTvElt_iff_cycleType ψ hg).2 ?_⟩, psiExt_of_mem ψ hg⟩
    rw [psiExt_of_mem ψ hg]
    exact hcyc

end CFSG.ASVolI.ChH
