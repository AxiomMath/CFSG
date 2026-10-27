module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Out
public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Ti
public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Cfg

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

namespace W183L34

open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four

theorem exists_embedding {Y : Type} [Group Y] (L : Subgroup Y)
    (hLn : L.Normal) (hC : Subgroup.centralizer (L : Set Y) = ⊥) (hL : IsL3 ↥L 2) :
    ∃ ι : Y →* Equiv.Perm (Fin 42), Function.Injective ι ∧ (∀ y, ι y ∈ R) ∧
      L.map ι = S := by
  obtain ⟨θ⟩ :=
    CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL
  haveI : L.Normal := hLn
  have hA : CFSG.Sporadic.SmallOddCore.AutModel S R :=
    CFSG.GH74.GLS.IVK.l34_autModel
  refine ⟨hA.embed L θ, hA.embed_injective L θ hC, fun y => hA.embed_mem L θ y, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    exact (hA.embed_coe L θ ⟨y, hy⟩).symm ▸ (θ ⟨y, hy⟩).2
  · intro hx
    refine ⟨((θ.symm ⟨x, hx⟩ : L) : Y), (θ.symm ⟨x, hx⟩).2, ?_⟩
    rw [hA.embed_coe L θ (θ.symm ⟨x, hx⟩)]
    simpa using congrArg Subtype.val (θ.apply_symm_apply ⟨x, hx⟩)

theorem g3_core
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAR : A ≤ R)
    (hcard : Nat.card A = 4) (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ S, g * t = t * g → ∀ a ∈ A, g * a = a * g) :
    A ≤ S ∧ ∃ n ∈ S, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  have hAS : A ≤ S := le_S_of_ti1 hAR hcard hel hTI1
  have hnorm : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ S, g * t = t * g →
      g ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42))) := by
    intro t ht ht1 g hgS hgt
    refine Subgroup.centralizer_le_normalizer (A : Set (Equiv.Perm (Fin 42))) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hTI1 t ht ht1 g hgS hgt a ha).symm
  obtain ⟨k, hkS, hk⟩ := exists_conj_Z0 hAS hcard hel hnorm
  obtain ⟨n, hnS, hnZ, hnfpf⟩ := exists_fpf_Z0
  refine ⟨hAS, k * n * k⁻¹, S.mul_mem (S.mul_mem hkS hnS) (S.inv_mem hkS), ?_, ?_⟩
  · intro x hx
    have hz : (MulAut.conj k⁻¹).toMonoidHom x ∈ Z0 := by
      rw [← hk]
      exact Subgroup.mem_map_of_mem _ hx
    have hz' : n * ((MulAut.conj k⁻¹).toMonoidHom x) * n⁻¹ ∈ Z0 := hnZ _ hz
    have heq : (MulAut.conj k⁻¹).toMonoidHom (k * n * k⁻¹ * x * (k * n * k⁻¹)⁻¹) =
        n * ((MulAut.conj k⁻¹).toMonoidHom x) * n⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hmem : (MulAut.conj k⁻¹).toMonoidHom (k * n * k⁻¹ * x * (k * n * k⁻¹)⁻¹) ∈
        A.map (MulAut.conj k⁻¹).toMonoidHom := by
      rw [heq, hk]
      exact hz'
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.1 hmem
    have hxa : k * n * k⁻¹ * x * (k * n * k⁻¹)⁻¹ = a :=
      ((MulAut.conj k⁻¹).injective haeq).symm
    rw [hxa]
    exact ha
  · intro x hx hx1 hfix
    have hz : (MulAut.conj k⁻¹).toMonoidHom x ∈ Z0 := by
      rw [← hk]
      exact Subgroup.mem_map_of_mem _ hx
    have hz1 : (MulAut.conj k⁻¹).toMonoidHom x ≠ 1 := by
      intro h
      exact hx1 ((MulAut.conj k⁻¹).injective (h.trans (MulAut.conj k⁻¹).map_one.symm))
    refine hnfpf _ hz hz1 ?_
    have heq : (MulAut.conj k⁻¹).toMonoidHom (k * n * k⁻¹ * x * (k * n * k⁻¹)⁻¹) =
        n * ((MulAut.conj k⁻¹).toMonoidHom x) * n⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [← heq, hfix]

end W183L34

theorem finG3L34_holds
    (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (hLn : L.Normal) (hL : IsL3 ↥L 2)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (A : Subgroup Y) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) :
    A ≤ L ∧ ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  obtain ⟨ι, hι, hιR, hιL⟩ := W183L34.exists_embedding L hLn hC hL
  set A' : Subgroup (Equiv.Perm (Fin 42)) := A.map ι with hA'
  have hA'R : A' ≤ CFSG.ComponentClassification.PSL3Four.R := by
    intro x hx
    rw [hA'] at hx
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact hιR a
  have hA'card : Nat.card A' = 4 := by
    rw [hA', Subgroup.card_map_of_injective hι, hcard]
  have hA'el : IsElemAbelian 2 A' := by
    rw [hA']
    exact W183L34.isElemAbelian_map ι hel
  have hA'TI : ∀ t ∈ A', t ≠ 1 → ∀ g ∈ CFSG.ComponentClassification.PSL3Four.S,
      g * t = t * g → ∀ a ∈ A', g * a = a * g := by
    intro t htA ht1 g hgS hgt a haA
    rw [hA'] at htA haA
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.1 htA
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 haA
    have hgS' : g ∈ L.map ι := by rwa [← hιL] at hgS
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hgS'
    have ht₁ : t₀ ≠ 1 := fun h => ht1 (by rw [h, map_one])
    have hgt₀ : g₀ * t₀ = t₀ * g₀ := hι (by rw [map_mul, map_mul]; exact hgt)
    show ι g₀ * ι a₀ = ι a₀ * ι g₀
    simpa using congrArg ι (hTI1 t₀ ht₀ ht₁ g₀ hg₀ hgt₀ a₀ ha₀)
  obtain ⟨hA'S, n', hn'S, hn'norm, hn'fpf⟩ := W183L34.g3_core hA'R hA'card hA'el hA'TI
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxS : ι x ∈ CFSG.ComponentClassification.PSL3Four.S :=
      hA'S (Subgroup.mem_map_of_mem ι hx)
    have hximg : ι x ∈ L.map ι := by rwa [← hιL] at hxS
    obtain ⟨l, hl, hlι⟩ := Subgroup.mem_map.1 hximg
    rwa [hι hlι] at hl
  · have hn'img : n' ∈ L.map ι := by rwa [← hιL] at hn'S
    obtain ⟨n, hn, hnι⟩ := Subgroup.mem_map.1 hn'img
    refine ⟨n, hn, ?_, ?_⟩
    · intro x hx
      have hx' : ι x ∈ A' := Subgroup.mem_map_of_mem ι hx
      have hmem : n' * ι x * n'⁻¹ ∈ A' := hn'norm (ι x) hx'
      rw [hA'] at hmem
      obtain ⟨a, ha, haι⟩ := Subgroup.mem_map.1 hmem
      have hxa : n * x * n⁻¹ = a := by
        apply hι
        rw [map_mul, map_mul, map_inv, hnι]
        exact haι.symm
      rw [hxa]
      exact ha
    · intro x hx hx1 hfix
      have hx' : ι x ∈ A' := Subgroup.mem_map_of_mem ι hx
      have hx1' : ι x ≠ 1 := fun h => hx1 (hι (by rw [h, map_one]))
      refine hn'fpf (ι x) hx' hx1' ?_
      have hthis : n' * ι x * n'⁻¹ = ι (n * x * n⁻¹) := by
        rw [← hnι, map_mul, map_mul, map_inv]
      rw [hthis, hfix]

end CFSG.LocalAnalysis.WeakClosure81

end
