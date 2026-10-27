module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup CFSG.Open

theorem map_normalizer_eq_of_odd_ker {Y K : Type} [Group Y] [Finite Y] [Group K] (π : Y →* K)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) {E : Subgroup Y}
    (hE : IsPGroup 2 E) :
    (Subgroup.normalizer (E : Set Y)).map π =
      Subgroup.normalizer ((E.map π : Subgroup K) : Set K) := by
  exact CFSG.ComponentClassification.OddKernelNormalizers.image π hπ hodd E hE

theorem map_setNormalizer_eq_of_odd_ker {Y K : Type} [Group Y] [Finite Y] [Group K] (π : Y →* K)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) {C : Set Y}
    (hC : ∀ g x : Y, x ∈ C → g * x * g⁻¹ ∈ C) {P : Subgroup Y} (hP : IsPGroup 2 P) :
    (Subgroup.normalizer (C ∩ (P : Set Y))).map π =
      Subgroup.normalizer (π '' (C ∩ (P : Set Y))) := by
  let T : Set Y := C ∩ (P : Set Y)
  let Q : Subgroup Y := Subgroup.closure T
  have hT_subset_P : T ⊆ (P : Set Y) := Set.inter_subset_right
  have hQ_le_P : Q ≤ P := (Subgroup.closure_le P).mpr hT_subset_P
  have hQ_two : IsPGroup 2 Q := hP.to_le hQ_le_P
  have hT_eq : T = C ∩ (Q : Set Y) := by
    ext x
    dsimp only [T]
    exact ⟨fun hx => ⟨hx.1, Subgroup.subset_closure hx⟩,
      fun hx => ⟨hx.1, hQ_le_P hx.2⟩⟩
  have hnormalizer_Q_le_T : Subgroup.normalizer (Q : Set Y) ≤ Subgroup.normalizer T := by
    rw [Subgroup.le_set_normalizer_iff]
    intro h hh g hg
    rw [hT_eq] at hg ⊢
    exact ⟨hC h g hg.1, ((Subgroup.mem_set_normalizer_iff.mp hh) g).mp hg.2⟩
  have hmap_le : (Subgroup.normalizer T).map π ≤ Subgroup.normalizer (π '' T) := by
    rw [Subgroup.le_set_normalizer_iff]
    rintro k ⟨g, hg, rfl⟩ x ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, (Subgroup.mem_set_normalizer_iff.mp hg y).mp hy,
      by simp [map_mul, map_inv]⟩
  have hmap_ge : Subgroup.normalizer (π '' T) ≤ (Subgroup.normalizer T).map π := by
    intro k hk
    have hk' : k ∈ Subgroup.normalizer (Subgroup.closure (π '' T)) :=
      Subgroup.normalizer_le_normalizer_closure (π '' T) hk
    have hclosure : Subgroup.closure (π '' T) = Q.map π := by
      rw [← MonoidHom.map_closure]
    rw [hclosure] at hk'
    have hQ : (Subgroup.normalizer Q).map π = Subgroup.normalizer (Q.map π) :=
      map_normalizer_eq_of_odd_ker π hπ hodd hQ_two
    rw [← hQ] at hk'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk'
    exact ⟨y, hnormalizer_Q_le_T hy, rfl⟩
  exact le_antisymm hmap_le hmap_ge

theorem map_setNormalizer_eq {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (_h : SymSetting e t P) :
    (Subgroup.setNormalizer (symT t (P : Subgroup Y))).map (symPi e) =
      Subgroup.setNormalizer (symPi e '' symT t (P : Subgroup Y)) := by
  have hker : (symPi e).ker = fusionOddCore Y := by
    rw [symPi]
    ext z
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card (symPi e).ker) := by
    rw [hker]
    exact CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y
  exact map_setNormalizer_eq_of_odd_ker (symPi e) (w85g_symPi_surjective e) hodd
    (fun g x hx => (hx.trans (isConj_iff.mpr ⟨g, rfl⟩))) P.isPGroup'

end CFSG.LocalAnalysis.WeakClosure81

end
