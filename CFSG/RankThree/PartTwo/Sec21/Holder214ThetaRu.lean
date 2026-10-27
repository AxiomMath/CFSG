module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaGen
public import CFSG.RankThree.PartTwo.Sec21.Hering214EFTrans
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.RankThree.Asc83Table.Ru

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Sporadic.RuSchreier
open Hering214Even

theorem card_dvd_of_le_centralizer_conj {G : Type*} [Group G] {P E : Subgroup G} {x g : G}
    (hg : g ∈ P) (hE : E ≤ P ⊓ Subgroup.centralizer {g * x * g⁻¹}) :
    Nat.card E ∣ Nat.card (P ⊓ Subgroup.centralizer {x} : Subgroup G) := by
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ P ⊓ Subgroup.centralizer {x} := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨heP, heC⟩ := Subgroup.mem_inf.mp (hE he)
    rw [Subgroup.mem_centralizer_singleton_iff] at heC
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · show g⁻¹ * e * g⁻¹⁻¹ ∈ P
      exact P.mul_mem (P.mul_mem (P.inv_mem hg) heP) (P.inv_mem (P.inv_mem hg))
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show g⁻¹ * e * g⁻¹⁻¹ * x = x * (g⁻¹ * e * g⁻¹⁻¹)
      rw [inv_inv]
      calc g⁻¹ * e * g * x = g⁻¹ * (e * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * e) * g := by rw [heC]
        _ = x * (g⁻¹ * e * g) := by group
  have h := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h


theorem ruP_fixNine (E : Subgroup ruP) (hE : Nat.card E = 9) (σ : MulAut ruP) (hσ : σ ^ 2 = 1)
    (hfix : ∀ e ∈ E, σ e = e) : σ = 1 := by
  obtain ⟨t, rfl⟩ := mulAut_inner σ
  have hinj := KS14.conj_injective_of_center_eq_bot center_ruP
  have ht2 : t ^ 2 = 1 := hinj (by rw [map_pow, hσ, map_one])
  by_contra hne
  have ht1 : t ≠ 1 := fun h => hne (by rw [h, map_one])
  have hto : orderOf (t : Equiv.Perm (Fin 4060)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime ht2 ht1
  set E' : Subgroup (Equiv.Perm (Fin 4060)) := E.map ruP.subtype with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective ruP.subtype_injective, hE]
  have hE'le : E' ≤ ruP ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 4060))} := by
    rintro _ ⟨e, he, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨e.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix e he
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
    exact congrArg Subtype.val h.symm
  have hmem : (t : Equiv.Perm (Fin 4060)) ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨t.2, hto⟩
  rw [ruInvolutions_eq] at hmem
  rcases hmem with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · rw [← hgt] at hE'le
    have h := card_dvd_of_le_centralizer_conj hg hE'le
    rw [hE'9, ← ruC_eq_centralizer, card_ruC] at h
    norm_num at h
  · rw [← hgt] at hE'le
    have h := card_dvd_of_le_centralizer_conj hg hE'le
    rw [hE'9, ruCentralizer_a, card_ruL] at h
    norm_num at h


theorem exists_e9_ruP : ∃ Q : Subgroup ruP, IsElemAbelian 3 Q ∧ Nat.card Q = 9 :=
  exists_e9_of_e9Basis (Asc83Table.Ru.E 0) ruEquivP

theorem evenThetaFacts_ruP : EvenThetaFacts ↥ruP :=
  evenThetaFacts_of_fixNine center_ruP
    (fun σ _ => (mulAut_inner σ).elim fun g hg => ⟨g, hg.symm⟩) exists_e9_ruP ruP_fixNine

theorem evenThetaFacts_of_ru {X : Type} [Group X] (hX : Nonempty (X ≃* NativeSporadic.Ru)) :
    EvenThetaFacts X := by
  obtain ⟨e⟩ := hX
  exact evenThetaFacts_of_mulEquiv (e.trans ruEquivP) evenThetaFacts_ruP

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
