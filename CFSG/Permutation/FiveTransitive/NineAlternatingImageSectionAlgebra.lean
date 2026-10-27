module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.NineAlternatingImageSectionAlgebra

open Subgroup

private theorem ker_le
    {G F E : Type*} [Group G] [Finite G]
    [Fintype F] [DecidableEq F] [Fintype E]
    (hF : Nat.card F = 9) (rho : G →* alternatingGroup F)
    (hrho : Function.Surjective rho) (sigma : G →* Equiv.Perm E)
    (hker : IsPGroup 5 sigma.ker) : sigma.ker ≤ rho.ker := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
  let K := sigma.ker.map rho
  let _ : K.Normal := (inferInstance : sigma.ker.Normal).map rho hrho
  have hK : IsPGroup 5 K := hker.map rho
  have hKbot : K = ⊥ := by
    rcases (inferInstance : K.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have htwo : 2 ∣ Nat.card K := by
        rw [h,Subgroup.card_top,nat_card_alternatingGroup,hF]
        norm_num [Nat.factorial]
      obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp hK
      rw [hk] at htwo
      have hh := Nat.prime_two.dvd_of_dvd_pow htwo
      norm_num at hh
  intro g hg
  have hm : rho g ∈ K := ⟨g,hg,rfl⟩
  rw [hKbot,Subgroup.mem_bot] at hm
  exact hm

theorem range_rigidity
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 9)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) :
    Function.Injective tau ∧ B = alternatingGroup E := by
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hA : Nat.card (alternatingGroup F) = 181440 := by rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  have hAE : Nat.card (alternatingGroup E) = 181440 := by rw [nat_card_alternatingGroup,hE]; norm_num [Nat.factorial]
  have hSym : Nat.card (Equiv.Perm E) = 362880 := by rw [Nat.card_perm,hE]; norm_num [Nat.factorial]
  have hBbound : Nat.card B ≤ 362880 := by
    rw [← hSym]
    exact Nat.card_le_card_of_injective B.subtype B.subtype_injective
  have hprod : Nat.card tau.ker * 181440 = Nat.card B := by
    have hm := tau.ker.card_mul_index
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr htau,Subgroup.card_top,hA] at hm
    exact hm
  have hkpos : 0 < Nat.card tau.ker := Nat.card_pos
  have hk : Nat.card tau.ker = 1 := by
    have halt : Nat.card tau.ker = 1 ∨ Nat.card tau.ker = 2 := by omega
    rcases halt with h | h
    · exact h
    · have hBcard : Nat.card B = 362880 := by omega
      have hBtop : B = ⊤ := B.eq_top_of_card_eq (hBcard.trans hSym.symm)
      let K := tau.ker.map B.subtype
      have hsurj : Function.Surjective B.subtype := by
        intro x
        exact ⟨⟨x,by rw [hBtop]; trivial⟩,rfl⟩
      let _ : K.Normal := (inferInstance : tau.ker.Normal).map B.subtype hsurj
      have hKcard : Nat.card K = 2 := by
        rw [← h]
        exact Nat.card_congr (tau.ker.equivMapOfInjective B.subtype B.subtype_injective).toEquiv.symm
      have hKnt : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      have hAlt : alternatingGroup E ≤ K := Equiv.Perm.alternatingGroup_le_of_normal (by omega) hKnt
      have hle : Nat.card (alternatingGroup E) ≤ Nat.card K :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAlt)
      rw [hAE,hKcard] at hle
      omega
  have hinj : Function.Injective tau := (MonoidHom.ker_eq_bot_iff tau).mp (Subgroup.card_eq_one.mp hk)
  have hBcard : Nat.card B = 181440 := by omega
  have hindex : B.index = 2 := by
    have hm := B.index_mul_card
    rw [hBcard,hSym] at hm
    omega
  exact ⟨hinj,Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex⟩

theorem exists_equiv
    {G F E : Type*} [Group G] [Finite G]
    [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 9)
    (rho : G →* alternatingGroup F) (hrho : Function.Surjective rho)
    (sigma : G →* Equiv.Perm E) (hker : IsPGroup 5 sigma.ker) :
    ∃ e : alternatingGroup F ≃* alternatingGroup E,
      (∀ g : G, (e (rho g)).val = sigma g) ∧ rho.ker = sigma.ker ∧
      sigma.range = alternatingGroup E := by
  have hk : sigma.rangeRestrict.ker ≤ rho.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_le hF rho hrho sigma hker
  let tau : sigma.range →* alternatingGroup F :=
    sigma.rangeRestrict.liftOfSurjective sigma.rangeRestrict_surjective ⟨rho,hk⟩
  have hcomp : tau.comp sigma.rangeRestrict = rho := by simp [tau]
  have htau : Function.Surjective tau := by
    intro u
    obtain ⟨g,hg⟩ := hrho u
    refine ⟨sigma.rangeRestrict g,?_⟩
    change (tau.comp sigma.rangeRestrict) g = u
    rw [hcomp,hg]
  obtain ⟨hinj,himage⟩ := range_rigidity hF hE sigma.range tau htau
  let d : sigma.range ≃* alternatingGroup F := MulEquiv.ofBijective tau ⟨hinj,htau⟩
  let e : alternatingGroup F ≃* alternatingGroup E := d.symm.trans (MulEquiv.subgroupCongr himage)
  refine ⟨e,?_,?_,himage⟩
  · intro g
    have hfactor : d (sigma.rangeRestrict g) = rho g := DFunLike.congr_fun hcomp g
    change (d.symm (rho g)).val = sigma g
    rw [← hfactor,d.symm_apply_apply]
    rfl
  · apply le_antisymm
    · intro g hg
      have he : tau (sigma.rangeRestrict g) = tau 1 := by
        change (tau.comp sigma.rangeRestrict) g = tau 1
        rw [hcomp,MonoidHom.mem_ker.mp hg,map_one]
      have hs := hinj he
      exact congrArg Subtype.val hs
    · exact ker_le hF rho hrho sigma hker

end FiveTransitive.NineAlternatingImageSectionAlgebra

end CFSG
