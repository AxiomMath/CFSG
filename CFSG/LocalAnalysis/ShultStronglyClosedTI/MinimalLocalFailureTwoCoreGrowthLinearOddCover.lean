module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import Certificates.Certificate43
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

universe u v

variable {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]

theorem perfect_odd_cover_kernel_eq_bot
    {D : Type v} [Group D] [Finite D] (η : E →* D)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card η.ker))
    (hcyclic : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p D, IsCyclic P) :
    η.ker = ⊥ := by
  classical
  apply le_antisymm
  · intro x hx
    by_contra hxone
    have hcard : Nat.card η.ker ≠ 1 := by
      intro hcard
      have hbot : η.ker = ⊥ := Subgroup.card_eq_one.mp hcard
      exact hxone (hbot ▸ hx)
    obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hcard
    let : Fact p.Prime := ⟨hp⟩
    have hpodd : p ≠ 2 := by
      intro heq
      exact hodd.not_two_dvd_nat (heq ▸ hpdiv)
    obtain ⟨a, haorder⟩ := exists_prime_orderOf_dvd_card' (G := η.ker) p hpdiv
    have haEorder : orderOf (a : E) = p := (Subgroup.orderOf_coe a).trans haorder
    have haPGroup : IsPGroup p (Subgroup.zpowers (a : E)) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, haEorder, pow_one]
    obtain ⟨P, hP⟩ := haPGroup.exists_le_sylow
    have haP : (a : E) ∈ (P : Subgroup E) := hP (Subgroup.mem_zpowers (a : E))
    let R : Sylow p D := Sylow.mapSurjective hsurj P
    let : IsCyclic R := hcyclic p hpodd R
    let φ : (P : Subgroup E) →* R :=
      (η.comp (P : Subgroup E).subtype).codRestrict (R : Subgroup D) (by
        intro b
        change η (b : E) ∈ (R : Subgroup D)
        rw [Sylow.coe_mapSurjective]
        exact Subgroup.mem_map_of_mem η b.property)
    have hφcentral : φ.ker ≤ Subgroup.center (P : Subgroup E) := by
      intro b hb
      have hbker : (b : E) ∈ η.ker := congrArg Subtype.val hb
      apply Subgroup.mem_center_iff.mpr
      intro c
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral hbker)) (c : E))
    let : IsMulCommutative (P : Subgroup E) :=
      φ.isMulCommutative_of_isCyclic_of_ker_le_center hφcentral
    have haderived : (⟨(a : E), haP⟩ : (P : Subgroup E)) ∈
        commutator (P : Subgroup E) :=
      central_element_mem_sylow_derived P ⟨(a : E), haP⟩ (hcentral a.property)
    rw [commutator_eq_bot] at haderived
    have haone : (a : E) = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp haderived)
    have hprimeone : p = 1 := by simpa only [haone, orderOf_one] using haEorder.symm
    exact hp.ne_one hprimeone
  · exact bot_le

theorem perfect_odd_cover_exact_isomorphism
    {D : Type v} [Group D] [Finite D] (η : E →* D)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card η.ker))
    (hcyclic : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p D, IsCyclic P) :
    η.ker = ⊥ ∧ ∃ e : E ≃* D, ∀ x : E, e x = η x := by
  have hbot := perfect_odd_cover_kernel_eq_bot η hsurj hcentral hodd hcyclic
  exact ⟨hbot, MulEquiv.ofBijective η ⟨η.ker_eq_bot_iff.mp hbot, hsurj⟩, fun _ => rfl⟩

theorem perfect_linear_odd_cover
    (f : ℕ) (hf : 2 ≤ f) (η : E →* PSL2BinaryMatrixGroup f)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card η.ker)) :
    η.ker = ⊥ ∧ ∃ e : E ≃* PSL2BinaryMatrixGroup f, ∀ x : E, e x = η x := by
  exact perfect_odd_cover_exact_isomorphism η hsurj hcentral hodd
    (lemma114_psl2_oddSylow_isCyclic_of_equiv hf (MulEquiv.refl _))

theorem perfect_suzuki_odd_cover
    (a : ℕ) (η : E →* SuzukiMatrixGroup a)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card η.ker)) :
    η.ker = ⊥ ∧ ∃ e : E ≃* SuzukiMatrixGroup a, ∀ x : E, e x = η x := by
  exact perfect_odd_cover_exact_isomorphism η hsurj hcentral hodd
    (lemma114_suzuki_oddSylow_isCyclic_of_equiv (MulEquiv.refl _))

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
