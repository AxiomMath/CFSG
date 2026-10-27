module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K46Quasi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem proper_normal_le_pPrimeCore {D : Subgroup G} (hD : Nat.card D = 3)
    (hgen : Subgroup.normalClosure (D : Set G) = ⊤)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1) (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊤) : N ≤ CFSG.pPrimeCore 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h3 : 3 ∣ Nat.card N
  · have hDle : D ≤ N :=
      le_of_normal_of_dvd_card (p := 3) (by norm_num) hrank hD (inferInstance : N.Normal) h3
    have hclosure : Subgroup.normalClosure (D : Set G) ≤ N :=
      Subgroup.normalClosure_le_normal (fun _ hx => hDle hx)
    rw [hgen] at hclosure
    exact absurd (eq_top_iff.2 hclosure) hN
  · have hcop : Nat.Coprime 3 (Nat.card N) :=
      (Nat.prime_three.coprime_iff_not_dvd).2 h3
    exact le_sSup (s := {K : Subgroup G | K.Normal ∧ Nat.Coprime 3 (Nat.card K)})
      ⟨inferInstance, hcop⟩

theorem isSimpleGroup_quotient_pPrimeCore {D : Subgroup G} (hD : Nat.card D = 3)
    (hgen : Subgroup.normalClosure (D : Set G) = ⊤)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1) :
    IsSimpleGroup (G ⧸ CFSG.pPrimeCore 3 G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup G := CFSG.pPrimeCore 3 G
  have hcop : Nat.Coprime 3 (Nat.card P) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := G)
  have hPne : P ≠ ⊤ := by
    intro htop
    have h3dvd : 3 ∣ Nat.card P := by
      rw [htop, Subgroup.card_top]
      exact hD ▸ Subgroup.card_subgroup_dvd_card D
    exact (Nat.prime_three.coprime_iff_not_dvd).1 hcop h3dvd
  haveI : Nontrivial (G ⧸ P) := QuotientGroup.nontrivial_iff.2 hPne
  refine { eq_bot_or_eq_top_of_normal := ?_ }
  intro T hT
  let M : Subgroup G := T.comap (QuotientGroup.mk' P)
  have hMnorm : M.Normal := hT.comap _
  have hPle : P ≤ M := fun x hx => by
    show QuotientGroup.mk' P x ∈ T
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact T.one_mem
  by_cases hMtop : M = ⊤
  · right
    refine eq_top_iff.2 fun t _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have : g ∈ M := by rw [hMtop]; exact mem_top g
    exact this
  · left
    haveI : M.Normal := hMnorm
    have hMle : M ≤ P := proper_normal_le_pPrimeCore hD hgen hrank M hMtop
    have hMeq : M = P := le_antisymm hMle hPle
    refine eq_bot_iff.2 fun t ht => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have hg : g ∈ M := ht
    rw [hMeq] at hg
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff g).2 hg

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
