module

public import CFSG.RankThree.PartOne.Q1327S.HNCenter
public import CFSG.RankThree.PartOne.Q1327S.Witness
public import CFSG.RankThree.PartOne.KS.HNFiveLocal

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KS CFSG.RankThree.PartOne.KS.HNFive
  CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.HNTwoRank CFSG.Blueprint

theorem exists_hn_rel :
    ∃ (q : Fin 4 → NativeSporadic.HN) (z x : NativeSporadic.HN) (r : Fin 3 → NativeSporadic.HN),
      Rel q z x r Mm XU cx BU cr := by
  let e : NativeSporadic.HN ≃* J := hnEquivJ
  let ι : NativeSporadic.HN →* GLHN := J.subtype.comp (e : NativeSporadic.HN →* J)
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιe : ∀ r, ι (e.symm ⟨Rg r, Rg_mem r⟩) = Rg r := fun r => by
    show ((e (e.symm ⟨Rg r, Rg_mem r⟩) : J) : GLHN) = Rg r
    rw [MulEquiv.apply_symm_apply]
  refine ⟨fun j => e.symm ⟨Rg (iQ j), Rg_mem _⟩, e.symm ⟨Rg iZ, Rg_mem _⟩,
    e.symm ⟨Rg iX, Rg_mem _⟩, fun j => e.symm ⟨Rg (iR j), Rg_mem _⟩, ?_⟩
  apply Rel.of_injective ι hι
  simp only [hιe]
  exact hnFive_rel

theorem false_HN
    {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* NativeSporadic.Carrier .HN) {Ē : Subgroup Q} (hEcard : Nat.card Ē = 5 ^ 2)
    (hcen : ∀ P : Subgroup Q, IsPGroup 5 P → Ē ≤ P → P ≤ Subgroup.centralizer (Ē : Set Q)) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨q, z, x, r, hR⟩ := exists_hn_rel
  have hfin : Finite NativeSporadic.HN :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.HN.card_HN]; norm_num)
  obtain ⟨SN, hSN⟩ := hR.P_sylow XU_ne_one factorization_card_HN_five
  obtain ⟨SQ, hESQ⟩ := (IsPGroup.of_card hEcard).exists_le_sylow
  have hcardN : Nat.card NativeSporadic.HN = Nat.card Q := (Nat.card_congr e.toEquiv).symm
  let f : Q →* NativeSporadic.HN := e.toMonoidHom
  have hfi : Function.Injective f := e.injective
  have hSQcard : Nat.card ((SQ : Subgroup Q).map f) =
      5 ^ (Nat.card NativeSporadic.HN).factorization 5 := by
    rw [Subgroup.card_map_of_injective hfi, Sylow.card_eq_multiplicity SQ, hcardN]
  have hSNcard : Nat.card (SN : Subgroup NativeSporadic.HN) =
      5 ^ (Nat.card NativeSporadic.HN).factorization 5 := Sylow.card_eq_multiplicity SN
  obtain ⟨g, hg⟩ := exists_conj_of_card hSQcard hSNcard
  let ψ : Q →* NativeSporadic.HN := (MulAut.conj g⁻¹).toMonoidHom.comp f
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective.comp hfi
  have hψy : ∀ y : Q, ψ y = g⁻¹ * f y * g := fun y => by
    simp [ψ]
  have hψS : ∀ y ∈ (SQ : Subgroup Q), ψ y ∈ (SN : Subgroup NativeSporadic.HN) := by
    intro y hy
    have h1 : f y ∈ (SQ : Subgroup Q).map f := ⟨y, hy, rfl⟩
    have := (hg (f y)).1 h1
    rw [hψy]
    exact this
  have hcomm : ∀ y ∈ Ē, ∀ w ∈ (SN : Subgroup NativeSporadic.HN), ψ y * w = w * ψ y := by
    intro y hy w hw
    have h1 : g * w * g⁻¹ ∈ (SQ : Subgroup Q).map f := by
      rw [hg]
      simpa [mul_assoc] using hw
    obtain ⟨s, hs, hsw⟩ := h1
    have h2 := Subgroup.mem_centralizer_iff.1 (hcen SQ SQ.isPGroup' hESQ hs) y hy
    have h3 : f y * (g * w * g⁻¹) = (g * w * g⁻¹) * f y := by
      rw [← hsw, ← map_mul, ← map_mul, h2]
    rw [hψy]
    calc g⁻¹ * f y * g * w = g⁻¹ * (f y * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * f y) * g := by rw [h3]
      _ = w * (g⁻¹ * f y * g) := by group
  have hE'card : Nat.card (Ē.map ψ) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective hψ, hEcard]
  have hEP : Ē.map ψ ≤ QG q ⊔ Subgroup.zpowers x := by
    rw [← hSN]
    rintro _ ⟨y, hy, rfl⟩
    exact hψS y (hESQ hy)
  have hEc : ∀ y ∈ Ē.map ψ, ∀ w ∈ QG q ⊔ Subgroup.zpowers x, y * w = w * y := by
    rw [← hSN]
    rintro _ ⟨y, hy, rfl⟩ w hw
    exact hcomm y hy w hw
  have hle := card_central_le hR XU_ne_one hEP hEc
  rw [hE'card] at hle
  omega

end CFSG.RankThree.PartOne.Q1327S
