module

public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenFieldInvolutions
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.Background.SmithB42G2Rank

public section

namespace CFSG.Quasithin.B45G2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem card_le_cube_adjointGroup {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {Γ : Subgroup (adjointGroup .G2 K)} (hΓ1 : ∀ g ∈ Γ, g * g = 1)
    (hΓc : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h = h * g) : Nat.card Γ ≤ Nat.card K ^ 3 := by
  obtain ⟨ψ, -, hsurj⟩ := B42G2Id.exists_surjective_adjointGroup_hom_cayleyGroup (F := K)
  have : Finite (adjointGroup .G2 K) := inferInstance
  have hinj : Function.Injective ψ := by
    refine (hsurj.bijective_of_nat_card_le ?_).1
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
      CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup]
    unfold CFSG.Open.ordG2
    rw [mul_assoc]
  have h := CFSG.Quasithin.B42G2.card_le_cube hK hn (Γ := Γ.map ψ)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, hΓ1 x hx, map_one])
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [← map_mul, ← map_mul, hΓc x hx y hy])
  rwa [Subgroup.card_map_of_injective hinj] at h

end Rank

section Outer

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem card_sq_le_of_outer_fixed {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup .G2 K)) (hα : orderOf α = 2) (hout : α ∉ inner (adjointGroup .G2 K))
    {Γ : Subgroup (adjointGroup .G2 K)} (hfix : ∀ g ∈ Γ, α g = g)
    (hΓ1 : ∀ g ∈ Γ, g * g = 1) (hΓc : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h = h * g) :
    Nat.card Γ ^ 2 ≤ 2 ^ (3 * f) := by
  classical
  obtain ⟨-, Θ, -, -, hΘker, hΘinv⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hΘker' : Θ.ker = inner (adjointGroup .G2 K) := hΘker
  have hα2 : α ^ 2 = 1 := by rw [← hα, pow_orderOf_eq_one]
  have hΘα : Θ α ≠ 1 := fun h => hout (by rw [← hΘker']; exact MonoidHom.mem_ker.mpr h)
  rcases hΘinv α hα2 with h | ⟨⟨e, he⟩, hpow, hkcard⟩
  · exact absurd h hΘα
  have hfe : f / 2 = e := by omega
  set σ : K ≃+* K := Θ α with hσdef
  rcases even_G2_involution_inner_or_canonical_field hf K hK α hα with h | ⟨-, hcan⟩
  · exact absurd h hout
  obtain ⟨β, ψ, hβ, hψ, -⟩ := hcan σ.toRingHom hpow
  have hβσ : β = CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hβ u, CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom]
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hmem : ∀ g ∈ Γ, ψ g ∈ (CFSG.RankThree.PartTwo.KFacts.g2Incl σ).range := by
    intro g hg
    rw [CFSG.RankThree.PartTwo.KFacts.mem_range_g2Incl_iff hK2, ← hβσ, ← hψ]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hfix g hg]
  set k := fixSubfield σ with hk
  have hkcard' : Nat.card k = 2 ^ e := by rw [hk, hkcard, hfe]
  have : CharP k 2 := RingHom.charP k.subtype Subtype.val_injective 2
  set Γ₀ := (Γ.map ψ.toMonoidHom).comap (CFSG.RankThree.PartTwo.KFacts.g2Incl σ) with hΓ₀
  have hinjI := CFSG.RankThree.PartTwo.KFacts.g2Incl_injective σ
  have hcardΓ₀ : Nat.card Γ₀ = Nat.card Γ := by
    have h1 : Γ₀.map (CFSG.RankThree.PartTwo.KFacts.g2Incl σ) = Γ.map ψ.toMonoidHom := by
      refine le_antisymm (Subgroup.map_comap_le _ _) ?_
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g₀, hg₀⟩ := hmem g hg
      refine ⟨g₀, ?_, hg₀⟩
      show CFSG.RankThree.PartTwo.KFacts.g2Incl σ g₀ ∈ Γ.map ψ.toMonoidHom
      rw [hg₀]
      exact ⟨g, hg, rfl⟩
    rw [← Subgroup.card_map_of_injective hinjI, h1,
      Subgroup.card_map_of_injective ψ.injective]
  have hΓ₀1 : ∀ g ∈ Γ₀, g * g = 1 := by
    intro g hg
    apply hinjI
    obtain ⟨x, hx, hxg⟩ := hg
    rw [map_mul, ← hxg, map_one]
    change ψ x * ψ x = 1
    rw [← map_mul, hΓ1 x hx, map_one]
  have hΓ₀c : ∀ g ∈ Γ₀, ∀ h ∈ Γ₀, g * h = h * g := by
    intro g hg h hh
    apply hinjI
    obtain ⟨x, hx, hxg⟩ := hg
    obtain ⟨y, hy, hyh⟩ := hh
    rw [map_mul, map_mul, ← hxg, ← hyh]
    change ψ x * ψ y = ψ y * ψ x
    rw [← map_mul, ← map_mul, hΓc x hx y hy]
  have hb := card_le_cube_adjointGroup hkcard' (by omega) hΓ₀1 hΓ₀c
  rw [hcardΓ₀, hkcard', ← pow_mul] at hb
  calc Nat.card Γ ^ 2 ≤ (2 ^ (e * 3)) ^ 2 := Nat.pow_le_pow_left hb 2
    _ = 2 ^ (3 * f) := by rw [← pow_mul, he]; ring_nf

end Outer

end CFSG.Quasithin.B45G2
