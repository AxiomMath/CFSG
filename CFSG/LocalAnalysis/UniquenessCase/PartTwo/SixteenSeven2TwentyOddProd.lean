module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.GH74.E2.DirectProd
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem s16c167_relPPrimeCore_le_of_internalDirect {A : Type} [Group A] [Finite A]
    {K L X : Subgroup A} (h : IsInternalDirect K L X) (hL : CFSG.oddCore ↥L = ⊥) :
    relPPrimeCore 2 X ≤ K := by
  obtain ⟨hc, hd, rfl⟩ := h
  have hcomm : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have hcent : a ∈ Subgroup.centralizer (L : Set A) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) ha
    exact ((Subgroup.mem_centralizer_iff.mp hcent) b hb).symm
  let e : ↥K × ↥L ≃* ↥(K ⊔ L) := CFSG.GH74.E2.prodSupEquiv K L hcomm hd
  have he : e = CFSG.GH74.E2.prodSupEquiv K L hcomm hd := rfl
  let N : Subgroup A := relPPrimeCore 2 (K ⊔ L)
  have hNle : N ≤ K ⊔ L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
      (p := 2) (K ⊔ L)
  have hNn : (N.subgroupOf (K ⊔ L)).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_two (K ⊔ L)
  have hNc : Nat.Coprime 2 (Nat.card N) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_two (K ⊔ L)
  let N₁ : Subgroup (↥K × ↥L) := (N.subgroupOf (K ⊔ L)).map e.symm.toMonoidHom
  have hN₁n : N₁.Normal := hNn.map e.symm.toMonoidHom e.symm.surjective
  have hN₁card : Nat.card N₁ = Nat.card N := by
    show Nat.card ((N.subgroupOf (K ⊔ L)).map e.symm.toMonoidHom) = Nat.card N
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
  have hN₁c : Nat.Coprime 2 (Nat.card N₁) := by
    rw [hN₁card]; exact hNc
  let N₂ : Subgroup ↥L := N₁.map (MonoidHom.snd ↥K ↥L)
  have hN₂n : N₂.Normal := hN₁n.map (MonoidHom.snd ↥K ↥L) (fun l => ⟨(1, l), rfl⟩)
  have hN₂odd : Odd (Nat.card N₂) := by
    refine Nat.coprime_two_left.mp (Nat.Coprime.of_dvd_right ?_ hN₁c)
    exact Subgroup.card_map_dvd (H := N₁) (f := MonoidHom.snd ↥K ↥L)
  have hN₂bot : N₂ = ⊥ := by
    have hle : N₂ ≤ CFSG.oddCore ↥L :=
      CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.le_oddCore_of_normal
        hN₂n hN₂odd
    rw [hL] at hle
    exact le_bot_iff.mp hle
  intro x hx
  have hy : (⟨x, hNle hx⟩ : ↥(K ⊔ L)) ∈ N.subgroupOf (K ⊔ L) :=
    Subgroup.mem_subgroupOf.mpr hx
  let p : ↥K × ↥L := e.symm ⟨x, hNle hx⟩
  have hpN₁ : p ∈ N₁ := ⟨⟨x, hNle hx⟩, hy, rfl⟩
  have hp2mem : p.2 ∈ N₂ := ⟨p, hpN₁, rfl⟩
  have hp2 : p.2 = 1 := by
    rw [hN₂bot] at hp2mem
    exact Subgroup.mem_bot.mp hp2mem
  have hxe : e p = ⟨x, hNle hx⟩ := e.apply_symm_apply ⟨x, hNle hx⟩
  have hxval : ((e p : ↥(K ⊔ L)) : A) = x := by rw [hxe]
  rw [he, CFSG.GH74.E2.prodSupEquiv_apply] at hxval
  simp only [hp2, Subgroup.coe_one, mul_one] at hxval
  rw [← hxval]
  exact p.1.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
