module

public import CFSG.Quasithin.Background.FFC6S
public import CFSG.Quasithin.Background.FFC5T9
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5

section B484

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V]

theorem card_commV_le_sixteen
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (hirr : commV L ∈ IrrPlus L ⊤)
    (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1) : Nat.card ↥(commV L) ≤ 2 ^ 4 := by
  obtain ⟨hinv, hcomm, -, -⟩ := irr_data hirr
  obtain ⟨D⟩ := exists_natQuot3 hnat
  have hexp : ∀ x : Additive ↥(commV L), 2 • x = 0 := by
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [toMul_nsmul, hV]
  let _ : Module (ZMod 2) (Additive ↥(commV L)) := AddCommGroup.zmodModule hexp
  have hker : ∀ m : Additive ↥(commV L), D.thetaA m = 0 → ∀ γ : SL3F2,
      muW hinv (D.ρ γ) m = m := by
    intro m hm γ
    have hmZ := D.thetaA_ker m hm
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [muW_apply]
    exact hmZ.1 (D.ρ γ : MulAut V) (D.ρ γ).2
  have hfin : ∀ f : Additive ↥(commV L) →+ ZMod 2,
      (∀ γ m, f (((muW hinv).comp D.ρ) γ m) = f m) → f = 0 := by
    intro f hf
    let ψ : ↥(commV L) →* Multiplicative (ZMod 2) :=
      { toFun := fun u => Multiplicative.ofAdd (f (Additive.ofMul u))
        map_one' := by simp
        map_mul' := fun a b => by simp }
    have hle : commSub (commV L) L ≤ ψ.ker.map (commV L).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, u, hu, rfl⟩
      have hx : g u * u⁻¹ ∈ commV L := (commV L).mul_mem (hinv g hg u hu) ((commV L).inv_mem hu)
      refine ⟨⟨g u * u⁻¹, hx⟩, ?_, rfl⟩
      obtain ⟨γ, hγ⟩ := D.surj ⟨g, hg⟩
      have h1 := hf γ (Additive.ofMul ⟨u, hu⟩)
      have h2 : Additive.ofMul (⟨g u * u⁻¹, hx⟩ : ↥(commV L)) =
          ((muW hinv).comp D.ρ) γ (Additive.ofMul ⟨u, hu⟩) - Additive.ofMul ⟨u, hu⟩ := by
        apply Additive.toMul.injective
        apply Subtype.ext
        show g u * u⁻¹ = ((Additive.toMul (muW hinv (D.ρ γ) (Additive.ofMul ⟨u, hu⟩) -
          Additive.ofMul ⟨u, hu⟩) : ↥(commV L)) : V)
        rw [muW_sub_apply, hγ]
        rfl
      show Multiplicative.ofAdd (f (Additive.ofMul (⟨g u * u⁻¹, hx⟩ : ↥(commV L)))) = 1
      rw [h2, map_sub, h1, sub_self]
      rfl
    ext m
    have hu : (m : V) ∈ commSub (commV L) L := by
      rw [hcomm]
      exact m.2
    obtain ⟨k, hk, hkeq⟩ := hle hu
    have hkm : k = m := Subtype.ext hkeq
    have h3 : ψ k = 1 := hk
    rw [hkm] at h3
    have h4 : f (Additive.ofMul m) = 0 := Multiplicative.ofAdd.injective h3
    simpa using h4
  have := card_le_sixteen ((muW hinv).comp D.ρ) D.thetaA D.thetaA_surj
    (fun γ m => D.thetaA_equiv hinv γ m) (fun m hm γ => hker m hm γ) hfin
  rw [Nat.card_congr (Additive.toMul : Additive ↥(commV L) ≃ ↥(commV L))] at this
  exact this

end B484

end FFC

end CFSG.Quasithin
