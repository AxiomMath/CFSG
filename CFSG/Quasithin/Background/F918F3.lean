module

public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.F918F1
public import CFSG.Quasithin.Background.F918F2
public import CFSG.Quasithin.EmptyFaithful.T1515dInputs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace A8Cover

theorem dualEquiv_equivariant_gen {Γ : Type*} [Group Γ] {n : ℕ}
    (ρ : Representation (ZMod 2) Γ (Fin n → ZMod 2)) (μ : Γ → Matrix (Fin n) (Fin n) (ZMod 2))
    (hρ : ∀ γ x, ρ γ x = μ γ *ᵥ x) (γ : Γ) (l : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    L3Dual.dualEquiv n ((Representation.dual ρ) γ l) = (μ γ⁻¹)ᵀ *ᵥ L3Dual.dualEquiv n l := by
  funext i
  show l (ρ γ⁻¹ (Pi.single i 1)) = _
  rw [hρ]
  have hcol : μ γ⁻¹ *ᵥ (Pi.single i 1 : Fin n → ZMod 2) = fun j => μ γ⁻¹ j i := by
    funext j
    simp
  rw [hcol]
  have h1 := LinearMap.pi_apply_eq_sum_univ l (fun j => μ γ⁻¹ j i)
  have hs : ∀ j : Fin n, (fun k : Fin n => if j = k then (1 : ZMod 2) else 0) = Pi.single j 1 := by
    intro j
    funext k
    simp [Pi.single_apply, eq_comm]
  simp only [hs, smul_eq_mul] at h1
  rw [h1]
  rfl

theorem finrank_H1_dual_wedgeRep4 :
    Module.finrank (ZMod 2) (H1 (Representation.dual wedgeRep4)) = 1 := by
  obtain ⟨θ, B, hB⟩ := exists_alt8_iso_wedgeDual
  have hfinD : Finite (Module.Dual (ZMod 2) (Fin 6 → ZMod 2)) :=
    Finite.of_equiv _ (L3Dual.dualEquiv 6).symm.toEquiv
  have hβ' : ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (l : Module.Dual (ZMod 2) (Fin 6 → ZMod 2)),
      ((L3Dual.dualEquiv 6).trans B) ((Representation.dual wedgeRep4) γ l) =
        SteinbergCB.I16.coords8.actA (θ γ) (((L3Dual.dualEquiv 6).trans B) l) := by
    intro γ l
    show B (L3Dual.dualEquiv 6 ((Representation.dual wedgeRep4) γ l)) = _
    rw [dualEquiv_equivariant_gen wedgeRep4 (fun γ => wedgeMat4
      (((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))) wedgeRep4_apply γ l]
    exact hB γ _
  have hH1 : Nat.card (H1 (Representation.dual wedgeRep4)) = 2 :=
    card_H1_eq_of_card (Representation.dual wedgeRep4) (θ := θ)
      (β := (L3Dual.dualEquiv 6).trans B) (μ := SteinbergCB.I16.coords8.actA) hβ' (k := 2)
      SteinbergCB.I16.card_Z1A_8
  exact finrank_H1_of_card _ (by rw [hH1]; norm_num)

end A8Cover

open A8Cover in
theorem asI16CoverA8_of : AsI16CoverA8 := by
  intro V _ _ hexp L hirr hext
  have hinv : ∀ x ∈ L, ∀ v ∈ commV L, x v ∈ commV L := fun x hx v hv => hirr.2.1 ⟨x, hx⟩ v hv
  have hcomm : XMod.commOf ↥L (commV L) = commV L := hirr.2.2.1
  obtain ⟨π, β, hπs, -, -, hβs, hβk, hβe⟩ := sl4ExteriorTwo_coord hext
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSL 4 (ZMod 2))) hexp L (commV L)
    (fixV L ⊓ commV L) inf_le_right (fun z hz x hx => mem_fixV.1 hz.1 x hx) hinv hcomm π hπs
    (Q := Fin 6 → ZMod 2) wedgeRep4 β hβs hβk hβe
  rw [finrank_H1_dual_wedgeRep4, pow_one] at hcard
  exact hcard

end CFSG.Quasithin
