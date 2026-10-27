module

public import CFSG.Quasithin.Background.F918D9

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem finrank_H1_SL2' {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {F : Type} [Field F] [Fintype F] [CharP F 2] {ρ : Representation (ZMod 2) Γ M} {a : ℕ}
    (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) {ε : Explicit.NatDual}
    (h : Explicit.BinaryNaturalSL ρ 2 F ε) : Module.finrank (ZMod 2) (H1 ρ) = a := by
  obtain ⟨θ, β, hβ⟩ := BinaryNaturalSL.intertwiner h
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite M := Finite.of_equiv _ β.toEquiv.symm
  have hβ' : ∀ γ w, β (ρ γ w) = mu2 (θ γ) (β w) := hβ
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' (card_Z1A_mu2 hF ha), hF]

theorem card_fixV_le_of_sl2 {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    (L : Subgroup (MulAut W)) (U : Subgroup W) (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U)
    (hcomm : XMod.commOf ↥L U = U) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hreal : (FFModel.nat (StatedSL 2 K)).Realizes L U (fixV L ⊓ U)) :
    Nat.card ↥(fixV L ⊓ U) ≤ 2 ^ n := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSL 2 K)) hexp L U (fixV L ⊓ U)
    inf_le_right (fun z hz x hx => mem_fixV.1 hz.1 x hx) hinv hcomm π hπ.1 (SLCover.natRepQ 2 K) β
    hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [finrank_H1_SL2' hF (by omega) (SLCover.binaryNaturalSL_dual 2 K)] at hcard

end CFSG.Quasithin.B513N
