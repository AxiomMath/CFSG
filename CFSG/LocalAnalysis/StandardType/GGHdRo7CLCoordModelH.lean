module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelG

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

theorem hdRo7CLCoordAux_card_fin_fun (p k : ℕ) :
    Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]

theorem hdRo7CLCoordAux_k_eq_of_card {E : Type} [Group E] [Finite E]
    (p k r : ℕ) (hp2 : 2 ≤ p)
    (τT : (Fin k → Multiplicative (ZMod p)) →* E) (hbij : Function.Bijective τT)
    (hr : Nat.card E = p ^ r) : k = r := by
  have h1 : p ^ k = p ^ r := by
    rw [← hdRo7CLCoordAux_card_fin_fun p k, ← hr]
    exact Nat.card_congr (MulEquiv.ofBijective τT hbij).toEquiv
  exact Nat.pow_right_injective hp2 h1

noncomputable def hdRo7CLCoordAux_tau {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L : Subgroup G)
    (k : ℕ) (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs) :
    (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
  (hdRo7CLCoordAux_piFinSuccEquiv (Multiplicative (ZMod p)) k).trans
    (((MulEquiv.ofBijective τT hτT).prodCongr τC).trans Φ)

theorem hdRo7CLCoordAux_tau_apply {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L : Subgroup G)
    (k : ℕ) (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (f : Fin (k + 1) → Multiplicative (ZMod p)) :
    ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f : ↥Bs) : G) =
      (τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val := by
  rw [hdRo7CLCoordAux_tau]
  change (Φ (τT (Fin.tail f), τC (f 0)) : G) = _
  rw [hΦ, hC (f 0)]

theorem hdRo7CLCoordAux_zmod_val_one {p : ℕ} (hp : 1 < p) : (1 : ZMod p).val = 1 := by
  haveI : Fact (1 < p) := ⟨hp⟩
  exact ZMod.val_one p

theorem hdRo7CLCoordAux_tau_mulSingle {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hp : Nat.Prime p) (hxp : x ^ p = 1) (hx : x ∈ Bs) :
    ∃ (hx' : x ∈ Bs),
      hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
        (Pi.mulSingle (0 : Fin (k + 1)) (Multiplicative.ofAdd (1 : ZMod p))) = ⟨x, hx'⟩ := by
  refine ⟨hx, ?_⟩
  let g : Fin (k + 1) → Multiplicative (ZMod p) :=
    Pi.mulSingle (0 : Fin (k + 1)) (Multiplicative.ofAdd (1 : ZMod p))
  change hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ g = ⟨x, hx⟩
  apply Subtype.ext
  rw [hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC]
  have htail : Fin.tail g = 1 := by
    funext i
    simp [g, Fin.tail, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i)]
  have hexp : g 0 = Multiplicative.ofAdd (1 : ZMod p) := by
    simp [g, Pi.mulSingle_eq_same]
  rw [htail, map_one, Subgroup.coe_one, one_mul, hexp,
    show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) = (1 : ZMod p) from rfl,
    hdRo7CLCoordAux_zmod_val_one hp.one_lt, pow_one]

end CFSG.StandardType.HdRo7C

end
