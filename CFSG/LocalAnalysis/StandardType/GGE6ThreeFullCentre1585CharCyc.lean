module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Defs

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ltrv4a_rootChar_neg {K : Type} [Field K] {τ : Tag}
    (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]

private theorem ltrv4a_rootChar_nsmul {K : Type} [Field K] {τ : Tag}
    (a : Fin τ.rank → Kˣ) (n : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar a (n • v) = rootChar a v ^ n := by
  induction n with
  | zero => simp [rootChar_zero]
  | succ n ih => rw [succ_nsmul, rootChar_add, ih, pow_succ]

private theorem ltrv4a_rootChar_zsmul {K : Type} [Field K] {τ : Tag}
    (a : Fin τ.rank → Kˣ) (n : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (n • v) = rootChar a v ^ n := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_coe, natCast_zsmul, ltrv4a_rootChar_nsmul, zpow_natCast]
  | negSucc n =>
      have hcast : (↑n + 1 : ℤ) = (↑(n + 1) : ℤ) := by push_cast; ring
      have hz : (Int.negSucc n) • v = -((n + 1 : ℕ) • v) := by
        rw [Int.negSucc_eq, neg_zsmul, hcast, natCast_zsmul]
      rw [hz, ltrv4a_rootChar_neg, ltrv4a_rootChar_nsmul, zpow_negSucc]

private theorem ltrv4a_rootChar_mul {K : Type} [Field K] {τ : Tag}
    (a b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem ltrv4a_rootChar_inv {K : Type} [Field K] {τ : Tag}
    (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow', zpow_neg, Finset.prod_inv_distrib]

private theorem ltrv4a_eq_one_of_rootChar_eval_eq_one {τ : Tag} {Omega : Type} [Field Omega]
    (N : Submodule ℤ (Fin τ.rank → ℤ))
    (v₀ : Fin τ.rank → ℤ) (g : (Fin τ.rank → ℤ) ⧸ N)
    (hg : ∀ b : (Fin τ.rank → ℤ) ⧸ N, ∃ n : ℤ, n • g = b)
    (hv₀ : N.mkQ v₀ = g)
    (c : charKilled τ Omega N) (hc : rootChar c.1 v₀ = 1) : c = 1 := by
  have hc1 : c.1 = 1 := by
    funext i
    have hsingle : rootChar c.1 (Pi.single i 1) = c.1 i := by
      have h := rootChar_nsmul_single c.1 i 1
      simpa using h
    rw [← hsingle]
    obtain ⟨n, hn⟩ := hg (N.mkQ (Pi.single i 1))
    have hmemN : Pi.single i 1 - n • v₀ ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change N.mkQ (Pi.single i 1 - n • v₀) = 0
      rw [map_sub, map_zsmul, hv₀, ← hn, sub_self]
    have hcN : rootChar c.1 (Pi.single i 1 - n • v₀) = 1 := c.2 _ hmemN
    calc
      rootChar c.1 (Pi.single i 1)
          = rootChar c.1 ((Pi.single i 1 - n • v₀) + n • v₀) := by rw [sub_add_cancel]
      _ = rootChar c.1 (Pi.single i 1 - n • v₀) * rootChar c.1 (n • v₀) :=
            rootChar_add c.1 _ _
      _ = 1 := by
            rw [hcN, ltrv4a_rootChar_zsmul c.1 n v₀, hc, one_zpow, mul_one]
  exact Subtype.ext hc1

theorem isCyclic_charKilled_of_isAddCyclic {τ : Tag} {Omega : Type} [Field Omega]
    (N : Submodule ℤ (Fin τ.rank → ℤ)) [Finite ((Fin τ.rank → ℤ) ⧸ N)]
    (h : IsAddCyclic ((Fin τ.rank → ℤ) ⧸ N)) : IsCyclic (charKilled τ Omega N) := by
  classical
  obtain ⟨g, hg⟩ := h
  obtain ⟨v₀, hv₀⟩ := Submodule.mkQ_surjective N g
  let m := Nat.card ((Fin τ.rank → ℤ) ⧸ N)
  haveI : Fintype ((Fin τ.rank → ℤ) ⧸ N) := Fintype.ofFinite _
  haveI : Nonempty ((Fin τ.rank → ℤ) ⧸ N) := ⟨N.mkQ 0⟩
  haveI : NeZero m := ⟨by
    rw [show m = Fintype.card ((Fin τ.rank → ℤ) ⧸ N) from Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero⟩
  have hmg : m • g = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero (x := g) (n := m)).mp (addOrderOf_dvd_natCard g)
  have hmemN : m • v₀ ∈ N := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change N.mkQ (m • v₀) = 0
    rw [map_nsmul, hv₀, hmg]
  have hroot_mem : ∀ b : charKilled τ Omega N, (rootChar b.1 v₀) ^ m = 1 := by
    intro b
    have hb : rootChar b.1 (m • v₀) = 1 := b.2 (m • v₀) hmemN
    have hz : rootChar b.1 ((m : ℤ) • v₀) = (rootChar b.1 v₀) ^ (m : ℤ) :=
      ltrv4a_rootChar_zsmul b.1 (m : ℤ) v₀
    rw [natCast_zsmul, hb, zpow_natCast] at hz
    exact hz.symm
  let ψ : charKilled τ Omega N →* rootsOfUnity m Omega :=
    { toFun := fun b => ⟨rootChar b.1 v₀, hroot_mem b⟩
      map_one' := by
        apply Subtype.ext
        simp [rootChar]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simpa using ltrv4a_rootChar_mul a.1 b.1 v₀ }
  refine isCyclic_of_injective ψ ?_
  intro a b hab
  have hab' : rootChar a.1 v₀ = rootChar b.1 v₀ :=
    congrArg (fun x : rootsOfUnity m Omega => (x : Omegaˣ)) hab
  have hroot : rootChar (a * b⁻¹).1 v₀ = 1 := by
    have hcoe : (a * b⁻¹).1 = a.1 * b.1⁻¹ := rfl
    rw [hcoe, ltrv4a_rootChar_mul, ltrv4a_rootChar_inv, hab', mul_inv_cancel]
  have hc : a * b⁻¹ = 1 :=
    ltrv4a_eq_one_of_rootChar_eval_eq_one N v₀ g hg hv₀ (a * b⁻¹) hroot
  exact mul_inv_eq_one.mp hc

end CFSG.StandardType.E6Centralizer1585

end
