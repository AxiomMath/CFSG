module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.Quasithin.H13.U3S1348J

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_bar_ctx (S : A6.Setting134 G T L V) {Lp : Subgroup G} (P : S134Plus S Lp) {z : G}
    {H VH : Subgroup G} (hHz : InHz T L V z H) (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hL1eq : Lp = oTwoRes (H ⊓ centralizer (VH : Set G)))
    (hHL1 : H ≤ normalizer (Lp : Set G))
    (hR₁ : IsSylowTwoOf (r1Of T L V) (centralizerMod (pCoreOf 2 Lp) H Lp)) :
    ∃ ℓ ∈ Lp, ℓ ^ 3 = 1 ∧ ℓ ∉ pCoreOf 2 H ∧ ℓ ∈ centralizer (VH : Set G) ∧
      (∀ x ∈ centralizerMod (pCoreOf 2 Lp) H Lp, x * ℓ * x⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 H) ∧
      (∀ x ∈ centralizerMod (pCoreOf 2 Lp) H Lp, x ∈ centralizer (VH : Set G) →
        ∃ k : ℕ, x * (ℓ ^ k)⁻¹ ∈ pCoreOf 2 H) ∧
      ℓ ∈ centralizerMod (pCoreOf 2 Lp) H Lp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O₁ := pCoreOf 2 Lp with hO₁
  set H₁ := centralizerMod O₁ H Lp with hH₁
  obtain ⟨hTsyl, hL1TH, -, -, -⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hLpH : Lp ≤ H := P.le_L1.trans (le_sup_left.trans hL1TH)
  have hH₁H : H₁ ≤ H := fun x hx => hx.1
  have hRH₁ : r1Of T L V ≤ H₁ := hR₁.1
  have hOn : H ≤ normalizer (O₁ : Set G) := hHL1.trans (normalizer_le_normalizer_pCoreOf 2 Lp)
  have hO₁O : O₁ ≤ pCoreOf 2 H := by
    have hO₁H : O₁ ≤ H := (pCoreOf_le 2 Lp).trans hLpH
    exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hO₁H
      ((normal_subgroupOf_iff_le_normalizer hO₁H).2 hOn) (pCoreOf_isPGroup 2 Lp)
  have hLpC : Lp ≤ centralizer (VH : Set G) :=
    hL1eq.le.trans ((oTwoRes_le _).trans inf_le_right)
  obtain ⟨ℓ, hℓL, hℓ3, hℓNV, hℓρ⟩ := P.exists_cube
    (inA4_cube_mem_C3 c012 c012_props.2.2 c012_props.2.1)
  have hℓO : ℓ ∉ pCoreOf 2 H := by
    intro hℓO
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨ℓ, hℓO⟩
    have hk' : ℓ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg : ℓ ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨hℓ3, hk'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at hg
    have h1 : (⟨ℓ, hℓNV⟩ : ↥(normalizer (V : Set G))) = 1 := Subtype.ext hg
    rw [h1, map_one] at hℓρ
    exact absurd hℓρ.symm (by decide)
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hCn : H ≤ normalizer ((H ⊓ centralizer (VH : Set G) : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_inf_of (le_normalizer hh)
      (mem_normalizer_centralizer_of_mem (hHN hh))
  have hH₁n : H ≤ normalizer (H₁ : Set G) := le_normalizer_centralizerMod hOn le_normalizer hHL1
  have hRH : r1Of T L V ≤ H := (r1Of_le_T T L V).trans hTH
  have hsylC : IsSylowTwoOf (pCoreOf 2 H) ((H ⊓ centralizer (VH : Set G)) ⊓ H₁) := by
    have h := A4.isSylowTwoOf_inf_normal hR₁
      (inf_le_right : (H ⊓ centralizer (VH : Set G)) ⊓ H₁ ≤ H₁)
      (fun x hx => mem_normalizer_inf_of (hCn (hH₁H hx)) (le_normalizer hx))
    have e : r1Of T L V ⊓ ((H ⊓ centralizer (VH : Set G)) ⊓ H₁) = pCoreOf 2 H := by
      rw [inf_comm (H ⊓ centralizer (VH : Set G)) H₁, ← inf_assoc, inf_eq_left.2 hRH₁,
        ← inf_assoc, inf_eq_left.2 hRH, hcR]
    rwa [e] at h
  have hLpbar : ∀ x ∈ Lp, ∃ k : ℕ, x * (ℓ ^ k)⁻¹ ∈ O₁ := by
    intro x hx
    have hxN : x ∈ normalizer (V : Set G) := P.le_NV hx
    have hA4 := P.rho (x := ⟨x, hxN⟩) hx
    have hK : ∀ (e : G) (he : e ∈ Lp) (heN : e ∈ normalizer (V : Set G)),
        S.frame.ρ ⟨e, heN⟩ ∈ K4List → e ∈ O₁ := fun e he heN hρ =>
      P.mem_pCoreOf_of_K4 (x := ⟨e, heN⟩) he hρ
    rcases A4_dec _ hA4 with h | h | h
    · exact ⟨0, by simpa using hK x hx hxN h⟩
    · refine ⟨1, ?_⟩
      rw [pow_one]
      refine hK _ (mul_mem hx (inv_mem hℓL)) (mul_mem hxN (inv_mem hℓNV)) ?_
      rw [show (⟨x * ℓ⁻¹, mul_mem hxN (inv_mem hℓNV)⟩ : ↥(normalizer (V : Set G))) =
        ⟨x, hxN⟩ * ⟨ℓ, hℓNV⟩⁻¹ from rfl, map_mul, map_inv, hℓρ]
      exact h
    · refine ⟨2, ?_⟩
      have e : (ℓ ^ 2)⁻¹ = ℓ := by
        calc (ℓ ^ 2)⁻¹ = ℓ ^ 3 * (ℓ ^ 2)⁻¹ := by rw [hℓ3, one_mul]
          _ = ℓ := by group
      rw [e]
      refine hK _ (mul_mem hx hℓL) (mul_mem hxN hℓNV) ?_
      rw [show (⟨x * ℓ, mul_mem hxN hℓNV⟩ : ↥(normalizer (V : Set G))) =
        ⟨x, hxN⟩ * ⟨ℓ, hℓNV⟩ from rfl, map_mul, hℓρ]
      exact h
  have hℓH₁ : ℓ ∈ H₁ := by
    have hℓN : ℓ ∈ normalizer (O₁ : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 Lp (le_normalizer hℓL)
    refine ⟨hLpH hℓL, hℓN, fun u hu => ?_⟩
    obtain ⟨k, hk⟩ := hLpbar u hu
    have e : ℓ * u * ℓ⁻¹ * u⁻¹ =
        (ℓ * (u * (ℓ ^ k)⁻¹) * ℓ⁻¹) * (u * (ℓ ^ k)⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp hℓN _).mp hk) (inv_mem hk)
  refine ⟨ℓ, hℓL, hℓ3, hℓO, hLpC hℓL, fun x hx => hO₁O (hx.2.2 ℓ hℓL), fun x hxH₁ hxC => ?_,
    hℓH₁⟩
  have hx : x ∈ H := hxH₁.1
  obtain ⟨y, hy, z', hz', hxyz, ⟨k, hyk⟩, m, hm, hzm⟩ := exists_two_odd_decomp x
  have hzpow : ∀ {X : Subgroup G}, x ∈ X → zpowers x ≤ X := fun hX => zpowers_le.2 hX
  have hyO : y ∈ pCoreOf 2 H :=
    Unc25G2.mem_of_isSylowTwoOf_of_normalizes hsylC
      (fun g hg => le_normalizer_pCoreOf 2 H hg.1.1)
      ⟨⟨hzpow hx hy, hzpow hxC hy⟩, hzpow hxH₁ hy⟩ ⟨k, hyk⟩
  have hzL : z' ∈ Lp :=
    hL1eq.ge (mem_oTwoRes_of_odd (mem_inf.2 ⟨hzpow hx hz', hzpow hxC hz'⟩) hm hzm)
  obtain ⟨j, hj⟩ := hLpbar z' hzL
  refine ⟨j, ?_⟩
  rw [hxyz, mul_assoc]
  exact mul_mem hyO (hO₁O hj)

end CFSG.Quasithin.H13.U3
