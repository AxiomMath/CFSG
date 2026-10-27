module

public import CFSG.Quasithin.Background.C126NatDSub
public import CFSG.Quasithin.Background.C126NatDSimple

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

section Aut

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem autI_commutator {A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autI hV ⁅A, B⁆ = ⁅autI hV A, autI hV B⁆ := by
  have hAB : ⁅A, B⁆ ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hA ha) (hB hb))
        (Subgroup.inv_mem _ (hA ha))) (Subgroup.inv_mem _ (hB hb))
  unfold autI
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective (Subgroup.normalizer (V : Set G)).subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hAB]

end Aut

namespace NatCtx

variable {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hV)))} (c : NatCtx H T M V hV I)

include c in
theorem commutator_star_eq {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    ⁅L, autI hV (baum T)⁆ = L := by
  obtain ⟨n, hn2, hnat⟩ := c.nat L hL
  obtain ⟨hn, F, iF, iFin, hF, ⟨e⟩⟩ := exists_equiv_sl2 hnat
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hF
  have hLle : L ≤ ⨆ L' ∈ I, L' := le_iSup₂_of_le L hL le_rfl
  have hnorm := c.iSup_le_normalizer hL
  have hS := c.sylow_star
  have hSyl : IsSylowTwoOf (autI hV (baum T) ⊓ L) L := B6.isSylowTwoOf_inf_normal hS hLle hnorm
  have hne : autI hV (baum T) ⊓ L ≠ ⊥ := fun h0 => by
    have h1 := card_sylow_of_equiv_sl2 hn hF e hSyl
    rw [h0, Subgroup.card_bot] at h1
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  have h1 := commutator_eq_of_ne_bot h4 e inf_le_right hne
  have hSn : autI hV (baum T) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV))) :=
    fun x hx => hnorm (hS.1 hx)
  refine le_antisymm (commutator_le_left_of_le_normalizer hSn) ?_
  calc L = ⁅L, autI hV (baum T) ⊓ L⁆ := h1.symm
    _ ≤ ⁅L, autI hV (baum T)⁆ := Subgroup.commutator_mono le_rfl inf_le_left

include c in
theorem commutator_K1_eq (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    {P : Subgroup G} (hSP : baum T ≤ P) (hPK : P ≤ twoResidual H ⊔ baum T)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) (hρ : autI hV (twoResidual P) = L) :
    ⁅twoResidual P, thompsonJ T⁆ = twoResidual P := by
  have hSH : baum T ≤ H := inf_le_left.trans c.min.isSylow.1
  have hKSH : twoResidual H ⊔ baum T ≤ H := sup_le (twoResidual_le H) hSH
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := (hPK.trans hKSH).trans c.hHN
  have hJP : thompsonJ T ≤ P := (B6.thompsonJ_le_baum T).trans hSP
  have hK1P : twoResidual P ≤ P := twoResidual_le P
  have hJn : thompsonJ T ≤ Subgroup.normalizer (twoResidual P : Set G) := fun j hj =>
    le_normalizer_twoResidual P (hJP hj)
  set K₁ : Subgroup G := twoResidual P with hK₁
  set X : Subgroup G := ⁅K₁, thompsonJ T⁆ with hX
  have hXK : X ≤ K₁ := commutator_le_left_of_le_normalizer hJn
  have hKX : K₁ ≤ Subgroup.normalizer (X : Set G) := le_normalizer_commutator_left K₁ _
  have hρX : autI hV X = L := by
    rw [hX, autI_commutator hV (hK1P.trans hPN) (hJP.trans hPN), hρ, ← c.sbj]
    exact c.commutator_star_eq hL
  have hKC : K₁ ⊓ Subgroup.centralizer (V : Set G) ≤ baum T := fun x hx =>
    c.kerK_le_baum hRF ⟨c.twoResidual_le_K hPK hx.1, hx.2⟩
  have hdec : ∀ k ∈ K₁, ∃ x ∈ X, ∃ r ∈ baum T ⊓ K₁, k = x * r := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := hPN (hK1P hk)
    have hmem : convI hV ⟨k, hkN⟩ ∈ autI hV X := by
      rw [hρX, ← hρ]
      exact convI_mem_autI hV hk hkN
    obtain ⟨x, hx, hxk⟩ := (mem_autI hV).1 hmem
    have h1 : convI hV (x⁻¹ * ⟨k, hkN⟩) = 1 := by
      rw [map_mul, map_inv, hxk, inv_mul_cancel]
    have h2 : (x : G)⁻¹ * k ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hrK : (x : G)⁻¹ * k ∈ K₁ := K₁.mul_mem (K₁.inv_mem (hXK hx)) hk
    exact ⟨x, hx, (x : G)⁻¹ * k, ⟨hKC ⟨hrK, h2⟩, hrK⟩, by group⟩
  have hsup : (baum T ⊓ K₁) ⊔ X = K₁ := by
    apply le_antisymm
    · exact sup_le inf_le_right hXK
    · intro k hk
      obtain ⟨x, hx, r, hr, rfl⟩ := hdec k hk
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hr)
  have hS2 : IsPGroup 2 ↥(baum T) := c.min.isSylow.2.1.to_le inf_le_left
  have h2q := B6.isTwoQuotient_of_sup_eq (hS2.to_le (inf_le_left : baum T ⊓ K₁ ≤ baum T)) hKX hsup
  have h3 := twoResidual_le_of_isTwoQuotient hXK hKX h2q
  rw [hK₁, twoResidual_twoResidual] at h3
  exact le_antisymm hXK h3

end NatCtx

end CFSG.Quasithin.C126.Nat
