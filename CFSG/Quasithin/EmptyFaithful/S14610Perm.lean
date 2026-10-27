module

public import CFSG.Quasithin.EmptyFaithful.S14610P0
public import CFSG.Quasithin.EmptyFaithful.S1422Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem wOf1469_le_pCoreOf (K : Subgroup G) : wOf1469 K ≤ pCoreOf 2 K := by
  refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
  have haO : a ∈ pCoreOf 2 K := (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1) ha
  have hkn : k ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K hk
  have h1 : k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp hkn a⁻¹).mp ((pCoreOf 2 K).inv_mem haO)
  have e : ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e]
  exact (pCoreOf 2 K).mul_mem haO h1

theorem wOf1469_le_T {I K : Subgroup G} (hKI : K ≤ I) (hKn : I ≤ Subgroup.normalizer (K : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ I) I) : wOf1469 K ≤ T := by
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKI)
      (hKn.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  exact ((wOf1469_le_pCoreOf K).trans h1).trans
    ((B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left)

theorem Setting146.odd_mem_i1_of_tI_eq_tZero (S : Setting146 G T M) {H : Subgroup G} {u : G}
    {I : Subgroup G} (hu : IsInvU T M H u) (hT0 : T ⊓ I = tZero T u)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) {x : G}
    (hx : x ∈ yOfL22 T M ⊔ T) (hxo : Odd (orderOf x)) : x ∈ i1Of1469 T M I := by
  have hTLT : IsSylowTwoOf T (yOfL22 T M ⊔ T) :=
    B6.isSylowTwoOf_mono S.isSylowTwoOf_top le_sup_right le_top
  have hRT : pCoreOf 2 (yOfL22 T M ⊔ T) ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hTLT
  have hXO : i1Of1469 T M I ≤ Subgroup.normalizer (pCoreOf 2 (yOfL22 T M ⊔ T) : Set G) :=
    (i1Of1469_le_yOfL22_sup T M I).trans (le_normalizer_pCoreOf 2 _)
  have hTI1 : T ⊓ I ≤ i1Of1469 T M I := le_sup_right
  obtain ⟨t₀, ht₀T, ht₀n, ht₀⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hu.index_two
  have hH : ∀ b ∈ yOfL22 T M ⊔ T, b ∈ i1Of1469 T M I ∨ b * t₀ ∈ i1Of1469 T M I := by
    intro b hb
    have hb' : b ∈ ((i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) : Subgroup G) : Set G) := hLT ▸ hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXO] at hb'
    obtain ⟨a, ha, r, hr, rfl⟩ := hb'
    rcases ht₀ r (hRT hr) with h | h
    · right
      have hr0 : r * t₀ ∈ i1Of1469 T M I := hTI1 (by rw [hT0]; exact h)
      rw [mul_assoc]
      exact (i1Of1469 T M I).mul_mem ha hr0
    · left
      exact (i1Of1469 T M I).mul_mem ha (hTI1 (by rw [hT0]; exact h))
  by_contra hxn
  have hx1 : x * t₀ ∈ i1Of1469 T M I := (hH x hx).resolve_left hxn
  have hx2 : x * x ∈ i1Of1469 T M I := by
    by_contra hxxn
    have h2 : (x * x) * t₀ ∈ i1Of1469 T M I :=
      (hH (x * x) ((yOfL22 T M ⊔ T).mul_mem hx hx)).resolve_left hxxn
    apply hxn
    have e : x = ((x * x) * t₀) * (x * t₀)⁻¹ := by group
    rw [e]
    exact (i1Of1469 T M I).mul_mem h2 ((i1Of1469 T M I).inv_mem hx1)
  have hcop : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.mpr hxo
  have hz : x ∈ Subgroup.zpowers (x ^ 2) := A4.mem_zpowers_pow_of_coprime hcop
  exact hxn (Subgroup.zpowers_le.mpr (by rw [sq]; exact hx2) hz)

theorem Setting146.facts14610_perm (i16 : Input14610PermFixed) (i17 : Input14610PermTu)
    {H : Subgroup G} {u : G} {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hcases : T ⊓ I = tU T u ∨ T ⊓ I = tZero T u)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K)
    (hperm : (IsAlt 6 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 5) ∨
      (IsAlt 7 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 6)) :
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3 := by
  by_contra hne
  rcases hcases with hTu | hT0
  · exact i17 G T M H u I I₂ K c hK hperm hTu hne
  · have S : Setting146 G T M := c.setting
    have hres : oTwoUpper (yOfL22 T M) = yOfL22 T M := S.hyp1281.residual
    have hLI1 : yOfL22 T M ≤ i1Of1469 T M I := by
      calc yOfL22 T M = oTwoUpper (yOfL22 T M) := hres.symm
        _ ≤ i1Of1469 T M I := (Subgroup.closure_le _).mpr fun x hx =>
          S.odd_mem_i1_of_tI_eq_tZero c.hu hT0 hLT (Subgroup.mem_sup_left hx.1) hx.2
    have hlI : lI T M I = yOfL22 T M := by
      have hLI : yOfL22 T M ≤ I := hLI1.trans (i1Of1469_le T M I)
      unfold lI
      rw [inf_eq_left.mpr hLI]
      exact hres
    have hW := i16 G T M H u I I₂ K c hK hperm
    rw [hlI] at hW
    apply hW
    have hWT : wOf1469 K ≤ T := wOf1469_le_T hK.le hK.normal hsyl
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← S.hyp.inf_centralizer_yOfL22_eq_bot S.facts]
    exact ⟨hWT hx.1, hx.2⟩

end CFSG.Quasithin
