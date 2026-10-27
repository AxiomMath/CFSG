module

public import CFSG.Quasithin.Background.C126NatDCtx
public import CFSG.Quasithin.Background.C126NatFstarAux

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section General

variable {P V : Subgroup G} (hV : IsElemAbelian 2 V) (hPN : P ≤ Subgroup.normalizer (V : Set G))

omit [Finite G] in
include hPN in
theorem conj_mem_preI {B : Subgroup (MulAut (IntMod V hV))}
    (hB : autI hV P ≤ Subgroup.normalizer (B : Set (MulAut (IntMod V hV)))) {q y : G} (hq : q ∈ P)
    (hy : y ∈ preI hV P hPN B) : q * y * q⁻¹ ∈ preI hV P hPN B := by
  obtain ⟨hyP, hyB⟩ := (mem_preI hV).1 hy
  have hqyP : q * y * q⁻¹ ∈ P := P.mul_mem (P.mul_mem hq hyP) (P.inv_mem hq)
  refine (mem_preI hV).2 ⟨hqyP, ?_⟩
  have h1 : convHom hV P hPN ⟨q * y * q⁻¹, hqyP⟩ =
      convHom hV P hPN ⟨q, hq⟩ * convHom hV P hPN ⟨y, hyP⟩ * (convHom hV P hPN ⟨q, hq⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h1]
  exact (Subgroup.mem_normalizer_iff.1 (hB (convI_mem_autI hV hq (hPN hq))) _).1 hyB

include hPN in
theorem autI_twoResidual_eq : autI hV (twoResidual P) = twoResidual (autI hV P) := by
  have hQP : twoResidual (autI hV P) ≤ autI hV P := twoResidual_le _
  apply le_antisymm
  · set Q := twoResidual (autI hV P) with hQ
    have hQn : autI hV P ≤ Subgroup.normalizer (Q : Set (MulAut (IntMod V hV))) :=
      le_normalizer_twoResidual _
    have hNnorm : P ≤ Subgroup.normalizer ((preI hV P hPN Q : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_preI hV hPN hQn hg hy, fun hy => ?_⟩
      have := conj_mem_preI hV hPN hQn (P.inv_mem hg) hy
      simpa [mul_assoc] using this
    have h2 : ∀ y ∈ P, ∃ k : ℕ, y ^ 2 ^ k ∈ preI hV P hPN Q := by
      intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (autI hV P) _ (convI_mem_autI hV hy (hPN hy))
      refine ⟨k, (mem_preI hV).2 ⟨P.pow_mem hy _, ?_⟩⟩
      have : convHom hV P hPN ⟨y ^ 2 ^ k, P.pow_mem hy _⟩ = (convI hV ⟨y, hPN hy⟩) ^ 2 ^ k := by
        rw [← map_pow]
        rfl
      rw [this]
      exact hk
    have h3 := twoResidual_le_of_isTwoQuotient (preI_le hV) hNnorm h2
    calc autI hV (twoResidual P) ≤ autI hV (preI hV P hPN Q) := autI_mono hV h3
      _ = Q := autI_preI hV hQP
  · exact twoResidual_le_of_isTwoQuotient (autI_mono hV (twoResidual_le P))
      (le_normalizer_autI_twoResidual hV hPN) (isTwoQuotient_autI_twoResidual hV hPN)

end General

section Perfect

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_twoResidual_of_perfect {A L : Subgroup Γ} (hLA : L ≤ A) (hL : ⁅L, L⁆ = L) :
    L ≤ twoResidual A := by
  have hnorm : L ≤ Subgroup.normalizer ((L ⊓ twoResidual A : Subgroup Γ) : Set Γ) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_twoResidual A (hLA hx)⟩
  have h2 : ∀ y ∈ L, ∃ k : ℕ, y ^ 2 ^ k ∈ L ⊓ twoResidual A := fun y hy => by
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient A y (hLA hy)
    exact ⟨k, L.pow_mem hy _, hk⟩
  have := twoResidual_le_of_isTwoQuotient inf_le_left hnorm h2
  rw [twoResidual_eq_of_perfect hL] at this
  exact fun x hx => (this hx).2

theorem twoResidual_sup_eq_of_perfect {L S₀ : Subgroup Γ} (hL : ⁅L, L⁆ = L)
    (hS : IsPGroup 2 S₀) (hn : S₀ ≤ Subgroup.normalizer (L : Set Γ)) :
    twoResidual (L ⊔ S₀) = L := by
  have hnorm : L ⊔ S₀ ≤ Subgroup.normalizer (L : Set Γ) := sup_le Subgroup.le_normalizer hn
  apply le_antisymm
  · exact twoResidual_le_of_isTwoQuotient le_sup_left hnorm
      (B6.isTwoQuotient_of_sup_eq hS hnorm (sup_comm S₀ L))
  · exact le_twoResidual_of_perfect le_sup_left hL

end Perfect


namespace NatCtx

variable {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hV)))} (c : NatCtx H T M V hV I)

include c in
theorem le_M_of_rho_le_normalizer {P : Subgroup G} (hPH : P ≤ H) (hSP : baum T ≤ P)
    (hmP : MinParabolic P (baum T) (P ⊓ M))
    (hρ : autI hV P ≤ Subgroup.normalizer
      ((autI hV (baum T) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV)))) :
    P ≤ M := by
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPH.trans c.hHN
  have hSS : autI hV (baum T) ≤ autI hV P := autI_mono hV hSP
  set SC : Subgroup G := preI hV P hPN (autI hV (baum T)) with hSC
  have hSSC : baum T ≤ SC := fun s hs =>
    (mem_preI hV).2 ⟨hSP hs, convI_mem_autI hV hs (hPN (hSP hs))⟩
  have hSCP : SC ≤ P := preI_le hV
  have hsyl : IsSylowTwoOf (baum T) SC := A4.isSylowTwoOf_mono hmP.isSylow hSSC hSCP
  have hSCM : SC ≤ M := by
    intro n hn
    obtain ⟨hnP, hnS⟩ := (mem_preI hV).1 hn
    obtain ⟨s, hs, hsn⟩ := (mem_autI hV).1 hnS
    have h1 : convI hV (⟨n, hPN hnP⟩ * s⁻¹) = 1 := by
      rw [map_mul, map_inv, hsn]
      exact mul_inv_cancel _
    have h2 : n * (s : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hsT : (s : G) ∈ T := hs.1
    have hsH : (s : G) ∈ H := c.min.isSylow.1 hsT
    have h3 : n * (s : G)⁻¹ ∈ M := c.cent_le_M ⟨H.mul_mem (hPH hnP) (H.inv_mem hsH), h2⟩
    have := M.mul_mem h3 (c.min.le hsT)
    simpa using this
  have hkey : ∀ q ∈ P, ∀ y ∈ SC, q * y * q⁻¹ ∈ SC := by
    intro q hq y hy
    obtain ⟨hyP, hyS⟩ := (mem_preI hV).1 hy
    have hqyP : q * y * q⁻¹ ∈ P := P.mul_mem (P.mul_mem hq hyP) (P.inv_mem hq)
    refine (mem_preI hV).2 ⟨hqyP, ?_⟩
    have h1 : convHom hV P hPN ⟨q * y * q⁻¹, hqyP⟩ =
        convHom hV P hPN ⟨q, hq⟩ * convHom hV P hPN ⟨y, hyP⟩ * (convHom hV P hPN ⟨q, hq⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    have hqρ : convHom hV P hPN ⟨q, hq⟩ ∈ Subgroup.normalizer
        ((autI hV (baum T) : Subgroup (MulAut (IntMod V hV))) :
          Set (MulAut (IntMod V hV))) :=
      hρ (convI_mem_autI hV hq (hPN hq))
    exact (Subgroup.mem_normalizer_iff.1 hqρ _).1 hyS
  intro p hp
  have hpSC : p ∈ Subgroup.normalizer (SC : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hkey p hp y, fun hy => ?_⟩
    have := hkey p⁻¹ (P.inv_mem hp) _ hy
    simpa [mul_assoc] using this
  obtain ⟨n, hn, m, hm, rfl⟩ := exists_mul_normalizer_of_sylow hsyl hpSC
  have hmPm : m ∈ P := by
    have := P.mul_mem (P.inv_mem (hSCP hn)) hp
    simpa using this
  have hmM : m ∈ M := (hmP.inf_normalizer_le ⟨hmPm, hm⟩).2
  exact M.mul_mem (hSCM hn) hmM


include c in
theorem exists_factor_le_rho {P : Subgroup G} (hPH : P ≤ H) (hSP : baum T ≤ P)
    (hPK : P ≤ twoResidual H ⊔ baum T) (hPM : ¬ P ≤ M)
    (hmP : MinParabolic P (baum T) (P ⊓ M)) : ∃ L ∈ I, L ≤ autI hV P := by
  by_contra hno
  push Not at hno
  exact hPM (c.le_M_of_rho_le_normalizer hPH hSP hmP
    (c.le_normalizer_star (c.rho_le hPK) (autI_mono hV hSP) hno))

omit [Finite G] in
include c in
theorem iSup_le_normalizer {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV))) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases h : L' = L
  · rw [h]
    exact Subgroup.le_normalizer
  · exact le_normalizer_of_commuting (c.comm L hL L' hL' (Ne.symm h))

include c in
theorem rho_eq {P : Subgroup G} (hPH : P ≤ H) (hSP : baum T ≤ P)
    (hmP : MinParabolic P (baum T) (P ⊓ M)) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I)
    (hLP : L ≤ autI hV P) : autI hV P = L ⊔ autI hV (baum T) := by
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPH.trans c.hHN
  have hSS : autI hV (baum T) ≤ autI hV P := autI_mono hV hSP
  have hB : L ⊔ autI hV (baum T) ≤ autI hV P := sup_le hLP hSS
  have hP'P : preI hV P hPN (L ⊔ autI hV (baum T)) ≤ P := preI_le hV
  have hSP' : baum T ≤ preI hV P hPN (L ⊔ autI hV (baum T)) := fun s hs =>
    (mem_preI hV).2 ⟨hSP hs, Subgroup.mem_sup_right (convI_mem_autI hV hs (hPN (hSP hs)))⟩
  have hrho : autI hV (preI hV P hPN (L ⊔ autI hV (baum T))) = L ⊔ autI hV (baum T) :=
    autI_preI hV hB
  have hP'M : ¬ preI hV P hPN (L ⊔ autI hV (baum T)) ≤ M := fun h =>
    c.not_le_rho_M L hL (le_sup_left.trans (hrho ▸ autI_mono hV h))
  have hP'eq : preI hV P hPN (L ⊔ autI hV (baum T)) = P := by
    by_contra hne
    exact hP'M ((hmP.le_of_lt hSP' (lt_of_le_of_ne hP'P hne)).trans inf_le_right)
  rw [← hrho, hP'eq]

include c in
theorem rho_twoResidual_eq {P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I)
    (hρ : autI hV P = L ⊔ autI hV (baum T)) : autI hV (twoResidual P) = L := by
  obtain ⟨n, hn, hnat⟩ := c.nat L hL
  obtain ⟨hn1, F, iF, iFin, hF, ⟨e⟩⟩ := exists_equiv_sl2 hnat
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hperf : ⁅L, L⁆ = L := commutator_eq_of_equiv_sl2 h4 e
  have hS := c.sylow_star
  rw [autI_twoResidual_eq hV hPN, hρ]
  exact twoResidual_sup_eq_of_perfect hperf hS.2.1
    (fun x hx => c.iSup_le_normalizer hL (hS.1 hx))

end NatCtx

end CFSG.Quasithin.C126.Nat
