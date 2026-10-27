module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBY
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBTriv

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace BCtx

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx T M L V g D)

include c in
theorem relIndex_inf_L_odd : ¬ 2 ∣ (T ⊓ L).relIndex L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 T (L ⊔ T) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_sup_right, c.h.sylow.1, c.h.faithful.1.2.2.1⟩
  have hLN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (c.h.T_le.trans c.h.normal)
  have h2 := hT.inf_of_le_normalizer le_sup_left hLN
  exact (CFSG.ABGLocalTools.isSylowOf_iff.mp h2).2.2

include c in
theorem sq_mem_V {s : G} (hs : s ∈ T ⊓ L) : s ^ 2 ∈ V := by
  obtain ⟨hsT, hsL⟩ := Subgroup.mem_inf.mp hs
  have hsN := c.L_le_N hsL
  by_cases hρ : c.ρ s = 1
  · have hsQ : s ∈ Subgroup.centralizer (V : Set G) := (c.ρ.eq_one_iff hsN).mp hρ
    rw [c.isElemAbelian_Q.2 s hsQ]
    exact V.one_mem
  · obtain ⟨k, hk⟩ := c.h.sylow.1 ⟨s, hsT⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h8 : c.ρ s ^ 8 = 1 :=
      perm5_pow_eight_of_two_power (k := k)
        (by rw [← PermRho.apply_pow hsN, hk', PermRho.apply_one])
    have hsq : c.ρ s * c.ρ s = 1 := perm5_sq_eq_one_of_sign_one (c.sign_rho_L s hsL) h8
    obtain ⟨y, hyL, -, hy2, hyρ2, hyρ1, hys⟩ := c.exists_y
    have hyN := c.L_le_N hyL
    obtain ⟨π, hπ⟩ := perm5_isConj_of_involution hyρ2 hsq hyρ1 hρ
      (by rw [hys, c.sign_rho_L s hsL])
    obtain ⟨n, hnN, hn⟩ := c.ρ.exists_eq π
    have hy'L : n * y * n⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (c.N_le_normalizer_L hnN) y).mp hyL
    have hy'N := c.L_le_N hy'L
    have hy'2 : (n * y * n⁻¹) * (n * y * n⁻¹) = 1 := by
      calc n * y * n⁻¹ * (n * y * n⁻¹) = n * (y * y) * n⁻¹ := by group
        _ = 1 := by rw [← pow_two, hy2]; group
    have hρy' : c.ρ (n * y * n⁻¹) = c.ρ s := by
      rw [PermRho.apply_conj hnN hyN, hn]
      exact hπ
    have hq : (n * y * n⁻¹)⁻¹ * s ∈ Subgroup.centralizer (V : Set G) :=
      (c.ρ.eq_iff hy'N hsN).mp hρy'
    have hq2 : ((n * y * n⁻¹)⁻¹ * s) * ((n * y * n⁻¹)⁻¹ * s) = 1 := by
      rw [← pow_two]
      exact c.isElemAbelian_Q.2 _ hq
    have hy'inv : (n * y * n⁻¹)⁻¹ = n * y * n⁻¹ := inv_eq_of_mul_eq_one_right hy'2
    have hv := c.L_comm_Q _ hy'L _ hq
    have key : s * s = ((n * y * n⁻¹) * ((n * y * n⁻¹)⁻¹ * s) * (n * y * n⁻¹)⁻¹ *
        ((n * y * n⁻¹)⁻¹ * s)⁻¹) * (((n * y * n⁻¹)⁻¹ * s) * ((n * y * n⁻¹)⁻¹ * s)) := by
      generalize n * y * n⁻¹ = z at *
      calc s * s = (z * (z⁻¹ * s)) * (z * (z⁻¹ * s)) := by group
        _ = (z * (z⁻¹ * s) * z⁻¹ * (z⁻¹ * s)⁻¹) * ((z⁻¹ * s) * (z⁻¹ * s)) := by
          rw [hy'inv]; group
    rw [pow_two, key, hq2, mul_one]
    exact hv

include c in
theorem commutator_inf_L_le : ⁅T ⊓ L, T ⊓ L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro s hs s' hs'
  have hss' : s * s' ∈ T ⊓ L := (T ⊓ L).mul_mem hs hs'
  have h1 := c.sq_mem_V hss'
  have h2 := V.inv_mem (c.sq_mem_V hs)
  have h3 := V.inv_mem (c.sq_mem_V hs')
  have hs'N : s' ∈ Subgroup.normalizer (V : Set G) := c.T_le_N (Subgroup.mem_inf.mp hs').1
  have h4 : s'⁻¹ * (s ^ 2)⁻¹ * s' ∈ V := by
    have := conj_mem ((Subgroup.normalizer (V : Set G)).inv_mem hs'N) h2
    simpa using this
  have : ⁅s, s'⁆ = (s * s') ^ 2 * (s'⁻¹ * (s ^ 2)⁻¹ * s') * (s' ^ 2)⁻¹ := by
    simp only [commutatorElement_def, pow_two]
    group
  rw [this]
  exact V.mul_mem (V.mul_mem h1 h4) h3

include c in
theorem inf_Q_L_le_V {q : G} (hqQ : q ∈ Subgroup.centralizer (V : Set G)) (hqL : q ∈ L) :
    q ∈ V := by
  by_contra hqV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqT : q ∈ T := c.Q_le_T hqQ
  have hqN := c.L_le_N hqL
  have hq2 : q ^ 2 = 1 := c.isElemAbelian_Q.2 q hqQ
  have hq1 : q ≠ 1 := fun h => hqV (h ▸ V.one_mem)
  refine generalized_thompson_transfer_two_subgroup (X := L) (H := T ⊓ L) (K := V)
    inf_le_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr c.relIndex_inf_L_odd)
    (le_inf c.h.toHyp611.le_T c.V_le_L)
    (fun h hh k hk => conj_mem (c.T_le_N (Subgroup.mem_inf.mp hh).1) hk)
    c.commutator_inf_L_le (g := q) ⟨hqT, hqL⟩ hqV (orderOf_eq_prime hq2 hq1) ?_ ?_
  · intro a ha _
    have h1 := c.L_comm_Q a⁻¹ (L.inv_mem ha) q hqQ
    have h2 := conj_mem ((Subgroup.normalizer (V : Set G)).inv_mem hqN) h1
    simpa [mul_assoc] using h2
  · rw [c.h.faithful.1.2.1.2.1]
    exact hqL

end BCtx

end CFSG.Quasithin.H13.GM22
