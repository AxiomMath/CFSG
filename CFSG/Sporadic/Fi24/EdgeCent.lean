module

public import CFSG.Sporadic.Fi24.Generate

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def x1 :
    R := jR (m1 : J) * xb * (jR (m1 : J))⁻¹

theorem x1_eq :
    x1 = jR (m1 : J) * xb * (jR (m1 : J))⁻¹ := rfl

theorem m1_mem_MR :
    jR (m1 : J) ∈ MR := Subgroup.mem_map.2 ⟨m1, m1.2, rfl⟩

theorem x1_mem_star :
    x1 ∈ LocalClass D24 tR := by
  have h := conj_mem_localClass_of_commute pair_R (commute_tR_of_mem_MR m1_mem_MR)
    xb_mem_localClass
  rw [x1_eq]
  exact h

theorem fi23EquivJMR_m1 :

    fi23EquivJMR ⟨jR (m1 : J), m1_mem_MR⟩ = exists_conj_y1.choose := by
  have h : (⟨jR (m1 : J), m1_mem_MR⟩ : MR) = (M.equivMapOfInjective jR jR_injective) m1 := rfl
  rw [h]
  show fi23EquivM (mREquiv ((M.equivMapOfInjective jR jR_injective) m1)) = _
  rw [show mREquiv = (M.equivMapOfInjective jR jR_injective).symm from rfl,
    MulEquiv.symm_apply_apply, fi23EquivM_m1]

theorem starEquiv_x1 :
    (starEquiv ⟨x1, x1_mem_star⟩ : Fi23.J) = y1 := by
  have h := starEquiv_conj m1_mem_MR ⟨xb, xb_mem_localClass⟩ x1_mem_star
  rw [fi23EquivJMR_m1] at h
  exact h.trans exists_conj_y1.choose_spec

theorem x1_mem :
    x1 ∈ LocalClass D24 tR ∩ LocalClass D24 xb := by
  refine ⟨x1_mem_star, ?_⟩
  have hc := (localPoints_tR.mem_localClass_iff Fi23.pair_J ⟨xb, xb_mem_localClass⟩
    ⟨x1, x1_mem_star⟩).2
  apply hc
  show ((starEquiv ⟨x1, x1_mem_star⟩ : Fi23.D23) : Fi23.J) ∈
    LocalClass Fi23.D23 ((starEquiv ⟨xb, xb_mem_localClass⟩ : Fi23.D23) : Fi23.J)
  rw [starEquiv_x1]
  exact y1_mem

theorem jR_t1J :
    jR t1J = tR * x1 := by
  rw [t1J_eq, map_mul, map_mul, map_inv, jR_tJ, x1_eq]
  have h := commute_tR_of_mem_MR m1_mem_MR
  calc jR (m1 : J) * (tR * xb) * (jR (m1 : J))⁻¹ =
      (jR (m1 : J) * tR) * xb * (jR (m1 : J))⁻¹ := by group
    _ = tR * jR (m1 : J) * xb * (jR (m1 : J))⁻¹ := by rw [h]
    _ = tR * (jR (m1 : J) * xb * (jR (m1 : J))⁻¹) := by group

section D

variable (hPF : PolarFacts)
  (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Fi22.D) (σ : Equiv.Perm Fi22.D),
    (∀ g : Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Fi22.pair_D g = Pair.conjPerm Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Fi22.pair_D (χ : Fi22.J))
  {e : J} (he : EdgeSwap e)
include hPF hfix22 hcent22 he

theorem pow_four_of_commute
    {x' : R} (hx' : x' ∈ LocalClass D24 tR ∩ LocalClass D24 xb) {y : R}
    (hy : y ∈ CE) (hcomm : ∀ ℓ ∈ LE, ℓ * x' * ℓ⁻¹ = x' → y * ℓ = ℓ * y) : y ^ 4 = 1 := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 hPF) ⟨tR, tR_mem_D24⟩ ⟨xb, xb_mem_D24⟩ tR_ne_xb
    tR_xb_comm
  have hW := exists_not_commute_of_edgeEquiv Fi22.pair_D ψ hψc Fi22.center_eq_bot
  set ρ := edgeHom pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
    Fi22.center_eq_bot with hρ
  have hrangeL := range_edgeHomL pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ
    hψc hψt Fi22.center_eq_bot Fi22.index_innerTau_range (inf_le_left : CE ≤ _) commutator_LE
    (by rw [Fi22.card_tauGroup]; exact card_LE) (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
  have hsurj := edgeHomC_surjective pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ
    hψc hψt Fi22.center_eq_bot Fi22.index_innerTau_range (inf_le_left : CE ≤ _) commutator_LE
    (by rw [Fi22.card_tauGroup]; exact card_LE) (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
    (jR_mem_CE he) (edgeHom_swap_not_mem he ψ hψc hψt hfix22)
  have hy1 : y ∈ Subgroup.centralizer ({tR * xb} : Set R) := (Subgroup.mem_inf.1 hy).1
  set χ := ψ ⟨x', hx'⟩
  have hσ : ∀ g : Fi22.J, g * χ = χ * g →
      ((ρ ⟨y, hy1⟩ : tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) * Pair.conjPerm Fi22.pair_D g =
        Pair.conjPerm Fi22.pair_D g * ((ρ ⟨y, hy1⟩ : tauGroup Fi22.pair_D) :
          Equiv.Perm Fi22.D) := by
    intro g hg
    have hmem : innerTau Fi22.pair_D g ∈ (innerTau Fi22.pair_D).range := ⟨g, rfl⟩
    rw [← hrangeL] at hmem
    obtain ⟨ℓ, hℓ⟩ := hmem
    have hfix : (ℓ : R) * x' * (ℓ : R)⁻¹ = x' := by
      have h1 : ((edgeHom pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
          Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) :
            tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) χ =
          ψ (edgeHomW pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
            Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ)
              ⟨x', hx'⟩) :=
        edgeHom_apply pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
          hψt Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) ⟨x', hx'⟩
      have h2 : ((edgeHom pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
          Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) :
            tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) χ = χ := by
        have h0 : edgeHom pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
            Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
              innerTau Fi22.pair_D g := hℓ
        rw [h0]
        apply Subtype.ext
        show g * (χ : Fi22.J) * g⁻¹ = χ
        rw [hg, mul_inv_cancel_right]
      rw [h1] at h2
      have h3 := Subtype.ext_iff.1 (ψ.injective h2)
      exact h3
    have hyℓ := hcomm ℓ ℓ.2 hfix
    have : ρ ⟨y, hy1⟩ * ρ (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
        ρ (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) * ρ ⟨y, hy1⟩ := by
      rw [← map_mul, ← map_mul]
      refine congrArg ρ (Subtype.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hyℓ
    have h' := Subtype.ext_iff.1 this
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    have hℓ' : ((ρ (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) :
        tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) = Pair.conjPerm Fi22.pair_D g := by
      have h0 := Subtype.ext_iff.1 hℓ
      exact h0
    rw [hℓ'] at h'
    exact h'
  have hsq : ρ ⟨y, hy1⟩ ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    rcases hcent22 χ _ hσ with h | h
    · rw [h, one_pow]
    · rw [h, ← map_pow, sq, Pair.mul_self Fi22.pair_D χ.2, map_one]
  have hker := edgeHomC_ker pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    hψt Fi22.center_eq_bot (inf_le_left : CE ≤ _) hsurj (card_CE he hW) tR_mul_xb_mem_CE
    (⟨y, hy⟩ * ⟨y, hy⟩) (by
      rw [map_mul, ← sq]
      exact hsq)
  rw [Subgroup.coe_mul] at hker
  have hy2 : y * y = 1 ∨ y * y = tR * xb := hker
  have h4 : y ^ 4 = y * y * (y * y) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rcases hy2 with h | h
  · rw [h4, h, one_mul]
  · rw [h4, h, tR_mul_xb_sq]

theorem centralizer_inter_isTwoGroup :
    ∀ y ∈ Subgroup.centralizer ({tJ} : Set J),
    (∀ x ∈ Subgroup.centralizer ({t1J} : Set J), x ∈ Subgroup.centralizer ({tJ} : Set J) →
      y * x = x * y) → ∃ r : ℕ, y ^ (2 ^ r) = 1 := by
  intro y hy hcomm
  have hyC : jR y ∈ CE := by
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_R.2 ?_, jR_mem_JR y⟩
    rw [← jR_tJ, show jR y * jR tJ = jR (y * tJ) from (map_mul jR y tJ).symm,
      show jR tJ * jR y = jR (tJ * y) from (map_mul jR tJ y).symm, mem_centralizer_J.1 hy]
  have h4 := pow_four_of_commute hPF hfix22 hcent22 he x1_mem hyC (fun ℓ hℓ hfix => by
    have hℓCE := (Subgroup.mem_inf.1 hℓ).1
    obtain ⟨l, rfl⟩ : ∃ l : J, jR l = ℓ := by
      have := (Subgroup.mem_inf.1 hℓCE).2
      rw [← range_jR] at this
      exact this
    have hlT : jR l * tR = tR * jR l := mem_centralizer_R.1 (Subgroup.mem_inf.1 hℓ).2
    have hl0 : l ∈ Subgroup.centralizer ({tJ} : Set J) := by
      apply mem_centralizer_J.2
      apply jR_injective
      rw [show jR (l * tJ) = jR l * jR tJ from map_mul jR l tJ,
        show jR (tJ * l) = jR tJ * jR l from map_mul jR tJ l, jR_tJ]
      exact mem_centralizer_R.1 (Subgroup.mem_inf.1 hℓCE).1
    have hlx : jR l * x1 = x1 * jR l := by
      calc jR l * x1 = jR l * x1 * (jR l)⁻¹ * jR l := by group
        _ = x1 * jR l := by rw [hfix]
    have hl1 : l ∈ Subgroup.centralizer ({t1J} : Set J) := by
      apply mem_centralizer_J.2
      apply jR_injective
      rw [show jR (l * t1J) = jR l * jR t1J from map_mul jR l t1J,
        show jR (t1J * l) = jR t1J * jR l from map_mul jR t1J l, jR_t1J, ← mul_assoc, hlT,
        mul_assoc, hlx, mul_assoc]
    rw [show jR y * jR l = jR (y * l) from (map_mul jR y l).symm,
      show jR l * jR y = jR (l * y) from (map_mul jR l y).symm, hcomm l hl1 hl0])
  refine ⟨2, ?_⟩
  apply jR_injective
  rw [map_pow, map_one]
  exact h4

end D

end CFSG.Sporadic.Fi24
