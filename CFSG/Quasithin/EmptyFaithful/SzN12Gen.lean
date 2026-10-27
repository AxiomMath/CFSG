module

public import CFSG.Quasithin.EmptyFaithful.SzN3V2
public import CFSG.Quasithin.EmptyFaithful.A38cAutOn
public import CFSG.Quasithin.EmptyFaithful.S153D16
public import CFSG.Quasithin.EmptyFaithful.SzN4Local

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Facts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN12_V_facts (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) {v : G} (hv : v ∈ VZ T M) :
    v ∈ Subgroup.normalizer (L : Set G) ∧ (∀ x ∈ pCoreOf 2 L, v * x = x * v) ∧
      ∀ l ∈ L, v * l * v⁻¹ * l⁻¹ ∈ blockU L := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := ctx.facts
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ ctx.conc.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := ctx.c16.R_norm
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := ctx.conc.2.2.2.2.2
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    S153D.pCoreOf_sup_R153_le hF hLI hLq hRN
  have hVc := S153D.VZ_le_centerOf hh ctx.ctx hF hLI hO
  have hvQ := hVc hv
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := hRN (hO hvQ.1)
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ R153 T V₁ Yp) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hvQc : ∀ x ∈ L, v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
    intro x hx
    have h1 : v * x * v⁻¹ * x⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hvN x).mp hx
      exact L.mul_mem this (L.inv_mem hx)
    have h2 : v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) := by
      have h3 : x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) :=
        (Subgroup.mem_normalizer_iff.mp (hLQ hx) _).mp ((pCoreOf 2 _).inv_mem hvQ.1)
      have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 _).mul_mem hvQ.1 h3
    have hmem : v * x * v⁻¹ * x⁻¹ ∈ L ⊓ pCoreOf 2 (L ⊔ R153 T V₁ Yp) := ⟨h1, h2⟩
    have hle : L ⊓ pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ pCoreOf 2 L :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hLQ hg⟩)
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hle hmem
  refine ⟨hvN, fun x hx => ?_, fun l hl => szN4_conj_comm_mem_blockU hperf hvN hvQc l hl⟩
  have hxQ : x ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) := pCoreOf_le_pCoreOf_sup_of_normalizer hRN hx
  exact (Subgroup.mem_centralizer_iff.mp hvQ.2 x hxQ).symm

end Facts

section Aux

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem szN12_comm_le_aux (h113 : StageLemma14113) (hhyp : Hyp153 G T Mc M)
    {hV : IsElemAbelian 2 (VZ T M)} {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) hV))}
    {tb : MulAut (IntMod (VZ T M) hV)} (hS : OfourStruct (autI hV M) L₁ L₂ tb) {P : Subgroup G}
    (hP : ∀ g : G, g ∈ Y153 Mc M → g ∈ Subgroup.centralizer
        (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) → ∃ k : ℕ, g ^ 2 ^ k ∈ P) :
    (commV L₂).map (inclMod hV) ≤ ⁅(commV L₂).map (inclMod hV), P⁆ := by
  obtain ⟨x, hxL, hx3, hx1⟩ := exists_orderThree hS.nat₂
  have hxord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  have hxM : x ∈ autI hV M := hS.L₂_le hxL
  have hxO : x ∈ oTwoUpper (autI hV M) :=
    mem_oTwoUpper_of_odd hxM (by rw [hxord]; decide)
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := hhyp.autOn_Y153 h113
  have hxY : x ∈ autI hV (Y153 Mc M) := by rw [e]; exact hxO
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hxY
  have hgC : (g : G) ∈ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
    refine (mem_centralizer_map_inclMod_iff hV g.2 (commV L₁)).2 fun u hu => ?_
    have hgx : convI hV ⟨(g : G), g.2⟩ = x := hg
    rw [hgx]
    exact hS.L₂_fix₁ hxL hu
  obtain ⟨k, hk⟩ := hP g hgY hgC
  have hx'L : x ^ 2 ^ k ∈ L₂ := L₂.pow_mem hxL _
  have hx'3 : (x ^ 2 ^ k) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have hx'1 : x ^ 2 ^ k ≠ 1 := by
    intro h1
    have hdvd : 3 ∣ 2 ^ k := hxord ▸ orderOf_dvd_of_pow_eq_one h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hx'ord : orderOf (x ^ 2 ^ k) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx'3 hx'1
  have hst : ∀ l ∈ L₂, ∀ u ∈ commV L₂, l u ∈ commV L₂ :=
    fun l hl u hu => commV_stable L₂ hl hu
  have hfix : ∀ u ∈ commV L₂, (x ^ 2 ^ k) u = u → u = 1 := by
    intro u hu hxu
    by_contra hu1
    exact hx'1 (eq_one_of_odd_of_fixed hS.nat₂ hst hx'L (by rw [hx'ord]; decide) hu hu1 hxu)
  have hconv : convI hV (g ^ 2 ^ k) = x ^ 2 ^ k := by rw [map_pow, hg]
  intro v hv
  obtain ⟨u₀, hu₀, rfl⟩ := hv
  obtain ⟨u, hu, hu0⟩ := szN3_exists_mul_inv_apply_eq (hst _ hx'L) hfix u₀ hu₀
  have h2 : ((x ^ 2 ^ k) u).val = (g : G) ^ 2 ^ k * u.val * ((g : G) ^ 2 ^ k)⁻¹ := by
    rw [← hconv, convI_apply_val]
    simp
  have hcomm : ⁅u.val, (g : G) ^ 2 ^ k⁆ = inclMod hV u₀ := by
    rw [← hu0, map_mul, map_inv, inclMod_apply, inclMod_apply, h2, commutatorElement_def]
    group
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator ⟨u, hu, rfl⟩ hk

end Aux

end CFSG.Quasithin
