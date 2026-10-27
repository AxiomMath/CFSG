module

public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaPlanes
import CFSG.GroupTheory.BraidCommutator
import CFSG.GroupTheory.RankOneQuotient

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

namespace Sec5Hyp

private theorem mem_of_commutator_mem_of_cap (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    {a y : G} (ha : a ∈ U) (ha1 : a ≠ 1) (hy : y ∈ ⁅Pc M V, U'⁆)
    (hay : ⁅a, y⁆ ∈ V) : y ∈ V := by
  have hyP : y ∈ Pc M V := hS.commutator_le_Pc hU' hy
  have hya : ⁅y, a⁆ ∈ V := by
    rw [← commutatorElement_inv]
    exact V.inv_mem hay
  have hyC : y ∈ Subgroup.centralizer (U : Set G) :=
    hS.mem_centralizer_of_commutator_mem hU ha ha1 hyP hya
  have hmem : y ∈ Pc M V ⊓ Subgroup.centralizer (U : Set G) := Subgroup.mem_inf.mpr ⟨hyP, hyC⟩
  rw [hS.Pc_inf_centralizer_eq_commutator hU] at hmem
  exact hcap ▸ Subgroup.mem_inf.mpr ⟨hy, hmem⟩

private theorem exists_partner_data (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    (hcap' : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G)) = V)
    {a : G} (ha : a ∈ U) (ha1 : a ≠ 1) :
    ∃ y₀ ∈ ⁅Pc M V, U'⁆, y₀ ∉ V ∧ ⁅a, y₀⁆ ∉ V ∧
      ⁅a, y₀⁆ ∉ Subgroup.centralizer (U' : Set G) ∧ ⁅a, y₀⁆ ∈ ⁅Pc M V, U⁆ ∧
      y₀ * ⁅a, y₀⁆ = ⁅a, y₀⁆ * y₀ := by
  classical
  have hVE' : V ≤ ⁅Pc M V, U'⁆ := hS.V_le_commutator hU'
  have hne : V ≠ ⁅Pc M V, U'⁆ := by
    intro hEq
    have hcard : Nat.card V ^ 3 = Nat.card V := by
      rw [← hS.card_commutator_Pc hU']
      exact congrArg (fun W : Subgroup G => Nat.card ↥W) hEq.symm
    have hlt : Nat.card V < Nat.card V ^ 3 := by
      simpa using Nat.pow_lt_pow_right (by have := hS.toRootHyp.four_le_card; omega)
        (by norm_num : 1 < 3)
    omega
  obtain ⟨y₀, hy₀E', hy₀V⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hVE' hne)
  have hy₀P : y₀ ∈ Pc M V := hS.commutator_le_Pc hU' hy₀E'
  have hz₀E : ⁅a, y₀⁆ ∈ ⁅Pc M V, U⁆ := by
    have h1 : ⁅a, y₀⁆ ∈ ⁅U, Pc M V⁆ := Subgroup.commutator_mem_commutator ha hy₀P
    simpa only [Subgroup.commutator_comm] using h1
  have hz₀V : ⁅a, y₀⁆ ∉ V := fun h =>
    hy₀V (hS.mem_of_commutator_mem_of_cap hU hU' hcap ha ha1 hy₀E' h)
  have hz₀P : ⁅a, y₀⁆ ∈ Pc M V := hS.commutator_le_Pc hU hz₀E
  have hy₀y : y₀ * ⁅a, y₀⁆ = ⁅a, y₀⁆ * y₀ := by
    have h := hS.commutator_commutator_eq_one hU (Subgroup.mem_sup_left ha) hy₀P
    exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  have hz₀C' : ⁅a, y₀⁆ ∉ Subgroup.centralizer (U' : Set G) := by
    intro hC
    apply hz₀V
    have hmem : ⁅a, y₀⁆ ∈ Pc M V ⊓ Subgroup.centralizer (U' : Set G) :=
      Subgroup.mem_inf.mpr ⟨hz₀P, hC⟩
    rw [hS.Pc_inf_centralizer_eq_commutator hU'] at hmem
    exact hcap' ▸ Subgroup.mem_inf.mpr ⟨hz₀E, hmem⟩
  exact ⟨y₀, hy₀E', hy₀V, hz₀V, hz₀C', hz₀E, hy₀y⟩

private theorem exists_partner_of_cap (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    (hcap' : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G)) = V)
    {a : G} (ha : a ∈ U) (ha1 : a ≠ 1) :
    ∃ b ∈ U', b ≠ 1 ∧ ∃ z ∈ ⁅Pc M V, U⁆, z ∉ V ∧ ⁅a, ⁅b, z⁆⁆ = z := by
  classical
  obtain ⟨y₀, hy₀E', hy₀V, hz₀V, hz₀C', hz₀E, hy₀y⟩ :=
    hS.exists_partner_data hU hU' hcap hcap' ha ha1
  have hy₀P : y₀ ∈ Pc M V := hS.commutator_le_Pc hU' hy₀E'
  have hz₀P : ⁅a, y₀⁆ ∈ Pc M V := hS.commutator_le_Pc hU hz₀E
  obtain ⟨v, hv, b, hb, hy₀eq⟩ :=
    hS.exists_eq_mul_commutator hU' hz₀P hz₀C' hy₀E' hy₀y
  have hy₀mul : y₀ * y₀ = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU' y₀ (Subgroup.mem_sup_right hy₀E')
  have hy₀v : y₀ * v = v * y₀ :=
    (Subgroup.mem_centralizer_iff.mp
      ((inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hy₀P) v hv).symm
  have hav : a * v = v * a :=
    (Subgroup.mem_centralizer_iff.mp ((hS.le_M_of_mem_sigmaSet hU).2 ha) v hv).symm
  have hzv : v * ⁅a, y₀⁆ = ⁅a, y₀⁆ * v :=
    Subgroup.mem_centralizer_iff.mp
      ((inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hz₀P) v hv
  have hbv : ⁅b, ⁅a, y₀⁆⁆ = v * y₀ := by
    have h1 : ⁅⁅a, y₀⁆, b⁆ = v⁻¹ * y₀ := by
      conv_rhs => rw [hy₀eq]
      group
    rw [← commutatorElement_inv, h1, mul_inv_rev, inv_inv,
      show y₀⁻¹ = y₀ from inv_eq_iff_mul_eq_one.mpr hy₀mul]
    exact hy₀v
  have hfix : ⁅a, ⁅b, ⁅a, y₀⁆⁆⁆ = ⁅a, y₀⁆ := by
    have h1 : ⁅a, v * y₀⁆ = ⁅a, y₀⁆ := by
      calc ⁅a, v * y₀⁆ = ⁅a, v⁆ * v * ⁅a, y₀⁆ * v⁻¹ :=
            commutatorElement_mul_right_eq_mul_conj a v y₀
        _ = v * ⁅a, y₀⁆ * v⁻¹ := by
            rw [show ⁅a, v⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr hav, one_mul]
        _ = ⁅a, y₀⁆ * v * v⁻¹ := by rw [hzv]
        _ = ⁅a, y₀⁆ := by group
    rw [hbv]
    exact h1
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hy₀V
    rw [hy₀eq, hb1, commutatorElement_one_right, mul_one]
    exact hv
  exact ⟨b, hb, hb1, ⁅a, y₀⁆, hz₀E, hz₀V, hfix⟩

private theorem plane_data_of_cap (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    (hcap' : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G)) = V)
    {b z : G} (hb : b ∈ U') (hb1 : b ≠ 1) (hz : z ∈ ⁅Pc M V, U⁆) (hzV : z ∉ V) :
    ⁅b, z⁆ ∈ ⁅Pc M V, U'⁆ ∧ ⁅b, z⁆ ∉ V ∧
      ⁅b, z⁆ ∉ Subgroup.centralizer (U : Set G) ∧
      z ∈ V ⊔ ⁅U, Subgroup.zpowers ⁅b, z⁆⁆ := by
  have hzP : z ∈ Pc M V := hS.commutator_le_Pc hU hz
  have hyE' : ⁅b, z⁆ ∈ ⁅Pc M V, U'⁆ := by
    have h1 : ⁅b, z⁆ ∈ ⁅U', Pc M V⁆ := Subgroup.commutator_mem_commutator hb hzP
    simpa only [Subgroup.commutator_comm] using h1
  have hyV : ⁅b, z⁆ ∉ V := fun h =>
    hzV (hS.mem_of_commutator_mem_of_cap hU' hU hcap' hb hb1 hz h)
  have hyP : ⁅b, z⁆ ∈ Pc M V := hS.commutator_le_Pc hU' hyE'
  have hyC : ⁅b, z⁆ ∉ Subgroup.centralizer (U : Set G) := by
    intro hC
    apply hyV
    have hmem : ⁅b, z⁆ ∈ Pc M V ⊓ Subgroup.centralizer (U : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyP, hC⟩
    rw [hS.Pc_inf_centralizer_eq_commutator hU] at hmem
    exact hcap ▸ Subgroup.mem_inf.mpr ⟨hyE', hmem⟩
  have hzy : z * ⁅b, z⁆ = ⁅b, z⁆ * z := by
    have h := hS.commutator_commutator_eq_one hU' (Subgroup.mem_sup_left hb) hzP
    exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  have hzmem : z ∈ ⁅Pc M V, U⁆ ⊓ Subgroup.centralizer ({⁅b, z⁆} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr hzy⟩
  rw [← hS.sup_commutator_zpowers_eq hU hyP hyC] at hzmem
  exact ⟨hyE', hyV, hyC, hzmem⟩

private theorem commutator_commutator_mem_of_mem_fSet (hS : Sec5Hyp M V)
    (h51a : Sec5.Stmt51a M V) (h51e : Sec5.Stmt51e M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    (hcap' : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G)) = V)
    {a b : G} (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1) {A : Subgroup G}
    (hA : A ∈ fSet M V) (hAE : A ≤ ⁅Pc M V, U⁆) {z : G} (hz : z ∈ A) :
    ⁅a, ⁅b, z⁆⁆ ∈ A := by
  by_cases hzV : z ∈ V
  · have hbz : ⁅b, z⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp
        ((hS.le_M_of_mem_sigmaSet hU').2 hb) z hzV).symm
    rw [hbz, commutatorElement_one_right]
    exact A.one_mem
  · obtain ⟨hyE', hyV, hyC, hzsup⟩ :=
      hS.plane_data_of_cap hU hU' hcap hcap' hb hb1 (hAE hz) hzV
    have hyP : ⁅b, z⁆ ∈ Pc M V := hS.commutator_le_Pc hU' hyE'
    have hB : V ⊔ ⁅U, Subgroup.zpowers ⁅b, z⁆⁆ ∈ fSet M V :=
      h51a U hU ⁅b, z⁆ hyP hyC
    have hzAB : z ∈ A ⊓ (V ⊔ ⁅U, Subgroup.zpowers ⁅b, z⁆⁆) :=
      Subgroup.mem_inf.mpr ⟨hz, hzsup⟩
    have hAB : A = V ⊔ ⁅U, Subgroup.zpowers ⁅b, z⁆⁆ := by
      rcases h51e A hA (V ⊔ ⁅U, Subgroup.zpowers ⁅b, z⁆⁆) hB with h | h
      · exact h
      · exact absurd (h ▸ hzAB) hzV
    rw [hAB]
    exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers _))

private theorem inv_mul_mem_of_fixed (hS : Sec5Hyp M V) (h51a : Sec5.Stmt51a M V)
    (h51e : Sec5.Stmt51e M V) (h52a : Sec5.Stmt52a M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    (hcap' : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G)) = V)
    {a b : G} (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1) {z₀ : G}
    (hz₀ : z₀ ∈ ⁅Pc M V, U⁆) (hz₀V : z₀ ∉ V) (hfix : ⁅a, ⁅b, z₀⁆⁆ = z₀) :
    ∀ z ∈ ⁅Pc M V, U⁆, z⁻¹ * ⁅a, ⁅b, z⁆⁆ ∈ V := by
  classical
  let 𝒜 : Set (Subgroup G) := {A | A ∈ fSet M V ∧ A ≤ ⁅Pc M V, U⁆}
  have hVE : ∀ v ∈ V, ∀ x ∈ ⁅Pc M V, U⁆, v * x = x * v := by
    intro v hv x hx
    exact Subgroup.mem_centralizer_iff.mp
      ((inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G))
        (hS.commutator_le_Pc hU hx)) v hv
  have hVA : ∀ A ∈ 𝒜, V ≤ A := by
    intro A hA
    obtain ⟨-, -, U₀, -, x, -, rfl⟩ := hA.1
    exact le_sup_left
  have hAE : ∀ A ∈ 𝒜, A ≤ ⁅Pc M V, U⁆ := fun A hA => hA.2
  have hcover : ∀ x ∈ ⁅Pc M V, U⁆, ∃ A ∈ 𝒜, x ∈ A := by
    intro x hx
    obtain ⟨A, hA, hxA, hAle⟩ := h52a U hU x hx
    exact ⟨A, ⟨hA, hAle⟩, hxA⟩
  have hdisj : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A = B ∨ A ⊓ B = V :=
    fun A hA B hB => h51e A hA.1 B hB.1
  have hout : ∀ A ∈ 𝒜, ∃ x ∈ ⁅Pc M V, U⁆, x ∉ A := by
    intro A hA
    have hcardA : Nat.card A = Nat.card V ^ 2 := hA.1.2.1
    have hcardE : Nat.card ↥⁅Pc M V, U⁆ = Nat.card V ^ 3 := hS.card_commutator_Pc hU
    have hlt : Nat.card V ^ 2 < Nat.card V ^ 3 :=
      Nat.pow_lt_pow_right (by have := hS.toRootHyp.four_le_card; omega)
        (by norm_num : 2 < 3)
    have hne : A ≠ ⁅Pc M V, U⁆ := by
      intro hEq
      have hc : Nat.card V ^ 2 = Nat.card V ^ 3 := by rw [← hcardA, hEq, hcardE]
      omega
    exact SetLike.exists_of_lt (lt_of_le_of_ne hA.2 hne)
  have hPP : ∀ x ∈ Pc M V, ∀ y ∈ Pc M V, ⁅x, y⁆ ∈ V := by
    intro x hx y hy
    rw [← hS.commutator_Pc_eq_V ⟨U, hU⟩]
    exact Subgroup.commutator_mem_commutator hx hy
  have haN : a ∈ Subgroup.normalizer (Pc M V : Set G) :=
    hS.toRootHyp.toHyp.le_normalizer_Pc ((hS.le_M_of_mem_sigmaSet hU).1 ha)
  have hbN : b ∈ Subgroup.normalizer (Pc M V : Set G) :=
    hS.toRootHyp.toHyp.le_normalizer_Pc ((hS.le_M_of_mem_sigmaSet hU').1 hb)
  have haC : ∀ v ∈ V, a * v = v * a := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp ((hS.le_M_of_mem_sigmaSet hU).2 ha) v hv).symm
  have hadd : ∀ x ∈ ⁅Pc M V, U⁆, ∀ y ∈ ⁅Pc M V, U⁆,
      (⁅a, ⁅b, x⁆⁆ * ⁅a, ⁅b, y⁆⁆)⁻¹ * ⁅a, ⁅b, x * y⁆⁆ ∈ V :=
    fun x hx y hy =>
      inv_mul_commutatorElement_commutatorElement_mul_mem hPP haN hbN haC
        (hS.commutator_le_Pc hU hx) (hS.commutator_le_Pc hU hy)
  have hf : ∀ A ∈ 𝒜, ∀ x ∈ A, ⁅a, ⁅b, x⁆⁆ ∈ A :=
    fun A hA x hx =>
      hS.commutator_commutator_mem_of_mem_fSet h51a h51e hU hU' hcap hcap' ha hb hb1
        hA.1 hA.2 hx
  have hfixV : z₀⁻¹ * ⁅a, ⁅b, z₀⁆⁆ ∈ V := by
    rw [hfix]
    simpa using V.one_mem
  exact inv_mul_mem_of_spread (V := V) (E := ⁅Pc M V, U⁆) (𝒜 := 𝒜)
    (f := fun z => ⁅a, ⁅b, z⁆⁆) hVE hVA hAE hcover hdisj hout hadd hf hz₀ hz₀V hfixV

private theorem commutator_pow_three_mem_of_fixed (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V) {a b : G}
    (ha : a ∈ U) (hb : b ∈ U')
    (hfixed : ∀ z ∈ ⁅Pc M V, U⁆, z⁻¹ * ⁅a, ⁅b, z⁆⁆ ∈ V)
    (hfixed' : ∀ y ∈ ⁅Pc M V, U'⁆, y⁻¹ * ⁅b, ⁅a, y⁆⁆ ∈ V) :
    ∀ x ∈ Pc M V, ⁅(a * b) ^ 3, x⁆ ∈ V := by
  have haM : a ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 ha
  have hbM : b ∈ M := (hS.le_M_of_mem_sigmaSet hU').1 hb
  have hPP : ∀ x ∈ Pc M V, ∀ y ∈ Pc M V, ⁅x, y⁆ ∈ V := by
    intro x hx y hy
    rw [← hS.commutator_Pc_eq_V ⟨U, hU⟩]
    exact Subgroup.commutator_mem_commutator hx hy
  have hsq : ∀ x ∈ Pc M V, x * x ∈ V := fun x hx => hS.toRootHyp.toHyp.mul_self_mem_of_mem_Pc hx
  have haN : a ∈ Subgroup.normalizer (Pc M V : Set G) :=
    hS.toRootHyp.toHyp.le_normalizer_Pc haM
  have hbN : b ∈ Subgroup.normalizer (Pc M V : Set G) :=
    hS.toRootHyp.toHyp.le_normalizer_Pc hbM
  have haVn : a ∈ Subgroup.normalizer (V : Set G) := hS.toRootHyp.toHyp.le_normalizer haM
  have hbVn : b ∈ Subgroup.normalizer (V : Set G) := hS.toRootHyp.toHyp.le_normalizer hbM
  have hcommU : ∀ x ∈ U ⊔ ⁅Pc M V, U⁆, ∀ y ∈ U ⊔ ⁅Pc M V, U⁆, x * y = y * x :=
    hS.mul_comm_of_mem_sup_commutator hU
  have hcommU' : ∀ x ∈ U' ⊔ ⁅Pc M V, U'⁆, ∀ y ∈ U' ⊔ ⁅Pc M V, U'⁆, x * y = y * x :=
    hS.mul_comm_of_mem_sup_commutator hU'
  have hE_of : ∀ x ∈ Pc M V, ⁅a, x⁆ ∈ ⁅Pc M V, U⁆ := by
    intro x hx
    have h1 : ⁅a, x⁆ ∈ ⁅U, Pc M V⁆ := Subgroup.commutator_mem_commutator ha hx
    simpa only [Subgroup.commutator_comm] using h1
  have hE'_of : ∀ x ∈ Pc M V, ⁅b, x⁆ ∈ ⁅Pc M V, U'⁆ := by
    intro x hx
    have h1 : ⁅b, x⁆ ∈ ⁅U', Pc M V⁆ := Subgroup.commutator_mem_commutator hb hx
    simpa only [Subgroup.commutator_comm] using h1
  have hαα : ∀ x ∈ Pc M V, ⁅a, ⁅a, x⁆⁆ ∈ V := by
    intro x hx
    have hmem := hcommU a (Subgroup.mem_sup_left ha) ⁅a, x⁆
      (Subgroup.mem_sup_right (hE_of x hx))
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hmem]
    exact V.one_mem
  have hββ : ∀ x ∈ Pc M V, ⁅b, ⁅b, x⁆⁆ ∈ V := by
    intro x hx
    have hmem := hcommU' b (Subgroup.mem_sup_left hb) ⁅b, x⁆
      (Subgroup.mem_sup_right (hE'_of x hx))
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hmem]
    exact V.one_mem
  have hαβα : ∀ x ∈ Pc M V, ⁅a, x⁆⁻¹ * ⁅a, ⁅b, ⁅a, x⁆⁆⁆ ∈ V :=
    fun x hx => hfixed ⁅a, x⁆ (hE_of x hx)
  have hβαβ : ∀ x ∈ Pc M V, ⁅b, x⁆⁻¹ * ⁅b, ⁅a, ⁅b, x⁆⁆⁆ ∈ V :=
    fun x hx => hfixed' ⁅b, x⁆ (hE'_of x hx)
  exact commutator_pow_three_mem_of_braid hPP hsq haN hbN haVn hbVn hαα hββ hαβα hβαβ

private theorem mem_Pc_of_pow_three_mem (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V) {a b : G}
    (ha : a ∈ U) (hb : b ∈ U') (h : ∀ x ∈ Pc M V, ⁅(a * b) ^ 3, x⁆ ∈ V) :
    (a * b) ^ 3 ∈ Pc M V := by
  have haM : a ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 ha
  have hbM : b ∈ M := (hS.le_M_of_mem_sigmaSet hU').1 hb
  have hM : (a * b) ^ 3 ∈ M := by
    have hab : a * b ∈ M := M.mul_mem haM hbM
    rw [pow_three']
    exact M.mul_mem (M.mul_mem hab hab) hab
  have hCV : (a * b) ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    have haC : a ∈ Subgroup.centralizer (V : Set G) := (hS.le_M_of_mem_sigmaSet hU).2 ha
    have hbC : b ∈ Subgroup.centralizer (V : Set G) := (hS.le_M_of_mem_sigmaSet hU').2 hb
    have habC : a * b ∈ Subgroup.centralizer (V : Set G) := Subgroup.mul_mem _ haC hbC
    rw [pow_three']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ habC habC) habC
  have hPcomm : ∀ p ∈ Pc M V, ⁅p, (a * b) ^ 3⁆ ∈ V := by
    intro p hp
    rw [← commutatorElement_inv]
    exact V.inv_mem (h p hp)
  obtain ⟨_, _, hSg, -, -, -, -, -, -, -⟩ := hS.exists_sigma_data hU
  exact Sec45Shape.mem_Pc_of_commutator_mem hS.toRootHyp hSg hM hCV hPcomm

private theorem exists_pow_three_mem_Pc (hS : Sec5Hyp M V) (h51a : Sec5.Stmt51a M V)
    (h51e : Sec5.Stmt51e M V) (h52a : Sec5.Stmt52a M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    {a : G} (ha : a ∈ U) (ha1 : a ≠ 1) :
    ∃ b ∈ U', b ≠ 1 ∧ (a * b) ^ 3 ∈ Pc M V := by
  classical
  have hcap' := (hS.cap_symm hU hU').mp hcap
  obtain ⟨b, hb, hb1, z₀, hz₀, hz₀V, hfix⟩ :=
    hS.exists_partner_of_cap hU hU' hcap hcap' ha ha1
  have hfixed : ∀ z ∈ ⁅Pc M V, U⁆, z⁻¹ * ⁅a, ⁅b, z⁆⁆ ∈ V :=
    hS.inv_mul_mem_of_fixed h51a h51e h52a hU hU' hcap hcap' ha hb hb1 hz₀ hz₀V hfix
  obtain ⟨hy₁E', hy₁V, -, -⟩ :=
    hS.plane_data_of_cap hU hU' hcap hcap' hb hb1 hz₀ hz₀V
  have hfix' : ⁅b, ⁅a, ⁅b, z₀⁆⁆⁆ = ⁅b, z₀⁆ := by rw [hfix]
  have hfixed' : ∀ y ∈ ⁅Pc M V, U'⁆, y⁻¹ * ⁅b, ⁅a, y⁆⁆ ∈ V :=
    hS.inv_mul_mem_of_fixed h51a h51e h52a hU' hU hcap' hcap hb ha ha1 hy₁E' hy₁V hfix'
  have haction : ∀ x ∈ Pc M V, ⁅(a * b) ^ 3, x⁆ ∈ V :=
    hS.commutator_pow_three_mem_of_fixed hU hU' ha hb hfixed hfixed'
  exact ⟨b, hb, hb1, hS.mem_Pc_of_pow_three_mem hU hU' ha hb haction⟩

private theorem inv_mul_not_mem_Pc (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U⁆ : Set G)) = V)
    {a u : G} (ha : a ∈ U) (ha1 : a ≠ 1) (hu : u ∈ U') : u⁻¹ * a ∉ Pc M V := by
  intro hmem
  have huM : u ∈ M := (hS.le_M_of_mem_sigmaSet hU').1 hu
  have huN : u ∈ Subgroup.normalizer (V : Set G) := hS.toRootHyp.toHyp.le_normalizer huM
  have hPP : ∀ x ∈ Pc M V, ∀ y ∈ Pc M V, ⁅x, y⁆ ∈ V := by
    intro x hx y hy
    rw [← hS.commutator_Pc_eq_V ⟨U, hU⟩]
    exact Subgroup.commutator_mem_commutator hx hy
  have hE'le : ⁅Pc M V, U'⁆ ≤ V := by
    intro y hy
    apply hS.mem_of_commutator_mem_of_cap hU hU' hcap ha ha1 hy
    have hyP : y ∈ Pc M V := hS.commutator_le_Pc hU' hy
    have huy : u * y = y * u :=
      hS.mul_comm_of_mem_sup_commutator hU' u (Subgroup.mem_sup_left hu) y
        (Subgroup.mem_sup_right hy)
    have hcomm : ⁅a, y⁆ = u * ⁅u⁻¹ * a, y⁆ * u⁻¹ := by
      rw [show a = u * (u⁻¹ * a) by group, commutatorElement_mul_left_eq_conj_mul,
        show ⁅u, y⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr huy]
      group
    rw [hcomm]
    exact (Subgroup.mem_normalizer_iff.mp huN ⁅u⁻¹ * a, y⁆).mp (hPP (u⁻¹ * a) hmem y hyP)
  have hcard : Nat.card ↥⁅Pc M V, U'⁆ ≤ Nat.card ↥V := Subgroup.card_le_of_le hE'le
  rw [hS.card_commutator_Pc hU'] at hcard
  have hlt : Nat.card V < Nat.card V ^ 3 := by
    simpa using Nat.pow_lt_pow_right (by have := hS.toRootHyp.four_le_card; omega)
      (by norm_num : 1 < 3)
  omega

theorem stmt56a (hS : Sec5Hyp M V) : Sec5.Stmt56a M V := by
  classical
  intro U hU U' hU' hcap
  have h := hS.toRootHyp
  have hcardU : Nat.card U = Nat.card V := by
    obtain ⟨g, hUg, -⟩ := hU
    rw [hUg, card_conjSubgroup]
  have hq : 4 ≤ Nat.card U := hcardU.symm ▸ h.four_le_card
  have hcap' := (hS.cap_symm hU hU').mp hcap
  have hR : U ⊔ U' ≤ Subgroup.normalizer (Pc M V : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact h.toHyp.le_normalizer_Pc ((hS.le_M_of_mem_sigmaSet hU).1 hx)
    · intro x hx
      exact h.toHyp.le_normalizer_Pc ((hS.le_M_of_mem_sigmaSet hU').1 hx)
  have hcomm : ∀ p ∈ U, ∀ p' ∈ U, p * p' = p' * p := fun p hp p' hp' =>
    hS.mul_comm_of_mem_sup_commutator hU p (Subgroup.mem_sup_left hp) p'
      (Subgroup.mem_sup_left hp')
  have hsq : ∀ p ∈ U, p * p = 1 := fun p hp =>
    hS.mul_self_eq_one_of_mem_sup_commutator hU p (Subgroup.mem_sup_left hp)
  have hne : ∀ p ∈ U, p ≠ 1 → ∀ u ∈ U', u⁻¹ * p ∉ Pc M V :=
    fun p hp hp1 u hu => hS.inv_mul_not_mem_Pc hU hU' hcap hp hp1 hu
  have hMouf : ∀ p ∈ U, p ≠ 1 → ∃ u ∈ U', u ≠ 1 ∧ ∃ r ∈ Pc M V,
      conjSubgroup p U' = conjSubgroup r (conjSubgroup u U) := by
    intro p hp hp1
    obtain ⟨u, hu, hu1, hpu⟩ :=
      hS.exists_pow_three_mem_Pc hS.stmt51a hS.stmt51e hS.stmt52a hU hU' hcap hp hp1
    obtain ⟨r, hr, hconj⟩ := hS.exists_conj_eq_conj_of_pow_three_mem hU hU' hp hu hu1 hpu
    exact ⟨u, hu, hu1, r, hr, hconj⟩
  have hMouf' : ∀ u ∈ U', u ≠ 1 → ∃ p ∈ U, p ≠ 1 ∧ ∃ r ∈ Pc M V,
      conjSubgroup u U = conjSubgroup r (conjSubgroup p U') := by
    intro u hu hu1
    obtain ⟨p, hp, hp1, hup⟩ :=
      hS.exists_pow_three_mem_Pc hS.stmt51a hS.stmt51e hS.stmt52a hU' hU hcap' hu hu1
    obtain ⟨r, hr, hconj⟩ := hS.exists_conj_eq_conj_of_pow_three_mem hU' hU hu hp hp1 hup
    exact ⟨p, hp, hp1, r, hr, hconj⟩
  obtain ⟨n, hn2, hncard, φ, hsurj, hker, hφU, hφU'⟩ :=
    CFSG.exists_hom_SL2_of_moufang_quot (P₁ := U) (P₂ := U') (R := Pc M V)
      hR hcomm hsq (hS.inf_Pc_eq_bot hU) (hS.inf_Pc_eq_bot hU') hne hMouf hMouf' hq
  have hn0 : n ≠ 0 := by omega
  have hcardF : Nat.card (GaloisField 2 n) = Nat.card V := by
    rw [GaloisField.card (p := 2) (n := n) hn0, ← hncard, hcardU]
  exact ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance, φ, hsurj, hker, hcardF,
    hφU, hφU'⟩

end Sec5Hyp

end CFSG.RankThree.GF2n.Tim81

end
