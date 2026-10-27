module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Cover
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Cent

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem inv_conj_eq_pow_of_conj {G : Type} [Group G] {x y h : G} (hx3 : x ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (hcon : h * y * h⁻¹ = x ^ e) : h⁻¹ * x * h = y ^ e := by
  have hy : y = h⁻¹ * x ^ e * h := by
    rw [← hcon]; group
  rcases he with rfl | rfl
  · rw [hy]; simp
  · have hsq : (h⁻¹ * x ^ 2 * h) ^ 2 = h⁻¹ * (x ^ 2) ^ 2 * h := by
      simp only [sq, mul_assoc, mul_inv_cancel_left]
    rw [hy, hsq, sq_sq_eq_of_pow_three hx3]

section Fusion

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271.Co2Cent CFSG.HardMathSupport.Dickson.I271.U42Presentation
  CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

theorem co2_vec3_zero : vec 3 0 = 0 := by decide

theorem co2_vec5_ne : vec 5 0 ≠ 0 := by decide

theorem co2_vec1_one : vec 1 1 = 0 := by decide

theorem co2_vec4_ne : vec 4 1 ≠ 0 := by decide

theorem co2_phi_mem_Dg (a : Fin 4 → ZMod 3) :
    φ (Multiplicative.ofAdd a) ∈ Dg :=
  MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem co2_phi_pow_notMem_zpowers {a b : Fin 4 → ZMod 3}
    {i : Fin 4} (hb : b i = 0) (ha : a i ≠ 0) {e : ℕ} (he : e = 1 ∨ e = 2) :
    φ (Multiplicative.ofAdd a) ^ e ∉ Subgroup.zpowers (φ (Multiplicative.ofAdd b)) := by
  rintro hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hn' : φ (Multiplicative.ofAdd b ^ n) = φ (Multiplicative.ofAdd a ^ e) := by
    rw [map_zpow, map_pow]; exact hn
  have h2 := congrArg Multiplicative.toAdd (φ_injective hn')
  rw [toAdd_zpow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd] at h2
  have h3 := congrFun h2 i
  simp only [Pi.smul_apply, hb, smul_zero, nsmul_eq_mul] at h3
  rcases he with rfl | rfl
  · rw [Nat.cast_one, one_mul] at h3
    exact ha h3.symm
  · have key : ∀ x : ZMod 3, x ≠ 0 → ((2 : ℕ) : ZMod 3) * x ≠ 0 := by decide
    exact key (a i) ha h3.symm

theorem listRow_co2P :
    ListRow ↥co2P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨rA, hrA⟩ : ∃ r : ↥co2P, (r : Equiv.Perm (Fin 2300)) = co2XA :=
    ⟨⟨co2XA, co2CaseA_spec.2.2.1⟩, rfl⟩
  obtain ⟨rB, hrB⟩ : ∃ r : ↥co2P, (r : Equiv.Perm (Fin 2300)) = co2XB :=
    ⟨⟨co2XB, co2CaseB_spec.2.2.1⟩, rfl⟩
  have hA3 : (rA : Equiv.Perm (Fin 2300)) ^ 3 = 1 := by rw [hrA]; exact co2CaseA_spec.1
  have hA1 : (rA : Equiv.Perm (Fin 2300)) ≠ 1 := by rw [hrA]; exact co2CaseA_spec.2.1
  have hB3 : (rB : Equiv.Perm (Fin 2300)) ^ 3 = 1 := by rw [hrB]; exact co2CaseB_spec.1
  have hB1 : (rB : Equiv.Perm (Fin 2300)) ≠ 1 := by rw [hrB]; exact co2CaseB_spec.2.1
  have hR : ∀ c ∈ ({rA, rB} : Set ↥co2P), orderOf c = 3 := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · rw [hc, ← Subgroup.orderOf_coe]; exact orderOf_eq_prime hA3 hA1
    · rw [hc, ← Subgroup.orderOf_coe]; exact orderOf_eq_prime hB3 hB1
  have hcov : ∀ s : ↥co2P, orderOf s = 3 → ∃ k c : ↥co2P, c ∈ ({rA, rB} : Set ↥co2P) ∧
      ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s := by
    intro s hs
    have hs' : orderOf (s : Equiv.Perm (Fin 2300)) = 3 := by
      rw [Subgroup.orderOf_coe]; exact hs
    obtain ⟨k, hk, c, hc, e, he, hfuse⟩ := co2_exists_conj_classes s.2 hs'
    refine ⟨⟨k, hk⟩, ?_⟩
    rcases hc with hc | hc
    · refine ⟨rA, by simp, e, he, Subtype.ext ?_⟩
      simpa [hrA, hc] using hfuse
    · refine ⟨rB, by simp, e, he, Subtype.ext ?_⟩
      simpa [hrB, hc] using hfuse
  have hw : ∀ c ∈ ({rA, rB} : Set ↥co2P), ∃ g : ↥co2P,
      (g * c * g⁻¹) * c = c * (g * c * g⁻¹) ∧ g * c * g⁻¹ ∉ Subgroup.zpowers c := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · rw [hc]
      obtain ⟨h, hh, e, he, hcon⟩ := co2_fuse_d5
      have hconj : h⁻¹ * co2XA * h = φ (Multiplicative.ofAdd (vec 5)) ^ e :=
        inv_conj_eq_pow_of_conj co2CaseA_spec.1 he hcon
      obtain ⟨g, hg⟩ : ∃ g : ↥co2P, (g : Equiv.Perm (Fin 2300)) = h⁻¹ :=
        ⟨⟨h⁻¹, co2P.inv_mem hh⟩, rfl⟩
      have hy : ((g * rA * g⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300)) =
          φ (Multiplicative.ofAdd (vec 5)) ^ e := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg, hrA, inv_inv]
        exact hconj
      have hY : φ (Multiplicative.ofAdd (vec 5)) ^ e ∈ Dg :=
        Subgroup.pow_mem _ (co2_phi_mem_Dg _) e
      have hX : co2XA ∈ Dg := by rw [co2XA_eq]; exact co2_phi_mem_Dg _
      refine ⟨g, ?_, ?_⟩
      · apply Subtype.ext
        show ((g * rA * g⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300)) * (rA : Equiv.Perm (Fin 2300)) =
          (rA : Equiv.Perm (Fin 2300)) * ((g * rA * g⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300))
        rw [hy, hrA]
        exact Dg_comm _ hY _ hX
      · intro hmem
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have h1 := congrArg Subtype.val hn
        rw [Subgroup.coe_zpow, hy, hrA, co2XA_eq] at h1
        exact co2_phi_pow_notMem_zpowers co2_vec3_zero co2_vec5_ne he
          (Subgroup.mem_zpowers_iff.mpr ⟨n, h1⟩)
    · rw [hc]
      obtain ⟨h, hh, e, he, hcon⟩ := co2_fuse_d4
      have hconj : h⁻¹ * co2XB * h = φ (Multiplicative.ofAdd (vec 4)) ^ e :=
        inv_conj_eq_pow_of_conj co2CaseB_spec.1 he hcon
      obtain ⟨g, hg⟩ : ∃ g : ↥co2P, (g : Equiv.Perm (Fin 2300)) = h⁻¹ :=
        ⟨⟨h⁻¹, co2P.inv_mem hh⟩, rfl⟩
      have hy : ((g * rB * g⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300)) =
          φ (Multiplicative.ofAdd (vec 4)) ^ e := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg, hrB, inv_inv]
        exact hconj
      have hY : φ (Multiplicative.ofAdd (vec 4)) ^ e ∈ Dg :=
        Subgroup.pow_mem _ (co2_phi_mem_Dg _) e
      have hX : co2XB ∈ Dg := by rw [co2XB_eq]; exact co2_phi_mem_Dg _
      refine ⟨g, ?_, ?_⟩
      · apply Subtype.ext
        show ((g * rB * g⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300)) * (rB : Equiv.Perm (Fin 2300)) =
          (rB : Equiv.Perm (Fin 2300)) * ((g * rB * g⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300))
        rw [hy, hrB]
        exact Dg_comm _ hY _ hX
      · intro hmem
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have h1 := congrArg Subtype.val hn
        rw [Subgroup.coe_zpow, hy, hrB, co2XB_eq] at h1
        exact co2_phi_pow_notMem_zpowers co2_vec1_one co2_vec4_ne he
          (Subgroup.mem_zpowers_iff.mpr ⟨n, h1⟩)
  exact listRow_of_cover ({rA, rB} : Set ↥co2P) hR hcov hw

end Fusion

theorem listRow_co2 :
    ListRow NativeSporadic.Co2 := by
  haveI : Finite NativeSporadic.Co2 :=
    Finite.of_equiv _ CFSG.Sporadic.Co2Cert.co2PermEquiv.symm.toEquiv
  exact ListRow.of_mulEquiv CFSG.Sporadic.Co2Cert.co2PermEquiv.symm listRow_co2P

theorem outerRow_co2 :
    OuterRow NativeSporadic.Co2 := by
  haveI : Finite NativeSporadic.Co2 :=
    Finite.of_equiv _ CFSG.Sporadic.Co2Cert.co2PermEquiv.symm.toEquiv
  refine outerRow_of_not_three_dvd_outer ?_
  have h1 : Nat.card (Outer NativeSporadic.Co2) = 1 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_Co2
  rw [h1]
  norm_num

theorem row_carrier_co2 :
    RowOf (NativeSporadic.Carrier .Co2) := by
  haveI : Finite NativeSporadic.Co2 :=
    Finite.of_equiv _ CFSG.Sporadic.Co2Cert.co2PermEquiv.symm.toEquiv
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.Co2) e.symm ⟨listRow_co2, outerRow_co2⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
