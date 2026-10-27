module

public import CFSG.Quasithin.Vol2.Ch3E213MOS1
public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.Quasithin.Background.E2TwoProofFam

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.GH74.GLS.IVK

theorem card_le_two_of_dihedral {X : Type*} [Group X] {T₀ V₀ : Subgroup X} {k : ℕ}
    (φ : ↥T₀ ≃* DihedralGroup k) (hk : 4 < k) (hVT : V₀ ≤ T₀)
    (hVn : T₀ ≤ Subgroup.normalizer (V₀ : Set X)) (hsq : ∀ v ∈ V₀, v * v = 1) :
    Nat.card V₀ ≤ 2 := by
  set V' : Subgroup (DihedralGroup k) := (V₀.subgroupOf T₀).map φ.toMonoidHom with hV'
  have hcard : Nat.card V' = Nat.card V₀ := by
    rw [hV', Nat.card_congr (Subgroup.equivMapOfInjective _ _ φ.injective).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv]
  rw [← hcard]
  refine Dih.card_le_two_of_normal (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    set g : ↥T₀ := φ.symm (DihedralGroup.r 1) with hg
    have hgn := Subgroup.mem_normalizer_iff.mp (hVn g.2) (v : X)
    refine ⟨g * v * g⁻¹, ?_, ?_⟩
    · show g * v * g⁻¹ ∈ V₀.subgroupOf T₀
      rw [Subgroup.mem_subgroupOf]
      exact hgn.mp (Subgroup.mem_subgroupOf.mp hv)
    · rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply]
  · rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul]
    have : v * v = 1 := Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.mp hv))
    rw [this, map_one]

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] {e : K ≃* L2 F}

omit [Finite K] in
theorem le_normalizer_P (N : L2Notation e) :
    (N.T : Subgroup (MulAut K)) ≤ Subgroup.normalizer (N.P : Set (MulAut K)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hy := Subgroup.mem_normalizer_iff.mp
    ((Subgroup.normalizer_eq_top_iff.mpr (innAut_normal (K := K))).symm ▸ Subgroup.mem_top x) y
  constructor
  · rintro ⟨hyT, hyI⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hyT) (Subgroup.inv_mem _ hx), hy.mp hyI⟩
  · rintro ⟨hyT, hyI⟩
    refine ⟨?_, hy.mpr hyI⟩
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hyT) hx
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem eq_or_eq (h12d : IVK_1_2d) (hF : L2Field F) (N : L2Notation e) {T₀ : Subgroup (MulAut K)}
    (hPT : N.P ≤ T₀) (hTPt : T₀ ≤ N.Pt) : T₀ = N.P ∨ T₀ = N.Pt := by
  obtain ⟨-, -, hPt, -⟩ := h12d F hF K e N
  by_cases ht : N.t ∈ T₀
  · right
    refine le_antisymm hTPt ?_
    rw [← hPt]
    exact sup_le hPT ((Subgroup.zpowers_le).mpr ht)
  · left
    refine le_antisymm ?_ hPT
    intro y hy
    have hy' : y ∈ N.P ⊔ Subgroup.zpowers N.t := hPt.symm ▸ hTPt hy
    have htn : Subgroup.zpowers N.t ≤ Subgroup.normalizer (N.P : Set (MulAut K)) :=
      (Subgroup.zpowers_le).mpr (le_normalizer_P N N.t_mem)
    obtain ⟨a, ha, b, hb, rfl⟩ := E2P.exists_mul_of_mem_sup_of_le_normalizer' htn hy'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have h2 : N.t ^ n = 1 ∨ N.t ^ n = N.t := by
      rw [← zpow_mod_orderOf, N.t_order, Nat.cast_ofNat]
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left
        rw [h, zpow_zero]
      · right
        rw [h, zpow_one]
    rcases h2 with h | h
    · rw [h, mul_one]
      exact ha
    · exfalso
      apply ht
      have : N.t = a⁻¹ * (a * N.t ^ n) := by rw [h]; group
      rw [this]
      exact T₀.mul_mem (T₀.inv_mem (hPT ha)) hy

theorem card_le_two_of_le_Pt (h12c : IVK_1_2c) (h12d : IVK_1_2d) (hF : L2Field F)
    (N : L2Notation e) {T₀ V₀ : Subgroup (MulAut K)} (hPT : N.P ≤ T₀) (hTPt : T₀ ≤ N.Pt)
    (hcard : 8 < Nat.card T₀) (hVT : V₀ ≤ T₀)
    (hVn : T₀ ≤ Subgroup.normalizer (V₀ : Set (MulAut K))) (hsq : ∀ v ∈ V₀, v * v = 1) :
    Nat.card V₀ ≤ 2 := by
  have hdih : ∃ n : ℕ, IsDihedralTwoGroup ↥T₀ n := by
    rcases eq_or_eq h12d hF N hPT hTPt with h | h
    · rw [h]
      exact h12c F hF K e N
    · rw [h]
      exact (h12d F hF K e N).2.2.2
  obtain ⟨n, -, k, hk, -, ⟨φ⟩⟩ := hdih
  have hcardT : Nat.card T₀ = 2 * k := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  exact card_le_two_of_dihedral φ (by omega) hVT hVn hsq

end CFSG.Quasithin.Ch3E213M.OS
