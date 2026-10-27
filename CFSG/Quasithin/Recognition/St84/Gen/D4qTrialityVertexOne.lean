module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qVertexOneDefs
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.LocalAnalysis.EvenBN.TrialityD4
open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {f : ℕ}

private theorem V_le_D (d : TrialityD4Data X (2 ^ f)) : d.V ≤ d.D :=
  d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))

private theorem mul_self_mem_V_of_mem_F (d : TrialityD4Data X (2 ^ f)) {x : X}
    (hx : x ∈ d.F) : x * x ∈ d.V := by
  obtain ⟨a, w, hw, rfl⟩ := d.mem_F_iff.1 hx
  rw [mul_mul_self_eq_commutatorElement (d.x₃_mul_self a), d.mul_self_eq_one_of_mem_W hw,
    mul_one]
  exact d.commutator_D_D (commutator_mem_commutator (d.F_le_D (d.x₃_mem_F a))
    (d.F_le_D (d.W_le_F hw)))

private theorem mul_self_mem_V_of_mem_D (d : TrialityD4Data X (2 ^ f)) {x : X}
    (hx : x ∈ d.D) : x * x ∈ d.V := by
  obtain ⟨a, g, hg, rfl⟩ := d.mem_D_iff.1 hx
  rw [mul_mul_self_eq_commutatorElement (d.x₂_mul_self a)]
  exact mul_mem (d.commutator_D_D (commutator_mem_commutator (d.x₂_mem_D a) (d.F_le_D hg)))
    (mul_self_mem_V_of_mem_F d hg)

theorem isSpecialPow_trialityD4Data_D (hf : 1 ≤ f) (d : TrialityD4Data X (2 ^ f)) :
    IsSpecialPow 2 (2 ^ f) 4 ↥d.D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVD : d.V ≤ d.D := V_le_D d
  have hDp : IsPGroup 2 ↥d.D :=
    IsPGroup.of_card (p := 2) (n := 9 * f) (by rw [d.card_D, ← pow_mul, Nat.mul_comm])
  have hcomm : _root_.commutator ↥d.D = d.V.subgroupOf d.D := by
    apply Subgroup.map_injective d.D.subtype_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hVD]
    exact d.commutator_D_eq
  have hcenterMap : (Subgroup.center ↥d.D).map d.D.subtype =
      d.D ⊓ Subgroup.centralizer (d.D : Set X) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun z hz => congrArg Subtype.val ((Subgroup.mem_center_iff.1 hy) ⟨z, hz⟩)⟩
    · rintro ⟨hxD, hx⟩
      exact ⟨⟨x, hxD⟩, Subgroup.mem_center_iff.2 fun z =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 hx z z.2), rfl⟩
  have hcenter : Subgroup.center ↥d.D = d.V.subgroupOf d.D := by
    apply Subgroup.map_injective d.D.subtype_injective
    rw [hcenterMap, d.D_inf_centralizer_D, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hVD]
  have hsq : ∀ x : ↥d.D, x ^ 2 ∈ d.V.subgroupOf d.D := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, pow_two]
    exact mul_self_mem_V_of_mem_D d x.2
  have hfrattini : frattini ↥d.D = Subgroup.center ↥d.D := by
    haveI : Fact (IsPGroup 2 ↥d.D) := ⟨hDp⟩
    rw [hcenter, ← hcomm,
      CFSG.frattini_eq_closure_commutator_union_powers (R := ↥d.D) (p := 2)]
    refine le_antisymm ((Subgroup.closure_le _).2 ?_)
      (fun x hx => Subgroup.subset_closure (Or.inl hx))
    rintro x (hx | ⟨y, rfl⟩)
    · exact hx
    · rw [hcomm]
      exact hsq y
  have hz2 : ∀ z ∈ Subgroup.center ↥d.D, z ^ 2 = 1 := by
    intro z hz
    rw [hcenter, Subgroup.mem_subgroupOf] at hz
    obtain ⟨a, ha⟩ := hz
    have hzX : (z : X) * (z : X) = 1 := by
      rw [← ha, d.x₆_mul_self a]
    have h2 : z * z = 1 := Subtype.ext (by simpa using hzX)
    rwa [pow_two]
  have hspecial : IsSpecialPGroup 2 ↥d.D :=
    ⟨hDp, Or.inr ⟨hcomm.trans hcenter.symm, hfrattini, hz2⟩⟩
  refine ⟨hspecial, ?_, ?_⟩
  · rw [d.card_D]
  · rw [hcenter, ← Subgroup.card_map_of_injective d.D.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hVD, d.card_V]

theorem sup_leviShort_sup_J₁_eq_normalizer (d : TrialityD4Data X (2 ^ f)) :
    d.D ⊔ (d.leviShort ⊔ d.J₁) = Subgroup.normalizer (d.V : Set X) :=
  d.yamada_three_eight_four.2.1.symm

theorem d4qVertexOneData_of_trialityD4Data (hf : 2 ≤ f)
    (d : TrialityD4Data X (2 ^ f)) : D4qVertexOneData d.D d.V d.leviShort d.J₁ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine
    { special := isSpecialPow_trialityD4Data_D (by omega) d
      centerOf_eq := d.D_inf_centralizer_D
      levi_le_normalizer := d.leviShort_le_normalizer_D
      torus_le_normalizer := d.J₁_le_normalizer_D
      disjoint := disjoint_iff_inf_le.mpr (le_of_eq d.yamada_three_eight_four.2.2.2.2)
      levi_inf_torus := d.yamada_three_eight_four.2.2.1
      levi_commute_torus := ?_
      levi_mulEquiv := ?_
      levi_centralizes := ?_
      irreducible := ?_
      card_torus := ?_
      torus_comm := ?_
      torus_faithful := ?_ }
  · intro k hk h hh
    exact Subgroup.mem_centralizer_iff.1 (d.yamada_three_eight_four.2.2.2.1 hh) k hk
  ·
    haveI : Fintype d.Γ := Fintype.ofFinite d.Γ
    haveI : Fintype (GaloisField 2 (3 * f)) := Fintype.ofFinite (GaloisField 2 (3 * f))
    have hcard : Fintype.card d.Γ = Fintype.card (GaloisField 2 (3 * f)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, d.card_Γ,
        GaloisField.card 2 (3 * f) (by omega), ← pow_mul, Nat.mul_comm]
    let e : d.Γ ≃+* GaloisField 2 (3 * f) := FiniteField.ringEquivOfCardEq hcard
    let ψ : Matrix.SpecialLinearGroup (Fin 2) d.Γ →*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (3 * f)) :=
      Matrix.SpecialLinearGroup.map e.toRingHom
    let ψ' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (3 * f)) →*
        Matrix.SpecialLinearGroup (Fin 2) d.Γ :=
      Matrix.SpecialLinearGroup.map e.symm.toRingHom
    have hψ : ψ.comp ψ' = MonoidHom.id _ := by
      ext x i j
      simp [ψ, ψ']
    have hψ' : ψ'.comp ψ = MonoidHom.id _ := by
      ext x i j
      simp [ψ, ψ']
    exact ⟨d.leviShortEquiv.trans (MonoidHom.toMulEquiv ψ ψ' hψ' hψ)⟩
  · intro k hk z hz
    have h := Subgroup.mem_centralizer_iff.1 (d.leviShort_le_centralizer_V hk) z hz
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  · intro W hZW hWQ hN
    exact d.leviShort_irreducible_D_mod_V hZW hWQ hN
  · exact d.yamada_three_five_one.2.2.2.1
  · intro a ha b hb
    obtain ⟨⟨l, m⟩, rfl, -⟩ := d.mem_J₁.1 ha
    obtain ⟨⟨l', m'⟩, rfl, -⟩ := d.mem_J₁.1 hb
    rw [← map_mul, ← map_mul, mul_comm]
  · intro h hh htriv
    obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hh
    dsimp only at hm
    subst hm
    have hx : d.torus (l, 1) * d.x₂ 1 * (d.torus (l, 1))⁻¹ * (d.x₂ 1)⁻¹ ∈ d.V :=
      htriv (d.x₂ 1) (d.x₂_mem_D 1)
    rw [d.torus_x₂, d.x₂_inv] at hx
    simp only [mul_one, ← d.x₂_add] at hx
    have hl1 : ((l, 1).1 : d.Γ₀) + 1 = 0 := d.x₂_mem_Y_iff.1 (d.V_le_Y hx)
    have hl : l = 1 := by
      have hl1' : (1 : d.Γ₀) + (l : d.Γ₀) = 0 := by rw [add_comm]; exact hl1
      have hneg : (l : d.Γ₀) = -1 := eq_neg_of_add_eq_zero_right hl1'
      have hsq : ((l : d.Γ₀)) * ((l : d.Γ₀)) = 1 := by rw [hneg]; ring
      refine d.units₀_eq_one_of_sq (Units.ext ?_)
      simpa [pow_two] using hsq
    rw [hl]
    exact map_one d.torus

end CFSG.Quasithin.F112R.St84

end
