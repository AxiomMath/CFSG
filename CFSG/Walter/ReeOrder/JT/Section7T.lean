module

public import CFSG.Walter.ReeOrder.JT.Section7Q

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_fixed_of_sq_eq_one {α : Type*} [Finite α] (σ : Equiv.Perm α) (hσ : σ ^ 2 = 1)
    (hα : Odd (Nat.card α)) : ∃ a, σ a = a := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have h2 := Equiv.Perm.two_dvd_card_support hσ
  by_contra hfix
  simp only [not_exists] at hfix
  have hsupp : σ.support = Finset.univ := by
    ext a
    simp [Equiv.Perm.mem_support, hfix a]
  rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  exact (Nat.not_even_iff_odd.mpr hα) (even_iff_two_dvd.mpr h2)

theorem exists_mem_centralizer_coset {P₂ : Subgroup X} (hP₂ : Odd (Nat.card P₂)) {u : X}
    (hu : u * u = 1) (huP : u ∈ Subgroup.normalizer (P₂ : Set X)) {x : X}
    (hx : x⁻¹ * u * x * u⁻¹ ∈ P₂) :
    ∃ n ∈ P₂, (x * n⁻¹) * u = u * (x * n⁻¹) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hmem : ∀ n ∈ P₂, x⁻¹ * u * x * n * u⁻¹ ∈ P₂ := by
    intro n hn
    have h1 := (Subgroup.mem_normalizer_iff.mp huP n).mp hn
    have : x⁻¹ * u * x * n * u⁻¹ = (x⁻¹ * u * x * u⁻¹) * (u * n * u⁻¹) := by group
    rw [this]
    exact P₂.mul_mem hx h1
  let σ : Equiv.Perm P₂ :=
    { toFun := fun n => ⟨x⁻¹ * u * x * n * u⁻¹, hmem n n.2⟩
      invFun := fun n => ⟨x⁻¹ * u * x * n * u⁻¹, hmem n n.2⟩
      left_inv := fun n => Subtype.ext (by
        simp only
        rw [huinv]
        calc x⁻¹ * u * x * (x⁻¹ * u * x * (n : X) * u) * u
            = x⁻¹ * (u * u) * x * n * (u * u) := by group
          _ = n := by rw [hu]; group)
      right_inv := fun n => Subtype.ext (by
        simp only
        rw [huinv]
        calc x⁻¹ * u * x * (x⁻¹ * u * x * (n : X) * u) * u
            = x⁻¹ * (u * u) * x * n * (u * u) := by group
          _ = n := by rw [hu]; group) }
  have hσ2 : σ ^ 2 = 1 := by
    ext n
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq, Equiv.Perm.coe_one]
    change x⁻¹ * u * x * (x⁻¹ * u * x * (n : X) * u⁻¹) * u⁻¹ = n
    rw [huinv]
    calc x⁻¹ * u * x * (x⁻¹ * u * x * (n : X) * u) * u
        = x⁻¹ * (u * u) * x * n * (u * u) := by group
      _ = n := by rw [hu]; group
  obtain ⟨⟨n, hn⟩, hfix⟩ := exists_fixed_of_sq_eq_one σ hσ2 hP₂
  have hfix' : x⁻¹ * u * x * n * u⁻¹ = n := congrArg Subtype.val hfix
  refine ⟨n⁻¹, P₂.inv_mem hn, ?_⟩
  rw [inv_inv]
  calc x * n * u = x * (x⁻¹ * u * x * n * u⁻¹) * u := by rw [hfix']
    _ = u * (x * n) := by group

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem exists_R (c : TorusConf h) :
    ∃ R : Subgroup G, R ≤ h.F ∧ Nat.card R = h.q ∧
      c.C ≤ Subgroup.normalizer (R : Set G) := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have hf := h.f_ne_zero
  set K := GaloisField h.p h.f
  have hKcard : Nat.card K = h.p ^ h.f := GaloisField.card h.p h.f hf
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact (Fact.out : h.p.Prime).odd_of_ne_two hp |>.pow
  obtain ⟨D, hDc, hDcard, hDN, hEcard⟩ := exists_borel_psl2 hKodd
  let ι : PSL(2, K) →* G := h.F.subtype.comp h.iso.symm.toMonoidHom
  have hι : Function.Injective ι := h.F.subtype_injective.comp h.iso.symm.injective
  have hιF : ∀ y, ι y ∈ h.F := fun y => (h.iso.symm y).2
  set D' := D.map ι
  set U' := (pslE K).map ι
  have hD'F : D' ≤ h.F := by rintro _ ⟨y, -, rfl⟩; exact hιF y
  have hU'F : U' ≤ h.F := by rintro _ ⟨y, -, rfl⟩; exact hιF y
  have hD'c : IsCyclic D' := isCyclic_of_surjective
    (D.equivMapOfInjective ι hι).toMonoidHom (D.equivMapOfInjective ι hι).surjective
  have hD'card : 2 * Nat.card D' + 1 = h.q := by
    rw [Subgroup.card_map_of_injective hι, hDcard, hKcard, JTHyp.q_eq]
  have hD'N : D' ≤ Subgroup.normalizer (U' : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    exact Subgroup.le_normalizer_map ι ⟨d, hDN hd, rfl⟩
  obtain ⟨g, hgF, hg⟩ := h.exists_conj_of_isCyclic hp3 hD'F c.torus.le hD'c c.torus.cyclic
    hD'card c.card_C
  refine ⟨U'.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact h.F.mul_mem (h.F.mul_mem hgF (hU'F hy)) (h.F.inv_mem hgF)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective hι, hEcard, hKcard, JTHyp.q_eq]
  · rw [hg]
    rintro _ ⟨d, hd, rfl⟩
    exact conj_mem_normalizer_map (hD'N hd) g

theorem le_of_le_centralizer_t {R : Subgroup G} (hRF : R ≤ h.F) (hRq : Nat.card R = h.q)
    {H : Subgroup G} (hH : IsPGroup 3 H) (hRH : R ≤ H) {S : Subgroup G} (hS : IsPGroup 3 S)
    (hSt : S ≤ Subgroup.centralizer ({h.t} : Set G))
    (hSH : S ≤ Subgroup.normalizer (H : Set G)) : S ≤ R := by
  have hu := h.unipotentFacts hp3
  have hp' : h.p = 3 := hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq3 : ∀ {T : Subgroup G}, IsPGroup 3 T → T ≤ h.F → Nat.card T ∣ h.q := by
    intro T hT hTF
    have := hu.card_dvd T hTF (hp3 ▸ hT)
    rwa [← JTHyp.q_eq] at this
  have hSodd : Odd (Nat.card S) := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn]
    exact Nat.odd_iff.mpr (by
      rw [Nat.pow_mod]; norm_num)
  have hSF : S ≤ h.F := h.le_F_of_odd hSt hSodd
  have hHF : H ⊓ h.F = R := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hRH hRF) ?_).symm
    rw [hRq]
    exact Nat.le_of_dvd (by have := h.five_lt; rw [← JTHyp.q_eq] at this; omega)
      (hq3 (hH.to_le inf_le_left) inf_le_right)
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    rw [← hHF]
    exact Walter.Transitivity.le_normalizer_inf (A := S) hSH
      (fun x hx => Subgroup.le_normalizer (hSF hx)) hs
  have hSRp : IsPGroup 3 (S ⊔ R : Subgroup G) :=
    hS.to_sup_of_normal_right' (hH.to_le hRH) hSR
  have hSRF : S ⊔ R ≤ h.F := sup_le hSF hRF
  have hle : Nat.card (S ⊔ R : Subgroup G) ≤ Nat.card R := by
    rw [hRq]
    exact Nat.le_of_dvd (by have := h.five_lt; rw [← JTHyp.q_eq] at this; omega)
      (hq3 hSRp hSRF)
  have := Subgroup.eq_of_le_of_card_ge (le_sup_right : R ≤ S ⊔ R) hle
  rw [this]
  exact le_sup_left

end JTHyp

end CFSG.Walter.JT
