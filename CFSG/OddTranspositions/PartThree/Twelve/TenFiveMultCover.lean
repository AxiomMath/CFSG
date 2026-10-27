module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic

public section

namespace CFSG.OddTranspositions.PartThree

open scoped commutatorElement

theorem sq_eq_one_of_card_eq_two {G : Type*} [Group G] (hcard : Nat.card G = 2) (x : G) :
    x * x = 1 := by
  have h := pow_card_eq_one' (x := x)
  rw [hcard] at h
  simpa [pow_two] using h

theorem commutatorElement_mul_mul_of_mem_center {G : Type*} [Group G] {a b c d : G}
    (hb : b ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ := by
  have hbc : ⁅b, c⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hb c).symm
  have hbd : ⁅b, d⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hb d).symm
  have had : ⁅a, d⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hd a)
  calc ⁅a * b, c * d⁆
      = a * ⁅b, c * d⁆ * a⁻¹ * ⁅a, c * d⁆ :=
        commutatorElement_mul_left_eq_conj_mul a b (c * d)
    _ = a * (⁅b, c⁆ * c * ⁅b, d⁆ * c⁻¹) * a⁻¹ * (⁅a, c⁆ * c * ⁅a, d⁆ * c⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj b c d,
            commutatorElement_mul_right_eq_mul_conj a c d]
    _ = ⁅a, c⁆ := by rw [hbc, hbd, had]; group

theorem modelInvolutionCover_abstract
    {U X Ω Γ : Type} [Group U] [Finite U] [Group X] [Group Ω] [Group Γ] [Finite Γ]
    (σ : U →* X) (ω : U →* Ω) (mk : Ω →* X) (z₀ : U)
    (hUperf : commutator U = ⊤)
    (hσ : Function.Surjective σ) (hω : Function.Surjective ω)
    (hσmk : ∀ u, σ u = mk (ω u))
    (hσker_center : σ.ker ≤ Subgroup.center U)
    (hsect : ∀ (E : Type) [Group E] [Finite E] (p : E →* U), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : U →* E, ∀ g, p (s g) = g)
    (hcardZ : Nat.card σ.ker ≤ 4)
    (hωker : ω.ker = Subgroup.zpowers z₀)
    (hz₀ne : z₀ ≠ 1) (hz₀sq : z₀ * z₀ = 1)
    (ρ : Γ →* X) (hρ : Function.Surjective ρ)
    (hΓperf : commutator Γ = ⊤)
    (hρker_center : ρ.ker ≤ Subgroup.center Γ)
    (hcardρ : Nat.card ρ.ker = 2)
    (g₀ : Ω) (x : Γ) (hx : ρ x = mk g₀) (hxsq : x * x = 1)
    (hcliff : ∃ u₀ : U, ω u₀ = g₀ ∧ u₀ * u₀ = z₀) :
    ∃ ψ : Γ ≃* Ω, ∀ g, ρ g = mk (ψ g) := by
  classical
  let E : Subgroup (U × Γ) :=
    { carrier := {p | σ p.1 = ρ p.2}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul]
        rw [ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv]
        rw [ha] }
  let proj : E →* U := (MonoidHom.fst U Γ).comp E.subtype
  have hproj_surj : Function.Surjective proj := by
    intro u
    obtain ⟨γ, hγ⟩ := hρ (σ u)
    exact ⟨⟨(u, γ), hγ.symm⟩, rfl⟩
  have hproj_ker : proj.ker ≤ Subgroup.center E := by
    intro e he
    have he1 : (e : U × Γ).1 = 1 := by
      show proj e = 1
      exact MonoidHom.mem_ker.mp he
    have he2 : (e : U × Γ).2 ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      have h : σ (e : U × Γ).1 = ρ (e : U × Γ).2 := e.2
      rw [he1, map_one] at h
      exact h.symm
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · simp [he1]
    · exact Subgroup.mem_center_iff.mp (hρker_center he2) (g : U × Γ).2
  obtain ⟨s, hs⟩ := hsect E proj hproj_surj hproj_ker
  let τ : U →* Γ := (MonoidHom.snd U Γ).comp (E.subtype.comp s)
  have hρτ : ∀ u, ρ (τ u) = σ u := by
    intro u
    have h1 : (s u : U × Γ).1 = u := hs u
    have h2 : σ (s u : U × Γ).1 = ρ (s u : U × Γ).2 := (s u).2
    show ρ ((s u : U × Γ).2) = σ u
    rw [← h2, h1]

  have hτ_surj : Function.Surjective τ := by
    have hsup : τ.range ⊔ ρ.ker = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_sup_of_normal_right]
      obtain ⟨u, hu⟩ := hσ (ρ g)
      refine ⟨τ u, ⟨u, rfl⟩, (τ u)⁻¹ * g, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hρτ u, hu]
        simp
      · group
    have hcomm_le : commutator Γ ≤ τ.range := by
      change ⁅(⊤ : Subgroup Γ), ⊤⁆ ≤ τ.range
      rw [← hsup, Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_sup_of_normal_right] at ha hb
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ha
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hb
      rw [commutatorElement_mul_mul_of_mem_center (hρker_center ha₂) (hρker_center hb₂)]
      rw [commutatorElement_def]
      exact τ.range.mul_mem (τ.range.mul_mem (τ.range.mul_mem ha₁ hb₁)
        (τ.range.inv_mem ha₁)) (τ.range.inv_mem hb₁)
    rw [← MonoidHom.range_eq_top]
    exact le_antisymm le_top (by
      calc ⊤ = commutator Γ := hΓperf.symm
        _ ≤ τ.range := hcomm_le)

  have hτker_le_Z : τ.ker ≤ σ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [← hρτ u, hu, map_one]
  have hτZ : (σ.ker).map τ = ρ.ker := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      rw [MonoidHom.mem_ker, hρτ u]
      exact MonoidHom.mem_ker.mp hu
    · intro y hy
      rw [Subgroup.mem_map]
      obtain ⟨u, rfl⟩ := hτ_surj y
      refine ⟨u, ?_, rfl⟩
      rw [MonoidHom.mem_ker, ← hρτ u]
      exact hy

  have hz₀_mem : z₀ ∈ τ.ker := by
    obtain ⟨u₀, hωu₀, hu₀sq⟩ := hcliff
    have hσu₀ : σ u₀ = ρ x := by rw [hσmk u₀, hωu₀, hx]
    have hxτ : x⁻¹ * τ u₀ ∈ (σ.ker).map τ := by
      rw [hτZ, MonoidHom.mem_ker, map_mul, map_inv, hρτ u₀, hσu₀]
      simp
    rw [Subgroup.mem_map] at hxτ
    obtain ⟨d, hdZ, hd⟩ := hxτ
    have hdker : τ d ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, hρτ d]
      exact MonoidHom.mem_ker.mp hdZ
    have hx_eq : x = τ u₀ * (τ d)⁻¹ := by rw [hd]; group
    have hτu₀_eq : τ u₀ = x * τ d := by rw [hx_eq]; group
    have hcomm : Commute x (τ d) := Subgroup.mem_center_iff.mp (hρker_center hdker) x
    have hτd_sq : τ d * τ d = 1 := by
      have h := sq_eq_one_of_card_eq_two hcardρ (⟨τ d, hdker⟩ : ρ.ker)
      simpa using congrArg Subtype.val h
    have hsqx : (x * τ d) * (x * τ d) = (x * x) * (τ d * τ d) := by
      calc (x * τ d) * (x * τ d) = x * (τ d * x) * τ d := by group
        _ = x * (x * τ d) * τ d := by rw [hcomm.eq]
        _ = (x * x) * (τ d * τ d) := by group
    have hτu₀_sq : τ u₀ * τ u₀ = 1 := by
      rw [hτu₀_eq, hsqx, hxsq, hτd_sq, mul_one]
    rw [MonoidHom.mem_ker]
    rw [← hu₀sq, map_mul]
    exact hτu₀_sq

  have hcard_τker_le : Nat.card τ.ker ≤ 2 := by
    let fZ : σ.ker →* ρ.ker := MonoidHom.codRestrict (τ.comp σ.ker.subtype) ρ.ker (fun z => by
      show ρ (τ (z : U)) = 1
      rw [hρτ (z : U)]
      exact MonoidHom.mem_ker.mp z.2)
    have hfZ_surj : Function.Surjective fZ := by
      intro y
      have hy : (y : Γ) ∈ (σ.ker).map τ := by rw [hτZ]; exact y.2
      rw [Subgroup.mem_map] at hy
      obtain ⟨u, hu, huy⟩ := hy
      exact ⟨⟨u, hu⟩, Subtype.ext huy⟩
    have h := Subgroup.card_ker_mul_card_of_surjective (f := fZ) hfZ_surj
    rw [hcardρ] at h
    have hle : Nat.card fZ.ker ≤ 2 := by
      have : Nat.card fZ.ker * 2 ≤ 4 := by rw [h]; exact hcardZ
      exact Nat.le_of_mul_le_mul_right this (by norm_num)
    have hfZker : fZ.ker = τ.ker.subgroupOf σ.ker := by
      ext z
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact Subtype.ext_iff
    have hcard_eq : Nat.card fZ.ker = Nat.card τ.ker := by
      rw [hfZker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hτker_le_Z).toEquiv
    rwa [hcard_eq] at hle
  have hcard_zp : Nat.card (Subgroup.zpowers z₀) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hz₀sq) hz₀ne
  have heq : Subgroup.zpowers z₀ = τ.ker :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz₀_mem)
      (by rw [hcard_zp]; exact hcard_τker_le)
  have hker_eq : τ.ker = ω.ker := by rw [hωker]; exact heq.symm

  let e1 : U ⧸ τ.ker ≃* Γ := QuotientGroup.quotientKerEquivOfSurjective τ hτ_surj
  let e2 : U ⧸ τ.ker ≃* U ⧸ ω.ker := QuotientGroup.quotientMulEquivOfEq hker_eq
  let e3 : U ⧸ ω.ker ≃* Ω := QuotientGroup.quotientKerEquivOfSurjective ω hω
  refine ⟨e1.symm.trans (e2.trans e3), fun g => ?_⟩
  obtain ⟨u, rfl⟩ := hτ_surj g
  have h1 : e1 (QuotientGroup.mk u) = τ u := by
    show (QuotientGroup.kerLift τ) (QuotientGroup.mk u) = τ u
    exact QuotientGroup.kerLift_mk (φ := τ) u
  have h2 : e1.symm (τ u) = QuotientGroup.mk u := by rw [← h1]; simp
  have h3 : e2 (QuotientGroup.mk u) = QuotientGroup.mk u :=
    QuotientGroup.quotientMulEquivOfEq_mk hker_eq u
  have h4 : e3 (QuotientGroup.mk u) = ω u := by
    show (QuotientGroup.kerLift ω) (QuotientGroup.mk u) = ω u
    exact QuotientGroup.kerLift_mk (φ := ω) u
  have hψ : (e1.symm.trans (e2.trans e3)) (τ u) = ω u := by
    change (e2.trans e3) (e1.symm (τ u)) = ω u
    rw [h2]
    change e3 (e2 (QuotientGroup.mk u)) = ω u
    rw [h3]
    exact h4
  rw [hψ, ← hσmk u]
  exact hρτ u

end CFSG.OddTranspositions.PartThree
