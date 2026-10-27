module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath
public import CFSG.Quasithin.Recognition.Kleidman.F204.NatA

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Edge

variable (F : Frame L1 L2 S D X)
include F

theorem edge_gen {α β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) {ρ : G} (hρα : ρ ∈ stab α) (hρβ : ρ ∈ stab β) (hρ3 : ρ ^ 3 = 1)
    (hρ1 : ρ ≠ 1) {N : Subgroup G} (hNα : Qv α ≤ N) (hNβ : Qv β ≤ N) (hNρ : ρ ∈ N) :
    stab α ⊓ stab β ≤ N := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hA := Amal.of_frame F
  obtain ⟨hsylβ, hsylα, hnorm⟩ := sylow_sup_Qv F hα hβ
  obtain ⟨g, hg1, hg0⟩ := exists_edge_conj_true hα hβ
  have hQ0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  have hsup : Qv α ⊔ Qv β = conjSub (g : G) S := by
    rw [← hg1, ← hg0, Qv_smul, Qv_smul, hQ0, hQ1, ← conjSub_sup,
      show Q2 L1 L2 S ⊔ Q1 L1 L2 S = S from by rw [sup_comm]; exact Q1_sup_Q2 F]
  have hsδ : stab β = conjSub (g : G) (P1 L1 L2 S) := by rw [← hg0, stab_smul, stab_γ₀ h₁]
  have hsx : stab α = conjSub (g : G) (P2 L1 L2 S) := by rw [← hg1, stab_smul, stab_γ₁ h₂]
  have hB : stab α ⊓ stab β = conjSub (g : G) S ⊔ conjSub (g : G) D := by
    rw [hsx, hsδ, ← conjSub_inf, inf_comm, F.P1_inf_P2, F.bigB_eq, conjSub_sup]
  set P : Subgroup G := Qv α ⊔ Qv β with hP
  set D' : Subgroup G := conjSub (g : G) D with hD'
  have hPN : P ≤ N := sup_le hNα hNβ
  have hD'B : D' ≤ stab α ⊓ stab β := by rw [hB, ← hsup]; exact le_sup_right
  have hD'n : D' ≤ Subgroup.normalizer (P : Set G) := hD'B.trans hnorm
  have hρB : ρ ∈ P ⊔ D' := by rw [hsup, ← hB]; exact ⟨hρα, hρβ⟩
  obtain ⟨p, hp, d, hd, hρpd⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hD'n).mp hρB
  have hP2 : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    have hxs : x ∈ stab α := hsylα.1 hx
    obtain ⟨k, hk⟩ := hsylα.2.1 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hd1 : d ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hρpd
    obtain ⟨k, hk⟩ := hP2 p hp
    have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk, hρpd ▸ hρ3⟩
    rw [hg, pow_one] at this
    exact hρ1 (hρpd ▸ this)
  have hD'3 : Nat.card D' = 3 := by rw [hD', card_conjSub, F.D_card]
  have hd3 : d ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥D') (x := ⟨d, hd⟩)
    rw [hD'3] at this
    simpa using congrArg Subtype.val this
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hgen : Subgroup.zpowers d = D' :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd)
      (by rw [hD'3, Nat.card_zpowers, hdord])
  have hdN : d ∈ N := by
    have : d = p⁻¹ * ρ := by rw [hρpd]; group
    rw [this]
    exact N.mul_mem (N.inv_mem (hPN hp)) hNρ
  have hD'N : D' ≤ N := by rw [← hgen]; exact Subgroup.zpowers_le.mpr hdN
  rw [hB, ← hsup]
  exact sup_le hPN hD'N

end Edge

section Transport

variable {H M : Subgroup G}

@[expose] def QuadAt (x δ : Geo H M) : Prop :=
  ∀ z ∈ Zv x, ∀ t ∈ Qv δ, z * t * z⁻¹ * t⁻¹ ∈ Subgroup.centralizer (Qv δ : Set G)

omit [Finite G] in
theorem QuadAt.smul {x δ : Geo H M} (h : QuadAt x δ) (g : ↥(H ⊔ M)) : QuadAt (g • x) (g • δ) := by
  intro z hz t ht
  rw [Zv_smul, mem_conjSub] at hz
  rw [Qv_smul, mem_conjSub] at ht
  have hc := h _ hz _ ht
  rw [Qv_smul, Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : (g : G)⁻¹ * y * (g : G) ∈ Qv δ := mem_conjSub.mp hy
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hy'
  have e : (g : G)⁻¹ * (z * t * z⁻¹ * t⁻¹) * (g : G) =
      ((g : G)⁻¹ * z * (g : G)) * ((g : G)⁻¹ * t * (g : G)) * ((g : G)⁻¹ * z * (g : G))⁻¹ *
        ((g : G)⁻¹ * t * (g : G))⁻¹ := by group
  rw [← e] at h1
  calc y * (z * t * z⁻¹ * t⁻¹)
      = (g : G) * (((g : G)⁻¹ * y * (g : G)) * ((g : G)⁻¹ * (z * t * z⁻¹ * t⁻¹) * (g : G))) *
          (g : G)⁻¹ := by group
    _ = (g : G) * (((g : G)⁻¹ * (z * t * z⁻¹ * t⁻¹) * (g : G)) * ((g : G)⁻¹ * y * (g : G))) *
          (g : G)⁻¹ := by rw [h1]
    _ = z * t * z⁻¹ * t⁻¹ * y := by group

theorem QuadAt.transport {x δ x' δ' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hx : vtype x = true) (hδ : δ ∈ nbrs x) (hx' : vtype x' = true) (hδ' : δ' ∈ nbrs x')
    (h : QuadAt x δ) : QuadAt x' δ' := by
  obtain ⟨g₁, hg1, hg0⟩ := exists_edge_conj_true hx hδ
  obtain ⟨g₂, hg2, hg3⟩ := exists_edge_conj_true hx' hδ'
  have e1 : (g₂ * g₁⁻¹) • x = x' := by
    rw [← hg1, ← hg2, mul_smul, inv_smul_smul]
  have e2 : (g₂ * g₁⁻¹) • δ = δ' := by
    rw [← hg0, ← hg3, mul_smul, inv_smul_smul]
  have := h.smul (g₂ * g₁⁻¹)
  rwa [e1, e2] at this

end Transport

end CFSG.Quasithin.Kleidman.F204
