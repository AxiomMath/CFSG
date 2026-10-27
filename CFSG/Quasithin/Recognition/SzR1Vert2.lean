module

public import CFSG.Quasithin.Recognition.SzR1Vert

public section

namespace CFSG.Quasithin.SzR1

open CFSG.Quasithin
open scoped commutatorElement

namespace Orbit

variable {G : Type*} [Group G]

theorem prod_three {Δ : Type*} [Fintype Δ] {C : Type*} [CommMonoid C] {β lam δ : Δ}
    (hlb : lam ≠ β) (hδb : δ ≠ β) (hδl : δ ≠ lam) (hall : ∀ x, x = β ∨ x = lam ∨ x = δ)
    (F : Δ → C) : ∏ x, F x = F β * F lam * F δ := by
  classical
  have huniv : (Finset.univ : Finset Δ) = {β, lam, δ} := by
    ext x
    simpa using hall x
  rw [huniv, Finset.prod_insert (by simp [hlb.symm, hδb.symm]), Finset.prod_pair hδl.symm,
    mul_assoc]

theorem perm_prod_three {Δ : Type*} [Fintype Δ] {C : Type*} [CommMonoid C] {β lam δ : Δ}
    (hlb : lam ≠ β) (hδb : δ ≠ β) (hδl : δ ≠ lam) (hall : ∀ x, x = β ∨ x = lam ∨ x = δ)
    (σ : Equiv.Perm Δ) (F : Δ → C) :
    F (σ β) * F (σ lam) * F (σ δ) = F β * F lam * F δ := by
  have h1 : ∏ x, F (σ x) = F (σ β) * F (σ lam) * F (σ δ) :=
    prod_three hlb hδb hδl hall (fun x => F (σ x))
  have h2 : ∏ x, F x = F β * F lam * F δ := prod_three hlb hδb hδl hall F
  rw [← h1, ← h2]
  exact Equiv.prod_comp σ F

theorem exists_invariant_product {P S T : Subgroup G} {u : G} (hS3 : S.relIndex P = 3)
    (hTN : P ≤ Subgroup.normalizer (T : Set G)) (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (huT : u ∈ T) (huS : ∀ s ∈ S, u * s = s * u) :
    ∃ a₁ ∈ P, ∃ a₂ ∈ P, a₁ ∉ S ∧ a₂ ∉ S ∧ a₁⁻¹ * a₂ ∉ S ∧ ∀ p ∈ P,
      p * (u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹)) * p⁻¹ =
        u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹) := by
  classical
  have hcard : Nat.card (↥P ⧸ S.subgroupOf P) = 3 := hS3
  have hfin : Finite (↥P ⧸ S.subgroupOf P) := Nat.finite_of_card_ne_zero (by omega)
  have hfint : Fintype (↥P ⧸ S.subgroupOf P) := Fintype.ofFinite _
  let : CommGroup ↥T :=
    { (inferInstance : Group ↥T) with mul_comm := fun a b => Subtype.ext (hTc a.1 a.2 b.1 b.2) }
  obtain ⟨β, hβ⟩ : ∃ β : ↥P ⧸ S.subgroupOf P, β = ((1 : ↥P) : ↥P ⧸ S.subgroupOf P) :=
    ⟨_, rfl⟩
  obtain ⟨lam, δ, hlb, hδb, hδl, hall⟩ := Vert.exists_two_others hcard β
  have hmem : ∀ h : ↥P, (h : G) * u * (h : G)⁻¹ ∈ T := fun h =>
    (Subgroup.mem_normalizer_iff.mp (hTN h.2) u).mp huT
  let w : ↥P → ↥T := fun h => ⟨(h : G) * u * (h : G)⁻¹, hmem h⟩
  have hw : ∀ h h' : ↥P, (h : ↥P ⧸ S.subgroupOf P) = h' → w h = w h' := by
    intro h h' hh
    have h1 : (h : G)⁻¹ * h' ∈ S := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hh)
    have h3 : ((h : G)⁻¹ * h') * u * ((h : G)⁻¹ * h')⁻¹ = u := by
      rw [← huS _ h1]
      group
    refine Subtype.ext ?_
    calc (h : G) * u * (h : G)⁻¹
        = (h : G) * (((h : G)⁻¹ * h') * u * ((h : G)⁻¹ * h')⁻¹) * (h : G)⁻¹ := by rw [h3]
      _ = (h' : G) * u * (h' : G)⁻¹ := by group
  let ū : ↥P ⧸ S.subgroupOf P → ↥T := fun x => w x.out
  have hū : ∀ h : ↥P, ū (h : ↥P ⧸ S.subgroupOf P) = w h := fun h =>
    hw _ _ (QuotientGroup.out_eq' _)
  have hsm : ∀ (p : ↥P) (x : ↥P ⧸ S.subgroupOf P),
      ((ū (p • x) : ↥T) : G) = (p : G) * (ū x : G) * (p : G)⁻¹ := by
    intro p x
    induction x using QuotientGroup.induction_on with
    | H h =>
      rw [Vert.smul_mk, hū, hū]
      change ((p * h : ↥P) : G) * u * ((p * h : ↥P) : G)⁻¹ =
        (p : G) * ((h : G) * u * (h : G)⁻¹) * (p : G)⁻¹
      rw [Subgroup.coe_mul]
      group
  have hu0 : ((ū β : ↥T) : G) = u := by
    rw [hβ, hū]
    change ((1 : ↥P) : G) * u * ((1 : ↥P) : G)⁻¹ = u
    simp
  have hu1 : ((ū lam : ↥T) : G) = (lam.out : G) * u * (lam.out : G)⁻¹ := rfl
  have hu2 : ((ū δ : ↥T) : G) = (δ.out : G) * u * (δ.out : G)⁻¹ := rfl
  have hfix : ∀ (x : ↥P ⧸ S.subgroupOf P) (h : ↥P), (x.out : G)⁻¹ * (h : G) ∈ S →
      x = (h : ↥P ⧸ S.subgroupOf P) := fun x h hxh => by
    have := QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hxh : x.out⁻¹ * h ∈ S.subgroupOf P)
    rwa [QuotientGroup.out_eq'] at this
  refine ⟨(lam.out : G), lam.out.2, (δ.out : G), δ.out.2, fun h => hlb ?_, fun h => hδb ?_,
    fun h => hδl ?_, fun p hp => ?_⟩
  · exact (hfix lam 1 (by simpa using h)).trans hβ.symm
  · exact (hfix δ 1 (by simpa using h)).trans hβ.symm
  · exact ((hfix lam δ.out h).trans (QuotientGroup.out_eq' δ)).symm
  have e0 : ((ū ((⟨p, hp⟩ : ↥P) • β) : ↥T) : G) = p * u * p⁻¹ := by
    rw [hsm, hu0]
  have e1 : ((ū ((⟨p, hp⟩ : ↥P) • lam) : ↥T) : G) = p * ((lam.out : G) * u * (lam.out : G)⁻¹) *
      p⁻¹ := by
    rw [hsm, hu1]
  have e2 : ((ū ((⟨p, hp⟩ : ↥P) • δ) : ↥T) : G) = p * ((δ.out : G) * u * (δ.out : G)⁻¹) *
      p⁻¹ := by
    rw [hsm, hu2]
  have key := Subtype.ext_iff.mp
    (perm_prod_three hlb hδb hδl hall (MulAction.toPerm (⟨p, hp⟩ : ↥P)) ū)
  change ((ū ((⟨p, hp⟩ : ↥P) • β) : ↥T) : G) * ((ū ((⟨p, hp⟩ : ↥P) • lam) : ↥T) : G) *
      ((ū ((⟨p, hp⟩ : ↥P) • δ) : ↥T) : G) = (ū β : G) * (ū lam : G) * (ū δ : G) at key
  rw [e0, e1, e2, hu0, hu1, hu2] at key
  calc p * (u * ((lam.out : G) * u * (lam.out : G)⁻¹) * ((δ.out : G) * u * (δ.out : G)⁻¹)) * p⁻¹
      = p * u * p⁻¹ * (p * ((lam.out : G) * u * (lam.out : G)⁻¹) * p⁻¹) *
        (p * ((δ.out : G) * u * (δ.out : G)⁻¹) * p⁻¹) := by group
    _ = _ := key

theorem mul_comm_of_commutator_eq_bot {T : Subgroup G} (h : ⁅T, T⁆ = ⊥) {x y : G} (hx : x ∈ T)
    (hy : y ∈ T) : x * y = y * x := by
  have h1 := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem exists_T_u [Finite G] {P S Q W Z M : Subgroup G}
    (hSP : S ≤ P) (hQS : Q ≤ S) (hQN : P ≤ Subgroup.normalizer (Q : Set G))
    (hS2 : IsPGroup 2 S)
    (hmax : ∀ N : Subgroup G, N ≤ P → P ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N →
      N ≤ Q)
    (hS3 : S.relIndex P = 3) (hQ2 : Q.relIndex S = 2)
    (hWS : W ≤ S) (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (hSM : S ≤ Subgroup.normalizer (M : Set G)) (hWM : W ≤ M)
    (hSZ : S ≤ Subgroup.centralizer (Z : Set G)) (hZ2 : Nat.card Z = 2)
    (hZP : ¬ P ≤ Subgroup.normalizer (Z : Set G))
    (hZW : ∀ g ∈ P, conjSub g Z ≤ W)
    (hWW : ⁅W, W⁆ ≤ Z) (hMW : ⁅M, W⁆ ≤ Z)
    (hWQ : ¬ W ≤ Q)
    (hnonab : ⁅W ⊓ Q, W ⊓ Q⁆ ≠ ⊥)
    (hB1 : ∀ s ∈ Q, (∀ w ∈ W ⊓ Q, s * w * s⁻¹ * w⁻¹ ∈ Z) → s ∈ M) :
    ∃ b ∈ P, b ∉ Subgroup.normalizer (Z : Set G) ∧
      ∃ a ∈ P, a ∉ Subgroup.normalizer (Z : Set G) ∧
        ∃ T : Subgroup G, P ≤ Subgroup.normalizer (T : Set G) ∧ T ≤ W ⊓ conjSub a W ∧
          (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
          ∃ u ∈ T, u ≠ 1 ∧ u * u = 1 ∧ (∀ s ∈ S, u * s = s * u) ∧ b * u * b⁻¹ ∈ ⁅W, S⁆ := by
  have hyp : Vert.Hyp P S Q W Z M :=
    ⟨hSP, hQS, hQN, hS3, hQ2, hWS, hSW, hSM, hWM, hZW, hWW, hMW, hWQ, hnonab, hB1⟩
  obtain ⟨g, b, y, hgP, hgS, hgg, hbP, hbS, hbg, hyg, hyS, hcase⟩ :=
    Vert.exists_vertex_elements hSP hQS hQN hS2 hmax hS3 hQ2
  have hSZN : S ≤ Subgroup.normalizer (Z : Set G) :=
    hSZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hgZ : g ∉ Subgroup.normalizer (Z : Set G) :=
    Vert.not_mem_normalizer_of_not_mem hSP hS3 hSZN hZP hgP hgS
  have hbZ : b ∉ Subgroup.normalizer (Z : Set G) :=
    Vert.not_mem_normalizer_of_not_mem hSP hS3 hSZN hZP hbP hbS
  have hTN := hyp.le_normalizer_T hgP hyg hyS
  have hTg : conjSub g (W ⊓ conjSub g M) = W ⊓ conjSub g M :=
    Vert.conjSub_eq_of_mem_normalizer (hTN hgP)
  have hTb : conjSub b (W ⊓ conjSub g M) = W ⊓ conjSub g M :=
    Vert.conjSub_eq_of_mem_normalizer (hTN hbP)
  have hTWl : W ⊓ conjSub g M ≤ conjSub g W := hyp.T_le_conjSub hgg hTg
  have hZZ : Z ⊓ conjSub g Z = ⊥ :=
    Vert.inf_eq_bot_of_card_two hZ2 ((Vert.card_conjSub g Z).trans hZ2)
      (fun h => hgZ (Vert.mem_normalizer_of_conjSub_eq h))
  have hTab := hyp.commutator_T_eq_bot hTWl hZZ
  have hD := hyp.not_commutator_le hgP hgg hTab
  have hD1 : ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ ≠ ⊥ := fun h0 => hD (h0.le.trans bot_le)
  have hDQ : ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ ≤ Q := Vert.commutator_le_of_le inf_le_right inf_le_right
  have hQb : Q ≤ conjSub b S :=
    calc Q = conjSub b Q := (Vert.conjSub_eq_of_mem_normalizer (hQN hbP)).symm
      _ ≤ conjSub b S := conjSub_mono b hQS
  have hSbN : conjSub b S ≤
      Subgroup.normalizer ((⁅W ⊓ Q, conjSub g W ⊓ Q⁆ : Subgroup G) : Set G) :=
    fun s hs => Vert.mem_normalizer_of_conjSub_eq
      (hyp.conjSub_D (Vert.conjSub_le_of_mem hSP hbP hs) (hcase s hs))
  obtain ⟨u₁, hu₁D, hu₁1, hu₁sq, hu₁c⟩ :=
    Vert.exists_involution_central (F7.isPGroup_conjSub hS2) (hDQ.trans hQb) hD1 hSbN
  have hu₁T : u₁ ∈ W ⊓ conjSub g M := hyp.D_le_T hgP hu₁D
  refine ⟨b, hbP, hbZ, g, hgP, hgZ, W ⊓ conjSub g M, hTN, le_inf inf_le_left hTWl,
    fun x hx y hy => mul_comm_of_commutator_eq_bot hTab hx hy, b⁻¹ * u₁ * b,
    mem_conjSub.mp (hTb.ge hu₁T), ?_, ?_, ?_, ?_⟩
  · intro h
    apply hu₁1
    have e : u₁ = b * (b⁻¹ * u₁ * b) * b⁻¹ := by group
    rw [e, h]
    group
  · have e : b⁻¹ * u₁ * b * (b⁻¹ * u₁ * b) = b⁻¹ * (u₁ * u₁) * b := by group
    rw [e, hu₁sq]
    group
  · intro s hs
    have hc := hu₁c (b * s * b⁻¹) (mul_mem_conjSub hs)
    calc b⁻¹ * u₁ * b * s = b⁻¹ * (u₁ * (b * s * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * s * b⁻¹) * u₁) * b := by rw [hc]
      _ = s * (b⁻¹ * u₁ * b) := by group
  · have e : b * (b⁻¹ * u₁ * b) * b⁻¹ = u₁ := by group
    have hle : ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ ≤ ⁅W, S⁆ :=
      Subgroup.commutator_mono inf_le_left (inf_le_right.trans hQS)
    rw [e]
    exact hle hu₁D

end Orbit

theorem exists_central_involution_with_orbit
    {G : Type*} [Group G] [Finite G] {P S Q W Z M : Subgroup G}
    (hSP : S ≤ P) (hQS : Q ≤ S) (hQN : P ≤ Subgroup.normalizer (Q : Set G))
    (hS2 : IsPGroup 2 S)
    (hmax : ∀ N : Subgroup G, N ≤ P → P ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N →
      N ≤ Q)
    (hS3 : S.relIndex P = 3) (hQ2 : Q.relIndex S = 2)
    (hWS : W ≤ S) (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (hSM : S ≤ Subgroup.normalizer (M : Set G)) (hWM : W ≤ M)
    (hSZ : S ≤ Subgroup.centralizer (Z : Set G)) (hZ2 : Nat.card Z = 2)
    (hZP : ¬ P ≤ Subgroup.normalizer (Z : Set G))
    (hZW : ∀ g ∈ P, conjSub g Z ≤ W)
    (hWW : ⁅W, W⁆ ≤ Z) (hMW : ⁅M, W⁆ ≤ Z)
    (hWQ : ¬ W ≤ Q)
    (hnonab : ⁅W ⊓ Q, W ⊓ Q⁆ ≠ ⊥)
    (hB1 : ∀ s ∈ Q, (∀ w ∈ W ⊓ Q, s * w * s⁻¹ * w⁻¹ ∈ Z) → s ∈ M) :
    ∃ b ∈ P, b ∉ Subgroup.normalizer (Z : Set G) ∧ ∃ a ∈ P, a ∉ Subgroup.normalizer (Z : Set G) ∧
      ∃ T : Subgroup G, P ≤ Subgroup.normalizer (T : Set G) ∧ T ≤ W ⊓ conjSub a W ∧
        (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
        ∃ u ∈ T, u ≠ 1 ∧ u * u = 1 ∧ (∀ s ∈ S, u * s = s * u) ∧ b * u * b⁻¹ ∈ ⁅W, S⁆ ∧
          ∃ a₁ ∈ P, ∃ a₂ ∈ P, ∀ p ∈ P,
            p * (u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹)) * p⁻¹ =
              u * (a₁ * u * a₁⁻¹) * (a₂ * u * a₂⁻¹) := by
  obtain ⟨b, hbP, hbZ, a, haP, haZ, T, hTN, hTW, hTc, u, huT, hu1, hu2, huS, hub⟩ :=
    Orbit.exists_T_u hSP hQS hQN hS2 hmax hS3 hQ2 hWS hSW hSM hWM hSZ hZ2 hZP hZW hWW hMW hWQ
      hnonab hB1
  obtain ⟨a₁, ha₁, a₂, ha₂, -, -, -, hinv⟩ :=
    Orbit.exists_invariant_product hS3 hTN hTc huT huS
  exact ⟨b, hbP, hbZ, a, haP, haZ, T, hTN, hTW, hTc, u, huT, hu1, hu2, huS, hub, a₁, ha₁, a₂,
    ha₂, hinv⟩

end CFSG.Quasithin.SzR1
