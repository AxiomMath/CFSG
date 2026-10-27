module

public import CFSG.Quasithin.MS93.S45UB
public import CFSG.Quasithin.MS93.S45M0

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Abstract

variable {𝔾 : Type} [Group 𝔾]

theorem burnsideRig_le_of_torus {A B S' St : Subgroup 𝔾} {e : 𝔾}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hBA : B ≤ A)
    (heA : ∀ a ∈ A, e * a * e⁻¹ ∈ A) (heB : ∀ b ∈ B, e * b * e⁻¹ ∈ B)
    (heSt : ∀ s ∈ St, e * s * e⁻¹ ∈ St)
    (htriv : ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ S')
    (hsurj : ∀ a ∈ A, ∃ y ∈ A, (e * y * e⁻¹ * y⁻¹)⁻¹ * a ∈ B)
    (hcap : St ⊓ B ≤ S') (hsup : ∀ a ∈ A, ∃ s ∈ St, ∃ b ∈ B, a = s * b) (hStA : St ≤ A) :
    St ≤ S' := by
  intro s hs
  obtain ⟨y, hyA, hyB⟩ := hsurj s (hStA hs)
  obtain ⟨s₁, hs₁, b₁, hb₁, rfl⟩ := hsup y hyA
  set u := e * s₁ * e⁻¹ * s₁⁻¹ with hu
  set v := e * b₁ * e⁻¹ * b₁⁻¹ with hv
  have hs₁A := hStA hs₁
  have hb₁A := hBA hb₁
  have huSt : u ∈ St := St.mul_mem (heSt s₁ hs₁) (St.inv_mem hs₁)
  have huS' : u ∈ S' := htriv s₁ hs₁A
  have hvB : v ∈ B := B.mul_mem (heB b₁ hb₁) (B.inv_mem hb₁)
  have hvA : v ∈ A := hBA hvB
  have hcomm : s₁⁻¹ * v = v * s₁⁻¹ := hA _ (A.inv_mem hs₁A) _ hvA
  have he : e * (s₁ * b₁) * e⁻¹ * (s₁ * b₁)⁻¹ = u * v := by
    calc e * (s₁ * b₁) * e⁻¹ * (s₁ * b₁)⁻¹ = (e * s₁ * e⁻¹) * (v * s₁⁻¹) := by
          rw [hv]; group
      _ = (e * s₁ * e⁻¹) * (s₁⁻¹ * v) := by rw [hcomm]
      _ = u * v := by rw [hu]; group
  rw [he] at hyB
  have h1 : u⁻¹ * s ∈ B := by
    have e1 : u⁻¹ * s = v * ((u * v)⁻¹ * s) := by group
    rw [e1]
    exact B.mul_mem hvB hyB
  have h2 : u⁻¹ * s ∈ St := St.mul_mem (St.inv_mem huSt) hs
  have h3 : u⁻¹ * s ∈ S' := hcap (Subgroup.mem_inf.mpr ⟨h2, h1⟩)
  have e2 : s = u * (u⁻¹ * s) := by group
  rw [e2]
  exact S'.mul_mem huS' h3

theorem burnsideRig_card_sup_mul_card_inf {H N : Subgroup 𝔾}
    (h : H ≤ Subgroup.normalizer (N : Set 𝔾)) :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(N ⊓ H) = Nat.card ↥H * Nat.card ↥N := by
  have h1 := Subgroup.relIndex_mul_card (H := N) (K := H ⊔ N)
  rw [inf_of_le_left (le_sup_right : N ≤ H ⊔ N), relIndex_sup_eq h] at h1
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := H)
  rw [← h1, ← h2]
  ring

end Abstract

section NatSecCount

variable {Γ : Type} [Group Γ] {F : Type} [Field F] {L V K : Subgroup Γ}
  {ψ : ↥L →* ↥(StatedSL 3 F)} {dual : Bool}

theorem burnsideRig_card_eq_of_natSec [Finite F] (N : NatSec L V K ψ dual) :
    Nat.card ↥V = Nat.card ↥K * Nat.card F ^ 3 := by
  have h1 := Subgroup.card_mul_index N.β.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr N.surj, Subgroup.card_top] at h1
  have hker : N.β.ker = K.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, N.ker v, Subgroup.mem_subgroupOf]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe N.le).toEquiv] at h1
  rw [← h1, show Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (Fin 3 → F) from rfl,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

theorem burnsideRig_card_le_of_coord (N : NatSec L V K ψ dual) [Finite ↥K] {H : Subgroup Γ}
    (hHV : H ≤ V) {S : Set (Fin 3 → F)} [Finite S] (hS : ∀ v ∈ H, N.coord v ∈ S) :
    Nat.card ↥H ≤ Nat.card ↥K * Nat.card S := by
  set f : ↥H →* Multiplicative (Fin 3 → F) := N.β.comp (Subgroup.inclusion hHV) with hf
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  refine Nat.mul_le_mul ?_ ?_
  · refine Nat.card_le_card_of_injective
      (fun x : ↥f.ker => (⟨((x : ↥H) : Γ), ?_⟩ : ↥K)) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      exact (N.ker (Subgroup.inclusion hHV x)).mp hx
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only at h
      exact Subtype.ext (Subtype.ext h)
  · have hmem : ∀ r : ↥f.range, Multiplicative.toAdd (r : Multiplicative (Fin 3 → F)) ∈ S := by
      rintro ⟨_, v, rfl⟩
      have := hS v v.2
      rwa [N.coord_of_mem (hHV v.2)] at this
    refine Nat.card_le_card_of_injective (fun r => ⟨_, hmem r⟩) fun r s hrs => ?_
    have h := congrArg Subtype.val hrs
    simp only at h
    exact Subtype.ext (Multiplicative.toAdd.injective h)

end NatSecCount

section TwoDuals

variable {Γ : Type} [Group Γ] {F : Type} [Field F]

theorem burnsideRig_card_le_of_isSum_two [Finite F] {K W Z X Q : Subgroup Γ} [Finite ↥Z]
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hW : IsSumOfNaturalModulesVia K W Z ψ true 2) (hXW : X ≤ W)
    (hQK : Q ≤ K) (hQ : 2 ≤ Module.finrank F (commN (natImage ψ Q)))
    (hX : ∀ x ∈ X, ∀ t ∈ Q, ⁅x, t⁆ ∈ Z) :
    Nat.card ↥X ≤ Nat.card ↥Z * Nat.card F ^ 2 := by
  obtain ⟨hKW, hZW, β, -, hβker, hβeq⟩ := hW
  set S : Set (Fin 3 → F) := {y | ∀ g ∈ natImage ψ Q, dualMat g *ᵥ y = y} with hSdef
  have hScard : Nat.card S ≤ Nat.card F := S45U.card_dualFix_le' hQ S fun y hy => hy
  have hfix : ∀ x : ↥W, (x : Γ) ∈ X → ∀ i : Fin 2, Multiplicative.toAdd (β x) i ∈ S := by
    intro x hx i g hg
    obtain ⟨t, htQ, rfl⟩ := mem_natImage.mp hg
    have hxinv : (t : Γ) * ((x : Γ))⁻¹ * (t : Γ)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hKW t.2) _).mp (W.inv_mem x.2)
    set y : ↥W := ⟨_, hxinv⟩ with hy
    have hyeq := hβeq t x⁻¹ y rfl i
    rw [moduleAct_eq_natAct, natAct_true] at hyeq
    have hc : ⁅(x : Γ), (t : Γ)⁆ ∈ Z := hX x hx t htQ
    have hmem : x * y ∈ Z.subgroupOf W := by
      rw [Subgroup.mem_subgroupOf]
      have e1 : ((x * y : ↥W) : Γ) = ⁅(x : Γ), (t : Γ)⁆ := by
        rw [commutatorElement_def, Subgroup.coe_mul, hy]
        group
      rw [e1]
      exact hc
    rw [← hβker, MonoidHom.mem_ker, map_mul] at hmem
    have h0 := congrArg (fun m : Multiplicative (Fin 2 → Fin 3 → F) => Multiplicative.toAdd m i) hmem
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply] at h0
    rw [hyeq, map_inv, toAdd_inv, Pi.neg_apply, Matrix.mulVec_neg] at h0
    exact (add_neg_eq_zero.mp h0).symm
  set f : ↥X →* Multiplicative (Fin 2 → Fin 3 → F) := β.comp (Subgroup.inclusion hXW) with hf
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  refine Nat.mul_le_mul ?_ ?_
  · refine Nat.card_le_card_of_injective
      (fun x : ↥f.ker => (⟨((x : ↥X) : Γ), ?_⟩ : ↥Z)) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have : Subgroup.inclusion hXW x.1 ∈ β.ker := hx
      rw [hβker, Subgroup.mem_subgroupOf] at this
      exact this
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only at h
      exact Subtype.ext (Subtype.ext h)
  · have hmem : ∀ r : ↥f.range, ∀ i : Fin 2,
        Multiplicative.toAdd (r : Multiplicative (Fin 2 → Fin 3 → F)) i ∈ S := by
      rintro ⟨_, v, rfl⟩ i
      exact hfix (Subgroup.inclusion hXW v) v.2 i
    have : Finite S := Set.toFinite S
    calc Nat.card ↥f.range ≤ Nat.card (S × S) := by
          refine Nat.card_le_card_of_injective
            (fun r => (⟨_, hmem r 0⟩, ⟨_, hmem r 1⟩)) fun r s hrs => ?_
          have h0 := congrArg (fun p => (p.1 : Fin 3 → F)) hrs
          have h1' := congrArg (fun p => (p.2 : Fin 3 → F)) hrs
          simp only at h0 h1'
          apply Subtype.ext
          apply Multiplicative.toAdd.injective
          funext i
          fin_cases i
          · exact h0
          · exact h1'
      _ = Nat.card S * Nat.card S := Nat.card_prod _ _
      _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul hScard hScard
      _ = Nat.card F ^ 2 := (sq _).symm

end TwoDuals

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
