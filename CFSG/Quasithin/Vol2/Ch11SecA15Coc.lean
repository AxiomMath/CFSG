module

public import CFSG.Quasithin.Background.JonesParshallSL3
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open CFSG.Quasithin.JonesParshall (SL3 mu3 Z1A B1A coboundaryA)
open scoped Matrix

variable {G : Type} [Group G]

theorem commutator_eq_of_map_eq {L : Subgroup G} {H : Type*} [Group H] (α : ↥L →* H) {z : G}
    (hzK : ∀ l : ↥L, α l = 1 → (l : G) * z = z * l) {l₁ l₂ : ↥L} (h : α l₁ = α l₂) :
    (l₁ : G) * z * (l₁ : G)⁻¹ * z⁻¹ = (l₂ : G) * z * (l₂ : G)⁻¹ * z⁻¹ := by
  have hk : α (l₁⁻¹ * l₂) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h1 := hzK _ hk
  have h2 : (l₂ : G) = l₁ * ((l₁⁻¹ * l₂ : ↥L) : G) := by simp
  rw [h2]
  calc (l₁ : G) * z * (l₁ : G)⁻¹ * z⁻¹
      = (l₁ : G) * (((l₁⁻¹ * l₂ : ↥L) : G) * z * ((l₁⁻¹ * l₂ : ↥L) : G)⁻¹) * (l₁ : G)⁻¹ * z⁻¹ := by
        rw [h1, mul_inv_cancel_right]
    _ = (l₁ * ((l₁⁻¹ * l₂ : ↥L) : G)) * z * (l₁ * ((l₁⁻¹ * l₂ : ↥L) : G))⁻¹ * z⁻¹ := by group

theorem exists_mem_centralizer_of_cocycle {L U : Subgroup G} {F : Type} [Field F] [Fintype F]
    {a k : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) (α : ↥L →* ↥(StatedSL 3 F))
    (hα : Function.Surjective α) (β : ↥U ≃* Multiplicative (Fin k → Fin 3 → F))
    (hβ : ∀ (l : ↥L) (u v : ↥U), (v : G) = l * u * l⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          Multiplicative.toAdd (β u) i)
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    {z : G} (hzL : ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ U)
    (hzK : ∀ l : ↥L, α l = 1 → (l : G) * z = z * l) :
    ∃ u₀ ∈ U, u₀⁻¹ * z ∈ Subgroup.centralizer (L : Set G) := by
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := a) Nat.prime_two (by omega) (by rw [Nat.card_eq_fintype_card, hF])
  set e := specialLinearGroupEquivStatedSL 3 F with he
  set α' : ↥L →* SL3 F := e.symm.toMonoidHom.comp α with hα'
  have hα's : Function.Surjective α' := e.symm.surjective.comp hα
  have hα'k : ∀ l : ↥L, α' l = 1 → α l = 1 := fun l hl => by
    have := congrArg e hl
    simpa [hα'] using this
  let d : ↥L → ↥U := fun l => ⟨(l : G) * z * (l : G)⁻¹ * z⁻¹, hzL l l.2⟩
  have hd : ∀ {l₁ l₂ : ↥L}, α' l₁ = α' l₂ → d l₁ = d l₂ := fun {l₁ l₂} h => by
    apply Subtype.ext
    exact commutator_eq_of_map_eq α' (fun l hl => hzK l (hα'k l hl)) h
  let cj : ↥L → ↥U → ↥U := fun l u =>
    ⟨(l : G) * (u : G) * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLU l.2) u).mp u.2⟩
  have hdmul : ∀ l l' : ↥L, d (l * l') = cj l (d l') * d l := by
    intro l l'
    apply Subtype.ext
    simp only [d, cj, Subgroup.coe_mul]
    group
  have hmat : ∀ l : ↥L, ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α' l : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
    intro l
    have h1 : e (α' l) = α l := by simp [hα']
    rw [← h1]
    rfl
  have hcj : ∀ (l : ↥L) (u : ↥U) (i : Fin k), Multiplicative.toAdd (β (cj l u)) i =
      ((α' l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u) i := by
    intro l u i
    rw [← hmat]
    exact hβ l u (cj l u) rfl i
  let sγ := Function.surjInv hα's
  have hsγ : ∀ γ, α' (sγ γ) = γ := Function.surjInv_eq hα's
  let f : Fin k → SL3 F → (Fin 3 → F) := fun i γ => Multiplicative.toAdd (β (d (sγ γ))) i
  have hfd : ∀ (i : Fin k) (l : ↥L), f i (α' l) = Multiplicative.toAdd (β (d l)) i := by
    intro i l
    simp only [f]
    rw [hd (hsγ (α' l))]
  have hZ1 : ∀ i, f i ∈ Z1A (mu3 (F := F)) := by
    intro i γ γ'
    obtain ⟨l, rfl⟩ := hα's γ
    obtain ⟨l', rfl⟩ := hα's γ'
    rw [← map_mul, hfd, hfd, hfd, hdmul, map_mul, toAdd_mul, Pi.add_apply, hcj,
      JonesParshall.mu3_apply, JonesParshall.smul3_def, add_comm]
  have hB1 : ∀ i, ∃ m : Fin 3 → F, coboundaryA (mu3 (F := F)) m = f i := fun i =>
    JonesParshall.mem_B1A_mu3 hF ha (hZ1 i)
  choose m hm using hB1
  set u₀ : ↥U := β.symm (Multiplicative.ofAdd m) with hu₀
  have hβu₀ : Multiplicative.toAdd (β u₀) = m := by simp [hu₀]
  have hdl : ∀ l : ↥L, d l = cj l u₀ * u₀⁻¹ := by
    intro l
    apply β.injective
    apply Multiplicative.toAdd.injective
    funext i
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, hcj, hβu₀,
      ← hfd, ← hm i, JonesParshall.coboundaryA_apply, JonesParshall.mu3_apply,
      JonesParshall.smul3_def, sub_eq_add_neg]
  refine ⟨u₀, u₀.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := congrArg Subtype.val (hdl ⟨x, hx⟩)
  simp only [d, cj, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have h2 : x * ((u₀ : G)⁻¹ * z) * x⁻¹ = (u₀ : G)⁻¹ * z := by
    calc x * ((u₀ : G)⁻¹ * z) * x⁻¹ = (x * (u₀ : G) * x⁻¹)⁻¹ * (x * z * x⁻¹ * z⁻¹) * z := by
          group
      _ = (u₀ : G)⁻¹ * z := by rw [h1]; group
  calc x * ((u₀ : G)⁻¹ * z) = x * ((u₀ : G)⁻¹ * z) * x⁻¹ * x := by group
    _ = (u₀ : G)⁻¹ * z * x := by rw [h2]

end CFSG.Quasithin.Vol2.Ch11.SecA
