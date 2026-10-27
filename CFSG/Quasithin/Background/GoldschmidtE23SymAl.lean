module

public import CFSG.Quasithin.Background.GoldschmidtE23SymSpec
public import CFSG.Quasithin.Background.GoldschmidtE23Blocks
public import CFSG.Quasithin.Background.GoldschmidtE23SymFin2
public import CFSG.Quasithin.Vol2.Ch3zBlocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 Equiv

namespace GE23

section Exists

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_symSpec_aux {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {H : Subgroup (MulAut V)} (hH : SymBlk X H 2) :
    ∃ (ψ : Perm (Fin 5) →* MulAut V) (β : ↥(coreMod 5) →* V), Function.Injective ψ ∧
      ψ.range = H ∧ Function.Injective β ∧ β.range = commV H ∧
      ∀ (σ : Perm (Fin 5)) (u : ↥(coreMod 5)), β (coreAct 5 σ u) = ψ σ (β u) := by
  obtain ⟨L, A, hL, hA, hLA, hblk, rfl, hk, π, hπs, hreal, hLeq, -⟩ := hH
  have hcomm : commV (L ⊔ A) = commV L := by
    rw [← hblk]
    exact commV_blk hB hL
  obtain ⟨θ, β₀, hθ, hβ, hrange, hker⟩ := Ch3z.isSymCore_of_realizes' hreal
  have hinj : Function.Injective β₀ := (injective_iff_map_eq_one β₀).2 fun u hu => by
    have : u ∈ β₀.ker := hu
    rw [hker] at this
    exact Subgroup.mem_bot.1 this
  have hπθ : ∀ σ, θ (π σ) = σ := fun σ => by rw [← hθ σ]; exact θ.apply_symm_apply σ
  refine ⟨(L ⊔ A).subtype.comp π, β₀, ?_, ?_, hinj, hrange.trans hcomm.symm, ?_⟩
  · intro a b hab
    have h1 : π a = π b := Subtype.ext hab
    have := congrArg θ h1
    rwa [hπθ, hπθ] at this
  · ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact (π σ).2
    · intro hx
      obtain ⟨σ, hσ⟩ := hπs ⟨x, hx⟩
      exact ⟨σ, congrArg Subtype.val hσ⟩
  · intro σ u
    have := hβ (π σ) u
    rw [hπθ] at this
    exact this

theorem exists_symSpec {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {H D : Subgroup (MulAut V)} (hH : SymBlk X H 2) (hD : IsSylowTwoOf D H) :
    ∃ (ψ : Perm (Fin 5) →* MulAut V) (β : ↥(coreMod 5) →* V), SymSpec H D ψ β := by
  classical
  obtain ⟨ψ₀, β₀, hψi, hψr, hβi, hβr, heq⟩ := exists_symSpec_aux hB hH
  have hDH : D ≤ H := hD.1
  set D' : Subgroup (Perm (Fin 5)) := D.comap ψ₀ with hD'
  have hDD' : D'.map ψ₀ = D := Subgroup.map_comap_eq_self (hψr ▸ hDH)
  have hcardD' : Nat.card ↥D' = Nat.card ↥D := by
    rw [← hDD']
    exact (Subgroup.card_map_of_injective hψi).symm
  have hcardH : Nat.card ↥H = 120 := by
    have e : Perm (Fin 5) ≃* ↥ψ₀.range := MonoidHom.ofInjective hψi
    have : Nat.card ↥ψ₀.range = 120 := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    rwa [hψr] at this
  have hrelD : D.relIndex H * Nat.card ↥D = 120 := by
    have := Subgroup.relIndex_mul_card D H
    rwa [inf_of_le_left hDH, hcardH] at this
  have hrelD' : D'.relIndex ⊤ * Nat.card ↥D' = 120 := by
    have := Subgroup.relIndex_mul_card D' ⊤
    rwa [inf_top_eq, Subgroup.card_top, Nat.card_perm, Nat.card_fin] at this
  have hrel : D'.relIndex ⊤ = D.relIndex H := by
    rw [hcardD'] at hrelD'
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hrelD'.trans hrelD.symm)
  have hD'syl : IsSylowTwoOf D' ⊤ := by
    refine ⟨le_top, hD.2.1.comap_of_injective ψ₀ hψi, ?_⟩
    show ¬ 2 ∣ D'.relIndex ⊤
    rw [hrel]
    exact hD.2.2
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_d8 hD'syl
  have hmap : d8.map (MulAut.conj g).toMonoidHom = D' := by
    rw [hg]
    rfl
  refine ⟨ψ₀.comp (MulAut.conj g).toMonoidHom, β₀.comp (coreAct 5 g).toMonoidHom,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hψi.comp (MulAut.conj g).injective
  · rw [← hψr]
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨τ, rfl⟩
      refine ⟨g⁻¹ * τ * g, ?_⟩
      show ψ₀ (g * (g⁻¹ * τ * g) * g⁻¹) = ψ₀ τ
      rw [show g * (g⁻¹ * τ * g) * g⁻¹ = τ by group]
  · exact hβi.comp (coreAct 5 g).injective
  · rw [← hβr]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨(coreAct 5 g)⁻¹ u, ?_⟩
      show β₀ (coreAct 5 g ((coreAct 5 g)⁻¹ u)) = β₀ u
      simp
  · intro τ u
    show β₀ (coreAct 5 g (coreAct 5 τ u)) =
      ψ₀ (g * τ * g⁻¹) (β₀ (coreAct 5 g u))
    rw [← heq, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    rw [show g * τ * g⁻¹ * g = g * τ by group]
  · rw [← Subgroup.map_map, hmap, hDD']

end Exists

end GE23

end CFSG.Quasithin
