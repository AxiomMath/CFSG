module

public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrthMat
public import CFSG.Quasithin.Vol2.Ch10SecAModels

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin
open scoped Matrix

theorem twist_conj {F : Type} [Field F] [CharP F 2] (a : ℕ)
    (g M U X : Matrix (Fin 2) (Fin 2) F) (h : U * g = g * M) :
    U * (g * X * (frobPow a g)ᵀ) * (frobPow a U)ᵀ =
      g * (M * X * (frobPow a M)ᵀ) * (frobPow a g)ᵀ := by
  have h' : frobPow a U * frobPow a g = frobPow a g * frobPow a M := by
    rw [← frobPow_mul, h, frobPow_mul]
  calc U * (g * X * (frobPow a g)ᵀ) * (frobPow a U)ᵀ =
      U * g * X * (frobPow a U * frobPow a g)ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = g * M * X * (frobPow a g * frobPow a M)ᵀ := by rw [h, h']
    _ = g * (M * X * (frobPow a M)ᵀ) * (frobPow a g)ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]

theorem exists_beta_of_realizesVia_bot {V : Type} [CommGroup V] {D : FFModel}
    {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H} (hker : D.ker = ⊥)
    (h : D.RealizesVia H ⊤ ⊥ π) :
    ∃ β : V →* D.Amb, Function.Injective β ∧ (∀ v, β v ∈ D.sec) ∧
      ∀ γ v, β (((π γ : ↥H) : MulAut V) v) = D.act γ (β v) := by
  obtain ⟨-, -, -, -, -, hsec, -, β₀, -, hβk, hβe⟩ := h
  let q : ↥D.sec →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := QuotientGroup.mk' _
  have hq : Function.Bijective q := by
    refine ⟨(injective_iff_map_eq_one q).mpr fun x hx => ?_, QuotientGroup.mk'_surjective _⟩
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, hker] at hx
    exact Subtype.ext (Subgroup.mem_bot.mp hx)
  let e := MulEquiv.ofBijective q hq
  have heq : ∀ m, e m = QuotientGroup.mk m := fun m => rfl
  let β : V →* D.Amb := D.sec.subtype.comp (e.symm.toMonoidHom.comp
    (β₀.comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom))
  have hβv : ∀ v, β v = (e.symm (β₀ ⟨v, Subgroup.mem_top v⟩) : D.Amb) := fun v => rfl
  refine ⟨β, ?_, fun v => (e.symm _).2, fun γ v => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : e.symm (β₀ ⟨v, Subgroup.mem_top v⟩) = 1 := Subtype.ext hv
    rw [MulEquiv.map_eq_one_iff, hβk] at h1
    exact Subgroup.mem_bot.mp h1
  · have hm' : β₀ ⟨v, Subgroup.mem_top v⟩ =
        QuotientGroup.mk (e.symm (β₀ ⟨v, Subgroup.mem_top v⟩)) := by
      rw [← heq, MulEquiv.apply_symm_apply]
    have h1 := hβe γ ⟨v, Subgroup.mem_top v⟩ (e.symm (β₀ ⟨v, Subgroup.mem_top v⟩))
      (Subgroup.mem_top _) (hsec _ _ (e.symm _).2) hm'
    rw [← heq] at h1
    rw [hβv, hβv, h1, MulEquiv.symm_apply_apply]

theorem exists_orthCoord {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    (hO : BinaryOrthogonalFour H ⊤ ⊥ n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * n) ∧
      ∃ (eρ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥H)
        (β : V →* Multiplicative (Matrix (Fin 2) (Fin 2) F)), Function.Injective β ∧
        (∀ v, (frobPow n (Multiplicative.toAdd (β v)))ᵀ = Multiplicative.toAdd (β v)) ∧
        ∀ γ v, β (((eρ γ : ↥H) : MulAut V) v) = Multiplicative.ofAdd
          ((γ : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β v) *
            (frobPow n (γ : Matrix (Fin 2) (Fin 2) F))ᵀ) := by
  obtain ⟨F, _, _, _, hF, π, hR⟩ := hO
  have hπinj := FFModel.RealizesVia.injective_of_faithful (twistTensor_faithful n) hR
  have hπs := hR.1
  obtain ⟨β, hβinj, hβsec, hβe⟩ := exists_beta_of_realizesVia_bot rfl hR
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans
      (MulEquiv.ofBijective π ⟨hπinj, hπs⟩), β, hβinj, fun v => hβsec v,
    fun γ v => hβe _ v⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
