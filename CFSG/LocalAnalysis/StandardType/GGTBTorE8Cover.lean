module

public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.Steinberg.CentralExt.E8Even
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem exists_e8_model_of_tableB {K : Type} [Field K] [Finite K] [CharP K 2]
    {p r : ℕ} {L : Type} [Group L] [Finite L]
    (ψ : L →* TableBExc.RecipeGroup .E8 K) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (TableBExc.RecipeGroup .E8 K)
      (TableBExc.RecipeID .E8 K) L ψ A) :
    ∃ e : L ≃* adjointGroup .E8 K,
      (∀ l, e l = TableBExc.recipeEquiv .E8 K (ψ l)) ∧
      ∃ E : Subgroup (adjointGroup .E8 K), IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
        (∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) ∧
        A.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) := by
  obtain ⟨hψ, hker, hperf, hA, hAI, -, -, hSC⟩ := hTB
  have : Group.IsPerfect L := ⟨hperf⟩
  let π : L →* adjointGroup .E8 K := (TableBExc.recipeEquiv .E8 K).toMonoidHom.comp ψ
  have hπ : Function.Surjective π := (TableBExc.recipeEquiv .E8 K).surjective.comp hψ
  have hπker : π.ker ≤ Subgroup.center L := by
    simpa only [π, MonoidHom.ker_comp_of_injective ψ
      (TableBExc.recipeEquiv .E8 K).toMonoidHom (TableBExc.recipeEquiv .E8 K).injective]
      using hker
  let e : L ≃* adjointGroup .E8 K := MulEquiv.ofBijective π
    (CFSG.LieType.Steinberg.CentralExt.e8_even_bijective_of_perfect π hπ hπker)
  let B : Subgroup (MulAut (adjointGroup .E8 K)) := A.map (MulAut.congr e).toMonoidHom
  let j : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K) := MulAut.conj
  have hj : Function.Injective j := mulAut_conj_injective_adjointGroup
  have hBinn : B ≤ j.range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφeq⟩ := hAI a ha
    obtain ⟨x, rfl⟩ := TableBExc.idImage_subset_inn_E8 K hφ
    refine ⟨TableBExc.recipeEquiv .E8 K x, ?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := e.surjective y
    have heq : ∀ l, e l = TableBExc.recipeEquiv .E8 K (ψ l) := fun _ => rfl
    change MulAut.conj (TableBExc.recipeEquiv .E8 K x) (e l) = MulAut.congr e a (e l)
    rw [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    change (TableBExc.recipeEquiv .E8 K x) * e l *
      (TableBExc.recipeEquiv .E8 K x)⁻¹ = e (a l)
    rw [heq, heq]
    simp only [← map_inv, ← map_mul]
    exact congrArg (TableBExc.recipeEquiv .E8 K) (hφeq l)
  let E : Subgroup (adjointGroup .E8 K) := B.comap j
  have hEB : E.map j = B := by
    exact Subgroup.map_comap_eq_self hBinn
  have hB : IsElemAbelian p B := TableB.isElemAbelian_map hA _
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hj ?_)⟩⟩, fun x hx => hj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hB x.2 y.2
    · rw [map_pow, map_one]
      exact hB.2 _ hx
  have hcard : Nat.card E = Nat.card A := by
    rw [← Subgroup.card_map_of_injective hj, hEB, Subgroup.card_map_of_injective
      (MulAut.congr e).injective]
  have hESC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) →
      g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hn3 : (e.symm g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have hfix : ∀ a ∈ A, a (e.symm g) = e.symm g := by
      intro a ha
      obtain ⟨x, hx⟩ := hBinn (Subgroup.mem_map_of_mem _ ha)
      have hxE : x ∈ E := by
        change j x ∈ B
        exact hx ▸ Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom ha
      apply e.injective
      have hax : MulAut.congr e a g = x * g * x⁻¹ := by
        exact (congrArg (fun f : MulAut (adjointGroup .E8 K) => f g) hx).symm
      have hconj : x * g * x⁻¹ = g := by rw [← hg x hxE, mul_inv_cancel_right]
      simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hax.trans hconj
    have hmem := hSC (e.symm g) hfix hn3
    change j g ∈ B
    have h := Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hmem
    change MulAut.congr e (MulAut.conj (e.symm g)) ∈ B at h
    simpa only [congr_conj, MulEquiv.apply_symm_apply] using h
  exact ⟨e, fun _ => rfl, E, hE, hcard, hESC, hEB.symm⟩

theorem exists_e8_model_of_tbGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} {L : Type} [Group L] [Finite L]
    (ψ : L →* TableBExc.RecipeGroup .E8 K) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup 3 r (TableBExc.RecipeGroup .E8 K)
      (TableBExc.RecipeID .E8 K) L ψ A) :
    ∃ e : L ≃* adjointGroup .E8 K,
      (∀ l, e l = TableBExc.recipeEquiv .E8 K (ψ l)) ∧
      ∃ E : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E ∧ Nat.card E = Nat.card A ∧
        (∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ 3 = 1 → g ∈ E) ∧
        A.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) := by
  exact exists_e8_model_of_tableB ψ A hTB

theorem torData_of_e8_model {K : Type} [Field K] [Finite K]
    {L : Type} [Group L] (e : L ≃* adjointGroup .E8 K)
    {A : Subgroup (MulAut L)} {E : Subgroup (adjointGroup .E8 K)}
    (hA : A.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)))
    {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (h : GGTorusTorData m N C M (adjointGroup .E8 K)
      (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)))) :
    GGTorusTorData m N C M L A := by
  have hback : (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))).map
      (MulAut.congr e.symm).toMonoidHom = A := by
    rw [← hA, Subgroup.map_map]
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomp, Subgroup.map_id]
  exact h.transport_eq e.symm hback.symm

end CFSG.StandardType
