module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepCore
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGIntCartan.cast_pair_ne_zero_of_bond {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) {Γ : Type} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {i j : Γ} (hij : i ≠ j) (hM : M.M i j ≠ 2) :
    (C i j : ZMod p) ≠ 0 ∧ (C j i : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 (by omega)
  rcases hC.entries hij with ⟨hm, _, _⟩ | ⟨_, h1, h2'⟩ |
    ⟨_, ⟨h1, h2'⟩ | ⟨h1, h2'⟩⟩ | ⟨_, ⟨h1, h2'⟩ | ⟨h1, h2'⟩⟩
  · exact (hM hm).elim
  all_goals rw [h1, h2']; simp [h2, h3]

theorem ggJoint_pairing_connected {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    [Nonempty {i : Λ // i ≠ b₁ ∧ i ≠ b₂}]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    (hWML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (hpairL : ∀ i j, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hpairK : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (i.map Subtype.val id) (h (j.map Subtype.val id)) = (CK i j : ZMod p)) :
    ∀ i j, Relation.ReflTransGen
      (fun a b : Λ ⊕ Λa => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j := by
  classical
  let j₀ : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} := Classical.choice inferInstance
  let R := fun a b : Λ ⊕ Λa => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0
  have hL : ∀ i j : Λ, Relation.ReflTransGen R (Sum.inl i) (Sum.inl j) := by
    intro i j
    induction ggRC_weyl_connected hWML i j with
    | refl => exact Relation.ReflTransGen.refl
    | tail hpath he ih =>
        apply ih.tail
        dsimp only [R]
        rw [hpairL, hpairL]
        exact hCL.cast_pair_ne_zero_of_bond hp he.1 he.2
  have hK : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      Relation.ReflTransGen R (i.map Subtype.val id) (j.map Subtype.val id) := by
    intro i j
    induction ggRC_weyl_connected hWMK i j with
    | refl => exact Relation.ReflTransGen.refl
    | tail hpath he ih =>
        apply ih.tail
        dsimp only [R]
        rw [hpairK, hpairK]
        exact hCK.cast_pair_ne_zero_of_bond hp he.1 he.2
  have hto : ∀ o : Λ ⊕ Λa, Relation.ReflTransGen R o (Sum.inl j₀.1) := by
    intro o
    cases o with
    | inl i => exact hL i j₀.1
    | inr a => exact hK (Sum.inr a) (Sum.inl j₀)
  have hfrom : ∀ o : Λ ⊕ Λa, Relation.ReflTransGen R (Sum.inl j₀.1) o := by
    intro o
    cases o with
    | inl i => exact hL j₀.1 i
    | inr a => exact hK (Sum.inl j₀) (Sum.inr a)
  intro i j
  exact (hto i).trans (hfrom j)

theorem ggJoint_span_eq_top_of_added_not_mem {p N : ℕ} [Fact p.Prime]
    (hN : 1 ≤ N) {Λ : Type} [Fintype Λ] {Λa : Type}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (e : Fin (N - 1) ≃ Λ) (h : Λ ⊕ Λa → V)
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGIndepAFrame p N (fun i => h (Sum.inl (e i))) α x)
    (ha : ∃ a : Λa, h (Sum.inr a) ∉
      Submodule.span (ZMod p) (Set.range fun i => h (Sum.inl i))) :
    Module.finrank (ZMod p) V = N ∧
      Submodule.span (ZMod p) (Set.range h) = ⊤ := by
  let H : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) (Set.range fun i : Λ => h (Sum.inl i))
  let U : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  have hind : LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) := by
    have hh := F.indep.comp e.symm e.symm.injective
    change LinearIndependent (ZMod p)
      (fun i : Λ => h (Sum.inl (e (e.symm i)))) at hh
    simpa only [Equiv.apply_symm_apply] using hh
  have hHdim : Module.finrank (ZMod p) H = N - 1 := by
    have hf := finrank_span_eq_card hind
    have hc : Fintype.card Λ = N - 1 := by
      simpa using (Fintype.card_congr e).symm
    exact hf.trans hc
  have hHU : H ≤ U := Submodule.span_mono (by
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩)
  have hlt : H < U := by
    obtain ⟨a, ha⟩ := ha
    refine lt_of_le_of_ne hHU ?_
    intro heq
    have hmem : h (Sum.inr a) ∈ U :=
      Submodule.subset_span (Set.mem_range_self (Sum.inr a))
    change h (Sum.inr a) ∉ H at ha
    apply ha
    rwa [heq]
  have hdimlt := Submodule.finrank_lt_finrank_of_lt hlt
  have hdimle := U.finrank_le
  have hVN := ggIndepFrame_finrank_le hN F
  have hVeq : Module.finrank (ZMod p) V = N := by omega
  refine ⟨hVeq, Submodule.eq_top_of_finrank_eq ?_⟩
  change Module.finrank (ZMod p) U = Module.finrank (ZMod p) V
  omega

theorem ggJoint_absIrred_of_added_not_mem {p N : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hN : 1 ≤ N)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    [Nonempty {i : Λ // i ≠ b₁ ∧ i ≠ b₂}]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    (hWML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (e : Fin (N - 1) ≃ Λ) (g : Λ ⊕ Λa → (V ≃ₗ[ZMod p] V))
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, g i w = w - α i w • h i)
    (hpairL : ∀ i j, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hpairK : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (i.map Subtype.val id) (h (j.map Subtype.val id)) = (CK i j : ZMod p))
    {x : V} (F : GGIndepAFrame p N (fun i => h (Sum.inl (e i)))
      (fun i => α (Sum.inl (e i))) x)
    (hmove : ∃ a : Λa, α (Sum.inr a) x ≠ 0)
    (ha : ∃ a : Λa, h (Sum.inr a) ∉
      Submodule.span (ZMod p) (Set.range fun i => h (Sum.inl i))) :
    Module.finrank (ZMod p) V = N ∧
      ZS.AbsIrred p (Subgroup.closure (Set.range g)) := by
  obtain ⟨hV, hspan⟩ := ggJoint_span_eq_top_of_added_not_mem hN e h F ha
  refine ⟨hV, ggRC_absIrred_of_connected (by omega) g h α hlin ?_ hspan ?_
    (ggJoint_pairing_connected hp hWML hCL hWMK hCK h α hpairL hpairK) _ rfl⟩
  · intro i
    cases i with
    | inl i => rw [hpairL i i, hCL.1]; norm_num
    | inr a => simpa using (hpairK (Sum.inr a) (Sum.inr a)).trans (by rw [hCK.1]; norm_num)
  · intro w hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (F.fix w fun i => hw (Sum.inl (e i)))
    obtain ⟨a, ha⟩ := hmove
    have hz := hw (Sum.inr a)
    rw [← hc, map_smul, smul_eq_mul] at hz
    have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_right ha
    rw [← hc, hc0, zero_smul]

end CFSG.StandardType

end
