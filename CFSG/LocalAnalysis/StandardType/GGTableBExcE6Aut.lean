module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableBExc

theorem eq_one_of_sq_of_pow_odd {M : Type*} [Monoid M] {x : M} {p : ℕ} (hodd : Odd p)
    (h2 : x ^ 2 = 1) (hp : x ^ p = 1) : x = 1 := by
  obtain ⟨m, rfl⟩ := hodd
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hp
  exact hp

section AutC

variable {K : Type} [Field K]

theorem exactNormalAut_eq_conj_of_mem {b : Fin Tag.E6.rank → Kˣ}
    (hb : rootDiagUnit .E6 b ∈ adjointGroup .E6 K) :
    exactNormalAut .E6 K b 1 0 = MulAut.conj (⟨rootDiagUnit .E6 b, hb⟩ : adjointGroup .E6 K) := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_exactNormalAut, exactQ_zero, AutSt.units_map_entrywiseHom_one, MulAut.conj_apply]
  simp only [inv_one, mul_one, Subgroup.coe_mul, Subgroup.coe_inv]

theorem pow_three_mem_inn_of_eq {α : MulAut (adjointGroup .E6 K)} {g : adjointGroup .E6 K}
    {a : Fin Tag.E6.rank → Kˣ} (hα : α = MulAut.conj g * exactNormalAut .E6 K a 1 0) :
    α ^ 3 ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  have := AutSt.normal_range_conj (S := adjointGroup .E6 K)
  set N := (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range with hN
  have hcube : rootDiagUnit .E6 (a ^ 3) ∈ adjointGroup .E6 K :=
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (rootDiagUnit_cube_mem_torusGroup_E6 a)
  have h3 : exactNormalAut .E6 K a 1 0 ^ 3 = exactNormalAut .E6 K (a ^ 3) 1 0 := by
    change AutSt.e6DiagHom K a ^ 3 = AutSt.e6DiagHom K (a ^ 3)
    rw [map_pow]
  have h1 : ((MulAut.conj g : MulAut (adjointGroup .E6 K)) : MulAut (adjointGroup .E6 K) ⧸ N) =
      1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hα, QuotientGroup.mk_mul, h1, one_mul,
    ← QuotientGroup.mk_pow, h3, exactNormalAut_eq_conj_of_mem hcube, QuotientGroup.eq_one_iff]
  exact ⟨_, rfl⟩

theorem card_le_mul_card_inf_inn_E6 [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {E : Subgroup (MulAut (adjointGroup .E6 K))} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card (E ⊓ (MulAut.conj : adjointGroup .E6 K →*
      MulAut (adjointGroup .E6 K)).range : Subgroup (MulAut (adjointGroup .E6 K))) := by
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have := TableBSymp.finite_mulAut (R := adjointGroup .E6 K)
  obtain ⟨Θ, -, -, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6
    (Or.inl rfl) K
  have hcyc := isCyclic_ringAut K hf hK
  set N := (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range with hN
  set φ : E →* (K ≃+* K) := (MonoidHom.fst _ _).comp (Θ.comp E.subtype) with hφ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : ∀ y : Multiplicative (ZMod (exactE .E6)), y ^ 2 = 1 := by
    have h0 : ∀ z : ZMod 2, z + z = 0 := by decide
    intro y
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
  have hkerN : ∀ e : E, φ e = 1 → (e : MulAut (adjointGroup .E6 K)) ∈ N := by
    intro e he
    have hep : (e : MulAut (adjointGroup .E6 K)) ^ p = 1 := hE.2 _ e.2
    have h2 : (Θ e).2 = 1 := by
      refine eq_one_of_sq_of_pow_odd hodd (hsq _) ?_
      rw [← Prod.pow_snd, ← map_pow, hep, map_one, Prod.snd_one]
    have hΘ1 : Θ e = 1 := Prod.ext he h2
    obtain ⟨g, a, hga⟩ := (hker _).1 hΘ1
    have hα : (e : MulAut (adjointGroup .E6 K)) =
        MulAut.conj g * exactNormalAut .E6 K a 1 0 :=
      eq_conj_mul_exactNormalAut_of_apply (σ := 1) (ε := 0) fun h => by
        rw [hga h, exactQ_zero, AutSt.units_map_entrywiseHom_one, inv_one, mul_one, mul_one]
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) hp.one_lt
    rw [← pow_mul_eq_self_of_mod hk hep, pow_mul]
    exact Subgroup.pow_mem _ (pow_three_mem_inn_of_eq hα) k
  have h1 := TableB.card_range_mul_card_ker φ
  have hrange : Nat.card φ.range ≤ p := by
    have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
    refine TableB.card_le_of_isCyclic hp.pos inferInstance ?_
    rintro _ ⟨e, rfl⟩
    rw [← map_pow, show e ^ p = 1 from Subtype.ext (hE.2 e e.2), map_one]
  have hkerle : Nat.card φ.ker ≤ Nat.card (E ⊓ N : Subgroup (MulAut (adjointGroup .E6 K))) := by
    refine Nat.card_le_card_of_injective
      (fun e => (⟨(e : E), (e : E).2, hkerN e e.2⟩ : (E ⊓ N : Subgroup _))) fun x y hxy => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (E ⊓ N : Subgroup (MulAut (adjointGroup .E6 K))) =>
      (z : MulAut (adjointGroup .E6 K))) hxy
  calc Nat.card E = Nat.card φ.range * Nat.card φ.ker := h1.symm
    _ ≤ p * Nat.card (E ⊓ N : Subgroup (MulAut (adjointGroup .E6 K))) :=
      Nat.mul_le_mul hrange hkerle

theorem card_le_mul_card_inf_inn_recipe_E6 [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {E : Subgroup (MulAut (RecipeGroup .E6 K))} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card (E ⊓ (MulAut.conj : RecipeGroup .E6 K →*
      MulAut (RecipeGroup .E6 K)).range : Subgroup (MulAut (RecipeGroup .E6 K))) := by
  set e := recipeEquiv .E6 K with he
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have h := card_le_mul_card_inf_inn_E6 hf hK hp hp2 hp3
    (E := E.map (MulAut.congr e).toMonoidHom) (TableB.isElemAbelian_map hE _)
  rw [Subgroup.card_map_of_injective hinj, AutSt.range_conj_congr e,
    ← Subgroup.map_inf_eq _ _ _ hinj, Subgroup.card_map_of_injective hinj] at h
  exact h

end AutC

section Diag

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
  {H : Subgroup (LargeEvenChevGL A K)}

theorem isDiagOf_comm {φ ψ : MulAut (LargeEvenCenterQuot H)} {a b : Fin r → Kˣ}
    (hφ : TableB.IsDiagOf H φ a) (hψ : TableB.IsDiagOf H ψ b) : φ * ψ = ψ * φ := by
  have hab : TableB.diagHom A K a * TableB.diagHom A K b =
      TableB.diagHom A K b * TableB.diagHom A K a := by
    rw [← map_mul, ← map_mul, mul_comm]
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    show φ (ψ (LargeEvenCenterMk H h)) = ψ (φ (LargeEvenCenterMk H h))
    rw [hψ.2 h (hψ.1 h h.2), hφ.2 h (hφ.1 h h.2),
      hφ.2 ⟨_, hψ.1 h h.2⟩ (hφ.1 _ (hψ.1 h h.2)), hψ.2 ⟨_, hφ.1 h h.2⟩ (hψ.1 _ (hφ.1 h h.2))]
    congr 1
    apply Subtype.ext
    show TableB.diagHom A K a * (TableB.diagHom A K b * h * (TableB.diagHom A K b)⁻¹) *
        (TableB.diagHom A K a)⁻¹ =
      TableB.diagHom A K b * (TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹) *
        (TableB.diagHom A K b)⁻¹
    calc TableB.diagHom A K a * (TableB.diagHom A K b * h * (TableB.diagHom A K b)⁻¹) *
          (TableB.diagHom A K a)⁻¹ =
        (TableB.diagHom A K a * TableB.diagHom A K b) * h *
          (TableB.diagHom A K a * TableB.diagHom A K b)⁻¹ := by group
      _ = (TableB.diagHom A K b * TableB.diagHom A K a) * h *
          (TableB.diagHom A K b * TableB.diagHom A K a)⁻¹ := by rw [hab]
      _ = _ := by group

end Diag

section DiagE6

variable {K : Type} [Field K]

theorem pow_three_mem_torusSubgroup_E6 (a : Fin Tag.E6.rank → Kˣ) :
    a ^ 3 ∈ TableB.torusSubgroup Tag.E6.cartan K := by
  rw [← Finset.univ_prod_mulSingle (a ^ 3)]
  refine Subgroup.prod_mem _ fun j _ => ?_
  have h := TableB.mulSingle_pow_mem_torusSubgroup (LargeEvenCartanE 6) K TableB.cartanE6_adj j
    (a j)
  rw [zpow_natCast] at h
  exact h

theorem diag_pow_three_mem_inn {φ : MulAut (RecipeGroup .E6 K)} {a : Fin Tag.E6.rank → Kˣ}
    (hφ : TableB.IsDiagOf (LargeEvenChevH Tag.E6.cartan K false) φ a) :
    φ ^ 3 ∈ (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)).range := by
  have hmem : TableB.diagHom Tag.E6.cartan K (a ^ 3) ∈ LargeEvenChevH Tag.E6.cartan K false :=
    TableB.diagHom_mem_of_mem_torusSubgroup .E6 K (pow_three_mem_torusSubgroup_E6 a)
  rw [TableB.isDiagOf_eq_conj (TableB.isDiagOf_pow hφ 3) hmem]
  exact ⟨_, rfl⟩

theorem pow_three_mem_inn_of_mem_recipeID_E6 {φ : MulAut (RecipeGroup .E6 K)}
    (hφ : φ ∈ RecipeID .E6 K) :
    φ ^ 3 ∈ (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)).range := by
  set N := (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)).range with hN
  set π := QuotientGroup.mk' N with hπ
  set S : Set (MulAut (RecipeGroup .E6 K) ⧸ N) :=
    π '' LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false) with hS
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨φ₁, h₁, rfl⟩ _ ⟨φ₂, h₂, rfl⟩
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf h₁
    obtain ⟨b, hb⟩ := TableB.exists_isDiagOf h₂
    change π φ₁ * π φ₂ = π φ₂ * π φ₁
    rw [← map_mul, ← map_mul, isDiagOf_comm ha hb]
  have hcube : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨φ₁, h₁, rfl⟩
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf h₁
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact diag_pow_three_mem_inn ha
  have hcS : ∀ x ∈ Subgroup.closure S, ∀ s ∈ S, Commute x s := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact fun s hs => hcomm y hy s hs
    | one => exact fun s _ => Commute.one_left s
    | mul y z _ _ hy hz => exact fun s hs => (hy s hs).mul_left (hz s hs)
    | inv y _ hy => exact fun s hs => (hy s hs).inv_left
  have hcC : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact hcS x hx z hz
    | one => exact Commute.one_right x
    | mul z w _ _ hz hw => exact hz.mul_right hw
    | inv z _ hz => exact hz.inv_right
  have hC : ∀ x ∈ Subgroup.closure S, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hcube y hy
    | one => exact one_pow 3
    | mul y z hy' hz' hy hz => rw [(hcC y hy' z hz').mul_pow, hy, hz, one_mul]
    | inv y _ hy => rw [inv_pow, hy, inv_one]
  have hle : Subgroup.closure (LargeEvenInnSet (RecipeGroup .E6 K) ∪
      LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) ≤
      (Subgroup.closure S).comap π := by
    rw [Subgroup.closure_le]
    rintro ψ (⟨x, rfl⟩ | hψ)
    · show π (MulAut.conj x) ∈ Subgroup.closure S
      have hx : MulAut.conj x ∈ N := ⟨x, rfl⟩
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hx]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨ψ, hψ, rfl⟩
  have h1 := hC _ (hle hφ)
  rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem ggOutdiagPrime_E6 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    GGOutdiagPrime p (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  intro φ hφ hφp
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) hp.one_lt
  rw [← pow_mul_eq_self_of_mod hk hφp, pow_mul]
  exact Subgroup.pow_mem _ (pow_three_mem_inn_of_mem_recipeID_E6 hφ) k

end DiagE6

end TableBExc

end CFSG.StandardType
