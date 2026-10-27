module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGIntCartan.eq_of_le_three {Λ : Type} {M : CoxeterMatrix Λ}
    {C C' : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) (hC' : GGIntCartan M C')
    (hM : ∀ i j, i ≠ j → M i j ≤ 3) : C = C' := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [hC.1, hC'.1]
  · exact ((hC.pair hC' hij).2 (hM i j hij)).1

theorem five_le_card_range_of_cartan_E6
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 6 → MulAut ↥Bs) (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hφ : ∀ i, φ i ∈ ggAutomizer X Bs)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A := (ggGamma X hN).range
  let F : V →ₗ[ZMod 3] (Fin 6 → ZMod 3) := LinearMap.pi α
  have hF : ∀ v i, F v i = α i v := fun _ _ => rfl
  have hhi : ∀ i, h i ≠ 0 := by
    intro i hi
    have he := hpair i i
    have htwo : CartanMatrix.E 6 i i = 2 := by fin_cases i <;> decide
    rw [hi, map_zero, htwo] at he
    have he' : ((2 : ℕ) : ZMod 3) = 0 := he.symm
    have hdvd : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp he'
    omega
  have hk : ∀ b : Bs, ggGamma X hN b = 1 → F (ι (Additive.ofMul b)) = 0 := by
    intro b hb
    have hbC := (ggGamma_eq_one_iff X hN b).mp hb
    funext i
    obtain ⟨g, hgX, hgN, heq⟩ := eq_ggConjAut_of_mem_ggAutomizer (hφ i)
    have hfix : φ i b = b := by
      rw [heq]
      apply Subtype.ext
      rw [ggConjAut_apply, Subgroup.mem_centralizer_iff.mp hbC g hgX, mul_inv_cancel_right]
    have he := hlin i (ι (Additive.ofMul b))
    rw [ggLin_apply_ofMul, hfix] at he
    have hsmul : α i (ι (Additive.ofMul b)) • h i = 0 := by
      have he' := sub_eq_self.mp he.symm
      exact he'
    exact (smul_eq_zero.mp hsmul).resolve_right (hhi i)
  let β : Bs →* Multiplicative (Fin 6 → ZMod 3) :=
    { toFun := fun b => Multiplicative.ofAdd (F (ι (Additive.ofMul b)))
      map_one' := by simp
      map_mul' := fun b c => by change Multiplicative.ofAdd (F (ι
        (Additive.ofMul b + Additive.ofMul c))) = _; rw [map_add, map_add]; rfl }
  have hker : (ggGamma X hN).rangeRestrict.ker ≤ β.ker := by
    intro b hb
    have hb' : ggGamma X hN b = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hb)
    exact MonoidHom.mem_ker.mpr (congrArg Multiplicative.ofAdd (hk b hb'))
  let δ : A →* Multiplicative (Fin 6 → ZMod 3) :=
    MonoidHom.liftOfSurjective (ggGamma X hN).rangeRestrict
      (ggGamma X hN).rangeRestrict_surjective ⟨β, hker⟩
  have hδ : ∀ b : Bs, δ ((ggGamma X hN).rangeRestrict b) = β b := by
    intro b
    change (MonoidHom.liftOfSurjective _ _ ⟨β, hker⟩) _ = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  have hMem : ∀ a : A, Multiplicative.toAdd (δ a) ∈ F.range := by
    intro a
    obtain ⟨b, hb⟩ := (ggGamma X hN).rangeRestrict_surjective a
    refine ⟨ι (Additive.ofMul b), ?_⟩
    rw [← hb, hδ]
    rfl
  let f : A → F.range := fun a => ⟨Multiplicative.toAdd (δ a), hMem a⟩
  have hSurj : Function.Surjective f := by
    rintro ⟨v, u, rfl⟩
    let b : Bs := Additive.toMul (ι.symm u)
    refine ⟨(ggGamma X hN).rangeRestrict b, ?_⟩
    apply Subtype.ext
    change Multiplicative.toAdd (δ ((ggGamma X hN).rangeRestrict b)) = F u
    rw [hδ]
    change F (ι (ι.symm u)) = F u
    rw [AddEquiv.apply_symm_apply]
  have hCard : Nat.card F.range ≤ Nat.card A := Nat.card_le_card_of_surjective _ hSurj
  let h' : Fin 6 → F.range := fun j => ⟨F (h j), ⟨h j, rfl⟩⟩
  let α' : Fin 6 → Module.Dual (ZMod 3) F.range :=
    fun i => (LinearMap.proj i).comp F.range.subtype
  have hp' : ∀ i j, α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := hpair
  have hfr := E6QTwo.five_le_finrank_span hp'
  have hdim : 5 ≤ Module.finrank (ZMod 3) F.range :=
    hfr.trans (Submodule.finrank_le _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hPow : 3 ^ 5 ≤ Nat.card F.range := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 F.range]
    exact Nat.pow_le_pow_right (by norm_num) hdim
  exact hPow.trans hCard

theorem five_le_card_range_of_e6_datum
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hC : GGIntCartan M C) (hE6 : GGIsTypeE6 M)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hφ : ∀ i, φ i ∈ ggAutomizer X Bs) :
    3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
  obtain ⟨e, hMeq⟩ := hE6
  have hCe : GGIntCartan M (Matrix.reindex e e (CartanMatrix.E 6)) := by
    rw [hMeq]
    exact GGIntCartan.reindex e ggIntCartan_E₆
  have hM3 : ∀ i j : Λ, i ≠ j → M i j ≤ 3 := by
    intro i j hij
    rw [hMeq, CoxeterMatrix.reindex_apply]
    have he : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    generalize e.symm i = a at he ⊢
    generalize e.symm j = b at he ⊢
    fin_cases a <;> fin_cases b <;> decide
  have hCeq : C = Matrix.reindex e e (CartanMatrix.E 6) := hC.eq_of_le_three hCe hM3
  refine five_le_card_range_of_cartan_E6 hN ι (fun i => φ (e i)) (fun i => h (e i))
    (fun i => α (e i)) (fun i => hφ (e i)) (fun i => hlin (e i)) ?_
  intro i j
  rw [hpair, hCeq]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem GGResE6DepShape.five_le_card_range
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L J K X : Subgroup G}
    (hS : GGResE6DepShape p Bs L J K) (hX : X = L ∨ X = K)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
  have hp3 : p = 3 := hS.1
  subst hp3
  obtain ⟨Λ, _, _, b, ML, CL, MK, CK, V, _, _, ι, φ, h, α,
    hWL, hCL, hWK, hCK, hTypes, hLin, _, hPairL, hPairK, _, hFL, hFK, _, _, _, _⟩ := hS.2.2
  rcases hX with hX | hX
  · subst X
    obtain ⟨fL, hfL⟩ := hFL
    refine five_le_card_range_of_e6_datum (Λ := Λ) (M := ML) (C := CL) (V := V)
      hN ι (fun i => φ (some i)) (fun i => h (some i))
      (fun i => α (some i)) hCL hTypes.1 (fun i => hLin (some i)) hPairL ?_
    intro i
    rw [← hfL i]
    exact (fL (ML.simple i)).2
  · subst X
    obtain ⟨fK, hfK⟩ := hFK
    refine five_le_card_range_of_e6_datum (Λ := Option {i : Λ // i ≠ b}) (M := MK) (C := CK)
      (V := V) hN ι (fun i : Option {i : Λ // i ≠ b} => φ (i.map Subtype.val))
      (fun i => h (i.map Subtype.val)) (fun i => α (i.map Subtype.val)) hCK hTypes.2
      (fun i => hLin (i.map Subtype.val)) hPairK ?_
    intro i
    rw [← hfK i]
    exact (fK (MK.simple i)).2

end CFSG.StandardType
