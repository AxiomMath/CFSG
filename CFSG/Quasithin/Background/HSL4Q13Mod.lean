module

public import CFSG.Quasithin.Background.HSL4Q13Fix
public import CFSG.Quasithin.Background.F918F1
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block

public section

namespace CFSG.Quasithin.H.Q13

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall

theorem det_sc (k : Fin 4) : (sc k).det = 1 := by
  revert k
  decide +kernel

@[expose] def scSL (k : Fin 4) : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨sc k, det_sc k⟩

theorem sci_mul_sc (k : Fin 4) : sci k * sc k = 1 := mul_eq_one_comm.1 (sc_mul_sci k)

theorem coe_scSL_inv (k : Fin 4) :
    (((scSL k)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      sci k := by
  have h1 : sc k * (((scSL k)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    have := congrArg (fun A : SpecialLinearGroup (Fin 4) (ZMod 2) =>
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2))) (mul_inv_cancel (scSL k))
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
    exact this
  calc (((scSL k)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
      = (sci k * sc k) * (((scSL k)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) := by rw [sci_mul_sc, one_mul]
    _ = sci k := by rw [mul_assoc, h1, mul_one]

theorem card_fix_conj_le {n : ℕ} {P P' : Matrix (Fin n) (Fin n) (ZMod 2)} (hPP : P * P' = 1)
    (hP'P : P' * P = 1) {S : Fin 4 → Matrix (Fin n) (Fin n) (ZMod 2)} {N : ℕ}
    (hN : (Finset.univ.filter fun v : Fin n → ZMod 2 => ∀ k, S k *ᵥ v = v).card ≤ N) :
    Nat.card {v : Fin n → ZMod 2 // ∀ k, (P * S k * P') *ᵥ v = v} ≤ N := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine le_trans (Finset.card_le_card_of_injOn (fun v => P' *ᵥ v) ?_ ?_) hN
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    intro k
    have h1 := congrArg (fun w => P' *ᵥ w) (hv k)
    simp only [mulVec_mulVec] at h1
    rw [show P' * (P * S k * P') = S k * P' by
      rw [← mul_assoc, ← mul_assoc, hP'P, one_mul]] at h1
    rw [mulVec_mulVec]
    exact h1
  · intro v _ w _ h
    have h1 := congrArg (fun x => P *ᵥ x) h
    simp only [mulVec_mulVec, hPP, one_mulVec] at h1
    exact h1

section Gam

variable {V : Type*} [CommGroup V] {Ks : Subgroup (MulAut V)}

@[expose] def HasMat (γ : ↥(StatedSL 4 (ZMod 2))) (M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    Prop :=
  ((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M ∧
    (((γ⁻¹ : ↥(StatedSL 4 (ZMod 2))) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M'

theorem exists_gam [Finite ↥Ks] (θc : ↥Ks ≃* SpecialLinearGroup (Fin 4) (ZMod 2))
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥Ks} (hπ : Function.Surjective π) :
    ∃ γ : Fin 4 → ↥(StatedSL 4 (ZMod 2)), (∀ k, π (γ k) = θc.symm (scSL k)) ∧
      ∃ A : GL (Fin 4) (ZMod 2),
        (∀ k, HasMat (γ k) ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) * sc k *
            ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))
          ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) * sci k *
            ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))) ∨
        (∀ k, HasMat (γ k) ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (sci k)ᵀ *
            ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))
          ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (sc k)ᵀ *
            ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))) := by
  set e₄ := specialLinearGroupEquivStatedSL 4 (ZMod 2) with he₄
  set σ : SpecialLinearGroup (Fin 4) (ZMod 2) →* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    θc.toMonoidHom.comp (π.comp e₄.toMonoidHom) with hσ
  have hσs : Function.Surjective σ :=
    θc.surjective.comp (hπ.comp e₄.surjective)
  have hσi : Function.Injective σ := Finite.injective_iff_surjective.2 hσs
  set σe := MulEquiv.ofBijective σ ⟨hσi, hσs⟩ with hσe
  set τ := σe.symm with hτ
  refine ⟨fun k => e₄ (τ (scSL k)), fun k => ?_, ?_⟩
  · apply θc.injective
    rw [MulEquiv.apply_symm_apply]
    exact σe.apply_symm_apply (scSL k)
  obtain ⟨A, σ', h⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl
    (by norm_num : 3 ≤ 4) τ
  have hσ' : ∀ c : ZMod 2, σ' c = c := by
    intro c
    fin_cases c
    · exact map_zero σ'
    · exact map_one σ'
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2), M.map σ' = M := fun M => by
    ext r c
    simp [hσ']
  have hinv : ∀ k, (scSL k)⁻¹ * scSL k = 1 := fun k => inv_mul_cancel _
  refine ⟨A, ?_⟩
  rcases h with h | h
  · left
    intro k
    refine ⟨?_, ?_⟩
    · rw [specialLinearGroupEquivStatedSL_coe, h, hmap]
      rfl
    · rw [← map_inv, ← map_inv, specialLinearGroupEquivStatedSL_coe, h, hmap,
        coe_scSL_inv]
  · right
    intro k
    refine ⟨?_, ?_⟩
    · rw [specialLinearGroupEquivStatedSL_coe, h, hmap, coe_scSL_inv]
    · rw [← map_inv, ← map_inv, specialLinearGroupEquivStatedSL_coe, h, hmap, inv_inv]
      rfl

end Gam

section Card

variable {V : Type} [CommGroup V] {Ks : Subgroup (MulAut V)}

theorem card_le_of_fix {U Z F : Subgroup V} (hFU : F ≤ U) (hFZ : F ⊓ Z = ⊥) {A : Type*}
    [Group A] [Finite A] (β : ↥U →* A) (hβ : ∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) (P : A → Prop)
    (hP : ∀ u : ↥U, (u : V) ∈ F → P (β u)) : Nat.card ↥F ≤ Nat.card {a : A // P a} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨β ⟨x, hFU x.2⟩, hP _ x.2⟩) fun x y hxy => ?_
  have h1 : β ⟨x, hFU x.2⟩ = β ⟨y, hFU y.2⟩ := congrArg Subtype.val hxy
  have h2 : β (⟨x, hFU x.2⟩⁻¹ * ⟨y, hFU y.2⟩) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 : ((x : V))⁻¹ * y ∈ F ⊓ Z := ⟨F.mul_mem (F.inv_mem x.2) y.2, (hβ _).1 h2⟩
  rw [hFZ, Subgroup.mem_bot, inv_mul_eq_one] at h3
  exact Subtype.ext h3

variable [Finite ↥Ks]

theorem card_le_nat (θc : ↥Ks ≃* SpecialLinearGroup (Fin 4) (ZMod 2))
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥Ks} {U Z F : Subgroup V}
    (h : (FFModel.nat (StatedSL 4 (ZMod 2))).RealizesVia Ks U Z π) (hFU : F ≤ U)
    (hFZ : F ⊓ Z = ⊥) (hF : ∀ k, ∀ u ∈ F, ((θc.symm (scSL k) : ↥Ks) : MulAut V) u = u) :
    Nat.card ↥F ≤ 2 := by
  obtain ⟨γ, hγ, A, hA⟩ := exists_gam θc h.1
  obtain ⟨β₀, -, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl h
  set β : ↥U →* Multiplicative (Fin 4 → ZMod 2) := β₀ with hβ
  have hP : ∀ u : ↥U, (u : V) ∈ F → ∀ k, natAct (StatedSL 4 (ZMod 2)) (γ k) (β u) = β u := by
    intro u hu k
    have hfix : ((π (γ k) : ↥Ks) : MulAut V) (u : V) = u := by rw [hγ k]; exact hF k u hu
    have hu' : ((π (γ k) : ↥Ks) : MulAut V) (u : V) ∈ U := by rw [hfix]; exact u.2
    have e := hβe (γ k) u hu'
    have e2 : β ⟨((π (γ k) : ↥Ks) : MulAut V) (u : V), hu'⟩ = β u :=
      congrArg β (Subtype.ext hfix)
    exact e.symm.trans e2
  calc Nat.card ↥F ≤ Nat.card {a : Multiplicative (Fin 4 → ZMod 2) //
        ∀ k, natAct (StatedSL 4 (ZMod 2)) (γ k) a = a} := card_le_of_fix hFU hFZ β hβk _ hP
    _ = Nat.card {v : Fin 4 → ZMod 2 //
        ∀ k, (((γ k : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) *ᵥ v = v} :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun a => by
        simp only [natAct]
        exact forall_congr' fun k => ⟨fun h => by simpa using congrArg Multiplicative.toAdd h,
          fun h => by rw [h]; rfl⟩)
    _ ≤ 2 := by
      rcases hA with hA | hA
      · simp_rw [fun k => (hA k).1]
        exact card_fix_conj_le A.mul_inv A.inv_mul card_fix_nat
      · simp_rw [fun k => (hA k).1]
        exact card_fix_conj_le A.mul_inv A.inv_mul card_fix_dual

theorem card_le_dual (θc : ↥Ks ≃* SpecialLinearGroup (Fin 4) (ZMod 2))
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥Ks} {U Z F : Subgroup V}
    (h : (FFModel.dualNat (StatedSL 4 (ZMod 2))).RealizesVia Ks U Z π) (hFU : F ≤ U)
    (hFZ : F ⊓ Z = ⊥) (hF : ∀ k, ∀ u ∈ F, ((θc.symm (scSL k) : ↥Ks) : MulAut V) u = u) :
    Nat.card ↥F ≤ 2 := by
  obtain ⟨γ, hγ, A, hA⟩ := exists_gam θc h.1
  obtain ⟨β₀, -, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl h
  set β : ↥U →* Multiplicative (Fin 4 → ZMod 2) := β₀ with hβ
  have hP : ∀ u : ↥U, (u : V) ∈ F → ∀ k, dualNatAct (StatedSL 4 (ZMod 2)) (γ k) (β u) = β u := by
    intro u hu k
    have hfix : ((π (γ k) : ↥Ks) : MulAut V) (u : V) = u := by rw [hγ k]; exact hF k u hu
    have hu' : ((π (γ k) : ↥Ks) : MulAut V) (u : V) ∈ U := by rw [hfix]; exact u.2
    have e := hβe (γ k) u hu'
    have e2 : β ⟨((π (γ k) : ↥Ks) : MulAut V) (u : V), hu'⟩ = β u :=
      congrArg β (Subtype.ext hfix)
    exact e.symm.trans e2
  have hT : ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2),
      ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) * M *
        ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ =
      (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ * Mᵀ *
        ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ := fun M => by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, mul_assoc]
  have h1 : ((((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ *
      ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ) = 1 := by
    rw [← Matrix.transpose_mul, A.mul_inv, Matrix.transpose_one]
  have h2 : (((A : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ *
      (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ) = 1 := by
    rw [← Matrix.transpose_mul, A.inv_mul, Matrix.transpose_one]
  calc Nat.card ↥F ≤ Nat.card {a : Multiplicative (Fin 4 → ZMod 2) //
        ∀ k, dualNatAct (StatedSL 4 (ZMod 2)) (γ k) a = a} := card_le_of_fix hFU hFZ β hβk _ hP
    _ = Nat.card {v : Fin 4 → ZMod 2 // ∀ k, ((((γ k)⁻¹ : ↥(StatedSL 4 (ZMod 2))) :
        GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ v = v} :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun a => by
        simp only [dualNatAct]
        exact forall_congr' fun k => ⟨fun h => by simpa using congrArg Multiplicative.toAdd h,
          fun h => by rw [h]; rfl⟩)
    _ ≤ 2 := by
      rcases hA with hA | hA
      · simp_rw [fun k => (hA k).2, hT]
        exact card_fix_conj_le h1 h2 card_fix_dual
      · simp_rw [fun k => (hA k).2, hT, Matrix.transpose_transpose]
        exact card_fix_conj_le h1 h2 card_fix_nat

theorem card_le_wedge (θc : ↥Ks ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) {U Z F : Subgroup V}
    (h : SLExteriorTwo Ks U Z 4) (hFU : F ≤ U) (hFZ : F ⊓ Z = ⊥)
    (hF : ∀ k, ∀ u ∈ F, ((θc.symm (scSL k) : ↥Ks) : MulAut V) u = u) : Nat.card ↥F ≤ 4 := by
  obtain ⟨π, β, hπs, -, -, -, hβk, hβe⟩ := sl4ExteriorTwo_coord h
  obtain ⟨γ, hγ, A, hA⟩ := exists_gam θc hπs
  have hP : ∀ u : ↥U, (u : V) ∈ F → ∀ k,
      Multiplicative.ofAdd (wedgeRep4 (γ k) (Multiplicative.toAdd (β u))) = β u := by
    intro u hu k
    have hfix : ((π (γ k) : ↥Ks) : MulAut V) (u : V) = u := by rw [hγ k]; exact hF k u hu
    have hu' : ((π (γ k) : ↥Ks) : MulAut V) (u : V) ∈ U := by rw [hfix]; exact u.2
    have e := hβe (γ k) u hu'
    have e2 : β ⟨((π (γ k) : ↥Ks) : MulAut V) (u : V), hu'⟩ = β u :=
      congrArg β (Subtype.ext hfix)
    exact e.symm.trans e2
  have hW : ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2),
      wedgeMat4 ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) * M *
        ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) =
      wedgeMat4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) * wedgeMat4 M *
        wedgeMat4 ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := fun M => by
    rw [wedgeMat4_mul, wedgeMat4_mul]
  have h1 : wedgeMat4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      wedgeMat4 ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [← wedgeMat4_mul, A.mul_inv, wedgeMat4_one]
  have h2 : wedgeMat4 ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      wedgeMat4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [← wedgeMat4_mul, A.inv_mul, wedgeMat4_one]
  calc Nat.card ↥F ≤ Nat.card {a : Multiplicative (Fin 6 → ZMod 2) //
        ∀ k, Multiplicative.ofAdd (wedgeRep4 (γ k) (Multiplicative.toAdd a)) = a} :=
      card_le_of_fix hFU hFZ β hβk _ hP
    _ = Nat.card {c : Fin 6 → ZMod 2 // ∀ k, wedgeMat4
        (((γ k : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) *ᵥ c = c} :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun a => by
        simp only [wedgeRep4_apply]
        exact forall_congr' fun k => ⟨fun h => by simpa using congrArg Multiplicative.toAdd h,
          fun h => by rw [h]; rfl⟩)
    _ ≤ 4 := by
      rcases hA with hA | hA
      · simp_rw [fun k => (hA k).1, hW]
        exact card_fix_conj_le h1 h2 card_fix_wedge
      · simp_rw [fun k => (hA k).1, hW]
        exact card_fix_conj_le h1 h2 card_fix_wedge_dual

end Card

section Sums

variable {V : Type*} [CommGroup V] {ι : Type*}

@[expose] def fixIn (U : Subgroup V) (f : ι → MulAut V) : Subgroup V where
  carrier := {u | u ∈ U ∧ ∀ i, f i u = u}
  one_mem' := ⟨U.one_mem, fun i => map_one _⟩
  mul_mem' := fun ha hb => ⟨U.mul_mem ha.1 hb.1, fun i => by rw [map_mul, ha.2 i, hb.2 i]⟩
  inv_mem' := fun ha => ⟨U.inv_mem ha.1, fun i => by rw [map_inv, ha.2 i]⟩

theorem mem_fixIn {U : Subgroup V} {f : ι → MulAut V} {u : V} :
    u ∈ fixIn U f ↔ u ∈ U ∧ ∀ i, f i u = u := Iff.rfl

theorem exists_fix_decomp {k : ℕ} (I : Fin k → Subgroup V)
    (hind : ∀ j, I j ⊓ ⨆ (j' : Fin k) (_ : j' ≠ j), I j' = ⊥) (f : ι → MulAut V)
    (hinv : ∀ i j, ∀ u ∈ I j, f i u ∈ I j) {u : V} (hu : u ∈ ⨆ j, I j) (hf : ∀ i, f i u = u) :
    ∃ x : Fin k → V, (∀ j, x j ∈ fixIn (I j) f) ∧ u = ∏ j, x j := by
  classical
  obtain ⟨x, hx, rfl⟩ : ∃ x : Fin k → V, (∀ j, x j ∈ I j) ∧ u = ∏ j, x j := by
    refine Subgroup.iSup_induction I (C := fun u => ∃ x : Fin k → V, (∀ j, x j ∈ I j) ∧
      u = ∏ j, x j) hu (fun j y hy => ⟨Pi.mulSingle j y, fun j' => ?_, ?_⟩) ⟨1, fun j => ?_, ?_⟩
      (fun a b ⟨xa, hxa, ha⟩ ⟨xb, hxb, hb⟩ => ⟨xa * xb, fun j => (I j).mul_mem (hxa j) (hxb j),
        by rw [ha, hb, Pi.mul_def, Finset.prod_mul_distrib]⟩)
    · by_cases hj : j' = j
      · subst hj
        rw [Pi.mulSingle_eq_same]
        exact hy
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact (I j').one_mem
    · simp only [Finset.prod_pi_mulSingle', Finset.mem_univ, ↓reduceIte]
    · exact (I j).one_mem
    · simp
  refine ⟨x, fun j => ⟨hx j, fun i => ?_⟩, rfl⟩
  set y : Fin k → V := fun j => f i (x j) * (x j)⁻¹ with hy
  have hyI : ∀ j, y j ∈ I j := fun j => (I j).mul_mem (hinv i j _ (hx j)) ((I j).inv_mem (hx j))
  have hprod : ∏ j, y j = 1 := by
    rw [hy, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← map_prod, hf i, mul_inv_cancel]
  have hyj : y j = (∏ j' ∈ Finset.univ.erase j, y j')⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ j), hprod]
  have hmem : y j ∈ I j ⊓ ⨆ (j' : Fin k) (_ : j' ≠ j), I j' := by
    refine ⟨hyI j, ?_⟩
    rw [hyj]
    refine Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j' hj' => ?_)
    exact (le_iSup₂ (f := fun (j'' : Fin k) (_ : j'' ≠ j) => I j'') j'
      (Finset.ne_of_mem_erase hj')) (hyI j')
  rw [hind j, Subgroup.mem_bot, hy] at hmem
  exact mul_inv_eq_one.1 hmem

theorem card_le_prod {k : ℕ} (I : Fin k → Subgroup V)
    (hind : ∀ j, I j ⊓ ⨆ (j' : Fin k) (_ : j' ≠ j), I j' = ⊥) (f : ι → MulAut V)
    (hinv : ∀ i j, ∀ u ∈ I j, f i u ∈ I j) {F : Subgroup V} (hFI : F ≤ ⨆ j, I j)
    (hF : ∀ i, ∀ u ∈ F, f i u = u) [∀ j, Finite ↥(fixIn (I j) f)] :
    Nat.card ↥F ≤ ∏ j, Nat.card ↥(fixIn (I j) f) := by
  classical
  have hdec : ∀ u : ↥F, ∃ x : (j : Fin k) → ↥(fixIn (I j) f), (u : V) = ∏ j, (x j : V) := by
    intro u
    obtain ⟨x, hx, e⟩ := exists_fix_decomp I hind f hinv (hFI u.2) (fun i => hF i u u.2)
    exact ⟨fun j => ⟨x j, hx j⟩, e⟩
  choose d hd using hdec
  have hinj : Function.Injective d := fun u v h => Subtype.ext (by rw [hd u, hd v, h])
  calc Nat.card ↥F ≤ Nat.card ((j : Fin k) → ↥(fixIn (I j) f)) :=
        Nat.card_le_card_of_injective d hinj
    _ = ∏ j, Nat.card ↥(fixIn (I j) f) := Nat.card_pi

theorem card_le_mul {U₁ U₂ : Subgroup V} (hinf : U₁ ⊓ U₂ = ⊥) (f : ι → MulAut V)
    (hinv₁ : ∀ i, ∀ u ∈ U₁, f i u ∈ U₁) (hinv₂ : ∀ i, ∀ u ∈ U₂, f i u ∈ U₂) {F : Subgroup V}
    (hFU : F ≤ U₁ ⊔ U₂) (hF : ∀ i, ∀ u ∈ F, f i u = u) [Finite ↥(fixIn U₁ f)]
    [Finite ↥(fixIn U₂ f)] :
    Nat.card ↥F ≤ Nat.card ↥(fixIn U₁ f) * Nat.card ↥(fixIn U₂ f) := by
  classical
  have hdec : ∀ u : ↥F, ∃ x : ↥(fixIn U₁ f) × ↥(fixIn U₂ f), (u : V) = x.1 * x.2 := by
    intro u
    obtain ⟨u₁, hu₁, u₂, hu₂, e⟩ := Subgroup.mem_sup.1 (hFU u.2)
    have hsplit : ∀ i, f i u₁ = u₁ ∧ f i u₂ = u₂ := by
      intro i
      have e1 := hF i u u.2
      rw [← e, map_mul] at e1
      have hm : f i u₁ * u₁⁻¹ ∈ U₁ ⊓ U₂ := by
        refine ⟨U₁.mul_mem (hinv₁ i u₁ hu₁) (U₁.inv_mem hu₁), ?_⟩
        have : f i u₁ * u₁⁻¹ = u₂ * (f i u₂)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, e1, mul_comm]
        rw [this]
        exact U₂.mul_mem hu₂ (U₂.inv_mem (hinv₂ i u₂ hu₂))
      rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hm
      refine ⟨hm, ?_⟩
      rw [hm] at e1
      exact mul_left_cancel e1
    exact ⟨(⟨u₁, hu₁, fun i => (hsplit i).1⟩, ⟨u₂, hu₂, fun i => (hsplit i).2⟩), e.symm⟩
  choose d hd using hdec
  have hinj : Function.Injective d := fun u v h => Subtype.ext (by rw [hd u, hd v, h])
  calc Nat.card ↥F ≤ Nat.card (↥(fixIn U₁ f) × ↥(fixIn U₂ f)) :=
        Nat.card_le_card_of_injective d hinj
    _ = Nat.card ↥(fixIn U₁ f) * Nat.card ↥(fixIn U₂ f) := Nat.card_prod _ _

end Sums

section Q13

theorem sl2_cube (w : SpecialLinearGroup (Fin 2) (ZMod 2)) (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    (w : Matrix (Fin 2) (Fin 2) (ZMod 2)) = om ∨
      (w : Matrix (Fin 2) (Fin 2) (ZMod 2)) = om * om := by
  revert w
  decide +kernel

theorem det_q13_one (a b c d e : ZMod 2) : (q13 a b c d e 1).det = 1 := by
  revert a b c d e
  decide +kernel

theorem det_q13_om : ∀ m ∈ ({om, om * om} : Finset (Matrix (Fin 2) (Fin 2) (ZMod 2))),
    (q13 0 0 0 0 0 m).det = 1 := by
  decide +kernel

theorem det_cj : ∀ m ∈ ({om, om * om} : Finset (Matrix (Fin 2) (Fin 2) (ZMod 2))),
    ∀ a b d e : ZMod 2, (cj a b d e m).det = 1 := by
  decide +kernel

theorem blk_sc (k : Fin 4) :
    CFSG.QuasithinUnique.Vol2Native.A312L.blkAt 1 2 (by norm_num) (sc k) = 1 := by
  revert k
  decide +kernel

theorem q13_mem {g : SpecialLinearGroup (Fin 4) (ZMod 2)} {a b c d e : ZMod 2}
    {m : Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (hg : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = q13 a b c d e m) :
    g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer 4 (ZMod 2) {1, 3} := by
  refine CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_flagStabilizer.2 fun i hi => ?_
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_stabilizer_of_entries fun r l hr hl => ?_
  rw [hg]
  rcases hi with rfl | hi
  · fin_cases r <;> fin_cases l <;> simp_all [q13]
  · rw [Set.mem_singleton_iff] at hi
    subst hi
    fin_cases r <;> fin_cases l <;> simp_all [q13]

theorem eq_q13 {g : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hg : g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer 4 (ZMod 2) {1, 3}) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = q13 (g 0 1) (g 0 2) (g 0 3) (g 1 3) (g 2 3)
      (CFSG.QuasithinUnique.Vol2Native.A312L.blkAt 1 2 (by norm_num)
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) := by
  have h1 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_flagStabilizer.1 hg 1 (by simp)
  have h3 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_flagStabilizer.1 hg 3 (by simp)
  have hgi :
      g⁻¹ ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer 4 (ZMod 2) {1, 3} :=
    Subgroup.inv_mem _ hg
  have h1' := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_flagStabilizer.1 hgi 1 (by simp)
  have h3' := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_flagStabilizer.1 hgi 3 (by simp)
  have z : ∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)),
      x ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagSpace 4 (ZMod 2) 1) →
      x ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagSpace 4 (ZMod 2) 3) →
      (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 0 = 0 ∧
        (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 0 = 0 ∧
        (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 0 = 0 ∧
        (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 1 = 0 ∧
        (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 2 = 0 := fun x hx1 hx3 =>
    ⟨CFSG.QuasithinUnique.Vol2Native.A312L.stabilizer_entries hx1 (by decide) (by decide),
      CFSG.QuasithinUnique.Vol2Native.A312L.stabilizer_entries hx1 (by decide) (by decide),
      CFSG.QuasithinUnique.Vol2Native.A312L.stabilizer_entries hx1 (by decide) (by decide),
      CFSG.QuasithinUnique.Vol2Native.A312L.stabilizer_entries hx3 (by decide) (by decide),
      CFSG.QuasithinUnique.Vol2Native.A312L.stabilizer_entries hx3 (by decide) (by decide)⟩
  obtain ⟨a10, a20, a30, a31, a32⟩ := z g h1 h3
  obtain ⟨b10, b20, b30, b31, b32⟩ := z g⁻¹ h1' h3'
  have hmul : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e00 := congrFun (congrFun hmul 0) 0
  have e33 := congrFun (congrFun hmul 3) 3
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply_eq] at e00 e33
  rw [b10, b20, b30] at e00
  rw [a30, a31, a32] at e33
  have h00 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0 = 1 := by
    have key : ∀ x y : ZMod 2, x * y + 0 * 0 + 0 * 0 + 0 * 0 = 1 → x = 1 := by decide
    exact key _ _ (by simpa [mul_zero] using e00)
  have h33 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 3 = 1 := by
    have key : ∀ x y : ZMod 2, 0 * 0 + 0 * 0 + 0 * 0 + x * y = 1 → x = 1 := by decide
    exact key _ _ (by simpa [mul_zero] using e33)
  ext r c
  fin_cases r <;> fin_cases c <;> simp [q13, CFSG.QuasithinUnique.Vol2Native.A312L.blkAt_apply, *]

end Q13

end CFSG.Quasithin.H.Q13
