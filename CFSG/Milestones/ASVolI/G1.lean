module

public import CFSG.Quasithin.Background.G13Theta
public import CFSG.Quasithin.Background.G13Fam
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.G13Two

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin.G1

@[expose] def conjSub {G : Type*} [Group G] (X : Subgroup G) (g : G) : Subgroup G :=
  X.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def IsIrreducibleSub {G : Type*} [Group G] {U : Type*} [AddCommGroup U]
    [DistribMulAction G U] (X : Subgroup G) (W : AddSubgroup U) : Prop :=
  W ≠ ⊥ ∧ (∀ g ∈ X, ∀ w ∈ W, g • w ∈ W) ∧
    ∀ Y : AddSubgroup U, Y ≤ W → (∀ g ∈ X, ∀ y ∈ Y, g • y ∈ Y) → Y = ⊥ ∨ Y = W

section natural

variable {F : Type} [Field F] {n : ℕ} {U : Type} [AddCommGroup U]
  [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]

@[expose] def IsSumOfNatural (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) F))
    (S : Submodule F (Fin n → F)) (Y : AddSubgroup U) (s : ℕ) : Prop :=
  ∃ W : Fin s → AddSubgroup U, iSupIndep W ∧ (⨆ j, W j) = Y ∧ ∀ j,
    (∀ g ∈ X, ∀ w ∈ W j, g • w ∈ W j) ∧
    ∃ f : (Fin n → F) →+ U, Set.InjOn f S ∧ S.toAddSubgroup.map f = W j ∧
      ∀ g ∈ X, ∀ v ∈ S, f (g • v) = g • f v

@[expose] def Uij (φ : Submodule F (Fin n → F) → AddSubgroup U) (i j : Fin n) : AddSubgroup U :=
  φ (Vi F n i) ⊔ φ (Vi F n j)

@[expose] def Uhat (φ : Submodule F (Fin n → F) → AddSubgroup U) (i : Fin n) : AddSubgroup U :=
  ⨆ k : {k : Fin n // k ≠ i}, φ (Vi F n k)

@[expose] def Uhatij (φ : Submodule F (Fin n → F) → AddSubgroup U) (i j : Fin n) :
    AddSubgroup U :=
  ⨆ k : {k : Fin n // k ≠ i ∧ k ≠ j}, φ (Vi F n k)

end natural

@[expose] def IsFullFlag (F : Type) [Field F] (n : ℕ) (W : Fin (n + 1) → Submodule F (Fin n → F)) :
    Prop :=
  Monotone W ∧ ∀ i : Fin (n + 1), Module.finrank F (W i) = i

@[expose] def flagSylow (F : Type) [Field F] (n : ℕ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
  ⨆ (i : Fin n) (j : Fin n) (_ : i < j), Rij F i j

@[expose] def oTwoPrimeUpper {A : Type*} [Group A] (X : Subgroup A) : Subgroup A :=
  Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Quasithin.G1 CFSG.ASVolI.ChG

@[expose] def G_1_2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n →
    (∀ i j : Fin n, i ≠ j →
      commSub F (Lij F i j) = Vij F i j ∧ fixSub F (Lij F i j) = Vhatij F i j ∧
      Lij F i j = ptStab F (Vhatij F i j) ⊓ setStab F (Vij F i j) ∧
      Nonempty (Lij F i j ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
    Ladj F n = ⊤

theorem as_G_1_2 : G_1_2 := by
  intro F _ _ _ n hn
  exact ⟨fun i j hij => ⟨commSub_Lij hij, fixSub_Lij hij, Lij_eq hij, Lij_mulEquiv hij⟩,
    Ladj_eq_top hn⟩

@[expose] def G_1_3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n),
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        ∃ s : ℕ, Nat.card (φ (Vi F n ⟨0, by omega⟩)) = Nat.card F ^ s ∧
          IsSumOfNatural (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) ⊤ (⊤ : AddSubgroup U) s

theorem as_G_1_3 : G_1_3 := by
  intro F _ _ _ n hn U _ _ _ hsq φ hφ
  obtain ⟨s, hs, W, hWi, hWsup, hWj⟩ := theorem_G_1_3 (F := F) hn U hsq φ hφ
  refine ⟨s, hs, W, hWi, hWsup, fun j => ?_⟩
  obtain ⟨hinv, f, hfi, hfr, hfe⟩ := hWj j
  refine ⟨fun g _ w hw => hinv g w hw, f, fun _ _ _ _ h => hfi h, ?_, fun g _ v _ => hfe g v⟩
  rw [← hfr, AddMonoidHom.range_eq_map]
  congr 1

@[expose] def G_1_4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n),
    (∀ W W' : Fin (n + 1) → Submodule F (Fin n → F), IsFullFlag F n W → IsFullFlag F n W' →
      ∃ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ i, actSub g (W i) = W' i) ∧
    (∀ A₁ A₂ B₁ B₂ : Submodule F (Fin n → F), IsPoint A₁ → IsPoint A₂ → IsPoint B₁ →
      IsPoint B₂ → A₁ ≠ A₂ → B₁ ≠ B₂ →
      ∃ g : Matrix.SpecialLinearGroup (Fin n) F, actSub g A₁ = B₁ ∧ actSub g A₂ = B₂) ∧
    (IsFlag (Vi F n ⟨0, by omega⟩) (Vhat F n ⟨1, by omega⟩) ∧
      Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ =
        rootGroup (Vi F n ⟨0, by omega⟩) (Vhat F n ⟨1, by omega⟩) ∧
      ∀ A A' : Submodule F (Fin n → F), IsPoint A → IsPoint A' → A ≤ Vhat F n ⟨1, by omega⟩ →
        A' ≤ Vhat F n ⟨1, by omega⟩ → A ≠ Vi F n ⟨0, by omega⟩ → A' ≠ Vi F n ⟨0, by omega⟩ →
        ∃ g ∈ setStab F (Vi F n ⟨0, by omega⟩) ⊓ setStab F (Vhat F n ⟨1, by omega⟩),
          actSub g A = A') ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U,
        (∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (A : Submodule F (Fin n → F)), IsPoint A →
          φ (actSub g A) = (φ A).map (actU g)) →
        (⨆ i : Fin n, φ (Vi F n i)) = ⊤ →
        φ (Vi F n ⟨0, by omega⟩) ⊓ φ (Vi F n ⟨1, by omega⟩) = ⊥ →
        (∀ r ∈ Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, ∀ u ∈ φ (Vi F n ⟨1, by omega⟩),
          r • u - u ∈ φ (Vi F n ⟨0, by omega⟩)) →
        φ (Vi F n ⟨0, by omega⟩) ≤ fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) →
        (∀ h : 2 < n, φ (Vi F n ⟨2, h⟩) ≤ fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) →
        G13Hyp F n U φ)

section G14

variable {F : Type} [Field F] {n : ℕ}

private theorem g14_smul_scalar (g : Matrix.SpecialLinearGroup (Fin n) F) (x : F) (v : Fin n → F) :
    g • (x • v) = x • (g • v) := by
  simp only [smul_eq_mulVec', Matrix.mulVec_smul]

private theorem g14_actSub_span (g : Matrix.SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    actSub g (Submodule.span F {v}) = Submodule.span F {g • v} := by
  unfold actSub
  rw [Submodule.map_span, Set.image_singleton]
  rfl

private theorem g14_actSub_sup (g : Matrix.SpecialLinearGroup (Fin n) F) (A B : Submodule F (Fin n → F)) :
    actSub g (A ⊔ B) = actSub g A ⊔ actSub g B := by
  unfold actSub
  exact Submodule.map_sup _ _ _

private theorem g14_actSub_bot (g : Matrix.SpecialLinearGroup (Fin n) F) :
    actSub g ⊥ = ⊥ := by
  unfold actSub
  exact Submodule.map_bot _

private theorem g14_sl_one_add (p q : Fin n → F) (h : dotProduct q p = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ v : Fin n → F, g • v = v + dotProduct q v • p := by
  have hdet : (1 + Matrix.vecMulVec p q).det = 1 := by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, h, add_zero]
  refine ⟨⟨1 + Matrix.vecMulVec p q, hdet⟩, fun v => ?_⟩
  show Matrix.mulVec (1 + Matrix.vecMulVec p q) v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  congr 1
  funext i
  simp [MulOpposite.smul_eq_mul_unop, mul_comm]

private theorem g14_key (hn : 0 < n) (c : Fin n → (Fin n → F)) (hc : LinearIndependent F c) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ k : Fin n, ∃ x : F, x ≠ 0 ∧
      g • (Pi.single k (1 : F) : Fin n → F) = x • c k := by
  set M : Matrix (Fin n) (Fin n) F := Matrix.of fun i k => c k i with hM
  have hcol : (fun k => M.col k) = c := funext fun k => funext fun i => rfl
  have hc' : LinearIndependent F (fun k => M.col k) := by rw [hcol]; exact hc
  have hunit : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.1 hc'
  have hdetu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hunit
  have hd0 : M.det⁻¹ ≠ 0 := inv_ne_zero hdetu.ne_zero
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set D : Matrix (Fin n) (Fin n) F := Matrix.diagonal fun k => if k = i0 then M.det⁻¹ else 1 with hD
  have hdetD : (M * D).det = 1 := by
    rw [Matrix.det_mul, hD, Matrix.det_diagonal]
    simp [Finset.prod_ite_eq', mul_inv_cancel₀ hdetu.ne_zero]
  have hMe : ∀ k : Fin n, Matrix.mulVec M (Pi.single k (1 : F) : Fin n → F) = c k := fun k => by
    funext i
    simp [hM, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hDe : ∀ k : Fin n, Matrix.mulVec D (Pi.single k (1 : F) : Fin n → F) =
      (if k = i0 then M.det⁻¹ else 1) • (Pi.single k (1 : F) : Fin n → F) := by
    intro k
    funext i
    by_cases hik : i = k
    · subst hik
      simp [hD, Matrix.mulVec_diagonal]
    · simp [hD, Matrix.mulVec_diagonal, Pi.single_apply, hik]
  refine ⟨⟨M * D, hdetD⟩, fun k => ?_⟩
  refine ⟨if k = i0 then M.det⁻¹ else 1, ?_, ?_⟩
  · split_ifs
    · exact hd0
    · exact one_ne_zero
  · show Matrix.mulVec (M * D) (Pi.single k (1 : F) : Fin n → F) = _
    rw [← Matrix.mulVec_mulVec, hDe k, Matrix.mulVec_smul, hMe k]

private theorem g14_key2 (hn : 0 < n) (b b' : Fin n → (Fin n → F))
    (hb : LinearIndependent F b) (hb' : LinearIndependent F b') :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ k : Fin n, ∃ z : F, z ≠ 0 ∧ g • b k = z • b' k := by
  obtain ⟨g₁, h₁⟩ := g14_key hn b hb
  obtain ⟨g₂, h₂⟩ := g14_key hn b' hb'
  refine ⟨g₂ * g₁⁻¹, fun k => ?_⟩
  obtain ⟨x, hx, hgx⟩ := h₁ k
  obtain ⟨y, hy, hgy⟩ := h₂ k
  have e1 : g₁⁻¹ • b k = x⁻¹ • (Pi.single k (1 : F) : Fin n → F) := by
    have h1 : g₁⁻¹ • (g₁ • (Pi.single k (1 : F) : Fin n → F)) = Pi.single k (1 : F) :=
      inv_smul_smul g₁ _
    rw [hgx, g14_smul_scalar] at h1
    rw [← h1, smul_smul, inv_mul_cancel₀ hx, one_smul]
  refine ⟨x⁻¹ * y, mul_ne_zero (inv_ne_zero hx) hy, ?_⟩
  rw [mul_smul, e1, g14_smul_scalar, hgy, smul_smul]

private theorem g14_full_zero {W : Fin (n + 1) → Submodule F (Fin n → F)} (hW : IsFullFlag F n W) :
    W 0 = ⊥ := by
  have h := hW.2 0
  simp only [Fin.val_zero] at h
  exact Submodule.finrank_eq_zero.1 h

private theorem g14_flag_basis {W : Fin (n + 1) → Submodule F (Fin n → F)} (hW : IsFullFlag F n W) :
    ∃ b : Fin n → (Fin n → F), LinearIndependent F b ∧
      ∀ k : Fin n, W k.succ = W k.castSucc ⊔ Submodule.span F {b k} := by
  have hW0 : W 0 = ⊥ := g14_full_zero hW
  have hmono := hW.1
  have hfr := hW.2
  have hcs : ∀ k : Fin n, k.castSucc < k.succ := fun k => Fin.castSucc_lt_succ
  have hex : ∀ k : Fin n, ∃ x, x ∈ W k.succ ∧ x ∉ W k.castSucc := by
    intro k
    have hlt : W k.castSucc < W k.succ := by
      refine lt_of_le_of_ne (hmono (hcs k).le) ?_
      intro hEq
      have h1 := hfr k.castSucc
      have h2 := hfr k.succ
      rw [hEq] at h1
      simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
      omega
    exact SetLike.exists_of_lt hlt
  choose b hb1 hb2 using hex
  have hsplit : ∀ k : Fin n, W k.succ = W k.castSucc ⊔ Submodule.span F {b k} := by
    intro k
    have hbz : b k ≠ 0 := fun h => hb2 k (h ▸ (W k.castSucc).zero_mem)
    have hinf : W k.castSucc ⊓ Submodule.span F {b k} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxP, hxs⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxs
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply hb2 k
        have hbk : b k = c⁻¹ • (c • b k) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [hbk]
        exact (W k.castSucc).smul_mem _ hxP
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W k.castSucc) (Submodule.span F {b k})
    rw [hinf, finrank_bot, finrank_span_singleton hbz, add_zero] at hsum
    have hPfin := hfr k.castSucc
    have hQfin := hfr k.succ
    simp only [Fin.coe_castSucc, Fin.val_succ] at hPfin hQfin
    have hle : W k.castSucc ⊔ Submodule.span F {b k} ≤ W k.succ :=
      sup_le (hmono (hcs k).le)
        (Submodule.span_le.2 (Set.singleton_subset_iff.2 (hb1 k)))
    have hfin : Module.finrank F ↥(W k.castSucc ⊔ Submodule.span F {b k}) =
        Module.finrank F ↥(W k.succ) := by
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
  refine ⟨b, ?_, hsplit⟩
  have hspan : ∀ i : Fin (n + 1), W i ≤ Submodule.span F (Set.range b) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [hW0]; exact bot_le
    | succ k ih =>
      rw [hsplit k]
      exact sup_le ih (Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_range_self k)))
  have htop : (⊤ : Submodule F (Fin n → F)) ≤ Submodule.span F (Set.range b) := by
    have hlast : W (Fin.last n) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simp [hfr (Fin.last n)]
    rw [← hlast]
    exact hspan _
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)

private theorem g14_P1 (hn : 0 < n) (W W' : Fin (n + 1) → Submodule F (Fin n → F))
    (hW : IsFullFlag F n W) (hW' : IsFullFlag F n W') :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ i : Fin (n + 1), actSub g (W i) = W' i := by
  obtain ⟨b, hb, hbs⟩ := g14_flag_basis hW
  obtain ⟨b', hb', hbs'⟩ := g14_flag_basis hW'
  obtain ⟨g, hg⟩ := g14_key2 hn b b' hb hb'
  refine ⟨g, fun i => ?_⟩
  induction i using Fin.induction with
  | zero => rw [g14_full_zero hW, g14_full_zero hW', g14_actSub_bot]
  | succ k ih =>
    rw [hbs k, hbs' k, g14_actSub_sup, ih]
    obtain ⟨z, hz, hgz⟩ := hg k
    rw [g14_actSub_span, hgz, Submodule.span_singleton_smul_eq (IsUnit.mk0 z hz)]

private theorem g14_pivot {z : Fin n} (w : Fin n → F) (hwz : w z = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ v : Fin n → F,
      g • v = v + v z • (w - Pi.single z (1 : F)) := by
  obtain ⟨g, hg⟩ := g14_sl_one_add (w - Pi.single z (1 : F)) (Pi.single z (1 : F))
    (by simp [dotProduct, Pi.single_apply, hwz])
  refine ⟨g, fun v => ?_⟩
  rw [hg v]
  simp [dotProduct, Pi.single_apply]

private theorem g14_swap [CharP F 2] {a b : Fin n} (hab : a ≠ b) :
    ∃ P : Matrix.SpecialLinearGroup (Fin n) F,
      (∀ (v : Fin n → F) (k : Fin n), (P • v) k = v (Equiv.swap a b k)) ∧
      (∀ x : Fin n, P • (Pi.single x (1 : F) : Fin n → F) = Pi.single (Equiv.swap a b x) (1 : F)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hP : ∀ (v : Fin n → F) (k : Fin n), ((Matrix.SpecialLinearGroup.transvection hab (1 : F) *
      Matrix.SpecialLinearGroup.transvection hab.symm (1 : F) *
      Matrix.SpecialLinearGroup.transvection hab (1 : F)) • v) k = v (Equiv.swap a b k) := by
    intro v k
    simp only [mul_smul, T_smul_apply hab, T_smul_apply hab.symm, one_mul]
    by_cases hka : k = a
    · rw [hka, Equiv.swap_apply_left]
      simp [hab, hab.symm]
      first
        | linear_combination (v a + v b) * h2
        | linear_combination (v a) * h2
        | linear_combination (v b) * h2
        | (ring_nf; simp [h2])
    · by_cases hkb : k = b
      · rw [hkb, Equiv.swap_apply_right]
        simp [hab, hab.symm, hka]
        first
          | linear_combination (v a + v b) * h2
          | linear_combination (v a) * h2
          | linear_combination (v b) * h2
          | (ring_nf; simp [h2])
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
        simp [hka, hkb, hab, hab.symm]
  refine ⟨_, hP, fun x => ?_⟩
  funext j
  rw [hP]
  simp [Pi.single_apply, Equiv.swap_apply_eq_iff]

private theorem g14_mem_setStab_Vi {i0 : Fin n} (h : Matrix.SpecialLinearGroup (Fin n) F) (c : F)
    (hc : h • (Pi.single i0 (1 : F) : Fin n → F) = c • (Pi.single i0 (1 : F) : Fin n → F)) :
    h ∈ setStab F (Vi F n i0) := by
  have he : (Pi.single i0 (1 : F) : Fin n → F) ≠ 0 := by
    intro h0
    have := congrFun h0 i0
    simp at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply he
    have h3 : h⁻¹ • (h • (Pi.single i0 (1 : F) : Fin n → F)) = Pi.single i0 (1 : F) :=
      inv_smul_smul h _
    rw [hc, zero_smul, smul_zero] at h3
    exact h3.symm
  have hinv : h⁻¹ • (Pi.single i0 (1 : F) : Fin n → F) =
      c⁻¹ • (Pi.single i0 (1 : F) : Fin n → F) := by
    rw [inv_smul_eq_iff, g14_smul_scalar, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  show ∀ v : Fin n → F, v ∈ Vi F n i0 ↔ h • v ∈ Vi F n i0
  intro v
  unfold Vi
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a * c, by rw [g14_smul_scalar, hc, smul_smul]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a * c⁻¹, ?_⟩
    rw [← inv_smul_smul h v, ← ha, g14_smul_scalar, hinv, smul_smul]

private theorem g14_setStab_act {W : Submodule F (Fin n → F)}
    {h : Matrix.SpecialLinearGroup (Fin n) F} (hh : h ∈ setStab F W) : actSub h W = W := by
  have hh' : ∀ v, v ∈ W ↔ h • v ∈ W := hh
  ext v
  rw [mem_actSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hh' w).1 hw
  · intro hv
    exact ⟨h⁻¹ • v, (hh' (h⁻¹ • v)).2 (by rw [smul_inv_smul]; exact hv), smul_inv_smul h v⟩

private theorem g14_point_span {D : Submodule F (Fin n → F)} (hD : IsPoint D) :
    ∃ d : Fin n → F, d ≠ 0 ∧ D = Submodule.span F {d} := by
  obtain ⟨d, hd0, hdD⟩ := exists_gen hD
  refine ⟨d, hd0, ?_⟩
  ext w
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hw
    obtain ⟨c, rfl⟩ := (hdD w).1 hw
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact (hdD _).2 ⟨c, rfl⟩

private theorem g14_coord_of_ne {i0 : Fin n} {d : Fin n → F} (hd0 : d ≠ 0)
    (hne : Submodule.span F {d} ≠ Vi F n i0) : ∃ k : Fin n, k ≠ i0 ∧ d k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hdi : d = d i0 • (Pi.single i0 (1 : F) : Fin n → F) := by
    funext k
    by_cases hk : k = i0
    · subst hk
      simp
    · simp [hk, hcon k hk]
  have hi0 : d i0 ≠ 0 := by
    intro h0
    apply hd0
    rw [hdi, h0, zero_smul]
  unfold Vi
  rw [hdi, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hi0)]

private theorem g14_pt0 [CharP F 2] (hn : 2 ≤ n) (D : Submodule F (Fin n → F)) (hD : IsPoint D)
    (hne : D ≠ Vi F n ⟨0, by omega⟩) :
    ∃ h : Matrix.SpecialLinearGroup (Fin n) F, h ∈ setStab F (Vi F n ⟨0, by omega⟩) ∧
      actSub h (Vi F n ⟨1, by omega⟩) = D := by
  obtain ⟨d, hd0, hDd⟩ := g14_point_span hD
  have hne' : Submodule.span F {d} ≠ Vi F n ⟨0, by omega⟩ := hDd ▸ hne
  have hi01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  by_cases h1 : d ⟨1, by omega⟩ = 0
  · obtain ⟨k, hk0, hdk⟩ := g14_coord_of_ne hd0 hne'
    have hk1 : k ≠ ⟨1, by omega⟩ := fun h => hdk (by rw [h]; exact h1)
    obtain ⟨P, -, hPe⟩ := g14_swap (F := F) (a := ⟨1, by omega⟩) (b := k) hk1.symm
    obtain ⟨g, hg⟩ := g14_pivot (z := k) ((d k)⁻¹ • d) (by simp [hdk])
    have hgk : g • (Pi.single k (1 : F) : Fin n → F) = (d k)⁻¹ • d := by
      rw [hg]
      simp
    refine ⟨g * P, ?_, ?_⟩
    · apply g14_mem_setStab_Vi (c := 1)
      rw [mul_smul, hPe, Equiv.swap_apply_of_ne_of_ne hi01 hk0.symm, hg]
      simp [Pi.single_apply, hk0]
    · show actSub (g * P) (Submodule.span F {(Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) :
          Fin n → F)}) = D
      rw [g14_actSub_span, mul_smul, hPe, Equiv.swap_apply_left, hgk, hDd,
        Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hdk))]
  · obtain ⟨g, hg⟩ := g14_pivot (z := (⟨1, by omega⟩ : Fin n)) ((d ⟨1, by omega⟩)⁻¹ • d)
      (by simp [h1])
    have hgi1 : g • (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) : Fin n → F) =
        (d ⟨1, by omega⟩)⁻¹ • d := by
      rw [hg]
      simp
    refine ⟨g, ?_, ?_⟩
    · apply g14_mem_setStab_Vi (c := 1)
      rw [hg, one_smul]
      simp [Pi.single_apply, hi01.symm]
    · show actSub g (Submodule.span F {(Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) :
          Fin n → F)}) = D
      rw [g14_actSub_span, hgi1, hDd,
        Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero h1))]

private theorem g14_stab_pt [CharP F 2] (hn : 3 ≤ n) (D : Submodule F (Fin n → F))
    (hD : IsPoint D) (hDV : D ≤ Vhat F n ⟨1, by omega⟩) (hne : D ≠ Vi F n ⟨0, by omega⟩) :
    ∃ h : Matrix.SpecialLinearGroup (Fin n) F,
      h ∈ setStab F (Vi F n ⟨0, by omega⟩) ⊓ setStab F (Vhat F n ⟨1, by omega⟩) ∧
      actSub h (Vi F n ⟨2, by omega⟩) = D := by
  obtain ⟨d, hd0, hDd⟩ := g14_point_span hD
  have hne' : Submodule.span F {d} ≠ Vi F n ⟨0, by omega⟩ := hDd ▸ hne
  have hd1 : d ⟨1, by omega⟩ = 0 := by
    have hdD : d ∈ D := by
      rw [hDd]
      exact Submodule.mem_span_singleton_self d
    exact mem_Vhat.1 (hDV hdD)
  obtain ⟨k, hk0, hdk⟩ := g14_coord_of_ne hd0 hne'
  have hk1 : k ≠ ⟨1, by omega⟩ := fun h => hdk (by rw [h]; exact hd1)
  have hi02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hi12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨g, hg⟩ := g14_pivot (z := k) ((d k)⁻¹ • d) (by simp [hdk])
  have hgi1 : ∀ v : Fin n → F, (g • v) ⟨1, by omega⟩ = v ⟨1, by omega⟩ := by
    intro v
    rw [hg]
    simp [Pi.single_apply, hd1, hk1.symm]
  have hmain : ∃ h : Matrix.SpecialLinearGroup (Fin n) F,
      h • (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F) =
        Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) ∧
      (∀ v : Fin n → F, (h • v) ⟨1, by omega⟩ = v ⟨1, by omega⟩) ∧
      h • (Pi.single (⟨2, by omega⟩ : Fin n) (1 : F) : Fin n → F) = (d k)⁻¹ • d := by
    by_cases hk2 : k = ⟨2, by omega⟩
    · refine ⟨g, ?_, hgi1, ?_⟩
      · rw [hg]
        simp [Pi.single_apply, hk0]
      · rw [hg]
        simp [hk2]
    · obtain ⟨P, hPv, hPe⟩ := g14_swap (F := F) (a := ⟨2, by omega⟩) (b := k) (Ne.symm hk2)
      refine ⟨g * P, ?_, ?_, ?_⟩
      · rw [mul_smul, hPe, Equiv.swap_apply_of_ne_of_ne hi02 hk0.symm, hg]
        simp [Pi.single_apply, hk0]
      · intro v
        rw [mul_smul, hgi1, hPv, Equiv.swap_apply_of_ne_of_ne hi12 hk1.symm]
      · rw [mul_smul, hPe, Equiv.swap_apply_left, hg]
        simp
  obtain ⟨h, hh0, hh1, hh2⟩ := hmain
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · apply g14_mem_setStab_Vi (c := 1)
    rw [hh0, one_smul]
  · show ∀ v : Fin n → F, v ∈ Vhat F n ⟨1, by omega⟩ ↔ h • v ∈ Vhat F n ⟨1, by omega⟩
    intro v
    rw [mem_Vhat, mem_Vhat, hh1 v]
  · show actSub h (Submodule.span F {(Pi.single (⟨2, by omega⟩ : Fin n) (1 : F) :
        Fin n → F)}) = D
    rw [g14_actSub_span, hh2, hDd, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hdk))]

private theorem g14_eq_Vi0_of_lt3 (hn : 2 ≤ n) (hn3 : ¬ 3 ≤ n) {A : Submodule F (Fin n → F)}
    (hA : IsPoint A) (hAV : A ≤ Vhat F n ⟨1, by omega⟩) : A = Vi F n ⟨0, by omega⟩ := by
  have hle : A ≤ Vi F n ⟨0, by omega⟩ := by
    intro x hx
    rw [mem_Vi]
    intro k hk
    have hk1 : k = ⟨1, by omega⟩ := by
      apply Fin.ext
      have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
      have := k.isLt
      show k.val = 1
      omega
    rw [hk1]
    exact mem_Vhat.1 (hAV hx)
  have h1 : Module.finrank F A = 1 := hA
  have h2 : Module.finrank F (Vi F n ⟨0, by omega⟩) = 1 := isPoint_Vi _
  exact Submodule.eq_of_le_of_finrank_eq hle (h1.trans h2.symm)

private theorem g14_trans_stab [CharP F 2] (hn : 2 ≤ n) {A A' : Submodule F (Fin n → F)}
    (hA : IsPoint A) (hA' : IsPoint A') (hAV : A ≤ Vhat F n ⟨1, by omega⟩)
    (hA'V : A' ≤ Vhat F n ⟨1, by omega⟩) (hA0 : A ≠ Vi F n ⟨0, by omega⟩)
    (hA'0 : A' ≠ Vi F n ⟨0, by omega⟩) :
    ∃ g ∈ setStab F (Vi F n ⟨0, by omega⟩) ⊓ setStab F (Vhat F n ⟨1, by omega⟩),
      actSub g A = A' := by
  by_cases hn3 : 3 ≤ n
  · obtain ⟨g₁, hg₁, hA₁⟩ := g14_stab_pt hn3 A hA hAV hA0
    obtain ⟨g₂, hg₂, hA₂⟩ := g14_stab_pt hn3 A' hA' hA'V hA'0
    refine ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁), ?_⟩
    rw [actSub_mul, actSub_inv_eq hA₁, hA₂]
  · exact absurd (g14_eq_Vi0_of_lt3 hn hn3 hA hAV) hA0

private theorem g14_pair [CharP F 2] (hn : 2 ≤ n) {A₁ A₂ : Submodule F (Fin n → F)}
    (h₁ : IsPoint A₁) (h₂ : IsPoint A₂) (hne : A₁ ≠ A₂) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F,
      actSub g (Vi F n ⟨0, by omega⟩) = A₁ ∧ actSub g (Vi F n ⟨1, by omega⟩) = A₂ := by
  obtain ⟨g₁, hg₁⟩ := exists_actSub_Vi_eq hn ⟨0, by omega⟩ h₁
  have hcancel : ∀ (m : Matrix.SpecialLinearGroup (Fin n) F) (B : Submodule F (Fin n → F)),
      actSub m (actSub m⁻¹ B) = B := fun m B => by
    rw [← actSub_mul, mul_inv_cancel, actSub_one]
  have hD : IsPoint (actSub g₁⁻¹ A₂) := isPoint_actSub _ h₂
  have hne' : actSub g₁⁻¹ A₂ ≠ Vi F n ⟨0, by omega⟩ := by
    intro h
    apply hne
    calc A₁ = actSub g₁ (Vi F n ⟨0, by omega⟩) := hg₁.symm
      _ = actSub g₁ (actSub g₁⁻¹ A₂) := by rw [h]
      _ = A₂ := hcancel g₁ A₂
  obtain ⟨h, hhS, hh⟩ := g14_pt0 hn (actSub g₁⁻¹ A₂) hD hne'
  refine ⟨g₁ * h, ?_, ?_⟩
  · rw [actSub_mul, g14_setStab_act hhS, hg₁]
  · rw [actSub_mul, hh, hcancel]

private theorem g14_two_trans [CharP F 2] (hn : 2 ≤ n) {A₁ A₂ B₁ B₂ : Submodule F (Fin n → F)}
    (hA₁ : IsPoint A₁) (hA₂ : IsPoint A₂) (hB₁ : IsPoint B₁) (hB₂ : IsPoint B₂)
    (hA : A₁ ≠ A₂) (hB : B₁ ≠ B₂) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, actSub g A₁ = B₁ ∧ actSub g A₂ = B₂ := by
  obtain ⟨gA, hA0, hA1⟩ := g14_pair hn hA₁ hA₂ hA
  obtain ⟨gB, hB0, hB1⟩ := g14_pair hn hB₁ hB₂ hB
  refine ⟨gB * gA⁻¹, ?_, ?_⟩
  · rw [actSub_mul, actSub_inv_eq hA0, hB0]
  · rw [actSub_mul, actSub_inv_eq hA1, hB1]

private theorem g14_single_smul (i : Fin n) (c : F) :
    (Pi.single i c : Fin n → F) = c • (Pi.single i (1 : F) : Fin n → F) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

private theorem g14_hyperplane_ker {B : Submodule F (Fin n → F)} (hB : IsHyperplane B) :
    ∃ f : (Fin n → F) →ₗ[F] F, f ≠ 0 ∧ LinearMap.ker f = B := by
  unfold IsHyperplane at hB
  have hBtop : B < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    rw [h, finrank_top, Module.finrank_fin_fun] at hB
    omega
  obtain ⟨f, hf0, hBf⟩ := Submodule.exists_le_ker_of_lt_top B hBtop
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (LinearMap.ext fun y => hcon y)
    exact ⟨(c * (f x)⁻¹) • x, by rw [map_smul, smul_eq_mul]; field_simp⟩
  have hrange : Module.finrank F (LinearMap.range f) = 1 := by
    rw [hsurj, finrank_top, Module.finrank_self]
  have hk := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, Module.finrank_fin_fun] at hk
  exact ⟨f, hf0, (Submodule.eq_of_le_of_finrank_eq hBf (by omega)).symm⟩

private theorem g14_flag_transport [CharP F 2] (hn : 2 ≤ n) {A B : Submodule F (Fin n → F)}
    (hA : IsPoint A) (hB : IsHyperplane B) (hAB : A ≤ B) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F,
      actSub g (Vi F n ⟨0, by omega⟩) = A ∧ actSub g (Vhat F n ⟨1, by omega⟩) = B := by
  obtain ⟨a, ha0, ha⟩ := exists_gen hA
  obtain ⟨f, hf0, hfB⟩ := g14_hyperplane_ker hB
  have hi0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have haB : a ∈ B := hAB ((ha a).2 ⟨1, (one_smul F a).symm⟩)
  have haf : f a = 0 := by
    rw [← LinearMap.mem_ker, hfB]
    exact haB
  obtain ⟨m₁, hm₁⟩ := exists_smul_single_eq hn ⟨0, by omega⟩ ha0
  set ell : (Fin n → F) →ₗ[F] F := f.comp (Matrix.mulVecLin (m₁ : Matrix (Fin n) (Fin n) F))
    with hell
  have hℓ : ∀ x, ell x = f (m₁ • x) := fun x => rfl
  have hℓ0 : ell (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F)) = 0 := by
    rw [hℓ, hm₁]
    exact haf
  have hℓne : ell ≠ 0 := by
    have key : ∀ y, f y = ell (m₁⁻¹ • y) := fun y => by rw [hℓ, smul_inv_smul]
    intro h0
    apply hf0
    exact LinearMap.ext fun y => by rw [key y, h0]; rfl
  obtain ⟨T, hT0, c, hc0, hcT⟩ : ∃ T : Matrix.SpecialLinearGroup (Fin n) F,
      T • (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F) =
        Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) ∧
      ∃ c : F, c ≠ 0 ∧ ell (T • (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) : Fin n → F)) = c := by
    by_cases h1 : ell (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F)) = 0
    · have hj : ∃ j : Fin n, ell (Pi.single j (1 : F)) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hℓne
        apply LinearMap.pi_ext
        intro i x
        rw [g14_single_smul, map_smul, hcon i, smul_zero, LinearMap.zero_apply]
      obtain ⟨j, hj⟩ := hj
      have hj1 : j ≠ ⟨1, by omega⟩ := fun h => hj (by rw [h]; exact h1)
      refine ⟨Matrix.SpecialLinearGroup.transvection hj1 (ell (Pi.single j (1 : F)))⁻¹, ?_, 1,
        one_ne_zero, ?_⟩
      · funext k
        rw [T_smul_apply]
        by_cases hk : k = j
        · subst hk
          simp [Pi.single_apply, hi0.symm]
        · simp [Pi.single_apply, hk, hi0.symm]
      · have hTe1 : Matrix.SpecialLinearGroup.transvection hj1 (ell (Pi.single j (1 : F)))⁻¹ •
            (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) : Fin n → F) =
            Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) +
              (ell (Pi.single j (1 : F)))⁻¹ • (Pi.single j (1 : F) : Fin n → F) := by
          funext k
          rw [T_smul_apply]
          by_cases hk : k = j
          · subst hk
            simp [Pi.single_apply, hj1]
          · simp [Pi.single_apply, hk]
        rw [hTe1, map_add, map_smul, h1, smul_eq_mul, zero_add, inv_mul_cancel₀ hj]
    · refine ⟨1, by rw [one_smul], ell (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F)), h1, ?_⟩
      rw [one_smul]
  set ellT : (Fin n → F) →ₗ[F] F := ell.comp (Matrix.mulVecLin (T : Matrix (Fin n) (Fin n) F))
    with hellT
  have hT' : ∀ x, ellT x = ell (T • x) := fun x => rfl
  have hcT' : ellT (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F)) = c := by
    rw [hT']
    exact hcT
  have hT0' : ellT (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F)) = 0 := by
    rw [hT', hT0, hℓ0]
  have hlin : ∀ y : Fin n → F, ellT y = ∑ k, y k * ellT (Pi.single k (1 : F)) := by
    intro y
    calc ellT y = ellT (∑ k, Pi.single k (y k)) := by rw [Finset.univ_sum_single]
      _ = ∑ k, ellT (Pi.single k (y k)) := map_sum ellT _ _
      _ = ∑ k, y k * ellT (Pi.single k (1 : F)) := Finset.sum_congr rfl fun k _ => by
          rw [g14_single_smul, map_smul, smul_eq_mul]
  set u : Fin n → F := fun k => ellT (Pi.single k (1 : F)) -
    (if k = (⟨1, by omega⟩ : Fin n) then c else 0) with hu
  have hu1 : u ⟨1, by omega⟩ = 0 := by
    simp [hu, hcT']
  have hu0 : u ⟨0, by omega⟩ = 0 := by
    simp [hu, hT0', hi0]
  have hform : ∀ y : Fin n → F, ellT y = dotProduct u y + c * y ⟨1, by omega⟩ := by
    intro y
    have hterm : ∀ k : Fin n, u k * y k = y k * ellT (Pi.single k (1 : F)) -
        (if k = (⟨1, by omega⟩ : Fin n) then c * y k else 0) := by
      intro k
      simp only [hu]
      split_ifs <;> ring
    rw [hlin y, dotProduct]
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hdot0 : dotProduct u (-(c⁻¹) • (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) : Fin n → F)) = 0 := by
    simp [dotProduct_smul, dotProduct_single, hu1]
  obtain ⟨M, hM⟩ := g14_sl_one_add (-(c⁻¹) • (Pi.single (⟨1, by omega⟩ : Fin n) (1 : F) :
    Fin n → F)) u hdot0
  set g : Matrix.SpecialLinearGroup (Fin n) F := m₁ * T * M with hg
  have hMe0 : M • (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F) =
      Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) := by
    rw [hM]
    have h0 : dotProduct u (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F)) = 0 := by
      simp [dotProduct_single, hu0]
    rw [h0, zero_smul, add_zero]
  have hgA : g • (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F) = a := by
    rw [hg, mul_smul, mul_smul, hMe0, hT0, hm₁]
  have hfg : ∀ x : Fin n → F, f (g • x) = c * x ⟨1, by omega⟩ := by
    intro x
    have h1 : f (g • x) = ellT (M • x) := by
      rw [hg, mul_smul, mul_smul]
      rfl
    rw [h1, hform, hM x]
    simp [dotProduct_add, dotProduct_smul, hdot0, hu1, Pi.single_apply] <;> field_simp <;> ring
  refine ⟨g, ?_, ?_⟩
  · show actSub g (Submodule.span F {(Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F)}) = A
    rw [g14_actSub_span, hgA]
    ext w
    rw [Submodule.mem_span_singleton, ha w]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, hr.symm⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, hr.symm⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := mem_actSub.1 hy
      rw [mem_Vhat] at hw
      rw [← hfB, LinearMap.mem_ker, hfg w, hw, mul_zero]
    · intro hy
      have hfy : f y = 0 := by
        rw [← LinearMap.mem_ker, hfB]
        exact hy
      refine mem_actSub.2 ⟨g⁻¹ • y, ?_, smul_inv_smul g y⟩
      rw [mem_Vhat]
      have h1 := hfg (g⁻¹ • y)
      rw [smul_inv_smul, hfy] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left hc0

private theorem g14_conj_mem (g : Matrix.SpecialLinearGroup (Fin n) F) (A B : Submodule F (Fin n → F))
    (t : Matrix.SpecialLinearGroup (Fin n) F) :
    t ∈ rootGroup (actSub g A) (actSub g B) ↔ g⁻¹ * t * g ∈ rootGroup A B := by
  have hmem : ∀ (v : Fin n → F) (W : Submodule F (Fin n → F)), v ∈ actSub g W ↔ g⁻¹ • v ∈ W := by
    intro v W
    rw [mem_actSub]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [inv_smul_smul]
      exact hw
    · intro hv
      exact ⟨g⁻¹ • v, hv, smul_inv_smul g v⟩
  have hsv : ∀ v : Fin n → F, (g⁻¹ * t * g) • v - v = g⁻¹ • (t • (g • v) - g • v) := fun v => by
    rw [smul_sub, mul_smul, mul_smul, inv_smul_smul]
  have htv : ∀ v : Fin n → F, g⁻¹ • (t • v - v) = (g⁻¹ * t * g) • (g⁻¹ • v) - g⁻¹ • v :=
    fun v => by
      rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [mem_rootGroup, mem_rootGroup]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [hsv]
      exact (hmem _ A).1 (h1 (g • v))
    · rw [mul_smul, mul_smul, h2 (g • v) (mem_actSub.2 ⟨v, hv, rfl⟩), inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · apply (hmem _ A).2
      rw [htv]
      exact h1 (g⁻¹ • v)
    · have h3 := h2 (g⁻¹ • v) ((hmem v B).1 hv)
      rw [mul_smul, mul_smul, smul_inv_smul] at h3
      have h4 := congrArg (fun x => g • x) h3
      simp only [smul_inv_smul] at h4
      exact h4

private theorem g14_commU_conj_le {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    (g : Matrix.SpecialLinearGroup (Fin n) F) (A B : Submodule F (Fin n → F)) :
    commU (U := U) (rootGroup (actSub g A) (actSub g B)) ≤
      (commU (U := U) (rootGroup A B)).map (actU g) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨t, ht, u, rfl⟩
  have hs : g⁻¹ * t * g ∈ rootGroup A B := (g14_conj_mem g A B t).1 ht
  refine AddSubgroup.mem_map.2 ⟨(g⁻¹ * t * g) • (g⁻¹ • u) - g⁻¹ • u,
    AddSubgroup.subset_closure ⟨_, hs, g⁻¹ • u, rfl⟩, ?_⟩
  show g • ((g⁻¹ * t * g) • (g⁻¹ • u) - g⁻¹ • u) = t • u - u
  simp only [smul_sub, mul_smul, smul_inv_smul]

private theorem g14_fixU_map_le {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    (g : Matrix.SpecialLinearGroup (Fin n) F) (A B : Submodule F (Fin n → F)) :
    (fixU (U := U) (rootGroup A B)).map (actU g) ≤
      fixU (U := U) (rootGroup (actSub g A) (actSub g B)) := by
  rintro _ ⟨y, hy, rfl⟩ t ht
  have hs : g⁻¹ * t * g ∈ rootGroup A B := (g14_conj_mem g A B t).1 ht
  have h1 : (g⁻¹ * t * g) • y = y := hy _ hs
  show t • (g • y) = g • y
  calc t • (g • y) = g • ((g⁻¹ * t * g) • y) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
    _ = g • y := by rw [h1]

private theorem g14_Vi_le_Vhat {i j : Fin n} (hij : i ≠ j) : Vi F n i ≤ Vhat F n j :=
  le_iSup (fun m : {m : Fin n // m ≠ j} => Vi F n m.1) ⟨i, hij⟩

private theorem g14_G13Hyp [CharP F 2] (hn : 2 ≤ n) (U : Type) [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    (φ : Submodule F (Fin n → F) → AddSubgroup U)
    (hequiv : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (A : Submodule F (Fin n → F)),
      IsPoint A → φ (actSub g A) = (φ A).map (actU g))
    (hsup : (⨆ i : Fin n, φ (Vi F n i)) = ⊤)
    (hdisj : φ (Vi F n ⟨0, by omega⟩) ⊓ φ (Vi F n ⟨1, by omega⟩) = ⊥)
    (hcomm : ∀ r ∈ Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, ∀ u ∈ φ (Vi F n ⟨1, by omega⟩),
      r • u - u ∈ φ (Vi F n ⟨0, by omega⟩))
    (hfix0 : φ (Vi F n ⟨0, by omega⟩) ≤ fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩))
    (hfix2 : ∀ h : 2 < n, φ (Vi F n ⟨2, h⟩) ≤ fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) :
    G13Hyp F n U φ := by
  have hfixV : ∀ D : Submodule F (Fin n → F), IsPoint D → D ≤ Vhat F n ⟨1, by omega⟩ →
      φ D ≤ fixU (U := U) (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) := by
    intro D hD hDV
    by_cases hD0 : D = Vi F n ⟨0, by omega⟩
    · rw [hD0]
      exact hfix0
    · by_cases hn3 : 3 ≤ n
      · obtain ⟨h, hhS, hh⟩ := g14_stab_pt hn3 D hD hDV hD0
        have hV2 : φ (Vi F n ⟨2, by omega⟩) ≤ fixU (U := U) (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) :=
          hfix2 (by omega)
        have hφD : φ D = (φ (Vi F n ⟨2, by omega⟩)).map (actU h) := by
          rw [← hh]
          exact hequiv h _ (isPoint_Vi _)
        rw [hφD]
        refine le_trans (AddSubgroup.map_mono hV2) ?_
        refine le_trans (g14_fixU_map_le h _ _) ?_
        rw [g14_setStab_act hhS.1, g14_setStab_act hhS.2]
        exact le_rfl
      · exact absurd (g14_eq_Vi0_of_lt3 hn hn3 hD hDV) hD0
  have hcommR : ∀ t ∈ Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, ∀ u : U,
      t • u - u ∈ φ (Vi F n ⟨0, by omega⟩) := by
    intro t ht
    let Q : AddSubgroup U := (φ (Vi F n ⟨0, by omega⟩)).comap ((actU t) - AddMonoidHom.id U)
    have hQ : (⨆ i : Fin n, φ (Vi F n i)) ≤ Q := by
      refine iSup_le fun i => ?_
      intro u hu
      show t • u - u ∈ φ (Vi F n ⟨0, by omega⟩)
      by_cases hi : i = ⟨1, by omega⟩
      · subst hi
        exact hcomm t ht u hu
      · have hfixu : u ∈ fixU (U := U) (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) :=
          hfixV (Vi F n i) (isPoint_Vi i) (g14_Vi_le_Vhat hi) hu
        have htu : t • u = u := hfixu t ht
        rw [htu, sub_self]
        exact AddSubgroup.zero_mem _
    have hall : ∀ u : U, u ∈ Q := fun u => by
      have hu : u ∈ (⨆ i : Fin n, φ (Vi F n i)) := by
        rw [hsup]
        exact AddSubgroup.mem_top u
      exact hQ hu
    intro u
    exact hall u
  have hcommle : commU (U := U) (rootGroup (Vi F n ⟨0, by omega⟩) (Vhat F n ⟨1, by omega⟩)) ≤
      φ (Vi F n ⟨0, by omega⟩) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨t, ht, u, rfl⟩
    exact hcommR t ht u
  have hcommLe : ∀ A B : Submodule F (Fin n → F), IsFlag A B →
      commU (U := U) (rootGroup A B) ≤ φ A := by
    rintro A B ⟨hA, hB, hAB⟩
    obtain ⟨g, hgA, hgB⟩ := g14_flag_transport hn hA hB hAB
    rw [← hgA, ← hgB]
    refine le_trans (g14_commU_conj_le g _ _) ?_
    refine le_trans (AddSubgroup.map_mono hcommle) ?_
    rw [hequiv g _ (isPoint_Vi _)]
  have hfixLe : ∀ A B : Submodule F (Fin n → F), IsFlag A B → ∀ D : Submodule F (Fin n → F),
      IsPoint D → D ≤ B → φ D ≤ fixU (U := U) (rootGroup A B) := by
    rintro A B ⟨hA, hB, hAB⟩ D hD hDB
    obtain ⟨g, hgA, hgB⟩ := g14_flag_transport hn hA hB hAB
    have hD' : IsPoint (actSub g⁻¹ D) := isPoint_actSub _ hD
    have hDD : actSub g (actSub g⁻¹ D) = D := by
      rw [← actSub_mul, mul_inv_cancel, actSub_one]
    have hD'V : actSub g⁻¹ D ≤ Vhat F n ⟨1, by omega⟩ := by
      intro x hx
      have h1 : g • x ∈ D := by
        rw [← hDD]
        exact mem_actSub.2 ⟨x, hx, rfl⟩
      have h2 : g • x ∈ actSub g (Vhat F n ⟨1, by omega⟩) := by
        rw [hgB]
        exact hDB h1
      obtain ⟨w, hw, hwx⟩ := mem_actSub.1 h2
      have hwx' : w = x := MulAction.injective g hwx
      rw [← hwx']
      exact hw
    have hφD : φ D = (φ (actSub g⁻¹ D)).map (actU g) := by
      rw [← hequiv g _ hD', hDD]
    rw [hφD, ← hgA, ← hgB]
    exact le_trans (AddSubgroup.map_mono (hfixV _ hD' hD'V)) (g14_fixU_map_le g _ _)
  have hdisjAll : ∀ A₁ A₂ : Submodule F (Fin n → F), IsPoint A₁ → IsPoint A₂ → A₁ ≠ A₂ →
      φ A₁ ⊓ φ A₂ = ⊥ := by
    intro A₁ A₂ h₁ h₂ hne
    obtain ⟨g, hg1, hg2⟩ := g14_pair hn h₁ h₂ hne
    have hinj : Function.Injective (actU (U := U) g) := fun a b h => MulAction.injective g h
    rw [← hg1, ← hg2, hequiv g _ (isPoint_Vi _), hequiv g _ (isPoint_Vi _),
      ← AddSubgroup.map_inf _ _ _ hinj, hdisj, AddSubgroup.map_bot]
  have hiSup : (⨆ (A : Submodule F (Fin n → F)) (_ : IsPoint A), φ A) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (A : Submodule F (Fin n → F)) (_ : IsPoint A) => φ A) (Vi F n i)
      (isPoint_Vi i)
  exact ⟨hequiv, fun A B hAB => hcommLe A B hAB, fun A B hAB D hD hDB => hfixLe A B hAB D hD hDB,
    hdisjAll, hiSup⟩
end G14

theorem as_G_1_4 : G_1_4 := by
  intro F _ _ _ n hn
  have hi01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine ⟨fun W W' hW hW' => g14_P1 (by omega) W W' hW hW', ?_,
    ⟨isFlag_Vi_Vhat hi01, rfl, ?_⟩, ?_⟩
  · intro A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hA hB
    exact g14_two_trans hn hA₁ hA₂ hB₁ hB₂ hA hB
  · intro A A' hA hA' hAV hA'V hA0 hA'0
    exact g14_trans_stab hn hA hA' hAV hA'V hA0 hA'0
  · intro U _ _ _ hsq φ hequiv hsup hdisj hcomm hfix0 hfix2
    exact g14_G13Hyp hn U φ hequiv hsup hdisj hcomm hfix0 hfix2


@[expose] def G_1_5 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
    (∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), (P : Subgroup _) = R) →
    (∃ A : Submodule F (Fin 2 → F), IsPoint A ∧ R = rootGroup A A) ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin 2 → F) → AddSubgroup U, G13Hyp F 2 U φ →
      ∀ A : Submodule F (Fin 2 → F), IsPoint A → R = rootGroup A A →
        φ A = commU R ∧ φ A = fixU R ∧
        ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, g ∉ Subgroup.normalizer (R : Set (Matrix.SpecialLinearGroup (Fin 2) F)) →
          IsCompl (commU (U := U) R) (commU (U := U) (conjSub R g))) ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (Y : AddSubgroup U),
        (∀ x ∈ Subgroup.normalizer (R : Set (Matrix.SpecialLinearGroup (Fin 2) F)), ∀ y ∈ Y, x • y ∈ Y) → commU (U := U) R ≤ Y → Y ≤ fixU (U := U) R →
        IsCompl Y (Y.map (actU g⁻¹)) →
        ∀ A : Submodule F (Fin 2 → F), IsPoint A → R = rootGroup A A →
          ∃ φ : Submodule F (Fin 2 → F) → AddSubgroup U, G13Hyp F 2 U φ ∧
            ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
              φ (actSub x⁻¹ A) = Y.map (actU x⁻¹)) ∧
    (∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ((∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
          IsCompl (fixU (U := U) R) (fixU (U := U) (conjSub R g))) ↔
        (commU (U := U) R ≤ fixU (U := U) R ∧
          ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 → Odd (orderOf x) →
            fixU (U := U) (Subgroup.zpowers x) = ⊥)) ∧
      ((∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
          IsCompl (fixU (U := U) R) (fixU (U := U) (conjSub R g))) ↔
        (commU (U := U) R ≤ fixU (U := U) R ∧
          ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 ∧ Odd (orderOf x) ∧
            fixU (U := U) (Subgroup.zpowers x) = ⊥)))

section G15Help

open CFSG.Quasithin.SL2Model

variable {F : Type} [Field F]

private theorem g15_mem_conjSub {X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    {g x : Matrix.SpecialLinearGroup (Fin 2) F} : x ∈ conjSub X g ↔ g * x * g⁻¹ ∈ X := by
  unfold conjSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem g15_actSub_inv_actSub (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (A : Submodule F (Fin 2 → F)) : actSub g⁻¹ (actSub g A) = A := by
  rw [← actSub_mul, inv_mul_cancel, actSub_one]

private theorem g15_actSub_actSub_inv (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (A : Submodule F (Fin 2 → F)) : actSub g (actSub g⁻¹ A) = A := by
  rw [← actSub_mul, mul_inv_cancel, actSub_one]

private theorem g15_conjSub_rootGroup (A : Submodule F (Fin 2 → F))
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    conjSub (rootGroup A A) g = rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A) := by
  ext x
  rw [g15_mem_conjSub, g14_conj_mem g⁻¹ A A x, inv_inv]

private theorem g15_B6_conjSub (A : Submodule F (Fin 2 → F))
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    CFSG.Quasithin.B6.conjSub g (rootGroup A A) = rootGroup (actSub g A) (actSub g A) := by
  ext x
  rw [CFSG.Quasithin.B6.mem_conjSub, g14_conj_mem g A A x]

private theorem g15_Rg_eq : Rg F = rootGroup (Vi F 2 0) (Vi F 2 0) := by
  rw [← Rij_zero_one_eq_Rg]
  unfold Rij
  rw [Vhat_one_eq]

private theorem g15_map_inv_map {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (Y : AddSubgroup U) :
    (Y.map (actU g⁻¹)).map (actU g) = Y := by
  rw [← map_actU_mul, mul_inv_cancel, map_actU_one]

private theorem g15_commU_actSub {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (A B : Submodule F (Fin 2 → F)) :
    commU (U := U) (rootGroup (actSub g A) (actSub g B)) =
      (commU (U := U) (rootGroup A B)).map (actU g) := by
  refine le_antisymm (g14_commU_conj_le (U := U) g A B) ?_
  have h := g14_commU_conj_le (U := U) g⁻¹ (actSub g A) (actSub g B)
  rw [g15_actSub_inv_actSub, g15_actSub_inv_actSub] at h
  have h2 := AddSubgroup.map_mono (f := actU g) h
  rwa [g15_map_inv_map] at h2

private theorem g15_fixU_actSub {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (A B : Submodule F (Fin 2 → F)) :
    fixU (U := U) (rootGroup (actSub g A) (actSub g B)) =
      (fixU (U := U) (rootGroup A B)).map (actU g) := by
  refine le_antisymm ?_ (g14_fixU_map_le (U := U) g A B)
  have h := g14_fixU_map_le (U := U) g⁻¹ (actSub g A) (actSub g B)
  rw [g15_actSub_inv_actSub, g15_actSub_inv_actSub] at h
  have h2 := AddSubgroup.map_mono (f := actU g) h
  rwa [g15_map_inv_map] at h2

private theorem g15_fixU_conjSub {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (A : Submodule F (Fin 2 → F)) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    fixU (U := U) (conjSub (rootGroup A A) g) =
      (fixU (U := U) (rootGroup A A)).map (actU g⁻¹) := by
  rw [g15_conjSub_rootGroup, g15_fixU_actSub]

private theorem g15_commU_conjSub {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (A : Submodule F (Fin 2 → F)) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    commU (U := U) (conjSub (rootGroup A A) g) =
      (commU (U := U) (rootGroup A A)).map (actU g⁻¹) := by
  rw [g15_conjSub_rootGroup, g15_commU_actSub]

private theorem g15_mem_normalizer {A : Submodule F (Fin 2 → F)}
    {k : Matrix.SpecialLinearGroup (Fin 2) F} (hk : actSub k A = A) :
    k ∈ Subgroup.normalizer
      ((rootGroup A A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have hk' : actSub k⁻¹ A = A := by
    calc actSub k⁻¹ A = actSub k⁻¹ (actSub k A) := by rw [hk]
      _ = A := g15_actSub_inv_actSub k A
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have key := g14_conj_mem k⁻¹ A A t
  rw [hk', inv_inv] at key
  simpa using key

private theorem g15_exists_actSub_eq {A B : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (hB : IsPoint B) : ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, actSub x A = B := by
  obtain ⟨g, hg⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  obtain ⟨h, hh⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hB
  refine ⟨h * g⁻¹, ?_⟩
  rw [actSub_mul, ← hg, g15_actSub_inv_actSub, hh]

private theorem g15_sylow_rootGroup [Finite F] [CharP F 2]
    {R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hR : ∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), (P : Subgroup _) = R) :
    ∃ A : Submodule F (Fin 2 → F), IsPoint A ∧ R = rootGroup A A := by
  have hRsyl : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤ := by
    obtain ⟨P, rfl⟩ := hR
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [show ((P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subgroupOf ⊤).index =
      (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).index from
        Subgroup.relIndex_top_right _]
    exact Sylow.not_dvd_index P
  have hRgsyl : CFSG.QuasithinUnique.IsSylowTwoOf (Rg F) ⊤ := by
    refine ⟨le_top, Rg_isPGroup, ?_⟩
    rw [show ((Rg F).subgroupOf ⊤).index = (Rg F).index from Subgroup.relIndex_top_right _]
    exact Rg_index_odd
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hRgsyl hRsyl
  refine ⟨actSub g (Vi F 2 0), isPoint_actSub g (isPoint_Vi 0), ?_⟩
  rw [hg, g15_Rg_eq, g15_B6_conjSub]

private theorem g15_isFlag_self {C : Submodule F (Fin 2 → F)} (hC : IsPoint C) :
    IsFlag C C := by
  refine ⟨hC, ?_, le_rfl⟩
  unfold IsPoint at hC
  unfold IsHyperplane
  omega

private theorem g15_rootGroup_map (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (A : Submodule F (Fin 2 → F)) :
    rootGroup (actSub g A) (actSub g A) = (rootGroup A A).map (MulAut.conj g).toMonoidHom := by
  ext t
  rw [g14_conj_mem g A A t, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ * t * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hs

private theorem g15_inv_lower_left (k : Matrix.SpecialLinearGroup (Fin 2) F) :
    (k⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 1 0 = -k.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp

private theorem g15_eq_one_of_fix_two {A B : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (hB : IsPoint B) (hAB : A ≠ B) {s : Matrix.SpecialLinearGroup (Fin 2) F}
    (hsA : ∀ v ∈ A, s • v = v) (hsB : ∀ v ∈ B, s • v = v) : s = 1 := by
  obtain ⟨m, hm0, hm1⟩ := exists_std_pair hA hB hAB
  have h0 : ∀ v ∈ Vi F 2 0, (m⁻¹ * s * m) • v = v := by
    intro v hv
    have hmv : m • v ∈ A := by
      rw [← hm0]
      exact mem_actSub.2 ⟨v, hv, rfl⟩
    calc (m⁻¹ * s * m) • v = m⁻¹ • (s • (m • v)) := by rw [mul_smul, mul_smul]
      _ = m⁻¹ • (m • v) := by rw [hsA _ hmv]
      _ = v := inv_smul_smul m v
  have h1 : ∀ v ∈ Vi F 2 1, (m⁻¹ * s * m) • v = v := by
    intro v hv
    have hmv : m • v ∈ B := by
      rw [← hm1]
      exact mem_actSub.2 ⟨v, hv, rfl⟩
    calc (m⁻¹ * s * m) • v = m⁻¹ • (s • (m • v)) := by rw [mul_smul, mul_smul]
      _ = m⁻¹ • (m • v) := by rw [hsB _ hmv]
      _ = v := inv_smul_smul m v
  have hconj : m⁻¹ * s * m = 1 := by
    refine SL_ext_basis fun c => ?_
    rw [one_smul]
    obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
    · exact h0 _ (Submodule.mem_span_singleton_self _)
    · exact h1 _ (Submodule.mem_span_singleton_self _)
  calc s = m * (m⁻¹ * s * m) * m⁻¹ := by group
    _ = 1 := by rw [hconj]; group

private theorem g15_sup_eq_top [CharP F 2] {A B : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (hB : IsPoint B) (hAB : A ≠ B) : rootGroup A A ⊔ rootGroup B B = ⊤ := by
  obtain ⟨x, rfl⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  have hB' : IsPoint (actSub x⁻¹ B) := isPoint_actSub _ hB
  obtain ⟨y, hy⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hB'
  have hy10 : y.1 1 0 ≠ 0 := by
    intro h0
    apply hAB
    have h1 : actSub x⁻¹ B = Vi F 2 0 := by
      rw [← hy, actSub_eq_of_lower_left_zero h0]
    calc actSub x (Vi F 2 0) = actSub x (actSub x⁻¹ B) := by rw [h1]
      _ = B := g15_actSub_actSub_inv x B
  have hgen : Rg F ⊔ (Rg F).map (MulAut.conj y).toMonoidHom = ⊤ := by
    have hinv : (y⁻¹).1 1 0 ≠ 0 := by
      rw [g15_inv_lower_left]
      exact neg_ne_zero.2 hy10
    have h := Rg_sup_conj_eq_top y⁻¹ hinv
    rwa [inv_inv] at h
  have hK1 : rootGroup (actSub x (Vi F 2 0)) (actSub x (Vi F 2 0)) =
      (Rg F).map (MulAut.conj x).toMonoidHom := by
    rw [g15_rootGroup_map, g15_Rg_eq]
  have hK2 : rootGroup B B =
      ((Rg F).map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    have hBe : rootGroup B B = rootGroup (actSub x (actSub x⁻¹ B)) (actSub x (actSub x⁻¹ B)) := by
      rw [g15_actSub_actSub_inv]
    rw [hBe, g15_rootGroup_map, ← hy, g15_rootGroup_map, ← g15_Rg_eq]
  rw [hK1, hK2, eq_top_iff]
  intro t _
  have hs : x⁻¹ * t * x ∈ Rg F ⊔ (Rg F).map (MulAut.conj y).toMonoidHom := by
    rw [hgen]
    exact Subgroup.mem_top _
  have ht := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hs
  rw [Subgroup.map_sup] at ht
  have e : (MulAut.conj x).toMonoidHom (x⁻¹ * t * x) = t := by
    simp [MulAut.conj_apply, mul_assoc]
  rwa [e] at ht

private theorem g15_halves_std {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U] [Finite U] [CharP F 2]
    (hsq : ∀ u : U, u + u = 0) {φ : Submodule F (Fin 2 → F) → AddSubgroup U}
    (hφ : G13Hyp F 2 U φ) :
    φ (Vi F 2 0) = commU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) ∧
      φ (Vi F 2 0) = fixU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) := by
  have hH := hφ.halves
  have hcomm : commU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) ≤ φ (Vi F 2 0) := by
    have h := hφ.commU_le (Vi F 2 0) (Vhat F 2 1) (isFlag_Vi_Vhat zero_ne_one)
    rwa [Vhat_one_eq] at h
  have hfix : φ (Vi F 2 0) ≤ fixU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) := by
    have h := hφ.le_fixU (Vi F 2 0) (Vhat F 2 1) (isFlag_Vi_Vhat zero_ne_one) (Vi F 2 0)
      (isPoint_Vi 0) (by rw [Vhat_one_eq])
    rwa [Vhat_one_eq] at h
  obtain ⟨-, -, -, -, hfixY⟩ := exists_equiv_of_halves_core hsq hH
  have hlow : ∀ y ∈ φ (Vi F 2 0),
      y ∈ commU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) := by
    intro y hy
    have h1 : th (1 : F) y = y := hH.toG13Pre.th_one hsq hy
    have h2 : e12 (1 : F) • wmat F • y - wmat F • y ∈
        commU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) := by
      rw [← g15_Rg_eq]
      exact AddSubgroup.subset_closure ⟨e12 1, e12_mem_Rg 1, wmat F • y, rfl⟩
    have h3 : e12 (1 : F) • wmat F • y - wmat F • y = y := h1
    rwa [h3] at h2
  refine ⟨le_antisymm (fun y hy => hlow y hy) hcomm, le_antisymm hfix (fun u hu => ?_)⟩
  have hu' : ∀ t ∈ Rg F, t • u = u := by
    rw [g15_Rg_eq]
    exact hu
  exact hfixY u hu'

private theorem g15_halves {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U] [Finite U] [CharP F 2]
    (hsq : ∀ u : U, u + u = 0) {φ : Submodule F (Fin 2 → F) → AddSubgroup U}
    (hφ : G13Hyp F 2 U φ) {A : Submodule F (Fin 2 → F)} (hA : IsPoint A) :
    φ A = commU (U := U) (rootGroup A A) ∧ φ A = fixU (U := U) (rootGroup A A) := by
  obtain ⟨h, rfl⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  have e := hφ.equivariant h (Vi F 2 0) (isPoint_Vi 0)
  obtain ⟨h1, h2⟩ := g15_halves_std hsq hφ
  constructor
  · rw [e, h1, g15_commU_actSub]
  · rw [e, h2, g15_fixU_actSub]

private theorem g15_conj_G13Hyp {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    {φ : Submodule F (Fin 2 → F) → AddSubgroup U} (hφ : G13Hyp F 2 U φ)
    (h : Matrix.SpecialLinearGroup (Fin 2) F) :
    G13Hyp F 2 U (fun B => (φ (actSub h⁻¹ B)).map (actU h)) := by
  have hinj : Function.Injective (actU (U := U) h) := fun a b hab => MulAction.injective h hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g B hB
    have e1 : actSub h⁻¹ (actSub g B) = actSub (h⁻¹ * g * h) (actSub h⁻¹ B) := by
      rw [← actSub_mul h⁻¹ g B, actSub_mul (h⁻¹ * g) h (actSub h⁻¹ B), g15_actSub_actSub_inv]
    have e2 := hφ.equivariant (h⁻¹ * g * h) (actSub h⁻¹ B) (isPoint_actSub _ hB)
    have e3 : h * (h⁻¹ * g * h) = g * h := by group
    show (φ (actSub h⁻¹ (actSub g B))).map (actU h) =
      ((φ (actSub h⁻¹ B)).map (actU h)).map (actU g)
    rw [e1, e2, ← map_actU_mul, e3, map_actU_mul]
  ·
    intro A B hAB
    obtain h2 := IsFlag.eq_two hAB
    subst h2
    have hA : IsPoint A := hAB.1
    have hCp : IsPoint (actSub h⁻¹ A) := isPoint_actSub _ hA
    have hAe : A = actSub h (actSub h⁻¹ A) := (g15_actSub_actSub_inv h A).symm
    show commU (U := U) (rootGroup A A) ≤ (φ (actSub h⁻¹ A)).map (actU h)
    generalize hC : actSub h⁻¹ A = C at hCp hAe ⊢
    rw [hAe, g15_commU_actSub]
    exact AddSubgroup.map_mono (hφ.commU_le _ _ (g15_isFlag_self hCp))
  ·
    intro A B hAB D hD hDB
    obtain h2 := IsFlag.eq_two hAB
    subst h2
    have hA : IsPoint A := hAB.1
    have hCp : IsPoint (actSub h⁻¹ A) := isPoint_actSub _ hA
    have hAe : A = actSub h (actSub h⁻¹ A) := (g15_actSub_actSub_inv h A).symm
    have hDC : actSub h⁻¹ D ≤ actSub h⁻¹ A := Submodule.map_mono hDB
    show (φ (actSub h⁻¹ D)).map (actU h) ≤ fixU (U := U) (rootGroup A A)
    generalize hC : actSub h⁻¹ A = C at hCp hAe hDC ⊢
    rw [hAe, g15_fixU_actSub]
    exact AddSubgroup.map_mono
      (hφ.le_fixU _ _ (g15_isFlag_self hCp) _ (isPoint_actSub _ hD) hDC)
  ·
    intro A₁ A₂ h₁ h₂ hne
    have hne' : actSub h⁻¹ A₁ ≠ actSub h⁻¹ A₂ := by
      intro heq
      apply hne
      have := congrArg (actSub h) heq
      rwa [g15_actSub_actSub_inv, g15_actSub_actSub_inv] at this
    show (φ (actSub h⁻¹ A₁)).map (actU h) ⊓ (φ (actSub h⁻¹ A₂)).map (actU h) = ⊥
    rw [← AddSubgroup.map_inf _ _ _ hinj,
      hφ.disjoint _ _ (isPoint_actSub _ h₁) (isPoint_actSub _ h₂) hne', AddSubgroup.map_bot]
  ·
    show (⨆ (A : Submodule F (Fin 2 → F)) (_ : IsPoint A), (φ (actSub h⁻¹ A)).map (actU h)) = ⊤
    set T : AddSubgroup U :=
      ⨆ (A : Submodule F (Fin 2 → F)) (_ : IsPoint A), (φ (actSub h⁻¹ A)).map (actU h) with hT
    have key : (⨆ (C : Submodule F (Fin 2 → F)) (_ : IsPoint C), φ C) ≤ T.comap (actU h) := by
      refine iSup₂_le fun C hC => ?_
      intro y hy
      have hmem : (φ C).map (actU h) ≤ T := by
        have := le_iSup₂
          (f := fun (A : Submodule F (Fin 2 → F)) (_ : IsPoint A) =>
            (φ (actSub h⁻¹ A)).map (actU h)) (actSub h C) (isPoint_actSub h hC)
        rwa [g15_actSub_inv_actSub] at this
      exact hmem ⟨y, hy, rfl⟩
    rw [hφ.iSup_eq] at key
    refine eq_top_iff.2 fun u _ => ?_
    have hu := key (AddSubgroup.mem_top (h⁻¹ • u))
    rw [AddSubgroup.mem_comap] at hu
    have e : actU (U := U) h (h⁻¹ • u) = u := by simp [actU]
    rw [e] at hu
    exact hu

private theorem g15_card_eq {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    {φ : Submodule F (Fin 2 → F) → AddSubgroup U} (hφ : G13Hyp F 2 U φ)
    {A : Submodule F (Fin 2 → F)} (hA : IsPoint A) :
    Nat.card (φ A) = Nat.card (φ (Vi F 2 0)) := by
  obtain ⟨h, rfl⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  rw [hφ.equivariant h _ (isPoint_Vi 0)]
  exact (Nat.card_congr (AddSubgroup.equivMapOfInjective _ _
    (fun a b hab => MulAction.injective h hab)).toEquiv).symm

private theorem g15_mul_self_of_mem [CharP F 2] {A : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    {t : Matrix.SpecialLinearGroup (Fin 2) F} (ht : t ∈ rootGroup A A) : t * t = 1 := by
  obtain ⟨g, rfl⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  have h1 : g⁻¹ * t * g ∈ rootGroup (Vi F 2 0) (Vi F 2 0) := (g14_conj_mem g _ _ t).1 ht
  rw [← g15_Rg_eq] at h1
  obtain ⟨b, hb⟩ := mem_Rg.1 h1
  calc t * t = g * (g⁻¹ * t * g) * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = g * (e12 b * e12 b) * g⁻¹ := by rw [hb]; group
    _ = 1 := by rw [e12_mul_self]; group

private theorem g15_fix_point [CharP F 2] {A B : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (hB : IsPoint B) {s : Matrix.SpecialLinearGroup (Fin 2) F} (hs : s ∈ rootGroup A A)
    (hs1 : s ≠ 1) (hsB : actSub s B = B) : B = A := by
  by_contra hBA
  obtain ⟨d, hd0, hdB⟩ := exists_gen hB
  have hsd : s • d ∈ B := by
    rw [← hsB]
    exact mem_actSub.2 ⟨d, (hdB d).2 ⟨1, (one_smul F d).symm⟩, rfl⟩
  obtain ⟨c, hc⟩ := (hdB (s • d)).1 hsd
  by_cases hc1 : c = 1
  · subst hc1
    apply hs1
    refine g15_eq_one_of_fix_two hA hB (Ne.symm hBA) (fun v hv => hs.2 v hv) ?_
    intro v hv
    obtain ⟨c', rfl⟩ := (hdB v).1 hv
    rw [g14_smul_scalar, hc, one_smul]
  · have hcd : (c - 1) • d ∈ A := by
      have h2 : (c - 1) • d = s • d - d := by rw [sub_smul, one_smul, ← hc]
      rw [h2]
      exact hs.1 d
    have hdA : d ∈ A := by
      have h3 := A.smul_mem (c - 1)⁻¹ hcd
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc1), one_smul] at h3
    have hBA' : B ≤ A := fun w hw => by
      obtain ⟨c', rfl⟩ := (hdB w).1 hw
      exact A.smul_mem c' hdA
    have hfin : Module.finrank F B = Module.finrank F A := by
      have h1 : Module.finrank F B = 1 := hB
      have h2 : Module.finrank F A = 1 := hA
      omega
    exact hBA (Submodule.eq_of_le_of_finrank_eq hBA' hfin)

private theorem g15_three {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U] [CharP F 2]
    {A : Submodule F (Fin 2 → F)} (hA : IsPoint A) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (Y : AddSubgroup U)
    (hN : ∀ x ∈ Subgroup.normalizer
      ((rootGroup A A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)), ∀ y ∈ Y, x • y ∈ Y)
    (hc : commU (U := U) (rootGroup A A) ≤ Y) (hf : Y ≤ fixU (U := U) (rootGroup A A))
    (hI : IsCompl Y (Y.map (actU g⁻¹))) :
    ∃ φ : Submodule F (Fin 2 → F) → AddSubgroup U, G13Hyp F 2 U φ ∧ φ A = Y := by
  obtain ⟨h, hh⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  have h1 : actSub h⁻¹ A = Vi F 2 0 := by rw [← hh, g15_actSub_inv_actSub]
  have hinjh : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Injective (actU (U := U) k) := fun k a b hab => MulAction.injective k hab
  set Y₀ : AddSubgroup U := Y.map (actU h⁻¹) with hY₀
  set g₀ : Matrix.SpecialLinearGroup (Fin 2) F := h⁻¹ * g⁻¹ * h with hg₀
  have hinv : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F,
      actSub k (Vi F 2 0) = Vi F 2 0 → ∀ y ∈ Y₀, k • y ∈ Y₀ := by
    intro k hk y hy
    obtain ⟨y₁, hy₁, rfl⟩ := AddSubgroup.mem_map.1 hy
    have hAk : actSub (h * k * h⁻¹) A = A := by
      rw [actSub_mul, actSub_mul, h1, hk, hh]
    have hk' := hN (h * k * h⁻¹) (g15_mem_normalizer hAk) y₁ hy₁
    refine AddSubgroup.mem_map.2 ⟨(h * k * h⁻¹) • y₁, hk', ?_⟩
    show h⁻¹ • ((h * k * h⁻¹) • y₁) = k • h⁻¹ • y₁
    rw [mul_smul, mul_smul, inv_smul_smul]
  have hcomm : commU (U := U) (Rij F (0 : Fin 2) 1) ≤ Y₀ := by
    have e : commU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) =
        (commU (U := U) (rootGroup A A)).map (actU h⁻¹) := by
      rw [← h1, g15_commU_actSub]
    rw [Rij_zero_one_eq_Rg, g15_Rg_eq, e]
    exact AddSubgroup.map_mono hc
  have hfix : Y₀ ≤ fixU (U := U) (Rij F (0 : Fin 2) 1) := by
    have e : fixU (U := U) (rootGroup (Vi F 2 0) (Vi F 2 0)) =
        (fixU (U := U) (rootGroup A A)).map (actU h⁻¹) := by
      rw [← h1, g15_fixU_actSub]
    rw [Rij_zero_one_eq_Rg, g15_Rg_eq, e]
    exact AddSubgroup.map_mono hf
  have hgY : Y₀.map (actU g₀) = (Y.map (actU g⁻¹)).map (actU h⁻¹) := by
    have e : g₀ * h⁻¹ = h⁻¹ * g⁻¹ := by rw [hg₀]; group
    rw [hY₀, ← map_actU_mul g₀ h⁻¹ Y, e, map_actU_mul h⁻¹ g⁻¹ Y]
  have hdisj : Y₀ ⊓ Y₀.map (actU g₀) = ⊥ := by
    rw [hgY, hY₀, ← AddSubgroup.map_inf _ _ _ (hinjh h⁻¹), disjoint_iff.1 hI.disjoint,
      AddSubgroup.map_bot]
  have hsup : Y₀ ⊔ Y₀.map (actU g₀) = ⊤ := by
    rw [hgY, hY₀, ← AddSubgroup.map_sup, hI.sup_eq_top]
    refine eq_top_iff.2 fun u _ => AddSubgroup.mem_map.2 ⟨h • u, AddSubgroup.mem_top _, ?_⟩
    simp [actU]
  obtain ⟨φ', hφ', hφ'V⟩ := exists_G13Hyp_of_halves Y₀ g₀ hinv hcomm hfix hdisj hsup
  refine ⟨fun B => (φ' (actSub h⁻¹ B)).map (actU h), g15_conj_G13Hyp hφ' h, ?_⟩
  show (φ' (actSub h⁻¹ A)).map (actU h) = Y
  rw [h1, hφ'V, hY₀, g15_map_inv_map]

private theorem g15_quadratic [CharP F 2] {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (hsq : ∀ u : U, u + u = 0) {A : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hI : IsCompl (fixU (U := U) (rootGroup A A)) (fixU (U := U) (conjSub (rootGroup A A) g))) :
    commU (U := U) (rootGroup A A) ≤ fixU (U := U) (rootGroup A A) := by
  by_cases hgN : g ∈ Subgroup.normalizer
      ((rootGroup A A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))
  ·
    have hconj : conjSub (rootGroup A A) g = rootGroup A A := by
      ext t
      rw [g15_mem_conjSub]
      have := Subgroup.mem_normalizer_iff.1 hgN t
      simpa using this.symm
    rw [hconj] at hI
    have hX : fixU (U := U) (rootGroup A A) = ⊤ := by
      have := hI.sup_eq_top
      rwa [sup_idem] at this
    intro u _
    rw [hX]
    exact AddSubgroup.mem_top u
  · have hB : IsPoint (actSub g⁻¹ A) := isPoint_actSub _ hA
    have hAB : A ≠ actSub g⁻¹ A := by
      intro heq
      apply hgN
      exact (Subgroup.inv_mem_iff _).1 (g15_mem_normalizer heq.symm)
    rw [g15_conjSub_rootGroup] at hI
    have hQ : ∀ s ∈ rootGroup A A, s ≠ 1 → ∀ w : U, s • w = w →
        ∀ r ∈ rootGroup A A, r • w = w := by
      intro s hs hs1 w hw
      have hw' : w ∈ fixU (U := U) (rootGroup A A) ⊔
          fixU (U := U) (rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A)) := by
        rw [hI.sup_eq_top]
        exact AddSubgroup.mem_top w
      obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.1 hw'
      have hsb : s • b = b := by
        have e : s • w = a + s • b := by rw [← hab, smul_add, ha s hs]
        rw [hw] at e
        exact add_left_cancel (e.symm.trans hab.symm)
      let H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := MulAction.stabilizer _ b
      have hRgH : rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A) ≤ H := by
        intro t ht
        exact MulAction.mem_stabilizer_iff.2 (hb t ht)
      have hsH : s ∈ H := MulAction.mem_stabilizer_iff.2 hsb
      have hconjH : (rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A)).map
          (MulAut.conj s).toMonoidHom ≤ H := by
        rintro _ ⟨t, ht, rfl⟩
        refine MulAction.mem_stabilizer_iff.2 ?_
        have hs' : s⁻¹ • b = b := by
          rw [inv_smul_eq_iff]
          exact hsb.symm
        show (s * t * s⁻¹) • b = b
        rw [mul_smul, mul_smul, hs', hb t ht, hsb]
      have hsB : actSub s (actSub g⁻¹ A) ≠ actSub g⁻¹ A := by
        intro heq
        exact hAB (g15_fix_point hA hB hs hs1 heq).symm
      have hgen := g15_sup_eq_top hB (isPoint_actSub s hB) (Ne.symm hsB)
      rw [← g15_rootGroup_map] at hconjH
      have hfull : H = ⊤ := by
        rw [eq_top_iff, ← hgen]
        exact sup_le hRgH hconjH
      have hbR : b ∈ fixU (U := U) (rootGroup A A) := fun t _ =>
        MulAction.mem_stabilizer_iff.1 (show t ∈ H from by rw [hfull]; exact Subgroup.mem_top t)
      have hb0 : b = 0 := by
        have hdisj := disjoint_iff.1 hI.disjoint
        have hmem : b ∈ fixU (U := U) (rootGroup A A) ⊓
            fixU (U := U) (rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A)) := ⟨hbR, hb⟩
        rw [hdisj] at hmem
        exact AddSubgroup.mem_bot.1 hmem
      have hwa : w = a := by rw [← hab, hb0, add_zero]
      rw [hwa]
      exact ha
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, u, rfl⟩
    by_cases ht1 : t = 1
    · subst ht1
      simp
    · have htt : t * t = 1 := g15_mul_self_of_mem hA ht
      have hfixt : t • (t • u - u) = t • u - u := by
        rw [smul_sub, ← mul_smul, htt, one_smul]
        have e : u - t • u = -(t • u - u) := by abel
        rw [e]
        exact neg_eq_iff_add_eq_zero.2 (hsq _)
      exact hQ t ht ht1 _ hfixt

private theorem g15_compl {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U] [Finite U] [CharP F 2]
    (hsq : ∀ u : U, u + u = 0) {φ : Submodule F (Fin 2 → F) → AddSubgroup U}
    (hφ : G13Hyp F 2 U φ) {A : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hgN : g ∉ Subgroup.normalizer
      ((rootGroup A A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))) :
    IsCompl (commU (U := U) (rootGroup A A)) (commU (U := U) (conjSub (rootGroup A A) g)) := by
  obtain ⟨hcA, -⟩ := g15_halves hsq hφ hA
  have hB : IsPoint (actSub g⁻¹ A) := isPoint_actSub _ hA
  have hcB : commU (U := U) (conjSub (rootGroup A A) g) = φ (actSub g⁻¹ A) := by
    rw [g15_conjSub_rootGroup, (g15_halves hsq hφ hB).1]
  have hAB : A ≠ actSub g⁻¹ A := by
    intro heq
    apply hgN
    exact (Subgroup.inv_mem_iff _).1 (g15_mem_normalizer heq.symm)
  rw [hcB, ← hcA]
  refine ⟨disjoint_iff.2 (hφ.disjoint A _ hA hB hAB), codisjoint_iff.2 ?_⟩
  set Z : AddSubgroup U := φ A ⊔ φ (actSub g⁻¹ A) with hZ
  have hZA : φ A ≤ Z := le_sup_left
  have hZB : φ (actSub g⁻¹ A) ≤ Z := le_sup_right
  have hstab : ∀ (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (M : AddSubgroup U),
      (∀ t ∈ K, ∀ u : U, t • u - u ∈ M) → M ≤ Z → ∀ t ∈ K, ∀ z ∈ Z, t • z ∈ Z := by
    intro K M hK hMZ t ht z hz
    have h1 : t • z = z + (t • z - z) := by abel
    rw [h1]
    exact Z.add_mem hz (hMZ (hK t ht z))
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { carrier := {t | ∀ z ∈ Z, t • z ∈ Z ∧ t⁻¹ • z ∈ Z}
      one_mem' := fun z hz => by simpa using And.intro hz hz
      mul_mem' := fun {t s} ht hs z hz => ⟨by rw [mul_smul]; exact (ht _ (hs z hz).1).1,
        by rw [mul_inv_rev, mul_smul]; exact (hs _ (ht z hz).2).2⟩
      inv_mem' := fun {t} ht z hz => ⟨(ht z hz).2, by rw [inv_inv]; exact (ht z hz).1⟩ }
  have hSmem : ∀ t, t ∈ S ↔ ∀ z ∈ Z, t • z ∈ Z ∧ t⁻¹ • z ∈ Z := fun t => Iff.rfl
  have hRS : rootGroup A A ≤ S := by
    intro t ht
    rw [hSmem]
    intro z hz
    have hM : commU (U := U) (rootGroup A A) ≤ Z := le_trans (le_of_eq hcA.symm) hZA
    have hK : ∀ t ∈ rootGroup A A, ∀ u : U, t • u - u ∈ commU (U := U) (rootGroup A A) :=
      fun t ht u => AddSubgroup.subset_closure ⟨t, ht, u, rfl⟩
    constructor
    · exact hstab _ _ hK hM t ht z hz
    · exact hstab _ _ hK hM t⁻¹ (inv_mem ht) z hz
  have hRS' : rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A) ≤ S := by
    intro t ht
    rw [hSmem]
    intro z hz
    have hc := (g15_halves hsq hφ hB).1
    have hM : commU (U := U) (rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A)) ≤ Z :=
      le_trans (le_of_eq hc.symm) hZB
    have hK : ∀ t ∈ rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A), ∀ u : U,
        t • u - u ∈ commU (U := U) (rootGroup (actSub g⁻¹ A) (actSub g⁻¹ A)) :=
      fun t ht u => AddSubgroup.subset_closure ⟨t, ht, u, rfl⟩
    constructor
    · exact hstab _ _ hK hM t ht z hz
    · exact hstab _ _ hK hM t⁻¹ (inv_mem ht) z hz
  have hTop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ S := by
    rw [← g15_sup_eq_top hA hB hAB]
    exact sup_le hRS hRS'
  have hall : ∀ t : Matrix.SpecialLinearGroup (Fin 2) F, ∀ z ∈ Z, t • z ∈ Z :=
    fun t z hz => ((hSmem t).1 (hTop (Subgroup.mem_top t)) z hz).1
  have hPZ : ∀ P : Submodule F (Fin 2 → F), IsPoint P → φ P ≤ Z := by
    intro P hP
    obtain ⟨x, rfl⟩ := g15_exists_actSub_eq hA hP
    rw [hφ.equivariant x A hA]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := AddSubgroup.mem_map.1 hy
    exact hall x y' (hZA hy')
  rw [eq_top_iff, ← hφ.iSup_eq]
  exact iSup₂_le fun P hP => hPZ P hP

end G15Help



section G15Four

variable {F : Type} [Field F]

private theorem g15_aux_trace [CharP F 2] {p q r s v0 v1 : F} (hdet : p * s - q * r = 1)
    (h0 : p * v0 + q * v1 = v0) (h1 : r * v0 + s * v1 = v1) (hv : v0 ≠ 0 ∨ v1 ≠ 0) :
    p + s = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e0 : (p + 1) * v0 = q * v1 := by linear_combination h0 + (v0 - q * v1) * h2
  have e1 : (s + 1) * v1 = r * v0 := by linear_combination h1 + (v1 - r * v0) * h2
  have key : (p + s) * (v0 * v1) = 0 := by
    linear_combination ((s + 1) * v1) * e0 + (q * v1) * e1 - (v0 * v1) * hdet - (v0 * v1) * h2
  by_cases hv0 : v0 = 0
  · have hv1 : v1 ≠ 0 := by
      rcases hv with h | h
      · exact absurd hv0 h
      · exact h
    have h3 : (s + 1) * v1 = 0 := by rw [e1, hv0, mul_zero]
    have hs1 : s = 1 := by
      have h4 : s + 1 = 0 := (mul_eq_zero.1 h3).resolve_right hv1
      linear_combination h4 - h2
    have h5 : q * v1 = 0 := by
      have h6 := e0
      rw [hv0, mul_zero] at h6
      exact h6.symm
    have hq : q = 0 := (mul_eq_zero.1 h5).resolve_right hv1
    have hp : p = 1 := by
      rw [hq, zero_mul, sub_zero, hs1, mul_one] at hdet
      exact hdet
    rw [hp, hs1]
    linear_combination h2
  · by_cases hv1 : v1 = 0
    · have h3 : (p + 1) * v0 = 0 := by rw [e0, hv1, mul_zero]
      have hp : p = 1 := by
        have h4 : p + 1 = 0 := (mul_eq_zero.1 h3).resolve_right hv0
        linear_combination h4 - h2
      have h5 : r * v0 = 0 := by
        have h6 := e1
        rw [hv1, mul_zero] at h6
        exact h6.symm
      have hr : r = 0 := (mul_eq_zero.1 h5).resolve_right hv0
      have hs1 : s = 1 := by
        rw [hr, mul_zero, sub_zero, hp, one_mul] at hdet
        exact hdet
      rw [hp, hs1]
      linear_combination h2
    · exact (mul_eq_zero.1 key).resolve_right (mul_ne_zero hv0 hv1)

private theorem g15_sq_of_fix [CharP F 2] {x : Matrix.SpecialLinearGroup (Fin 2) F}
    {w : Fin 2 → F} (hw : x • w = w) (hw0 : w ≠ 0) : x * x = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : x.1 0 0 * x.1 1 1 - x.1 0 1 * x.1 1 0 = 1 := by
    have := x.2
    rw [Matrix.det_fin_two] at this
    exact this
  have h0 : x.1 0 0 * w 0 + x.1 0 1 * w 1 = w 0 := by
    have := congrFun hw 0
    simp only [CFSG.Quasithin.G1.smul_eq_mulVec', Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at this
    exact this
  have h1 : x.1 1 0 * w 0 + x.1 1 1 * w 1 = w 1 := by
    have := congrFun hw 1
    simp only [CFSG.Quasithin.G1.smul_eq_mulVec', Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at this
    exact this
  have hv : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw0 (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
  have htr := g15_aux_trace hdet h0 h1 hv
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination (x.1 0 0) * htr - hdet - h2
      | linear_combination (x.1 1 1) * htr - hdet - h2
      | linear_combination (x.1 0 1) * htr
      | linear_combination (x.1 1 0) * htr

private theorem g15_fix_free_odd [CharP F 2] {x : Matrix.SpecialLinearGroup (Fin 2) F}
    (hx1 : x ≠ 1) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) (w : Fin 2 → F) (hw : x • w = w) :
    w = 0 := by
  by_contra hw0
  have hsq := g15_sq_of_fix hw hw0
  obtain ⟨k, rfl⟩ := hm
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hsq
  have h3 : x ^ (2 * k + 1) = x := by rw [pow_succ, pow_mul, hx2, one_pow, one_mul]
  exact hx1 (h3.symm.trans hxm)

private theorem g15_odd_nsmul {U : Type} [AddCommGroup U] (hsq : ∀ u : U, u + u = 0) (u : U) :
    ∀ k : ℕ, (2 * k + 1) • u = u := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, add_nsmul, ih, two_nsmul, hsq, add_zero]

private theorem g15_range_all {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (hsq : ∀ u : U, u + u = 0) {y : Matrix.SpecialLinearGroup (Fin 2) F} {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) (hC : ∀ v : U, y • v = v → v = 0) (u : U) :
    u ∈ AddMonoidHom.range (actU (U := U) y - AddMonoidHom.id U) := by
  have hgen : ∀ v : U, y • v - v ∈ AddMonoidHom.range (actU (U := U) y - AddMonoidHom.id U) :=
    fun v => ⟨v, rfl⟩
  have hTinv : ∀ w ∈ AddMonoidHom.range (actU (U := U) y - AddMonoidHom.id U),
      y • w ∈ AddMonoidHom.range (actU (U := U) y - AddMonoidHom.id U) := by
    rintro w ⟨v, rfl⟩
    refine ⟨y • v, ?_⟩
    show y • (y • v) - y • v = y • (y • v - v)
    rw [smul_sub]
  have hdiff : ∀ i : ℕ, ∀ v : U,
      y ^ i • v - v ∈ AddMonoidHom.range (actU (U := U) y - AddMonoidHom.id U) := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      have e : y ^ (i + 1) • v - v = y • (y ^ i • v - v) + (y • v - v) := by
        rw [pow_succ', mul_smul, smul_sub]
        abel
      rw [e]
      exact AddSubgroup.add_mem _ (hTinv _ (ih v)) (hgen v)
  have hs1 : ∑ i ∈ Finset.range m, y ^ (i + 1) • u =
      ∑ i ∈ Finset.range m, y ^ i • u := by
    have h1 := Finset.sum_range_succ' (fun i => y ^ i • u) m
    have h2 := Finset.sum_range_succ (fun i => y ^ i • u) m
    simp only [pow_zero, one_smul, hym] at h1 h2
    have h3 : (∑ i ∈ Finset.range m, y ^ (i + 1) • u) + u =
        (∑ i ∈ Finset.range m, y ^ i • u) + u := by
      rw [← h1, h2]
    exact add_right_cancel h3
  have hyN : y • (∑ i ∈ Finset.range m, y ^ i • u) = ∑ i ∈ Finset.range m, y ^ i • u := by
    rw [Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun i _ => (show y • y ^ i • u = y ^ (i + 1) • u by
      rw [← mul_smul, ← pow_succ']))]
    exact hs1
  have hN0 : ∑ i ∈ Finset.range m, y ^ i • u = 0 := hC _ hyN
  have hm' : m • u = u := by
    obtain ⟨k, rfl⟩ := hm
    exact g15_odd_nsmul hsq u k
  have hsum : ∑ i ∈ Finset.range m, (y ^ i • u - u) = -u := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, hm', hN0, zero_sub]
  have hmem : ∑ i ∈ Finset.range m, (y ^ i • u - u) ∈
      AddMonoidHom.range (actU (U := U) y - AddMonoidHom.id U) :=
    AddSubgroup.sum_mem _ fun i _ => hdiff i u
  rw [hsum] at hmem
  simpa using AddSubgroup.neg_mem _ hmem

private theorem g15_claim {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (hsq : ∀ u : U, u + u = 0) {y ρ : Matrix.SpecialLinearGroup (Fin 2) F}
    (hC : ∀ v : U, y • v = v → v = 0)
    (hT : ∀ u : U, u ∈ AddMonoidHom.range (actU (U := U) y - AddMonoidHom.id U))
    (hρy : ρ * y = y⁻¹ * ρ) {c : U} (hc : ρ • c = c) : ∃ u : U, c = ρ • u - u := by
  obtain ⟨u0, hu0⟩ := hT c
  have hu0' : y • u0 - u0 = c := hu0
  have h1 : y⁻¹ • (ρ • u0) - ρ • u0 = y • u0 - u0 := by
    have e : ρ • (y • u0 - u0) = y⁻¹ • (ρ • u0) - ρ • u0 := by
      rw [smul_sub, ← mul_smul, hρy, mul_smul]
    rw [← e, hu0', hc]
  have h2 : ρ • u0 - y • (ρ • u0) = y • (y • u0) - y • u0 := by
    have h4 := congrArg (fun v => y • v) h1
    simp only [smul_sub, smul_inv_smul] at h4
    exact h4
  have h3 : y • (y • u0 - ρ • u0) - (y • u0 - ρ • u0) = 0 := by
    have e : y • (y • u0 - ρ • u0) - (y • u0 - ρ • u0) =
        (y • (y • u0) - y • u0) + (ρ • u0 - y • (ρ • u0)) := by
      rw [smul_sub]
      abel
    rw [e, h2]
    exact hsq _
  have hyw : y • u0 = ρ • u0 := sub_eq_zero.1 (hC _ (sub_eq_zero.1 h3))
  exact ⟨u0, by rw [← hu0', hyw]⟩

private theorem g15_fix_conj {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hC : ∀ v : U, x • v = v → v = 0)
    (z : Matrix.SpecialLinearGroup (Fin 2) F) (v : U) (hv : (z * x * z⁻¹) • v = v) : v = 0 := by
  have e : z⁻¹ • (z * x * z⁻¹) • v = x • z⁻¹ • v := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  rw [hv] at e
  have h0 : z⁻¹ • v = 0 := hC _ e.symm
  calc v = z • z⁻¹ • v := (smul_inv_smul z v).symm
    _ = 0 := by rw [h0, smul_zero]

private theorem g15_entries_decomp [CharP F 2] (y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hd : y.1 1 0 ≠ 0) :
    ∃ (b : F) (t : Matrix.SpecialLinearGroup (Fin 2) F) (P : Submodule F (Fin 2 → F)),
      IsPoint P ∧ y = CFSG.Quasithin.SL2Model.e12 b * t ∧ t * t = 1 ∧ t ∈ rootGroup P P := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : y.1 0 0 * y.1 1 1 - y.1 0 1 * y.1 1 0 = 1 := by
    have := y.2
    rw [Matrix.det_fin_two] at this
    exact this
  obtain ⟨e, he⟩ : ∃ e : F, y.1 1 0 * e = 1 := ⟨(y.1 1 0)⁻¹, mul_inv_cancel₀ hd⟩
  have ht_det : (1 + (y.1 1 1 + 1)) * (1 + (y.1 1 1 + 1)) -
      (y.1 1 1 + 1) ^ 2 * e * y.1 1 0 = 1 := by
    linear_combination (y.1 1 1 + 1) * h2 - (y.1 1 1 + 1) ^ 2 * he
  let t : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1 + (y.1 1 1 + 1), (y.1 1 1 + 1) ^ 2 * e; y.1 1 0, 1 + (y.1 1 1 + 1)],
      by rw [Matrix.det_fin_two_of]; exact ht_det⟩
  have ht : (t : Matrix (Fin 2) (Fin 2) F) =
      !![1 + (y.1 1 1 + 1), (y.1 1 1 + 1) ^ 2 * e; y.1 1 0, 1 + (y.1 1 1 + 1)] := rfl
  refine ⟨(y.1 0 0 + y.1 1 1) * e, t, Submodule.span F {![y.1 1 1 + 1, y.1 1 0]}, ?_, ?_, ?_, ?_⟩
  ·
    have hne : (![y.1 1 1 + 1, y.1 1 0] : Fin 2 → F) ≠ 0 := by
      intro h0
      apply hd
      exact congrFun h0 1
    unfold IsPoint
    exact finrank_span_singleton hne
  ·
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ht, CFSG.Quasithin.SL2Model.e12_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (-(y.1 1 1 + 1)) * h2 - (y.1 0 0 + y.1 1 1) * he
        | linear_combination (-1 : F) * h2
        | linear_combination (-e) * hdet - (y.1 0 1) * he
            + (-(e * (1 + y.1 1 1 ^ 2 + 2 * y.1 1 1 + y.1 0 0))) * h2
        | ring
  ·
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ht, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (y.1 1 1 ^ 2 + 3 * y.1 1 1 + 2) * h2 + (y.1 1 1 + 1) ^ 2 * he
        | linear_combination ((1 + (y.1 1 1 + 1)) * (y.1 1 1 + 1) ^ 2 * e) * h2
        | linear_combination ((y.1 1 0) * (1 + (y.1 1 1 + 1))) * h2
        | linear_combination h2
        | ring
  ·
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have hvec : t • v - v = (((y.1 1 0) * v 0 + (y.1 1 1 + 1) * v 1) * e) •
          (![y.1 1 1 + 1, y.1 1 0] : Fin 2 → F) := by
        funext i
        fin_cases i
        · simp [CFSG.Quasithin.G1.smul_eq_mulVec', ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          linear_combination (-(y.1 1 1 + 1) * v 0) * he
        · simp [CFSG.Quasithin.G1.smul_eq_mulVec', ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          linear_combination (-((y.1 1 0) * v 0 + (y.1 1 1 + 1) * v 1)) * he
      rw [hvec]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 hv
      funext i
      fin_cases i
      · simp [CFSG.Quasithin.G1.smul_eq_mulVec', ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        linear_combination (μ * (y.1 1 1 + 1) ^ 2) * he + (μ * (y.1 1 1 + 1) ^ 2) * h2
      · simp [CFSG.Quasithin.G1.smul_eq_mulVec', ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        linear_combination (μ * (y.1 1 1 + 1) * y.1 1 0) * h2

private theorem g15_lower_left_conj [CharP F 2] (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x ≠ 1) : ∃ z : Matrix.SpecialLinearGroup (Fin 2) F, (z * x * z⁻¹).1 1 0 ≠ 0 := by
  by_cases h10 : x.1 1 0 = 0
  · by_cases h01 : x.1 0 1 = 0
    ·
      have hdet : x.1 0 0 * x.1 1 1 - x.1 0 1 * x.1 1 0 = 1 := by
        have := x.2
        rw [Matrix.det_fin_two] at this
        exact this
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have hu : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [Matrix.det_fin_two_of]
        ring
      obtain ⟨u, hu1⟩ : ∃ u : Matrix.SpecialLinearGroup (Fin 2) F,
          (u : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := ⟨⟨!![1, 0; 1, 1], hu⟩, rfl⟩
      refine ⟨u, ?_⟩
      have hval : (u * x * u⁻¹).1 1 0 = x.1 0 0 - x.1 1 1 := by
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
          Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h10, h01, hu1,
          Matrix.vecMul, dotProduct]
        try ring
      rw [hval]
      intro hsub
      apply hx
      have h11 : x.1 1 1 = x.1 0 0 := by
        linear_combination -hsub
      have hsq : (x.1 0 0 - 1) * (x.1 0 0 - 1) = 0 := by
        rw [h10, h01, h11] at hdet
        linear_combination hdet + (1 - x.1 0 0) * h2
      have h00 : x.1 0 0 = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 hsq)
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h10, h01, h11, h00]
    · refine ⟨wmat F, ?_⟩
      have hw : (wmat F * x * (wmat F)⁻¹).1 1 0 = x.1 0 1 := by
        simp [wmat_inv, Matrix.SpecialLinearGroup.coe_mul, wmat_coe, Matrix.mul_apply,
          Fin.sum_univ_two, h10, Matrix.vecMul, dotProduct]
      rw [hw]
      exact h01
  · refine ⟨1, ?_⟩
    simpa using h10

private theorem g15_fixed_comm {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (hsq : ∀ u : U, u + u = 0) {ρ : Matrix.SpecialLinearGroup (Fin 2) F} (hρ : ρ * ρ = 1) (w : U) :
    ρ • (ρ • w - w) = ρ • w - w := by
  rw [smul_sub, ← mul_smul, hρ, one_smul]
  have e : w - ρ • w = -(ρ • w - w) := by abel
  rw [e]
  exact neg_eq_iff_add_eq_zero.2 (hsq _)

private theorem g15_decomp {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (hsq : ∀ u : U, u + u = 0) {y r t : Matrix.SpecialLinearGroup (Fin 2) F} {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) (hC : ∀ v : U, y • v = v → v = 0) (hy : y = r * t) (hr2 : r * r = 1)
    (ht2 : t * t = 1) {R R' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hr : r ∈ R)
    (ht : t ∈ R') (hR : commU (U := U) R ≤ fixU (U := U) R)
    (hR' : commU (U := U) R' ≤ fixU (U := U) R') :
    IsCompl (fixU (U := U) R) (fixU (U := U) R') := by
  have hyinv : y⁻¹ = t * r := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hy]
    calc r * t * (t * r) = r * (t * t) * r := by group
      _ = 1 := by rw [ht2, mul_one, hr2]
  have hry : r * y = y⁻¹ * r := by
    rw [hyinv, hy]
    calc r * (r * t) = (r * r) * t := by group
      _ = t * r * r := by rw [hr2, one_mul, mul_assoc, hr2, mul_one]
  have hty : t * y = y⁻¹ * t := by
    rw [hyinv, hy]
    calc t * (r * t) = t * r * t := by group
      _ = t * r * t := rfl
  have hT := g15_range_all hsq hm hym hC
  have hfixR : ∀ c : U, r • c = c → c ∈ fixU (U := U) R := by
    intro c hc
    obtain ⟨u, rfl⟩ := g15_claim hsq hC hT hry hc
    exact hR (AddSubgroup.subset_closure ⟨r, hr, u, rfl⟩)
  have hfixR' : ∀ c : U, t • c = c → c ∈ fixU (U := U) R' := by
    intro c hc
    obtain ⟨u, rfl⟩ := g15_claim hsq hC hT hty hc
    exact hR' (AddSubgroup.subset_closure ⟨t, ht, u, rfl⟩)
  refine ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
  · rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu1, hu2⟩ := AddSubgroup.mem_inf.1 hu
    have hyu : y • u = u := by
      rw [hy, mul_smul, hu2 t ht, hu1 r hr]
    exact AddSubgroup.mem_bot.2 (hC u hyu)
  · rw [eq_top_iff]
    intro u _
    obtain ⟨u1, hu1⟩ := hT u
    have hu1' : y • u1 - u1 = u := hu1
    have hsplit : u = (r • (t • u1) - t • u1) + (t • u1 - u1) := by
      have : r • (t • u1) = y • u1 := by rw [hy, mul_smul]
      rw [← hu1']
      rw [this]
      abel
    rw [hsplit]
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (hfixR _ ?_))
      (AddSubgroup.mem_sup_right (hfixR' _ ?_))
    · exact g15_fixed_comm hsq hr2 (t • u1)
    · exact g15_fixed_comm hsq ht2 u1

private theorem g15_order_three [CharP F 2] :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 ∧ Odd (orderOf x) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h2
  obtain ⟨x, hx⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 2) F,
      (x : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := ⟨⟨_, hdet⟩, rfl⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hx]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h2
  have hx1 : x ≠ 1 := by
    intro h
    have := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [hx] at this
  refine ⟨x, hx1, ?_⟩
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.1 h1) hx1
  · rw [h3]
    decide

private theorem g15_exists_ne_one [CharP F 2] {A : Submodule F (Fin 2 → F)} (hA : IsPoint A) :
    ∃ s ∈ rootGroup A A, s ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  refine ⟨g * CFSG.Quasithin.SL2Model.e12 1 * g⁻¹, ?_, ?_⟩
  · rw [← hg]
    refine (g14_conj_mem g (Vi F 2 0) (Vi F 2 0) _).2 ?_
    have e : g⁻¹ * (g * CFSG.Quasithin.SL2Model.e12 (1 : F) * g⁻¹) * g =
        CFSG.Quasithin.SL2Model.e12 (1 : F) := by group
    rw [e, ← g15_Rg_eq]
    exact CFSG.Quasithin.SL2Model.e12_mem_Rg (1 : F)
  · intro h
    have h1 : CFSG.Quasithin.SL2Model.e12 (1 : F) = 1 := by
      calc CFSG.Quasithin.SL2Model.e12 (1 : F) =
            g⁻¹ * (g * CFSG.Quasithin.SL2Model.e12 1 * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h2 := congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp at h2

private theorem g15_point_unique [CharP F 2] {A B : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (hB : IsPoint B) (h : rootGroup A A = rootGroup B B) : A = B := by
  by_contra hne
  obtain ⟨s, hs, hs1⟩ := g15_exists_ne_one hA
  have hsB : s ∈ rootGroup B B := h ▸ hs
  exact hs1 (g15_eq_one_of_fix_two hA hB hne (mem_rootGroup.1 hs).2 (mem_rootGroup.1 hsB).2)

private theorem g15_c_to_a [CharP F 2] {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (hsq : ∀ u : U, u + u = 0) {A : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (hquad : commU (U := U) (rootGroup A A) ≤ fixU (U := U) (rootGroup A A))
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx1 : x ≠ 1) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) (hxC : ∀ v : U, x • v = v → v = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      IsCompl (fixU (U := U) (rootGroup A A)) (fixU (U := U) (conjSub (rootGroup A A) g)) := by
  obtain ⟨h, hh⟩ := exists_actSub_Vi_eq (le_refl 2) 0 hA
  have hx0 : h⁻¹ * x * h ≠ 1 := by
    intro h1
    apply hx1
    calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨z', hz'⟩ := g15_lower_left_conj (h⁻¹ * x * h) hx0
  set z : Matrix.SpecialLinearGroup (Fin 2) F := h * z' * h⁻¹ with hz
  set y : Matrix.SpecialLinearGroup (Fin 2) F := z * x * z⁻¹ with hy
  have hyC : ∀ v : U, y • v = v → v = 0 := fun v hv => g15_fix_conj hxC z v hv
  have hym : y ^ m = 1 := by
    rw [hy, conj_pow, hxm]
    group
  obtain ⟨b, t0, P0, hP0, hy0, ht0, ht0mem⟩ := g15_entries_decomp (z' * (h⁻¹ * x * h) * z'⁻¹) hz'
  set r : Matrix.SpecialLinearGroup (Fin 2) F := h * CFSG.Quasithin.SL2Model.e12 b * h⁻¹ with hr
  set t : Matrix.SpecialLinearGroup (Fin 2) F := h * t0 * h⁻¹ with ht
  have hyrt : y = r * t := by
    calc y = h * (z' * (h⁻¹ * x * h) * z'⁻¹) * h⁻¹ := by rw [hy, hz]; group
      _ = h * (CFSG.Quasithin.SL2Model.e12 b * t0) * h⁻¹ := by rw [hy0]
      _ = r * t := by rw [hr, ht]; group
  have hr2 : r * r = 1 := by
    calc r * r = h * (CFSG.Quasithin.SL2Model.e12 b * CFSG.Quasithin.SL2Model.e12 b) * h⁻¹ := by
          rw [hr]; group
      _ = 1 := by rw [CFSG.Quasithin.SL2Model.e12_mul_self, mul_one]; group
  have ht2 : t * t = 1 := by
    calc t * t = h * (t0 * t0) * h⁻¹ := by rw [ht]; group
      _ = 1 := by rw [ht0, mul_one]; group
  have hrR : r ∈ rootGroup A A := by
    rw [← hh]
    refine (g14_conj_mem h (Vi F 2 0) (Vi F 2 0) r).2 ?_
    have e : h⁻¹ * r * h = CFSG.Quasithin.SL2Model.e12 b := by rw [hr]; group
    rw [e, ← g15_Rg_eq]
    exact CFSG.Quasithin.SL2Model.e12_mem_Rg b
  have hP : IsPoint (actSub h P0) := isPoint_actSub h hP0
  obtain ⟨x0, hx0P⟩ := g15_exists_actSub_eq hA hP
  have hconj : conjSub (rootGroup A A) x0⁻¹ = rootGroup (actSub h P0) (actSub h P0) := by
    rw [g15_conjSub_rootGroup, inv_inv, hx0P]
  have htR' : t ∈ conjSub (rootGroup A A) x0⁻¹ := by
    rw [hconj]
    refine (g14_conj_mem h P0 P0 t).2 ?_
    have e : h⁻¹ * t * h = t0 := by rw [ht]; group
    rw [e]
    exact ht0mem
  have hR' : commU (U := U) (conjSub (rootGroup A A) x0⁻¹) ≤
      fixU (U := U) (conjSub (rootGroup A A) x0⁻¹) := by
    rw [g15_commU_conjSub, g15_fixU_conjSub]
    exact AddSubgroup.map_mono hquad
  exact ⟨x0⁻¹, g15_decomp hsq hm hym hyC hyrt hr2 ht2 hrR htR' hquad hR'⟩

private theorem g15_fix_free_U [CharP F 2] {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U] [Finite U]
    (hsq : ∀ u : U, u + u = 0) {φ : Submodule F (Fin 2 → F) → AddSubgroup U}
    (hφ : G13Hyp F 2 U φ) {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx1 : x ≠ 1) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) (v : U) (hv : x • v = v) : v = 0 := by
  obtain ⟨s, Θ, hΘ, -, -⟩ := exists_equiv_of_halves_core hsq hφ.halves
  set w := Θ.symm v with hwdef
  have hΘw : Θ w = v := Θ.apply_symm_apply v
  have hfix : (fun j => x • w j) = w := by
    apply Θ.injective
    rw [hΘ x w, hΘw, hv]
  have hwj : ∀ j, w j = 0 := fun j =>
    g15_fix_free_odd hx1 hm hxm (w j) (congrFun hfix j)
  have hw0 : w = 0 := funext hwj
  calc v = Θ w := hΘw.symm
    _ = 0 := by rw [hw0, map_zero]

private theorem g15_ab [CharP F 2] {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U] [Finite U]
    (hsq : ∀ u : U, u + u = 0) {A : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (hex : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      IsCompl (fixU (U := U) (rootGroup A A)) (fixU (U := U) (conjSub (rootGroup A A) g))) :
    commU (U := U) (rootGroup A A) ≤ fixU (U := U) (rootGroup A A) ∧
      ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 → Odd (orderOf x) →
        fixU (U := U) (Subgroup.zpowers x) = ⊥ := by
  obtain ⟨g, hI⟩ := hex
  have hquad := g15_quadratic hsq hA hI
  refine ⟨hquad, fun x hx1 hxo => ?_⟩
  have hIg : IsCompl (fixU (U := U) (rootGroup A A))
      ((fixU (U := U) (rootGroup A A)).map (actU g⁻¹)) := by
    rw [← g15_fixU_conjSub]
    exact hI
  have hN : ∀ x ∈ Subgroup.normalizer
      ((rootGroup A A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)),
      ∀ y ∈ fixU (U := U) (rootGroup A A), x • y ∈ fixU (U := U) (rootGroup A A) := by
    intro x hx y hy t ht
    have hxt : x⁻¹ * t * x ∈ rootGroup A A := by
      have h1 := Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * t * x)
      have e : x * (x⁻¹ * t * x) * x⁻¹ = t := by group
      rw [e] at h1
      exact h1.2 ht
    show t • x • y = x • y
    rw [← mul_smul, show t * x = x * (x⁻¹ * t * x) from by group, mul_smul, hy _ hxt]
  obtain ⟨φ, hφ, -⟩ := g15_three hA g _ hN hquad le_rfl hIg
  rw [eq_bot_iff]
  intro v hv
  have hxv : x • v = v := hv x (Subgroup.mem_zpowers x)
  exact AddSubgroup.mem_bot.2 (g15_fix_free_U hsq hφ hx1 hxo (pow_orderOf_eq_one x) v hxv)

private theorem g15_bc [CharP F 2] {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    {R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (h : commU (U := U) R ≤ fixU (U := U) R ∧ ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
      x ≠ 1 → Odd (orderOf x) → fixU (U := U) (Subgroup.zpowers x) = ⊥) :
    commU (U := U) R ≤ fixU (U := U) R ∧ ∃ x : Matrix.SpecialLinearGroup (Fin 2) F,
      x ≠ 1 ∧ Odd (orderOf x) ∧ fixU (U := U) (Subgroup.zpowers x) = ⊥ := by
  obtain ⟨x, hx1, hxo⟩ := g15_order_three (F := F)
  exact ⟨h.1, x, hx1, hxo, h.2 x hx1 hxo⟩

private theorem g15_ca [CharP F 2] {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
    (hsq : ∀ u : U, u + u = 0) {A : Submodule F (Fin 2 → F)} (hA : IsPoint A)
    (h : commU (U := U) (rootGroup A A) ≤ fixU (U := U) (rootGroup A A) ∧
      ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 ∧ Odd (orderOf x) ∧
        fixU (U := U) (Subgroup.zpowers x) = ⊥) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      IsCompl (fixU (U := U) (rootGroup A A)) (fixU (U := U) (conjSub (rootGroup A A) g)) := by
  obtain ⟨hquad, x, hx1, hxo, hfix⟩ := h
  have hxC : ∀ v : U, x • v = v → v = 0 := by
    intro v hv
    have hvz : v ∈ fixU (U := U) (Subgroup.zpowers x) := by
      show ∀ t ∈ Subgroup.zpowers x, t • v = v
      intro t ht
      have hst : x ∈ MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) F) v :=
        MulAction.mem_stabilizer_iff.2 hv
      exact MulAction.mem_stabilizer_iff.1 (Subgroup.zpowers_le.2 hst ht)
    rw [hfix] at hvz
    exact AddSubgroup.mem_bot.1 hvz
  exact g15_c_to_a hsq hA hquad hx1 hxo (pow_orderOf_eq_one x) hxC

end G15Four

theorem as_G_1_5 : G_1_5 := by
  intro F _ _ _ R hR
  obtain ⟨A, hA, rfl⟩ := g15_sylow_rootGroup hR
  refine ⟨⟨A, hA, rfl⟩, ?_, ?_, ?_⟩
  · intro U _ _ _ hsq φ hφ A' hA' hAA'
    obtain rfl := g15_point_unique hA hA' hAA'
    obtain ⟨h1, h2⟩ := g15_halves hsq hφ hA
    exact ⟨h1, h2, fun g hg => g15_compl hsq hφ hA hg⟩
  · intro U _ _ _ hsq g Y hN hc hf hI A' hA' hAA'
    obtain rfl := g15_point_unique hA hA' hAA'
    obtain ⟨φ, hφ, hφA⟩ := g15_three hA g Y hN hc hf hI
    refine ⟨φ, hφ, fun x => ?_⟩
    rw [hφ.equivariant x⁻¹ _ hA, hφA]
  · intro U _ _ _ hsq
    exact ⟨⟨fun hex => g15_ab hsq hA hex, fun h => g15_ca hsq hA (g15_bc h)⟩,
      ⟨fun hex => g15_bc (g15_ab hsq hA hex), fun h => g15_ca hsq hA h⟩⟩

@[expose] def G_1_6 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], 2 < Nat.card F →
    ∀ (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
    (∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), (P : Subgroup _) = R) →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      (⨆ g : Matrix.SpecialLinearGroup (Fin 2) F, (fixU (U := U) R).map (actU g)) = ⊤ →
      (∀ r ∈ R, r ≠ 1 → fixU (U := U) (Subgroup.zpowers r) = fixU (U := U) R) →
      ∃ (s : ℕ) (f : U →+ (Fin s → Fin 2 → F)), Function.Surjective f ∧
        (∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (u : U) (i : Fin s),
          f (g • u) i = g • f u i) ∧
        f.ker = fixU (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))

section G16

open CFSG.Quasithin.SL2Model

variable {F : Type} [Field F]

private theorem g16_inv_lower_left (k : Matrix.SpecialLinearGroup (Fin 2) F) :
    (k⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 1 0 = -k.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp

private theorem g16_conj_mem_Rg [CharP F 2] {k t : Matrix.SpecialLinearGroup (Fin 2) F}
    (hk : k.1 1 0 = 0) (ht : t ∈ Rg F) : k * t * k⁻¹ ∈ Rg F := by
  obtain ⟨c, rfl⟩ := mem_Rg.1 ht
  have hdet := det_eq_one' k
  have hk' : (k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hk
  rw [hk', mul_zero, sub_zero] at hdet
  refine mem_Rg.2 ⟨(k : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * c, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hk', e12_coe] <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

private theorem g16_mul_self [CharP F 2] {t : Matrix.SpecialLinearGroup (Fin 2) F}
    (ht : t ∈ Rg F) : t * t = 1 := by
  obtain ⟨b, rfl⟩ := mem_Rg.1 ht
  exact e12_mul_self b

private theorem g16_conj_mem {R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg : R = CFSG.Quasithin.B6.conjSub g (Rg F))
    {s : Matrix.SpecialLinearGroup (Fin 2) F} (hs : s ∈ Rg F) : g * s * g⁻¹ ∈ R := by
  rw [hg]
  exact CFSG.Quasithin.B6.mem_conjSub.2
    (by rw [show g⁻¹ * (g * s * g⁻¹) * g = s by group]; exact hs)

private theorem g16_comm [CharP F 2] {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] (hsq : ∀ v : V, v + v = 0)
    (hC : ∀ t ∈ Rg F, t ≠ 1 → ∀ w : V, t • w = w → ∀ s ∈ Rg F, s • w = w)
    {t : Matrix.SpecialLinearGroup (Fin 2) F} (ht : t ∈ Rg F) (v : V) :
    t • v - v ∈ fixU (U := V) (Rg F) := by
  by_cases h1 : t = 1
  · subst h1
    show ∀ s ∈ Rg F, s • (1 • v - v) = 1 • v - v
    intro s _
    simp
  · have htt : t • (t • v - v) = t • v - v := by
      rw [smul_sub, ← mul_smul, g16_mul_self ht, one_smul,
        show v - t • v = -(t • v - v) from (neg_sub _ _).symm]
      exact neg_eq_iff_add_eq_zero.2 (hsq _)
    exact fun s hs => hC t ht h1 _ htt s hs

private theorem g16_fix_lower [CharP F 2] {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V]
    {k : Matrix.SpecialLinearGroup (Fin 2) F} (hk : k.1 1 0 = 0) {y : V}
    (hy : y ∈ fixU (U := V) (Rg F)) : k • y ∈ fixU (U := V) (Rg F) := by
  intro t ht
  have hk' : (k⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 1 0 = 0 := by
    rw [g16_inv_lower_left, hk, neg_zero]
  have hc : k⁻¹ * t * k ∈ Rg F := by
    have h := g16_conj_mem_Rg hk' ht
    rwa [inv_inv] at h
  calc t • k • y = (t * k) • y := (mul_smul t k y).symm
    _ = (k * (k⁻¹ * t * k)) • y := by congr 1; group
    _ = k • ((k⁻¹ * t * k) • y) := mul_smul _ _ _
    _ = k • y := by rw [hy _ hc]

private theorem g16_fix_top [CharP F 2] {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V]
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx : x.1 1 0 ≠ 0) {u u' : V}
    (hu : u ∈ fixU (U := V) (Rg F)) (hu' : u' ∈ fixU (U := V) (Rg F))
    (h : u - x • u' ∈ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :
    u ∈ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have hx' : (x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 1 0 ≠ 0 := by
    rw [g16_inv_lower_left]; exact neg_ne_zero.2 hx
  have hTop := Rg_sup_conj_eq_top x⁻¹ hx'
  rw [inv_inv] at hTop
  have hvT : ∀ t ∈ Rg F, t • (x • u') = x • u' := by
    intro t ht
    have h1 := h t (Subgroup.mem_top t)
    rw [smul_sub, hu t ht] at h1
    exact sub_right_inj.1 h1
  have hvR : ∀ t ∈ Rg F, (x * t * x⁻¹) • (x • u') = x • u' := by
    intro t ht
    rw [← mul_smul, show x * t * x⁻¹ * x = x * t by group, mul_smul, hu' t ht]
  have hle : Rg F ⊔ (Rg F).map (MulAut.conj x).toMonoidHom ≤
      MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) F) (x • u') := by
    refine sup_le (fun t ht => MulAction.mem_stabilizer_iff.2 (hvT t ht)) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact MulAction.mem_stabilizer_iff.2 (hvR t ht)
  have hall : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, k • (x • u') = x • u' := fun k =>
    MulAction.mem_stabilizer_iff.1 (hle (by rw [hTop]; exact Subgroup.mem_top k))
  have hv : x • u' ∈ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    fun k _ => hall k
  have hs := add_mem hv h
  have e : x • u' + (u - x • u') = u := by abel
  rwa [e] at hs

private theorem g16_decomp [CharP F 2] {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] (hsq : ∀ v : V, v + v = 0)
    (hC : ∀ t ∈ Rg F, t ≠ 1 → ∀ w : V, t • w = w → ∀ s ∈ Rg F, s • w = w)
    (hgen : (⨆ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (fixU (U := V) (Rg F)).map (actU g)) = ⊤)
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx : x.1 1 0 ≠ 0) (v : V) :
    ∃ a ∈ fixU (U := V) (Rg F), ∃ b ∈ fixU (U := V) (Rg F), v = a + x • b := by
  have hx' : (x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 1 0 ≠ 0 := by
    rw [g16_inv_lower_left]; exact neg_ne_zero.2 hx
  set D : AddSubgroup V := fixU (U := V) (Rg F) ⊔ (fixU (U := V) (Rg F)).map (actU x) with hD
  have hD1 : ∀ t ∈ Rg F, ∀ d ∈ D, t • d ∈ D := by
    intro t ht d hd
    obtain ⟨a, ha, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hd
    have h1 : t • (a + z) = (a + (t • z - z)) + z := by
      rw [smul_add, ha t ht]; abel
    rw [h1]
    exact add_mem (AddSubgroup.mem_sup_left (add_mem ha (g16_comm hsq hC ht z)))
      (AddSubgroup.mem_sup_right hz)
  have hD2 : ∀ t ∈ Rg F, ∀ d ∈ D, (x * t * x⁻¹) • d ∈ D := by
    intro t ht d hd
    obtain ⟨a, ha, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hd
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hz
    have hc : t • (x⁻¹ • a) - x⁻¹ • a ∈ fixU (U := V) (Rg F) :=
      g16_comm hsq hC ht (x⁻¹ • a)
    have e1 : (x * t * x⁻¹) • a = x • (t • (x⁻¹ • a)) := by rw [mul_smul, mul_smul]
    have e2 : (x * t * x⁻¹) • actU x a' = x • (t • a') := by
      rw [show actU x a' = x • a' from rfl, ← mul_smul,
        show x * t * x⁻¹ * x = x * t by group, mul_smul]
    have e3 : x • (x⁻¹ • a) = a := smul_inv_smul x a
    have e : (x * t * x⁻¹) • (a + actU x a') =
        a + x • ((t • (x⁻¹ • a) - x⁻¹ • a) + a') := by
      rw [smul_add, e1, e2, ha' t ht, smul_add, smul_sub, e3]; abel
    rw [e]
    exact add_mem (AddSubgroup.mem_sup_left ha)
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨_, add_mem hc ha', rfl⟩))
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | ∀ d ∈ D, g • d ∈ D ∧ g⁻¹ • d ∈ D}
      one_mem' := fun d hd => ⟨by rw [one_smul]; exact hd, by rw [inv_one, one_smul]; exact hd⟩
      mul_mem' := fun {g h} hg hh d hd =>
        ⟨by rw [mul_smul]; exact (hg _ (hh d hd).1).1,
         by rw [mul_inv_rev, mul_smul]; exact (hh _ (hg d hd).2).2⟩
      inv_mem' := fun {g} hg d hd => ⟨(hg d hd).2, by rw [inv_inv]; exact (hg d hd).1⟩ }
  have hRS : Rg F ≤ S := fun t ht d hd => by
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (g16_mul_self ht)
    exact ⟨hD1 t ht d hd, by rw [hinv]; exact hD1 t ht d hd⟩
  have hCS : (Rg F).map (MulAut.conj x).toMonoidHom ≤ S := by
    rintro _ ⟨t, ht, rfl⟩ d hd
    have hinv : (x * t * x⁻¹)⁻¹ = x * t * x⁻¹ := by
      rw [show (x * t * x⁻¹)⁻¹ = x * t⁻¹ * x⁻¹ by group,
        inv_eq_of_mul_eq_one_right (g16_mul_self ht)]
    refine ⟨hD2 t ht d hd, ?_⟩
    show (x * t * x⁻¹)⁻¹ • d ∈ D
    rw [hinv]
    exact hD2 t ht d hd
  have hTop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ S := by
    have h := Rg_sup_conj_eq_top x⁻¹ hx'
    rw [inv_inv] at h
    rw [← h]
    exact sup_le hRS hCS
  have hall : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ d ∈ D, g • d ∈ D :=
    fun g d hd => (hTop (Subgroup.mem_top g) d hd).1
  have hle : (⨆ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (fixU (U := V) (Rg F)).map (actU g)) ≤ D :=
    iSup_le fun g => by
      rintro _ ⟨a, ha, rfl⟩
      exact hall g a (AddSubgroup.mem_sup_left ha)
  rw [hgen] at hle
  obtain ⟨a, ha, z, hz, hv⟩ := AddSubgroup.mem_sup.1 (hle (AddSubgroup.mem_top v))
  obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hz
  exact ⟨a, ha, b, hb, hv.symm⟩

private def g16qAct {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) →+
      (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :=
  QuotientAddGroup.map _ _ (actU g) fun c hc k _ => by
    show k • g • c = g • c
    calc k • g • c = (k * g) • c := (mul_smul k g c).symm
      _ = (g * (g⁻¹ * k * g)) • c := by congr 1; group
      _ = g • ((g⁻¹ * k * g) • c) := mul_smul _ _ _
      _ = g • c := by rw [hc (g⁻¹ * k * g) (Subgroup.mem_top _)]

private instance g16Quot {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F)
      (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) where
  smul g q := g16qAct g q
  one_smul q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    exact congrArg QuotientAddGroup.mk (one_smul _ v)
  mul_smul g h q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    exact congrArg QuotientAddGroup.mk (mul_smul g h v)
  smul_zero g := map_zero (g16qAct g)
  smul_add g q r := map_add (g16qAct g) q r

private theorem g16_core [CharP F 2] [Finite F] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] (hsq : ∀ v : V, v + v = 0)
    (hC : ∀ t ∈ Rg F, t ≠ 1 → ∀ w : V, t • w = w → ∀ s ∈ Rg F, s • w = w)
    (hgen : (⨆ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (fixU (U := V) (Rg F)).map (actU g)) = ⊤) :
    ∃ (s : ℕ) (f : V →+ (Fin s → Fin 2 → F)), Function.Surjective f ∧
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : V) (i : Fin s),
        f (g • v) i = g • f v i) ∧
      ∀ v : V, f v = 0 ↔ ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, k • v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let mk : V →+ (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    QuotientAddGroup.mk' _
  have hsqQ : ∀ q : V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      q + q = 0 := by
    intro q
    refine QuotientAddGroup.induction_on q fun v => ?_
    show mk v + mk v = 0
    rw [← map_add, hsq v, map_zero]
  let Y : AddSubgroup (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    (fixU (U := V) (Rg F)).map mk
  have hY : G13Halves F Y :=
    { stab := fun d q hq => by
        obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hq
        exact AddSubgroup.mem_map.2 ⟨dgm d • a, g16_fix_lower (k := dgm d) (by simp) ha, rfl⟩
      fix := fun c q hq => by
        obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hq
        exact congrArg mk (ha (e12 c) (e12_mem_Rg c))
      comm := fun c q => by
        obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
        refine AddSubgroup.mem_map.2 ⟨e12 c • v - v, g16_comm hsq hC (e12_mem_Rg c) v, ?_⟩
        show mk (e12 c • v - v) = e12 c • mk v - mk v
        rw [map_sub]
        rfl
      disj := fun z hz hwz => by
        obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hz
        obtain ⟨b, hb, hbeq⟩ := AddSubgroup.mem_map.1 hwz
        have hbeq' : mk b = mk (wmat F • a) := hbeq
        have hc' : -(wmat F • a) + b ∈
            fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
          QuotientAddGroup.eq.1 hbeq'.symm
        have h4 : -a + (wmat F)⁻¹ • b = -(wmat F • a) + b :=
          (show (wmat F)⁻¹ • (-(wmat F • a) + b) = -a + (wmat F)⁻¹ • b by
            rw [smul_add, smul_neg, inv_smul_smul]).symm.trans
            (hc' (wmat F)⁻¹ (Subgroup.mem_top _))
        have h5 : a - (wmat F)⁻¹ • b ∈
            fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
          have e : a - (wmat F)⁻¹ • b = -(-(wmat F • a) + b) := by rw [← h4]; abel
          rw [e]
          exact neg_mem hc'
        have hx : ((wmat F)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 1 0 ≠ 0 := by
          rw [wmat_inv]; exact wmat_lower_left
        have ha' := g16_fix_top hx ha hb h5
        exact (QuotientAddGroup.eq_zero_iff a).2 ha'
      sup := fun q => by
        obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
        obtain ⟨a, ha, b, hb, hv⟩ := g16_decomp hsq hC hgen wmat_lower_left v
        exact ⟨mk a, AddSubgroup.mem_map.2 ⟨a, ha, rfl⟩, mk b,
          AddSubgroup.mem_map.2 ⟨b, hb, rfl⟩, by rw [hv]; exact map_add mk a (wmat F • b)⟩ }
  haveI : Finite (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    inferInstance
  obtain ⟨s, Θ, hΘ, -, -⟩ := exists_equiv_of_halves_core hsqQ hY
  have key : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F)
      (q : V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))),
      Θ.symm (g • q) = g • Θ.symm q := by
    intro g q
    apply Θ.injective
    rw [AddEquiv.apply_symm_apply]
    have h := hΘ g (Θ.symm q)
    rw [AddEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨s, (Θ.symm.toAddMonoidHom).comp mk, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective (Θ y)
    exact ⟨v, by show Θ.symm (QuotientAddGroup.mk v) = y; rw [hv, AddEquiv.symm_apply_apply]⟩
  · intro g v i
    show Θ.symm (g • mk v) i = (g • Θ.symm (mk v)) i
    rw [key]
  · intro v
    have h0 : Θ.symm (mk v) = 0 ↔ mk v = 0 := by
      constructor
      · intro h
        rw [← Θ.apply_symm_apply (mk v), h, map_zero]
      · intro h
        rw [h, map_zero]
    show Θ.symm (mk v) = 0 ↔ _
    exact h0.trans ((QuotientAddGroup.eq_zero_iff v).trans
      ⟨fun h k => h k (Subgroup.mem_top k), fun h k _ => h k⟩)

private def g16Tw (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type) : Type := V

private instance g16TwAddCommGroup (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] : AddCommGroup (g16Tw g V) :=
  inferInstanceAs (AddCommGroup V)

private instance g16TwDMA (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) (g16Tw g V) where
  smul k v := ((g * k * g⁻¹) • (show V from v) : V)
  one_smul v := by
    show (g * 1 * g⁻¹) • (show V from v) = show V from v
    rw [mul_one, mul_inv_cancel, one_smul]
  mul_smul k l v := by
    show (g * (k * l) * g⁻¹) • (show V from v) =
      (g * k * g⁻¹) • ((g * l * g⁻¹) • (show V from v))
    rw [← mul_smul, show g * k * g⁻¹ * (g * l * g⁻¹) = g * (k * l) * g⁻¹ by group]
  smul_zero k := by
    show (g * k * g⁻¹) • (0 : V) = 0
    exact smul_zero _
  smul_add k v w := by
    show (g * k * g⁻¹) • ((show V from v) + (show V from w)) =
      (g * k * g⁻¹) • (show V from v) + (g * k * g⁻¹) • (show V from w)
    exact smul_add _ _ _

private instance g16TwFinite (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] [Finite V] : Finite (g16Tw g V) :=
  inferInstanceAs (Finite V)

end G16

section G16Thm

open CFSG.Quasithin.SL2Model

theorem as_G_1_6 : G_1_6 := by
  intro F _ _ _ hF R hR U _ _ _ hsq hgen hC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRsyl : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤ := by
    obtain ⟨P, rfl⟩ := hR
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [show ((P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subgroupOf ⊤).index =
      (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).index from
        Subgroup.relIndex_top_right _]
    exact Sylow.not_dvd_index P
  have hRgsyl : CFSG.QuasithinUnique.IsSylowTwoOf (Rg F) ⊤ := by
    refine ⟨le_top, Rg_isPGroup, ?_⟩
    rw [show ((Rg F).subgroupOf ⊤).index = (Rg F).index from Subgroup.relIndex_top_right _]
    exact Rg_index_odd
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hRgsyl hRsyl
  have hC' : ∀ r ∈ R, r ≠ 1 → ∀ w : U, r • w = w → ∀ s ∈ R, s • w = w := by
    intro r hr hr1 w hw
    have hw' : w ∈ fixU (U := U) (Subgroup.zpowers r) := fun k hk =>
      MulAction.mem_stabilizer_iff.1 (Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hw) hk)
    rw [hC r hr hr1] at hw'
    exact hw'
  have hgenW : (⨆ k : Matrix.SpecialLinearGroup (Fin 2) F,
      (fixU (U := g16Tw g U) (Rg F)).map (actU k)) = ⊤ := by
    refine eq_top_iff.2 (le_trans (le_of_eq hgen.symm) ?_)
    refine iSup_le fun k => ?_
    rintro _ ⟨a, ha, rfl⟩
    refine AddSubgroup.mem_iSup_of_mem (g⁻¹ * k * g)
      (AddSubgroup.mem_map.2 ⟨a, fun s hs => ?_, ?_⟩)
    · exact ha (g * s * g⁻¹) (g16_conj_mem hg hs)
    · show (g * (g⁻¹ * k * g) * g⁻¹) • a = k • a
      congr 1
      group
  have hCW : ∀ t ∈ Rg F, t ≠ 1 → ∀ w : g16Tw g U, t • w = w → ∀ s ∈ Rg F, s • w = w := by
    intro t ht ht1 w hw s hs
    have hw' : (g * t * g⁻¹) • (show U from w) = show U from w := hw
    have hr : g * t * g⁻¹ ∈ R := g16_conj_mem hg ht
    have hr1 : g * t * g⁻¹ ≠ 1 := by
      intro h1
      apply ht1
      have e : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [e, h1]
      group
    exact hC' _ hr hr1 w hw' (g * s * g⁻¹) (g16_conj_mem hg hs)
  obtain ⟨s, f, hfs, hfe, hfk⟩ := g16_core (V := g16Tw g U) (fun w => hsq w) hCW hgenW
  refine ⟨s, AddMonoidHom.mk' (fun v => g • f v) (fun a b => by
    show g • f ((show g16Tw g U from a) + (show g16Tw g U from b)) =
      g • f (show g16Tw g U from a) + g • f (show g16Tw g U from b)
    rw [map_add, smul_add]), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hfs (g⁻¹ • y)
    exact ⟨v, by show g • f v = y; rw [hv, smul_inv_smul]⟩
  · intro k v i
    have e : (g⁻¹ * k * g) • (show g16Tw g U from v) = k • v := by
      show (g * (g⁻¹ * k * g) * g⁻¹) • v = k • v
      congr 1
      group
    have h1 : f (k • v) = (g⁻¹ * k * g) • f v := by
      funext j
      have h := hfe (g⁻¹ * k * g) (v : g16Tw g U) j
      rw [e] at h
      exact h
    have h2 : ∀ x : Fin s → Fin 2 → F, g • ((g⁻¹ * k * g) • x) = k • (g • x) := fun x => by
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    have h3 : g • f (k • v) = k • (g • f v) := by rw [h1, h2]
    exact congrFun h3 i
  · refine AddSubgroup.ext fun v => ?_
    have hk : f (v : g16Tw g U) = 0 ↔ ∀ k : Matrix.SpecialLinearGroup (Fin 2) F, k • v = v := by
      rw [hfk v]
      constructor
      · intro h k
        have h' : (g * (g⁻¹ * k * g) * g⁻¹) • v = v := h (g⁻¹ * k * g)
        rwa [show g * (g⁻¹ * k * g) * g⁻¹ = k by group] at h'
      · intro h k
        exact h (g * k * g⁻¹)
    have hgf : g • f (v : g16Tw g U) = 0 ↔ f (v : g16Tw g U) = 0 := by
      constructor
      · intro h
        have := congrArg (fun x => g⁻¹ • x) h
        simpa using this
      · intro h
        rw [h, smul_zero]
    rw [AddMonoidHom.mem_ker]
    show g • f (v : g16Tw g U) = 0 ↔ v ∈ fixU (U := U) (⊤ : Subgroup _)
    rw [hgf, hk]
    exact ⟨fun h k _ => h k, fun h k => h k (Subgroup.mem_top k)⟩

end G16Thm

@[expose] def G_1_7 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
    (∃ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F), (P : Subgroup _) = R) →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      (∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
        IsCompl (fixU (U := U) R) (fixU (U := U) (conjSub R g))) →
      ∃ s : ℕ, Nat.card (commU (U := U) R) = Nat.card F ^ s ∧
        IsSumOfNatural (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ⊤ (⊤ : AddSubgroup U) s

theorem as_G_1_7 : G_1_7 := by
  intro F _ _ _ R hR U _ _ _ hsq hex
  obtain ⟨g, hI⟩ := hex
  obtain ⟨A, hA, rfl⟩ := g15_sylow_rootGroup hR
  have hquad := g15_quadratic hsq hA hI
  have hIg : IsCompl (fixU (U := U) (rootGroup A A))
      ((fixU (U := U) (rootGroup A A)).map (actU g⁻¹)) := by
    rw [← g15_fixU_conjSub]
    exact hI
  have hN : ∀ x ∈ Subgroup.normalizer
      ((rootGroup A A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)),
      ∀ y ∈ fixU (U := U) (rootGroup A A), x • y ∈ fixU (U := U) (rootGroup A A) := by
    intro x hx y hy t ht
    have hxt : x⁻¹ * t * x ∈ rootGroup A A := by
      have h1 := Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * t * x)
      have e : x * (x⁻¹ * t * x) * x⁻¹ = t := by group
      rw [e] at h1
      exact h1.2 ht
    show t • x • y = x • y
    rw [← mul_smul, show t * x = x * (x⁻¹ * t * x) from by group, mul_smul, hy _ hxt]
  obtain ⟨φ, hφ, hφA⟩ := g15_three hA g _ hN hquad le_rfl hIg
  obtain ⟨s, hs, W, hWi, hWsup, hWj⟩ := theorem_G_1_3 (F := F) (le_refl 2) U hsq φ hφ
  refine ⟨s, ?_, ?_⟩
  · rw [← (g15_halves hsq hφ hA).1, g15_card_eq hφ hA]
    exact hs
  · unfold IsSumOfNatural
    refine ⟨W, hWi, hWsup, fun j => ?_⟩
    obtain ⟨hinv, f, hfi, hfr, hfe⟩ := hWj j
    refine ⟨fun g _ w hw => hinv g w hw, f, fun _ _ _ _ h => hfi h, ?_,
      fun g _ v _ => hfe g v⟩
    rw [← hfr, AddMonoidHom.range_eq_map]
    congr 1

@[expose] def G_1_8 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        (⨆ i : Fin n, φ (Vi F n i)) = ⊤

theorem as_G_1_8 : G_1_8 := by
  intro F _ _ _ n hn U _ _ _ _ φ h
  exact iSup_phi_Vi_eq_top hn h

@[expose] def G_1_10 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n),
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        ∃ s : ℕ, Nat.card (φ (Vi F n ⟨0, by omega⟩)) = Nat.card F ^ s ∧
          (Disjoint (φ (Vi F n ⟨0, by omega⟩)) (φ (Vi F n ⟨1, by omega⟩)) ∧
            IsSumOfNatural (Lij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
              (Vij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
              (Uij φ ⟨0, by omega⟩ ⟨1, by omega⟩) s) ∧
          IsCompl (Uij φ ⟨0, by omega⟩ ⟨1, by omega⟩) (Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
          Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩ =
            fixU (Lij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) ∧
          (Disjoint (φ (Vi F n ⟨0, by omega⟩)) (Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
            Uhat φ ⟨1, by omega⟩ = φ (Vi F n ⟨0, by omega⟩) ⊔ Uhatij φ ⟨0, by omega⟩ ⟨1, by omega⟩ ∧
            Uhat φ ⟨1, by omega⟩ = fixU (Rij F (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) ∧
          IsCompl (φ (Vi F n ⟨0, by omega⟩)) (Uhat φ ⟨0, by omega⟩)

private theorem asG11_iSupIndep_of_coord {F : Type} [Field F] {n s : ℕ} {U : Type}
    [AddCommGroup U] (Θ : (Fin s → Fin n → F) ≃+ U) (Uk : Fin n → AddSubgroup U)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ Uk k ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l))) :
    iSupIndep Uk := by
  rw [iSupIndep_def]
  intro k
  rw [disjoint_iff]
  let P : U →+ (Fin s → F) :=
    AddMonoidHom.mk' (fun u l => Θ.symm u l k) (fun a b => by funext l; simp)
  have hle : (⨆ (j : Fin n) (_ : j ≠ k), Uk j) ≤ P.ker := by
    refine iSup₂_le fun j hj => ?_
    intro u hu
    obtain ⟨a, rfl⟩ := (hmem j u).1 hu
    rw [AddMonoidHom.mem_ker]
    funext l
    simp [P, Pi.single_apply, hj, Ne.symm hj]
  refine eq_bot_iff.2 fun u hu => ?_
  obtain ⟨a, rfl⟩ := (hmem k u).1 (AddSubgroup.mem_inf.1 hu).1
  have h0 := hle (AddSubgroup.mem_inf.1 hu).2
  rw [AddMonoidHom.mem_ker] at h0
  have ha : ∀ l, a l = 0 := fun l => by
    have := congrFun h0 l
    simpa [P, Pi.single_apply] using this
  have hz : (fun l => (Pi.single k (a l) : Fin n → F)) = 0 := by
    funext l
    simp [ha l]
  rw [AddSubgroup.mem_bot, hz, map_zero]

private theorem asG11_fam {F : Type} [Field F] [CharP F 2] {n : ℕ} {U : Type} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    {φ : Submodule F (Fin n → F) → AddSubgroup U} (hφ : G13Hyp F n U φ) (hn : 2 ≤ n) :
    G13Fam F hn (fun k => φ (Vi F n k)) :=
  ⟨fun _ h => phi_Vi_eq hφ h,
    fun d y hy => by
      have hg := hφ.equivariant
        (embSL (idx0_ne_idx1 hn) (CFSG.Quasithin.SL2Model.dgm d)) (Vi F n (idx0 hn)) (isPoint_Vi _)
      rw [actSub_embSL_of_lower_left_zero (idx0_ne_idx1 hn) (by simp)] at hg
      show embSL (idx0_ne_idx1 hn) (CFSG.Quasithin.SL2Model.dgm d) • y ∈ φ (Vi F n (idx0 hn))
      rw [hg]
      exact ⟨y, hy, rfl⟩,
    fun _ _ hab _ hkb c _ hy => root_smul_of_ne hφ hab hkb (T_mem_Rij hab c) hy,
    fun c u => hφ.commU_le _ _ (isFlag_Vi_Vhat (idx0_ne_idx1 hn))
      (AddSubgroup.subset_closure ⟨_, T_mem_Rij (idx0_ne_idx1 hn) c, u, rfl⟩),
    hφ.disjoint _ _ (isPoint_Vi _) (isPoint_Vi _) (Vi_ne_Vi (idx0_ne_idx1 hn)),
    iSup_phi_Vi_eq_top hn hφ⟩

@[expose] def G_1_11 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 3 ≤ n →
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        iSupIndep (fun i : Fin n => φ (Vi F n i)) ∧ (⨆ i : Fin n, φ (Vi F n i)) = ⊤

theorem as_G_1_11 : G_1_11 := by
  intro F _ _ _ n hn3 U _ _ _ hsq φ hφ
  have hn : 2 ≤ n := by omega
  obtain ⟨_, Θ, -, -, hmem⟩ := G13Fam.exists_equiv_fam (asG11_fam hφ hn) hsq
  exact ⟨asG11_iSupIndep_of_coord Θ (fun k => φ (Vi F n k)) hmem, iSup_phi_Vi_eq_top hn hφ⟩

private theorem asG12_transvection_mem_setStab {F : Type} [Field F] {n : ℕ} {i j p : Fin n}
    (hij : i ≠ j) (hp : j ≠ p) (b : F) :
    Matrix.SpecialLinearGroup.transvection hij b ∈ setStab F (Vi F n p) := by
  intro w
  rw [mem_Vi, mem_Vi]
  constructor
  · intro hw k hk
    simp [T_smul_apply, hw k hk, hw j hp]
  · intro hw k hk
    have hwj : w j = 0 := by
      have h := hw j hp
      rw [T_smul_apply, if_neg hij.symm, add_zero] at h
      exact h
    have h := hw k hk
    simpa [T_smul_apply, hwj] using h

private theorem asG12_transvection_sq {F : Type} [Field F] [CharP F 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (b : F) : Matrix.SpecialLinearGroup.transvection hij b ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply SL_ext_vec
  intro v
  rw [pow_two, mul_smul, one_smul]
  funext m
  by_cases hm : m = i
  · subst hm
    simp [T_smul_apply, Ne.symm hij]
    linear_combination (b * v j) * h2
  · simp [T_smul_apply, hm, Ne.symm hij]

private theorem asG12_smul_e {F : Type} [Field F] {n : ℕ} {p : Fin n}
    {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : g ∈ setStab F (Vi F n p)) :
    g • (Pi.single p 1 : Fin n → F) =
      (g • (Pi.single p 1 : Fin n → F)) p • (Pi.single p 1 : Fin n → F) := by
  have h1 : (Pi.single p 1 : Fin n → F) ∈ Vi F n p := Submodule.mem_span_singleton_self _
  have h2 := mem_Vi.1 ((hg _).1 h1)
  funext k
  by_cases hk : k = p
  · subst hk; simp
  · simp [hk, h2 k hk]

private theorem asG12_pow_smul_e {F : Type} [Field F] {n : ℕ} {p : Fin n}
    {g : Matrix.SpecialLinearGroup (Fin n) F} {c : F}
    (hg : g • (Pi.single p 1 : Fin n → F) = c • (Pi.single p 1 : Fin n → F)) (m : ℕ) :
    (g ^ m) • (Pi.single p 1 : Fin n → F) = (c ^ m) • (Pi.single p 1 : Fin n → F) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_smul, ih, smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', hg,
      smul_smul, pow_succ]

private theorem asG12_eq_one_of_pow {F : Type} [Field F] [CharP F 2] (c : F) (k : ℕ)
    (h : c ^ 2 ^ k = 1) : c = 1 := by
  have h1 : (c - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).1 h1)

private theorem asG12_fix_e {F : Type} [Field F] [CharP F 2] {n : ℕ} {p : Fin n}
    {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : g ∈ setStab F (Vi F n p)) (k : ℕ)
    (hk : g ^ 2 ^ k = 1) : g • (Pi.single p 1 : Fin n → F) = (Pi.single p 1 : Fin n → F) := by
  obtain ⟨c, hgc⟩ : ∃ c : F, g • (Pi.single p 1 : Fin n → F) = c • (Pi.single p 1 : Fin n → F) :=
    ⟨_, asG12_smul_e hg⟩
  have h1 := asG12_pow_smul_e hgc (2 ^ k)
  rw [hk, one_smul] at h1
  have h2 : c ^ 2 ^ k = 1 := by
    have := congrFun h1 p
    simpa using this.symm
  rw [hgc, asG12_eq_one_of_pow c k h2, one_smul]

private theorem asG12_fix_Vi {F : Type} [Field F] [CharP F 2] {n : ℕ} {p : Fin n}
    {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : g ∈ setStab F (Vi F n p)) (k : ℕ)
    (hk : g ^ 2 ^ k = 1) {v : Fin n → F} (hv : v ∈ Vi F n p) : g • v = v := by
  have hve : v = v p • (Pi.single p 1 : Fin n → F) := by
    funext m
    by_cases hm : m = p
    · subst hm; simp
    · simp [hm, mem_Vi.1 hv m hm]
  rw [hve, smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', asG12_fix_e hg k hk]

private theorem asG12_fixSub_flagSylow {F : Type} [Field F] {n : ℕ} (hn : 2 ≤ n) :
    fixSub F (flagSylow F n) = Vi F n ⟨0, by omega⟩ := by
  ext v
  show (∀ t ∈ flagSylow F n, t • v = v) ↔ v ∈ Vi F n ⟨0, by omega⟩
  rw [mem_Vi]
  constructor
  · intro hv k hk
    have hk0 : (⟨0, by omega⟩ : Fin n) < k := by
      rw [Fin.lt_def]
      have := Fin.val_ne_of_ne hk
      simp only at this ⊢
      omega
    have hle : Rij F (⟨0, by omega⟩ : Fin n) k ≤ flagSylow F n :=
      le_iSup_of_le (⟨0, by omega⟩ : Fin n) (le_iSup_of_le k (le_iSup_of_le hk0 le_rfl))
    have h := congrFun (hv _ (hle (T_mem_Rij (Ne.symm hk) 1))) (⟨0, by omega⟩ : Fin n)
    rw [T_smul_apply, if_pos rfl] at h
    simpa using h
  · intro hv t ht
    have hle : flagSylow F n ≤ MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) F) v := by
      unfold flagSylow
      refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
      intro x hx
      obtain ⟨b, rfl⟩ := (mem_Rij_iff (F := F) (ne_of_lt hij)).1 hx
      rw [MulAction.mem_stabilizer_iff]
      have hj : v j = 0 := by
        apply hv j
        intro h
        rw [h, Fin.lt_def] at hij
        simp at hij
      funext m
      simp [T_smul_apply, hj]
    exact MulAction.mem_stabilizer_iff.1 (hle ht)

private theorem asG12_fixSub_oTwo {F : Type} [Field F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) :
    fixSub F (oTwoPrimeUpper (setStab F (Vi F n ⟨0, by omega⟩))) = Vi F n ⟨0, by omega⟩ := by
  ext v
  show (∀ t ∈ oTwoPrimeUpper (setStab F (Vi F n (⟨0, by omega⟩ : Fin n))), t • v = v) ↔
    v ∈ Vi F n (⟨0, by omega⟩ : Fin n)
  rw [mem_Vi]
  constructor
  · intro hv k hk
    have ht : Matrix.SpecialLinearGroup.transvection (Ne.symm hk) 1 ∈
        oTwoPrimeUpper (setStab F (Vi F n (⟨0, by omega⟩ : Fin n))) := by
      apply Subgroup.subset_closure
      exact ⟨asG12_transvection_mem_setStab (Ne.symm hk) hk 1, 1,
        by simpa using asG12_transvection_sq (Ne.symm hk) (1 : F)⟩
    have h := congrFun (hv _ ht) (⟨0, by omega⟩ : Fin n)
    rw [T_smul_apply, if_pos rfl] at h
    simpa using h
  · intro hv
    have hle : oTwoPrimeUpper (setStab F (Vi F n (⟨0, by omega⟩ : Fin n))) ≤
        MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) F) v := by
      unfold oTwoPrimeUpper
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hx, k, hk⟩
      exact MulAction.mem_stabilizer_iff.2 (asG12_fix_Vi hx k hk (mem_Vi.2 hv))
    exact fun t ht => MulAction.mem_stabilizer_iff.1 (hle ht)

private theorem asG12_mem_setStab_of_actSub {F : Type} [Field F] {n : ℕ} {p : Fin n}
    {g : Matrix.SpecialLinearGroup (Fin n) F} (h : actSub g (Vi F n p) = Vi F n p) :
    g ∈ setStab F (Vi F n p) := by
  intro v
  constructor
  · intro hv
    have : g • v ∈ actSub g (Vi F n p) := mem_actSub.2 ⟨v, hv, rfl⟩
    rwa [h] at this
  · intro hv
    rw [← h] at hv
    obtain ⟨w, hw, hwv⟩ := mem_actSub.1 hv
    rwa [MulAction.injective g hwv] at hw

private theorem asG12_embSL_e {F : Type} [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) (hB : B.1 1 0 = 0) :
    embSL hij B • (Pi.single i 1 : Fin n → F) = (B.1 0 0) • (Pi.single i 1 : Fin n → F) := by
  funext k
  rw [smul_eq_mulVec', embSL_coe, emb_mulVec, blockMap_apply]
  by_cases hki : k = i
  · subst hki; simp [Pi.single_apply, Ne.symm hij]
  · by_cases hkj : k = j
    · subst hkj; simp [Pi.single_apply, hki, hB]
    · simp [Pi.single_apply, hki, hkj]

private theorem asG12_diag_exists {F : Type} [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {c : F} (hc : c ≠ 0) :
    ∃ g ∈ setStab F (Vi F n i), g • (Pi.single i 1 : Fin n → F) = c • (Pi.single i 1 : Fin n → F) := by
  have hB : (CFSG.Quasithin.SL2Model.dgm (Units.mk0 c hc)).1 1 0 = 0 := by
    simp [CFSG.Quasithin.SL2Model.dgm]
  refine ⟨embSL hij (CFSG.Quasithin.SL2Model.dgm (Units.mk0 c hc)), ?_, ?_⟩
  · exact asG12_mem_setStab_of_actSub (actSub_embSL_of_lower_left_zero hij hB)
  · rw [asG12_embSL_e hij _ hB]
    congr 1

private def asG12_psi {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (i0 : Fin n) (j : Fin s) : F →+ U :=
  AddMonoidHom.mk' (fun c => Θ (Pi.single j (Pi.single i0 c)))
    (fun a b => by simp only [Pi.single_add, map_add])

private theorem asG12_psi_apply_symm {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (i0 : Fin n) (j : Fin s) (c : F) :
    Θ.symm (asG12_psi Θ i0 j c) = Pi.single j (Pi.single i0 c) := by
  simp [asG12_psi]

private theorem asG12_psi_injective {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (i0 : Fin n) (j : Fin s) :
    Function.Injective (asG12_psi Θ i0 j) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have h1 := asG12_psi_apply_symm Θ i0 j c
  rw [hc, map_zero] at h1
  have h2 := congrFun (congrFun h1.symm j) i0
  simpa using h2

private theorem asG12_iSupIndep {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (i0 : Fin n) :
    iSupIndep (fun j : Fin s => (asG12_psi Θ i0 j).range) := by
  rw [iSupIndep_def]
  intro j
  rw [disjoint_iff]
  let P : U →+ (Fin n → F) := AddMonoidHom.mk' (fun u => Θ.symm u j) (fun a b => by simp)
  have hle : (⨆ (i : Fin s) (_ : i ≠ j), (asG12_psi Θ i0 i).range) ≤ P.ker := by
    refine iSup₂_le fun i hi => ?_
    rintro _ ⟨c, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show Θ.symm (asG12_psi Θ i0 i c) j = 0
    rw [asG12_psi_apply_symm]
    simp [Pi.single_eq_of_ne (Ne.symm hi)]
  rw [eq_bot_iff]
  rintro u ⟨⟨c, rfl⟩, hu⟩
  have h0 := hle hu
  rw [AddMonoidHom.mem_ker] at h0
  have h3 : P (asG12_psi Θ i0 j c) = Pi.single i0 c := by
    show Θ.symm (asG12_psi Θ i0 j c) j = Pi.single i0 c
    rw [asG12_psi_apply_symm, Pi.single_eq_same]
  rw [h3] at h0
  have hc : c = 0 := by simpa using congrFun h0 i0
  simp [hc]

private theorem asG12_single_eq_smul {F : Type} [Field F] {n : ℕ} (i0 : Fin n) (x : F) :
    (Pi.single i0 x : Fin n → F) = x • (Pi.single i0 1 : Fin n → F) := by
  funext k
  by_cases hk : k = i0
  · subst hk; simp
  · simp [hk]

private theorem asG12_smul_psi {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x)
    (i0 : Fin n) (j : Fin s) {g : Matrix.SpecialLinearGroup (Fin n) F} {c : F}
    (hg : g • (Pi.single i0 1 : Fin n → F) = c • (Pi.single i0 1 : Fin n → F)) (a : F) :
    g • asG12_psi Θ i0 j a = asG12_psi Θ i0 j (a * c) := by
  show g • Θ (Pi.single j (Pi.single i0 a)) = Θ (Pi.single j (Pi.single i0 (a * c)))
  rw [← hΘ]
  congr 1
  funext l
  by_cases hl : l = j
  · subst hl
    rw [Pi.single_eq_same, Pi.single_eq_same, asG12_single_eq_smul i0 a,
      smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', hg, smul_smul,
      asG12_single_eq_smul i0 (a * c)]
  · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, smul_zero]

private theorem asG12_irred {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x)
    {i0 i1 : Fin n} (hi : i0 ≠ i1) (j : Fin s) :
    IsIrreducibleSub (setStab F (Vi F n i0)) (asG12_psi Θ i0 j).range := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : asG12_psi Θ i0 j 1 ∈ (asG12_psi Θ i0 j).range := ⟨1, rfl⟩
    rw [h, AddSubgroup.mem_bot] at h1
    exact one_ne_zero ((asG12_psi_injective Θ i0 j) (h1.trans (map_zero _).symm))
  · intro g hg w hw
    obtain ⟨a, rfl⟩ := hw
    rw [asG12_smul_psi Θ hΘ i0 j (asG12_smul_e hg) a]
    exact ⟨_, rfl⟩
  · intro Y hY hYinv
    by_cases hY0 : Y = ⊥
    · exact Or.inl hY0
    · right
      obtain ⟨y, hyY, hy0⟩ : ∃ y ∈ Y, y ≠ 0 := by
        by_contra h
        push Not at h
        exact hY0 (eq_bot_iff.2 fun y hy => AddSubgroup.mem_bot.2 (h y hy))
      obtain ⟨a, rfl⟩ := hY hyY
      have ha : a ≠ 0 := by
        rintro rfl
        exact hy0 (map_zero _)
      refine le_antisymm hY ?_
      rintro w ⟨b, rfl⟩
      by_cases hb : b = 0
      · rw [hb, map_zero]
        exact Y.zero_mem
      · obtain ⟨g, hg, hgc⟩ :=
          asG12_diag_exists (j := i1) hi (c := a⁻¹ * b) (mul_ne_zero (inv_ne_zero ha) hb)
        have hw : asG12_psi Θ i0 j b = g • asG12_psi Θ i0 j a := by
          rw [asG12_smul_psi Θ hΘ i0 j hgc a, mul_inv_cancel_left₀ ha]
        rw [hw]
        exact hYinv g hg _ hyY

private theorem asG12_card {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (i0 : Fin n) (j : Fin s) :
    Nat.card (asG12_psi Θ i0 j).range = Nat.card F :=
  (Nat.card_congr (AddMonoidHom.ofInjective (asG12_psi_injective Θ i0 j)).toEquiv).symm

@[expose] def G_1_12 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : 3 ≤ n),
    ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
      [Finite U], (∀ u : U, u + u = 0) →
      ∀ φ : Submodule F (Fin n → F) → AddSubgroup U, G13Hyp F n U φ →
        (φ (Vi F n ⟨0, by omega⟩) = fixU (flagSylow F n) ∧
          φ (Vi F n ⟨0, by omega⟩) =
            fixU (oTwoPrimeUpper (setStab F (Vi F n (⟨0, by omega⟩ : Fin n))))) ∧
        ∃ s : ℕ, Nat.card (φ (Vi F n ⟨0, by omega⟩)) = Nat.card F ^ s ∧
          ∃ W : Fin s → AddSubgroup U, iSupIndep W ∧ (⨆ j, W j) = φ (Vi F n ⟨0, by omega⟩) ∧
            ∀ j, IsIrreducibleSub (setStab F (Vi F n (⟨0, by omega⟩ : Fin n))) (W j) ∧
              Nat.card (W j) = Nat.card F

private theorem asG12_mem_coord {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U) (k : Fin n)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)))
    (u : U) : u ∈ φ (Vi F n k) ↔ ∀ l, Θ.symm u l ∈ Vi F n k := by
  constructor
  · intro hu l
    obtain ⟨a, rfl⟩ := (hmem k _).1 hu
    rw [AddEquiv.symm_apply_apply]
    exact mem_Vi.2 fun m hm => by simp [Pi.single_apply, hm]
  · intro hu
    have hx : Θ.symm u = fun l => Pi.single k (Θ.symm u l k) := by
      funext l
      funext m
      by_cases hm : m = k
      · subst hm; simp
      · have := mem_Vi.1 (hu l) m hm
        simp [hm, this]
    exact (hmem k u).2 ⟨fun l => Θ.symm u l k, (Θ.apply_symm_apply u).symm.trans (congrArg Θ hx)⟩

private theorem asG12_range_le {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U) (i0 : Fin n)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)))
    (j : Fin s) : (asG12_psi Θ i0 j).range ≤ φ (Vi F n i0) := by
  rintro _ ⟨c, rfl⟩
  rw [asG12_mem_coord Θ φ i0 hmem]
  intro l
  rw [asG12_psi_apply_symm]
  by_cases hl : l = j
  · subst hl
    rw [Pi.single_eq_same]
    exact mem_Vi.2 fun k hk => by simp [Pi.single_apply, hk]
  · rw [Pi.single_eq_of_ne hl]
    exact Submodule.zero_mem _

private theorem asG12_ge {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U) (i0 : Fin n)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l))) :
    φ (Vi F n i0) ≤ ⨆ j, (asG12_psi Θ i0 j).range := by
  intro u hu
  obtain ⟨a, rfl⟩ := (hmem i0 u).1 hu
  have hsum : (fun l => (Pi.single i0 (a l) : Fin n → F)) =
      ∑ j, Pi.single j (Pi.single i0 (a j)) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hval : Θ (fun l => (Pi.single i0 (a l) : Fin n → F)) = ∑ j, asG12_psi Θ i0 j (a j) := by
    rw [hsum, map_sum]
    rfl
  rw [hval]
  exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.mem_iSup_of_mem j ⟨a j, rfl⟩

private theorem asG12_mem_fixU {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x)
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) (u : U) :
    u ∈ fixU X ↔ ∀ l, Θ.symm u l ∈ fixSub F X := by
  have key : ∀ t : Matrix.SpecialLinearGroup (Fin n) F,
      t • u = u ↔ ∀ l, t • Θ.symm u l = Θ.symm u l := by
    intro t
    constructor
    · intro h
      have h1 := hΘ t (Θ.symm u)
      rw [Θ.apply_symm_apply, h] at h1
      have h2 : (fun l => t • Θ.symm u l) = Θ.symm u := by
        apply Θ.injective
        rw [h1, Θ.apply_symm_apply]
      intro l
      exact congrFun h2 l
    · intro h
      have h2 : (fun l => t • Θ.symm u l) = Θ.symm u := funext h
      have h3 := hΘ t (Θ.symm u)
      rw [h2, Θ.apply_symm_apply] at h3
      exact h3.symm
  constructor
  · intro hu l t ht
    exact (key t).1 (hu t ht) l
  · intro hu t ht
    exact (key t).2 fun l => hu l t ht

private theorem asG12_eq_flag {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U] (hn : 2 ≤ n)
    (φ : Submodule F (Fin n → F) → AddSubgroup U) (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l))) :
    φ (Vi F n ⟨0, by omega⟩) = fixU (flagSylow F n) := by
  ext u
  rw [asG12_mem_coord Θ φ _ hmem, asG12_mem_fixU Θ hΘ, asG12_fixSub_flagSylow hn]

private theorem asG12_eq_oTwo {F U : Type} [Field F] [CharP F 2] {n s : ℕ} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U] (hn : 2 ≤ n)
    (φ : Submodule F (Fin n → F) → AddSubgroup U) (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l))) :
    φ (Vi F n ⟨0, by omega⟩) = fixU (oTwoPrimeUpper (setStab F (Vi F n ⟨0, by omega⟩))) := by
  ext u
  rw [asG12_mem_coord Θ φ _ hmem, asG12_mem_fixU Θ hΘ, asG12_fixSub_oTwo hn]

private theorem asG12_sup_eq {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U] (i0 : Fin n)
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l))) :
    (⨆ j, (asG12_psi Θ i0 j).range) = φ (Vi F n i0) :=
  le_antisymm (iSup_le fun j => asG12_range_le Θ φ i0 hmem j) (asG12_ge Θ φ i0 hmem)

private theorem asG10_vi_inter {F : Type} [Field F] {n : ℕ} {i j : Fin n} {v : Fin n → F}
    (hij : i ≠ j) (h1 : v ∈ Vi F n i) (h2 : v ∈ Vi F n j) : v = 0 := by
  funext k
  by_cases hki : k = i
  · subst hki
    exact mem_Vi.1 h2 _ hij
  · exact mem_Vi.1 h1 k hki

private theorem asG10_vi_zero {F : Type} [Field F] {n : ℕ} {i : Fin n} {v : Fin n → F}
    (h1 : v ∈ Vi F n i) (h0 : v i = 0) : v = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    exact h0
  · exact mem_Vi.1 h1 k hk

private theorem asG10_Vi_le_Vhat {F : Type} [Field F] {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    Vi F n j ≤ Vhat F n k :=
  le_iSup (fun m : {m : Fin n // m ≠ k} => Vi F n m.1) ⟨j, hjk⟩

private theorem asG10_Vij_Vhatij {F : Type} [Field F] {n : ℕ} {i j : Fin n} {v : Fin n → F}
    (hij : i ≠ j) (h1 : v ∈ Vi F n i ⊔ Vi F n j) (h2 : v ∈ Vhat F n i ⊓ Vhat F n j) :
    v = 0 := by
  funext k
  by_cases hki : k = i
  · subst hki
    exact mem_Vhat.1 (Submodule.mem_inf.1 h2).1
  · by_cases hkj : k = j
    · subst hkj
      exact mem_Vhat.1 (Submodule.mem_inf.1 h2).2
    · exact (mem_Vij hij).1 h1 k hki hkj

private theorem asG10_fixSub_Rij {F : Type} [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    fixSub F (Rij F i j) = Vhat F n j := by
  ext v
  show (∀ t ∈ Rij F i j, t • v = v) ↔ v ∈ Vhat F n j
  rw [mem_Vhat]
  constructor
  · intro hv
    have h := congrFun (hv _ (T_mem_Rij hij 1)) i
    rw [T_smul_apply, if_pos rfl] at h
    simpa using h
  · intro hv t ht
    obtain ⟨b, rfl⟩ := (mem_Rij_iff hij).1 ht
    funext m
    rw [T_smul_apply]
    by_cases hm : m = i
    · subst hm
      simp [hv]
    · simp [hm]

private theorem asG10_transvection_mem_Vij {F : Type} [Field F] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (b : F) :
    Matrix.SpecialLinearGroup.transvection hij b ∈ setStab F (Vi F n i ⊔ Vi F n j) := by
  intro w
  rw [mem_Vij hij, mem_Vij hij]
  constructor
  · intro hw k hk1 hk2
    rw [T_smul_apply, if_neg hk1, add_zero]
    exact hw k hk1 hk2
  · intro hw k hk1 hk2
    have h := hw k hk1 hk2
    rw [T_smul_apply, if_neg hk1, add_zero] at h
    exact h

private theorem asG10_Lij_le_setStab {F : Type} [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Lij F i j ≤ setStab F (Vi F n i ⊔ Vi F n j) := by
  unfold Lij
  refine sup_le ?_ ?_
  · intro t ht
    obtain ⟨b, rfl⟩ := (mem_Rij_iff hij).1 ht
    exact asG10_transvection_mem_Vij hij b
  · intro t ht
    obtain ⟨b, rfl⟩ := (mem_Rij_iff hij.symm).1 ht
    have h := asG10_transvection_mem_Vij hij.symm b
    rwa [sup_comm] at h

private theorem asG10_eq_zero_of_coord {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (u : U) (h : ∀ l, Θ.symm u l = 0) : u = 0 := by
  have h' : Θ.symm u = 0 := funext h
  exact Θ.symm.injective (by rw [h', map_zero])

private def asG10_blk {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (j : Fin s) : (Fin n → F) →+ U :=
  AddMonoidHom.mk' (fun v => Θ (Pi.single j v))
    (fun a b => by simp only [Pi.single_add, map_add])

private theorem asG10_blk_apply_symm {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (j : Fin s) (v : Fin n → F) :
    Θ.symm (asG10_blk Θ j v) = Pi.single j v := by
  simp [asG10_blk]

private theorem asG10_blk_injective {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (j : Fin s) : Function.Injective (asG10_blk Θ j) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 := asG10_blk_apply_symm Θ j v
  rw [hv, map_zero] at h1
  have h2 := congrFun h1.symm j
  simpa using h2

private theorem asG10_iSupIndep {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (A : Submodule F (Fin n → F)) :
    iSupIndep (fun j : Fin s => A.toAddSubgroup.map (asG10_blk Θ j)) := by
  rw [iSupIndep_def]
  intro j
  rw [disjoint_iff]
  let P : U →+ (Fin n → F) := AddMonoidHom.mk' (fun u => Θ.symm u j) (fun a b => by simp)
  have hle : (⨆ (i : Fin s) (_ : i ≠ j), A.toAddSubgroup.map (asG10_blk Θ i)) ≤ P.ker := by
    refine iSup₂_le fun i hi => ?_
    rintro _ ⟨v, -, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show Θ.symm (asG10_blk Θ i v) j = 0
    rw [asG10_blk_apply_symm, Pi.single_eq_of_ne (Ne.symm hi)]
  rw [eq_bot_iff]
  rintro u ⟨⟨v, -, rfl⟩, hu⟩
  have h0 := hle hu
  rw [AddMonoidHom.mem_ker] at h0
  have h3 : P (asG10_blk Θ j v) = v := by
    show Θ.symm (asG10_blk Θ j v) j = v
    rw [asG10_blk_apply_symm, Pi.single_eq_same]
  rw [h3] at h0
  rw [h0, map_zero, AddSubgroup.mem_bot]

private theorem asG10_mem_blk_sup {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    (Θ : (Fin s → Fin n → F) ≃+ U) (A : Submodule F (Fin n → F)) (u : U) :
    u ∈ ⨆ j : Fin s, A.toAddSubgroup.map (asG10_blk Θ j) ↔ ∀ l, Θ.symm u l ∈ A := by
  constructor
  · intro hu
    refine AddSubgroup.iSup_induction (fun j : Fin s => A.toAddSubgroup.map (asG10_blk Θ j))
      (C := fun u => ∀ l, Θ.symm u l ∈ A) hu ?_ ?_ ?_
    · rintro j _ ⟨v, hv, rfl⟩ l
      rw [asG10_blk_apply_symm]
      by_cases hl : l = j
      · subst hl
        rw [Pi.single_eq_same]
        exact hv
      · rw [Pi.single_eq_of_ne hl]
        exact A.zero_mem
    · intro l
      simp [A.zero_mem]
    · intro x y hx hy l
      rw [map_add, Pi.add_apply]
      exact A.add_mem (hx l) (hy l)
  · intro hu
    have hdec : u = ∑ j, asG10_blk Θ j (Θ.symm u j) := by
      calc u = Θ (Θ.symm u) := (Θ.apply_symm_apply u).symm
        _ = Θ (∑ j, Pi.single j (Θ.symm u j)) := by rw [Finset.univ_sum_single]
        _ = ∑ j, Θ (Pi.single j (Θ.symm u j)) := map_sum Θ _ _
    rw [hdec]
    exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.mem_iSup_of_mem j ⟨Θ.symm u j, hu j, rfl⟩

private theorem asG10_smul_blk {F U : Type} [Field F] [AddCommGroup U] {n s : ℕ}
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x)
    (m : Fin s) (g : Matrix.SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    g • asG10_blk Θ m v = asG10_blk Θ m (g • v) := by
  show g • Θ (Pi.single m v) = Θ (Pi.single m (g • v))
  rw [← hΘ]
  congr 1
  funext l
  by_cases hl : l = m
  · subst hl
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, smul_zero]

private theorem asG10_mem_iSup {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)))
    (J : Fin n → Prop) (M : Submodule F (Fin n → F))
    (hM1 : ∀ j, J j → Vi F n j ≤ M) (hM2 : ∀ v ∈ M, ∀ j, ¬ J j → v j = 0) (u : U) :
    u ∈ ⨆ j : {j : Fin n // J j}, φ (Vi F n j.1) ↔ ∀ l, Θ.symm u l ∈ M := by
  constructor
  · intro hu
    refine AddSubgroup.iSup_induction (fun j : {j : Fin n // J j} => φ (Vi F n j.1))
      (C := fun u => ∀ l, Θ.symm u l ∈ M) hu ?_ ?_ ?_
    · rintro ⟨j, hj⟩ x hx l
      exact hM1 j hj ((asG12_mem_coord Θ φ j hmem x).1 hx l)
    · intro l
      simp [M.zero_mem]
    · intro x y hx hy l
      rw [map_add, Pi.add_apply]
      exact M.add_mem (hx l) (hy l)
  · intro hu
    have hx : Θ.symm u = ∑ j : Fin n, (fun l => (Pi.single j (Θ.symm u l j) : Fin n → F)) := by
      funext l
      rw [Finset.sum_apply]
      exact (Finset.univ_sum_single (Θ.symm u l)).symm
    have hdec : u = ∑ j : Fin n, Θ (fun l => (Pi.single j (Θ.symm u l j) : Fin n → F)) := by
      calc u = Θ (Θ.symm u) := (Θ.apply_symm_apply u).symm
        _ = Θ (∑ j : Fin n, (fun l => (Pi.single j (Θ.symm u l j) : Fin n → F))) :=
          congrArg Θ hx
        _ = ∑ j : Fin n, Θ (fun l => (Pi.single j (Θ.symm u l j) : Fin n → F)) := map_sum Θ _ _
    rw [hdec]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    by_cases hJ : J j
    · exact AddSubgroup.mem_iSup_of_mem (⟨j, hJ⟩ : {j : Fin n // J j})
        ((hmem j _).2 ⟨fun l => Θ.symm u l j, rfl⟩)
    · have hz : (fun l => (Pi.single j (Θ.symm u l j) : Fin n → F)) = 0 := by
        funext l
        have h0 := hM2 _ (hu l) j hJ
        simp [h0]
      rw [hz, map_zero]
      exact AddSubgroup.zero_mem _

private theorem asG10_sup_two {F U : Type} [Field F] {n : ℕ} [AddCommGroup U]
    (φ : Submodule F (Fin n → F) → AddSubgroup U) (i j : Fin n) :
    φ (Vi F n i) ⊔ φ (Vi F n j) = ⨆ k : {k : Fin n // k = i ∨ k = j}, φ (Vi F n k.1) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact le_iSup (fun k : {k : Fin n // k = i ∨ k = j} => φ (Vi F n k.1)) ⟨i, Or.inl rfl⟩
    · exact le_iSup (fun k : {k : Fin n // k = i ∨ k = j} => φ (Vi F n k.1)) ⟨j, Or.inr rfl⟩
  · refine iSup_le fun k => ?_
    rcases k with ⟨k, hk⟩
    rcases hk with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right

private theorem asG10_mem_Uij {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)))
    {i j : Fin n} (hij : i ≠ j) (u : U) :
    u ∈ Uij φ i j ↔ ∀ l, Θ.symm u l ∈ Vij F i j := by
  show u ∈ φ (Vi F n i) ⊔ φ (Vi F n j) ↔ _
  rw [asG10_sup_two φ i j]
  refine asG10_mem_iSup Θ φ hmem (fun k => k = i ∨ k = j) (Vij F i j) ?_ ?_ u
  · intro m hm
    rcases hm with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · intro v hv m hm
    rw [not_or] at hm
    exact (mem_Vij hij).1 hv m hm.1 hm.2

private theorem asG10_mem_Uhatij {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)))
    {i j : Fin n} (hij : i ≠ j) (u : U) :
    u ∈ Uhatij φ i j ↔ ∀ l, Θ.symm u l ∈ Vhatij F i j := by
  show u ∈ ⨆ k : {k : Fin n // k ≠ i ∧ k ≠ j}, φ (Vi F n k.1) ↔ _
  refine asG10_mem_iSup Θ φ hmem (fun k => k ≠ i ∧ k ≠ j) (Vhatij F i j) ?_ ?_ u
  · intro m hm
    exact le_inf (asG10_Vi_le_Vhat hm.1) (asG10_Vi_le_Vhat hm.2)
  · intro v hv m hm
    simp only [not_and_or, not_not] at hm
    rcases hm with rfl | rfl
    · exact mem_Vhat.1 (Submodule.mem_inf.1 hv).1
    · exact mem_Vhat.1 (Submodule.mem_inf.1 hv).2

private theorem asG10_mem_Uhat {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    (Θ : (Fin s → Fin n → F) ≃+ U) (φ : Submodule F (Fin n → F) → AddSubgroup U)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)))
    (k : Fin n) (u : U) :
    u ∈ Uhat φ k ↔ ∀ l, Θ.symm u l ∈ Vhat F n k := by
  show u ∈ ⨆ m : {m : Fin n // m ≠ k}, φ (Vi F n m.1) ↔ _
  refine asG10_mem_iSup Θ φ hmem (fun m => m ≠ k) (Vhat F n k) ?_ ?_ u
  · intro m hm
    exact asG10_Vi_le_Vhat hm
  · intro v hv m hm
    have hmk : m = k := not_not.1 hm
    rw [hmk]
    exact mem_Vhat.1 hv

private theorem asG10_main {F U : Type} [Field F] {n s : ℕ} [AddCommGroup U]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U] (hn : 2 ≤ n)
    (φ : Submodule F (Fin n → F) → AddSubgroup U) (hφ : G13Hyp F n U φ)
    (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x)
    (hmem : ∀ (k : Fin n) (u : U),
      u ∈ φ (Vi F n k) ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)))
    {i j : Fin n} (hij : i ≠ j) :
    (Disjoint (φ (Vi F n i)) (φ (Vi F n j)) ∧
        IsSumOfNatural (Lij F i j) (Vij F i j) (Uij φ i j) s) ∧
      IsCompl (Uij φ i j) (Uhatij φ i j) ∧
      Uhatij φ i j = fixU (Lij F i j) ∧
      (Disjoint (φ (Vi F n i)) (Uhatij φ i j) ∧
        Uhat φ j = φ (Vi F n i) ⊔ Uhatij φ i j ∧ Uhat φ j = fixU (Rij F i j)) ∧
      IsCompl (φ (Vi F n i)) (Uhat φ i) := by
  have hA : Disjoint (φ (Vi F n i)) (φ (Vi F n j)) := by
    rw [disjoint_iff, eq_bot_iff]
    intro u hu
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hu
    rw [AddSubgroup.mem_bot]
    exact asG10_eq_zero_of_coord Θ u fun l =>
      asG10_vi_inter hij ((asG12_mem_coord Θ φ i hmem u).1 h1 l)
        ((asG12_mem_coord Θ φ j hmem u).1 h2 l)
  have hS : IsSumOfNatural (Lij F i j) (Vij F i j) (Uij φ i j) s := by
    refine ⟨fun m => (Vij F i j).toAddSubgroup.map (asG10_blk Θ m), asG10_iSupIndep Θ _, ?_, ?_⟩
    · ext u
      rw [asG10_mem_blk_sup Θ (Vij F i j) u, asG10_mem_Uij Θ φ hmem hij u]
    · intro m
      refine ⟨?_, asG10_blk Θ m, ?_, rfl, ?_⟩
      · intro g hg w hw
        obtain ⟨v, hv, rfl⟩ := hw
        rw [asG10_smul_blk Θ hΘ]
        exact ⟨g • v, ((asG10_Lij_le_setStab hij hg) v).1 hv, rfl⟩
      · intro x _ y _ h
        exact asG10_blk_injective Θ m h
      · intro g _ v _
        exact (asG10_smul_blk Θ hΘ m g v).symm
  have hB : IsCompl (Uij φ i j) (Uhatij φ i j) := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro u hu
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hu
      rw [AddSubgroup.mem_bot]
      exact asG10_eq_zero_of_coord Θ u fun l =>
        asG10_Vij_Vhatij hij ((asG10_mem_Uij Θ φ hmem hij u).1 h1 l)
          ((asG10_mem_Uhatij Θ φ hmem hij u).1 h2 l)
    · rw [codisjoint_iff, eq_top_iff, ← iSup_phi_Vi_eq_top hn hφ]
      refine iSup_le fun k => ?_
      by_cases hki : k = i
      · rw [hki]
        exact le_sup_of_le_left le_sup_left
      · by_cases hkj : k = j
        · rw [hkj]
          exact le_sup_of_le_left le_sup_right
        · exact le_sup_of_le_right
            (le_iSup (fun m : {m : Fin n // m ≠ i ∧ m ≠ j} => φ (Vi F n m.1)) ⟨k, ⟨hki, hkj⟩⟩)
  have hC : Uhatij φ i j = fixU (Lij F i j) := by
    ext u
    rw [asG10_mem_Uhatij Θ φ hmem hij u, asG12_mem_fixU Θ hΘ, fixSub_Lij hij]
  have hD1 : Disjoint (φ (Vi F n i)) (Uhatij φ i j) := by
    rw [disjoint_iff, eq_bot_iff]
    intro u hu
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hu
    rw [AddSubgroup.mem_bot]
    exact asG10_eq_zero_of_coord Θ u fun l =>
      asG10_vi_zero ((asG12_mem_coord Θ φ i hmem u).1 h1 l)
        (mem_Vhat.1 (Submodule.mem_inf.1 ((asG10_mem_Uhatij Θ φ hmem hij u).1 h2 l)).1)
  have hD2 : Uhat φ j = φ (Vi F n i) ⊔ Uhatij φ i j := by
    ext u
    constructor
    · intro hu
      have hu' := (asG10_mem_Uhat Θ φ hmem j u).1 hu
      have hu0 : Θ (fun l => (Pi.single i (Θ.symm u l i) : Fin n → F)) ∈ φ (Vi F n i) :=
        (hmem i _).2 ⟨fun l => Θ.symm u l i, rfl⟩
      have hrest : u - Θ (fun l => (Pi.single i (Θ.symm u l i) : Fin n → F)) ∈
          Uhatij φ i j := by
        rw [asG10_mem_Uhatij Θ φ hmem hij]
        intro l
        have e : Θ.symm (u - Θ (fun l => (Pi.single i (Θ.symm u l i) : Fin n → F))) l =
            Θ.symm u l - Pi.single i (Θ.symm u l i) := by
          rw [map_sub, AddEquiv.symm_apply_apply]
          rfl
        rw [e]
        refine Submodule.mem_inf.2 ⟨mem_Vhat.2 ?_, mem_Vhat.2 ?_⟩
        · simp
        · have h1 := mem_Vhat.1 (hu' l)
          simp [Pi.single_eq_of_ne (Ne.symm hij), h1]
      exact AddSubgroup.mem_sup.2 ⟨_, hu0, _, hrest, by abel⟩
    · intro hu
      obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hu
      rw [asG10_mem_Uhat Θ φ hmem j]
      intro l
      rw [map_add, Pi.add_apply]
      exact Submodule.add_mem _ (asG10_Vi_le_Vhat hij ((asG12_mem_coord Θ φ i hmem y).1 hy l))
        (Submodule.mem_inf.1 ((asG10_mem_Uhatij Θ φ hmem hij z).1 hz l)).2
  have hD3 : Uhat φ j = fixU (Rij F i j) := by
    ext u
    rw [asG10_mem_Uhat Θ φ hmem j u, asG12_mem_fixU Θ hΘ, asG10_fixSub_Rij hij]
  have hE : IsCompl (φ (Vi F n i)) (Uhat φ i) := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro u hu
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hu
      rw [AddSubgroup.mem_bot]
      exact asG10_eq_zero_of_coord Θ u fun l =>
        asG10_vi_zero ((asG12_mem_coord Θ φ i hmem u).1 h1 l)
          (mem_Vhat.1 ((asG10_mem_Uhat Θ φ hmem i u).1 h2 l))
    · rw [codisjoint_iff, eq_top_iff, ← iSup_phi_Vi_eq_top hn hφ]
      refine iSup_le fun k => ?_
      by_cases hki : k = i
      · rw [hki]
        exact le_sup_left
      · exact le_sup_of_le_right
          (le_iSup (fun m : {m : Fin n // m ≠ i} => φ (Vi F n m.1)) ⟨k, hki⟩)
  exact ⟨⟨hA, hS⟩, hB, hC, ⟨hD1, hD2, hD3⟩, hE⟩

theorem as_G_1_10 : G_1_10 := by
  intro F _ _ _ n hn U _ _ _ hsq φ hφ
  obtain ⟨s, Θ, hΘ, hcard, hmem⟩ := G13Fam.exists_equiv_fam (asG11_fam hφ hn) hsq
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn1 : 1 < n := lt_of_lt_of_le (by norm_num) hn
  exact ⟨s, hcard, asG10_main hn φ hφ Θ hΘ hmem
    (show (⟨0, hn0⟩ : Fin n) ≠ ⟨1, hn1⟩ by simp [Fin.ext_iff])⟩

theorem as_G_1_12 : G_1_12 := by
  intro F _ _ _ n hn3 U _ _ _ hsq φ hφ
  have hn : 2 ≤ n := by omega
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn1 : 1 < n := lt_of_lt_of_le (by norm_num) hn
  obtain ⟨s, Θ, hΘ, hcard, hmem⟩ := G13Fam.exists_equiv_fam (asG11_fam hφ hn) hsq
  exact ⟨⟨asG12_eq_flag hn φ Θ hΘ hmem, asG12_eq_oTwo hn φ Θ hΘ hmem⟩, s, hcard,
    fun j => (asG12_psi Θ ⟨0, hn0⟩ j).range, asG12_iSupIndep Θ _,
    asG12_sup_eq ⟨0, hn0⟩ Θ φ hmem,
    fun j => ⟨asG12_irred Θ hΘ (i0 := ⟨0, hn0⟩) (i1 := ⟨1, hn1⟩)
      (by simp [Fin.ext_iff]) j, asG12_card Θ _ j⟩⟩

end CFSG.ASVolI
