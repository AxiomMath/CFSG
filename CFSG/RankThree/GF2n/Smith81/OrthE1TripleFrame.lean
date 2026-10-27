module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleCocycle
public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleFactors
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
public import CFSG.CGT.PushingUpLit.A78.BenderTI
public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCForms
public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCSplit

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

open CFSG CFSG.Open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Tensor

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem omega_tensor (hK : 4 ≤ Nat.card K) {A : GL (Fin 2 ⊕ Fin 2) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus 2 K)) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ X, toMat K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (toMat K).symm X) =
        (z.1 : Matrix (Fin 2) (Fin 2) K) * X * ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) := by
  have hmem : Ψ K A ∈ (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom :=
    ⟨A, hA, rfl⟩
  rw [map_statedOmega, commutator_eq_range hK] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, fun X => ?_⟩
  have h1 := LinearEquiv.congr_fun hz X
  rw [Ψ_apply] at h1
  rw [← h1]
  exact (specialRho_apply z X).symm

theorem exists_omega_of_tensor (hK : 4 ≤ Nat.card K)
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ A ∈ StatedOmega (StatedQuadPlus 2 K), ∀ X,
      toMat K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (toMat K).symm X) =
        (z.1 : Matrix (Fin 2) (Fin 2) K) * X * ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) := by
  have hmem : (rho' K z : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) ∈
      (rho' K).range := ⟨z, rfl⟩
  rw [← commutator_eq_range hK, ← map_statedOmega] at hmem
  obtain ⟨A, hA, hAz⟩ := hmem
  refine ⟨A, hA, fun X => ?_⟩
  have h1 : toMat K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (toMat K).symm X) =
      rho' K z X := by
    rw [← Ψ_apply]
    exact LinearEquiv.congr_fun hAz X
  rw [h1]
  exact (specialRho_apply z X).symm


end Tensor

section FrameData

variable {K : Type} [Field K] [Finite K] [CharP K 2] {S : QSpace K} {V : Submodule K S.E}
  {𝔛 : Subgroup (S.E ≃ₗ[K] S.E)} (D : LCData S V 𝔛)
  (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))

@[expose] noncomputable def cM : ↥V ≃ₗ[K] Matrix (Fin 2) (Fin 2) K := c.trans (toMat K)

@[expose] def Rel (g : ↥𝔛) (z : Matrix.SpecialLinearGroup (Fin 2) K ×
    Matrix.SpecialLinearGroup (Fin 2) K) : Prop :=
  ∀ v : V, cM c (D.act g v) = (z.1 : Matrix (Fin 2) (Fin 2) K) * cM c v *
    ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

variable (hact : ActsAsNatural S V 𝔛 c (StatedQuadPlus 2 K)) (hK : 4 ≤ Nat.card K)
include hact hK

theorem exists_rel (g : ↥𝔛) : ∃ z, Rel D c g z := by
  obtain ⟨hX, h1, -, -⟩ := hact
  obtain ⟨A, hA, hAe⟩ := h1 g g.2
  obtain ⟨z, hz⟩ := omega_tensor hK hA
  refine ⟨z, fun v => ?_⟩
  have e1 : c (D.act g v) = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ c v := by
    have := hAe v v.2
    convert this using 2
    exact Subtype.ext (D.act_coe g v)
  have e2 := hz (cM c v)
  simp only [cM, LinearEquiv.trans_apply] at e2 ⊢
  rw [e1]
  simpa using e2

theorem exists_lift
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ g : ↥𝔛, Rel D c g z := by
  obtain ⟨hX, -, h2, -⟩ := hact
  obtain ⟨A, hA, hz⟩ := exists_omega_of_tensor hK z
  obtain ⟨g, hg, hge⟩ := h2 A hA
  refine ⟨⟨g, hg⟩, fun v => ?_⟩
  have e1 : c (D.act ⟨g, hg⟩ v) = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ c v := by
    have := hge v v.2
    convert this using 2
    exact Subtype.ext (D.act_coe ⟨g, hg⟩ v)
  have e2 := hz (cM c v)
  simp only [cM, LinearEquiv.trans_apply] at e2 ⊢
  rw [e1]
  simpa using e2

theorem rel_unique {g : ↥𝔛} {z z' : Matrix.SpecialLinearGroup (Fin 2) K ×
    Matrix.SpecialLinearGroup (Fin 2) K} (h : Rel D c g z) (h' : Rel D c g z') : z = z' := by
  apply specialRho_injective (K := K)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  obtain ⟨v, rfl⟩ := (cM c).surjective X
  have e := (h v).symm.trans (h' v)
  rw [specialRho_apply, specialRho_apply]
  exact e

theorem eq_of_rel {g g' : ↥𝔛} {z : Matrix.SpecialLinearGroup (Fin 2) K ×
    Matrix.SpecialLinearGroup (Fin 2) K} (h : Rel D c g z) (h' : Rel D c g' z) : g = g' := by
  obtain ⟨hX, -, -, h3⟩ := hact
  have hv : ∀ v : V, D.act g v = D.act g' v := fun v =>
    (cM c).injective ((h v).trans (h' v).symm)
  have hv' : ∀ v ∈ V, (g : S.E ≃ₗ[K] S.E) v = (g' : S.E ≃ₗ[K] S.E) v := fun v hv0 => by
    have := congrArg Subtype.val (hv ⟨v, hv0⟩)
    rwa [D.act_coe, D.act_coe] at this
  have h1 : ((g⁻¹ * g' : ↥𝔛) : S.E ≃ₗ[K] S.E) = 1 := by
    apply h3 _ (g⁻¹ * g' : ↥𝔛).2
    intro v hv0
    change (g : S.E ≃ₗ[K] S.E)⁻¹ ((g' : S.E ≃ₗ[K] S.E) v) = v
    rw [← hv' v hv0]
    simp
  have h2 : g⁻¹ * g' = 1 := Subtype.ext h1
  exact inv_mul_eq_one.mp h2

theorem rel_mul {g h : ↥𝔛} {z w : Matrix.SpecialLinearGroup (Fin 2) K ×
    Matrix.SpecialLinearGroup (Fin 2) K} (hg : Rel D c g z) (hh : Rel D c h w) :
    Rel D c (g * h) (z * w) := by
  intro v
  have e : D.act (g * h) v = D.act g (D.act h v) :=
    Subtype.ext (by rw [D.act_coe, D.act_coe, D.act_coe]; rfl)
  rw [e, hg, hh]
  simp [mul_assoc, Matrix.SpecialLinearGroup.coe_mul, mul_inv_rev]

theorem rel_one : Rel D c (1 : ↥𝔛) 1 := by
  intro v
  have e : D.act 1 v = v := Subtype.ext (by rw [D.act_coe]; rfl)
  rw [e]
  simp

noncomputable def lift
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    ↥𝔛 := Classical.choose (exists_lift D c hact hK z)

theorem lift_rel (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    Rel D c (lift D c hact hK z) z := Classical.choose_spec (exists_lift D c hact hK z)

noncomputable def liftHom :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* ↥𝔛 where
  toFun := lift D c hact hK
  map_one' := eq_of_rel D c hact hK (lift_rel D c hact hK 1) (rel_one D c hact hK)
  map_mul' z w := eq_of_rel D c hact hK (lift_rel D c hact hK (z * w))
    (rel_mul D c hact hK (lift_rel D c hact hK z) (lift_rel D c hact hK w))

theorem liftHom_rel
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    Rel D c (liftHom D c hact hK z) z := lift_rel D c hact hK z

theorem liftHom_injective : Function.Injective (liftHom D c hact hK) := by
  intro z z' h
  exact rel_unique D c hact hK (liftHom_rel D c hact hK z)
    (h ▸ liftHom_rel D c hact hK z')

theorem liftHom_surjective : Function.Surjective (liftHom D c hact hK) := by
  intro g
  obtain ⟨z, hz⟩ := exists_rel D c hact hK g
  exact ⟨z, eq_of_rel D c hact hK (liftHom_rel D c hact hK z) hz⟩

noncomputable def Phi :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      (S.E ≃ₗ[K] S.E) := 𝔛.subtype.comp (liftHom D c hact hK)

theorem Phi_injective : Function.Injective (Phi D c hact hK) :=
  Subtype.val_injective.comp (liftHom_injective D c hact hK)

theorem Phi_range : (Phi D c hact hK).range = 𝔛 := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact (liftHom D c hact hK z).2
  · intro hg
    obtain ⟨z, hz⟩ := liftHom_surjective D c hact hK ⟨g, hg⟩
    exact ⟨z, congrArg Subtype.val hz⟩

noncomputable def leftG : Subgroup (S.E ≃ₗ[K] S.E) :=
  ((Phi D c hact hK).comp (MonoidHom.inl _ _)).range

noncomputable def rightG : Subgroup (S.E ≃ₗ[K] S.E) :=
  ((Phi D c hact hK).comp (MonoidHom.inr _ _)).range

end FrameData

section Complement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {S : QSpace K} {V : Submodule K S.E}
  {𝔛 : Subgroup (S.E ≃ₗ[K] S.E)} {D : LCData S V 𝔛}

theorem exists_section (D : LCData S V 𝔛) : ∃ s : ↥V →ₗ[K] S.E, ∀ u, D.β0 (s u) = u := by
  obtain ⟨s, hs⟩ := D.β0.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr D.β0_surjective)
  exact ⟨s, fun u => by simpa using LinearMap.congr_fun hs u⟩

theorem mem_V_of_comm (s : ↥V →ₗ[K] S.E) (hs : ∀ u, D.β0 (s u) = u) (g : ↥𝔛) (v : ↥V) :
    (g : S.E ≃ₗ[K] S.E) (s v) - s (D.act g v) ∈ V := by
  rw [← D.β0_eq_zero_iff, map_sub, D.β0_act g (s v), hs, hs, sub_self]

@[expose] noncomputable def cocycle0 (s : ↥V →ₗ[K] S.E) (hs : ∀ u, D.β0 (s u) = u) (g : ↥𝔛) :
    Module.End K ↥V :=
  LinearMap.codRestrict V
    (((g : S.E ≃ₗ[K] S.E) : S.E →ₗ[K] S.E) ∘ₗ s - s ∘ₗ D.act g) (mem_V_of_comm s hs g)

theorem cocycle0_apply (s : ↥V →ₗ[K] S.E) (hs : ∀ u, D.β0 (s u) = u) (g : ↥𝔛) (v : ↥V) :
    ((cocycle0 s hs g v : ↥V) : S.E) = (g : S.E ≃ₗ[K] S.E) (s v) - s (D.act g v) := rfl

theorem cocycle0_mul (s : ↥V →ₗ[K] S.E) (hs : ∀ u, D.β0 (s u) = u) (g h : ↥𝔛) :
    cocycle0 s hs (g * h) = D.act g * cocycle0 s hs h + cocycle0 s hs g * D.act h := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have e1 : D.act (g * h) v = D.act g (D.act h v) :=
    Subtype.ext (by rw [D.act_coe, D.act_coe, D.act_coe]; rfl)
  simp only [cocycle0_apply, Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add, e1,
    D.act_coe, map_sub]
  have : ((g * h : ↥𝔛) : S.E ≃ₗ[K] S.E) (s v) =
      (g : S.E ≃ₗ[K] S.E) ((h : S.E ≃ₗ[K] S.E) (s v)) := rfl
  rw [this]
  abel

theorem algConj_act {c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)} {g : ↥𝔛}
    {z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K}
    (h : Rel D c g z) : (cM c).conjRingEquiv (D.act g) = rhoLin z := by
  apply LinearMap.ext
  intro X
  obtain ⟨v, rfl⟩ := (cM c).surjective X
  have h1 : (cM c).conjRingEquiv (D.act g) ((cM c) v) = (cM c) (D.act g v) := by
    change (cM c).conj (D.act g) ((cM c) v) = _
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  rw [h1]
  exact h v

theorem exists_split (hKF10 : H1TensorStatement) (hK : 4 ≤ Nat.card K)
    (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (hact : ActsAsNatural S V 𝔛 c (StatedQuadPlus 2 K)) :
    Nonempty D.Split := by
  obtain ⟨s, hs⟩ := exists_section D
  set 𝓒 := (cM c).conjRingEquiv with h𝓒
  let ct : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →
      Module.End K (Matrix (Fin 2) (Fin 2) K) :=
    fun z => 𝓒 (cocycle0 s hs (liftHom D c hact hK z))
  have hct : ∀ z w, ct (z * w) = rhoLin z * ct w + ct z * rhoLin w := by
    intro z w
    simp only [ct, map_mul, cocycle0_mul, map_add]
    rw [algConj_act (liftHom_rel D c hact hK z), algConj_act (liftHom_rel D c hact hK w)]
  obtain ⟨m, hm⟩ := cocycle_coboundary hKF10 hK ct hct
  set m₀ : Module.End K ↥V := 𝓒.symm m with hm₀def
  have hm₀ : ∀ g : ↥𝔛, cocycle0 s hs g = D.act g * m₀ - m₀ * D.act g := by
    intro g
    obtain ⟨z, rfl⟩ := liftHom_surjective D c hact hK g
    have h1 := hm z
    apply 𝓒.injective
    simp only [ct] at h1
    rw [h1, map_sub, map_mul, map_mul, algConj_act (liftHom_rel D c hact hK z)]
    simp [m₀]
  have h2 : ∀ x : S.E, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  let s' : ↥V →ₗ[K] S.E := s + V.subtype ∘ₗ m₀
  have hs' : ∀ v, D.β0 (s' v) = v := by
    intro v
    change D.β0 (s v + (m₀ v : S.E)) = v
    rw [map_add, hs, (D.β0_eq_zero_iff _).2 (m₀ v).2, add_zero]
  have hinv' : ∀ g : ↥𝔛, ∀ v, (g : S.E ≃ₗ[K] S.E) (s' v) = s' (D.act g v) := by
    intro g v
    have h1 := congrArg Subtype.val (LinearMap.congr_fun (hm₀ g) v)
    simp only [cocycle0_apply, LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub,
      D.act_coe] at h1
    change (g : S.E ≃ₗ[K] S.E) (s v + (m₀ v : S.E)) = s (D.act g v) + (m₀ (D.act g v) : S.E)
    rw [map_add]
    have h3 : (g : S.E ≃ₗ[K] S.E) (s v) = s (D.act g v) + ((g : S.E ≃ₗ[K] S.E) (m₀ v : S.E) -
        (m₀ (D.act g v) : S.E)) := by
      rw [← h1]; abel
    rw [h3]
    have h4 := h2 ((g : S.E ≃ₗ[K] S.E) (m₀ v : S.E))
    have h5 := h2 (m₀ (D.act g v) : S.E)
    have h6 : ∀ x y : S.E, x - y = x + y := fun x y => by
      rw [sub_eq_add_neg]
      congr 1
      exact (add_eq_zero_iff_neg_eq.mp (h2 y))
    rw [h6]
    calc s (D.act g v) + ((g : S.E ≃ₗ[K] S.E) (m₀ v : S.E) + (m₀ (D.act g v) : S.E)) +
        (g : S.E ≃ₗ[K] S.E) (m₀ v : S.E)
        = s (D.act g v) + (m₀ (D.act g v) : S.E) +
          ((g : S.E ≃ₗ[K] S.E) (m₀ v : S.E) + (g : S.E ≃ₗ[K] S.E) (m₀ v : S.E)) := by abel
      _ = _ := by rw [h4, add_zero]
  refine ⟨⟨LinearMap.range s', ?_, ?_⟩⟩
  · refine IsCompl.of_eq ?_ ?_
    · apply eq_bot_iff.mpr
      intro e he
      obtain ⟨hV, ⟨v, rfl⟩⟩ := Submodule.mem_inf.mp he
      have h7 := (D.β0_eq_zero_iff _).2 hV
      rw [hs'] at h7
      rw [h7]
      simp
    · apply eq_top_iff.mpr
      intro e _
      have h8 : e - s' (D.β0 e) ∈ V := by
        rw [← D.β0_eq_zero_iff, map_sub, hs', sub_self]
      have : e = (e - s' (D.β0 e)) + s' (D.β0 e) := by abel
      rw [this]
      exact Submodule.add_mem_sup h8 ⟨_, rfl⟩
  · rintro g hg e ⟨v, rfl⟩
    exact ⟨D.act ⟨g, hg⟩ v, (hinv' ⟨g, hg⟩ v).symm⟩

end Complement

section FrameMap

variable {K : Type} [Field K] [Finite K] [CharP K 2] {S : QSpace K} {V : Submodule K S.E}
  {𝔛 : Subgroup (S.E ≃ₗ[K] S.E)} {D : LCData S V 𝔛}

@[expose] def pairT : (Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) ≃ₗ[K] Tensor3 K where
  toFun p a b c := if a = 0 then p.1 b c else p.2 b c
  map_add' p q := by
    funext a b c
    by_cases h : a = 0 <;> simp [h]
  map_smul' r p := by
    funext a b c
    by_cases h : a = 0 <;> simp [h]
  invFun T := (Matrix.of fun b c => T 0 b c, Matrix.of fun b c => T 1 b c)
  left_inv p := by
    ext <;> simp
  right_inv T := by
    funext a b c
    fin_cases a <;> simp

theorem pairT_apply (p : Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) (a b c : Fin 2) :
    pairT p a b c = if a = 0 then p.1 b c else p.2 b c := rfl

@[expose] def colSL (R : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  (R⁻¹).transpose

theorem colSL_apply (R : Matrix.SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    (colSL R : Matrix (Fin 2) (Fin 2) K) i j =
      ((R⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) j i := rfl

theorem act_pairT (P R : Matrix.SpecialLinearGroup (Fin 2) K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    tensor3Act1 (P : Matrix (Fin 2) (Fin 2) K) (tensor3Act2 (colSL R : Matrix (Fin 2) (Fin 2) K)
      (pairT (X, Y))) =
      pairT ((P : Matrix (Fin 2) (Fin 2) K) * X * ((R⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K),
        (P : Matrix (Fin 2) (Fin 2) K) * Y * ((R⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) := by
  funext a b c
  fin_cases a <;>
    simp [tensor3Act1, tensor3Act2, pairT_apply, colSL_apply, Fin.sum_univ_two,
      Matrix.mul_apply] <;>
    ring

@[expose] noncomputable def frame (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (Sp : D.Split) :
    S.E ≃ₗ[K] Tensor3 K :=
  (Sp.Θ.symm.trans (LinearEquiv.prodCongr (cM c) (cM c))).trans pairT

theorem frame_Θ (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (Sp : D.Split) (v w : ↥V) :
    frame c Sp (Sp.Θ (v, w)) = pairT (cM c v, cM c w) := by
  simp [frame]

theorem conj_frame (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (Sp : D.Split) (g : ↥𝔛)
    {z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K}
    (h : Rel D c g z) :
    conjE (frame c Sp) (g : S.E ≃ₗ[K] S.E) = act1E z.1 * act2E (colSL z.2) := by
  apply LinearEquiv.ext
  intro T
  obtain ⟨e, rfl⟩ := (frame c Sp).surjective T
  rw [conjE_apply, LinearEquiv.symm_apply_apply]
  obtain ⟨⟨v, w⟩, rfl⟩ := Sp.Θ.surjective e
  rw [Sp.act_Θ, frame_Θ, frame_Θ, h v, h w, LinearEquiv.mul_apply, act2E_apply, act1E_apply,
    act_pairT]

theorem conj_frame_unip (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (Sp : D.Split) (r : K) :
    conjE (frame c Sp) (D.unip r) = act0E (unipSL r) := by
  apply LinearEquiv.ext
  intro T
  obtain ⟨e, rfl⟩ := (frame c Sp).surjective T
  rw [conjE_apply, LinearEquiv.symm_apply_apply]
  obtain ⟨⟨v, w⟩, rfl⟩ := Sp.Θ.surjective e
  have h1 : D.unip r (Sp.Θ (v, w)) = Sp.Θ (v + r • w, w) := by
    rw [D.unip_apply, Sp.β_Θ]
    have : (w : S.E) = Sp.Θ (w, 0) := by
      rw [Sp.Θ_apply]; simp
    rw [this, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [h1, frame_Θ, frame_Θ, act0E_apply]
  funext a b c'
  fin_cases a <;>
    simp [tensor3Act0, pairT_apply, unipSL_apply, Fin.sum_univ_two, map_add, map_smul]

section TauForm

variable (Sp : D.Split)

@[expose] noncomputable def bTau : ↥V →ₗ[K] ↥V →ₗ[K] K := S.B.compl₁₂ Sp.τ Sp.τ

theorem bTau_apply (w w' : ↥V) : bTau Sp w w' = S.B (Sp.τ w) (Sp.τ w') := rfl

theorem bTau_act (g : ↥𝔛) (w w' : ↥V) : bTau Sp (D.act g w) (D.act g w') = bTau Sp w w' := by
  rw [bTau_apply, bTau_apply, Sp.τ_act, Sp.τ_act]
  exact S.B_isometry (D.O_le g.2) _ _

theorem exists_kappa : ∃ κ : K, ∀ w w' : ↥V, S.B (Sp.τ w) (Sp.τ w') = κ * D.pf w w' := by
  let a : ↥V →ₗ[K] ↥V := D.pfEquiv.symm.toLinearMap ∘ₗ bTau Sp
  have ha : ∀ w w', D.pf (a w) w' = bTau Sp w w' := by
    intro w w'
    have h : D.pfEquiv (a w) = bTau Sp w := D.pfEquiv.apply_symm_apply (bTau Sp w)
    exact LinearMap.congr_fun h w'
  have hcomm : ∀ (g : ↥𝔛) (v : ↥V), a (D.act g v) = D.act g (a v) := by
    intro g v
    rw [← sub_eq_zero]
    apply D.pf_nondeg
    intro w'
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, ha]
    have h1 : D.pf (D.act g (a v)) w' = D.pf (a v) (D.act g⁻¹ w') := by
      conv_lhs => rw [← D.act_act_inv g w']
      exact D.pf_inv g _ _
    rw [h1, ha]
    have h2 := bTau_act Sp g v (D.act g⁻¹ w')
    rw [D.act_act_inv g w'] at h2
    exact h2
  obtain ⟨κ, hκ⟩ := D.schur a hcomm
  refine ⟨κ, fun w w' => ?_⟩
  have := ha w w'
  rw [hκ w, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [← bTau_apply, ← this]

end TauForm

section StdForms

theorem plusPolar_eq_tensor3Form (x y : Fin 2 ⊕ Fin 2 → K) :
    plusPolar 2 K y x = tensor3Form (pairT (toMat K x, toMat K y)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [plusPolar_apply, Fin.sum_univ_two, tensor3Form, pairT_apply, toMat]
  simp
  linear_combination
    (x (.inr 1) * y (.inr 1) * 0 + (x (.inl 1) * y (.inr 1) + x (.inr 1) * y (.inl 1))) * h2

theorem det_toMat_eq (x : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K x = (toMat K x).det := (det_toMat K x).symm

theorem detW_pairT (X Y : Matrix (Fin 2) (Fin 2) K) : detW (pairT (X, Y)) = Y.det := by
  simp [detW, pairT_apply, Matrix.det_fin_two]

end StdForms

@[expose] def frLowSL (c : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

theorem frLowSL_apply (c : K) : (frLowSL c : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

section QForm

variable (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (hact : ActsAsNatural S V 𝔛 c (StatedQuadPlus 2 K))
  (hK : 4 ≤ Nat.card K) (Sp : D.Split)

include hact in
theorem invariant_f0 (g : ↥𝔛) (w : ↥V) :
    StatedQuadPlus 2 K (c (D.act g w)) = StatedQuadPlus 2 K (c w) := by
  obtain ⟨hX, h1, -, -⟩ := hact
  obtain ⟨A, hA, hAe⟩ := h1 g g.2
  have e1 : c (D.act g w) = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ c w := by
    have := hAe w w.2
    convert this using 2
    exact Subtype.ext (D.act_coe g w)
  rw [e1]
  exact KFLin.isometry_of_mem_statedOmega hA (c w)

include hact hK in
theorem nu_eq_kappa (hpf : ∀ v w, D.pf v w = plusPolar 2 K (c v) (c w)) {κ : K}
    (hκ : ∀ w w', S.B (Sp.τ w) (Sp.τ w') = κ * D.pf w w') (w : ↥V) :
    Sp.ν w = κ * StatedQuadPlus 2 K (c w) := by
  set ν₀ : ↥V → K := fun w => Sp.ν w - κ * StatedQuadPlus 2 K (c w) with hν₀
  have hadd : ∀ w w', ν₀ (w + w') = ν₀ w + ν₀ w' := by
    intro w w'
    simp only [ν₀]
    rw [Sp.ν_add, hκ, hpf]
    have hp := plusPolar_isPolar (m := 2) (K := K) (c w) (c w')
    have : StatedQuadPlus 2 K (c (w + w')) = StatedQuadPlus 2 K (c w) +
        StatedQuadPlus 2 K (c w') + plusPolar 2 K (c w) (c w') := by
      rw [map_add]; exact hp
    rw [this]; ring
  have hinv : ∀ (g : ↥𝔛) w, ν₀ (D.act g w) = ν₀ w := by
    intro g w
    simp only [ν₀]
    rw [invariant_f0 c hact g w]
    have : Sp.ν (D.act g w) = Sp.ν w := by
      simp only [LCData.Split.ν, Sp.τ_act]
      have hg0 := D.O_le g.2
      have hg' : ∀ e, S.Qf ((g : S.E ≃ₗ[K] S.E) e) = S.Qf e := hg0
      exact hg' _
    rw [this]
  let N : Matrix (Fin 2) (Fin 2) K → K := fun X => ν₀ ((cM c).symm X)
  have hNadd : ∀ X Y, N (X + Y) = N X + N Y := fun X Y => by
    simp only [N, map_add]; exact hadd _ _
  have hNinv : ∀ (P : Matrix.SpecialLinearGroup (Fin 2) K) X,
      N ((P : Matrix (Fin 2) (Fin 2) K) * X) = N X := by
    intro P X
    have hrel := liftHom_rel D c hact hK (P, 1)
    have e : D.act (liftHom D c hact hK (P, 1)) ((cM c).symm X) =
        (cM c).symm ((P : Matrix (Fin 2) (Fin 2) K) * X) := by
      apply (cM c).injective
      rw [hrel ((cM c).symm X)]
      simp
    simp only [N]
    rw [← e, hinv]
  have hup : ∀ a b : K, N !![a, b; 0, 0] = 0 := by
    intro a b
    have h := hNinv (unipSL 1) !![0, 0; a, b]
    have e : (unipSL (1 : K) : Matrix (Fin 2) (Fin 2) K) * !![0, 0; a, b] =
        !![0, 0; a, b] + !![a, b; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [unipSL_apply]
    rw [e, hNadd] at h
    exact add_eq_left.mp h |> fun h' => by simpa using h'
  have hlow : ∀ a b : K, N !![0, 0; a, b] = 0 := by
    intro a b
    have h := hNinv (frLowSL 1) !![a, b; 0, 0]
    have e : (frLowSL (1 : K) : Matrix (Fin 2) (Fin 2) K) * !![a, b; 0, 0] =
        !![a, b; 0, 0] + !![0, 0; a, b] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [frLowSL_apply]
    rw [e, hNadd] at h
    exact add_eq_left.mp h |> fun h' => by simpa using h'
  have hN0 : ∀ X, N X = 0 := by
    intro X
    have e : X = !![X 0 0, X 0 1; 0, 0] + !![0, 0; X 1 0, X 1 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e, hNadd, hup, hlow, add_zero]
  have := hN0 (cM c w)
  simp only [N, LinearEquiv.symm_apply_apply, ν₀] at this
  exact sub_eq_zero.mp this

include hact hK in
theorem Qf_frame (hpf : ∀ v w, D.pf v w = plusPolar 2 K (c v) (c w)) :
    ∃ κ : K, ∀ e, S.Qf e = Qk κ (frame c Sp e) := by
  obtain ⟨κ, hκ⟩ := exists_kappa Sp
  refine ⟨κ, fun e => ?_⟩
  obtain ⟨⟨v, w⟩, rfl⟩ := Sp.Θ.surjective e
  rw [Sp.Qf_Θ, frame_Θ, nu_eq_kappa c hact hK Sp hpf hκ w, hpf]
  have h1 := plusPolar_eq_tensor3Form (c v) (c w)
  have h2 := det_toMat_eq (c w)
  have h3 := detW_pairT (cM c v) (cM c w)
  have e1 : cM c v = toMat K (c v) := rfl
  have e2 : cM c w = toMat K (c w) := rfl
  rw [Qk, h3, e1, e2, h1, ← h2]
  ring

end QForm

section Images

variable (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (hact : ActsAsNatural S V 𝔛 c (StatedQuadPlus 2 K))
  (hK : 4 ≤ Nat.card K) (Sp : D.Split)

theorem colSL_one : colSL (1 : Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
  apply Subtype.ext
  simp [colSL, Matrix.SpecialLinearGroup.transpose]

theorem sl_transpose_inv (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (A.transpose)⁻¹ = (A⁻¹).transpose := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose]

theorem sl_transpose_transpose (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    A.transpose.transpose = A := Subtype.ext (by simp)

theorem colSL_colSL (R : Matrix.SpecialLinearGroup (Fin 2) K) : colSL (colSL R) = R := by
  unfold colSL
  rw [sl_transpose_inv, inv_inv, sl_transpose_transpose]

include hact hK in
theorem conj_leftG : (leftG D c hact hK).map (conjE (frame c Sp)).toMonoidHom = rowG := by
  ext T
  constructor
  · rintro ⟨x, ⟨P, rfl⟩, rfl⟩
    refine ⟨P, ?_⟩
    have h := conj_frame c Sp (liftHom D c hact hK (P, 1)) (liftHom_rel D c hact hK (P, 1))
    symm
    show conjE (frame c Sp) ((liftHom D c hact hK (P, 1) : ↥𝔛) : S.E ≃ₗ[K] S.E) = act1E P
    rw [h]
    simp [colSL_one]
  · rintro ⟨P, rfl⟩
    refine ⟨Phi D c hact hK (P, 1), ⟨P, rfl⟩, ?_⟩
    have h := conj_frame c Sp (liftHom D c hact hK (P, 1)) (liftHom_rel D c hact hK (P, 1))
    show conjE (frame c Sp) ((liftHom D c hact hK (P, 1) : ↥𝔛) : S.E ≃ₗ[K] S.E) = act1E P
    rw [h]
    simp [colSL_one]

include hact hK in
theorem conj_rightG : (rightG D c hact hK).map (conjE (frame c Sp)).toMonoidHom = colG := by
  ext T
  constructor
  · rintro ⟨x, ⟨R, rfl⟩, rfl⟩
    refine ⟨colSL R, ?_⟩
    have h := conj_frame c Sp (liftHom D c hact hK (1, R)) (liftHom_rel D c hact hK (1, R))
    symm
    show conjE (frame c Sp) ((liftHom D c hact hK (1, R) : ↥𝔛) : S.E ≃ₗ[K] S.E) = act2E (colSL R)
    rw [h]
    simp
  · rintro ⟨A, rfl⟩
    refine ⟨Phi D c hact hK (1, colSL A), ⟨colSL A, rfl⟩, ?_⟩
    have h := conj_frame c Sp (liftHom D c hact hK (1, colSL A))
      (liftHom_rel D c hact hK (1, colSL A))
    show conjE (frame c Sp) ((liftHom D c hact hK (1, colSL A) : ↥𝔛) : S.E ≃ₗ[K] S.E) = act2E A
    rw [h]
    simp [colSL_colSL]

end Images

end FrameMap

section MainFrame

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sl2_not_commutative : ¬ IsMulCommutative (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro h
  have h1 := h.is_comm.comm (unipSL (1 : K)) (frLowSL 1)
  have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  simp [unipSL_apply, frLowSL_apply, Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem map_conjFlip_colG : (colG (K := K)).map (conjFlip (K := K)).toMonoidHom = rowG := by
  ext T
  constructor
  · rintro ⟨x, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, (conjFlip_act2E A).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨act2E A, ⟨A, rfl⟩, conjFlip_act2E A⟩

theorem map_conjFlip_rowG : (rowG (K := K)).map (conjFlip (K := K)).toMonoidHom = colG := by
  ext T
  constructor
  · rintro ⟨x, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, (conjFlip_act1E A).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨act1E A, ⟨A, rfl⟩, conjFlip_act1E A⟩

section LR

variable {S : QSpace K} {V : Submodule K S.E} {𝔛 : Subgroup (S.E ≃ₗ[K] S.E)}
  (D : LCData S V 𝔛) (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))
  (hact : ActsAsNatural S V 𝔛 c (StatedQuadPlus 2 K)) (hK : 4 ≤ Nat.card K)

theorem leftG_le : leftG D c hact hK ≤ 𝔛 := by
  rintro _ ⟨P, rfl⟩
  exact (liftHom D c hact hK (P, 1)).2

theorem rightG_le : rightG D c hact hK ≤ 𝔛 := by
  rintro _ ⟨R, rfl⟩
  exact (liftHom D c hact hK (1, R)).2

theorem leftG_comm_rightG : ∀ x ∈ leftG D c hact hK, ∀ y ∈ rightG D c hact hK, x * y = y * x := by
  rintro _ ⟨P, rfl⟩ _ ⟨R, rfl⟩
  change Phi D c hact hK (P, 1) * Phi D c hact hK (1, R) =
    Phi D c hact hK (1, R) * Phi D c hact hK (P, 1)
  rw [← map_mul, ← map_mul]
  simp

theorem leftG_sup_rightG : leftG D c hact hK ⊔ rightG D c hact hK = 𝔛 := by
  apply le_antisymm
  · exact sup_le (leftG_le D c hact hK) (rightG_le D c hact hK)
  · intro g hg
    obtain ⟨⟨P, R⟩, rfl⟩ := (Phi_range D c hact hK).ge hg
    have e : ((P, R) : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) =
        (P, 1) * (1, R) := by simp
    rw [e, map_mul]
    exact Subgroup.mul_mem_sup ⟨P, rfl⟩ ⟨R, rfl⟩

theorem leftG_inf_rightG : leftG D c hact hK ⊓ rightG D c hact hK = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨⟨P, rfl⟩, ⟨R, hR⟩⟩
  have := Phi_injective D c hact hK (show Phi D c hact hK (1, R) = Phi D c hact hK (P, 1) from hR)
  have h1 : (1 : Matrix.SpecialLinearGroup (Fin 2) K) = P := (Prod.ext_iff.mp this).1
  have hP : P = 1 := h1.symm
  subst hP
  exact map_one (Phi D c hact hK)

theorem not_comm_of_injective {G H : Type*} [Group G] [Group H] (hG : ¬ IsMulCommutative G)
    (f : G →* H) (hf : Function.Injective f) : ¬ IsMulCommutative f.range := by
  intro h
  apply hG
  refine ⟨⟨fun a b => ?_⟩⟩
  have := h.is_comm.comm ⟨f a, a, rfl⟩ ⟨f b, b, rfl⟩
  apply hf
  simpa [map_mul] using congrArg Subtype.val this

theorem leftG_simple : IsSimpleGroup ↥(leftG D c hact hK) := by
  haveI := CFSG.CGT.PushingUpLit.A78.isSimpleGroup_SL2_charTwo K hK
  have hinj : Function.Injective ((Phi D c hact hK).comp
      (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K))) := fun a b h =>
    (Prod.ext_iff.mp (Phi_injective D c hact hK h)).1
  exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup

theorem rightG_simple : IsSimpleGroup ↥(rightG D c hact hK) := by
  haveI := CFSG.CGT.PushingUpLit.A78.isSimpleGroup_SL2_charTwo K hK
  have hinj : Function.Injective ((Phi D c hact hK).comp
      (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K))) := fun a b h =>
    (Prod.ext_iff.mp (Phi_injective D c hact hK h)).2
  exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup

theorem leftG_not_comm : ¬ IsMulCommutative ↥(leftG D c hact hK) := by
  have hinj : Function.Injective ((Phi D c hact hK).comp
      (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K))) := fun a b h =>
    (Prod.ext_iff.mp (Phi_injective D c hact hK h)).1
  exact not_comm_of_injective sl2_not_commutative _ hinj

theorem rightG_not_comm : ¬ IsMulCommutative ↥(rightG D c hact hK) := by
  have hinj : Function.Injective ((Phi D c hact hK).comp
      (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K))) := fun a b h =>
    (Prod.ext_iff.mp (Phi_injective D c hact hK h)).2
  exact not_comm_of_injective sl2_not_commutative _ hinj

theorem conjE_trans_flip {E : Type} [AddCommGroup E] [Module K E] (θ : E ≃ₗ[K] Tensor3 K)
    (g : E ≃ₗ[K] E) : conjE (θ.trans flipE) g = conjFlip (conjE θ g) := by
  rw [conjFlip_apply]
  apply LinearEquiv.ext
  intro T
  have hsymm : (flipE : T3E K).symm T = flipE T := by
    rw [LinearEquiv.symm_apply_eq]
    exact (LinearEquiv.congr_fun flipE_mul_self T).symm
  simp only [conjE_apply, LinearEquiv.mul_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, hsymm]

theorem conjE_trans_flip_hom {E : Type} [AddCommGroup E] [Module K E] (θ : E ≃ₗ[K] Tensor3 K) :
    (conjE (θ.trans flipE)).toMonoidHom = (conjFlip (K := K)).toMonoidHom.comp
      (conjE θ).toMonoidHom := by
  ext g : 1
  exact conjE_trans_flip θ g

end LR

theorem exists_frame (hKF10 : H1TensorStatement) (hK : 4 ≤ Nat.card K)
    {S : QSpace K} {V : Submodule K S.E} {𝔛 : Subgroup (S.E ≃ₗ[K] S.E)} (D : LCData S V 𝔛)
    (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (hact : ActsAsNatural S V 𝔛 c (StatedQuadPlus 2 K))
    (hpf : ∀ v w, D.pf v w = plusPolar 2 K (c v) (c w))
    (B C : Subgroup (S.E ≃ₗ[K] S.E)) (hBC : B ⊔ C = 𝔛)
    (hcomm : ∀ b ∈ B, ∀ x ∈ C, b * x = x * b) (hinf : B ⊓ C = ⊥)
    [IsSimpleGroup ↥B] [IsSimpleGroup ↥C] (hBn : ¬ IsMulCommutative ↥B)
    (hCn : ¬ IsMulCommutative ↥C) :
    ∃ (θ : S.E ≃ₗ[K] Tensor3 K) (κ : K), (∀ e, S.Qf e = Qk κ (θ e)) ∧
      B.map (conjE θ).toMonoidHom = rowG ∧ C.map (conjE θ).toMonoidHom = colG ∧
      ∀ r : K, conjE θ (D.unip r) = act0E (unipSL r) := by
  obtain ⟨Sp⟩ := exists_split (D := D) hKF10 hK c hact
  obtain ⟨κ, hκ⟩ := Qf_frame c hact hK Sp hpf
  haveI := leftG_simple D c hact hK
  haveI := rightG_simple D c hact hK
  have hfu := factor_unique (leftG_comm_rightG D c hact hK) hcomm (leftG_inf_rightG D c hact hK)
    hinf ((leftG_sup_rightG D c hact hK).trans hBC.symm) (leftG_not_comm D c hact hK)
    (rightG_not_comm D c hact hK) hBn hCn
  rcases hfu with ⟨hB, hC⟩ | ⟨hB, hC⟩
  · refine ⟨frame c Sp, κ, hκ, ?_, ?_, fun r => conj_frame_unip c Sp r⟩
    · rw [hB]; exact conj_leftG c hact hK Sp
    · rw [hC]; exact conj_rightG c hact hK Sp
  · refine ⟨(frame c Sp).trans flipE, κ, fun e => ?_, ?_, ?_, fun r => ?_⟩
    · rw [hκ e]
      have h := flipE_mem_Ok (K := K) κ
      exact (h _).symm
    · rw [hB, conjE_trans_flip_hom, ← Subgroup.map_map]
      rw [conj_rightG c hact hK Sp, map_conjFlip_colG]
    · rw [hC, conjE_trans_flip_hom, ← Subgroup.map_map]
      rw [conj_leftG c hact hK Sp, map_conjFlip_rowG]
    · rw [conjE_trans_flip, conj_frame_unip, conjFlip_act0E]

end MainFrame

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
