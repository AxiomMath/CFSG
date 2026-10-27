module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphDefs
public import CFSG.LocalAnalysis.StandardType.GGGraphNonePrimFamily
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix

private lemma pslBPF_formAdj_add {n : ℕ} {K : Type} [Field K]
    (G a b : Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) G (a + b) = formAdj (RingHom.id K) G a + formAdj (RingHom.id K) G b :=
  Geo.formAdj_add (RingHom.id K) G a b

private lemma pslBPF_formAdj_smul {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) (c : K) (a : Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) G (c • a) = c • formAdj (RingHom.id K) G a :=
  Geo.formAdj_smul (RingHom.id K) G c a

private lemma pslBPF_formAdj_mul {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (a b : Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) G (a * b) =
      formAdj (RingHom.id K) G b * formAdj (RingHom.id K) G a :=
  Geo.formAdj_mul (RingHom.id K) hG a b

private lemma pslBPF_formAdj_one {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) :
    formAdj (RingHom.id K) G (1 : Matrix (Fin n) (Fin n) K) = 1 :=
  Geo.formAdj_one (RingHom.id K) hG

private lemma pslBPF_formAdj_formAdj {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (hsymm : Gᵀ = G)
    (a : Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a) = a := by
  have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by
    simpa using hsymm
  exact Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG hGh a

private lemma pslBPF_formAdj_mem_adjoin {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) {S : Set (GL (Fin n) K)}
    (hS : ∀ s ∈ S, formAdj (RingHom.id K) G (s : Matrix (Fin n) (Fin n) K) ∈
      Algebra.adjoin K (Units.val '' S))
    {a : Matrix (Fin n) (Fin n) K}
    (ha : a ∈ Algebra.adjoin K (Units.val '' S)) :
    formAdj (RingHom.id K) G a ∈ Algebra.adjoin K (Units.val '' S) := by
  refine Algebra.adjoin_induction
    (p := fun x _ => formAdj (RingHom.id K) G x ∈ Algebra.adjoin K (Units.val '' S))
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    exact hS s hs
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, pslBPF_formAdj_smul, pslBPF_formAdj_one hG,
      ← Algebra.algebraMap_eq_smul_one]
    exact Subalgebra.algebraMap_mem _ r
  · intro x y _ _ hx hy
    rw [pslBPF_formAdj_add]
    exact Subalgebra.add_mem _ hx hy
  · intro x y _ _ hx hy
    rw [pslBPF_formAdj_mul hG]
    exact Subalgebra.mul_mem _ hy hx

private lemma pslBPF_star_B_mem {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K}
    (h : ∃ c : Kˣ, formAdj (RingHom.id K) G (B : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = (c : K) • (1 : Matrix (Fin n) (Fin n) K)) :
    formAdj (RingHom.id K) G (B : Matrix (Fin n) (Fin n) K) ∈ pslAlg B := by
  obtain ⟨c, hc⟩ := h
  have hleft : formAdj (RingHom.id K) G (B : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      formAdj (RingHom.id K) G (B : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hright : ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) • ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  have hstar : formAdj (RingHom.id K) G (B : Matrix (Fin n) (Fin n) K) =
      (c : K) • ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← hleft, hc, hright]
  rw [hstar]
  have hB : (B : Matrix (Fin n) (Fin n) K) ∈ pslAlg B :=
    Algebra.subset_adjoin ⟨B, Set.mem_singleton B, rfl⟩
  have hBinv : ((B : Matrix (Fin n) (Fin n) K))⁻¹ * (B : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let T : pslAlg B →ₗ[K] pslAlg B :=
    { toFun := fun s => ⟨(B : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K),
        Subalgebra.mul_mem _ hB s.2⟩
      map_add' := by
        intro s t
        ext
        simp [Matrix.mul_add]
      map_smul' := by
        intro d s
        ext
        simp [Matrix.mul_smul] }
  have hT_inj : Function.Injective T := by
    intro s t hst
    have hval : (B : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * (t : Matrix (Fin n) (Fin n) K) :=
      congrArg Subtype.val hst
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
      ((B : Matrix (Fin n) (Fin n) K))⁻¹ * M) hval
    apply Subtype.ext
    rw [show (s : Matrix (Fin n) (Fin n) K) =
          ((B : Matrix (Fin n) (Fin n) K))⁻¹ *
            ((B : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K)) from by
        rw [← Matrix.mul_assoc, hBinv, Matrix.one_mul],
      show (t : Matrix (Fin n) (Fin n) K) =
          ((B : Matrix (Fin n) (Fin n) K))⁻¹ *
            ((B : Matrix (Fin n) (Fin n) K) * (t : Matrix (Fin n) (Fin n) K)) from by
        rw [← Matrix.mul_assoc, hBinv, Matrix.one_mul]]
    exact h2
  have hT_surj : Function.Surjective T := LinearMap.surjective_of_injective hT_inj
  obtain ⟨s, hs⟩ := hT_surj 1
  have hsval : (B : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) = 1 :=
    congrArg Subtype.val hs
  have hs_eq : (s : Matrix (Fin n) (Fin n) K) = ((B : Matrix (Fin n) (Fin n) K))⁻¹ := by
    calc (s : Matrix (Fin n) (Fin n) K)
        = ((B : Matrix (Fin n) (Fin n) K))⁻¹ *
            ((B : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K)) := by
          rw [← Matrix.mul_assoc, hBinv, Matrix.one_mul]
      _ = ((B : Matrix (Fin n) (Fin n) K))⁻¹ * 1 := by rw [hsval]
      _ = ((B : Matrix (Fin n) (Fin n) K))⁻¹ := mul_one _
  have hmem : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ pslAlg B := by
    rw [Matrix.GeneralLinearGroup.coe_inv, ← hs_eq]
    exact s.2
  exact Subalgebra.smul_mem _ hmem (c : K)

private lemma pslBPF_pslAlg_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ pslAlg B, ∀ b ∈ pslAlg B, a * b = b * a := by
  have hcommS : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  letI : CommSemiring (pslAlg B) := Algebra.adjoinCommSemiringOfComm K hcommS
  intro a ha b hb
  have h := mul_comm (⟨a, ha⟩ : pslAlg B) (⟨b, hb⟩ : pslAlg B)
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

theorem pslGraph_star_mem {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    ∀ a ∈ pslAlg B, formAdj (RingHom.id K) G a ∈ pslAlg B := by
  intro a ha
  refine pslBPF_formAdj_mem_adjoin S.det_isUnit ?_ ha
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  subst s
  exact pslBPF_star_B_mem S.star_mul

theorem pslGraph_primFamily {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    ∃ P : Finset (Matrix (Fin n) (Fin n) K), PrimFamily (pslAlg B) P ∧
      ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P := by
  obtain ⟨P, hP⟩ := exists_primFamily_adjoin B
  refine ⟨P, hP, ?_⟩
  intro e he
  exact primFamily_map_mem hP (formAdj (RingHom.id K) G)
    (fun a b => pslBPF_formAdj_add G a b)
    (fun a b => pslBPF_formAdj_mul S.det_isUnit a b)
    (fun a ha => pslGraph_star_mem S a ha)
    (fun a _ => pslBPF_formAdj_formAdj S.det_isUnit S.symm a)
    (pslBPF_pslAlg_comm B) e he

end CFSG.StandardType
