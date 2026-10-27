module

public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank SpecialLinear Matrix

namespace CompatA

variable {m : ℕ} {F : Type} [Field F]

theorem apply_eq_zero_of_mem_ggTorus {h : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hh : h ∈ ggTorus (SpecialLinear.rootDatum m F)) {a i j : Fin (m + 1)} (hij : i ≠ j)
    (hai : a ≠ i) : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a i = 0 := by
  have hN : h ∈ Subgroup.normalizer (SpecialLinear.rootSubgroup m F hij :
      Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    have h1 : h ∈ Subgroup.normalizer (SpecialLinear.rootGroup m F (InnerDiagA.typeARoot i j) :
        Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :=
      hh _ (InnerDiagA.typeARoot_mem_roots F hij)
    rwa [InnerDiagA.rootGroup_typeARoot] at h1
  obtain ⟨χ, hχ⟩ := InnerDiagA.exists_conj_transvection_eq hij hN
  have h2 : h * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij (χ * 1) * h := by
    rw [← hχ 1, inv_mul_cancel_right]
  have h3 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a j) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
    Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hai, mul_one,
    add_zero, add_eq_left] at h3
  exact h3

theorem isDiag_of_mem_ggTorus (hm : 1 ≤ m) {h : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hh : h ∈ ggTorus (SpecialLinear.rootDatum m F)) :
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
  intro a b hab
  have : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hj⟩ := exists_ne b
  exact apply_eq_zero_of_mem_ggTorus hh hj.symm hab

theorem diag_ne_zero {h : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hd : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) (i : Fin (m + 1)) :
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i ≠ 0 := by
  have h1 : (Matrix.diagonal (Matrix.diag (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F))).det = 1 := by
    rw [hd.diagonal_diag]
    exact h.2
  rw [Matrix.det_diagonal] at h1
  have h2 : ∏ l, Matrix.diag (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) l ≠ 0 := by
    rw [h1]
    exact one_ne_zero
  exact Finset.prod_ne_zero_iff.mp h2 i (Finset.mem_univ i)

end CompatA

section Block

variable {n : ℕ} {F : Type} [Field F]

theorem slBlockMat_diagonal (d : Fin (n + 1) → F) :
    slBlockMat n F (Matrix.diagonal d) = Matrix.diagonal (Fin.snoc (α := fun _ => F) d 1) := by
  ext a b
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective b
  rw [slBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q
  · simp [Matrix.diagonal_apply, castAdd_one_eq]
  · obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [castAdd_one_eq, natAdd_zero_eq_last, Fin.castSucc_ne_last]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    simp [castAdd_one_eq, natAdd_zero_eq_last, (Fin.castSucc_ne_last _).symm]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [natAdd_zero_eq_last]

theorem slBlockHom_mem_ggTorus (hn : 1 ≤ n) {h : Matrix.SpecialLinearGroup (Fin (n + 1)) F}
    (hh : h ∈ ggTorus (SpecialLinear.rootDatum n F)) :
    slBlockHom n F h ∈ ggTorus (SpecialLinear.rootDatum (n + 1) F) := by
  have hd := CompatA.isDiag_of_mem_ggTorus hn hh
  refine HypSixTypeA.mem_ggTorus_of_diagonal
    (e := Fin.snoc (α := fun _ => F) (Matrix.diag (h : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) 1)
    (fun l => ?_) ?_
  · refine Fin.lastCases ?_ (fun i => ?_) l
    · simp
    · simp only [Fin.snoc_castSucc]
      exact CompatA.diag_ne_zero hd i
  · change slBlockMat n F (h : Matrix (Fin (n + 1)) (Fin (n + 1)) F) = _
    conv_lhs => rw [← hd.diagonal_diag]
    exact slBlockMat_diagonal _

theorem slBlockHom_rootGroup {i j : Fin (n + 1)} (hij : i ≠ j) :
    ∀ z ∈ (SpecialLinear.rootDatum (n + 1) F).rootGroup
        (InnerDiagA.typeARoot (m := n + 1) i.castSucc j.castSucc),
      ∃ z' ∈ (SpecialLinear.rootDatum n F).rootGroup (InnerDiagA.typeARoot (m := n) i j),
        slBlockHom n F z' = z := by
  intro z hz
  have hij' : i.castSucc ≠ j.castSucc := (Fin.castSucc_injective _).ne hij
  change z ∈ SpecialLinear.rootGroup (n + 1) F _ at hz
  rw [InnerDiagA.rootGroup_typeARoot hij'] at hz
  obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij' z).mp hz
  refine ⟨Matrix.SpecialLinearGroup.transvection hij c, ?_, slBlockHom_transvection hij c⟩
  change _ ∈ SpecialLinear.rootGroup n F _
  rw [InnerDiagA.rootGroup_typeARoot hij]
  exact SpecialLinear.transvection_mem_rootSubgroup hij c

end Block

section Compat

theorem ggCompatPresented_slBlock {G : Type*} [Group G] {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1 + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1 + 1)) (GaloisField 2 f))) :
    GGCompatPresented (SpecialLinear.rootDatum (n + 1) (GaloisField 2 f)) ψ
      (ψ.comp (slBlockHom n (GaloisField 2 f))).range := by
  have hij : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact ggCompatPresented_comp (t' := .PSL) (n' := n + 1) (f' := f) hker
    (statedLieAdmissible_PSL hn hf) (by change 2 ≤ n; omega)
    (ι := slBlockHom n (GaloisField 2 f)) slBlockHom_injective
    (InnerDiagA.typeARoot_mem_roots _ hij)
    (InnerDiagA.typeARoot_mem_roots _ ((Fin.castSucc_injective _).ne hij))
    (slBlockHom_rootGroup hij) (fun _ hh' => slBlockHom_mem_ggTorus (by omega) hh')

theorem ggCompatPresented_slBlock₂ {G : Type*} [Group G] {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1)) (GaloisField 2 f))) :
    GGCompatPresented (SpecialLinear.rootDatum (n + 1 + 1) (GaloisField 2 f)) ψ
      (ψ.comp (slBlockHom₂ n (GaloisField 2 f))).range := by
  have hij : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hij' : (⟨0, by omega⟩ : Fin (n + 1)).castSucc ≠ (⟨1, by omega⟩ : Fin (n + 1)).castSucc :=
    (Fin.castSucc_injective _).ne hij
  refine ggCompatPresented_comp (t' := .PSL) (n' := n + 1) (f' := f) hker
    (statedLieAdmissible_PSL hn hf) (by change 2 ≤ n; omega)
    (ι := slBlockHom₂ n (GaloisField 2 f)) slBlockHom₂_injective
    (InnerDiagA.typeARoot_mem_roots _ hij)
    (InnerDiagA.typeARoot_mem_roots _ ((Fin.castSucc_injective _).ne hij')) (fun z hz => ?_)
    (fun _ hh' => slBlockHom_mem_ggTorus (by omega) (slBlockHom_mem_ggTorus (by omega) hh'))
  obtain ⟨z₁, hz₁, rfl⟩ := slBlockHom_rootGroup hij' z hz
  obtain ⟨z₂, hz₂, rfl⟩ := slBlockHom_rootGroup hij z₁ hz₁
  exact ⟨z₂, hz₂, slBlockHom₂_apply z₂⟩

end Compat

section Presentation

variable {G : Type} [Group G] [Finite G]

theorem exists_presents_typeA_ext {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {m k f : ℕ} (hk : 4 ≤ k) (hkm : k ≤ m) (hf : 1 ≤ f)
    (φ : ggSub (rootDatum m (GaloisField 2 f))
      (ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)) →* G)
    (ρ : (coxeterMatrix (isFiniteType_A m)).Group →* G) (hρ : Function.Injective ρ)
    (hspecial : ∀ j ∈ typeALeviJ m k, ggExt φ (weylRep m (GaloisField 2 f) j) =
      ρ ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j))
    (hcent : ∀ (w : (coxeterMatrix (isFiniteType_A m)).Group),
      ∀ α ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
        weylAction (isFiniteType_A m) w α = α → ∀ z ∈ rootGroup m (GaloisField 2 f) α,
          ρ w * ggExt φ z * (ρ w)⁻¹ = ggExt φ z)
    (hnt : ∃ γ ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
      ∃ z ∈ rootGroup m (GaloisField 2 f) γ, ggExt φ z ≠ 1)
    (hφG : φ.range ≤ ggG0 p B x L D J) (hρG : ρ.range ≤ ggG0 p B x L D J)
    (hL : L ≤ ggClosure (rootDatum m (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)) (fun _ => φ)
        ρ.range)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ ggClosure (rootDatum m (GaloisField 2 f))
        (fun _ : Unit => ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)) (fun _ => φ)
          ρ.range) :
    ∃ ψ₀ : (ggU .PSL (m + 1) f).K →* G,
      GGPresentsG0 (ggG0 p B x L D J) (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ₀ ∧
        ∀ u : ggSub (rootDatum m (GaloisField 2 f))
          (ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)),
          ψ₀ (u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) = φ u := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ψ, hext, -, -, hrange, hker, hq, hmodel⟩ := ggPresentation_typeALevi hk hkm hF hf φ
    (R := ρ.range) (δ := (MonoidHom.ofInjective hρ).symm.toMonoidHom)
    (MonoidHom.ofInjective hρ).symm.surjective
    (fun j hj => ⟨MonoidHom.ofInjective hρ
      ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j),
      by rw [MonoidHom.ofInjective_apply hρ, hspecial j hj],
      (MonoidHom.ofInjective hρ).symm_apply_apply _⟩)
    (fun r => forall_range_ofInjective hρ (P := fun g w =>
      ∀ α ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
        weylAction (isFiniteType_A m) w α = α → ∀ z ∈ rootGroup m (GaloisField 2 f) α,
          g * ggExt φ z * g⁻¹ = ggExt φ z) hcent r)
    hnt
  have hcl := ggClosure_eq_ggG0 (fun _ : Unit => hφG) hρG hL hK
  rw [hcl] at hrange hq hmodel
  exact ⟨ψ, ⟨⟨statedLieAdmissible_PSL (by omega) hf, by change 2 ≤ m; omega⟩, ⟨hrange, hker⟩,
    Group.isPerfect_def.mp hq.1, hmodel⟩, hext⟩

end Presentation

end CFSG.StandardType
