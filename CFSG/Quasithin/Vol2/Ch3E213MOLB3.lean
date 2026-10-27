module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB1
public import CFSG.ClassicalInvolution.Q3.Q3WASAut
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Vol2.Ch3E213MOLFacts
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups Matrix

theorem false_of_twist₂ {F : Type} [Field F] {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) (h2 : (2 : F) ≠ 0) {v : MulAut E}
    {α : SL(3, F) →* SL(3, F)} {G : GL (Fin 3) F} (hα : ∀ x, θ (α x) = v (θ x))
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ *
        ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F)) (hv2 : v * v = 1)
    {A₁ A₂ : SL(2, F)} (hA₁ : (A₁ : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1])
    (hA₂ : (A₂ : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1])
    (hfix₁ : v (θ (WeakCT.blockSL F 3 2 0 (by omega) A₁)) =
      θ (WeakCT.blockSL F 3 2 0 (by omega) A₁))
    (hfix₂ : v (θ (WeakCT.blockSL F 3 2 0 (by omega) A₂)) =
      θ (WeakCT.blockSL F 3 2 0 (by omega) A₂)) :
    False := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have hσσ : ∀ x, v (v x) = x := fun x => by rw [← MulAut.mul_apply, hv2, MulAut.one_apply]
  have hαα := ModelFacts.UnitaryAut.lift_comp_self_eq_id hker hσσ hα
  set Gm := (G : Matrix (Fin 3) (Fin 3) F) with hGm
  set Gi := ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGidef
  have hGi : Gi * Gm = 1 := Units.inv_mul G
  have hGi' : Gm * Gi = 1 := Units.mul_inv G
  have hdet0 : Gm.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hGi'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hcomm : ∀ x : SL(3, F), (Gm * Giᵀ) * (x : Matrix (Fin 3) (Fin 3) F) =
      (x : Matrix (Fin 3) (Fin 3) F) * (Gm * Giᵀ) := by
    intro x
    have h1 := congrArg (fun y : SL(3, F) => (y : Matrix (Fin 3) (Fin 3) F))
      (DFunLike.congr_fun hαα x)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h1
    rw [hform] at h1
    have h2' : (((α x)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ =
        Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) * Gmᵀ := by
      rw [← map_inv, hform, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [h2'] at h1
    have hP : Gmᵀ * Gi * (Gm * Giᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Gi Gm, hGi, Matrix.one_mul,
        ← Matrix.transpose_mul, hGi, Matrix.transpose_one]
    calc Gm * Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) =
        Gm * Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) * (Gmᵀ * Gi * (Gm * Giᵀ)) := by
          rw [hP, Matrix.mul_one]
      _ = (Gm * (Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) * Gmᵀ) * Gi) * (Gm * Giᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 3) (Fin 3) F) * (Gm * Giᵀ) := by rw [h1]
  obtain ⟨s, hs⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := Gm * Giᵀ)
    fun t => (hcomm t.toSpecialLinearGroup).symm
  have hGs : Gm = s • Gmᵀ := by
    have h1 : Gm * Giᵀ * Gmᵀ = Gm := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hGi', Matrix.transpose_one, Matrix.mul_one]
    rw [← hs, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] at h1
    exact h1.symm
  obtain ⟨hG02, hG12, hG20, hG21⟩ := hG
  have hdetB : Gm.det = (Gm 0 0 * Gm 1 1 - Gm 0 1 * Gm 1 0) * Gm 2 2 := by
    rw [Matrix.det_fin_three, hG02, hG12, hG20, hG21]
    ring
  have hG22 : Gm 2 2 ≠ 0 := fun h => hdet0 (by rw [hdetB, h, mul_zero])
  have hs1 : s = 1 := by
    have h1 := congrFun (congrFun hGs 2) 2
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h1
    have h2'' : 1 * Gm 2 2 = s * Gm 2 2 := by rw [one_mul]; exact h1
    exact (mul_right_cancel₀ hG22 h2'').symm
  have hsymm : Gm 0 1 = Gm 1 0 := by
    have h1 := congrFun (congrFun hGs 0) 1
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hs1, one_mul] at h1
    exact h1
  have heq : ∀ A : SL(2, F), v (θ (WeakCT.blockSL F 3 2 0 (by omega) A)) =
      θ (WeakCT.blockSL F 3 2 0 (by omega) A) → ∃ r : F,
      Gm * (((WeakCT.blockSL F 3 2 0 (by omega) A)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ =
        r • ((WeakCT.blockSL F 3 2 0 (by omega) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Gm := by
    intro A hA
    set x := WeakCT.blockSL F 3 2 0 (by omega) A with hx
    have h1 : α x * x⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hA, mul_inv_cancel]
    obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp (hker h1)
    refine ⟨r, ?_⟩
    have h2'' : α x = (α x * x⁻¹) * x := by group
    have h3 : ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        r • ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
      rw [h2'', Matrix.SpecialLinearGroup.coe_mul, ← hr, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    rw [hform] at h3
    calc Gm * ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ =
        Gm * ((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ * Gi * Gm := by
          rw [Matrix.mul_assoc _ Gi Gm, hGi, Matrix.mul_one]
      _ = r • ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Gm := by rw [h3]
  have htw : ∀ A : SL(2, F),
      (((WeakCT.blockSL F 3 2 0 (by omega) A)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ =
      !![(A : Matrix (Fin 2) (Fin 2) F) 1 1, -(A : Matrix (Fin 2) (Fin 2) F) 1 0, 0;
        -(A : Matrix (Fin 2) (Fin 2) F) 0 1, (A : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0, 1] := by
    intro A
    simp only [← map_inv, WeakCT.coe_blockSL_three_zero, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨r₁, h₁⟩ := heq A₁ hfix₁
  obtain ⟨r₂, h₂⟩ := heq A₂ hfix₂
  rw [htw, WeakCT.coe_blockSL_three_zero, hA₁] at h₁
  rw [htw, WeakCT.coe_blockSL_three_zero, hA₂] at h₂
  have e122 := congrFun (congrFun h₁ 2) 2
  have e100 := congrFun (congrFun h₁ 0) 0
  have e101 := congrFun (congrFun h₁ 0) 1
  have e201 := congrFun (congrFun h₂ 0) 1
  have e222 := congrFun (congrFun h₂ 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, hG02, hG12, hG20, hG21] at e122 e100 e101 e201 e222
  have hr₁ : r₁ = 1 := (mul_right_cancel₀ hG22 (by rw [one_mul]; exact e122)).symm
  have hr₂ : r₂ = 1 := (mul_right_cancel₀ hG22 (by rw [one_mul]; exact e222)).symm
  subst hr₁ hr₂
  simp only [one_mul] at e100 e101 e201
  have hc : Gm 1 0 = -Gm 0 1 := by linear_combination -e100
  have hd : Gm 1 1 = 0 := by linear_combination -e101
  have ha : Gm 0 0 = 0 := by linear_combination -e201
  have hb : Gm 0 1 = 0 := by
    have h3 : (2 : F) * Gm 0 1 = 0 := by linear_combination hsymm + hc
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h2
    · exact h
  apply hdet0
  rw [hdetB, ha, hd, hb]
  ring

variable {X : Type} [Group X] {K : Subgroup X} [K.Normal]

theorem coe_conjNormal (t : X) (k : K) : ((MulAut.conjNormal t k : K) : X) = t * k * t⁻¹ :=
  MulAut.conjNormal_apply t k

theorem mem_of_inner_lift (ι : SL(3, GaloisField 3 1) ≃* K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {t : X}
    {α : SL(3, GaloisField 3 1) →* SL(3, GaloisField 3 1)}
    (hα : ∀ x, ι (α x) = MulAut.conjNormal t (ι x)) {A B : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)}
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hform : ∀ x, ((α x : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) =
      A * (x : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) * B) : t ∈ K := by
  have hdA : A.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hAB
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hd2 := sq_eq_one_of_ne_zero hdA
  have hydet : (A.det • A).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin]
    calc A.det ^ 3 * A.det = (A.det * A.det) * (A.det * A.det) := by ring
      _ = 1 := by rw [hd2, one_mul]
  set y : SL(3, GaloisField 3 1) := ⟨A.det • A, hydet⟩ with hy
  have hαy : ∀ x, α x = y * x * y⁻¹ := by
    intro x
    refine eq_mul_inv_of_mul_eq (Subtype.ext ?_)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hform]
    change A * (x : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) * B * (A.det • A) =
      (A.det • A) * (x : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc _ B A, hBA, Matrix.mul_one]
  have hcen : ((ι y : K) : X)⁻¹ * t ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨x, hx⟩ := ι.surjective ⟨k, hk⟩
    have h1 := congrArg Subtype.val (hα x)
    rw [hαy, map_mul, map_mul, map_inv, coe_conjNormal, hx] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc k * (((ι y : K) : X)⁻¹ * t) = ((ι y : K) : X)⁻¹ * (((ι y : K) : X) * k *
        ((ι y : K) : X)⁻¹) * t := by group
      _ = ((ι y : K) : X)⁻¹ * (t * k * t⁻¹) * t := by rw [h1]
      _ = ((ι y : K) : X)⁻¹ * t * k := by group
  rw [hC, Subgroup.mem_bot] at hcen
  have h2 : t = ((ι y : K) : X) := by
    calc t = ((ι y : K) : X) * (((ι y : K) : X)⁻¹ * t) := by group
      _ = ((ι y : K) : X) := by rw [hcen, mul_one]
  rw [h2]
  exact (ι y).2

theorem exists_lift (ι : SL(3, GaloisField 3 1) ≃* K) (t : X) :
    ∃ (α : SL(3, GaloisField 3 1) →* SL(3, GaloisField 3 1)) (g : GL (Fin 3) (GaloisField 3 1))
      (ε : Bool), (∀ x, ι (α x) = MulAut.conjNormal t (ι x)) ∧
      ∀ x, ((α x : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) =
        (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
          (if ε then (((x⁻¹ : SL(3, GaloisField 3 1)) :
            Matrix (Fin 3) (Fin 3) (GaloisField 3 1)))ᵀ
            else (x : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) *
          ((g⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) := by
  have hcl := CFSG.ClassicalInvolution.Q3.Q3W.linearAutClassification3 (n := 3) (le_refl 3)
  obtain ⟨α, g, φ, ε, hα, hform⟩ := hcl K ι.toMonoidHom ι.surjective (by
      intro x hx
      have h1 : x = 1 := ι.injective (by rw [map_one]; exact hx)
      rw [h1]
      exact Subgroup.one_mem _) (MulAut.conjNormal t)
  refine ⟨α, g, ε, hα, fun x => ?_⟩
  rw [hform, ringEquiv_eq_refl φ, RingEquiv.mapMatrix_refl]
  rfl

theorem exists_twist_lift (ι : SL(3, GaloisField 3 1) ≃* K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {t : X} (ht : t ∉ K) :
    ∃ (α : SL(3, GaloisField 3 1) →* SL(3, GaloisField 3 1)) (g : GL (Fin 3) (GaloisField 3 1)),
      (∀ x, ι (α x) = MulAut.conjNormal t (ι x)) ∧
      ∀ x, ((α x : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) =
        (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
          (((x⁻¹ : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)))ᵀ *
          ((g⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) := by
  obtain ⟨α, g, ε, hα, hform⟩ := exists_lift ι t
  cases ε with
  | false =>
    exact absurd (mem_of_inner_lift ι hC hα (Units.mul_inv g) (Units.inv_mul g)
      fun x => by rw [hform]; rfl) ht
  | true => exact ⟨α, g, hα, fun x => by rw [hform]; rfl⟩

theorem mul_mem_of_not_mem (ι : SL(3, GaloisField 3 1) ≃* K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {t₁ t₂ : X} (h₁ : t₁ ∉ K) (h₂ : t₂ ∉ K) :
    t₁ * t₂ ∈ K := by
  obtain ⟨α₁, g₁, hα₁, hf₁⟩ := exists_twist_lift ι hC h₁
  obtain ⟨α₂, g₂, hα₂, hf₂⟩ := exists_twist_lift ι hC h₂
  have e₁ : (g₁ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
      ((g₁⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) = 1 :=
    Units.mul_inv g₁
  have e₁' : ((g₁⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
      (g₁ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) = 1 := Units.inv_mul g₁
  have e₂ : (g₂ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
      ((g₂⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) = 1 :=
    Units.mul_inv g₂
  have e₂' : ((g₂⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
      (g₂ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) = 1 := Units.inv_mul g₂
  refine mem_of_inner_lift ι hC (α := α₁.comp α₂)
    (A := (g₁ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
      ((g₂⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))ᵀ)
    (B := (g₂ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))ᵀ *
      ((g₁⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)))
    (fun x => ?_) ?_ ?_ (fun x => ?_)
  · rw [MonoidHom.comp_apply, hα₁, hα₂, ← MulAut.mul_apply, ← map_mul]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (g₂ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))ᵀ,
      ← Matrix.transpose_mul, e₂, Matrix.transpose_one, Matrix.one_mul, e₁]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (g₁ : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)),
      e₁', Matrix.one_mul, ← Matrix.transpose_mul, e₂', Matrix.transpose_one]
  · rw [MonoidHom.comp_apply, hf₁, ← map_inv, hf₂, inv_inv, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]

theorem false_of_fix (ι : SL(3, GaloisField 3 1) ≃* K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {t : X} (ht : t ∉ K) (ht2 : t * t = 1)
    (hz : t * (ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X) =
      (ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X) * t)
    {A₁ A₂ : SL(2, GaloisField 3 1)}
    (hA₁ : (A₁ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 1; 0, 1])
    (hA₂ : (A₂ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 0; 1, 1])
    (h₁ : t * (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A₁) : X) =
      (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A₁) : X) * t)
    (h₂ : t * (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A₂) : X) =
      (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A₂) : X) * t) : False := by
  obtain ⟨α, g, hα, hform⟩ := exists_twist_lift ι hC ht
  have hfixK : ∀ y : SL(3, GaloisField 3 1), t * (ι y : X) = (ι y : X) * t →
      MulAut.conjNormal t (ι y) = ι y := by
    intro y hy
    apply Subtype.ext
    rw [coe_conjNormal]
    calc t * (ι y : X) * t⁻¹ = (ι y : X) * t * t⁻¹ := by rw [hy]
      _ = (ι y : X) := by group
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  have hz2 : z₀ * z₀ = 1 := by
    have h1 := pow_orderOf_eq_one z₀
    rw [hcl.orderOf_eq_two, pow_two] at h1
    exact h1
  have hαz : α z₀ = z₀ := ι.injective (by rw [hα, hfixK _ hz])
  have hG : IsBlockDiag (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) := by
    refine isBlockDiag_of_commute_negBlock two_ne_zero_gf3 _ ?_
    have h1 := hform z₀
    rw [hαz, inv_eq_of_mul_eq_one_right hz2, coe_rootInv_three] at h1
    have hT : (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))ᵀ =
        !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hT] at h1
    calc (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
        (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
          (((g⁻¹ : GL (Fin 3) (GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) *
            (g : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) := by
          rw [Units.inv_mul, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← h1]
  have hker : (ι : SL(3, GaloisField 3 1) ≃* K).toMonoidHom.ker ≤
      Subgroup.center SL(3, GaloisField 3 1) := by
    intro x hx
    have h1 : x = 1 := ι.injective (by rw [map_one]; exact hx)
    rw [h1]
    exact Subgroup.one_mem _
  have hv2 : MulAut.conjNormal t * MulAut.conjNormal t = (1 : MulAut K) := by
    rw [← map_mul, ht2, map_one]
  exact false_of_twist₂ ι.toMonoidHom hker two_ne_zero_gf3 hα hform hG hv2 hA₁ hA₂
    (hfixK _ h₁) (hfixK _ h₂)

end CFSG.Quasithin.Ch3E213M.OLB
