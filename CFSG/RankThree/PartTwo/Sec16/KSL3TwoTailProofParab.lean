module

public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofPara
public import CFSG.LieType.SteinbergBRLinearSmallParabolic
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1623Parab

open CFSG
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open Matrix

@[expose] def ParabConcl {G : Type} [Group G] (b : G) (P : Subgroup G) (p m : ℕ) : Prop :=
  ∃ V X : Subgroup G,
    CFSG.Assembly.IsElemAbelian 2 V ∧ Nat.card V = 2 ^ (2 * m) ∧ X ≤ P ∧ Nat.card X = p ∧
    b ∈ inSubgroup perfectResidual (Subgroup.normalizer (V : Set G)) ∧
    X ≤ inSubgroup perfectResidual (Subgroup.normalizer (V : Set G)) ∧
    V ≤ inSubgroup perfectResidual (Subgroup.normalizer (V : Set G)) ∧
    ∃ _ : (V.subgroupOf (inSubgroup perfectResidual (Subgroup.normalizer (V : Set G)))).Normal,
      Nonempty (↥(inSubgroup perfectResidual (Subgroup.normalizer (V : Set G))) ⧸
        V.subgroupOf (inSubgroup perfectResidual (Subgroup.normalizer (V : Set G))) ≃*
        projSL 2 (GaloisField 2 m))

theorem isElemAbelian_map {G G' : Type*} [Group G] [Group G'] {r : ℕ} (f : G →* G')
    {V : Subgroup G} (hV : CFSG.Assembly.IsElemAbelian r V) :
    CFSG.Assembly.IsElemAbelian r (V.map f) := CFSG.SectionRank.isElemAbelian_map hV _

theorem parabConcl_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {b : G}
    {P : Subgroup G} {p m : ℕ} (h : ParabConcl (e b) (P.map e.toMonoidHom) p m) :
    ParabConcl b P p m := by
  obtain ⟨V', X', hV'el, hV'c, hX'P, hX'c, hbK, hXK, hVK, hn, ⟨q⟩⟩ := h
  set ι : G' →* G := e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := e.symm.injective
  have hN : Subgroup.normalizer ((V'.map ι : Subgroup G) : Set G) =
      (Subgroup.normalizer (V' : Set G')).map ι :=
    (Subgroup.map_equiv_normalizer_eq V' e.symm).symm
  have hK : inSubgroup perfectResidual (Subgroup.normalizer ((V'.map ι : Subgroup G) : Set G)) =
      (inSubgroup perfectResidual (Subgroup.normalizer (V' : Set G'))).map ι := by
    rw [hN, Proof1623Para.inSubgroup_perfectResidual_map hιinj]
  obtain ⟨hn', ⟨q'⟩⟩ := Proof1623Para.exists_quot_map hιinj hn q
  refine ⟨V'.map ι, X'.map ι, isElemAbelian_map ι hV'el, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hιinj, hV'c]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hX'P hy
    change e.symm (e z) ∈ P
    rw [MulEquiv.symm_apply_apply]
    exact hz
  · rw [Subgroup.card_map_of_injective hιinj, hX'c]
  · rw [hK]
    exact ⟨e b, hbK, by simp [hι]⟩
  · rw [hK]
    exact Subgroup.map_mono hXK
  · rw [hK]
    exact Subgroup.map_mono hVK
  · rw [hK]
    exact ⟨hn', ⟨q'⟩⟩

variable {F : Type} [Field F]

theorem mem_flagSpace_two {v : Fin 3 → F} : v ∈ flagSpace 3 F 2 ↔ v 2 = 0 := by
  rw [mem_flagSpace]
  constructor
  · intro h
    exact h 2 (by norm_num)
  · intro h j hj
    have : j = 2 := by
      ext
      have := j.2
      simp only [Fin.val_two]
      omega
    rw [this]
    exact h

theorem conj_mem_radU {n : ℕ} {W : Submodule F (Fin n → F)} {g u : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ stabilizer W) (hu : u ∈ radU F W) : g * u * g⁻¹ ∈ radU F W := by
  have hgW : ∀ w ∈ W, g.val *ᵥ w ∈ W := fun w hw => by
    have : W.map (mulVecLin g.val) = W := hg
    rw [← this]
    exact ⟨w, hw, rfl⟩
  have hgW' : ∀ w ∈ W, (g⁻¹).val *ᵥ w ∈ W := fun w hw => by
    have : W.map (mulVecLin (g⁻¹).val) = W := inv_mem hg
    rw [← this]
    exact ⟨w, hw, rfl⟩
  have hval : ∀ v, (g * u * g⁻¹).val *ᵥ v = g.val *ᵥ (u.val *ᵥ ((g⁻¹).val *ᵥ v)) := fun v => by
    rw [show (g * u * g⁻¹).val = g.val * u.val * (g⁻¹).val from rfl, ← mulVec_mulVec,
      ← mulVec_mulVec]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · have h1 := hgW _ (hu.1 ((g⁻¹).val *ᵥ v))
    rw [mulVec_sub, val_mulVec_inv_val_mulVec] at h1
    rw [hval]
    exact h1
  · rw [hval, hu.2 _ (hgW' w hw), val_mulVec_inv_val_mulVec]

@[expose] def uOneMat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 1; 0, 1, 0; 0, 0, 1]

@[expose] def uOne (F : Type) [Field F] : SpecialLinearGroup (Fin 3) F :=
  ⟨uOneMat F, by simp [uOneMat, Matrix.det_fin_three]⟩

theorem uOne_mem_radU : uOne F ∈ radU F (flagSpace 3 F 2) := by
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [mem_flagSpace_two]
    simp [uOne, uOneMat, dotProduct, Fin.sum_univ_three]
  · rw [mem_flagSpace_two] at hw
    ext i
    fin_cases i <;> simp [uOne, uOneMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hw]

theorem diag_eq_one_of_mem_radU {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ radU F (flagSpace 3 F 2)) (i : Fin 3) : u.val i i = 1 := by
  have he0 : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
    rw [mem_flagSpace_two]; simp
  have he1 : (Pi.single 1 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
    rw [mem_flagSpace_two]; simp
  fin_cases i
  · have h := congrFun (hu.2 _ he0) 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  · have h := congrFun (hu.2 _ he1) 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  · have h := (mem_flagSpace_two).mp (hu.1 (Pi.single 2 1))
    have h' : u.val 2 2 - 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
    exact sub_eq_zero.mp h'

theorem mem_stabilizer_of_normalizes [CharP F 2] {h : SpecialLinearGroup (Fin 3) F}
    (hN : proj 3 F h ∈ Subgroup.normalizer
      (((radU F (flagSpace 3 F 2)).map (proj 3 F) : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) :
    h ∈ stabilizer (flagSpace 3 F 2) := by
  set W := flagSpace 3 F 2 with hW
  have h1 : proj 3 F h * proj 3 F (uOne F) * (proj 3 F h)⁻¹ ∈ (radU F W).map (proj 3 F) :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp ⟨_, uOne_mem_radU, rfl⟩
  obtain ⟨u', hu', hu'e⟩ := h1
  rw [← map_inv, ← map_mul, ← map_mul, proj_eq_proj_iff] at hu'e
  obtain ⟨c, hc3, hcz⟩ := mem_scalars.mp hu'e
  set y := h * uOne F * h⁻¹ with hy
  have hyz : y.val = u'.val * scalar (Fin 3) (c : F) := by
    have : y = u' * (u'⁻¹ * y) := by group
    rw [this, show (u' * (u'⁻¹ * y)).val = u'.val * (u'⁻¹ * y).val from rfl, hcz]
  have htr1 : y.val.trace = 3 := by
    rw [show y.val = h.val * (uOne F).val * (h⁻¹).val from rfl, Matrix.trace_mul_cycle,
      inv_val_mul_val, Matrix.one_mul]
    simp [uOne, uOneMat, Matrix.trace_fin_three]
    norm_num
  have htr2 : y.val.trace = 3 * (c : F) := by
    rw [hyz, Matrix.scalar_apply, Matrix.trace_fin_three, Matrix.mul_diagonal,
      Matrix.mul_diagonal, Matrix.mul_diagonal, diag_eq_one_of_mem_radU hu' 0,
      diag_eq_one_of_mem_radU hu' 1, diag_eq_one_of_mem_radU hu' 2]
    ring
  have h3 : (3 : F) ≠ 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    intro h3
    have : (1 : F) = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  have hc1 : (c : F) = 1 := by
    have := htr1.symm.trans htr2
    have h' : (3 : F) * ((c : F) - 1) = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left h3)
  have hyU : y ∈ radU F W := by
    have : y = u' := by
      apply Subtype.ext
      rw [hyz, hc1, map_one, Matrix.mul_one]
    rw [this]
    exact hu'
  have hfix : ∀ w ∈ W, (h⁻¹).val *ᵥ w ∈ W := by
    intro w hw
    have h2 := hyU.2 w hw
    rw [show y.val = h.val * (uOne F).val * (h⁻¹).val from rfl, ← mulVec_mulVec,
      ← mulVec_mulVec] at h2
    have h3 : (uOne F).val *ᵥ ((h⁻¹).val *ᵥ w) = (h⁻¹).val *ᵥ w := by
      have := congrArg (fun v => (h⁻¹).val *ᵥ v) h2
      simpa only [inv_val_mulVec_val_mulVec] using this
    rw [hW, mem_flagSpace_two]
    generalize (h⁻¹).val *ᵥ w = v at h3
    have h4 := congrFun h3 0
    simp only [uOne, uOneMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h4
    simpa using h4
  have hinv : h⁻¹ ∈ stabilizer W := by
    rw [mem_stabilizer_iff_map_le]
    rintro _ ⟨w, hw, rfl⟩
    exact hfix w hw
  simpa using inv_mem hinv

theorem normalizer_radU [Finite F] [CharP F 2] :
    Subgroup.normalizer (((radU F (flagSpace 3 F 2)).map (proj 3 F) :
      Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) =
      (stabilizer (flagSpace 3 F 2)).map (proj 3 F) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h, rfl⟩ := proj_surjective 3 F x
    exact ⟨h, mem_stabilizer_of_normalizes hx, rfl⟩
  · rintro _ ⟨h, hh, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨u, hu, rfl⟩ := hy
    refine ⟨h * u * h⁻¹, conj_mem_radU hh hu, ?_⟩
    rw [map_mul, map_mul, map_inv]

theorem radU_commute {n : ℕ} {W : Submodule F (Fin n → F)} {u u' : SpecialLinearGroup (Fin n) F}
    (hu : u ∈ radU F W) (hu' : u' ∈ radU F W) : u * u' = u' * u := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply,
    show (u * u').val = u.val * u'.val from rfl, show (u' * u).val = u'.val * u.val from rfl,
    ← mulVec_mulVec, ← mulVec_mulVec]
  have e1 : u'.val *ᵥ v = v + (u'.val *ᵥ v - v) := by abel
  have e2 : u.val *ᵥ v = v + (u.val *ᵥ v - v) := by abel
  rw [e1, mulVec_add, hu.2 _ (hu'.1 v), e2, mulVec_add, hu'.2 _ (hu.1 v)]
  abel

theorem radU_mul_self [CharP F 2] {n : ℕ} {W : Submodule F (Fin n → F)}
    {u : SpecialLinearGroup (Fin n) F} (hu : u ∈ radU F W) : u * u = 1 := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply,
    show (u * u).val = u.val * u.val from rfl, ← mulVec_mulVec,
    show (1 : SpecialLinearGroup (Fin n) F).val = 1 from rfl, one_mulVec]
  have e2 : u.val *ᵥ v = v + (u.val *ᵥ v - v) := by abel
  rw [e2, mulVec_add, hu.2 _ (hu.1 v)]
  have : (u.val *ᵥ v - v) + (u.val *ᵥ v - v) = 0 := by
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  calc u.val *ᵥ v + (u.val *ᵥ v - v) = v + ((u.val *ᵥ v - v) + (u.val *ᵥ v - v)) := by abel
    _ = v := by rw [this, add_zero]

theorem isElemAbelian_radU [CharP F 2] {n : ℕ} (W : Submodule F (Fin n → F)) :
    CFSG.Assembly.IsElemAbelian 2 ((radU F W).map (proj n F)) := by
  refine isElemAbelian_map (proj n F) ⟨⟨⟨fun a b => Subtype.ext (radU_commute a.2 b.2)⟩⟩,
    fun u hu => ?_⟩
  rw [sq]
  exact radU_mul_self hu

@[expose] def levMat (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem det_levMat (A : Matrix (Fin 2) (Fin 2) F) : (levMat A).det = A.det := by
  simp [levMat, Matrix.det_fin_three, Matrix.det_fin_two]

theorem levMat_mul (A B : Matrix (Fin 2) (Fin 2) F) : levMat (A * B) = levMat A * levMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem levMat_one : levMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat]

@[expose] def lev (F : Type) [Field F] :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun A := ⟨levMat A.val, by rw [det_levMat, A.prop]⟩
  map_one' := Subtype.ext levMat_one
  map_mul' A B := Subtype.ext (levMat_mul _ _)

theorem lev_val (A : SpecialLinearGroup (Fin 2) F) : (lev F A).val = levMat A.val :=
  rfl

@[expose] def leviP (F : Type) [Field F] : Subgroup (projectiveSL 3 F) :=
  ((proj 3 F).comp (lev F)).range

theorem lev_mem_stabilizer (A : SpecialLinearGroup (Fin 2) F) :
    lev F A ∈ stabilizer (flagSpace 3 F 2) := by
  rw [mem_stabilizer_flagSpace_iff]
  intro i j hi hj
  have hi2 : i = 2 := by
    ext
    have := i.2
    simp only [Fin.val_two]
    omega
  subst hi2
  fin_cases j
  · rfl
  · rfl
  · exact absurd hj (by decide)

theorem leviP_le_stabilizer : leviP F ≤ (stabilizer (flagSpace 3 F 2)).map (proj 3 F) := by
  rintro _ ⟨A, rfl⟩
  exact ⟨lev F A, lev_mem_stabilizer A, rfl⟩

theorem isPerfect_leviP [Finite F] (hF4 : 4 ≤ Nat.card F) : Group.IsPerfect (leviP F) := by
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  exact Group.IsPerfect.ofSurjective (f := ((proj 3 F).comp (lev F)).rangeRestrict)
    ((proj 3 F).comp (lev F)).rangeRestrict_surjective

theorem parabConcl_of_le_levi {m : ℕ} (hm : 2 ≤ m)
    {b : projectiveSL 3 (GaloisField 2 m)} {P X : Subgroup (projectiveSL 3 (GaloisField 2 m))}
    {p : ℕ} (hb : b ∈ leviP (GaloisField 2 m)) (hXP : X ≤ P) (hXc : Nat.card X = p)
    (hXlev : X ≤ leviP (GaloisField 2 m)) : ParabConcl b P p m := by
  set F := GaloisField 2 m with hFdef
  have hFc : Nat.card F = 2 ^ m := GaloisField.card 2 m (by omega)
  have hFe : Even (Nat.card F) := by
    rw [hFc]
    exact (Nat.even_pow' (by omega)).mpr even_two
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  set W := flagSpace 3 F 2 with hW
  set PW := (stabilizer W).map (proj 3 F) with hPW
  set B := inSubgroup perfectResidual PW with hB
  obtain ⟨-, -, hle, -, hRad, ⟨hq⟩, -, hcard, -⟩ :=
    CFSG.LieType.linear_small_parabolic_perfect_residual_structure hFe (n := 3) (d := 2)
      (by norm_num) (by norm_num) (Or.inl ⟨rfl, hF4⟩) W (finrank_flagSpace (by norm_num))
      (P := PW) (B := B) rfl rfl
  set V := (radU F W).map (proj 3 F) with hV
  have hNV : Subgroup.normalizer (V : Set (projectiveSL 3 F)) = PW := normalizer_radU
  have hK : inSubgroup perfectResidual (Subgroup.normalizer (V : Set (projectiveSL 3 F))) = B := by
    rw [hNV]
  have hlevB : leviP F ≤ B :=
    CFSG.RankThree.PartOne.EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
      leviP_le_stabilizer (isPerfect_leviP hF4)
  refine ⟨V, X, isElemAbelian_radU W, ?_, hXP, hXc, ?_, ?_, ?_, ?_⟩
  · rw [hcard, hFc, ← pow_mul]
    congr 1
    omega
  · rw [hK]
    exact hlevB hb
  · rw [hK]
    exact hXlev.trans hlevB
  · rw [hK]
    exact hle
  · rw [hK]
    have hn : (V.subgroupOf B).Normal := by
      rw [← hRad]
      infer_instance
    refine ⟨hn, ⟨(QuotientGroup.quotientMulEquivOfEq hRad.symm).trans (hq.trans ?_)⟩⟩
    exact (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 2 F).symm

end ProofKS1623Parab

end CFSG.RankThree.PartTwo.Sec16
