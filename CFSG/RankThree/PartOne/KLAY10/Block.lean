module

public import CFSG.RankThree.PartOne.KF.SpQuad
public import CFSG.RankThree.PartOne.KF.R8Levi

public section

namespace CFSG.RankThree.PartOne.KLAY10

open CFSG.GroupTheory.WeirSylow Module
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ

section Space2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def formQ2 (K : Type) [Field K] [Finite K] [CharP K 2] :
    QV K (Fin 2) → QV K (Fin 2) → K :=
  fun x y => ∑ i, qForm (x i) (y i)

@[expose] noncomputable def M2 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  formIsometryGroup K (formQ2 K)

theorem mem_M2_iff (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :
    g ∈ M2 K ↔ ∀ x y, ∑ i, qForm (g x i) (g y i) = ∑ i, qForm (x i) (y i) :=
  Iff.rfl

noncomputable abbrev sp2Space (K : Type) [Field K] [Finite K] [CharP K 2] : FormSpace K K :=
  FormSpace.pi (fun _ : Fin 2 => (⟨Qext K, fun x y => qForm x y⟩ : FormSpace K K))

theorem isSymplecticSpace_sp2 : IsSymplecticSpace (sp2Space K) :=
  isSymplecticSpace_pi _ (fun _ => ⟨qForm, fun _ _ => rfl, qForm_isAlt, qForm_nondegenerate⟩)

theorem finrank_sp2 : finrank K (sp2Space K).V = 2 * 2 := by
  rw [FormSpace.finrank_pi]
  simp [finrank_qext]

theorem nonempty_m2Equiv : Nonempty (↥(M2 K) ≃* ↥(StatedSp 2 K)) := by
  obtain ⟨B, hBF, hBa, hBn⟩ := isSymplecticSpace_sp2 (K := K)
  obtain ⟨ι⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_form_isometry B
    (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K 2) hBa hBn
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [finrank_sp2, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard])
  let e₁ : (sp2Space K).isom ≃* (stdSympSpace K 2).isom :=
    formIsometryGroupCongr ι.toLinearEquiv fun x y => by
      rw [hBF]
      exact ι.map_app y x
  let M := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun K (Fin 2 ⊕ Fin 2))
  have hmem : ∀ g : (stdSympSpace K 2).isom, M g.1 ∈ StatedSp 2 K := fun g => by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp]
    exact Subgroup.mem_map_of_mem _ (TauCeti.BilinForm.mem_isometryGroup_iff.2 g.2)
  let ψ₀ : (stdSympSpace K 2).isom →* StatedSp 2 K :=
    { toFun := fun g => ⟨M g.1, hmem g⟩
      map_one' := Subtype.ext (map_one M)
      map_mul' := fun g h => Subtype.ext (map_mul M g.1 h.1) }
  have hinj : Function.Injective ψ₀ := fun g h hgh =>
    Subtype.ext (M.injective (congrArg Subtype.val hgh))
  have hsurj : Function.Surjective ψ₀ := by
    rintro ⟨A, hA⟩
    have hA' := hA
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp] at hA'
    obtain ⟨g, hg, hgA⟩ := hA'
    refine ⟨⟨g, ?_⟩, Subtype.ext hgA⟩
    intro x y
    exact TauCeti.BilinForm.mem_isometryGroup_iff.1 hg x y
  have hbij : Function.Bijective (ψ₀.comp e₁.toMonoidHom) :=
    ⟨hinj.comp e₁.injective, hsurj.comp e₁.surjective⟩
  exact ⟨MulEquiv.ofBijective _ hbij⟩

end Space2

section Blk

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def split3 : QV K (Fin 3) ≃ₗ[K] QV K (Fin 2) × Qext K where
  toFun v := (fun i : Fin 2 => v (Fin.castSucc i), v 2)
  invFun w := ![w.1 0, w.1 1, w.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv w := by
    refine Prod.ext ?_ rfl
    funext i
    fin_cases i <;> rfl

@[expose] noncomputable def blk2Aut (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :
    QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) :=
  split3.trans ((g.prodCongr (LinearEquiv.refl K (Qext K))).trans split3.symm)

@[expose] def front (v : QV K (Fin 3)) : QV K (Fin 2) := fun i => v (Fin.castSucc i)

theorem blk2Aut_apply_zero (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (v : QV K (Fin 3)) :
    blk2Aut g v 0 = g (front v) 0 := rfl

theorem blk2Aut_apply_one (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (v : QV K (Fin 3)) :
    blk2Aut g v 1 = g (front v) 1 := rfl

theorem blk2Aut_apply_two (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (v : QV K (Fin 3)) :
    blk2Aut g v 2 = v 2 := rfl

theorem front_blk2Aut (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (v : QV K (Fin 3)) :
    front (blk2Aut g v) = g (front v) := by
  funext i
  fin_cases i <;> rfl

theorem blk2Aut_mul (g h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :
    blk2Aut (g * h) = blk2Aut g * blk2Aut h := by
  refine LinearEquiv.ext fun v => ?_
  funext k
  fin_cases k
  · show blk2Aut (g * h) v 0 = blk2Aut g (blk2Aut h v) 0
    rw [blk2Aut_apply_zero, blk2Aut_apply_zero, front_blk2Aut]
    rfl
  · show blk2Aut (g * h) v 1 = blk2Aut g (blk2Aut h v) 1
    rw [blk2Aut_apply_one, blk2Aut_apply_one, front_blk2Aut]
    rfl
  · rfl

theorem blk2Aut_one : blk2Aut (1 : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = 1 := by
  refine LinearEquiv.ext fun v => ?_
  funext k
  fin_cases k <;> rfl

theorem blk2Aut_mem (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (hg : g ∈ M2 K) :
    blk2Aut g ∈ M10 K := by
  rw [mem_M10_iff]
  intro x y
  have h := (mem_M2_iff g).1 hg (front x) (front y)
  simp only [Fin.sum_univ_two, Fin.sum_univ_three] at h ⊢
  rw [blk2Aut_apply_zero, blk2Aut_apply_zero, blk2Aut_apply_one, blk2Aut_apply_one,
    blk2Aut_apply_two, blk2Aut_apply_two, h]
  rfl

@[expose] noncomputable def blk2 : ↥(M2 K) →* ↥(M10 K) where
  toFun g := ⟨blk2Aut g.1, blk2Aut_mem g.1 g.2⟩
  map_one' := Subtype.ext blk2Aut_one
  map_mul' g h := Subtype.ext (blk2Aut_mul g.1 h.1)

theorem coe_blk2 (g : ↥(M2 K)) :
    ((blk2 g : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = blk2Aut g.1 := rfl

theorem blk2_injective : Function.Injective (blk2 (K := K)) := by
  intro g h hgh
  apply Subtype.ext
  refine LinearEquiv.ext fun u => ?_
  have h1 := congrArg (fun x : ↥(M10 K) =>
    front ((x : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (split3.symm (u, 0)))) hgh
  simp only [coe_blk2, front_blk2Aut] at h1
  have hf : ∀ u : QV K (Fin 2), front (split3.symm (u, 0)) = u := by
    intro u
    funext i
    fin_cases i <;> rfl
  rwa [hf] at h1

end Blk

section Cent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def e2v (u : Qext K) : QV K (Fin 3) := Pi.single 2 u

theorem e2v_zero_coord (u : Qext K) : e2v u 0 = 0 := by simp [e2v]

theorem e2v_one_coord (u : Qext K) : e2v u 1 = 0 := by simp [e2v]

theorem e2v_two_coord (u : Qext K) : e2v u 2 = u := by simp [e2v]

@[expose] noncomputable def bAut (z : (Qext K)ˣ) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) :=
  torusEquiv ![1, 1, z]

theorem bAut_apply_zero (z : (Qext K)ˣ) (v : QV K (Fin 3)) : bAut z v 0 = v 0 := by
  simp [bAut, torusEquiv_apply]

theorem bAut_apply_one (z : (Qext K)ˣ) (v : QV K (Fin 3)) : bAut z v 1 = v 1 := by
  simp [bAut, torusEquiv_apply]

theorem bAut_apply_two (z : (Qext K)ˣ) (v : QV K (Fin 3)) : bAut z v 2 = (z : Qext K) * v 2 := by
  simp [bAut, torusEquiv_apply]

@[expose] noncomputable def b10 (z : (Qext K)ˣ) (hmem : bAut z ∈ M10 K) : ↥(M10 K) :=
  ⟨bAut z, hmem⟩

theorem vec_eq_front_add (v : QV K (Fin 3)) : v = split3.symm (front v, 0) + e2v (v 2) := by
  funext k
  fin_cases k <;> simp [split3, front, e2v]

section Comm

variable {z : (Qext K)ˣ} {g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)}

theorem comm_apply (hg : g * bAut z = bAut z * g) (v : QV K (Fin 3)) :
    g (bAut z v) = bAut z (g v) :=
  congrArg (fun h : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) => h v) hg

theorem coord_two_zero_of_comm (hz1 : z ≠ 1) (hg : g * bAut z = bAut z * g)
    (v : QV K (Fin 3)) (hv : v 2 = 0) : g v 2 = 0 := by
  have h1 : bAut z v = v := by
    funext k
    fin_cases k
    · exact bAut_apply_zero z v
    · exact bAut_apply_one z v
    · show bAut z v 2 = v 2
      rw [bAut_apply_two, hv, mul_zero]
  have h2 : bAut z (g v) = g v := by
    have := comm_apply hg v
    rw [h1] at this
    exact this.symm
  have h3 := congrFun h2 2
  rw [bAut_apply_two] at h3
  by_contra hne
  apply hz1
  apply Units.ext
  have : ((z : Qext K) - 1) * (g v 2) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 this with h | h
  · simpa [sub_eq_zero] using h
  · exact absurd h hne

theorem front_single_zero_of_comm (hz1 : z ≠ 1) (hg : g * bAut z = bAut z * g) (u : Qext K) :
    g (e2v u) 0 = 0 ∧ g (e2v u) 1 = 0 := by
  have hz' : (z : Qext K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hz1 (Units.ext h)
  set u' : Qext K := ((z : Qext K) - 1)⁻¹ * u with hu'
  have e : e2v u = bAut z (e2v u') - e2v u' := by
    funext k
    fin_cases k
    · show e2v u 0 = bAut z (e2v u') 0 - e2v u' 0
      rw [bAut_apply_zero, e2v_zero_coord, e2v_zero_coord]
      simp
    · show e2v u 1 = bAut z (e2v u') 1 - e2v u' 1
      rw [bAut_apply_one, e2v_one_coord, e2v_one_coord]
      simp
    · show e2v u 2 = bAut z (e2v u') 2 - e2v u' 2
      rw [bAut_apply_two, e2v_two_coord, e2v_two_coord, hu']
      field_simp
  have e2 : g (e2v u) = bAut z (g (e2v u')) - g (e2v u') := by
    rw [e, map_sub, comm_apply hg]
  rw [e2]
  constructor
  · show bAut z (g (e2v u')) 0 - g (e2v u') 0 = 0
    rw [bAut_apply_zero, sub_self]
  · show bAut z (g (e2v u')) 1 - g (e2v u') 1 = 0
    rw [bAut_apply_one, sub_self]

@[expose] noncomputable def wOf (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) : Qext K := g (e2v 1) 2

theorem e2v_smul (s : K) (u : Qext K) : s • e2v u = e2v (s • u) := by
  funext k
  fin_cases k <;> simp [e2v]

theorem e2v_add (u v : Qext K) : e2v (u + v) = e2v u + e2v v := by
  funext k
  fin_cases k <;> simp [e2v]

theorem single_two_apply (hz1 : z ≠ 1) (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hg : g * bAut z = bAut z * g) (u : Qext K) :
    g (e2v u) = e2v (u * wOf g) := by
  have he : g (e2v 1) = e2v (wOf g) := by
    funext k
    fin_cases k
    · exact (front_single_zero_of_comm hz1 hg 1).1.trans (e2v_zero_coord _).symm
    · exact (front_single_zero_of_comm hz1 hg 1).2.trans (e2v_one_coord _).symm
    · simp [wOf, e2v_two_coord]
  obtain ⟨s, t, hst⟩ := span_one_z hzK u
  have e1 : e2v u = s • e2v 1 + t • e2v (z : Qext K) := by
    rw [e2v_smul, e2v_smul, ← e2v_add, hst]
  have e3 : e2v (z : Qext K) = bAut z (e2v 1) := by
    funext k
    fin_cases k
    · show e2v (z : Qext K) 0 = bAut z (e2v 1) 0
      rw [bAut_apply_zero, e2v_zero_coord, e2v_zero_coord]
    · show e2v (z : Qext K) 1 = bAut z (e2v 1) 1
      rw [bAut_apply_one, e2v_one_coord, e2v_one_coord]
    · show e2v (z : Qext K) 2 = bAut z (e2v 1) 2
      rw [bAut_apply_two, e2v_two_coord, e2v_two_coord, mul_one]
  have e4 : g (e2v (z : Qext K)) = e2v ((z : Qext K) * wOf g) := by
    rw [e3, comm_apply hg, he]
    funext k
    fin_cases k
    · show bAut z (e2v (wOf g)) 0 = e2v ((z : Qext K) * wOf g) 0
      rw [bAut_apply_zero, e2v_zero_coord, e2v_zero_coord]
    · show bAut z (e2v (wOf g)) 1 = e2v ((z : Qext K) * wOf g) 1
      rw [bAut_apply_one, e2v_one_coord, e2v_one_coord]
    · show bAut z (e2v (wOf g)) 2 = e2v ((z : Qext K) * wOf g) 2
      rw [bAut_apply_two, e2v_two_coord, e2v_two_coord]
  rw [e1, map_add, map_smul, map_smul, he, e4, e2v_smul, e2v_smul, ← e2v_add, hst]
  congr 1
  simp only [Algebra.smul_def, mul_one]
  ring

theorem wOf_ne_zero (hz1 : z ≠ 1) (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hg : g * bAut z = bAut z * g) : wOf g ≠ 0 := by
  intro h0
  have h1 := single_two_apply hz1 hzK hg 1
  rw [h0, mul_zero] at h1
  have h2 : g (e2v 1) = g 0 := by
    rw [h1, map_zero]
    funext k
    fin_cases k <;> simp [e2v]
  have h3 := g.injective h2
  have := congrFun h3 2
  simp [e2v] at this

theorem wOf_mul (hz1 : z ≠ 1) (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    {h : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)} (hg : g * bAut z = bAut z * g)
    (hh : h * bAut z = bAut z * h) : wOf (g * h) = wOf g * wOf h := by
  have h1 : (g * h) (e2v 1) = g (e2v (wOf h)) := by
    rw [LinearEquiv.mul_apply, single_two_apply hz1 hzK hh 1, one_mul]
  rw [wOf, h1, single_two_apply hz1 hzK hg, e2v_two_coord, mul_comm]

end Comm

end Cent

section Phi

variable {K : Type} [Field K] [Finite K] [CharP K 2] {z : (Qext K)ˣ}

theorem coord_split3_symm_two (u : QV K (Fin 2)) : (split3.symm (u, 0) : QV K (Fin 3)) 2 = 0 :=
  rfl

theorem split3_symm_zero (u : QV K (Fin 2)) (c : Qext K) :
    (split3.symm (u, c) : QV K (Fin 3)) 0 = u 0 := rfl

theorem split3_symm_one (u : QV K (Fin 2)) (c : Qext K) :
    (split3.symm (u, c) : QV K (Fin 3)) 1 = u 1 := rfl

theorem exists_blk2_of_wOf_one (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    {g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)} (hgM : g ∈ M10 K) (hg : g * bAut z = bAut z * g)
    (hw : wOf g = 1) : ∃ h ∈ M2 K, blk2Aut h = g := by
  classical
  let inj : QV K (Fin 2) →ₗ[K] QV K (Fin 3) :=
    split3.symm.toLinearMap ∘ₗ LinearMap.inl K (QV K (Fin 2)) (Qext K)
  let frontL : QV K (Fin 3) →ₗ[K] QV K (Fin 2) :=
    LinearMap.fst K (QV K (Fin 2)) (Qext K) ∘ₗ split3.toLinearMap
  let h₀ : QV K (Fin 2) →ₗ[K] QV K (Fin 2) := frontL ∘ₗ g.toLinearMap ∘ₗ inj
  have h0apply : ∀ u, h₀ u = front (g (split3.symm (u, 0))) := fun u => rfl
  have hinj0 : ∀ u, inj u = split3.symm (u, 0) := fun u => rfl
  have hh0 : Function.Injective h₀ := by
    refine (injective_iff_map_eq_zero h₀).2 fun u hu => ?_
    have hc2 : g (split3.symm (u, 0)) 2 = 0 :=
      coord_two_zero_of_comm hz1 hg _ (coord_split3_symm_two u)
    have hg0 : g (split3.symm (u, 0)) = 0 := by
      funext k
      fin_cases k
      · exact congrFun hu 0
      · exact congrFun hu 1
      · exact hc2
    have h1 : split3.symm (u, 0) = 0 := g.injective (by rw [hg0, map_zero])
    have h2 : ((u, 0) : QV K (Fin 2) × Qext K) = 0 := by
      apply split3.symm.injective
      rw [h1, map_zero]
    exact congrArg Prod.fst h2
  let h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) := LinearEquiv.ofInjectiveEndo h₀ hh0
  have hhapply : ∀ u, h u = h₀ u := fun u => congrFun (LinearEquiv.coe_ofInjectiveEndo h₀ hh0) u
  have hgfront : ∀ u : QV K (Fin 2), ∀ k : Fin 2, g (split3.symm (u, 0)) (Fin.castSucc k) =
      h u k := fun u k => by rw [hhapply, h0apply]; rfl
  refine ⟨h, ?_, ?_⟩
  · rw [mem_M2_iff]
    intro x y
    have hM := (mem_M10_iff g).1 hgM (split3.symm (x, 0)) (split3.symm (y, 0))
    simp only [Fin.sum_univ_two, Fin.sum_univ_three] at hM ⊢
    have e0 := hgfront x 0
    have e1 := hgfront x 1
    have f0 := hgfront y 0
    have f1 := hgfront y 1
    have c2x := coord_two_zero_of_comm hz1 hg _ (coord_split3_symm_two x)
    have c2y := coord_two_zero_of_comm hz1 hg _ (coord_split3_symm_two y)
    rw [show (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 from rfl] at e0 f0
    rw [show (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 from rfl] at e1 f1
    rw [e0, e1, f0, f1, c2x, c2y, split3_symm_zero, split3_symm_one, split3_symm_zero,
      split3_symm_one, coord_split3_symm_two, coord_split3_symm_two] at hM
    simpa using hM
  · refine LinearEquiv.ext fun v => ?_
    have hv := vec_eq_front_add v
    have hsplit : g v = g (split3.symm (front v, 0)) + g (e2v (v 2)) := by
      conv_lhs => rw [hv]
      rw [map_add]
    have hs2 := single_two_apply hz1 hzK hg (v 2)
    rw [hw, mul_one] at hs2
    funext k
    fin_cases k
    · show blk2Aut h v 0 = g v 0
      rw [blk2Aut_apply_zero, hsplit, Pi.add_apply, hs2, e2v_zero_coord, add_zero, hhapply,
        h0apply]
      rfl
    · show blk2Aut h v 1 = g v 1
      rw [blk2Aut_apply_one, hsplit, Pi.add_apply, hs2, e2v_one_coord, add_zero, hhapply,
        h0apply]
      rfl
    · show blk2Aut h v 2 = g v 2
      rw [blk2Aut_apply_two, hsplit, Pi.add_apply, hs2, e2v_two_coord,
        coord_two_zero_of_comm hz1 hg _ (coord_split3_symm_two (front v)), zero_add]

theorem comm_of_mem_centralizer {hmem : bAut z ∈ M10 K} {g : ↥(M10 K)}
    (hg : g ∈ Subgroup.centralizer ({b10 z hmem} : Set ↥(M10 K))) :
    (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) * bAut z =
      bAut z * (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) :=
  congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)

@[expose] noncomputable def phi10 (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) (hmem : bAut z ∈ M10 K) :
    ↥(Subgroup.centralizer ({b10 z hmem} : Set ↥(M10 K))) →* (Qext K)ˣ where
  toFun g := Units.mk0 (wOf ((g : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)))
    (wOf_ne_zero hz1 hzK (comm_of_mem_centralizer g.2))
  map_one' := by
    apply Units.ext
    show wOf (1 : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = 1
    simp [wOf, e2v_two_coord]
  map_mul' g h := by
    apply Units.ext
    exact wOf_mul hz1 hzK (comm_of_mem_centralizer g.2) (comm_of_mem_centralizer h.2)

theorem blk2_mem_centralizer (hmem : bAut z ∈ M10 K) (h : ↥(M2 K)) :
    blk2 h ∈ Subgroup.centralizer ({b10 z hmem} : Set ↥(M10 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  have hf : front (bAut z v) = front v := by
    funext i
    fin_cases i
    · exact bAut_apply_zero z v
    · exact bAut_apply_one z v
  funext k
  fin_cases k
  · show blk2Aut h.1 (bAut z v) 0 = bAut z (blk2Aut h.1 v) 0
    rw [blk2Aut_apply_zero, bAut_apply_zero, blk2Aut_apply_zero, hf]
  · show blk2Aut h.1 (bAut z v) 1 = bAut z (blk2Aut h.1 v) 1
    rw [blk2Aut_apply_one, bAut_apply_one, blk2Aut_apply_one, hf]
  · show blk2Aut h.1 (bAut z v) 2 = bAut z (blk2Aut h.1 v) 2
    rw [blk2Aut_apply_two, bAut_apply_two, bAut_apply_two, blk2Aut_apply_two]

theorem ker_phi10 (hz1 : z ≠ 1) (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hmem : bAut z ∈ M10 K) :
    (phi10 hz1 hzK hmem).ker =
      (blk2 (K := K)).range.subgroupOf
        (Subgroup.centralizer ({b10 z hmem} : Set ↥(M10 K))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hw : wOf ((g : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = 1 :=
      congrArg Units.val h
    obtain ⟨h', hh'M, hh'⟩ := exists_blk2_of_wOf_one hz1 hzK (g : ↥(M10 K)).2
      (comm_of_mem_centralizer g.2) hw
    exact ⟨⟨h', hh'M⟩, Subtype.ext hh'⟩
  · rintro ⟨h', hh'⟩
    apply Units.ext
    show wOf ((g : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = 1
    rw [← hh']
    show blk2Aut h'.1 (e2v 1) 2 = 1
    rw [blk2Aut_apply_two, e2v_two_coord]

end Phi

section Levi

open CFSG.LieType.Universal.Unitary
open CFSG.Assembly.LowTwoRank (StatedProj)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {z : (Qext K)ˣ}

noncomputable def blkEquiv : ↥((blk2 (K := K)).range) ≃* ↥(StatedSp 2 K) :=
  (MonoidHom.ofInjective blk2_injective).symm.trans (nonempty_m2Equiv (K := K)).some

theorem isQuasisimple_range_blk2 (hK : 4 ≤ Nat.card K) :
    IsQuasisimple ↥((blk2 (K := K)).range) :=
  isQuasisimple_of_mulEquiv blkEquiv.symm
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (Or.inl (Or.inr hK)))

theorem card_center_range_blk2 :
    Nat.card (Subgroup.center ↥((blk2 (K := K)).range)) = 1 := by
  rw [card_center_mulEquiv blkEquiv, CFSG.LieType.Universal.Symplectic.center_eq 2 K,
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)]
  simp

theorem perfectResidual_centralizer_b10 (hK : 4 ≤ Nat.card K) (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) (hmem : bAut z ∈ M10 K) :
    inSubgroup perfectResidual (Subgroup.centralizer ({b10 z hmem} : Set ↥(M10 K))) =
      (blk2 (K := K)).range := by
  have hq := isQuasisimple_range_blk2 (K := K) hK
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨h, rfl⟩
    exact blk2_mem_centralizer hmem h) hq.1 (phi10 hz1 hzK hmem) (ker_phi10 hz1 hzK hmem)

theorem isQuasisimple_perfectResidual_centralizer_b10 (hK : 4 ≤ Nat.card K) (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) (hmem : bAut z ∈ M10 K) :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({b10 z hmem} : Set ↥(M10 K)))) := by
  rw [perfectResidual_centralizer_b10 hK hz1 hzK hmem]
  exact isQuasisimple_range_blk2 hK

theorem exists_model_range_blk2 :
    Nonempty (↥((blk2 (K := K)).range) ⧸ Subgroup.center ↥((blk2 (K := K)).range) ≃*
      StatedProj (StatedSp 2 K)) :=
  ⟨(exists_centerQuotient_mulEquiv blkEquiv).some.trans
    (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 2 K)⟩

end Levi

end CFSG.RankThree.PartOne.KLAY10
