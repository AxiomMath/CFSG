module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBLevi
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras

variable {F : Type} [Field F] {p : ℕ}

private theorem pairMat_injective {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R] {a b : ι}
    (hab : a ≠ b) : Function.Injective (pairMat a b : Matrix (Fin 2) (Fin 2) R → Matrix ι ι R) := by
  intro g g' h
  obtain ⟨g11, g12, g21, g22⟩ := pairMat_apply_pair hab g
  obtain ⟨g11', g12', g21', g22'⟩ := pairMat_apply_pair hab g'
  ext x y
  fin_cases x <;> fin_cases y
  · simpa [g11, g11'] using congrFun (congrFun h a) a
  · simpa [g12, g12'] using congrFun (congrFun h a) b
  · simpa [g21, g21'] using congrFun (congrFun h b) a
  · simpa [g22, g22'] using congrFun (congrFun h b) b

private theorem lam_eq_longBlock {r : ℕ} (i : Fin r) (g : SpecialLinearGroup (Fin 2) F) :
    lam i g = longBlock F r i g := by
  apply statedSp_ext
  rfl

theorem lam_injective {r : ℕ} (i : Fin r) :
    Function.Injective (lam i : SpecialLinearGroup (Fin 2) F →* StatedSp r F) := by
  intro g g' h
  have hm : mat r F (lam i g) = mat r F (lam i g') := by rw [h]
  simp only [mat_apply, coe_lam] at hm
  exact Subtype.ext (pairMat_injective Sum.inl_ne_inr hm)

theorem spLeviBlock_lam {m : ℕ} (i : Fin m) (g : SpecialLinearGroup (Fin 2) F) :
    CFSG.StandardType.spLeviBlock m F (lam i g) = lam i.succ g := by
  rw [lam_eq_longBlock i g, CFSG.StandardType.spLeviBlock]
  rw [spEmbed_longBlock (Fin.succ_injective m) i g]
  exact (lam_eq_longBlock i.succ g).symm

private theorem isSupp_iff_basic {n : ℕ} {A : Set (Fin n ⊕ Fin n)}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp A M ↔
      CFSG.ClassicalInvolution.Models.SymplecticPairs.IsSupp A M := by
  constructor
  · intro h x y hxy
    exact h x y (not_and_or.mp hxy)
  · intro h x y hxy
    exact h x y (not_and_or.mpr hxy)

private theorem isSupp_mat_spLeviBlock {m : ℕ} (h : StatedSp m F) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp
      (Set.range (Sum.map Fin.succ Fin.succ : Fin m ⊕ Fin m → Fin (m + 1) ⊕ Fin (m + 1)))
      (mat (m + 1) F (CFSG.StandardType.spLeviBlock m F h)) := by
  rw [isSupp_iff_basic]
  simpa only [CFSG.StandardType.spLeviBlock] using
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.isSupp_spEmbed (K := F)
      (Fin.succ_injective m) h)

private theorem disjoint_plane_zero_range_succ (m : ℕ) :
    Disjoint ({Sum.inl (0 : Fin (m + 1)), Sum.inr (0 : Fin (m + 1))} :
        Set (Fin (m + 1) ⊕ Fin (m + 1)))
      (Set.range (Sum.map Fin.succ Fin.succ : Fin m ⊕ Fin m → Fin (m + 1) ⊕ Fin (m + 1))) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨y, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases y with y | y <;> simp [Fin.succ_ne_zero] at hx

private theorem inl_zero_notMem_range_succ (m : ℕ) :
    (Sum.inl (0 : Fin (m + 1)) : Fin (m + 1) ⊕ Fin (m + 1)) ∉
      Set.range (Sum.map Fin.succ Fin.succ : Fin m ⊕ Fin m → Fin (m + 1) ⊕ Fin (m + 1)) := by
  rintro ⟨y, hy⟩
  rcases y with y | y <;> simp [Fin.succ_ne_zero] at hy

private theorem inr_zero_notMem_range_succ (m : ℕ) :
    (Sum.inr (0 : Fin (m + 1)) : Fin (m + 1) ⊕ Fin (m + 1)) ∉
      Set.range (Sum.map Fin.succ Fin.succ : Fin m ⊕ Fin m → Fin (m + 1) ⊕ Fin (m + 1)) := by
  rintro ⟨y, hy⟩
  rcases y with y | y <;> simp [Fin.succ_ne_zero] at hy

private theorem mat_spLeviBlock_apply_of_notMem {m : ℕ} (h : StatedSp m F)
    {a b : Fin (m + 1) ⊕ Fin (m + 1)}
    (ha : a ∉ Set.range (Sum.map Fin.succ Fin.succ : Fin m ⊕ Fin m → Fin (m + 1) ⊕ Fin (m + 1)))
    (hb : b ∉ Set.range (Sum.map Fin.succ Fin.succ : Fin m ⊕ Fin m → Fin (m + 1) ⊕ Fin (m + 1))) :
    mat (m + 1) F (CFSG.StandardType.spLeviBlock m F h) a b =
      (1 : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) a b := by
  rw [CFSG.StandardType.spLeviBlock, mat_spEmbed]
  exact CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbedMat_apply_of_not_mem (mat m F h)
    (fun hcon => ha hcon.1)

private theorem mat_commute_lam_zero_spLeviBlock {m : ℕ} (g : SpecialLinearGroup (Fin 2) F)
    (h : StatedSp m F) :
    Commute (mat (m + 1) F (lam (0 : Fin (m + 1)) g))
      (mat (m + 1) F (CFSG.StandardType.spLeviBlock m F h)) :=
  (isSupp_lam (0 : Fin (m + 1)) g).commute (isSupp_mat_spLeviBlock h)
    (disjoint_plane_zero_range_succ m)

theorem lam_zero_commute_spLeviBlock {m : ℕ} (g : SpecialLinearGroup (Fin 2) F) (h : StatedSp m F) :
    Commute (lam (0 : Fin (m + 1)) g) (CFSG.StandardType.spLeviBlock m F h) := by
  exact statedSp_commute (mat_commute_lam_zero_spLeviBlock g h)

theorem eq_one_of_lam_zero_eq_spLeviBlock {m : ℕ} {g : SpecialLinearGroup (Fin 2) F}
    {h : StatedSp m F} (hgh : lam (0 : Fin (m + 1)) g = CFSG.StandardType.spLeviBlock m F h) :
    g = 1 ∧ h = 1 := by
  have hm : mat (m + 1) F (lam (0 : Fin (m + 1)) g) =
      mat (m + 1) F (CFSG.StandardType.spLeviBlock m F h) := by rw [hgh]
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (1 : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have h' := congrFun (congrFun hm (Sum.inl (0 : Fin (m + 1)))) (Sum.inl (0 : Fin (m + 1)))
    rw [mat_apply, coe_lam, pairMat_apply_fst,
      mat_spLeviBlock_apply_of_notMem h (inl_zero_notMem_range_succ m)
        (inl_zero_notMem_range_succ m)] at h'
    simpa using h'
  have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (1 : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    have h' := congrFun (congrFun hm (Sum.inl (0 : Fin (m + 1)))) (Sum.inr (0 : Fin (m + 1)))
    rw [mat_apply, coe_lam, pairMat_apply_fst,
      mat_spLeviBlock_apply_of_notMem h (inl_zero_notMem_range_succ m)
        (inr_zero_notMem_range_succ m)] at h'
    simpa using h'
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (1 : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    have h' := congrFun (congrFun hm (Sum.inr (0 : Fin (m + 1)))) (Sum.inl (0 : Fin (m + 1)))
    rw [mat_apply, coe_lam, pairMat_apply_snd Sum.inl_ne_inr,
      mat_spLeviBlock_apply_of_notMem h (inr_zero_notMem_range_succ m)
        (inl_zero_notMem_range_succ m)] at h'
    simpa using h'
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (1 : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have h' := congrFun (congrFun hm (Sum.inr (0 : Fin (m + 1)))) (Sum.inr (0 : Fin (m + 1)))
    rw [mat_apply, coe_lam, pairMat_apply_snd Sum.inl_ne_inr,
      mat_spLeviBlock_apply_of_notMem h (inr_zero_notMem_range_succ m)
        (inr_zero_notMem_range_succ m)] at h'
    simpa using h'
  have hg : g = 1 := Matrix.SpecialLinearGroup.ext g 1 fun a b => by
    fin_cases a <;> fin_cases b <;> simp [h00, h01, h10, h11]
  refine ⟨hg, ?_⟩
  have hh : h = 1 := by
    apply CFSG.StandardType.spLeviBlock_injective
    simp only [← hgh, hg, map_one]
  exact hh

@[expose] noncomputable def spPlaneLevi (m : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin 2) F × StatedSp m F →* StatedSp (m + 1) F :=
  MonoidHom.noncommCoprod (lam (0 : Fin (m + 1))) (CFSG.StandardType.spLeviBlock m F)
    fun g h => lam_zero_commute_spLeviBlock g h

theorem spPlaneLevi_apply {m : ℕ} (g : SpecialLinearGroup (Fin 2) F) (h : StatedSp m F) :
    spPlaneLevi m F (g, h) = lam (0 : Fin (m + 1)) g * CFSG.StandardType.spLeviBlock m F h := by
  rw [spPlaneLevi, MonoidHom.noncommCoprod_apply]

theorem spPlaneLevi_injective (m : ℕ) : Function.Injective (spPlaneLevi m F) := by
  rintro ⟨g, h⟩ ⟨g', h'⟩ heq
  simp only [spPlaneLevi_apply] at heq
  have h1 : lam (0 : Fin (m + 1)) (g'⁻¹ * g) * CFSG.StandardType.spLeviBlock m F h =
      CFSG.StandardType.spLeviBlock m F h' := by
    calc lam (0 : Fin (m + 1)) (g'⁻¹ * g) * CFSG.StandardType.spLeviBlock m F h
        = lam (0 : Fin (m + 1)) g'⁻¹ * (lam (0 : Fin (m + 1)) g *
            CFSG.StandardType.spLeviBlock m F h) := by rw [map_mul, mul_assoc]
      _ = lam (0 : Fin (m + 1)) g'⁻¹ * (lam (0 : Fin (m + 1)) g' *
            CFSG.StandardType.spLeviBlock m F h') := by rw [heq]
      _ = CFSG.StandardType.spLeviBlock m F h' := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hkey : lam (0 : Fin (m + 1)) (g'⁻¹ * g) =
      CFSG.StandardType.spLeviBlock m F (h' * h⁻¹) := by
    have h2 : lam (0 : Fin (m + 1)) (g'⁻¹ * g) * CFSG.StandardType.spLeviBlock m F h =
        CFSG.StandardType.spLeviBlock m F (h' * h⁻¹) *
          CFSG.StandardType.spLeviBlock m F h := by
      rw [h1, map_mul, map_inv]
      group
    exact mul_right_cancel h2
  obtain ⟨hg, hh⟩ := eq_one_of_lam_zero_eq_spLeviBlock hkey
  exact Prod.ext (inv_mul_eq_one.mp hg).symm (mul_inv_eq_one.mp hh).symm

theorem lam_zero_surjective :
    Function.Surjective (lam (0 : Fin 1) : SpecialLinearGroup (Fin 2) F →* StatedSp 1 F) := by
  intro X
  have hcol : ∀ c : Fin 1 ⊕ Fin 1, c ∉ coords (0 : Fin 1) →
      mat 1 F X c (Sum.inl (0 : Fin 1)) = 0 := by
    intro c hc
    exact absurd (by rcases c with c | c <;> fin_cases c <;> simp [coords]) hc
  refine ⟨mkSL (stdBlock (0 : Fin 1) (mat 1 F X)) (det_stdBlock_eq_one X 0 hcol), ?_⟩
  apply statedSp_ext
  rw [coe_lam]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [pairMat, stdBlock, mat_apply]

private def finTailHom (G : Type*) [Monoid G] (n : ℕ) :
    ((Fin (n + 1) → G) →* (Fin n → G)) where
  toFun := Fin.tail
  map_one' := funext fun _ => rfl
  map_mul' := fun _ _ => funext fun _ => rfl

@[simp] private theorem finTailHom_apply (G : Type*) [Monoid G] (n : ℕ) (f : Fin (n + 1) → G) :
    finTailHom G n f = Fin.tail f := rfl

theorem spPlaneTorus_succ {m : ℕ} (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F)
    (f : Fin (m + 1) → Multiplicative (ZMod p)) :
    spPlaneTorus (m + 1) ζ f = lam (0 : Fin (m + 1)) (ζ (f 0)) *
      CFSG.StandardType.spLeviBlock m F (spPlaneTorus m ζ (Fin.tail f)) := by
  have hAB : spPlaneTorus (m + 1) ζ =
      (spPlaneLevi m F).comp
        ((ζ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => Multiplicative (ZMod p)) 0)).prod
          ((spPlaneTorus m ζ).comp (finTailHom (Multiplicative (ZMod p)) m))) := by
    refine MonoidHom.pi_ext (fun i a => ?_)
    rw [spPlaneTorus_mulSingle]
    simp only [MonoidHom.comp_apply, MonoidHom.prod_apply, Pi.evalMonoidHom_apply,
      finTailHom_apply, spPlaneLevi_apply]
    induction i using Fin.cases with
    | zero =>
        have htail0 : Fin.tail (Pi.mulSingle
            (M := fun _ : Fin (m + 1) => Multiplicative (ZMod p)) (0 : Fin (m + 1)) a) = 1 := by
          funext l
          simp [Fin.tail, Pi.mulSingle_apply, Fin.succ_ne_zero]
        simp [Pi.mulSingle_eq_same, htail0]
    | succ j =>
        have htail : Fin.tail (Pi.mulSingle
            (M := fun _ : Fin (m + 1) => Multiplicative (ZMod p)) j.succ a) =
            (Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod p)) j a) := by
          funext l
          simp [Fin.tail, Pi.mulSingle_apply, Fin.succ_inj]
        simp [htail, spPlaneTorus_mulSingle, spLeviBlock_lam, Pi.mulSingle_apply,
          Fin.succ_ne_zero]
  calc spPlaneTorus (m + 1) ζ f
      = ((spPlaneLevi m F).comp
          ((ζ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => Multiplicative (ZMod p)) 0)).prod
            ((spPlaneTorus m ζ).comp (finTailHom (Multiplicative (ZMod p)) m)))) f :=
        congrArg (fun ψ => ψ f) hAB
    _ = lam (0 : Fin (m + 1)) (ζ (f 0)) *
          CFSG.StandardType.spLeviBlock m F (spPlaneTorus m ζ (Fin.tail f)) := by
        simp only [MonoidHom.comp_apply, MonoidHom.prod_apply, Pi.evalMonoidHom_apply,
          finTailHom_apply, spPlaneLevi_apply]

end CFSG.StandardType.SpJoin
