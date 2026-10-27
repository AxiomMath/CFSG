module

public import CFSG.RankThree.Chevalley.SteinbergBID4Kernel

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

variable (τ) in
@[expose] def wordAct (ω : List (Fin τ.rank)) (α : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  ω.foldr (reflect τ) α

variable (τ) in
@[expose] def wordSign : List (Fin τ.rank) → (Fin τ.rank → ℤ) → ℤ
  | [], _ => 1
  | i :: ω, α => allRootWeylSign τ i (wordAct τ ω α) * wordSign ω α

variable (τ) in
@[expose] def wordRep (R : Type*) [CommRing R] (ω : List (Fin τ.rank)) :
    (Module.End R (RootModule τ R))ˣ :=
  (ω.map fun i => weylElt τ R i 1).prod

theorem isRoot_wordAct (ω : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    IsRoot τ (wordAct τ ω α) := by
  induction ω with
  | nil => exact hα
  | cons i ω ih => exact IsRoot.reflect i ih

theorem wordAct_eq_smul (ω : List (Fin τ.rank)) (α : Fin τ.rank → ℤ) :
    wordAct τ ω α = (coxeterSystem τ).wordProd ω • α :=
  (wordProd_smul ω α).symm

theorem wordRep_conj_pinnedX (R : Type*) [CommRing R] (ω : List (Fin τ.rank))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : R) :
    wordRep τ R ω * pinnedX τ R α c * (wordRep τ R ω)⁻¹ =
      pinnedX τ R (wordAct τ ω α) ((wordSign τ ω α : R) * c) := by
  induction ω generalizing c with
  | nil =>
    simp [wordRep, wordAct, wordSign]
  | cons i ω ih =>
    have e : wordRep τ R (i :: ω) = weylElt τ R i 1 * wordRep τ R ω := by
      simp [wordRep]
    rw [e, _root_.mul_inv_rev, show weylElt τ R i 1 * wordRep τ R ω * pinnedX τ R α c *
      ((wordRep τ R ω)⁻¹ * (weylElt τ R i 1)⁻¹) = weylElt τ R i 1 *
        (wordRep τ R ω * pinnedX τ R α c * (wordRep τ R ω)⁻¹) * (weylElt τ R i 1)⁻¹ by group,
      ih, weylElt_one_mul_pinnedX_mul_inv R i (isRoot_wordAct ω hα)]
    simp only [wordAct, wordSign, List.foldr_cons, Int.cast_mul, mul_assoc]

theorem wordSign_eq_one_or (ω : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    wordSign τ ω α = 1 ∨ wordSign τ ω α = -1 := by
  induction ω with
  | nil => exact Or.inl rfl
  | cons i ω ih =>
    have h := (all_root_weyl_infinitesimal.{0} τ).2.2.2.1 i _ (isRoot_wordAct ω hα)
    rcases h with h | h <;> rcases ih with ih | ih <;> simp [wordSign, h, ih]

theorem baseChange_wordRep {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (ω : List (Fin τ.rank)) :
    BaseChange f (wordRep τ R ω : Module.End R (RootModule τ R))
      (wordRep τ S ω : Module.End S (RootModule τ S)) := by
  induction ω with
  | nil => simpa [wordRep] using BaseChange.one (τ := τ) (f := f)
  | cons i ω ih =>
    simp only [wordRep, List.map_cons, List.prod_cons, Units.val_mul]
    exact (BaseChange.weylElt_one i).mul ih

theorem wordRep_mem_adjointGroup (K : Type) [Field K] (ω : List (Fin τ.rank)) :
    wordRep τ K ω ∈ adjointGroup τ K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem baseChangeGL_wordRep {K L : Type} [Field K] [Field L] (σ : K →+* L)
    (ω : List (Fin τ.rank)) : baseChangeGL σ (wordRep τ K ω) = wordRep τ L ω := by
  induction ω with
  | nil => simp [wordRep]
  | cons i ω ih =>
    simp only [wordRep, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih, LieType.Chevalley.weylElt_eq_xUnit_mul, LieType.Chevalley.weylElt_eq_xUnit_mul,
      map_mul, map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit]
    simp


@[expose] def d4TrialityWord : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 1, 2, 3, 4, 5]

@[expose] def d4Rho : Fin Tag.D4.rank → Fin Tag.D4.rank := ![1, 3, 2, 0]

@[expose] def d4RhoInv : Fin Tag.D4.rank → Fin Tag.D4.rank := ![3, 0, 2, 1]

theorem d4Rho_d4RhoInv : ∀ k, d4Rho (d4RhoInv k) = k := by decide

theorem d4RhoInv_d4Rho : ∀ k, d4RhoInv (d4Rho k) = k := by decide

theorem d4Rho_d4Rho : ∀ k, d4Rho (d4Rho k) = d4RhoInv k := by decide

theorem d4TrialityWord_check : ∀ k : Fin Tag.D4.rank,
    wordAct Tag.E6 d4TrialityWord (Pi.single (d4Idx k) 1) = Pi.single (d4Idx (d4Rho k)) 1 ∧
    wordAct Tag.E6 d4TrialityWord (-Pi.single (d4Idx k) 1) = -Pi.single (d4Idx (d4Rho k)) 1 ∧
    wordSign Tag.E6 d4TrialityWord (Pi.single (d4Idx k) 1) = 1 ∧
    wordSign Tag.E6 d4TrialityWord (-Pi.single (d4Idx k) 1) = 1 := by
  decide +kernel

theorem d4TrialityWord_cube_check : ∀ i : Fin Tag.E6.rank,
    wordAct Tag.E6 d4TrialityWord (wordAct Tag.E6 d4TrialityWord
      (wordAct Tag.E6 d4TrialityWord (Pi.single i 1))) = Pi.single i 1 := by
  decide +kernel

theorem d4TrialityWord_ne_check :
    wordAct Tag.E6 d4TrialityWord (Pi.single 1 1) ≠ Pi.single 1 1 := by
  decide +kernel

theorem d4TrialityWeyl_pow_three : (coxeterSystem Tag.E6).wordProd d4TrialityWord ^ 3 = 1 := by
  refine ext_single fun i => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, ← wordAct_eq_smul,
    ← wordAct_eq_smul, ← wordAct_eq_smul]
  exact d4TrialityWord_cube_check i

theorem d4TrialityWeyl_ne_one : (coxeterSystem Tag.E6).wordProd d4TrialityWord ≠ 1 := by
  intro h
  apply d4TrialityWord_ne_check
  rw [wordAct_eq_smul, h, one_smul]

variable {K : Type} [Field K]

variable (K) in
abbrev d4TrialityRep : ModGL Tag.E6 K := wordRep Tag.E6 K d4TrialityWord

theorem d4TrialityRep_conj_xUnit (k : Fin Tag.D4.rank) (c : K) :
    d4TrialityRep K * xUnit Tag.E6 K (d4Idx k) c * (d4TrialityRep K)⁻¹ =
      xUnit Tag.E6 K (d4Idx (d4Rho k)) c := by
  have h := wordRep_conj_pinnedX K d4TrialityWord (isRoot_single _ (d4Idx k)) c
  obtain ⟨h1, -, h3, -⟩ := d4TrialityWord_check k
  rw [h1, h3, Int.cast_one, one_mul, pinnedX_single, pinnedX_single] at h
  exact h

theorem d4TrialityRep_conj_yUnit (k : Fin Tag.D4.rank) (c : K) :
    d4TrialityRep K * yUnit Tag.E6 K (d4Idx k) c * (d4TrialityRep K)⁻¹ =
      yUnit Tag.E6 K (d4Idx (d4Rho k)) c := by
  have h := wordRep_conj_pinnedX K d4TrialityWord (isRoot_neg_single _ (d4Idx k)) c
  obtain ⟨-, h2, -, h4⟩ := d4TrialityWord_check k
  rw [h2, h4, Int.cast_one, one_mul, pinnedX_neg_single, pinnedX_neg_single] at h
  exact h

theorem d4TrialityRep_conj_rootSubgroup {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    (rootSubgroup Tag.E6 K α).map (MulAut.conj (d4TrialityRep K)).toMonoidHom =
      rootSubgroup Tag.E6 K ((coxeterSystem Tag.E6).wordProd d4TrialityWord • α) := by
  have hs := wordSign_eq_one_or d4TrialityWord hα
  have hss : ((wordSign Tag.E6 d4TrialityWord α : K) * wordSign Tag.E6 d4TrialityWord α) = 1 := by
    rcases hs with h | h <;> simp [h]
  ext g
  rw [Subgroup.mem_map, mem_rootSubgroup, ← wordAct_eq_smul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    exact ⟨_, (wordRep_conj_pinnedX K d4TrialityWord hα c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨pinnedX Tag.E6 K α ((wordSign Tag.E6 d4TrialityWord α : K) * c),
      mem_rootSubgroup.2 ⟨_, rfl⟩, ?_⟩
    change d4TrialityRep K * _ * (d4TrialityRep K)⁻¹ = _
    rw [wordRep_conj_pinnedX K d4TrialityWord hα, ← mul_assoc, hss, one_mul]

theorem map_conj_d4TrialityRep :
    (subsystemGroup Tag.E6 K d4Support).map (MulAut.conj (d4TrialityRep K)).toMonoidHom =
      subsystemGroup Tag.E6 K d4Support := by
  rw [subsystemGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨i, hi, c, rfl | rfl⟩, rfl⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      exact ⟨d4Idx (d4Rho k), d4Idx_mem _, c, Or.inl (d4TrialityRep_conj_xUnit k c)⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      exact ⟨d4Idx (d4Rho k), d4Idx_mem _, c, Or.inr (d4TrialityRep_conj_yUnit k c)⟩
  · rintro ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      refine ⟨xUnit Tag.E6 K (d4Idx (d4RhoInv k)) c, ⟨_, d4Idx_mem _, c, Or.inl rfl⟩, ?_⟩
      change d4TrialityRep K * _ * (d4TrialityRep K)⁻¹ = _
      rw [d4TrialityRep_conj_xUnit, d4Rho_d4RhoInv]
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      refine ⟨yUnit Tag.E6 K (d4Idx (d4RhoInv k)) c, ⟨_, d4Idx_mem _, c, Or.inr rfl⟩, ?_⟩
      change d4TrialityRep K * _ * (d4TrialityRep K)⁻¹ = _
      rw [d4TrialityRep_conj_yUnit, d4Rho_d4RhoInv]

variable (K) in
@[expose] def d4Triality : subsystemGroup Tag.E6 K d4Support ≃* subsystemGroup Tag.E6 K d4Support :=
  ((MulAut.conj (d4TrialityRep K)).subgroupMap (subsystemGroup Tag.E6 K d4Support)).trans
    (MulEquiv.subgroupCongr map_conj_d4TrialityRep)

theorem coe_d4Triality (g : subsystemGroup Tag.E6 K d4Support) :
    ((d4Triality K g : subsystemGroup Tag.E6 K d4Support) : ModGL Tag.E6 K) =
      d4TrialityRep K * g * (d4TrialityRep K)⁻¹ :=
  rfl

theorem d4Triality_xUnit (k : Fin Tag.D4.rank) (c : K) :
    d4Triality K ⟨xUnit Tag.E6 K (d4Idx k) c, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      ⟨xUnit Tag.E6 K (d4Idx (d4Rho k)) c, xUnit_mem_subsystemGroup (d4Idx_mem _) c⟩ :=
  Subtype.ext (d4TrialityRep_conj_xUnit k c)

theorem d4Triality_yUnit (k : Fin Tag.D4.rank) (c : K) :
    d4Triality K ⟨yUnit Tag.E6 K (d4Idx k) c, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      ⟨yUnit Tag.E6 K (d4Idx (d4Rho k)) c, yUnit_mem_subsystemGroup (d4Idx_mem _) c⟩ :=
  Subtype.ext (d4TrialityRep_conj_yUnit k c)

theorem d4Q_hom_ext {M : Type*} [Group M] {f g : subsystemGroup Tag.E6 K d4Support →* M}
    (hx : ∀ (k : Fin Tag.D4.rank) (c : K),
      f ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
        g ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩)
    (hy : ∀ (k : Fin Tag.D4.rank) (c : K),
      f ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
        g ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense closure_d4Q_generators ?_
  rintro ⟨x, hx'⟩ ⟨i, hi, c, h | h⟩
  · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
    have e : (⟨x, hx'⟩ : subsystemGroup Tag.E6 K d4Support) =
        ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ := Subtype.ext h
    rw [e]
    exact hx k c
  · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
    have e : (⟨x, hx'⟩ : subsystemGroup Tag.E6 K d4Support) =
        ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ := Subtype.ext h
    rw [e]
    exact hy k c

theorem eq_d4Triality {φ : subsystemGroup Tag.E6 K d4Support ≃* subsystemGroup Tag.E6 K d4Support}
    (hx : ∀ (k : Fin Tag.D4.rank) (c : K),
      φ ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
        ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem (d4Rho k)) c⟩)
    (hy : ∀ (k : Fin Tag.D4.rank) (c : K),
      φ ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
        ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem (d4Rho k)) c⟩) : φ = d4Triality K := by
  have h : φ.toMonoidHom = (d4Triality K).toMonoidHom :=
    d4Q_hom_ext (fun k c => (hx k c).trans (d4Triality_xUnit k c).symm)
      (fun k c => (hy k c).trans (d4Triality_yUnit k c).symm)
  exact MulEquiv.ext fun g => DFunLike.congr_fun h g

theorem d4Triality_cube (g : subsystemGroup Tag.E6 K d4Support) :
    d4Triality K (d4Triality K (d4Triality K g)) = g := by
  have h : ((d4Triality K).toMonoidHom.comp ((d4Triality K).toMonoidHom.comp
      (d4Triality K).toMonoidHom)) = MonoidHom.id _ := by
    refine d4Q_hom_ext (fun k c => ?_) (fun k c => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, d4Triality_xUnit,
        MonoidHom.id_apply, d4Rho_d4Rho, d4Rho_d4RhoInv]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, d4Triality_yUnit,
        MonoidHom.id_apply, d4Rho_d4Rho, d4Rho_d4RhoInv]
  exact DFunLike.congr_fun h g

theorem xOp_apply_hVec (i j : Fin Tag.E6.rank) (c : K) :
    xOp Tag.E6 K i c (hVec Tag.E6 K j) =
      hVec Tag.E6 K j + (((Tag.E6.cartan j i).natAbs : K) * c) •
        rootVec Tag.E6 K (Pi.single i 1) := by
  simp only [xOp, hVec, Finsupp.linearCombination_single, one_smul]

theorem d4Triality_ne_one : d4Triality K ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : subsystemGroup Tag.E6 K d4Support => (((g : ModGL Tag.E6 K) :
    Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K 3)) (Sum.inr ⟨Pi.single 1 1,
      isRoot_single _ 1⟩)) (congrArg (fun φ => φ ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem 0) 1⟩) h)
  simp only [d4Triality_xUnit, MulAut.one_apply] at h1
  change (xOp Tag.E6 K (d4Idx (d4Rho 0)) 1 (hVec Tag.E6 K 3)) _ =
    (xOp Tag.E6 K (d4Idx 0) 1 (hVec Tag.E6 K 3)) _ at h1
  rw [xOp_apply_hVec, xOp_apply_hVec] at h1
  have e1 : d4Idx (d4Rho 0) = 2 := rfl
  have e0 : d4Idx 0 = 1 := rfl
  rw [e1, e0, rootVec_eq_single_of_isRoot (isRoot_single _ _),
    rootVec_eq_single_of_isRoot (isRoot_single _ _)] at h1
  have hc1 : (Tag.E6.cartan 3 1).natAbs = 1 := by decide
  have hc2 : (Tag.E6.cartan 3 2).natAbs = 1 := by decide
  have hne : (Sum.inr ⟨Pi.single 2 1, isRoot_single _ 2⟩ : Label Tag.E6) ≠
      Sum.inr ⟨Pi.single 1 1, isRoot_single _ 1⟩ := by decide
  simp only [Finsupp.add_apply, Finsupp.smul_apply, hVec, Finsupp.single_apply, hc1, hc2,
    reduceCtorEq, ite_false, ite_eq_right hne, ite_true, smul_eq_mul, mul_zero, mul_one, add_zero,
    zero_add, Nat.cast_one] at h1
  exact zero_ne_one h1


theorem d4TrialityRep_conj_torusElt (k : Fin Tag.D4.rank) (t : Kˣ) :
    d4TrialityRep K * torusElt Tag.E6 K (d4Idx k) t * (d4TrialityRep K)⁻¹ =
      torusElt Tag.E6 K (d4Idx (d4Rho k)) t := by
  have h : ∀ g : ModGL Tag.E6 K, d4TrialityRep K * g * (d4TrialityRep K)⁻¹ =
      MulAut.conj (d4TrialityRep K) g := fun g => rfl
  rw [h, torusElt, torusElt, LieType.Chevalley.weylElt_eq_xUnit_mul,
    LieType.Chevalley.weylElt_eq_xUnit_mul, LieType.Chevalley.weylElt_eq_xUnit_mul,
    LieType.Chevalley.weylElt_eq_xUnit_mul]
  simp only [map_mul]
  simp only [← h, d4TrialityRep_conj_xUnit, d4TrialityRep_conj_yUnit]

@[expose] def d4Rho4 : Fin 4 → Fin 4 := ![1, 3, 2, 0]

@[expose] def d4RhoInv4 : Fin 4 → Fin 4 := ![3, 0, 2, 1]

theorem d4Rho4_d4RhoInv4 : ∀ k, d4Rho4 (d4RhoInv4 k) = k := by decide

theorem d4RhoInv4_d4Rho4 : ∀ k, d4RhoInv4 (d4Rho4 k) = k := by decide

@[expose] def d4RhoPrecomp : (Fin 4 → Kˣ) →* (Fin 4 → Kˣ) where
  toFun t k := t (d4RhoInv4 k)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem d4TrialityRep_conj_d4TorusHom (t : Fin 4 → Kˣ) :
    d4TrialityRep K * d4TorusHom K t * (d4TrialityRep K)⁻¹ =
      d4TorusHom K (fun k => t (d4RhoInv4 k)) := by
  have h : (MulAut.conj (d4TrialityRep K)).toMonoidHom.comp (d4TorusHom K) =
      (d4TorusHom K).comp d4RhoPrecomp := by
    refine MonoidHom.pi_ext fun k s => ?_
    have e : (d4RhoPrecomp (Pi.mulSingle k s) : Fin 4 → Kˣ) = Pi.mulSingle (d4Rho4 k) s := by
      funext l
      change (Pi.mulSingle k s : Fin 4 → Kˣ) (d4RhoInv4 l) =
        (Pi.mulSingle (d4Rho4 k) s : Fin 4 → Kˣ) l
      by_cases hl : l = d4Rho4 k
      · rw [hl, d4RhoInv4_d4Rho4, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hl, Pi.mulSingle_eq_of_ne (fun h => hl (by
          rw [← h, d4Rho4_d4RhoInv4]))]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, d4TorusHom_mulSingle (d4Rho4 k) s,
      d4TorusHom_mulSingle k s, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact d4TrialityRep_conj_torusElt k s
  exact DFunLike.congr_fun h t

theorem coe_d4Triality_d4TorusHom_sign (a b d : Kˣ) :
    ((d4Triality K ⟨_, d4TorusHom_mem_d4Q ![a, b, 1, d]⟩ : subsystemGroup Tag.E6 K d4Support) :
      ModGL Tag.E6 K) = d4TorusHom K ![d, a, 1, b] := by
  rw [coe_d4Triality, d4TrialityRep_conj_d4TorusHom]
  congr 1
  funext k
  fin_cases k <;> rfl

@[expose] def d4KernelShiftAdd (x : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (x.1 + x.2, x.1)

@[expose] def d4KernelShift (p : Multiplicative (ZMod 2 × ZMod 2)) :
    Multiplicative (ZMod 2 × ZMod 2) :=
  Multiplicative.ofAdd (d4KernelShiftAdd (Multiplicative.toAdd p))

theorem d4Triality_d4KernelHom (p : Multiplicative (ZMod 2 × ZMod 2)) :
    d4Triality K (d4KernelHom K p : subsystemGroup Tag.E6 K d4Support) =
      (d4KernelHom K (d4KernelShift p) : subsystemGroup Tag.E6 K d4Support) := by
  apply Subtype.ext
  simp only [d4KernelHom, MonoidHom.coe_mk, OneHom.coe_mk, d4KernelShift, d4KernelShiftAdd,
    toAdd_ofAdd]
  rw [coe_d4Triality_d4TorusHom_sign, zmodTwoSign_add, mul_right_comm, ← sq, zmodTwoSign_sq,
    one_mul]

theorem d4KernelShiftAdd_check : ∀ x y : ZMod 2 × ZMod 2, x ≠ 0 → y ≠ 0 →
    (y = x ∨ y = d4KernelShiftAdd x ∨ y = d4KernelShiftAdd (d4KernelShiftAdd x)) ∧
      d4KernelShiftAdd x ≠ x ∧ d4KernelShiftAdd (d4KernelShiftAdd x) ≠ x ∧
        d4KernelShiftAdd (d4KernelShiftAdd x) ≠ d4KernelShiftAdd x := by
  decide

theorem d4KernelShift_check (p p' : Multiplicative (ZMod 2 × ZMod 2)) (hp : p ≠ 1)
    (hp' : p' ≠ 1) :
    (p' = p ∨ p' = d4KernelShift p ∨ p' = d4KernelShift (d4KernelShift p)) ∧
      d4KernelShift p ≠ p ∧ d4KernelShift (d4KernelShift p) ≠ p ∧
        d4KernelShift (d4KernelShift p) ≠ d4KernelShift p := by
  have h := d4KernelShiftAdd_check (Multiplicative.toAdd p) (Multiplicative.toAdd p')
    (fun h => hp (by rw [← ofAdd_toAdd p, h, ofAdd_zero])) (fun h => hp' (by
      rw [← ofAdd_toAdd p', h, ofAdd_zero]))
  simp only [d4KernelShift, toAdd_ofAdd, ne_eq]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun e => h2 (by rw [← toAdd_ofAdd (d4KernelShiftAdd _), e]),
    fun e => h3 (by rw [← toAdd_ofAdd (d4KernelShiftAdd _), e]),
    fun e => h4 (Multiplicative.ofAdd.injective e)⟩
  rcases h1 with e | e | e
  · exact Or.inl (Multiplicative.toAdd.injective e)
  · exact Or.inr (Or.inl (Multiplicative.toAdd.injective e))
  · exact Or.inr (Or.inr (Multiplicative.toAdd.injective e))

theorem d4Res_d4Triality_eq_one {g : subsystemGroup Tag.E6 K d4Support} (hg : d4Res K g = 1) :
    d4Res K (d4Triality K g) = 1 := by
  obtain ⟨a, b, d, ha, hb, hd, habd, he⟩ := (d4Res_eq_one_iff_mem_d4KernelSet g).1 hg
  rw [← d4TorusHom_sign] at he
  have e : g = ⟨_, d4TorusHom_mem_d4Q ![a, b, 1, d]⟩ := Subtype.ext he
  rw [d4Res_eq_one_iff_mem_d4KernelSet, e, coe_d4Triality_d4TorusHom_sign]
  exact ⟨d, a, b, hd, ha, hb, (mul_rotate d a b).trans habd, (d4TorusHom_sign d a b)⟩

theorem d4Triality_cycles_kernel (h2 : ringChar K ≠ 2) {z z' : subsystemGroup Tag.E6 K d4Support}
    (hz : d4Res K z = 1) (hz' : d4Res K z' = 1) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) :
    (z' = z ∨ z' = d4Triality K z ∨ z' = d4Triality K (d4Triality K z)) ∧
      d4Triality K z ≠ z ∧ d4Triality K (d4Triality K z) ≠ z ∧
        d4Triality K (d4Triality K z) ≠ d4Triality K z := by
  obtain ⟨p, hp⟩ := (d4KernelHom_bijective h2).2 ⟨z, hz⟩
  obtain ⟨p', hp'⟩ := (d4KernelHom_bijective h2).2 ⟨z', hz'⟩
  have hz2 : z = (d4KernelHom K p : subsystemGroup Tag.E6 K d4Support) := by rw [hp]
  have hz2' : z' = (d4KernelHom K p' : subsystemGroup Tag.E6 K d4Support) := by rw [hp']
  have hp1 : p ≠ 1 := fun h => hz1 (by rw [hz2, h, map_one]; rfl)
  have hp1' : p' ≠ 1 := fun h => hz1' (by rw [hz2', h, map_one]; rfl)
  have hinj : ∀ q q', (d4KernelHom K q : subsystemGroup Tag.E6 K d4Support) =
      d4KernelHom K q' → q = q' := fun q q' h =>
    (d4KernelHom_bijective h2).1 (Subtype.ext h)
  obtain ⟨hor, hne1, hne2, hne3⟩ := d4KernelShift_check p p' hp1 hp1'
  rw [hz2, hz2']
  simp only [d4Triality_d4KernelHom]
  refine ⟨?_, fun h => hne1 (hinj _ _ h), fun h => hne2 (hinj _ _ h),
    fun h => hne3 (hinj _ _ h)⟩
  rcases hor with h | h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end CFSG.RankThree.Chevalley
