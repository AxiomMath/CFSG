module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYPsi
public import CFSG.LieType.Chevalley.C2E6D4Faithful

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open scoped Pointwise

section TorusChar

variable {K : Type} [Field K]

@[expose] noncomputable def d4TorusChar (c : Fin 4 → Kˣ) (β : Fin Tag.E6.rank → ℤ) : Kˣ :=
  ∏ k, c k ^ rootWeight (jD k) β

@[expose] def IsD4TorusParam (t : ModGL Tag.E6 K) (c : Fin 4 → Kˣ) : Prop :=
  (∀ i, (t : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K i) = hVec Tag.E6 K i) ∧
    ∀ β, IsRoot Tag.E6 β → (t : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
      ((d4TorusChar c β : Kˣ) : K) • rootVec Tag.E6 K β

theorem d4TorusChar_mul (c c' : Fin 4 → Kˣ) (β : Fin Tag.E6.rank → ℤ) :
    d4TorusChar (c * c') β = d4TorusChar c β * d4TorusChar c' β := by
  simp only [d4TorusChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem d4TorusChar_inv (c : Fin 4 → Kˣ) (β : Fin Tag.E6.rank → ℤ) :
    d4TorusChar c⁻¹ β = (d4TorusChar c β)⁻¹ := by
  simp only [d4TorusChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem d4TorusChar_one (β : Fin Tag.E6.rank → ℤ) : d4TorusChar (1 : Fin 4 → Kˣ) β = 1 := by
  simp [d4TorusChar]

theorem d4TorusChar_mulSingle (k : Fin 4) (s : Kˣ) (β : Fin Tag.E6.rank → ℤ) :
    d4TorusChar (Pi.mulSingle k s) β = s ^ rootWeight (jD k) β := by
  rw [d4TorusChar, Finset.prod_eq_single k]
  · rw [Pi.mulSingle_eq_same]
  · intro k' _ hk'
    rw [Pi.mulSingle_eq_of_ne hk', one_zpow]
  · intro h
    exact absurd (Finset.mem_univ k) h

end TorusChar

section Torus

variable {K : Type} [Field K]

theorem exists_d4TorusParam {t : ModGL Tag.E6 K} (ht : t ∈ subsystemTorus Tag.E6 K setD) :
    ∃ c, IsD4TorusParam t c := by
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, s, rfl⟩ := hg
    obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    refine ⟨Pi.mulSingle k s, fun i => torusElt_hVec (jD k) i s, fun β hβ => ?_⟩
    rw [torusElt_rootVec (jD k) s hβ, d4TorusChar_mulSingle]
    rfl
  | one => exact ⟨1, fun i => rfl, fun β _ => by simp [d4TorusChar_one]⟩
  | mul g h _ _ hg hh =>
    obtain ⟨c, hc1, hc2⟩ := hg
    obtain ⟨c', hc1', hc2'⟩ := hh
    refine ⟨c * c', fun i => ?_, fun β hβ => ?_⟩
    · rw [Units.val_mul, Module.End.mul_apply, hc1', hc1]
    · rw [Units.val_mul, Module.End.mul_apply, hc2' β hβ, map_smul, hc2 β hβ, smul_smul,
        d4TorusChar_mul, Units.val_mul, mul_comm]
  | inv g _ hg =>
    obtain ⟨c, hc1, hc2⟩ := hg
    refine ⟨c⁻¹, fun i => ?_, fun β hβ => ?_⟩
    · have h := hc1 i
      calc ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K i)
          = ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
              ((g : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K i)) := by rw [h]
        _ = hVec Tag.E6 K i := by
          rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Module.End.one_apply]
    · have h := hc2 β hβ
      have h' : ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
          (((d4TorusChar c β : Kˣ) : K) • rootVec Tag.E6 K β) = rootVec Tag.E6 K β := by
        rw [← h, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]
      rw [map_smul] at h'
      rw [d4TorusChar_inv]
      calc ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β)
          = (((d4TorusChar c β)⁻¹ : Kˣ) : K) • (((d4TorusChar c β : Kˣ) : K) •
              ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
                (rootVec Tag.E6 K β)) := by
            rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
        _ = _ := by rw [h']

theorem end_eq_one_of_fix {f : Module.End K (RootModule Tag.E6 K)}
    (hh : ∀ i, f (hVec Tag.E6 K i) = hVec Tag.E6 K i)
    (hv : ∀ β, IsRoot Tag.E6 β → f (rootVec Tag.E6 K β) = rootVec Tag.E6 K β) : f = 1 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  rcases b with i | ⟨β, hβ⟩
  · exact hh i
  · have := hv β hβ
    rw [C2E6Std.rootVec_eq_single hβ] at this
    exact this

@[expose] noncomputable def d4NatChar (c : Fin 4 → Kˣ) : Fin 4 → Kˣ :=
  fun i => ∏ k, c k ^ natWeight (.inl i) k

theorem natWeight_inr (i k : Fin 4) : natWeight (.inr i) k = -natWeight (.inl i) k := rfl

theorem elim_d4NatChar (c : Fin 4 → Kˣ) (s : Fin 4 ⊕ Fin 4) :
    (Sum.elim (d4NatChar c) (d4NatChar c)⁻¹ s : Kˣ) = ∏ k, c k ^ natWeight s k := by
  rcases s with i | i
  · rfl
  · change (d4NatChar c i)⁻¹ = _
    rw [d4NatChar, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [natWeight_inr, zpow_neg]

theorem d4TorusElt_single (a : Fin 4 → Kˣ) (s : Fin 4 ⊕ Fin 4) :
    torusElt 4 K a (Pi.single s 1) = ((Sum.elim a a⁻¹ s : Kˣ) : K) • Pi.single s 1 := by
  funext s'
  rw [OrthogonalSplit.torusElt_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : s' = s
  · subst h
    rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem d4Psi_of_isD4TorusParam {t : d4Levi K} {c : Fin 4 → Kˣ}
    (hc : IsD4TorusParam (t : ModGL Tag.E6 K) c) : d4Psi K t = torusElt 4 K (d4NatChar c) := by
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun K (Fin 4 ⊕ Fin 4)).ext fun s => ?_)
  obtain ⟨j, rfl⟩ := exists_natD_eq s
  rw [Pi.basisFun_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← d4Phi_vec j, d4Psi_phi,
    d4Phi_vec, d4TorusElt_single, elim_d4NatChar]
  have h : (⟨((t : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (d4Vec K j),
      mem_d4Module_of_mem_subsystemGroup t.2 _ (d4Vec_mem j)⟩ : d4Module K) =
      ((d4TorusChar c (rootD j) : Kˣ) : K) • ⟨d4Vec K j, d4Vec_mem j⟩ :=
    Subtype.ext (by rw [SetLike.val_smul]; exact hc.2 _ (isRoot_rootD j))
  rw [h, map_smul, d4Phi_vec, d4TorusChar]
  simp only [weight_rootD]

theorem d4_eq_one_of_mul_self_eq_one [CharP K 2] {x : K} (h : x * x = 1) : x = 1 := by
  have h2 : (x - 1) * (x - 1) = 0 := by
    have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination h - (x - 1) * h2'
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h2)

theorem natWeight_inl_check : ∀ i k : Fin 4, natWeight (.inl i) k =
    (![![1, 0, 0, 0], ![-1, 1, 0, 0], ![0, -1, 1, 1], ![0, 0, -1, 1]] : Fin 4 → Fin 4 → ℤ) i k := by
  decide

theorem eq_one_of_d4NatChar_eq_one [CharP K 2] {c : Fin 4 → Kˣ} (h : d4NatChar c = 1) :
    c = 1 := by
  have h' : ∀ i, ∏ k, c k ^ natWeight (.inl i) k = 1 := fun i => congrFun h i
  have e0 := h' 0
  have e1 := h' 1
  have e2 := h' 2
  have e3 := h' 3
  simp only [Fin.prod_univ_four, natWeight_inl_check] at e0 e1 e2 e3
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, zpow_one, zpow_zero, mul_one, one_mul, zpow_neg,
    Matrix.tail_cons] at e0 e1 e2 e3
  have hc0 : c 0 = 1 := e0
  have hc1 : c 1 = 1 := by rw [hc0, inv_one, one_mul] at e1; exact e1
  have hc32 : c 3 = c 2 := by
    have := e3
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hc22 : c 2 * c 2 = 1 := by
    rw [hc1, inv_one, one_mul, hc32] at e2
    exact e2
  have hc2 : c 2 = 1 := Units.ext (d4_eq_one_of_mul_self_eq_one
    (by rw [← Units.val_mul, hc22, Units.val_one]))
  funext k
  fin_cases k
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc32.trans hc2

theorem eq_one_of_mem_subsystemTorus_of_d4Psi_eq_one [CharP K 2] {t : d4Levi K}
    (ht : (t : ModGL Tag.E6 K) ∈ subsystemTorus Tag.E6 K setD) (h : d4Psi K t = 1) : t = 1 := by
  obtain ⟨c, hc⟩ := exists_d4TorusParam ht
  rw [d4Psi_of_isD4TorusParam hc, ← map_one (torusElt 4 K)] at h
  have hc1 : c = 1 := eq_one_of_d4NatChar_eq_one (torusElt_injective h)
  subst hc1
  refine Subtype.ext (Units.ext (end_eq_one_of_fix hc.1 fun β hβ => ?_))
  rw [hc.2 β hβ, d4TorusChar_one, Units.val_one, one_smul]

theorem d4Psi_mem_range_torusElt {t : d4Levi K}
    (ht : (t : ModGL Tag.E6 K) ∈ subsystemTorus Tag.E6 K setD) :
    d4Psi K t ∈ (torusElt 4 K).range := by
  obtain ⟨c, hc⟩ := exists_d4TorusParam ht
  exact ⟨_, (d4Psi_of_isD4TorusParam hc).symm⟩

end Torus

section Weyl

variable {K : Type} [Field K]

theorem d4_list_prod_weylElt_rootVec (ω : List (Fin Tag.E6.rank)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : ∃ ε : K, ε ≠ 0 ∧
      (((ω.map fun i => weylElt Tag.E6 K i 1).prod : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
      ε • rootVec Tag.E6 K ((coxeterSystem Tag.E6).wordProd ω • β) := by
  induction ω with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨ε * ((-1) ^ stringDown Tag.E6 i ((coxeterSystem Tag.E6).wordProd ω • β) *
      (((1 : Kˣ) ^ (-∑ j, Tag.E6.cartan i j * ((coxeterSystem Tag.E6).wordProd ω • β) j) : Kˣ) :
        K)), mul_ne_zero hε (by simp), ?_⟩
    have e : (coxeterSystem Tag.E6).wordProd (i :: ω) • β =
        reflect Tag.E6 i ((coxeterSystem Tag.E6).wordProd ω • β) := by
      rw [CoxeterSystem.wordProd_cons, mul_smul]
      exact simple_smul i _
    rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
      weylElt_rootVec i 1 (IsRoot.smul hβ _), smul_smul]

theorem d4_canonicalRep_rootVec (w : WeylGroup Tag.E6) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : ∃ ε : K, ε ≠ 0 ∧
      (canonicalRep (coxeterSystem Tag.E6) K w : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K β) = ε • rootVec Tag.E6 K (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact d4_list_prod_weylElt_rootVec ω hβ

end Weyl

section Unipotent


variable {K : Type} [Field K]

theorem card_d4Unipotent [Finite K] :
    Nat.card (parabolicLeviUnipotent Tag.E6 K setD) = Nat.card K ^ 12 := by
  have hS : ∀ α ∈ parabolicPosRoots Tag.E6 setD, IsRoot Tag.E6 α ∧ 0 < height α :=
    fun _ hα => hα.2
  have hcl : ∀ α ∈ parabolicPosRoots Tag.E6 setD, ∀ β ∈ parabolicPosRoots Tag.E6 setD,
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E6 (a • α + b • β) →
        a • α + b • β ∈ parabolicPosRoots Tag.E6 setD := by
    intro α hα β hβ a b ha hb hr
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, hα.1.2 i hi, hβ.1.2 i hi, smul_zero, add_zero]
    · have e : height (a • α + b • β) = a * height α + b * height β := by
        simp only [height, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
      have h1 : (0 : ℤ) < a * height α := mul_pos (by exact_mod_cast ha) hα.2.2
      have h2 : (0 : ℤ) < b * height β := mul_pos (by exact_mod_cast hb) hβ.2.2
      rw [e]
      linarith
  have hbij := (positive_root_collection Tag.E6 K).1 _ hS hcl posD posD_injective range_posD
  calc Nat.card (parabolicLeviUnipotent Tag.E6 K setD) =
        Nat.card (Set.univ : Set (Fin 12 → K)) := (Nat.card_congr hbij.equiv).symm
    _ = Nat.card K ^ 12 := by rw [Nat.card_univ, Nat.card_fun, Nat.card_fin]

theorem d4Unipotent_le_d4Levi : parabolicLeviUnipotent Tag.E6 K setD ≤ d4Levi K :=
  parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setD)

theorem xUnit_mem_d4Unipotent (k : Fin 4) (c : K) :
    xUnit Tag.E6 K (jD k) c ∈ parabolicLeviUnipotent Tag.E6 K setD := by
  rw [← pinnedX_single]
  refine (le_iSup₂_of_le (Pi.single (jD k) 1) ?_ le_rfl :
    rootSubgroup Tag.E6 K (Pi.single (jD k) 1) ≤ parabolicLeviUnipotent Tag.E6 K setD)
      (Subgroup.subset_closure ⟨c, rfl⟩)
  exact mem_parabolicPosRoots_of (single_mem_parabolicRoots (d4_jD_mem_setD k))
    (by rw [height, Finset.sum_pi_single']; simp)

@[expose] noncomputable def d4PsiOnto (H : Subgroup (d4Levi K)) : H → H.map (d4Psi K) :=
  fun x => ⟨d4Psi K x, Subgroup.mem_map_of_mem (d4Psi K) x.2⟩

theorem d4PsiOnto_surjective (H : Subgroup (d4Levi K)) : Function.Surjective (d4PsiOnto H) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem card_d4Unipotent_subgroupOf [Finite K] :
    Nat.card ((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)) = Nat.card K ^ 12 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d4Unipotent_le_d4Levi).toEquiv,
    card_d4Unipotent]

variable [CharP K 2]

theorem unipotent_le_map_d4Psi :
    unipotent 4 K ≤ ((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)).map (d4Psi K) :=
  d4Unipotent_le_of fun k c =>
    ⟨⟨xUnit Tag.E6 K (jD k) c, xUnit_mem_d4Levi k c⟩, xUnit_mem_d4Unipotent k c,
      d4Psi_xUnit k c⟩

theorem map_d4Psi_unipotent [Finite K] :
    ((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)).map (d4Psi K) =
      unipotent 4 K := by
  have hfinH : Finite ((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)) :=
    Nat.finite_of_card_ne_zero (by rw [card_d4Unipotent_subgroupOf]; exact pow_ne_zero _ Nat.card_pos.ne')
  have hfin : Finite (((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)).map
      (d4Psi K)) := Finite.of_surjective _ (d4PsiOnto_surjective _)
  have hcard : Nat.card (((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)).map
      (d4Psi K)) ≤ Nat.card K ^ 12 := by
    rw [← card_d4Unipotent_subgroupOf]
    exact Nat.card_le_card_of_surjective _ (d4PsiOnto_surjective _)
  have hU : Nat.card (unipotent 4 K) = Nat.card K ^ 12 := by
    rw [unipotent_eq_posUnip, card_posUnip]
  exact (Subgroup.eq_of_le_of_card_ge unipotent_le_map_d4Psi (hcard.trans hU.ge)).symm

theorem d4Psi_injOn_unipotent [Finite K] :
    Set.InjOn (d4Psi K) ((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)) := by
  have hfinH : Finite ((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K)) :=
    Nat.finite_of_card_ne_zero (by rw [card_d4Unipotent_subgroupOf]; exact pow_ne_zero _ Nat.card_pos.ne')
  have hbij := (d4PsiOnto_surjective ((parabolicLeviUnipotent Tag.E6 K setD).subgroupOf
    (d4Levi K))).bijective_of_nat_card_le (by
      rw [map_d4Psi_unipotent, unipotent_eq_posUnip, card_posUnip, card_d4Unipotent_subgroupOf])
  intro x hx y hy hxy
  have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
  exact congrArg Subtype.val this

end Unipotent

section Injective


variable {K : Type} [Field K]

theorem d4_borel_apply_vec_eq_zero {c : ModGL Tag.E6 K} (hc : c ∈ borelGroup Tag.E6 K)
    {j j' : Fin 8} (h : (labD j).Precedes (labD j')) :
    (c : Module.End K (RootModule Tag.E6 K)) (d4Vec K j) (labD j') = 0 := by
  have := (triangular_borel_structure.{0, 0} Tag.E6 K).2.2.2.2.2.2.2.2.2.1 c hc (labD j') (labD j) h
  rwa [d4Vec, C2E6Std.rootVec_eq_single (isRoot_rootD j)]

theorem d4_eq_one_of_torusElt_mem_unipotent {a : Fin 4 → Kˣ} (h : torusElt 4 K a ∈ unipotent 4 K) :
    a = 1 := by
  rw [unipotent_eq_posUnip] at h
  have h1 := (mem_posUnip.mp h).2
  funext i
  apply Units.ext
  have := h1 i
  rw [toMatrix'_torusElt, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq] at this
  exact this

theorem d4Psi_injective [Finite K] [CharP K 2] : Function.Injective (d4Psi K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix := (d4Psi_eq_one_iff g).mp hg
  have hgS : (g : ModGL Tag.E6 K) ∈ (subsystemGroup Tag.E6 K setD : Set (ModGL Tag.E6 K)) := g.2
  rw [(subsystem_root_group_bruhat Tag.E6 K setD).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup Tag.E6 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.E6 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup Tag.E6 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ d4Levi K := parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K)
    (A := setD) (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.E6) K w : Module.End K (RootModule Tag.E6 K))
      (d4Vec K j) =
        ((b⁻¹ * v⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (d4Vec K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.E6) K w = b⁻¹ * (g : ModGL Tag.E6 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (mem_d4Module_of_mem_subsystemGroup (inv_mem hvS) _ (d4Vec_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j', rootD j' = w • rootD j → ¬(labD j).Precedes (labD j') := by
    intro j j' hj' hp
    obtain ⟨ε, hε, hne⟩ := d4_canonicalRep_rootVec (K := K) w (isRoot_rootD j)
    have h0 := d4_borel_apply_vec_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hp
    rw [← hn j, d4Vec, hne, ← hj', C2E6Std.rootVec_eq_single (isRoot_rootD j'),
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_rootD hw (smul_rootD_eq_of_not_precedes hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.E6 K (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (subsystemTorus Tag.E6 K setD : Set (ModGL Tag.E6 K)) *
      (parabolicLeviUnipotent Tag.E6 K setD : Set (ModGL Tag.E6 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.E6) (K := K) (A := setD)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  set t' : d4Levi K := ⟨t, subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setD) ht⟩
  set u' : d4Levi K := ⟨u, d4Unipotent_le_d4Levi hu⟩
  have hgtu : g = t' * u' := Subtype.ext hgbv.symm
  have hψ : d4Psi K t' * d4Psi K u' = 1 := by rw [← map_mul, ← hgtu, hg]
  obtain ⟨a, ha⟩ := d4Psi_mem_range_torusElt (t := t') ht
  have hu0 : d4Psi K u' ∈ unipotent 4 K := by
    rw [← map_d4Psi_unipotent]
    exact Subgroup.mem_map_of_mem _ (show u' ∈ (parabolicLeviUnipotent Tag.E6 K setD).subgroupOf
      (d4Levi K) from hu)
  have hua : d4Psi K u' = torusElt 4 K a⁻¹ := by
    rw [map_inv, ha]
    exact eq_inv_of_mul_eq_one_right hψ
  have ha1 : a⁻¹ = 1 := d4_eq_one_of_torusElt_mem_unipotent (hua ▸ hu0)
  have hu1 : d4Psi K u' = 1 := by rw [hua, ha1, map_one]
  have hu'1 : u' = 1 := d4Psi_injOn_unipotent
    (show u' ∈ (parabolicLeviUnipotent Tag.E6 K setD).subgroupOf (d4Levi K) from hu)
    (one_mem _) (hu1.trans (map_one (d4Psi K)).symm)
  have ht1 : d4Psi K t' = 1 := by rw [hu1, mul_one] at hψ; exact hψ
  have ht'1 : t' = 1 := eq_one_of_mem_subsystemTorus_of_d4Psi_eq_one ht ht1
  rw [hgtu, hu'1, ht'1, mul_one]

end Injective

end CFSG.SeitzReduction.TwistedE6Pilot
