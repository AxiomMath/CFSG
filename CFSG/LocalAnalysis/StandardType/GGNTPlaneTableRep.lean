module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableVec
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableOrbits
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableClosureA
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableClosureB
public import CFSG.RankThree.E6.LargePrimeStabilizers

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open scoped Matrix

private noncomputable def n1d2_weylMat (w : WeylGroup Tag.E6) :
    Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.of fun i j => (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i

private theorem n1d2_weylMat_mulVec (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    n1d2_weylMat w *ᵥ v = w • v := by
  have h : w • v = ∑ j, v j • (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
    conv_lhs => rw [pi_eq_sum v]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm w (v j) _
  ext i
  rw [h]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    n1d2_weylMat, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private noncomputable def n1d2_weylMatHom : WeylGroup Tag.E6 →*
    Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ where
  toFun := n1d2_weylMat
  map_one' := by
    ext i j
    simp [n1d2_weylMat, Matrix.one_apply, Pi.single_apply]
  map_mul' w₁ w₂ := by
    refine (Matrix.ext_iff_mulVec).2 fun v => ?_
    rw [← Matrix.mulVec_mulVec v (n1d2_weylMat w₁) (n1d2_weylMat w₂)]
    rw [n1d2_weylMat_mulVec, n1d2_weylMat_mulVec, n1d2_weylMat_mulVec, mul_smul]

private theorem n1d2_weylMat_injective : Function.Injective n1d2_weylMat := by
  intro w w' h
  apply ext_single
  intro i
  have h' := congrArg (fun M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ =>
    M *ᵥ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) h
  simpa only [n1d2_weylMat_mulVec] using h'

private def n1d2_cartanForm (u v : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ i, ∑ j, u i * Tag.E6.cartan i j * v j

private theorem n1d2_cartan_symm (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan i j = Tag.E6.cartan j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem n1d2_cartanForm_single_left (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm (Pi.single i 1) v = ∑ j, Tag.E6.cartan i j * v j := by
  simp only [n1d2_cartanForm, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem n1d2_cartanForm_comm (u v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm u v = n1d2_cartanForm v u := by
  simp only [n1d2_cartanForm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [n1d2_cartan_symm j i]
  ring

private theorem n1d2_cartanForm_smul_left (a : ℤ) (u v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm (a • u) v = a * n1d2_cartanForm u v := by
  simp only [n1d2_cartanForm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem n1d2_cartanForm_sub_left (u₁ u₂ v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm (u₁ - u₂) v = n1d2_cartanForm u₁ v - n1d2_cartanForm u₂ v := by
  simp only [n1d2_cartanForm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem n1d2_cartanForm_sub_right (u v₁ v₂ : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm u (v₁ - v₂) = n1d2_cartanForm u v₁ - n1d2_cartanForm u v₂ := by
  simp only [n1d2_cartanForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem n1d2_cartanForm_smul_right (a : ℤ) (u v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm u (a • v) = a * n1d2_cartanForm u v := by
  simp only [n1d2_cartanForm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem n1d2_cartanForm_reflect (i : Fin Tag.E6.rank) (u v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm (reflect Tag.E6 i u) (reflect Tag.E6 i v) = n1d2_cartanForm u v := by
  set cu := ∑ j, Tag.E6.cartan i j * u j
  set cv := ∑ j, Tag.E6.cartan i j * v j
  have hu : reflect Tag.E6 i u = u - cu • Pi.single i 1 := rfl
  have hv : reflect Tag.E6 i v = v - cv • Pi.single i 1 := rfl
  have hev : n1d2_cartanForm (Pi.single i 1) v = cv := by
    rw [n1d2_cartanForm_single_left]
  have hue : n1d2_cartanForm u (Pi.single i 1) = cu := by
    rw [n1d2_cartanForm_comm, n1d2_cartanForm_single_left]
  have hee : n1d2_cartanForm (Pi.single i 1) (Pi.single i 1) = 2 := by
    rw [n1d2_cartanForm_single_left]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, Tag.cartan_self]
      ring
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hu, hv]
  simp only [n1d2_cartanForm_sub_left, n1d2_cartanForm_sub_right, n1d2_cartanForm_smul_left,
    n1d2_cartanForm_smul_right, hev, hue, hee]
  ring

private theorem n1d2_cartanForm_weylAction (w : WeylGroup Tag.E6) (u v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm (w • u) (w • v) = n1d2_cartanForm u v := by
  induction w using (coxeterSystem Tag.E6).simple_induction_left generalizing u v with
  | one => simp
  | mul_simple_left w i ih =>
    simp only [mul_smul, simple_smul]
    rw [n1d2_cartanForm_reflect]
    exact ih u v

private theorem n1d2_cartanForm_eq_dotProduct (u v : Fin Tag.E6.rank → ℤ) :
    n1d2_cartanForm u v = (Tag.E6.cartan.mulVec u) ⬝ᵥ v := by
  simp only [n1d2_cartanForm, dotProduct, Matrix.mulVec]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [n1d2_cartan_symm j i]
  ring

private theorem n1d2_reflMatRoot_mulVec (α v : Fin Tag.E6.rank → ℤ) :
    reflMatRoot α *ᵥ v = v - n1d2_cartanForm α v • α := by
  rw [reflMatRoot, Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  rw [n1d2_cartanForm_eq_dotProduct]
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem n1d2_weylMat_conj_simple (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank) :
    n1d2_weylMat (w * simple Tag.E6 i * w⁻¹) =
      reflMatRoot (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
  set α : Fin Tag.E6.rank → ℤ := w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
  refine (Matrix.ext_iff_mulVec).2 fun v => ?_
  rw [n1d2_weylMat_mulVec, n1d2_reflMatRoot_mulVec]
  have hsmul : (w * simple Tag.E6 i * w⁻¹) • v =
      w • (reflect Tag.E6 i (w⁻¹ • v)) := by
    rw [mul_smul, mul_smul, simple_smul]
  rw [hsmul]
  set cu := ∑ j, Tag.E6.cartan i j * (w⁻¹ • v) j
  have hu : reflect Tag.E6 i (w⁻¹ • v) = (w⁻¹ • v) - cu • Pi.single i 1 := rfl
  rw [hu, smul_sub, smul_inv_smul, smul_comm]
  have hcu : cu = n1d2_cartanForm α v := by
    rw [show cu = n1d2_cartanForm (Pi.single i 1) (w⁻¹ • v) from
      (n1d2_cartanForm_single_left i (w⁻¹ • v)).symm]
    rw [← n1d2_cartanForm_weylAction w (Pi.single i 1) (w⁻¹ • v)]
    rw [smul_inv_smul]
  rw [hcu]

private def n1d2_genSet (x : X3) : Set (WeylGroup Tag.E6) :=
  {r | ∃ (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank),
    w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ kerRoots x ∧ r = w * simple Tag.E6 i * w⁻¹}

private theorem n1d2_genSet_inv (x : X3) : (n1d2_genSet x)⁻¹ ⊆ n1d2_genSet x := by
  rintro r ⟨w, i, hmem, hr⟩
  refine ⟨w, i, hmem, ?_⟩
  rw [← inv_inv r, hr, mul_inv_rev, mul_inv_rev, inv_inv, CoxeterSystem.inv_simple, mul_assoc]

private theorem n1d2_genSet_closure_eq (x : X3) :
    (Subgroup.closure (n1d2_genSet x) : Set (WeylGroup Tag.E6)) =
      (Submonoid.closure (n1d2_genSet x) : Set (WeylGroup Tag.E6)) := by
  have h : n1d2_genSet x ∪ (n1d2_genSet x)⁻¹ = n1d2_genSet x :=
    Set.union_eq_left.2 (n1d2_genSet_inv x)
  rw [← Subgroup.coe_toSubmonoid (Subgroup.closure (n1d2_genSet x)),
    Subgroup.closure_toSubmonoid, h]

private theorem n1d2_weylMat_image_genSet (x : X3) :
    n1d2_weylMat '' n1d2_genSet x = kerReflSet x := by
  ext M
  constructor
  · rintro ⟨r, ⟨w, i, hmem, rfl⟩, rfl⟩
    exact ⟨w • (Pi.single i 1), hmem, n1d2_weylMat_conj_simple w i⟩
  · rintro ⟨α, ⟨hroot, hpair⟩, rfl⟩
    obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hroot
    exact ⟨w * simple Tag.E6 i * w⁻¹,
      ⟨w, i, ⟨isRoot_iff_exists_smul_single.2 ⟨w, i, rfl⟩, hpair⟩, rfl⟩,
      n1d2_weylMat_conj_simple w i⟩

private theorem n1d2_weylMat_image_kerReflVec (x : X3) :
    n1d2_weylMat '' (kerReflVec x : Set (WeylGroup Tag.E6)) =
      (Submonoid.closure (kerReflSet x) :
        Set (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)) := by
  calc n1d2_weylMat '' (kerReflVec x : Set _)
      = n1d2_weylMat '' (Subgroup.closure (n1d2_genSet x) : Set _) := by
          rw [show kerReflVec x = Subgroup.closure (n1d2_genSet x) from rfl]
    _ = n1d2_weylMat '' (Submonoid.closure (n1d2_genSet x) : Set _) := by
          rw [n1d2_genSet_closure_eq x]
    _ = (Submonoid.map n1d2_weylMatHom (Submonoid.closure (n1d2_genSet x)) : Set _) := by
          rw [Submonoid.coe_map]; rfl
    _ = (Submonoid.closure (n1d2_weylMatHom '' n1d2_genSet x) : Set _) := by
          rw [MonoidHom.map_mclosure]
    _ = (Submonoid.closure (kerReflSet x) : Set _) := by
          rw [show (⇑n1d2_weylMatHom '' n1d2_genSet x) = kerReflSet x from
            n1d2_weylMat_image_genSet x]

private theorem n1d2_card_kerReflVec (x : X3) :
    Nat.card (kerReflVec x) = Nat.card (Submonoid.closure (kerReflSet x)) := by
  have h := n1d2_weylMat_image_kerReflVec x
  calc Nat.card (kerReflVec x)
      = Nat.card (n1d2_weylMat '' (kerReflVec x : Set (WeylGroup Tag.E6))) :=
        (Nat.card_image_of_injective n1d2_weylMat_injective
          (kerReflVec x : Set (WeylGroup Tag.E6))).symm
    _ = Nat.card (Submonoid.closure (kerReflSet x)) :=
        congrArg (fun s : Set (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) =>
          Nat.card s) h

private theorem n1d2_wordProd_smul (l : List (Fin Tag.E6.rank)) (x : X3) :
    (coxeterSystem Tag.E6).wordProd l • x = applyWord l x := by
  induction l with
  | nil => simp [CoxeterSystem.wordProd, applyWord]
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, simple_smul_X3, ih]
    rfl

private theorem n1d2_orbit_eq (x : X3) :
    MulAction.orbit (WeylGroup Tag.E6) x =
      {y : X3 | ∃ l : List (Fin Tag.E6.rank), applyWord l x = y} := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨l, rfl⟩ := (coxeterSystem Tag.E6).wordProd_surjective w
    exact ⟨l, (n1d2_wordProd_smul l x).symm⟩
  · rintro ⟨l, rfl⟩
    exact ⟨(coxeterSystem Tag.E6).wordProd l, n1d2_wordProd_smul l x⟩

private theorem n1d2_card_stabVec
    (k : Fin 7) : Nat.card (stabVec (reps k)) = 51840 / repOrbitSize k := by
  have hidx : (stabVec (reps k)).index = repOrbitSize k := by
    rw [stabVec, MulAction.index_stabilizer, n1d2_orbit_eq (reps k)]
    exact ncard_wordOrbit_rep k
  have hcard := Subgroup.card_mul_index (stabVec (reps k))
  rw [hidx, CFSG.RankThree.E6.card_weylGroup_E6] at hcard
  exact Nat.eq_div_of_mul_eq_left (by fin_cases k <;> decide) hcard

private theorem n1d2_card_kerReflVec_rep
    (k : Fin 7) :
    Nat.card (kerReflVec (reps k)) = repKerGroupOrder k := by
  have hc := n1d2_card_kerReflVec (reps k)
  rcases lt_or_ge k.val 3 with hk | hk
  · obtain ⟨L, hnd, hlen, hmem⟩ := exists_nodup_closure_kerReflSet_rep_lt3 k hk
    have hle : kerReflVec (reps k) ≤ stabVec (reps k) := kerReflVec_le_stabVec (reps k)
    have h2 : Nat.card (kerReflVec (reps k)) ≤ Nat.card (stabVec (reps k)) :=
      Subgroup.card_le_of_le hle
    rw [n1d2_card_stabVec k] at h2
    have h3 : 51840 / repOrbitSize k = repKerGroupOrder k := by
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
        have h := k.isLt
        omega
      rcases hk' with rfl | rfl | rfl <;> decide
    have hfin : (Submonoid.closure (kerReflSet (reps k)) :
        Set (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)).Finite := by
      rw [← n1d2_weylMat_image_kerReflVec (reps k)]
      exact Set.Finite.image _ (Set.toFinite _)
    have hsub : (↑L.toFinset : Set (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)) ⊆
        (Submonoid.closure (kerReflSet (reps k)) :
          Set (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)) := by
      intro g hg
      rw [Finset.mem_coe, List.mem_toFinset] at hg
      exact hmem g hg
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen,
      ← Nat.card_coe_set_eq] at h1
    have h4 : repKerGroupOrder k ≤ Nat.card (Submonoid.closure (kerReflSet (reps k))) := h1
    omega
  · rw [hc]
    exact card_closure_kerReflSet_rep_ge3 k hk

theorem tableVec_rep
    (k : Fin 7) : TableVec (reps k) := by
  have hle : kerReflVec (reps k) ≤ stabVec (reps k) := kerReflVec_le_stabVec (reps k)
  have hker : Nat.card (kerReflVec (reps k)) = repKerGroupOrder k := n1d2_card_kerReflVec_rep k
  have hstab : Nat.card (stabVec (reps k)) = 51840 / repOrbitSize k := n1d2_card_stabVec k
  have hkr : (kerRoots (reps k)).ncard = repKerCard k := by
    rcases lt_or_ge k.val 3 with hk | hk
    · exact ncard_kerRoots_rep_lt3 k hk
    · exact ncard_kerRoots_rep_ge3 k hk
  have hidx : ((kerReflVec (reps k)).subgroupOf (stabVec (reps k))).index =
      (51840 / repOrbitSize k) / repKerGroupOrder k := by
    rw [Subgroup.index_eq_card_div, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      hstab, hker]
  rw [TableVec]
  fin_cases k
  · left; apply Subgroup.eq_of_le_of_card_ge hle; rw [hker, hstab]; decide
  · left; apply Subgroup.eq_of_le_of_card_ge hle; rw [hker, hstab]; decide
  · left; apply Subgroup.eq_of_le_of_card_ge hle; rw [hker, hstab]; decide
  · right; exact ⟨by rw [hkr]; decide, by rw [hidx]; decide⟩
  · right; exact ⟨by rw [hkr]; decide, by rw [hidx]; decide⟩
  · left; apply Subgroup.eq_of_le_of_card_ge hle; rw [hker, hstab]; decide
  · left; apply Subgroup.eq_of_le_of_card_ge hle; rw [hker, hstab]; decide

end CFSG.StandardType.NTPlane

end
