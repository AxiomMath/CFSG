module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma lk0xpa1_rootChar_pow_eq_one {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i ^ p = 1) (v : Fin τ.rank → ℤ) :
    rootChar b v ^ p = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb i, one_zpow]

private lemma lk0xpa1_zeta_pow_pow_p {K : Type} [Field K] {p : ℕ} {ζ : Kˣ}
    (hζpow : ζ ^ p = 1) (a : ℕ) : (ζ ^ a) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζpow, one_pow]

private lemma lk0xpa1_zmod_natCast_val {p : ℕ} [NeZero p] (i : ZMod p) :
    ((i.val : ℕ) : ZMod p) = i := by
  apply ZMod.val_injective p
  rw [ZMod.val_natCast_of_lt (ZMod.val_lt i)]

private lemma lk0xpa1_zeta_pow_inj {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (fun k : ZMod p => ζ ^ k.val) := by
  intro a b hab
  apply ZMod.val_injective p
  have hmod : a.val ≡ b.val [MOD p] := by
    have h := (pow_eq_pow_iff_modEq (x := ζ)).mp hab
    rwa [← hζ.eq_orderOf] at h
  exact hmod.eq_of_lt_of_lt (ZMod.val_lt a) (ZMod.val_lt b)

private lemma lk0xpa1_exists_zeta_pow {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {u : Kˣ} (hu : u ^ p = 1) :
    ∃ k : ZMod p, ζ ^ k.val = u := by
  obtain ⟨i, hi, hiu⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p u).mpr hu)
  exact ⟨(i : ZMod p), by rw [ZMod.val_natCast_of_lt hi]; exact hiu⟩

private lemma lk0xpa1_zeta_zpow_eq_of_intCast_eq {K : Type} [Field K] {p : ℕ}
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {a b : ℤ}
    (h : (a : ZMod p) = (b : ZMod p)) : ζ ^ a = ζ ^ b := by
  rw [zpow_eq_zpow_iff_modEq, ← hζ.eq_orderOf]
  exact (ZMod.intCast_eq_intCast_iff a b p).mp h

private lemma lk0xpa1_zeta_zpow_val_eq {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (a : ℤ) :
    ζ ^ ((a : ZMod p)).val = ζ ^ a := by
  have h : ((((a : ZMod p)).val : ℤ) : ZMod p) = (a : ZMod p) := by
    rw [Int.cast_natCast, lk0xpa1_zmod_natCast_val]
  rw [← zpow_natCast]
  exact lk0xpa1_zeta_zpow_eq_of_intCast_eq hζ h

private lemma lk0xpa1_rootChar_nodeMap_eq_zpow_sum
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {n : ℕ} {ζ : Kˣ} (nodeMap : (Fin n → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
    (b : Fin τ.rank → Kˣ) (t : Fin n → ZMod p)
    (ht : ∀ i, ζ ^ (t i).val = rootChar b (nodeMap (Pi.single i 1)))
    (w : Fin n → ℤ) :
    rootChar b (nodeMap w) = ζ ^ (∑ i, w i * (t i).val) := by
  have hw : w = ∑ i, w i • (Pi.single i 1 : Fin n → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc rootChar b (nodeMap w)
      = rootChar b (nodeMap (∑ i, w i • (Pi.single i 1 : Fin n → ℤ))) := by
          conv_lhs => rw [hw]
    _ = rootChar b (∑ i, w i • nodeMap (Pi.single i 1)) := by
          simp only [map_sum, map_smul]
    _ = ∏ i, rootChar b (w i • nodeMap (Pi.single i 1)) := by
          rw [rootChar_sum]
    _ = ∏ i, (rootChar b (nodeMap (Pi.single i 1))) ^ (w i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [rootChar_zsmul]
    _ = ∏ i, (ζ ^ (t i).val) ^ (w i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [ht i]
    _ = ∏ i, ζ ^ ((t i).val * w i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← zpow_natCast, zpow_mul]
    _ = ζ ^ (∑ i, (t i).val * w i) := by
          rw [Finset.prod_zpow_eq_zpow_sum]
    _ = ζ ^ (∑ i, w i * (t i).val) := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring

private lemma lk0xpa1_nodeExp_constraint
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (marks : List ℕ)
    (nodeMap : (Fin marks.length → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
    (hker : nodeMap.ker = Submodule.span ℤ
      ({fun i : Fin marks.length => (marks.getD i.val 0 : ℤ)} : Set (Fin marks.length → ℤ)))
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (b : Fin τ.rank → Kˣ) (t : Fin marks.length → ZMod p)
    (ht : ∀ i, ζ ^ (t i).val = rootChar b (nodeMap (Pi.single i 1))) :
    ∑ i, (marks.getD i.val 0 : ZMod p) * t i = 0 := by
  let m : Fin marks.length → ℤ := fun i => (marks.getD i.val 0 : ℤ)
  have hm_ker : m ∈ nodeMap.ker := by
    rw [hker]
    exact Submodule.subset_span (Set.mem_singleton m)
  have hnode : nodeMap m = 0 := hm_ker
  have hkey := lk0xpa1_rootChar_nodeMap_eq_zpow_sum nodeMap b t ht m
  have hz : ζ ^ (∑ i, m i * (t i).val) = 1 := by
    have h1 : rootChar b (nodeMap m) = 1 := by rw [hnode, rootChar_zero]
    rw [← hkey]; exact h1
  have hmod : (∑ i, m i * (t i).val) ≡ 0 [ZMOD p] := by
    have h := (zpow_eq_zpow_iff_modEq (x := ζ) (m := ∑ i, m i * (t i).val) (n := 0)).mp (by
      rw [zpow_zero]; exact hz)
    rwa [← hζ.eq_orderOf] at h
  have hN : ((∑ i, m i * (t i).val : ℤ) : ZMod p) = ((0 : ℤ) : ZMod p) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact Int.modEq_iff_dvd.mp hmod
  have hcast : ((∑ i, m i * (t i).val : ℤ) : ZMod p) =
      ∑ i, (marks.getD i.val 0 : ZMod p) * t i := by
    change ((∑ i, ((marks.getD i.val 0 : ℤ) * (t i).val) : ℤ) : ZMod p) =
      ∑ i, (marks.getD i.val 0 : ZMod p) * t i
    push_cast
    simp [lk0xpa1_zmod_natCast_val]
  rw [← hcast]
  simpa using hN

private lemma lk0xpa1_rootChar_eq_of_eq_on_nodes
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {n : ℕ} {ζ : Kˣ} (nodeMap : (Fin n → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
    (hsurj : Function.Surjective nodeMap)
    (b b' : Fin τ.rank → Kˣ) (t : Fin n → ZMod p)
    (hb : ∀ i, ζ ^ (t i).val = rootChar b (nodeMap (Pi.single i 1)))
    (hb' : ∀ i, ζ ^ (t i).val = rootChar b' (nodeMap (Pi.single i 1)))
    (v : Fin τ.rank → ℤ) :
    rootChar b v = rootChar b' v := by
  obtain ⟨w, hw⟩ := hsurj v
  rw [← hw, lk0xpa1_rootChar_nodeMap_eq_zpow_sum nodeMap b t hb w,
    lk0xpa1_rootChar_nodeMap_eq_zpow_sum nodeMap b' t hb' w]

private lemma lk0xpa1_eq_of_rootChar_eq {τ : Tag} {K : Type} [Field K]
    {b b' : Fin τ.rank → Kˣ} (h : ∀ v, rootChar b v = rootChar b' v) : b = b' := by
  funext j
  have hj := h (Pi.single j 1)
  rwa [rootChar_single b j, rootChar_single b' j] at hj

private lemma lk0xpa1_exists_lift
    {τ : Tag} {p : ℕ}
    (marks : List ℕ)
    (nodeMap : (Fin marks.length → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
    (hsurj : Function.Surjective nodeMap)
    (hker : nodeMap.ker = Submodule.span ℤ
      ({fun i : Fin marks.length => (marks.getD i.val 0 : ℤ)} : Set (Fin marks.length → ℤ)))
    (t : Fin marks.length → ZMod p)
    (ht : ∑ i, (marks.getD i.val 0 : ZMod p) * t i = 0) :
    ∃ χ : (Fin τ.rank → ℤ) →ₗ[ℤ] ZMod p, ∀ i, χ (nodeMap (Pi.single i 1)) = t i := by
  classical
  let L : (Fin marks.length → ℤ) →ₗ[ℤ] ZMod p :=
    { toFun := fun w => ∑ i, (w i : ZMod p) * t i
      map_add' := by
        intro w w'
        simp [Int.cast_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  have hLm : L (fun i : Fin marks.length => (marks.getD i.val 0 : ℤ)) = 0 := by
    change (∑ i, (((marks.getD i.val 0 : ℤ)) : ZMod p) * t i) = 0
    simp only [Int.cast_natCast]
    exact ht
  have hker_le : nodeMap.ker ≤ L.ker := by
    rw [hker, Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    simpa using hLm
  let lift : (Fin marks.length → ℤ) ⧸ nodeMap.ker →ₗ[ℤ] ZMod p :=
    nodeMap.ker.liftQ L hker_le
  let qe : (Fin τ.rank → ℤ) ≃ₗ[ℤ] (Fin marks.length → ℤ) ⧸ nodeMap.ker :=
    (LinearMap.quotKerEquivOfSurjective nodeMap hsurj).symm
  refine ⟨lift.comp qe.toLinearMap, ?_⟩
  intro i
  have hqe : qe (nodeMap (Pi.single i 1)) =
      Submodule.Quotient.mk (Pi.single i 1 : Fin marks.length → ℤ) := by
    change (LinearMap.quotKerEquivOfSurjective nodeMap hsurj).symm (nodeMap (Pi.single i 1)) =
      Submodule.Quotient.mk (Pi.single i 1 : Fin marks.length → ℤ)
    exact LinearMap.quotKerEquivOfSurjective_symm_apply (f := nodeMap) hsurj (Pi.single i 1)
  have hlift : lift (Submodule.Quotient.mk (Pi.single i 1 : Fin marks.length → ℤ)) = t i := by
    change nodeMap.ker.liftQ L hker_le
      (Submodule.Quotient.mk (Pi.single i 1 : Fin marks.length → ℤ)) = t i
    rw [Submodule.liftQ_apply]
    change (∑ j, ((Pi.single i 1 : Fin marks.length → ℤ) j : ZMod p) * t j) = t i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [LinearMap.comp_apply]
  change lift (qe (nodeMap (Pi.single i 1))) = t i
  rw [hqe, hlift]

private lemma lk0xpa1_rootChar_of_chi
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (χ : (Fin τ.rank → ℤ) →ₗ[ℤ] ZMod p) (v : Fin τ.rank → ℤ) :
    rootChar (fun j => ζ ^ (χ (Pi.single j 1)).val) v = ζ ^ (χ v).val := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hχv : ((∑ j, (χ (Pi.single j 1)).val * v j : ℤ) : ZMod p) = χ v := by
    have h1 : χ v = ∑ j, v j • χ (Pi.single j 1) := by
      conv_lhs => rw [hv]
      rw [map_sum]
      simp only [map_smul]
    rw [h1, Int.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, lk0xpa1_zmod_natCast_val, zsmul_eq_mul]
    ring
  calc rootChar (fun j => ζ ^ (χ (Pi.single j 1)).val) v
      = ∏ j, rootChar (fun j => ζ ^ (χ (Pi.single j 1)).val) (v j • Pi.single j 1) := by
          conv_lhs => rw [hv]
          rw [rootChar_sum]
    _ = ∏ j, (rootChar (fun j => ζ ^ (χ (Pi.single j 1)).val) (Pi.single j 1)) ^ (v j) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [rootChar_zsmul]
    _ = ∏ j, (ζ ^ (χ (Pi.single j 1)).val) ^ (v j) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          simp [rootChar_single]
    _ = ∏ j, ζ ^ ((χ (Pi.single j 1)).val * v j) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← zpow_natCast, zpow_mul]
    _ = ζ ^ (∑ j, (χ (Pi.single j 1)).val * v j) := by
          rw [Finset.prod_zpow_eq_zpow_sum]
    _ = ζ ^ (((∑ j, (χ (Pi.single j 1)).val * v j : ℤ) : ZMod p)).val := by
          rw [← lk0xpa1_zeta_zpow_val_eq hζ]
    _ = ζ ^ (χ v).val := by rw [hχv]

theorem PA1_nodeExp_equiv
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hp : p.Prime) (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    ∃ e : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} ≃
        {t : Fin ρ.row.diagram.marks.length → ZMod p //
          ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0},
      ∀ b i, rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((e b).1 i).val := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ : IsPrimitiveRoot ρ.zeta p := IsPrimitiveRoot.iff_orderOf.mpr ρ.zeta_order
  have hζpow : ρ.zeta ^ p = 1 := (hζ.pow_eq_one_iff_dvd p).mpr (dvd_refl p)
  let Φ : {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} →
      {t : Fin ρ.row.diagram.marks.length → ZMod p //
        ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0} :=
    fun b => ⟨fun i => Classical.choose (lk0xpa1_exists_zeta_pow hζ
        (lk0xpa1_rootChar_pow_eq_one b.1 b.2 (ρ.nodeMap (Pi.single i 1)))),
      lk0xpa1_nodeExp_constraint ρ.row.diagram.marks ρ.nodeMap ρ.nodeMap_ker hζ b.1
        (fun i => Classical.choose (lk0xpa1_exists_zeta_pow hζ
          (lk0xpa1_rootChar_pow_eq_one b.1 b.2 (ρ.nodeMap (Pi.single i 1)))))
        (fun i => Classical.choose_spec (lk0xpa1_exists_zeta_pow hζ
          (lk0xpa1_rootChar_pow_eq_one b.1 b.2 (ρ.nodeMap (Pi.single i 1)))))⟩
  have hΦspec : ∀ b i, ρ.zeta ^ ((Φ b).1 i).val = rootChar b.1 (ρ.nodeMap (Pi.single i 1)) := by
    intro b i
    change ρ.zeta ^ (Classical.choose (lk0xpa1_exists_zeta_pow hζ
      (lk0xpa1_rootChar_pow_eq_one b.1 b.2 (ρ.nodeMap (Pi.single i 1))))).val =
      rootChar b.1 (ρ.nodeMap (Pi.single i 1))
    exact Classical.choose_spec (lk0xpa1_exists_zeta_pow hζ
      (lk0xpa1_rootChar_pow_eq_one b.1 b.2 (ρ.nodeMap (Pi.single i 1))))
  let χOf : {t : Fin ρ.row.diagram.marks.length → ZMod p //
        ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0} →
      (Fin ρ.tau.rank → ℤ) →ₗ[ℤ] ZMod p :=
    fun t => Classical.choose (lk0xpa1_exists_lift ρ.row.diagram.marks ρ.nodeMap
      ρ.nodeMap_surj ρ.nodeMap_ker t.1 t.2)
  have hχOf : ∀ t i, χOf t (ρ.nodeMap (Pi.single i 1)) = t.1 i := by
    intro t i
    exact Classical.choose_spec (lk0xpa1_exists_lift ρ.row.diagram.marks ρ.nodeMap
      ρ.nodeMap_surj ρ.nodeMap_ker t.1 t.2) i
  let Ψ : {t : Fin ρ.row.diagram.marks.length → ZMod p //
        ∑ i, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) * t i = 0} →
      {b : Fin ρ.tau.rank → Omegaˣ // ∀ i, b i ^ p = 1} :=
    fun t => ⟨fun j => ρ.zeta ^ ((χOf t) (Pi.single j 1)).val,
      fun j => lk0xpa1_zeta_pow_pow_p hζpow _⟩
  have hΨchar : ∀ t v, rootChar (Ψ t).1 v = ρ.zeta ^ ((χOf t) v).val := by
    intro t v
    exact lk0xpa1_rootChar_of_chi hζ (χOf t) v
  have hleft : Function.LeftInverse Ψ Φ := by
    intro b
    apply Subtype.ext
    apply lk0xpa1_eq_of_rootChar_eq
    intro v
    exact lk0xpa1_rootChar_eq_of_eq_on_nodes ρ.nodeMap ρ.nodeMap_surj (Ψ (Φ b)).1 b.1 (Φ b).1
      (fun i => by rw [hΨchar (Φ b) (ρ.nodeMap (Pi.single i 1)), hχOf (Φ b) i])
      (hΦspec b) v
  have hright : Function.RightInverse Ψ Φ := by
    intro t
    apply Subtype.ext
    funext i
    apply lk0xpa1_zeta_pow_inj hζ
    change ρ.zeta ^ ((Φ (Ψ t)).1 i).val = ρ.zeta ^ (t.1 i).val
    rw [hΦspec (Ψ t) i, hΨchar t (ρ.nodeMap (Pi.single i 1)), hχOf t i]
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h := congrArg Ψ hab
    rwa [hleft a, hleft b] at h
  have hsurj : Function.Surjective Φ := fun b => ⟨Ψ b, hright b⟩
  refine ⟨Equiv.ofBijective Φ ⟨hinj, hsurj⟩, ?_⟩
  intro b i
  change rootChar b.1 (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ ((Φ b).1 i).val
  exact (hΦspec b i).symm

end CFSG.StandardType.GGK0ExcCentreU

end
