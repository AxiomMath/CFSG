module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableVec
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableOrbits
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableRep

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem n1d1_prod_zpow_eq {G : Type*} [CommGroup G] (y : G)
    (e : Fin Tag.E6.rank → ℤ) :
    ∏ k, y ^ e k = y ^ ∑ k, e k := by
  have h : ∀ n : ℤ, y ^ n = zpowersHom G y (Multiplicative.ofAdd n) := fun _ => rfl
  simp only [h, ofAdd_sum, map_prod]

theorem kerRoots_smul (w : WeylGroup Tag.E6) (x : X3) :
    kerRoots (w • x) = (fun α : Fin Tag.E6.rank → ℤ => w • α) '' kerRoots x := by
  ext α
  constructor
  · intro hα
    refine ⟨w⁻¹ • α, ⟨IsRoot.smul hα.1 w⁻¹, ?_⟩,
      by change w • (w⁻¹ • α) = α; exact smul_inv_smul w α⟩
    have h := hα.2
    rw [pairVec_smul] at h
    exact h
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨IsRoot.smul hβ.1 w, by rw [pairVec_smul_self, hβ.2]⟩

theorem stabVec_smul (w : WeylGroup Tag.E6) (x : X3) :
    stabVec (w • x) = (stabVec x).map (MulAut.conj w).toMonoidHom := by
  simpa only [stabVec] using MulAction.stabilizer_smul_eq_stabilizer_map_conj w x

private def n1d1_reflGens (x : X3) : Set (WeylGroup Tag.E6) :=
  {r | ∃ (u : WeylGroup Tag.E6) (i : Fin Tag.E6.rank),
    u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ kerRoots x ∧
      r = u * simple Tag.E6 i * u⁻¹}

private theorem n1d1_kerReflVec_eq_closure (x : X3) :
    kerReflVec x = Subgroup.closure (n1d1_reflGens x) := rfl

private theorem n1d1_reflGens_smul (w : WeylGroup Tag.E6) (x : X3) :
    n1d1_reflGens (w • x) =
      (MulAut.conj w).toMonoidHom '' n1d1_reflGens x := by
  ext r
  constructor
  · rintro ⟨u, i, hu, rfl⟩
    rw [kerRoots_smul] at hu
    rcases hu with ⟨β, hβ, hβeq⟩
    have hβeq' : w • β = u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := hβeq
    have hmem : w⁻¹ • (u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ∈ kerRoots x := by
      rw [← hβeq', inv_smul_smul]
      exact hβ
    refine ⟨(w⁻¹ * u) * simple Tag.E6 i * (w⁻¹ * u)⁻¹,
      ⟨w⁻¹ * u, i, by simpa [mul_smul] using hmem, rfl⟩, ?_⟩
    show w * ((w⁻¹ * u) * simple Tag.E6 i * (w⁻¹ * u)⁻¹) * w⁻¹ =
      u * simple Tag.E6 i * u⁻¹
    group
  · rintro ⟨r', hr', rfl⟩
    rcases hr' with ⟨u', i, hu', rfl⟩
    refine ⟨w * u', i, ?_, ?_⟩
    · rw [mul_smul, kerRoots_smul]
      exact ⟨u' • (Pi.single i 1 : Fin Tag.E6.rank → ℤ), hu', rfl⟩
    · show w * (u' * simple Tag.E6 i * u'⁻¹) * w⁻¹ =
        (w * u') * simple Tag.E6 i * (w * u')⁻¹
      group

theorem kerReflVec_smul (w : WeylGroup Tag.E6) (x : X3) :
    kerReflVec (w • x) = (kerReflVec x).map (MulAut.conj w).toMonoidHom := by
  rw [n1d1_kerReflVec_eq_closure, n1d1_kerReflVec_eq_closure x, n1d1_reflGens_smul w x,
    ← MonoidHom.map_closure (MulAut.conj w).toMonoidHom (n1d1_reflGens x)]

private theorem n1d1_tableVec_smul_forward (w : WeylGroup Tag.E6) (x : X3)
    (h : TableVec x) : TableVec (w • x) := by
  rcases h with h | ⟨hcard, hidx⟩
  · left
    rw [kerReflVec_smul, stabVec_smul, h]
  · right
    refine ⟨?_, ?_⟩
    · rw [kerRoots_smul,
        Set.ncard_image_of_injective (f := fun α : Fin Tag.E6.rank → ℤ => w • α) _
          (Function.LeftInverse.injective (g := fun α : Fin Tag.E6.rank → ℤ => w⁻¹ • α)
            (fun α => by change w⁻¹ • (w • α) = α; exact inv_smul_smul w α))]
      exact hcard
    · rw [← hidx, kerReflVec_smul, stabVec_smul]
      simpa only [Subgroup.relIndex] using
        Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj w).toMonoidHom)
          (kerReflVec x) (stabVec x) (MulAut.conj w).injective

private theorem n1d1_tableVec_smul (w : WeylGroup Tag.E6) (x : X3) :
    TableVec (w • x) ↔ TableVec x :=
  ⟨fun h => by simpa using n1d1_tableVec_smul_forward w⁻¹ (w • x) h,
    n1d1_tableVec_smul_forward w x⟩

theorem applyWord_eq_prod_smul (l : List (Fin Tag.E6.rank)) (x : X3) :
    applyWord l x = (l.map (simple Tag.E6)).prod • x := by
  induction l with
  | nil => simp [applyWord]
  | cons i l ih =>
    show dualRefl i (applyWord l x) = _
    rw [List.map_cons, List.prod_cons, mul_smul, ← ih, ← simple_smul_X3]

theorem ncard_kerRoots_smul (w : WeylGroup Tag.E6) (x : X3) :
    (kerRoots (w • x)).ncard = (kerRoots x).ncard := by
  rw [kerRoots_smul]
  exact Set.ncard_image_of_injective _ (MulAction.injective w)

theorem ncard_kerRoots_reps (k : Fin 7) : (kerRoots (reps k)).ncard = repKerCard k := by
  rcases lt_or_ge k.val 3 with hk | hk
  · exact ncard_kerRoots_rep_lt3 k hk
  · exact ncard_kerRoots_rep_ge3 k hk

theorem exists_smul_reps (x : X3) (hx : x ≠ 0) :
    ∃ (k : Fin 7) (w : WeylGroup Tag.E6), x = w • reps k := by
  obtain ⟨k, l, hl⟩ := exists_word_to_rep x hx
  refine ⟨k, ((l.map (simple Tag.E6)).prod)⁻¹, ?_⟩
  rw [← hl, applyWord_eq_prod_smul, inv_smul_smul]

theorem exists_vec_of_cube_roots {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (ha1 : a ≠ 1) :
    ∃ x : X3, x ≠ 0 ∧ ∀ v : Fin Tag.E6.rank → ℤ, rootChar a v = 1 ↔ pairVec x v = 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    exact ha1 (funext fun i => not_not.mp (h i))
  have hζo : orderOf (a i₀) = 3 := orderOf_eq_prime (ha3 i₀) hi₀
  have hprim : IsPrimitiveRoot (a i₀) 3 := hζo ▸ IsPrimitiveRoot.orderOf (a i₀)
  have hroot : ∀ y : Lˣ, y ^ 3 = 1 → ∃ m : ZMod 3, (a i₀) ^ m.val = y := fun y hy => by
    obtain ⟨n, hn, hn'⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 y).2 hy)
    exact ⟨n, by rw [ZMod.val_natCast_of_lt hn]; exact hn'⟩
  choose x hx using fun j => hroot (a j) (ha3 j)
  have hNcast : ∀ v, ((∑ j, ((x j).val : ℤ) * v j : ℤ) : ZMod 3) = pairVec x v := fun v => by
    rw [pairVec]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [ZMod.natCast_zmod_val]
  have hprod : ∀ v, rootChar a v = (a i₀) ^ (∑ j, ((x j).val : ℤ) * v j) := fun v => by
    simp only [rootChar]
    rw [show (∏ j, a j ^ v j) = ∏ j, ((a i₀) ^ (x j).val) ^ v j from
      Finset.prod_congr rfl fun j _ => by rw [hx j]]
    rw [show (∏ j, ((a i₀) ^ (x j).val) ^ v j) =
        ∏ j, (a i₀) ^ (((x j).val : ℤ) * v j) from
      Finset.prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul]]
    exact n1d1_prod_zpow_eq (a i₀) fun j => ((x j).val : ℤ) * v j
  have hxchar : ∀ v, rootChar a v = 1 ↔ pairVec x v = 0 := fun v => by
    rw [hprod v, ← hNcast v, ← orderOf_dvd_iff_zpow_eq_one, hζo]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).symm
  refine ⟨x, ?_, hxchar⟩
  intro hx0
  apply ha1
  funext j
  have hpv : pairVec x (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = 0 := by
    rw [hx0]; simp [pairVec]
  have hrc : rootChar a (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = 1 :=
    (hxchar (Pi.single j 1)).2 hpv
  have hsing : rootChar a (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = a j := by
    simpa using rootChar_nsmul_single a j 1
  exact hsing.symm.trans hrc

theorem rootCharKernel_eq_kerRoots {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {x : X3}
    (hxchar : ∀ v : Fin Tag.E6.rank → ℤ, rootChar a v = 1 ↔ pairVec x v = 0) :
    rootCharKernel a = kerRoots x := by
  ext α
  rw [rootCharKernel, kerRoots]
  exact ⟨fun h => ⟨h.1, (hxchar α).1 h.2⟩, fun h => ⟨h.1, (hxchar α).2 h.2⟩⟩

theorem rootCharStabilizerSubgroup_eq_stabVec {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {x : X3} (hxchar : ∀ v : Fin Tag.E6.rank → ℤ, rootChar a v = 1 ↔ pairVec x v = 0) :
    rootCharStabilizerSubgroup a = stabVec x := by
  ext w
  rw [stabVec, MulAction.mem_stabilizer_iff]
  change (∀ v : Fin Tag.E6.rank → ℤ, rootChar a (w • v) = rootChar a v) ↔ w • x = x
  have hiff1 : ∀ v : Fin Tag.E6.rank → ℤ,
      rootChar a (w • v) = rootChar a v ↔ pairVec x (w • v) = pairVec x v := by
    intro v
    rw [show pairVec x (w • v) = pairVec x v ↔ pairVec x (w • v - v) = 0 from by
      rw [pairVec_sub, sub_eq_zero]]
    rw [← hxchar, rootChar_sub, mul_inv_eq_one]
  constructor
  · intro hw
    apply pairVec_eq_of_forall
    intro v
    rw [pairVec_smul]
    have hv : pairVec x (w • (w⁻¹ • v)) = pairVec x (w⁻¹ • v) :=
      (hiff1 (w⁻¹ • v)).1 (hw (w⁻¹ • v))
    simpa using hv.symm
  · intro hwx v
    rw [hiff1 v]
    have h := pairVec_smul_self w x v
    rw [hwx] at h
    exact h

theorem kernelReflectionGroup_eq_kerReflVec {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {x : X3} (hxchar : ∀ v : Fin Tag.E6.rank → ℤ, rootChar a v = 1 ↔ pairVec x v = 0) :
    kernelReflectionGroup a = kerReflVec x := by
  unfold kernelReflectionGroup kerReflVec
  rw [rootCharKernel_eq_kerRoots hxchar]

theorem tableVec_of_ne_zero
    (x : X3) (hx : x ≠ 0) : TableVec x := by
  obtain ⟨k, l, hl⟩ := exists_word_to_rep x hx
  have hw : (l.map (simple Tag.E6)).prod • x = reps k :=
    (applyWord_eq_prod_smul l x).symm.trans hl
  have hxreps : x = ((l.map (simple Tag.E6)).prod)⁻¹ • reps k := by
    rw [← hw, inv_smul_smul]
  rw [hxreps]
  exact (n1d1_tableVec_smul ((l.map (simple Tag.E6)).prod)⁻¹ (reps k)).mpr (tableVec_rep k)

theorem e6_three_class_table
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (ha1 : a ≠ 1) :
    kernelReflectionGroup a = rootCharStabilizerSubgroup a ∨
      (((rootCharKernel a).ncard = 18 ∨ (rootCharKernel a).ncard = 24) ∧
        ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)).index = 3) := by
  obtain ⟨x, hx0, hxchar⟩ := exists_vec_of_cube_roots a ha3 ha1
  have ht := tableVec_of_ne_zero x hx0
  rw [kernelReflectionGroup_eq_kerReflVec hxchar, rootCharStabilizerSubgroup_eq_stabVec hxchar,
    rootCharKernel_eq_kerRoots hxchar]
  simpa only [TableVec] using ht

end CFSG.StandardType.NTPlane

end
