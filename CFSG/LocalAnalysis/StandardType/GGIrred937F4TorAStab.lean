module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8bAux

private def KpOrder3Check (r : Fin Tag.F4.rank → ZMod 3) (L : List ℕ) : Prop :=
  ∀ c ∈ L,
    (∀ j : Fin Tag.F4.rank,
      kpAct (kpTupN c) (kpAct (kpTupN c) (kpAct (kpTupN c) (Pi.single j 1))) = Pi.single j 1) →
    c = kpIdCode ∨
      ∃ p q s u : ZMod 3, (∀ j, kpPair (kpVec p q s u) (kpTupN c j) = kpVec p q s u j) ∧
        ∀ p' q' s' u' : ZMod 3,
          (∀ j, kpPair (kpVec p' q' s' u') (kpTupN c j) = kpVec p' q' s' u' j) →
          ∃ x y : ZMod 3, kpVec p' q' s' u' = x • r + y • kpVec p q s u

theorem kpOrder3_one : ∀ c ∈ kpCodesOne,
    (∀ j : Fin Tag.F4.rank,
      kpAct (kpTupN c) (kpAct (kpTupN c) (kpAct (kpTupN c) (Pi.single j 1))) = Pi.single j 1) →
    c = kpIdCode ∨
      ∃ p q s u : ZMod 3, (∀ j, kpPair (kpVec p q s u) (kpTupN c j) = kpVec p q s u j) ∧
        ∀ p' q' s' u' : ZMod 3,
          (∀ j, kpPair (kpVec p' q' s' u') (kpTupN c j) = kpVec p' q' s' u' j) →
          ∃ x y : ZMod 3, kpVec p' q' s' u' = x • kpVec 1 0 0 0 + y • kpVec p q s u := by
  decide +kernel

theorem kpOrder3_three : ∀ c ∈ kpCodesThree,
    (∀ j : Fin Tag.F4.rank,
      kpAct (kpTupN c) (kpAct (kpTupN c) (kpAct (kpTupN c) (Pi.single j 1))) = Pi.single j 1) →
    c = kpIdCode ∨
      ∃ p q s u : ZMod 3, (∀ j, kpPair (kpVec p q s u) (kpTupN c j) = kpVec p q s u j) ∧
        ∀ p' q' s' u' : ZMod 3,
          (∀ j, kpPair (kpVec p' q' s' u') (kpTupN c j) = kpVec p' q' s' u' j) →
          ∃ x y : ZMod 3, kpVec p' q' s' u' = x • kpVec 1 0 1 0 + y • kpVec p q s u := by
  decide +kernel

private theorem kpOrder3Check_one : KpOrder3Check (kpVec 1 0 0 0) kpCodesOne := kpOrder3_one

private theorem kpOrder3Check_three : KpOrder3Check (kpVec 1 0 1 0) kpCodesThree := kpOrder3_three

private theorem triPairing_eq_of_mem_charStabilizer {b : Fin Tag.F4.rank → ZMod 3}
    {w : WeylGroup Tag.F4} (hw : w ∈ charStabilizer (triChar b)) (v : Fin Tag.F4.rank → ℤ) :
    triPairing b (w • v) = triPairing b v := by
  have h := mem_charStabilizer.1 hw v
  rwa [triChar_apply, triChar_apply, Z3.ofAdd_eq_ofAdd_iff] at h

private theorem charStabilizer_of_kp_pair
    {l : Fin Tag.F4.rank → ZMod 3}
    {T : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ} {w : WeylGroup Tag.F4}
    (hT : ∀ j, w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = T j)
    (hfix : ∀ j, kpPair l (T j) = l j) :
    w ∈ charStabilizer (triChar l) := by
  rw [mem_charStabilizer]
  intro v
  have hcomp : charComp (triChar l) w = triChar l := by
    refine lattice_hom_ext fun j => ?_
    rw [charComp_apply, hT j, triChar_apply, triChar_apply]
    have h1 : triPairing l (T j) = triPairing l (Pi.single j 1) := by
      rw [kp_triPairing, hfix j]
      have hsingle := triPairing_zsmul_single l 1 j
      rw [one_smul, Int.cast_one, mul_one] at hsingle
      exact hsingle.symm
    exact congrArg Z3.ofAdd h1
  have h := congrArg (fun f => f (Multiplicative.ofAdd v)) hcomp
  rwa [charComp_apply] at h

private theorem triChar_transport
    (b : Fin Tag.F4.rank → ZMod 3) (t : WeylGroup Tag.F4) :
    triChar (fun j => triPairing b (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))) =
      charComp (triChar b) t := by
  refine lattice_hom_ext fun j => ?_
  rw [charComp_apply, triChar_apply, triChar_apply]
  exact congrArg Z3.ofAdd (kp_triPairing_transport b t (Pi.single j 1))

private theorem isCharConj_triChar_transport
    (b : Fin Tag.F4.rank → ZMod 3) (t : WeylGroup Tag.F4) :
    IsCharConj (triChar (fun j => triPairing b (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))))
      (triChar b) t := by
  intro v
  rw [triChar_transport, charComp_apply, smul_inv_smul]

private theorem isCharConj_pi_transport {ι : Type}
    (k : ι → Fin Tag.F4.rank → ZMod 3) (t : WeylGroup Tag.F4) :
    IsCharConj
      (MonoidHom.pi fun s =>
        triChar (fun j => triPairing (k s) (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))))
      (MonoidHom.pi fun s => triChar (k s)) t := by
  intro v
  funext s
  exact isCharConj_triChar_transport (k s) t v

private theorem kpTriPairing_smul_add (x y : ZMod 3) (r l : Fin Tag.F4.rank → ZMod 3)
    (α : Fin Tag.F4.rank → ℤ) :
    triPairing (x • r + y • l) α = x * triPairing r α + y * triPairing l α := by
  simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring

private theorem kernelWeylGroup_mono {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ ⊆ kernelRoots χ') : kernelWeylGroup χ ≤ kernelWeylGroup χ' := by
  rw [kernelWeylGroup, kernelWeylGroup]
  refine Subgroup.closure_mono ?_
  rintro r ⟨w, i, hα, rfl⟩
  exact ⟨w, i, h hα, rfl⟩

private theorem mem_kernelRoots_pi {ι : Type} (A : ι → Fin Tag.F4.rank → ZMod 3)
    {α : Fin Tag.F4.rank → ℤ} :
    α ∈ kernelRoots (MonoidHom.pi fun s => triChar (A s)) ↔
      IsRoot Tag.F4 α ∧ ∀ s, triPairing (A s) α = 0 := by
  refine Iff.trans Iff.rfl (and_congr_right fun _ => ?_)
  rw [funext_iff]
  refine forall_congr' fun s => ?_
  change Z3.ofAdd (triPairing (A s) α) = 1 ↔ triPairing (A s) α = 0
  rw [Z3.ofAdd_eq_one]

private theorem kpOrder3_family
    {ι : Type} (r : Fin Tag.F4.rank → ZMod 3) (L : List ℕ)
    (hid : kpIdCode ∈ L) (hcl : KpClosed r L) (hfin : KpOrder3Check r L)
    (hr : r = kpVec 1 0 0 0 ∨ r = kpVec 1 0 1 0)
    (A : ι → Fin Tag.F4.rank → ZMod 3) (i₀ : ι) (hi : A i₀ = r)
    (w : WeylGroup Tag.F4) (hw3 : w ^ 3 = 1)
    (hw : w ∈ charStabilizer (MonoidHom.pi fun s => triChar (A s))) :
    w ∈ kernelWeylGroup (MonoidHom.pi fun s => triChar (A s)) := by
  classical
  have hw_s : ∀ s, w ∈ charStabilizer (triChar (A s)) := by
    intro s
    rw [mem_charStabilizer]
    intro v
    exact congrArg (fun f : ι → Z3 => f s) (mem_charStabilizer.1 hw v)
  have hw_r : w ∈ charStabilizer (triChar r) := by
    rw [← hi]
    exact hw_s i₀
  have hwK_r : w ∈ kernelWeylGroup (triChar r) := by
    rw [← charStabilizer_eq_kernelWeylGroup_F4_three]
    exact hw_r
  obtain ⟨c, hc, hcw⟩ := kp_exists_code hid hcl hwK_r
  have hact : ∀ v, w • v = kpAct (kpTupN c) v := kp_smul_eq fun j => (hcw j).symm
  have hpow : ∀ j : Fin Tag.F4.rank,
      kpAct (kpTupN c) (kpAct (kpTupN c) (kpAct (kpTupN c) (Pi.single j 1))) =
        Pi.single j 1 := by
    intro j
    rw [← hact, ← hact, ← hact]
    have h :=
      congrArg (fun g : WeylGroup Tag.F4 => g • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) hw3
    simpa [pow_succ, mul_smul] using h
  rcases hfin c hc hpow with hcId | ⟨p, q, s, u, hlfix, hplane⟩
  · have hw1 : w = 1 := by
      refine ext_single fun j => ?_
      have : w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = Pi.single j 1 := by
        rw [← hcw j, hcId, kpIdCode_spec]
      simpa using this
    rw [hw1]
    exact one_mem _
  · let l : Fin Tag.F4.rank → ZMod 3 := kpVec p q s u
    have hw_l : w ∈ charStabilizer (triChar l) :=
      charStabilizer_of_kp_pair (l := l) (fun j => (hcw j).symm) hlfix
    have hw_pair : w ∈ charStabilizer (kpPairChar r l) := by
      rw [mem_charStabilizer]
      intro v
      rw [kpPairChar_apply, kpPairChar_apply, Prod.mk.injEq]
      exact ⟨mem_charStabilizer.1 hw_r v, mem_charStabilizer.1 hw_l v⟩
    have hne : (kernelRoots (kpPairChar r l)).Nonempty := by
      rcases hr with hr | hr
      · rw [hr]
        obtain ⟨t', ht', h1, h2⟩ := kp_commonRoot_one p q s u
        exact ⟨kpOfCoords t', mem_kernelRoots_kpPairChar.2
          ⟨mem_rootFinset.1 (kpTuples_isRoot t' ht'),
            by rw [kp_triPairing]; exact h1, by rw [kp_triPairing]; exact h2⟩⟩
      · rw [hr]
        obtain ⟨t', ht', h1, h2⟩ := kp_commonRoot_three p q s u
        exact ⟨kpOfCoords t', mem_kernelRoots_kpPairChar.2
          ⟨mem_rootFinset.1 (kpTuples_isRoot t' ht'),
            by rw [kp_triPairing]; exact h1, by rw [kp_triPairing]; exact h2⟩⟩
    have hwK : w ∈ kernelWeylGroup (kpPairChar r l) := kp_charStabilizer_le r l hne hw_pair
    refine kernelWeylGroup_mono (χ := kpPairChar r l)
      (χ' := MonoidHom.pi fun s => triChar (A s)) ?_ hwK
    intro α hα
    obtain ⟨hroot, hr0, hl0⟩ := mem_kernelRoots_kpPairChar.1 hα
    refine (mem_kernelRoots_pi A).2 ⟨hroot, fun s => ?_⟩
    have hfix_s : ∀ j, kpPair (kpVec (A s 0) (A s 1) (A s 2) (A s 3)) (kpTupN c j) =
        kpVec (A s 0) (A s 1) (A s 2) (A s 3) j := by
      intro j
      rw [kpVec_eta, hcw j, ← kp_triPairing,
        triPairing_eq_of_mem_charStabilizer (hw_s s) (Pi.single j 1)]
      have hsingle := triPairing_zsmul_single (A s) 1 j
      rwa [one_smul, Int.cast_one, mul_one] at hsingle
    obtain ⟨x, y, hxy⟩ := hplane (A s 0) (A s 1) (A s 2) (A s 3) hfix_s
    rw [show A s = x • r + y • l from by rw [← kpVec_eta (A s)]; exact hxy]
    rw [kpTriPairing_smul_add, hr0, hl0, mul_zero, mul_zero, add_zero]

private theorem kpOrder3_transport
    {ι : Type} (r : Fin Tag.F4.rank → ZMod 3) (L : List ℕ)
    (hid : kpIdCode ∈ L) (hcl : KpClosed r L) (hfin : KpOrder3Check r L)
    (hr : r = kpVec 1 0 0 0 ∨ r = kpVec 1 0 1 0)
    (k : ι → Fin Tag.F4.rank → ZMod 3) (i₀ : ι) (t : WeylGroup Tag.F4)
    (ht : IsCharConj (triChar r) (triChar (k i₀)) t)
    (w : WeylGroup Tag.F4) (hw3 : w ^ 3 = 1)
    (hw : w ∈ charStabilizer (MonoidHom.pi fun s => triChar (k s))) :
    w ∈ kernelWeylGroup (MonoidHom.pi fun s => triChar (k s)) := by
  classical
  let k' : ι → Fin Tag.F4.rank → ZMod 3 :=
    fun s j => triPairing (k s) (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))
  let w' : WeylGroup Tag.F4 := t⁻¹ * w * t
  have hir : k' i₀ = r := by
    funext j
    show triPairing (k i₀) (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) = r j
    have h := ht (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))
    rw [triChar_apply, triChar_apply, inv_smul_smul, Z3.ofAdd_eq_ofAdd_iff] at h
    rw [h]
    have hsingle := triPairing_zsmul_single r 1 j
    rw [one_smul, Int.cast_one, mul_one] at hsingle
    exact hsingle
  have hw'3 : w' ^ 3 = 1 := by
    have h := congrArg (MulAut.conj t⁻¹) hw3
    simpa [w', map_pow, MulAut.conj_apply] using h
  have hw'_stab : w' ∈ charStabilizer (MonoidHom.pi fun s => triChar (k' s)) :=
    (charStabilizer_iff_of_isCharConj (isCharConj_pi_transport k t)).mp hw
  have hw'_mem : w' ∈ kernelWeylGroup (MonoidHom.pi fun s => triChar (k' s)) :=
    kpOrder3_family r L hid hcl hfin hr k' i₀ hir w' hw'3 hw'_stab
  rw [kernelWeylGroup_eq_map (isCharConj_pi_transport k t)]
  refine Subgroup.mem_map.2 ⟨w', hw'_mem, ?_⟩
  show (MulAut.conj t) w' = w
  simp only [MulAut.conj_apply, w']
  group

theorem f4_hstab3_of_eighteen
    (L : Type) [Field L] {ι : Type}
    (a : ι → Fin Tag.F4.rank → Lˣ) (i₀ : ι)
    (ha : ∀ (s : ι) (i : Fin Tag.F4.rank), a s i ^ 3 = 1)
    (h18 : (rootCharKernel (τ := Tag.F4) (a i₀)).ncard = 18)
    (w : WeylGroup Tag.F4) (hw3 : w ^ 3 = 1) (hw : ∀ s, w ∈ rootCharStabilizer (a s)) :
    w ∈ kernelWeylGroup (familyChar a) := by
  classical
  have hχex : ∀ s, ∃ χ' : Multiplicative (Fin Tag.F4.rank → ℤ) →* Z3,
      ∀ x, rootCharHom3 (a s) x = 1 ↔ χ' x = 1 :=
    fun s => exists_triChar_ker_eq (rootCharHom3 (a s)) (rootCharHom3_pow_three (a s) (ha s))
  choose χ hχker using hχex
  let k : ι → Fin Tag.F4.rank → ZMod 3 :=
    fun s j => Z3.toAdd (χ s (Multiplicative.ofAdd (Pi.single j 1)))
  have hk : ∀ s, χ s = triChar (k s) := fun s => eq_triChar (χ s)
  have hker_s : ∀ s x, rootCharHom3 (a s) x = 1 ↔ triChar (k s) x = 1 := by
    intro s x
    rw [← hk s]
    exact hχker s x
  have hker_a : ∀ x, familyChar a x = 1 ↔
      (MonoidHom.pi fun s => triChar (k s)) x = 1 := by
    intro x
    have h1 : familyChar a x = 1 ↔ ∀ s, rootCharHom3 (a s) x = 1 := by
      rw [funext_iff]
      exact forall_congr' fun s => Iff.rfl
    have h2 : (MonoidHom.pi fun s => triChar (k s)) x = 1 ↔
        ∀ s, triChar (k s) x = 1 := by
      rw [funext_iff]
      exact forall_congr' fun s => Iff.rfl
    rw [h1, h2]
    exact forall_congr' fun s => hker_s s x
  have hw_char : w ∈ charStabilizer (familyChar a) := by
    rw [mem_charStabilizer]
    intro v
    funext s
    exact hw s v
  have hwC : w ∈ charStabilizer (MonoidHom.pi fun s => triChar (k s)) :=
    (charStabilizer_congr_ker hker_a).le hw_char
  obtain ⟨ρ, hρ, t, ht⟩ :=
    exists_isCharConj_of_orbitCheck3 f4ThreeOrbit_check (triChar (k i₀))
  have h4 : f4ThreeReps.length = 4 := rfl
  rw [h4] at hρ
  have h18tri : (kernelRoots (triChar (k i₀))).ncard = 18 := by
    rw [← kernelRoots_congr_ker (hker_s i₀)]
    exact h18
  have hn : (kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD ρ [])))).ncard = 18 := by
    have h := ncard_kernelRoots_of_isCharConj ht
    rw [h18tri] at h
    exact h.symm
  interval_cases ρ
  · have h48 := f4_kernelSizes_F4.1
    change (kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD 0 [])))).ncard = 48 at h48
    omega
  · rw [kp_vec3_one] at ht
    rw [kernelWeylGroup_congr_ker hker_a]
    exact kpOrder3_transport (kpVec 1 0 0 0) kpCodesOne (by decide) kpClosedOne
      kpOrder3Check_one (Or.inl rfl) k i₀ t ht w hw3 hwC
  · have h12 := f4_kernelSizes_A2A2t.1
    change (kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD 2 [])))).ncard = 12 at h12
    omega
  · rw [kp_vec3_three] at ht
    rw [kernelWeylGroup_congr_ker hker_a]
    exact kpOrder3_transport (kpVec 1 0 1 0) kpCodesThree (by decide) kpClosedThree
      kpOrder3Check_three (Or.inr rfl) k i₀ t ht w hw3 hwC

end Irred937

end CFSG.StandardType

end
