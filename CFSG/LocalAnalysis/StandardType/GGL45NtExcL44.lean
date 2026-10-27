module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcW1
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice

public section

namespace CFSG.HardMathSupport.C14L44

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Torus
  CFSG.HardMathSupport.Timmesfeld.Torality
open scoped Matrix

theorem permLattice_permLattice {τ : Tag} (σ σ' : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice σ (permLattice σ' v) = permLattice (σ * σ') v := rfl

theorem permLattice_one {τ : Tag} (v : Fin τ.rank → ℤ) :
    permLattice (1 : Equiv.Perm (Fin τ.rank)) v = v :=
  rfl

theorem exists_permLattice_smul {τ : Tag}
    {σ : Equiv.Perm (Fin τ.rank)} (hσ : ∀ i j, τ.cartan (σ i) (σ j) = τ.cartan i j)
    (w : WeylGroup τ) :
    ∃ w' : WeylGroup τ, ∀ v, permLattice σ (w • v) = w' • permLattice σ v := by
  induction w using (coxeterSystem τ).simple_induction with
  | simple i => exact ⟨simple τ (σ i), fun v => by rw [simple_smul, simple_smul, permLattice_reflect hσ]⟩
  | one => exact ⟨1, fun v => by rw [one_smul, one_smul]⟩
  | mul w w' hw hw' =>
    obtain ⟨u, hu⟩ := hw
    obtain ⟨u', hu'⟩ := hw'
    exact ⟨u * u', fun v => by rw [mul_smul, hu, hu', mul_smul]⟩

theorem exists_pow_mulVec_eq_smul {τ : Tag}
    {σ : Equiv.Perm (Fin τ.rank)} (hσ : ∀ i j, τ.cartan (σ i) (σ j) = τ.cartan i j)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (w₁ : WeylGroup τ)
    (hM : ∀ v, M *ᵥ v = w₁ • permLattice σ v) (j : ℕ) :
    ∃ u : WeylGroup τ, ∀ v, (M ^ j) *ᵥ v = u • permLattice (σ ^ j) v := by
  induction j with
  | zero => exact ⟨1, fun v => by rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]; rfl⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨u', hu'⟩ := exists_permLattice_smul hσ u
    refine ⟨w₁ * u', fun v => ?_⟩
    rw [pow_succ', ← Matrix.mulVec_mulVec, hu, hM, hu', mul_smul, permLattice_permLattice,
      pow_succ']

theorem rootChar_smul_of_mem_familyReflectionGroup {τ : Tag}
    {K : Type} [Field K] {ι : Type}
    (a : ι → Fin τ.rank → Kˣ) {r : WeylGroup τ}
    (hr : r ∈ CFSG.HardMathSupport.C14Lattice.familyReflectionGroup a)
    {z : Fin τ.rank → Kˣ} (hz : ∀ β ∈ familyKernel a, rootChar z β = 1) (v : Fin τ.rank → ℤ) :
    rootChar z (r • v) = rootChar z v := by
  have hn := CFSG.HardMathSupport.C14Lattice.canonicalRep_mem_familyGroup (K := K) (inv_mem hr)
  let b : Unit → Fin τ.rank → Kˣ := fun _ => z
  have hker : familyKernel a ⊆ familyKernel b := fun α hα => ⟨hα.1, fun _ => hz α hα⟩
  have hle : familyGroup (K := K) a ≤ familyGroup (K := K) b :=
    sup_le_sup_left (rootSpan_mono hker) _
  have hc : rootDiagUnit τ z * canonicalRep (coxeterSystem τ) K r⁻¹ * (rootDiagUnit τ z)⁻¹ =
      canonicalRep (coxeterSystem τ) K r⁻¹ :=
    (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer b (hle hn))).2 ()
  have h1 : canonicalRep (coxeterSystem τ) K r⁻¹ * rootDiagUnit τ z *
      (canonicalRep (coxeterSystem τ) K r⁻¹)⁻¹ = rootDiagUnit τ z := by
    rw [mul_inv_eq_iff_eq_mul] at hc ⊢
    exact hc.symm
  rw [canonicalRep_conj_rootDiagUnit] at h1
  have h2 := CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' h1
  calc rootChar z (r • v) = rootChar (weylTuple r⁻¹ z) v := by rw [rootChar_weylTuple, inv_inv]
    _ = rootChar z v := by rw [h2]

theorem exists_weylTuple {τ : Tag}
    {L : Type} [Field L] {n : ModGL τ L} (hn : n ∈ adjointGroup τ L)
    (hnT : ∀ t, ∃ t', n * rootDiagUnit τ t * n⁻¹ = rootDiagUnit τ t') :
    ∃ w : WeylGroup τ, ∀ t, n * rootDiagUnit τ t * n⁻¹ = rootDiagUnit τ (weylTuple w t) := by
  obtain ⟨w, hw⟩ :=
    CFSG.StandardType.NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (V := Set.range (rootDiagUnit τ)) (fun _ ⟨a, ha⟩ => ⟨a, ha.symm⟩) hn
      (fun _ ⟨a, ha⟩ => by obtain ⟨t', ht'⟩ := hnT a; exact ⟨t', by rw [← ha, ht']⟩)
  exact ⟨w, fun t => by rw [hw _ ⟨t, rfl⟩, canonicalRep_conj_rootDiagUnit]⟩

theorem diagramMap_conj_rootDiagUnit




    {L : Type} [Field L] (t : TwistTag) (b : Fin t.tag.rank → Lˣ) :
    diagramMap t L * rootDiagUnit t.tag b * (diagramMap t L)⁻¹ =
      rootDiagUnit t.tag (fun i => b (t.perm.symm i)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change (diagramMap t L : Module.End L (RootModule t.tag L)) * rootDiag b * _ = rootDiag _
  rw [diagramMap_mul_rootDiag, mul_assoc, Units.mul_inv, mul_one]

theorem diagramMap_zpow_conj_rootDiagUnit




    {L : Type} [Field L] (t : TwistTag) (k : ℤ) (b : Fin t.tag.rank → Lˣ) :
    diagramMap t L ^ k * rootDiagUnit t.tag b * (diagramMap t L ^ k)⁻¹ =
      rootDiagUnit t.tag (fun i => b ((t.perm ^ k).symm i)) := by
  induction k using Int.induction_on generalizing b with
  | zero => simp only [zpow_zero, one_mul, inv_one, mul_one]; rfl
  | succ k ih =>
    calc diagramMap t L ^ ((k : ℤ) + 1) * rootDiagUnit t.tag b * (diagramMap t L ^ ((k : ℤ) + 1))⁻¹
        = diagramMap t L ^ (k : ℤ) * (diagramMap t L * rootDiagUnit t.tag b * (diagramMap t L)⁻¹) *
            (diagramMap t L ^ (k : ℤ))⁻¹ := by rw [zpow_add_one]; group
      _ = _ := by
        rw [diagramMap_conj_rootDiagUnit, ih, zpow_add_one]
        rfl
  | pred k ih =>
    have hP : (diagramMap t L)⁻¹ * rootDiagUnit t.tag b * diagramMap t L =
        rootDiagUnit t.tag (fun i => b (t.perm i)) := by
      have := diagramMap_conj_rootDiagUnit (L := L) t (fun i => b (t.perm i))
      simp only [Equiv.apply_symm_apply] at this
      rw [← this]
      group
    calc diagramMap t L ^ (-(k : ℤ) - 1) * rootDiagUnit t.tag b * (diagramMap t L ^ (-(k : ℤ) - 1))⁻¹
        = diagramMap t L ^ (-(k : ℤ)) * ((diagramMap t L)⁻¹ * rootDiagUnit t.tag b * diagramMap t L) *
            (diagramMap t L ^ (-(k : ℤ)))⁻¹ := by rw [zpow_sub_one]; group
      _ = _ := by
        rw [hP, ih, zpow_sub_one]
        rfl

theorem cartan_zpow





    {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (k : ℤ) (i j : Fin τ.rank) :
    τ.cartan ((π ^ k) i) ((π ^ k) j) = τ.cartan i j := by
  let H : Subgroup (Equiv.Perm (Fin τ.rank)) :=
    { carrier := {σ | ∀ i j, τ.cartan (σ i) (σ j) = τ.cartan i j}
      one_mem' := fun _ _ => rfl
      mul_mem' := fun {a b} ha hb i j => by
        change τ.cartan (a (b i)) (a (b j)) = _
        rw [ha, hb]
      inv_mem' := fun {a} ha i j => cartan_perm_symm ha i j }
  exact (H.zpow_mem (show π ∈ H from hπ) k) i j

theorem exists_pow_weyl {τ : Tag}
    {L : Type} [Field L] [Infinite L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3D : τ = .D4 → p ≠ 3) (Q : ModGL τ L) (A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hA : ∀ t, Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ (tmap A t))
    (hQτ : Q ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q = (h ▸ diagramMap t L ^ j) * n) :
    ∃ o : ℕ, 0 < o ∧ ¬ p ∣ o ∧ ∃ w₀ : WeylGroup τ, ∀ v, (A ^ o) *ᵥ v = w₀ • v := by
  have hinj := CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' (τ := τ) (K := L)
  rcases hQτ with hQ | ⟨t, j, rfl, n, hn, rfl⟩
  · obtain ⟨w, hw⟩ := exists_weylTuple hQ fun s => ⟨_, hA s⟩
    refine ⟨1, one_pos, hp.not_dvd_one, w⁻¹, fun v => ?_⟩
    · rw [pow_one]
      refine CFSG.HardMathSupport.C14W1.eq_of_rootChar_eq (K := L) fun s => ?_
      rw [← rootChar_tmap, hinj ((hA s).symm.trans (hw s)), rootChar_weylTuple]
  ·
    set D := diagramMap t L ^ j with hD
    set ρ := t.perm ^ j with hρ
    have hDc : ∀ b, D * rootDiagUnit t.tag b * D⁻¹ = rootDiagUnit t.tag (fun i => b (ρ.symm i)) :=
      fun b => diagramMap_zpow_conj_rootDiagUnit t j b
    have hP : ∀ b, D⁻¹ * rootDiagUnit t.tag b * D = rootDiagUnit t.tag (fun i => b (ρ i)) := by
      intro b
      have := hDc (fun i => b (ρ i))
      simp only [Equiv.apply_symm_apply] at this
      rw [← this]
      group
    obtain ⟨w, hw⟩ := exists_weylTuple hn fun s => ⟨fun i => tmap A s (ρ i), by
      have h1 := hA s
      calc n * rootDiagUnit t.tag s * n⁻¹ = D⁻¹ *
            (D * n * rootDiagUnit t.tag s * (D * n)⁻¹) * D := by group
        _ = _ := by rw [h1, hP]⟩
    have hQc : ∀ s : Fin t.tag.rank → Lˣ, tmap A s = fun i => weylTuple w s (ρ.symm i) := by
      intro s
      apply hinj
      rw [← hA, ← hDc, ← hw]
      group
    have hσ : ∀ i j, t.tag.cartan (ρ.symm i) (ρ.symm j) = t.tag.cartan i j :=
      cartan_perm_symm (cartan_zpow t.cartan_perm j)
    have hAv : ∀ v, A *ᵥ v = w⁻¹ • permLattice ρ.symm v := by
      intro v
      refine CFSG.HardMathSupport.C14W1.eq_of_rootChar_eq (K := L) fun s => ?_
      rw [← rootChar_tmap, hQc, ← rootChar_weylTuple, rootChar_permLattice]
    obtain ⟨u, hu⟩ := exists_pow_mulVec_eq_smul hσ A w⁻¹ hAv t.order
    have hord : ρ.symm ^ t.order = 1 := by
      rw [← Equiv.Perm.inv_def, inv_pow, hρ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, TwistTag.perm_pow_order, one_zpow, inv_one]
    refine ⟨t.order, ?_, ?_, u, fun v => by rw [hu, hord, permLattice_one]⟩
    · cases t <;> decide
    · cases t
      · intro h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
      · intro h
        exact h3D rfl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

end CFSG.HardMathSupport.C14L44
