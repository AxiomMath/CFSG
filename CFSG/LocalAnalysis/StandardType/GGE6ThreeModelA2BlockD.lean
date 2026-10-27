module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelA2BlockB
public import CFSG.RankThree.SteinbergR3ESL3RootPermutingFixed

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Quasithin.F134.LieOdd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
open scoped MatrixGroups
open Matrix


section Helpers

variable {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

private theorem frobenius_algebraMap {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (c : K) : Fr (algebraMap K Ω c) = algebraMap K Ω c := by
  rw [hFr, ← map_pow]
  have hpow : c ^ Nat.card K = c := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  rw [hpow]

private theorem frobE6_pinnedX {Fr : Ω →+* Ω} (γ : Fin Tag.E6.rank → ℤ) (c : Ω) :
    frobE6 Fr (pinnedX Tag.E6 Ω γ c) = pinnedX Tag.E6 Ω γ (Fr c) := by
  refine Units.ext ?_
  change entrywiseHom Fr (pinnedX Tag.E6 Ω γ c : Module.End Ω (RootModule Tag.E6 Ω)) =
    (pinnedX Tag.E6 Ω γ (Fr c) : Module.End Ω (RootModule Tag.E6 Ω))
  exact entrywise_pinnedX Fr γ c

private theorem frobE6_injective {Fr : Ω →+* Ω} : Function.Injective (frobE6 Fr) := by
  intro A B h
  refine Units.ext ?_
  exact entrywise_injective (σ := Fr) (congrArg Units.val h)

private theorem frobE6_mem_rootSpan {Fr : Ω →+* Ω} {S : Set (Fin Tag.E6.rank → ℤ)}
    {u : ModGL Tag.E6 Ω} (hu : u ∈ rootSpan Tag.E6 Ω S) :
    frobE6 Fr u ∈ rootSpan Tag.E6 Ω S := by
  rw [rootSpan_eq_closure] at hu ⊢
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨γ, hγ, c, rfl⟩ := hx
      rw [frobE6_pinnedX]
      exact Subgroup.subset_closure ⟨γ, hγ, Fr c, rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

private theorem frobE6_baseChangeGL_eq {Fr : Ω →+* Ω}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {S : Set (Fin Tag.E6.rank → ℤ)}
    {y : ModGL Tag.E6 K} (hy : y ∈ rootSpan Tag.E6 K S) :
    frobE6 Fr (baseChangeGL (algebraMap K Ω) y) = baseChangeGL (algebraMap K Ω) y := by
  rw [rootSpan_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨γ, hγ, c, rfl⟩ := hx
      rw [baseChangeGL_pinnedX, frobE6_pinnedX, frobenius_algebraMap hFr, ← baseChangeGL_pinnedX]
  | one => simp
  | mul x y _ _ hx hy =>
      rw [map_mul (baseChangeGL (algebraMap K Ω)), map_mul (frobE6 Fr), hx, hy]
  | inv x _ hx =>
      rw [map_inv (baseChangeGL (algebraMap K Ω)), map_inv (frobE6 Fr), hx]

end Helpers

theorem fixed_blockGroup_eq {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card K) (i : Fin 3)
    {z : ModGL Tag.E6 Ω} (hz : z ∈ rootSpan Tag.E6 Ω (a2Roots (a2PairE6 i).1 (a2PairE6 i).2))
    (hF : frobE6 Fr z = z) :
    ∃ y ∈ rootSpan Tag.E6 K (a2Roots (a2PairE6 i).1 (a2PairE6 i).2),
      baseChangeGL (algebraMap K Ω) y = z := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ρK, σK, hfrK, hσK01, hσK12⟩ := exists_frame_a2PairE6 K i
  obtain ⟨ρ, σ, hfr, hσ01, hσ12⟩ := exists_frame_a2PairE6 Ω i
  set S : Set (Fin Tag.E6.rank → ℤ) := a2Roots (a2PairE6 i).1 (a2PairE6 i).2 with hS
  have hspanK : rootSpan Tag.E6 K S = ρK.range := by
    rw [hS, ← hσK01, ← hσK12]
    exact rootSpan_a2Roots_eq_range hfrK
  have hspan : ρ.range = rootSpan Tag.E6 Ω S := by
    rw [hS, ← hσ01, ← hσ12]
    exact (rootSpan_a2Roots_eq_range hfr).symm
  have hFmem : ∀ r ∈ rootSpan Tag.E6 Ω S, frobE6 Fr r ∈ rootSpan Tag.E6 Ω S :=
    fun r hr => frobE6_mem_rootSpan hr
  have hqpos : 0 < Nat.card K := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨(0 : K)⟩
  have hFr_surj : Function.Surjective Fr := by
    intro c
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq c hqpos
    exact ⟨x, by rw [hFr, hx]⟩
  have hFsurj : rootSpan Tag.E6 Ω S ≤ (rootSpan Tag.E6 Ω S).map (frobE6 Fr) := by
    rw [rootSpan_eq_closure, Subgroup.closure_le]
    rintro g ⟨γ, hγ, c, rfl⟩
    obtain ⟨c', rfl⟩ := hFr_surj c
    rw [← frobE6_pinnedX γ c']
    exact Subgroup.mem_map_of_mem (frobE6 Fr) (Subgroup.subset_closure ⟨γ, hγ, c', rfl⟩)
  let eρ : SL(3, Ω) ≃* ρ.range := MonoidHom.ofInjective hfr.injective
  have hFmem' : ∀ r ∈ ρ.range, frobE6 Fr r ∈ ρ.range := by
    intro r hr
    rw [hspan] at hr ⊢
    exact hFmem r hr
  let FQ : ρ.range →* ρ.range :=
    { toFun := fun r => ⟨frobE6 Fr r.1, hFmem' r.1 r.2⟩
      map_one' := Subtype.ext (map_one (frobE6 Fr))
      map_mul' := fun a b => Subtype.ext (map_mul (frobE6 Fr) a.1 b.1) }
  have hFQinj : Function.Injective FQ := by
    intro a b h
    apply Subtype.ext
    exact frobE6_injective (congrArg Subtype.val h)
  have hFQsurj : Function.Surjective FQ := by
    intro r
    have hr : r.1 ∈ (rootSpan Tag.E6 Ω S).map (frobE6 Fr) :=
      hFsurj (hspan ▸ r.2)
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hr
    exact ⟨⟨q, by rw [hspan]; exact hq⟩, Subtype.ext hqeq⟩
  let FQe : ρ.range ≃* ρ.range := MulEquiv.ofBijective FQ ⟨hFQinj, hFQsurj⟩
  let Θ : SL(3, Ω) ≃* SL(3, Ω) := (eρ.trans FQe).trans eρ.symm
  have hΘ : ∀ A : SL(3, Ω), ρ (Θ A) = frobE6 Fr (ρ A) := by
    intro A
    have h1 : ρ (eρ.symm (FQ (eρ A))) = (FQ (eρ A) : ModGL Tag.E6 Ω) :=
      congrArg Subtype.val (eρ.apply_symm_apply (FQ (eρ A)))
    change ρ (eρ.symm (FQ (eρ A))) = frobE6 Fr (ρ A)
    rw [h1]
    rfl
  choose ε hε using fun (i j : Fin 3) (hij : i ≠ j) => hfr.transv i j hij
  let b : Fin 3 → Fin 3 → Ωˣ := fun i j =>
    if h : i = j then 1 else Units.map Fr.toMonoidHom (ε i j h) * (ε i j h)⁻¹
  have hTheta_transvection : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      Θ (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection hij ((b i j : Ω) * t ^ Nat.card K) := by
    intro i j hij t
    apply hfr.injective
    rw [hΘ, hε i j hij t, frobE6_pinnedX, hε i j hij ((b i j : Ω) * t ^ Nat.card K)]
    congr 1
    have hb : (b i j : Ω) = Fr (ε i j hij : Ω) * ((ε i j hij : Ω))⁻¹ := by
      simp [b, dif_neg hij]
    rw [hb, map_mul, hFr, hFr]
    field_simp
  let ιK : SL(3, K) →* SL(3, Ω) := Matrix.SpecialLinearGroup.map (algebraMap K Ω)
  have hιK : Function.Injective ιK :=
    CFSG.RankThree.Classical2.specialLinearGroup_map_injective (algebraMap K Ω).injective
  obtain ⟨p, -, n, hpn, hkcard⟩ := FiniteField.card' (K := K)
  have hp : p.Prime := hpn
  have hf : 1 ≤ (n : ℕ) := Nat.succ_le_of_lt n.pos
  have hk : Nat.card K = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hkcard
  have hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Θ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) =
        1 + single (Equiv.refl (Fin 3) i) (Equiv.refl (Fin 3) j)
          ((b i j : Ω) * t ^ p ^ (n : ℕ)) := by
    intro i j hij t
    rw [hTheta_transvection i j hij t, Matrix.SpecialLinearGroup.transvection_coe, ← hk]
    simp only [Equiv.refl_apply]
  obtain ⟨-, ⟨H, hH⟩, hfin, -, -, -⟩ :=
    CFSG.RankThree.Classical2.sln_root_permuting_frobenius_fixed_split
      (n := 3) hp hf hk (by norm_num) (Equiv.refl (Fin 3)) Θ b hΦ
  let A : Subgroup (ModGL Tag.E6 Ω) := (rootSpan Tag.E6 K S).map (baseChangeGL (algebraMap K Ω))
  let B : Subgroup (ModGL Tag.E6 Ω) := ρ.range ⊓ (frobE6 Fr).eqLocus (MonoidHom.id _)
  have hmap_le : (rootSpan Tag.E6 K S).map (baseChangeGL (algebraMap K Ω)) ≤
      rootSpan Tag.E6 Ω S := by
    rw [rootSpan_eq_closure (R := K), Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro g ⟨γ, hγ, c, rfl⟩
    show baseChangeGL (algebraMap K Ω) (pinnedX Tag.E6 K γ c) ∈ rootSpan Tag.E6 Ω S
    rw [baseChangeGL_pinnedX]
    exact pinnedX_mem_rootSpan hγ _
  have hle : A ≤ B := by
    intro x hx
    change x ∈ (rootSpan Tag.E6 K S).map (baseChangeGL (algebraMap K Ω)) at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hspan]
      exact hmap_le (Subgroup.mem_map_of_mem (baseChangeGL (algebraMap K Ω)) hy)
    · exact frobE6_baseChangeGL_eq hFr hy
  let eB : B ≃ fixSubgroup Θ :=
    Equiv.ofBijective (fun b : B =>
      ⟨eρ.symm ⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩, by
        rw [mem_fixSubgroup]
        apply hfr.injective
        have h1 : ρ (eρ.symm ⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩) = b.1 :=
          congrArg Subtype.val (eρ.apply_symm_apply ⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩)
        rw [hΘ, h1]
        exact (Subgroup.mem_inf.1 b.2).2⟩) (by
      constructor
      · intro b b' h
        have hA : eρ.symm ⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩ =
            eρ.symm ⟨b'.1, (Subgroup.mem_inf.1 b'.2).1⟩ := congrArg Subtype.val h
        have h2 := congrArg eρ hA
        rw [eρ.apply_symm_apply, eρ.apply_symm_apply] at h2
        exact Subtype.ext (congrArg (fun z : ρ.range => (z : ModGL Tag.E6 Ω)) h2)
      · intro X
        have hX : Θ X.1 = X.1 := X.2
        let b : B := ⟨ρ X.1, ⟨⟨X.1, rfl⟩, by
          change frobE6 Fr (ρ X.1) = ρ X.1
          rw [← hΘ X.1, hX]⟩⟩
        refine ⟨b, ?_⟩
        apply Subtype.ext
        change eρ.symm ⟨ρ X.1, _⟩ = X.1
        rw [eρ.symm_apply_eq]
        exact Subtype.ext rfl)
  have hBcard : Nat.card B = Nat.card (fixSubgroup Θ) := Nat.card_congr eB
  have hfixcard : Nat.card (fixSubgroup Θ) = Nat.card (SL(3, K)) := by
    let f : SL(3, K) → fixSubgroup Θ := fun Y =>
      ⟨H * ιK Y * H⁻¹, (hH _).mpr ⟨Y, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro Y Y' h
        have h1 : H * ιK Y * H⁻¹ = H * ιK Y' * H⁻¹ := congrArg Subtype.val h
        apply hιK
        calc ιK Y = H⁻¹ * (H * ιK Y * H⁻¹) * H := by group
          _ = H⁻¹ * (H * ιK Y' * H⁻¹) * H := by rw [h1]
          _ = ιK Y' := by group
      · intro X
        obtain ⟨Y, hY⟩ := (hH X.1).mp X.2
        exact ⟨Y, Subtype.ext hY.symm⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hcardA : Nat.card A = Nat.card (SL(3, K)) := by
    change Nat.card ((rootSpan Tag.E6 K S).map (baseChangeGL (algebraMap K Ω))) = _
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective (algebraMap K Ω))]
    rw [hspanK]
    exact (Nat.card_congr (MonoidHom.ofInjective hfrK.injective).toEquiv).symm
  have hcardB : Nat.card B = Nat.card (SL(3, K)) := hBcard.trans hfixcard
  have hcardBA : Nat.card B ≤ Nat.card A := by rw [hcardB, hcardA]
  haveI : Finite (fixSubgroup Θ) := hfin
  haveI : Finite B := Finite.of_injective (eB : B → fixSubgroup Θ) (Equiv.injective eB)
  have hAB : A = B := Subgroup.eq_of_le_of_card_ge hle hcardBA
  have hzB : z ∈ B := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hspan]; exact hz
    · exact hF
  rw [← hAB] at hzB
  change z ∈ (rootSpan Tag.E6 K S).map (baseChangeGL (algebraMap K Ω)) at hzB
  obtain ⟨y, hy, hyz⟩ := hzB
  exact ⟨y, hy, hyz⟩

end CFSG.StandardType.E6ThreeModel
