module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdMod

public section

namespace CFSG.StandardType.U63TB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

theorem mod63_of_cover {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ 4 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    ModConcl 3 A := by
  classical
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by simpa using hr
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    Line63.exists_diagModel_of hK hn (by norm_num) Nat.prime_three hpq (by norm_num) hperfSU hψ
      hker hperf hA hAI hcard hcov'
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have hM : Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hd5 : 5 ≤ 6 := by norm_num
  have hd3 : 3 ≤ 6 := by norm_num
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp3 hpq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp3.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp3.one_lt
  set H := Subgroup.closure (heartSetU φ 3) with hH
  have hVA : heartSetU φ 3 ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  refine ⟨H, {x | ∃ σ : Equiv.Perm (Fin 6), x = φ (permSU hM.field σ)}, hHA, ?_,
    card_le_mul_card_heart hM hpq hp3 hd3 hAp hdiag, ?_,
    weyl_W_prop hM.field hd3 hM.ker hAp hdiag, ?_⟩
  · intro hbot
    set i0 : Fin 6 := ⟨0, by omega⟩
    set i1 : Fin 6 := ⟨1, by omega⟩
    set i2 : Fin 6 := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hi02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have hi12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    obtain ⟨D₁, hD₁⟩ := exists_diagSU hM.field hpq (u := TypeA.rootT ζ i0 i1)
      (fun k => TypeA.rootT_pow hζ.pow_eq_one i0 i1 k) (TypeA.prod_rootT hζ0 h01)
    have he₁ : MulAut.conj (φ D₁) ∈ H :=
      Subgroup.subset_closure ⟨D₁, _, hD₁, TypeA.rootT_pow hζ.pow_eq_one i0 i1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at he₁
    have h2 : ActsDiagU φ (MulAut.conj (φ D₁)) (fun _ => (1 : K)) := by
      rw [he₁]
      exact actsDiagU_one φ
    have h3' := (actsDiagU_conj (φ := φ) hD₁).ratio_eq hM.field hd3 hM.ker h2 i0 i2
    rw [TypeA.rootT_left, TypeA.rootT_other ζ (Ne.symm hi02) (Ne.symm hi12)] at h3'
    simp only [inv_one, mul_one] at h3'
    exact hζ1 h3'
  · intro w hw h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      exact Subgroup.subset_closure
        (conj_mem_heart_of_normalizes hM hK hp3 hp2 hpq hd5 hA hsc hdiag hw hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : MulAut.conj w * (x * y) * (MulAut.conj w)⁻¹ =
          (MulAut.conj w * x * (MulAut.conj w)⁻¹) * (MulAut.conj w * y * (MulAut.conj w)⁻¹) := by
        group
      rw [e]
      exact H.mul_mem hx hy
    | inv x _ hx =>
      have e : MulAut.conj w * x⁻¹ * (MulAut.conj w)⁻¹ =
          (MulAut.conj w * x * (MulAut.conj w)⁻¹)⁻¹ := by group
      rw [e]
      exact H.inv_mem hx
  · intro A' hA'A hA'ne hinv
    obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'ne
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    refine (Subgroup.closure_le A').mpr ?_
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_invariant hM hp3 hpq hd5 hA'A hsc hdiag hAp
      (fun σ a ha => hinv _ ⟨σ, rfl⟩ a ha) ha₀ ha₀1' hD hu

section Certificates


theorem ggTableBModuleSCr_unitary63_big {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTableBModuleSCr 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc
  have hcov := unitaryUniversalCover_holds n 6 K hK (by norm_num)
    (fun h => absurd (congrArg Prod.snd h) (by omega))
  exact mod63_of_cover hK (by omega) hpq hcov.1
    (fun ψ'' hs hk => hcov.2 L' ψ'' hs (hk ▸ hker) hperf) hψ hker hperf hA hAI hr hsc

theorem ggTableBModuleSCr_unitary63_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGTableBModuleSCr 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc
  have hcov := unitaryCoverOddAt_six_two K (by norm_num [hK])
  exact modConcl_descent hker hψ hperf hA hAI hsc
    (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc hsc₁ =>
      mod63_of_cover hK le_rfl (by norm_num) hcov.1
        (fun ψ'' hs'' hk'' => hcov.2 L₁ ψ'' hs'' (hk'' ▸ hk) hp (hk'' ▸ hodd)) hs hk hp hA₁ hAI₁
        (by rw [hc]; exact hr) hsc₁)

theorem ggTableBModuleSCr_unitary63 {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTableBModuleSCr 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact ggTableBModuleSCr_unitary63_two hK
  · exact ggTableBModuleSCr_unitary63_big hK h hpq

end Certificates

end CFSG.StandardType.U63TB

end
