module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Nbr
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActEnd
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredDef
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore

public section

namespace CFSG.StandardType.U63TB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.StandardType.UnitAct
  CFSG.Assembly TableB

@[expose] def ActConcl (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ (H : Subgroup (MulAut L')) (W : Set L'), H ≤ A ∧ H ≠ ⊥ ∧
    (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ h ∈ H, MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ H) ∧
    (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
    (∀ A' : Subgroup (MulAut L'), A' ≤ A → A' ≠ ⊥ →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A') ∧
    (∀ a ∈ A, (∀ n ∈ W, MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1) ∧
    (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹ ∈ H) ∧
    (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ w ∈ W, ∀ a ∈ A, a (n * w⁻¹) = n * w⁻¹) ∧
    (∀ n ∈ W, n ∈ Subgroup.closure {m | m ∈ W ∧ m * m = 1}) ∧
    ∀ f : MulAut L' → MulAut L', (∀ a ∈ H, f a ∈ H) →
      (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a * f b) →
      (∀ n ∈ W, ∀ a ∈ H, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
        MulAut.conj n * f a * (MulAut.conj n)⁻¹) → ∃ c : ℕ, ∀ a ∈ H, f a = a ^ c

theorem act63_of_cover {n : ℕ} {K : Type} [Field K] [Finite K]
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
    ActConcl 3 A := by
  classical
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by simpa using hr
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    Line63.exists_diagModel_of hK hn (by norm_num) Nat.prime_three hpq (by norm_num) hperfSU hψ
      hker hperf hA hAI hcard hcov'
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hd : 5 ≤ 6 := by norm_num
  have hd3 : 3 ≤ 6 := by norm_num
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  set H := Subgroup.closure (heartSetU φ 3) with hH
  have hVA : heartSetU φ 3 ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  refine ⟨H, {x | ∃ σ : Equiv.Perm (Fin 6), x = φ (permSU hM.field σ)}, hHA, ?_, ?_,
    weyl_W_prop hM.field hd3 hM.ker hAp hdiag, ?_, eq_one_of_perm_fixed hM hd3 hdiag, ?_, ?_, ?_,
    ?_⟩
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
        (conj_mem_heart_of_normalizes hM hK hp hp2 hpq hd hA hsc hdiag hw hx)
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
    exact conj_mem_of_invariant hM hp hpq hd hA'A hsc hdiag hAp
      (fun σ a ha => hinv _ ⟨σ, rfl⟩ a ha) ha₀ ha₀1' hD hu
  · rintro x ⟨σ, rfl⟩ a ha
    exact conj_mul_inv_mem_heart hM hp hpq hd3 hAp hdiag σ ha
  · intro w hw
    exact exists_weyl_fix hM hK hp hp2 hpq (by omega) hA hsc hdiag hw
  · rintro x ⟨σ, rfl⟩
    exact perm_image_mem_closure hM.field φ σ
  · intro f hfH hfmul hfW
    exact heart_end_pow hM hp hp2 hpq hd hA hsc hdiag f hfH hfmul hfW

end CFSG.StandardType.U63TB

end
