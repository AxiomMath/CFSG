module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdCent
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLModPSL
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeAMono

public section

namespace CFSG.StandardType.UnitTB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.Assembly TableB

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

@[expose] def heartSetU (φ : ↥(unitarySU 2 n K d) →* L') (p : ℕ) : Set (MulAut L') :=
  {a | ∃ (D : ↥(unitarySU 2 n K d)) (u : Fin d → K),
    ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u ∧ (∀ i, u i ^ p = 1) ∧
      a = MulAut.conj (φ D)}

theorem card_le_mul_card_heart [Finite K] [Finite L'] (hM : Model φ) (hpq : p ∣ 2 ^ n + 1)
    (hp : p.Prime) (hd : 3 ≤ d) {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) :
    Nat.card A ≤ p * Nat.card (Subgroup.closure (heartSetU φ p)) := by
  classical
  have := Fact.mk hp
  choose tA htA' using fun a : A => hdiag a a.2
  have htA : ∀ a : A, ActsDiagU φ a (tA a) := htA'
  set i0 : Fin d := ⟨0, by omega⟩
  have hne : ∀ (a : A) k, tA a k ≠ 0 := fun a k => (htA a).ne_zero k
  have hrat : ∀ (a : A) (t : Fin d → K), ActsDiagU φ a t →
      ∀ k, tA a k * (tA a i0)⁻¹ = t k * (t i0)⁻¹ := fun a t ht k =>
    (htA a).ratio_eq hM.field hd hM.ker ht k i0
  let χf : A → Kˣ := fun a => Units.mk0 (∏ k, tA a k * (tA a i0)⁻¹)
    (Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (hne a k) (inv_ne_zero (hne a i0)))
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    apply Units.ext
    simp only [χf, Units.val_mk0, Units.val_mul]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hrat (a * b) _ (actsDiagU_mul (htA a) (htA b)) k, mul_inv, mul_mul_mul_comm]
  let χ : A →* Kˣ := MonoidHom.mk' χf hχmul
  have hrange : χ.range ≤ rootsOfUnity p K := by
    rintro _ ⟨a, rfl⟩
    rw [mem_rootsOfUnity']
    change (∏ k, tA a k * (tA a i0)⁻¹) ^ p = 1
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun k _ => (htA a).ratio_pow hM.field hd hM.ker (hAp a a.2) k i0
  have hker : ∀ a : A, χ a = 1 → (a : MulAut L') ∈ heartSetU φ p := by
    intro a ha
    have h1 : ∏ k, tA a k * (tA a i0)⁻¹ = 1 := by
      have := congrArg Units.val ha
      simpa [χ, χf] using this
    have hpow : ∀ k, (tA a k * (tA a i0)⁻¹) ^ p = 1 := fun k =>
      (htA a).ratio_pow hM.field hd hM.ker (hAp a a.2) k i0
    obtain ⟨D, hD⟩ := exists_diagSU hM.field hpq hpow h1
    exact ⟨D, _, hD, hpow, actsDiagU_unique hM.surj
      (actsDiagU_mul_const (htA a) (inv_ne_zero (hne a i0))) (actsDiagU_conj hD)⟩
  have hc1 := card_range_mul_card_ker χ
  have hc2 : Nat.card χ.range ≤ p :=
    (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity K p)
  have hc3 : Nat.card χ.ker ≤ Nat.card (Subgroup.closure (heartSetU φ p)) := by
    have hle : χ.ker.map A.subtype ≤ Subgroup.closure (heartSetU φ p) := by
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.subset_closure (hker a ha)
    calc Nat.card χ.ker = Nat.card (χ.ker.map A.subtype) :=
          (Subgroup.card_map_of_injective A.subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  rw [← hc1]
  exact Nat.mul_le_mul hc2 hc3

theorem conj_mem_heart_of_normalizes [Finite K] (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {w : L'}
    (hw : MulAut.conj w ∈ Subgroup.normalizer (A : Set (MulAut L'))) {h : MulAut L'}
    (hh : h ∈ heartSetU φ p) :
    MulAut.conj w * h * (MulAut.conj w)⁻¹ ∈ heartSetU φ p := by
  classical
  obtain ⟨g, rfl⟩ := hM.surj w
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpv : ∀ k l m : Fin d, TypeA.ggPairVec k l ζ m ^ p = 1 := fun k l m =>
    TypeA.pow_ggPairVec hζ.pow_eq_one m
  have hDex : ∀ k l : Fin d, k ≠ l → ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec k l ζ) :=
    fun k l _ => exists_diagSU hM.field hpq (fun m => hpv k l m) (TypeA.prod_ggPairVec ζ hζ0)
  have hconj : ∀ s : ↥(unitarySU 2 n K d),
      MulAut.conj (φ (g * s * g⁻¹)) =
        MulAut.conj (φ g) * MulAut.conj (φ s) * (MulAut.conj (φ g))⁻¹ := by
    intro s
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D' : Fin d → K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal (TypeA.rootT ζ i j) =
        diagonal D' * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    obtain ⟨Dij, hDij⟩ := exists_diagSU hM.field hpq (u := TypeA.rootT ζ i j)
      (fun k => TypeA.rootT_pow hζ.pow_eq_one i j k) (TypeA.prod_rootT hζ0 hij)
    set X := g * Dij * g⁻¹ with hX
    have hXA : MulAut.conj (φ X) ∈ A := by
      have h1 : MulAut.conj (φ Dij) ∈ A :=
        conj_mem_of_selfCent hsc hdiag hDij (TypeA.rootT_pow hζ.pow_eq_one i j)
      rw [hX, hconj]
      exact (Subgroup.mem_normalizer_iff.mp hw _).mp h1
    have hXd : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag :=
      isDiag_of_conj_comm hM hK (by omega) hζinv hDex fun k l _ D hD =>
        IsElemAbelian.comm hA hXA (conj_mem_of_selfCent hsc hdiag hD (hpv k l))
    refine ⟨fun k => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k, ?_⟩
    have e1 : X * g = g * Dij := by rw [hX]; group
    have e2 := congrArg (fun y : ↥(unitarySU 2 n K d) =>
      ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) e1
    simp only [Subgroup.coe_mul, Units.val_mul] at e2
    have hXm : ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal fun k => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k :=
      ((isDiag_iff_diagonal_diag _).mp hXd).symm
    rw [← hDij, ← e2]
    exact congrArg (· * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hXm
  obtain ⟨π, hπ⟩ := TypeA.exists_perm_mul_diagonal hζinv (g : GL (Fin d) K) hmono
  obtain ⟨D, u, hD, hu, rfl⟩ := hh
  have hgg : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      (((g : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDπ : ∀ i, (u ∘ π) i ^ p = 1 := fun i => hu (π i)
  have hmat : ((g * D * g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      (g : GL (Fin d) K) * D * (g : GL (Fin d) K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨g * D * g⁻¹, u ∘ π, ?_, hDπ, (hconj D).symm⟩
  have h1 := hπ u
  rw [hmat, Units.val_mul, Units.val_mul, hD, h1, Matrix.mul_assoc, hgg, Matrix.mul_one]

theorem ggTableBModuleSCr_unitary
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGTableBModuleSCr p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have := Fact.mk hp
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hrank : ggUnitaryTorusRank p d = d - 3 := by simp [ggUnitaryTorusRank, hpd]
  rw [hrank] at hr
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn hd hp hpq hpd
    (unitaryUniversalCover_holds n d K hK hd hdnd) hψ hker hperf hA hAI hcard
  haveI : Finite (MulAut L') := Finite.of_injective (fun f : MulAut L' => (f : L' → L'))
    DFunLike.coe_injective
  have hM : Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  have hd3 : 3 ≤ d := by omega
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  set H := Subgroup.closure (heartSetU φ p) with hH
  have hVA : heartSetU φ p ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  refine ⟨H, {x | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)}, hHA, ?_,
    card_le_mul_card_heart hM hpq hp hd3 hAp hdiag, ?_,
    weyl_W_prop hM.field hd3 hM.ker hAp hdiag, ?_⟩
  · intro hbot
    set i0 : Fin d := ⟨0, by omega⟩
    set i1 : Fin d := ⟨1, by omega⟩
    set i2 : Fin d := ⟨2, by omega⟩
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

end CFSG.StandardType.UnitTB

end
