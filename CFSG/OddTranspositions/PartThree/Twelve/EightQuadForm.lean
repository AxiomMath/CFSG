module

public import CFSG.OddTranspositions.PartThree.Twelve.EightDescent
public import CFSG.OddTranspositions.PartThree.Twelve.EightModel
import CFSG.OddTranspositions.PartThree.Twelve.MarkedEmbedding
import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.Orthogonal CFSG.LieType.BorelTits
open QuadraticMap

theorem exists_ringHom_fixed_unitaryInvolution {K F : Type} [Field K] [Finite K] [Field F]
    [Finite F] [CharP F 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ ι : K →+* F, ∀ c : F, unitaryInvolution F 2 f c = c ↔ ∃ k, ι k = c := by
  classical
  let _ := Fintype.ofFinite K
  let _ := Fintype.ofFinite (CFSG.LieType.Steinberg.fixedSubfield F 2 f)
  have hcard : Fintype.card K = Fintype.card (CFSG.LieType.Steinberg.fixedSubfield F 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.LieType.Steinberg.card_fixedSubfield hF]
  let φ := FiniteField.ringEquivOfCardEq (K := K)
    (K' := CFSG.LieType.Steinberg.fixedSubfield F 2 f) hcard
  refine ⟨(CFSG.LieType.Steinberg.fixedSubfield F 2 f).subtype.comp φ.toRingHom, fun c =>
    ⟨fun hc => ⟨φ.symm ⟨c, hc⟩, by simp⟩, ?_⟩⟩
  rintro ⟨k, rfl⟩
  exact CFSG.LieType.Steinberg.mem_fixedSubfield.1 (φ k).2

private theorem sum_ringHom_smul_injective {K F : Type} [Field K] [Field F] (ι : K →+* F)
    {e : Fin 4 → Fin 4 → F} (he : (Matrix.of e).det ≠ 0) :
    Function.Injective fun c : Fin 4 → K => ∑ i, ι (c i) • e i := by
  intro c c' h
  have hli : LinearIndependent F e :=
    Matrix.linearIndependent_rows_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he))
  have h0 : ∑ i, (ι (c i) - ι (c' i)) • e i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h
  funext i
  exact ι.injective (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i))

private theorem sum_ringHom_smul_single {K F : Type} [Field K] [Field F] (ι : K →+* F)
    (e : Fin 4 → Fin 4 → F) (j : Fin 4) :
    ∑ i, ι ((Pi.single j (1 : K) : Fin 4 → K) i) • e i = e j := by
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, map_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, map_one, one_smul]

private theorem smul_sum_ringHom_smul {K F : Type} [Field K] [Field F] (ι : K →+* F)
    (e : Fin 4 → Fin 4 → F) (k : K) (c : Fin 4 → K) :
    ι k • ∑ i, ι (c i) • e i = ∑ i, ι ((k • c) i) • e i := by
  simp only [Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul, map_mul]

theorem exists_isFixedQuadForm_of_quadraticForm {K F : Type} [Field K] [Field F] {σ : F ≃+* F}
    (ι : K →+* F) (hι : ∀ c : F, σ c = c ↔ ∃ k, ι k = c) {e : Fin 4 → Fin 4 → F}
    (he : (Matrix.of e).det ≠ 0) (Q' : QuadraticForm K (Fin 4 → K))
    (hQ' : ∀ c c' : Fin 4 → K,
      ι (polar Q' c c') = herm σ (∑ i, ι (c i) • e i) (∑ i, ι (c' i) • e i)) :
    ∃ (U : AddSubgroup (Fin 4 → F)) (Q : (Fin 4 → F) → F), IsFixedQuadForm σ U Q ∧
      (∀ c : Fin 4 → K, ∑ i, ι (c i) • e i ∈ U ∧ Q (∑ i, ι (c i) • e i) = ι (Q' c)) ∧
      ∀ v ∈ U, ∃ c : Fin 4 → K, v = ∑ i, ι (c i) • e i := by
  classical
  let Φ : (Fin 4 → K) →+ (Fin 4 → F) :=
    { toFun := fun c => ∑ i, ι (c i) • e i
      map_zero' := by simp
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib] }
  have hinj : Function.Injective Φ := sum_ringHom_smul_injective ι he
  have hsmul : ∀ (k : K) (d : Fin 4 → K), ι k • Φ d = Φ (k • d) := smul_sum_ringHom_smul ι e
  have hfixι : ∀ k, σ (ι k) = ι k := fun k => (hι _).2 ⟨k, rfl⟩
  have hQ'Φ : ∀ c c', ι (polar Q' c c') = herm σ (Φ c) (Φ c') := hQ'
  let Q : (Fin 4 → F) → F := fun v => ι (Q' (Function.invFun Φ v))
  have hQΦ : ∀ c, Q (Φ c) = ι (Q' c) := fun c => by
    show ι (Q' (Function.invFun Φ (Φ c))) = _
    rw [Function.leftInverse_invFun hinj c]
  refine ⟨Φ.range, Q, ⟨?_, ?_, ?_, ?_, ?_⟩, fun c => ⟨⟨c, rfl⟩, hQΦ c⟩, ?_⟩
  · rintro c hc _ ⟨d, rfl⟩
    obtain ⟨k, rfl⟩ := (hι c).1 hc
    exact ⟨k • d, (hsmul k d).symm⟩
  · refine ⟨e, fun i => ⟨Pi.single i 1, sum_ringHom_smul_single ι e i⟩, he, ?_⟩
    rintro _ ⟨d, rfl⟩
    exact ⟨fun i => ι (d i), fun i => hfixι _, rfl⟩
  · rintro _ ⟨d, rfl⟩
    rw [hQΦ]
    exact hfixι _
  · rintro c hc _ ⟨d, rfl⟩
    obtain ⟨k, rfl⟩ := (hι c).1 hc
    rw [hsmul, hQΦ, hQΦ, QuadraticMap.map_smul, smul_eq_mul, map_mul, map_mul]
    ring
  · rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩
    rw [← map_add Φ d d', hQΦ, hQΦ, hQΦ, QuadraticMap.map_add Q', map_add ι, map_add ι, hQ'Φ]
  · rintro _ ⟨d, rfl⟩
    exact ⟨d, rfl⟩

theorem exists_isFixedQuadForm_of_exactMarked {K F : Type} [Field K] [Finite K] [CharP K 2]
    [Field F] {σ : F ≃+* F} (hinv : ∀ c, σ (σ c) = c) (ι : K →+* F)
    (hι : ∀ c : F, σ c = c ↔ ∃ k, ι k = c) {Q₀ : QuadraticForm K (Fin 4 → K)}
    (hQ₀ : Q₀.polarBilin.Nondegenerate) {e : Fin 4 → Fin 4 → F}
    (hGram : ∀ i j, σ (herm σ (e i) (e j)) = herm σ (e i) (e j))
    (halt : ∀ i, herm σ (e i) (e i) = 0) (he : (Matrix.of e).det ≠ 0)
    {a : (Fin 4 → K) → (Fin 4 → F)}
    (hmem : ∀ y, Q₀ y = 1 → ∃ c : Fin 4 → F, (∀ i, σ (c i) = c i) ∧ a y = ∑ i, c i • e i)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → (herm σ (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    (hA3 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 →
      a (reflect Q₀ x y) = a y + herm σ (a x) (a y) • a x)
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q₀ ≤
      Subgroup.closure (reflect Q₀ '' {v | Q₀ v = 1})) :
    ∃ (U : AddSubgroup (Fin 4 → F)) (Q : (Fin 4 → F) → F), IsFixedQuadForm σ U Q ∧
      (∀ y, Q₀ y = 1 → a y ∈ U ∧ Q (a y) = 1) ∧
      ∀ v ∈ U, Q v = 1 → ∃ y, Q₀ y = 1 ∧ v = a y := by
  classical
  let Φ : (Fin 4 → K) →+ (Fin 4 → F) :=
    { toFun := fun c => ∑ i, ι (c i) • e i
      map_zero' := by simp
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib] }
  have hΦ : ∀ c, Φ c = ∑ i, ι (c i) • e i := fun _ => rfl
  have hinj : Function.Injective Φ := sum_ringHom_smul_injective ι he
  have hsmul : ∀ (k : K) (d : Fin 4 → K), Φ (k • d) = ι k • Φ d :=
    fun k d => (smul_sum_ringHom_smul ι e k d).symm
  have hfixι : ∀ k, σ (ι k) = ι k := fun k => (hι _).2 ⟨k, rfl⟩
  have hg : ∀ i j, ∃ g : K, ι g = herm σ (e i) (e j) := fun i j => (hι _).1 (hGram i j)
  choose g hg using hg
  have hg0 : ∀ i, g i i = 0 := fun i => ι.injective (by rw [hg, halt, map_zero])
  have hgs : ∀ i j, g j i = g i j := fun i j =>
    ι.injective (by rw [hg, hg, herm_conj σ hinv (e i) (e j), hGram])
  have hsl : ∀ (u : Fin 4 → Fin 4 → F) (w : Fin 4 → F),
      herm σ (∑ i, u i) w = ∑ i, herm σ (u i) w := by
    intro u w
    simp only [herm, Finset.sum_apply, map_sum, Finset.sum_mul]
    exact Finset.sum_comm
  have hsr : ∀ (v : Fin 4 → F) (u : Fin 4 → Fin 4 → F),
      herm σ v (∑ j, u j) = ∑ j, herm σ v (u j) := by
    intro v u
    simp only [herm, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  let b : LinearMap.BilinForm K (Fin 4 → K) := Matrix.toBilin' (Matrix.of g)
  have hb : ∀ c c', ι (b c c') = herm σ (Φ c) (Φ c') := by
    intro c c'
    simp only [b, Matrix.toBilin'_apply, Matrix.of_apply, map_sum, map_mul, hg, hΦ, hsl, hsr,
      herm_smul_left, herm_smul_right, hfixι]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hbalt : ∀ v, b v v = 0 := by
    intro v
    have hK2 : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [b, Matrix.toBilin'_apply, Matrix.of_apply, Fin.sum_univ_four]
    linear_combination v 0 ^ 2 * hg0 0 + v 1 ^ 2 * hg0 1 + v 2 ^ 2 * hg0 2 + v 3 ^ 2 * hg0 3 +
      v 0 * v 1 * hgs 0 1 + v 0 * v 2 * hgs 0 2 + v 0 * v 3 * hgs 0 3 + v 1 * v 2 * hgs 1 2 +
      v 1 * v 3 * hgs 1 3 + v 2 * v 3 * hgs 2 3 +
      (v 0 * v 1 * g 0 1 + v 0 * v 2 * g 0 2 + v 0 * v 3 * g 0 3 + v 1 * v 2 * g 1 2 +
        v 1 * v 3 * g 1 3 + v 2 * v 3 * g 2 3) * hK2
  have hbnd : ∀ v, (∀ w, b v w = 0) → v = 0 := by
    intro v hv
    have hz : ∀ j, herm σ (Φ v) (e j) = 0 := by
      intro j
      have hej : Φ (Pi.single j 1) = e j := sum_ringHom_smul_single ι e j
      rw [← hej, ← hb, hv, map_zero]
    have hli : LinearIndependent F e :=
      Matrix.linearIndependent_rows_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he))
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp)
    have hΦv : Φ v = 0 := by
      refine eq_zero_of_herm σ fun u => ?_
      have hle : Submodule.span F (Set.range e) ≤ LinearMap.ker (hermL σ (Φ v)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        simpa using hz j
      have hu : u ∈ Submodule.span F (Set.range e) := by
        rw [htop]
        exact Submodule.mem_top
      simpa using hle hu
    exact hinj (by rw [hΦv, map_zero])
  have hmemΦ : ∀ y, Q₀ y = 1 → ∃ c, Φ c = a y := by
    intro y hy
    obtain ⟨c, hc, hcy⟩ := hmem y hy
    have hk : ∀ i, ∃ k : K, ι k = c i := fun i => (hι _).1 (hc i)
    choose k hk using hk
    exact ⟨k, by rw [hΦ, hcy]; simp only [hk]⟩
  let φ : (Fin 4 → K) → (Fin 4 → K) := fun y => Function.invFun Φ (a y)
  have hφ : ∀ y, Q₀ y = 1 → Φ (φ y) = a y := fun y hy => Function.invFun_eq (hmemΦ y hy)
  have hherm : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → ι (b (φ x) (φ y)) = herm σ (a x) (a y) :=
    fun x hx y hy => by rw [hb, hφ x hx, hφ y hy]
  have hfixh : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → σ (herm σ (a x) (a y)) = herm σ (a x) (a y) :=
    fun x hx y hy => by rw [← hherm x hx y hy, hfixι]
  have hconj : ∀ w x, Q₀ w = 1 → Q₀ x = 1 →
      φ (reflect Q₀ w x) = φ x + b (φ x) (φ w) • φ w := by
    intro w x hw hx
    have hr : Q₀ (reflect Q₀ w x) = 1 := by
      rw [map_of_mem (reflect_mem_orthogonalGroup Q₀ w) x, hx]
    apply hinj
    rw [hφ _ hr, map_add Φ, hsmul, hφ x hx, hφ w hw, hherm x hx w hw, hA3 w hw x hx,
      herm_conj σ hinv (a w) (a x), hfixh w hw x hx]
  have hcomm : ∀ x y, Q₀ x = 1 → Q₀ y = 1 → (b (φ x) (φ y) = 0 ↔ polar Q₀ x y = 0) := by
    intro x y hx hy
    rw [← hA2 x hx y hy, ← hherm x hx y hy, map_eq_zero_iff ι ι.injective]
  obtain ⟨Q', hQ'b, hQ'1, -⟩ := exists_quadraticForm_of_marked (Q := Q₀) (b := b) (φ := φ) hQ₀
    (by simp) hbalt hbnd rfl rfl hconj hcomm hgen
  obtain ⟨U, Q, hUQ, hΦU, hU⟩ := exists_isFixedQuadForm_of_quadraticForm ι hι he Q'
    fun c c' => (congrArg ι (hQ'b c c')).trans (hb c c')
  refine ⟨U, Q, hUQ, fun y hy => ?_, fun v hv hQv => ?_⟩
  · obtain ⟨hmemU, hQy⟩ := hΦU (φ y)
    have h1 : Q' (φ y) = 1 := (hQ'1 _).2 ⟨y, hy, rfl⟩
    rw [← hφ y hy]
    exact ⟨hmemU, hQy.trans (by rw [h1, map_one])⟩
  · obtain ⟨c, rfl⟩ := hU v hv
    obtain ⟨-, hQc⟩ := hΦU c
    have h1 : Q' c = 1 := ι.injective (by rw [map_one, ← hQc, hQv])
    obtain ⟨x, hx, rfl⟩ := (hQ'1 c).1 h1
    exact ⟨x, hx, hφ x hx⟩

theorem exists_isFixedQuadForm_of_unitaryMarked {K F : Type} [Field K] [Finite K] [CharP K 2]
    [Field F] [Finite F] [CharP F 2] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hK4 : 4 ≤ Nat.card K) {Q₀ : QuadraticForm K (Fin 4 → K)}
    (hQ₀ : Q₀.polarBilin.Nondegenerate) {a : (Fin 4 → K) → (Fin 4 → F)}
    (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧ herm (unitaryInvolution F 2 f) (a y) (a y) = 0)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 →
      (herm (unitaryInvolution F 2 f) (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    (hA3 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → ∃ μ : F, unitaryInvolution F 2 f μ * μ = 1 ∧
      a (reflect Q₀ x y) = μ • (a y + herm (unitaryInvolution F 2 f) (a x) (a y) • a x))
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q₀ ≤
      Subgroup.closure (reflect Q₀ '' {v | Q₀ v = 1})) :
    ∃ (U : AddSubgroup (Fin 4 → F)) (Q : (Fin 4 → F) → F),
      IsFixedQuadForm (unitaryInvolution F 2 f) U Q ∧
      (∀ y, Q₀ y = 1 → ∃ μ : F, unitaryInvolution F 2 f μ * μ = 1 ∧ μ • a y ∈ U ∧
        Q (μ • a y) = 1) ∧
      ∀ v ∈ U, Q v = 1 → ∃ y, Q₀ y = 1 ∧ ∃ μ : F, unitaryInvolution F 2 f μ * μ = 1 ∧
        v = μ • a y := by
  have hinv : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨e, a', hGram, halt, hdet, ha'μ, hmem, hA3'⟩ :=
    exists_fixedSpan_centres hinv hK4 hQ₀ hA1 hA2 hA3
  obtain ⟨ι, hι⟩ := exists_ringHom_fixed_unitaryInvolution hK hF
  have hA2' : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 →
      (herm (unitaryInvolution F 2 f) (a' x) (a' y) = 0 ↔ polar Q₀ x y = 0) := by
    intro x hx y hy
    obtain ⟨μ, hμ, hμx⟩ := ha'μ x hx
    obtain ⟨ν, hν, hνy⟩ := ha'μ y hy
    rw [hμx, hνy, herm_smul_left, herm_smul_right, ← hA2 x hx y hy]
    have hμ0 : unitaryInvolution F 2 f μ ≠ 0 := by
      intro h
      simp [h] at hμ
    have hν0 : ν ≠ 0 := by
      rintro rfl
      simp at hν
    constructor
    · intro h
      exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hμ0)).resolve_left hν0
    · intro h
      rw [h, mul_zero, mul_zero]
  obtain ⟨U, Q, hUQ, h1, h2⟩ :=
    exists_isFixedQuadForm_of_exactMarked hinv ι hι hQ₀ hGram halt hdet hmem hA2' hA3' hgen
  refine ⟨U, Q, hUQ, fun y hy => ?_, fun v hv hQv => ?_⟩
  · obtain ⟨μ, hμ, hy'⟩ := ha'μ y hy
    exact ⟨μ, hμ, by rw [← hy']; exact h1 y hy⟩
  · obtain ⟨y, hy, rfl⟩ := h2 v hv hQv
    obtain ⟨μ, hμ, hy'⟩ := ha'μ y hy
    exact ⟨y, hy, μ, hμ, hy'⟩

end CFSG.OddTranspositions.PartThree

end
