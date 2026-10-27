module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModelLift
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModelWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open scoped commutatorElement

theorem sympMinus_map_conj_centralizer {G : Type*} [Group G] (g a : G) :
    (Subgroup.centralizer ({g * a * g⁻¹} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
      = Subgroup.centralizer ({a} : Set G) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    change (MulAut.conj g⁻¹) y * a = a * (MulAut.conj g⁻¹) y
    rw [MulAut.conj_apply]
    calc g⁻¹ * y * g⁻¹⁻¹ * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [hy]
      _ = a * (g⁻¹ * y * g⁻¹⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
        _ = g * (a * x) * g⁻¹ := by rw [hx]
        _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
    · change (MulAut.conj g⁻¹) (g * x * g⁻¹) = x
      rw [MulAut.conj_apply]
      group

theorem sympMinus_map_centralizer_singleton_mulEquiv {M M' : Type*} [Group M] [Group M']
    (φ : M ≃* M') (t : M) :
    (Subgroup.centralizer ({t} : Set M)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ t} : Set M') := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    change φ y * φ t = φ t * φ y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine Subgroup.mem_map.mpr ⟨φ.symm x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
    · simp

theorem sympMinus_injective_of_surjective_natCard {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (hf : Function.Surjective f) (hcard : Nat.card α ≤ Nat.card β) :
    Function.Injective f := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  have hle : Nat.card β ≤ Nat.card α := Nat.card_le_card_of_surjective f hf
  have heq : Nat.card α = Nat.card β := le_antisymm hcard hle
  let e : α ≃ β := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact heq)
  have hg : Function.Surjective (fun a : α => e.symm (f a)) := fun b => by
    obtain ⟨a, ha⟩ := hf (e b)
    exact ⟨a, by
      change e.symm (f a) = b
      rw [ha, e.symm_apply_apply]⟩
  have hgi : Function.Injective (fun a : α => e.symm (f a)) :=
    Finite.injective_iff_surjective.mpr hg
  intro a b hab
  exact hgi (congrArg e.symm hab)

theorem sympMinus_range_conj_subset_matConjImage {K : Type} [Field K] [Finite K] [CharP K 2]
    (m : ℕ) [NeZero m] :
    Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
  classical
  rintro φ ⟨r, rfl⟩
  let e : ↥(LargeEvenSpGroup K m) ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨AutPSp.proj_injective (n := m) (K := K), QuotientGroup.mk'_surjective _⟩
  let A : ↥(LargeEvenSpGroup K m) := e.symm r
  have hA : LargeEvenProjMk (LargeEvenSpGroup K m) A = r := e.apply_symm_apply r
  refine ⟨(A : GL (Fin m ⊕ Fin m) K), ?_, ?_⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul]
    exact mem_statedSp_iff.mp A.2
  · intro h h' hrel
    have hrelH : h' = A * h * A⁻¹ := Subtype.ext hrel
    change MulAut.conj r (LargeEvenProjMk (LargeEvenSpGroup K m) h) =
      LargeEvenProjMk (LargeEvenSpGroup K m) h'
    rw [hrelH, map_mul, map_mul, map_inv, MulAut.conj_apply, hA]

theorem sympMinus_commutatorElement_mul_right_central {G : Type*} [Group G] {x y z : G}
    (hz : z ∈ Subgroup.center G) : ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have hc := Subgroup.mem_center_iff.mp hz
  calc ⁅x, y * z⁆ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by rw [commutatorElement_def]; group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [← hc x⁻¹]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem sympMinus_commutatorElement_mul_left_of_commute {G : Type*} [Group G] {u v w : G}
    (h : v * w = w * v) : ⁅u * v, w⁆ = ⁅u, w⁆ := by
  calc ⁅u * v, w⁆ = u * (v * w) * v⁻¹ * u⁻¹ * w⁻¹ := by rw [commutatorElement_def]; group
    _ = u * (w * v) * v⁻¹ * u⁻¹ * w⁻¹ := by rw [h]
    _ = ⁅u, w⁆ := by rw [commutatorElement_def]; group

theorem sympMinus_pow_eq_one_of_conj_eq_mul_center {G : Type*} [Group G] {s j z : G}
    (hzc : ∀ x, z * x = x * z) (h : s * j * s⁻¹ = z * j) {p : ℕ} (hsp : s ^ p = 1) :
    z ^ p = 1 := by
  have hsje : s * j = j * (z * s) := by
    have h2 : (s * j * s⁻¹) * s = (z * j) * s := congrArg (· * s) h
    calc s * j = (s * j * s⁻¹) * s := by group
      _ = (z * j) * s := h2
      _ = j * (z * s) := by rw [hzc j]; group
  have hsz : ∀ k : ℕ, s * z ^ k = z ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
        calc s * z ^ (k + 1) = s * (z ^ k * z) := by rw [pow_succ]
          _ = (s * z ^ k) * z := by group
          _ = (z ^ k * s) * z := by rw [ihk]
          _ = z ^ k * (s * z) := by group
          _ = z ^ k * (z * s) := by rw [hzc s]
          _ = z ^ (k + 1) * s := by rw [pow_succ]; group
  have key : ∀ k : ℕ, s ^ k * j = j * z ^ k * s ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc s ^ (k + 1) * j = s * (s ^ k * j) := by rw [pow_succ]; group
          _ = s * (j * z ^ k * s ^ k) := by rw [ih]
          _ = (s * j) * z ^ k * s ^ k := by group
          _ = (j * (z * s)) * z ^ k * s ^ k := by rw [hsje]
          _ = j * z * (s * z ^ k) * s ^ k := by group
          _ = j * z * (z ^ k * s) * s ^ k := by rw [hsz k]
          _ = j * z ^ (k + 1) * s ^ (k + 1) := by rw [pow_succ]; group
  have h1 : j * 1 = j * z ^ p := by
    rw [mul_one]
    have hk := key p
    rw [hsp, one_mul, mul_one] at hk
    exact hk
  exact (mul_left_cancel h1).symm

end CFSG.StandardType.SympMinus

end
