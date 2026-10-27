module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev GGDepAE (p N : ℕ) : Type := Fin N → ZMod p

@[expose] def ggDepAdot {p N : ℕ} (a v : GGDepAE p N) : ZMod p := ∑ j, a j * v j

@[expose] def ggDepAh (p N : ℕ) (i : Fin (N - 1)) : GGDepAE p N := fun j =>
  if j.val + 1 = N then 0
  else (if j.val = i.val then 1 else 0) - (if j.val = i.val + 1 then 1 else 0) +
    (if i.val + 2 = N then 1 else 0)

@[expose] def ggDepAα (p N : ℕ) (i : Fin (N - 1)) : GGDepAE p N := fun j =>
  if j.val + 1 = N then 0 else (if j.val = i.val then 1 else 0) - (if j.val = i.val + 1 then 1 else
  0)

@[expose] def ggDepAx (p N : ℕ) : GGDepAE p N := fun j => if j.val + 1 = N then 1 else 0

@[expose] def ggDepAform {p N : ℕ} (f : GGDepAE p N) : GGDepAE p N →ₗ[ZMod p] ZMod p :=
  ∑ j, f j • LinearMap.proj j

@[expose] def ggDepARefl {p N : ℕ} (c f : GGDepAE p N) : Module.End (ZMod p) (GGDepAE p N) :=
  LinearMap.id - (ggDepAform f).smulRight c

@[expose] def GGDepAIsTv {p N : ℕ} (g : Module.End (ZMod p) (GGDepAE p N)) : Prop :=
  Module.finrank (ZMod p) (LinearMap.range (g - LinearMap.id)) = 1 ∧ ∀ w, g (g w - w) = g w - w

@[expose] def GGDepAPat (N : ℕ) (b c0 : Fin (N - 1)) (m n : ℤ) : Prop :=
  (b.val = 0 ∨ b.val + 2 = N) ∧ c0 ≠ b ∧
    (((if b.val = 0 then c0.val - 1 else c0.val) = 0 ∨
        (if b.val = 0 then c0.val - 1 else c0.val) + 1 = N - 2) ∧
      ((m = -1 ∧ n = -1) ∨ (m = -1 ∧ n = -2) ∨ (m = -2 ∧ n = -1)) ∨
    3 ≤ N - 2 ∧ ((if b.val = 0 then c0.val - 1 else c0.val) = 1 ∨
        (if b.val = 0 then c0.val - 1 else c0.val) + 2 = N - 2) ∧ m = -1 ∧ n = -1 ∨
    N - 2 = 5 ∧ (if b.val = 0 then c0.val - 1 else c0.val) = 2 ∧ m = -1 ∧ n = -1)

@[expose] def GGDepASmallCells (p N : ℕ) : Prop :=
  ∀ (b c0 : Fin (N - 1)) (m n : ℤ), GGDepAPat N b c0 m n → ∀ ha αa : GGDepAE p N,
    (∀ c : Fin (N - 1), c ≠ b →
      ggDepAdot αa (ggDepAh p N c) = (if c = c0 then (m : ZMod p) else 0) ∧
        ggDepAdot (ggDepAα p N c) ha = (if c = c0 then (n : ZMod p) else 0)) →
    ggDepAdot αa ha = 2 → ggDepAdot αa (ggDepAx p N) ≠ 0 →
      ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
          ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g

private theorem l05nPD_A_succ {N : ℕ} (hN : 2 ≤ N) (i j : Fin (N-2)) :
    CartanMatrix.A (N-1) ⟨i.val+1, by omega⟩ ⟨j.val+1, by omega⟩ =
      CartanMatrix.A (N-2) i j := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

private theorem l05nPD_A_castSucc {N : ℕ} (hN : 2 ≤ N) (i j : Fin (N-2)) :
    CartanMatrix.A (N-1) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
      CartanMatrix.A (N-2) i j := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

private theorem l05nPD_A_det_ne {p k : ℕ} [Fact p.Prime] (hp : p ∣ k + 2) :
    ((CartanMatrix.A k).map (fun x : ℤ => (x : ZMod p))).det ≠ 0 := by
  rw [← Int.cast_det, CartanMatrix.A_det]
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h2 : (p : ℤ) ∣ ((k + 2 : ℕ) : ℤ) := by exact_mod_cast hp
  have h1 : (p : ℤ) ∣ (1 : ℤ) := by
    have hsub := dvd_sub h2 h
    have heq : ((k + 2 : ℕ) : ℤ) - ((k : ℤ) + 1) = 1 := by omega
    rwa [heq] at hsub
  exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.1 h1)

private theorem l05nPD_finrank_le {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N-1) → V}
    {α : Fin (N-1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (hN : 2 ≤ N) :
    Module.finrank (ZMod p) V ≤ N := by
  classical
  let Ψ : V →ₗ[ZMod p] (Fin (N-1) → ZMod p) := LinearMap.pi (fun i => α i)
  have hker_le : LinearMap.ker Ψ ≤ Submodule.span (ZMod p) {x} := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    apply F.fix v
    intro i
    have := congrFun hv i
    rwa [LinearMap.pi_apply] at this
  have hker1 : Module.finrank (ZMod p) (LinearMap.ker Ψ) ≤ 1 := by
    calc Module.finrank (ZMod p) (LinearMap.ker Ψ)
        ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) {x}) :=
          Submodule.finrank_mono hker_le
      _ = 1 := finrank_span_singleton F.x_ne
  have hrange_le : Module.finrank (ZMod p) (LinearMap.range Ψ) ≤ N - 1 := by
    calc Module.finrank (ZMod p) (LinearMap.range Ψ)
        ≤ Module.finrank (ZMod p) (Fin (N-1) → ZMod p) := Submodule.finrank_le _
      _ = N - 1 :=
        (Module.finrank_pi (R := ZMod p) (ι := Fin (N-1))).trans (by rw [Fintype.card_fin])
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  omega

private theorem l05nPD_finrank_ge {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N-1) → V}
    {α : Fin (N-1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (hN : 2 ≤ N) (y : V) (hyx : y ∉ Submodule.span (ZMod p) {x})
    (e : Fin (N-2) → Fin (N-1))
    (hmat : ∀ i j, α (e i) (h (e j)) = (CartanMatrix.A (N-2) i j : ZMod p))
    (hyker : ∀ i, α (e i) y = 0) :
    N ≤ Module.finrank (ZMod p) V := by
  classical
  have hp : p ∣ (N - 2) + 2 := by rw [Nat.sub_add_cancel hN]; exact F.dvd
  let Φ : V →ₗ[ZMod p] (Fin (N-2) → ZMod p) := LinearMap.pi (fun i => α (e i))
  have hx_ker : x ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker]
    funext i
    rw [LinearMap.pi_apply]
    exact F.x_ker (e i)
  have hy_ker : y ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker]
    funext i
    rw [LinearMap.pi_apply]
    exact hyker i
  have hker2 : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker Φ) := by
    have hspan_le : Submodule.span (ZMod p) {x} ≤ LinearMap.ker Φ := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hx_ker
    have hlt : Submodule.span (ZMod p) {x} < LinearMap.ker Φ := by
      refine lt_of_le_of_ne hspan_le ?_
      intro heq
      apply hyx
      rw [heq]
      exact hy_ker
    have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {x}) = 1 :=
      finrank_span_singleton F.x_ne
    have hlt2 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [h1] at hlt2
    omega
  have hsurj : Function.Surjective Φ := by
    intro w
    have hMdet : ((CartanMatrix.A (N-2)).map (fun z : ℤ => (z : ZMod p))).det ≠ 0 :=
      l05nPD_A_det_ne hp
    have hMsurj : Function.Surjective
        (Matrix.mulVec ((CartanMatrix.A (N-2)).map (fun z : ℤ => (z : ZMod p)))) := by
      rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hMdet
    obtain ⟨c, hc⟩ := hMsurj w
    refine ⟨∑ j, c j • h (e j), ?_⟩
    funext i
    rw [LinearMap.pi_apply,
      show (∑ j, c j • h (e j)) = ∑ j ∈ Finset.univ, c j • h (e j) from rfl, map_sum]
    simp only [map_smul, smul_eq_mul]
    have hci : (Matrix.mulVec ((CartanMatrix.A (N-2)).map (fun z : ℤ => (z : ZMod p))) c) i
        = w i := congrFun hc i
    rw [Matrix.mulVec_apply_eq_sum] at hci
    simp only [Matrix.map_apply] at hci
    rw [← hci]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hmat i j]
    ring
  have hrange : Module.finrank (ZMod p) (LinearMap.range Φ) = N - 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    exact (Module.finrank_pi (R := ZMod p) (ι := Fin (N-2))).trans (by rw [Fintype.card_fin])
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  omega

theorem ggDepA_finrank_eq {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) (b : Fin (N - 1)) (hb : b.val = 0 ∨ b.val + 2 = N)
    (hy : ∃ y : V, y ∉ Submodule.span (ZMod p) {x} ∧ ∀ c, c ≠ b → α c y = 0) :
    Module.finrank (ZMod p) V = N := by
  obtain ⟨y, hyx, hyker'⟩ := hy
  have hN : 2 ≤ N := by have := b.isLt; omega
  refine le_antisymm (l05nPD_finrank_le F hN) ?_
  rcases hb with hb0 | hblast
  · let e : Fin (N-2) → Fin (N-1) := fun i => ⟨i.val + 1, by have := i.isLt; omega⟩
    have hmat : ∀ i j, α (e i) (h (e j)) = (CartanMatrix.A (N-2) i j : ZMod p) := by
      intro i j
      rw [F.pair (e i) (e j)]
      have hA : CartanMatrix.A (N-1) (e i) (e j) = CartanMatrix.A (N-2) i j := by
        dsimp only [e]
        exact l05nPD_A_succ hN i j
      rw [hA]
    have hyker : ∀ i, α (e i) y = 0 := by
      intro i
      apply hyker'
      intro hcontra
      have h1 : (e i).val = b.val := by rw [hcontra]
      rw [hb0] at h1
      dsimp only [e] at h1
      omega
    exact l05nPD_finrank_ge F hN y hyx e hmat hyker
  · let e : Fin (N-2) → Fin (N-1) := fun i => ⟨i.val, by have := i.isLt; omega⟩
    have hmat : ∀ i j, α (e i) (h (e j)) = (CartanMatrix.A (N-2) i j : ZMod p) := by
      intro i j
      rw [F.pair (e i) (e j)]
      have hA : CartanMatrix.A (N-1) (e i) (e j) = CartanMatrix.A (N-2) i j := by
        dsimp only [e]
        exact l05nPD_A_castSucc hN i j
      rw [hA]
    have hyker : ∀ i, α (e i) y = 0 := by
      intro i
      apply hyker'
      intro hcontra
      have h1 : (e i).val = b.val := by rw [hcontra]
      dsimp only [e] at h1
      omega
    exact l05nPD_finrank_ge F hN y hyx e hmat hyker

private abbrev l05nPIfinCast (N : ℕ) (j : Fin (N - 1)) : Fin N :=
  ⟨j.val, by omega⟩

private abbrev l05nPIsuccIdx (N : ℕ) (i : Fin (N - 1)) : Fin N :=
  ⟨i.val + 1, by omega⟩

private abbrev l05nPIlastIdx (N : ℕ) (hN : 0 < N) : Fin N :=
  ⟨N - 1, by omega⟩

private abbrev l05nPIlastRoot (N : ℕ) (hN : 2 ≤ N) : Fin (N - 1) :=
  ⟨N - 2, by omega⟩

private theorem l05nPIalpha_eq (p N : ℕ) (i : Fin (N - 1)) (h : i.val + 1 < N - 1) :
    ggDepAα p N i = fun j : Fin N =>
      (if j = l05nPIfinCast N i then (1 : ZMod p) else 0) -
        (if j = l05nPIsuccIdx N i then 1 else 0) := by
  funext j
  simp only [ggDepAα]
  have h0 : (j = l05nPIfinCast N i) ↔ (j.val = i.val) := by
    constructor
    · rintro rfl; rfl
    · intro hh; exact Fin.ext (by simpa [l05nPIfinCast] using hh)
  have h1 : (j = l05nPIsuccIdx N i) ↔ (j.val = i.val + 1) := by
    constructor
    · rintro rfl; rfl
    · intro hh; exact Fin.ext (by simpa [l05nPIsuccIdx] using hh)
  by_cases hj : j.val + 1 = N
  · rw [if_pos hj]
    have h0' : ¬ (j = l05nPIfinCast N i) := by
      intro hh; have := h0.mp hh; omega
    have h1' : ¬ (j = l05nPIsuccIdx N i) := by
      intro hh; have := h1.mp hh; omega
    simp [h0', h1']
  · rw [if_neg hj]
    simp only [h0, h1]

private theorem l05nPIalpha_eq_last (p N : ℕ) (i : Fin (N - 1)) (h : i.val + 1 = N - 1) :
    ggDepAα p N i = fun j : Fin N =>
      (if j = l05nPIfinCast N i then (1 : ZMod p) else 0) := by
  funext j
  simp only [ggDepAα]
  by_cases hj : j.val + 1 = N
  · rw [if_pos hj]
    have h0 : j ≠ l05nPIfinCast N i := by
      intro hh; have := congrArg Fin.val hh; simp only [l05nPIfinCast] at this; omega
    rw [if_neg h0]
  · rw [if_neg hj]
    have hj1 : j.val ≠ i.val + 1 := by intro hv; exact hj (by omega)
    rw [if_neg hj1]
    have h0 : (j = l05nPIfinCast N i) ↔ (j.val = i.val) := by
      constructor
      · rintro rfl; rfl
      · intro hh; exact Fin.ext (by simpa [l05nPIfinCast] using hh)
    simp [h0]

private theorem l05nPIdot_alpha (p N : ℕ) (w : Fin N → ZMod p) (i : Fin (N - 1)) :
    ggDepAdot (ggDepAα p N i) w =
      w (l05nPIfinCast N i) -
        (if h : i.val + 1 < N - 1 then w (l05nPIsuccIdx N i) else 0) := by
  rw [ggDepAdot]
  by_cases h : i.val + 1 < N - 1
  · rw [dif_pos h, l05nPIalpha_eq p N i h]
    have hpt : ∀ j : Fin N,
        ((if j = l05nPIfinCast N i then (1 : ZMod p) else 0) -
            (if j = l05nPIsuccIdx N i then 1 else 0)) * w j =
          (if j = l05nPIfinCast N i then w j else 0) -
            (if j = l05nPIsuccIdx N i then w j else 0) := by
      intro j
      by_cases hj0 : j = l05nPIfinCast N i
      · subst hj0
        have hne : l05nPIfinCast N i ≠ l05nPIsuccIdx N i := by
          intro hh; have := congrArg Fin.val hh
          simp only [l05nPIfinCast, l05nPIsuccIdx] at this; omega
        simp [hne]
      · rw [if_neg hj0]
        by_cases hj1 : j = l05nPIsuccIdx N i
        · subst hj1
          have hne : l05nPIsuccIdx N i ≠ l05nPIfinCast N i := by
            intro hh; have := congrArg Fin.val hh
            simp only [l05nPIfinCast, l05nPIsuccIdx] at this; omega
          simp [hne]
        · simp [hj0, hj1]
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq']
  · rw [dif_neg h, l05nPIalpha_eq_last p N i (by omega)]
    have hpt : ∀ j : Fin N,
        (if j = l05nPIfinCast N i then (1 : ZMod p) else 0) * w j =
          (if j = l05nPIfinCast N i then w j else 0) := by
      intro j
      by_cases hj0 : j = l05nPIfinCast N i
      · subst hj0; simp
      · simp [hj0]
    rw [Finset.sum_congr rfl (fun j _ => hpt j)]
    simp [Finset.sum_ite_eq']

private theorem l05nPIsum_telescope {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin (N - 1) → Module.Dual (ZMod p) V) (v : V) (i : Fin (N - 1)) :
    (∑ k : Fin (N - 1), if i.val ≤ k.val then α k v else 0) -
      (if h : i.val + 1 < N - 1 then
        ∑ k : Fin (N - 1), if i.val + 1 ≤ k.val then α k v else 0 else 0) = α i v := by
  by_cases h : i.val + 1 < N - 1
  · rw [dif_pos h, ← Finset.sum_sub_distrib]
    trans ∑ k : Fin (N - 1), (if k = i then α k v else 0)
    · apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i
      · subst hk; simp
      · rw [if_neg hk]
        by_cases hlt : k.val < i.val
        · rw [if_neg (by omega), if_neg (by omega)]; simp
        · rw [if_pos (by omega : i.val ≤ k.val), if_pos (by omega : i.val + 1 ≤ k.val)]; simp
    · simp [Finset.sum_ite_eq']
  · rw [dif_neg h, sub_zero]
    trans ∑ k : Fin (N - 1), (if k = i then α k v else 0)
    · apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i
      · subst hk; simp
      · rw [if_neg hk]
        have hik : ¬ (i.val ≤ k.val) := by
          intro hle; apply hk; apply Fin.ext
          have := k.isLt; omega
        rw [if_neg hik]
    · simp [Finset.sum_ite_eq']

private theorem l05nPIh_diff (p N : ℕ) (i j : Fin (N - 1)) (h : j.val + 1 < N - 1) :
    ggDepAh p N i (l05nPIfinCast N j) -
        ggDepAh p N i (l05nPIfinCast N ⟨j.val + 1, h⟩) =
      (CartanMatrix.A (N - 1) j i : ZMod p) := by
  have h1 : (l05nPIfinCast N j).val + 1 ≠ N := by
    simp only [l05nPIfinCast]; have := j.isLt; omega
  have h2 : (l05nPIfinCast N ⟨j.val + 1, h⟩).val + 1 ≠ N := by
    simp only [l05nPIfinCast]; omega
  simp only [ggDepAh, l05nPIfinCast, h1, h2, CartanMatrix.A, Matrix.of_apply]
  split_ifs <;> (first | (exfalso; omega) | ring_nf)

private theorem l05nPIh_step (p N : ℕ) (i j : Fin (N - 1)) (h : j.val + 1 < N - 1) :
    ggDepAh p N i (l05nPIfinCast N j) =
      (CartanMatrix.A (N - 1) j i : ZMod p) +
        ggDepAh p N i (l05nPIfinCast N ⟨j.val + 1, h⟩) := by
  have := l05nPIh_diff p N i j h
  rw [sub_eq_iff_eq_add] at this
  exact this

private theorem l05nPIh_base (p N : ℕ) (i : Fin (N - 1)) (hN : 2 ≤ N) :
    ggDepAh p N i (l05nPIfinCast N (l05nPIlastRoot N hN)) =
      (CartanMatrix.A (N - 1) (l05nPIlastRoot N hN) i : ZMod p) := by
  have h1 : (l05nPIfinCast N (l05nPIlastRoot N hN)).val + 1 ≠ N := by
    simp only [l05nPIfinCast, l05nPIlastRoot]; omega
  simp only [ggDepAh, l05nPIfinCast, l05nPIlastRoot, h1, CartanMatrix.A, Matrix.of_apply,
    Fin.ext_iff]
  split_ifs <;> (first | (exfalso; omega) | ring_nf)

private theorem l05nPIsum_step (p N : ℕ) (i j : Fin (N - 1)) (h : j.val + 1 < N - 1) :
    (∑ k : Fin (N - 1), if j.val ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p) else 0) =
      (CartanMatrix.A (N - 1) j i : ZMod p) +
        (∑ k : Fin (N - 1),
          if (⟨j.val + 1, h⟩ : Fin (N - 1)).val ≤ k.val then
            (CartanMatrix.A (N - 1) k i : ZMod p) else 0) := by
  have hpt : ∀ k : Fin (N - 1),
      (if j.val ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p) else 0) =
        (if k = j then (CartanMatrix.A (N - 1) j i : ZMod p) else 0) +
          (if j.val + 1 ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p) else 0) := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · rw [if_neg hk]
      by_cases hlt : k.val < j.val
      · rw [if_neg (by omega), if_neg (by omega)]; simp
      · rw [if_pos (by omega : j.val ≤ k.val), if_pos (by omega : j.val + 1 ≤ k.val)]; simp
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

private theorem l05nPIsum_base (p N : ℕ) (i : Fin (N - 1)) (hN : 2 ≤ N) :
    (∑ k : Fin (N - 1),
        if (l05nPIlastRoot N hN).val ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p)
        else 0) = (CartanMatrix.A (N - 1) (l05nPIlastRoot N hN) i : ZMod p) := by
  have hpt : ∀ k : Fin (N - 1),
      (if (l05nPIlastRoot N hN).val ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p)
        else 0) =
        (if k = l05nPIlastRoot N hN then (CartanMatrix.A (N - 1) k i : ZMod p) else 0) := by
    intro k
    by_cases hk : k = l05nPIlastRoot N hN
    · subst hk; simp
    · rw [if_neg hk]
      have : ¬ ((l05nPIlastRoot N hN).val ≤ k.val) := by
        intro hle; apply hk; apply Fin.ext
        have := k.isLt; simp only [l05nPIlastRoot] at *; omega
      rw [if_neg this]
  rw [Finset.sum_congr rfl (fun k _ => hpt k)]
  simp [Finset.sum_ite_eq']

private theorem l05nPIh_prefix (p N : ℕ) (i : Fin (N - 1)) :
    ∀ j : Fin (N - 1),
      (∑ k : Fin (N - 1), if j.val ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p)
        else 0) = ggDepAh p N i (l05nPIfinCast N j) := by
  have hN : 2 ≤ N := by have := i.isLt; omega
  have hS : ∀ m, ∀ j : Fin (N - 1), N - 2 - j.val = m →
      (∑ k : Fin (N - 1), if j.val ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p)
        else 0) = ggDepAh p N i (l05nPIfinCast N j) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hm
      by_cases hlast : j = l05nPIlastRoot N hN
      · subst hlast
        rw [l05nPIsum_base p N i hN, l05nPIh_base p N i hN]
      · have hjlt : j.val + 1 < N - 1 := by
          have hjne : j.val ≠ N - 2 := by
            intro hv; apply hlast; exact Fin.ext (by simpa [l05nPIlastRoot] using hv)
          have := j.isLt; omega
        rw [l05nPIsum_step p N i j hjlt, l05nPIh_step p N i j hjlt]
        congr 1
        exact ih (N - 2 - (j.val + 1)) (by omega) ⟨j.val + 1, hjlt⟩ rfl
  intro j
  exact hS (N - 2 - j.val) j rfl

theorem ggDepA_model_iso {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) (hdim : Module.finrank (ZMod p) V = N) :
    ∃ θ : V ≃ₗ[ZMod p] GGDepAE p N, (∀ i, θ (h i) = ggDepAh p N i) ∧
      (∀ i v, α i v = ggDepAdot (ggDepAα p N i) (θ v)) ∧ θ x = ggDepAx p N := by
  have hNpos : 0 < N := by
    haveI : Nontrivial V := ⟨x, 0, F.x_ne⟩
    rw [← hdim]
    exact Module.finrank_pos
  obtain ⟨_, hxH, _⟩ := ggDepA_relation F
  obtain ⟨lam, hlamH, hlamx⟩ :=
    LinearMap.exists_extend_of_notMem (p := Submodule.span (ZMod p) (Set.range h)) (v := x)
      (0 : Submodule.span (ZMod p) (Set.range h) →ₗ[ZMod p] ZMod p) hxH 1
  have hlamh : ∀ i, lam (h i) = 0 := by
    intro i
    have hmem : h i ∈ Submodule.span (ZMod p) (Set.range h) := Submodule.subset_span ⟨i, rfl⟩
    have := LinearMap.congr_fun hlamH ⟨h i, hmem⟩
    simpa using this
  let θ₀ : V →ₗ[ZMod p] (Fin N → ZMod p) :=
    { toFun := fun v j => if hj : j.val + 1 = N then lam v
        else ∑ k : Fin (N - 1), if j.val ≤ k.val then α k v else 0
      map_add' := by
        intro a b
        funext j
        by_cases hj : j.val + 1 = N
        · simp [hj]
        · simp only [dif_neg hj, Pi.add_apply]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : j.val ≤ k.val <;> simp [hk, map_add]
      map_smul' := by
        intro c a
        funext j
        by_cases hj : j.val + 1 = N
        · simp [hj]
        · simp only [dif_neg hj, Pi.smul_apply]
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : j.val ≤ k.val <;> simp [hk, map_smul] }
  have hθ₀_apply : ∀ v j, θ₀ v j = if hj : j.val + 1 = N then lam v
      else ∑ k : Fin (N - 1), if j.val ≤ k.val then α k v else 0 := fun _ _ => rfl
  have hT : ∀ v (j : Fin (N - 1)), θ₀ v (l05nPIfinCast N j) =
      ∑ k : Fin (N - 1), if j.val ≤ k.val then α k v else 0 := by
    intro v j
    have hnc : (l05nPIfinCast N j).val + 1 ≠ N := by
      simp only [l05nPIfinCast]; have := j.isLt; omega
    rw [hθ₀_apply, dif_neg hnc]
  have hkey : ∀ w, θ₀ w = 0 → w = 0 := by
    intro w hw
    have hlamw : lam w = 0 := by
      have hlast : (l05nPIlastIdx N hNpos).val + 1 = N := by
        simp only [l05nPIlastIdx]; omega
      have h := congr_fun hw (l05nPIlastIdx N hNpos)
      rwa [hθ₀_apply, dif_pos hlast] at h
    have hT0 : ∀ j : Fin (N - 1),
        (∑ k : Fin (N - 1), if j.val ≤ k.val then α k w else 0) = 0 := by
      intro j
      exact (hT w j).symm.trans (congr_fun hw (l05nPIfinCast N j))
    have hαw : ∀ i : Fin (N - 1), α i w = 0 := by
      intro i
      have htel := l05nPIsum_telescope (p := p) (N := N) α w i
      rw [hT0 i] at htel
      by_cases hh : i.val + 1 < N - 1
      · rw [dif_pos hh, hT0 ⟨i.val + 1, hh⟩, sub_zero] at htel
        exact htel.symm
      · rw [dif_neg hh] at htel
        simpa using htel.symm
    have hspan : w ∈ Submodule.span (ZMod p) {x} := F.fix w hαw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
    have hc_eq : c = lam w := by
      rw [← hc, map_smul, hlamx]
      simp
    rw [← hc, hc_eq.trans hlamw, zero_smul]
  have hθ₀_inj : Function.Injective θ₀ := by
    intro u v huv
    have : θ₀ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hkey (u - v) this)
  have hdim' : Module.finrank (ZMod p) V = Module.finrank (ZMod p) (Fin N → ZMod p) := by
    rw [hdim, Module.finrank_fin_fun]
  refine ⟨LinearMap.linearEquivOfInjective θ₀ hθ₀_inj hdim', ?_, ?_, ?_⟩
  · intro i
    rw [LinearMap.linearEquivOfInjective_apply]
    funext j
    by_cases hj : j.val + 1 = N
    · rw [hθ₀_apply, dif_pos hj, hlamh i]
      simp [ggDepAh, hj]
    · rw [hθ₀_apply, dif_neg hj]
      have hjlt : j.val < N - 1 := by omega
      calc (∑ k : Fin (N - 1), if j.val ≤ k.val then α k (h i) else 0)
          = ∑ k : Fin (N - 1),
              (if j.val ≤ k.val then (CartanMatrix.A (N - 1) k i : ZMod p) else 0) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [F.pair k i]
        _ = ggDepAh p N i (l05nPIfinCast N ⟨j.val, hjlt⟩) :=
            l05nPIh_prefix p N i ⟨j.val, hjlt⟩
        _ = ggDepAh p N i j := rfl
  · intro i v
    rw [LinearMap.linearEquivOfInjective_apply, l05nPIdot_alpha p N (θ₀ v) i]
    by_cases hh : i.val + 1 < N - 1
    · rw [dif_pos hh, hT v i]
      have hs : l05nPIsuccIdx N i = l05nPIfinCast N ⟨i.val + 1, hh⟩ := Fin.ext rfl
      rw [hs, hT v ⟨i.val + 1, hh⟩]
      have htel := l05nPIsum_telescope (p := p) (N := N) α v i
      rw [dif_pos hh] at htel
      exact htel.symm
    · rw [dif_neg hh, hT v i]
      have htel := l05nPIsum_telescope (p := p) (N := N) α v i
      rw [dif_neg hh] at htel
      exact htel.symm
  · rw [LinearMap.linearEquivOfInjective_apply]
    funext j
    by_cases hj : j.val + 1 = N
    · rw [hθ₀_apply, dif_pos hj, hlamx]
      simp [ggDepAx, hj]
    · rw [hθ₀_apply, dif_neg hj]
      have hx0 : ∀ k : Fin (N - 1), α k x = 0 := fun k => F.x_ker k
      simp [hx0, ggDepAx, hj]


lemma l05nPT_refl_apply {p N : ℕ} (c f w : GGDepAE p N) :
    ggDepARefl c f w = w - ggDepAdot f w • c := by
  simp [ggDepARefl, ggDepAform, ggDepAdot, LinearMap.smulRight_apply, smul_eq_mul]

lemma l05nPT_apply_symm {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M]
    [Module (ZMod p) M] [AddCommGroup N] [Module (ZMod p) N]
    (e : M ≃ₗ[ZMod p] N) (x : N) :
    (e : M →ₗ[ZMod p] N) ((e.symm : N →ₗ[ZMod p] M) x) = x := by
  change (e : M → N) ((e.symm : N → M) x) = x
  exact LinearEquiv.apply_symm_apply e x

lemma l05nPT_symm_apply {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M]
    [Module (ZMod p) M] [AddCommGroup N] [Module (ZMod p) N]
    (e : M ≃ₗ[ZMod p] N) (x : M) :
    (e.symm : N →ₗ[ZMod p] M) ((e : M →ₗ[ZMod p] N) x) = x := by
  change (e.symm : N → M) (e x) = x
  exact LinearEquiv.symm_apply_apply e x

lemma l05nPT_dot_of_comp_symm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (αa : Module.Dual (ZMod p) V) (θ : V ≃ₗ[ZMod p] GGDepAE p N) :
    ∃ αa' : GGDepAE p N, ∀ v : GGDepAE p N, ggDepAdot αa' v = αa (θ.symm v) := by
  classical
  refine ⟨fun i => αa (θ.symm.toLinearMap (fun j => if i = j then (1 : ZMod p) else 0)), ?_⟩
  intro v
  have hlin := LinearMap.pi_apply_eq_sum_univ (αa.comp θ.symm.toLinearMap) v
  have hcomp : αa (θ.symm v) = (αa.comp θ.symm.toLinearMap) v := rfl
  rw [hcomp, hlin]
  simp only [ggDepAdot, LinearMap.comp_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

private lemma l05nPT_conj_range {p : ℕ} [Fact p.Prime] {V E : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup E] [Module (ZMod p) E]
    (θ : V ≃ₗ[ZMod p] E) (g : Module.End (ZMod p) E) (g' : V ≃ₗ[ZMod p] V)
    (hg' : (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (g.comp θ.toLinearMap)) :
    ggLinMove g' = Submodule.map θ.symm.toLinearMap (LinearMap.range (g - LinearMap.id)) := by
  rw [ggLinMove, hg']
  have h1 : θ.symm.toLinearMap.comp (g.comp θ.toLinearMap) - LinearMap.id =
      θ.symm.toLinearMap.comp ((g - LinearMap.id).comp θ.toLinearMap) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]
    rw [l05nPT_symm_apply θ v]
  rw [h1, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr θ.surjective]
  simp

lemma l05nPT_conj_finrank {p : ℕ} [Fact p.Prime] {V E : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup E] [Module (ZMod p) E]
    (θ : V ≃ₗ[ZMod p] E) (g : Module.End (ZMod p) E) (g' : V ≃ₗ[ZMod p] V)
    (hg' : (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (g.comp θ.toLinearMap)) :
    Module.finrank (ZMod p) (ggLinMove g') =
      Module.finrank (ZMod p) (LinearMap.range (g - LinearMap.id)) := by
  rw [l05nPT_conj_range θ g g' hg', LinearEquiv.finrank_map_eq]

lemma l05nPT_conj_move_fix {p : ℕ} [Fact p.Prime] {V E : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup E] [Module (ZMod p) E]
    (θ : V ≃ₗ[ZMod p] E) (g : Module.End (ZMod p) E) (g' : V ≃ₗ[ZMod p] V)
    (hg' : (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (g.comp θ.toLinearMap))
    (hfix : ∀ u, g (g u - u) = g u - u) :
    ∀ w, g' (g' w - w) = g' w - w := by
  intro w
  change g'.toLinearMap (g'.toLinearMap w - w) = g'.toLinearMap w - w
  rw [hg']
  simp only [LinearMap.comp_apply]
  rw [show θ.toLinearMap (θ.symm.toLinearMap (g (θ.toLinearMap w)) - w) =
        g (θ.toLinearMap w) - θ.toLinearMap w by
      rw [map_sub, l05nPT_apply_symm θ (g (θ.toLinearMap w))]]
  rw [hfix (θ.toLinearMap w), map_sub, l05nPT_symm_apply θ w]

theorem ggDepA_small_false {p N : ℕ} [Fact p.Prime] (hcells : GGDepASmallCells p N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0) (b c0 : Fin (N - 1))
    (m n : ℤ) (hpat : GGDepAPat N b c0 m n)
    (hpair : ∀ c : Fin (N - 1), c ≠ b →
      αa (h c) = (if c = c0 then (m : ZMod p) else 0) ∧
        α c ha = (if c = c0 then (n : ZMod p) else 0))
    (hy : ∃ y : V, y ∉ Submodule.span (ZMod p) {x} ∧ ∀ c, c ≠ b → α c y = 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  classical
  have hdim : Module.finrank (ZMod p) V = N := ggDepA_finrank_eq F b hpat.1 hy
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepA_model_iso F hdim
  have hθα' : ∀ i v, α i v =
      ggDepAdot (ggDepAα p N i) ((θ : V →ₗ[ZMod p] GGDepAE p N) v) := fun i v => hθα i v
  obtain ⟨αa', hαa'dot⟩ := l05nPT_dot_of_comp_symm (p := p) (N := N) αa θ
  have hαa'dot' : ∀ y : GGDepAE p N,
      ggDepAdot αa' y = αa ((θ.symm : GGDepAE p N →ₗ[ZMod p] V) y) := fun y => hαa'dot y
  set ha' : GGDepAE p N := θ ha with ha'_def
  have hpair' : ∀ c : Fin (N - 1), c ≠ b →
      ggDepAdot αa' (ggDepAh p N c) = (if c = c0 then (m : ZMod p) else 0) ∧
        ggDepAdot (ggDepAα p N c) ha' = (if c = c0 then (n : ZMod p) else 0) := by
    intro c hc
    constructor
    · rw [hαa'dot]
      rw [show θ.symm (ggDepAh p N c) = h c by
        rw [← hθh c, LinearEquiv.symm_apply_apply]]
      exact (hpair c hc).1
    · rw [ha'_def, ← hθα c ha]
      exact (hpair c hc).2
  have hha : ggDepAdot αa' ha' = 2 := by
    rw [hαa'dot, ha'_def, LinearEquiv.symm_apply_apply]
    exact hαa
  have hhw : ggDepAdot αa' (ggDepAx p N) ≠ 0 := by
    rw [hαa'dot]
    rw [show θ.symm (ggDepAx p N) = x by
      rw [← hθx, LinearEquiv.symm_apply_apply]]
    exact hw
  obtain ⟨g, hgS, htv⟩ := hcells b c0 m n hpat ha' αa' hpair' hha hhw
  let S : Set (Module.End (ZMod p) (GGDepAE p N)) :=
    Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
      {ggDepARefl ha' αa'}
  let T : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod p] V) v = v - α i v • h i := fun i v => hr i v
  have hra_apply : ∀ v, (ra : V →ₗ[ZMod p] V) v = v - αa v • ha := fun v => hra v
  have hconj : ∀ y ∈ Submonoid.closure S, ∃ g' ∈ Subgroup.closure T,
      (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (y.comp θ.toLinearMap) := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem z hz =>
        dsimp only [S] at hz
        rcases hz with ⟨i, rfl⟩ | hz
        · refine ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩), ?_⟩
          ext v
          rw [hr_apply i v]
          simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
          rw [l05nPT_symm_apply θ v]
          rw [show θ.symm.toLinearMap (ggDepAh p N i) = h i by
            change (θ.symm : GGDepAE p N → V) (ggDepAh p N i) = h i
            rw [← hθh i, LinearEquiv.symm_apply_apply]]
          rw [← hθα' i v]
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          refine ⟨ra, Subgroup.subset_closure (Or.inr rfl), ?_⟩
          ext v
          rw [hra_apply v]
          simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
          rw [l05nPT_symm_apply θ v]
          rw [show θ.symm.toLinearMap ha' = ha by
            change (θ.symm : GGDepAE p N → V) ha' = ha
            rw [ha'_def, LinearEquiv.symm_apply_apply]]
          rw [hαa'dot' (θ.toLinearMap v), l05nPT_symm_apply θ v]
    | one =>
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        ext v
        simp
    | mul y z _ _ hpy hpz =>
        obtain ⟨gy, hgy, egy⟩ := hpy
        obtain ⟨gz, hgz, ez⟩ := hpz
        refine ⟨gy * gz, Subgroup.mul_mem _ hgy hgz, ?_⟩
        rw [LinearEquiv.coe_toLinearMap_mul, egy, ez, Module.End.mul_eq_comp,
          Module.End.mul_eq_comp]
        ext v
        simp only [LinearMap.comp_apply]
        rw [l05nPT_apply_symm θ]
  obtain ⟨g', hg'T, hg'eq⟩ := hconj g hgS
  exact hnt g' hg'T ⟨by
      rw [l05nPT_conj_finrank θ g g' hg'eq]
      exact htv.1,
    l05nPT_conj_move_fix θ g g' hg'eq htv.2⟩

end CFSG.StandardType
