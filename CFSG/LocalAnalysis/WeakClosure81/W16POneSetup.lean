module

public import CFSG.LocalAnalysis.WeakClosure81.W16Three

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Cfg161 (M V₀ V U : Subgroup G) (g : G) : Prop where
  hyp : Hyp15 M V₀ V
  mbar : 1 < mBar M V₀ V hyp.h6.elemAbelian
  le : U ≤ V
  lt : E3.mQuot V (U ⊔ V₀) < mBar M V₀ V hyp.h6.elemAbelian
  conj_le : conjSubgroup V g ≤ M ⊓ centralizer (U : Set G)
  not_comm : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x

namespace Cfg161

variable {M V₀ V U : Subgroup G} {g : G}

private theorem comm_mem_V₀_of_mem_sup {M V₀ U : Subgroup G} (hUN : U ≤ normalizer (V₀ : Set G))
    (hM₀ : M ≤ normalizer (V₀ : Set G)) {a d : G} (haM : a ∈ M)
    (haU : a ∈ centralizer (U : Set G)) (hd : d ∈ U ⊔ V₀) :
    a * d * a⁻¹ * d⁻¹ ∈ V₀ := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right U V₀ hUN] at hd
  obtain ⟨u, hu, w, hw, rfl⟩ := hd
  have hau : a * u = u * a := (Subgroup.mem_centralizer_iff.1 haU u hu).symm
  have haw : a * w * a⁻¹ * w⁻¹ ∈ V₀ :=
    V₀.mul_mem ((Subgroup.mem_normalizer_iff.1 (hM₀ haM) w).1 hw) (V₀.inv_mem hw)
  have huN : u ∈ normalizer (V₀ : Set G) := hUN hu
  have hconj : u * (a * w * a⁻¹ * w⁻¹) * u⁻¹ ∈ V₀ :=
    (Subgroup.mem_normalizer_iff.1 huN _).1 haw
  have hmain : a * (u * w) * a⁻¹ * (u * w)⁻¹ =
      u * (a * w * a⁻¹ * w⁻¹) * u⁻¹ := by
    calc a * (u * w) * a⁻¹ * (u * w)⁻¹
        = (a * u) * w * a⁻¹ * (u * w)⁻¹ := by group
      _ = (u * a) * w * a⁻¹ * (u * w)⁻¹ := by rw [hau]
      _ = u * (a * w * a⁻¹ * w⁻¹) * u⁻¹ := by group
  rw [hmain]
  exact hconj

theorem conj_le_cTilde (c : Cfg161 M V₀ V U g) : conjSubgroup V g ≤ F11.CTilde M V₀ V := by
  intro a ha
  have hAel : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup c.hyp.h6.elemAbelian g
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 (hAel.2 a ha)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).1 hdvd
  refine mem_cTilde_of_mQuot_lt_mod (C := U ⊔ V₀) c.hyp.h6.elemAbelian c.hyp.h6.le
    (le_of_eq c.hyp.h6.normalizer_eq.symm) c.hyp.h6.le_normalizer₀ (c.conj_le ha).1 ⟨k, hk⟩
    (sup_le c.le c.hyp.h6.le) ?_ (by exact_mod_cast c.lt)
  intro d hd
  exact comm_mem_V₀_of_mem_sup (c.le.trans (c.hyp.h6.le_M.trans c.hyp.h6.le_normalizer₀))
    c.hyp.h6.le_normalizer₀ (c.conj_le ha).1 (c.conj_le ha).2 hd

theorem le_conjSubgroup (h152 : Thm152 G) (c : Cfg161 M V₀ V U g) :
    V ≤ conjSubgroup M g := by
  intro v hv
  have hDV : conjSubgroup V g ≤ normalizer (V : Set G) := by
    rw [c.hyp.h6.normalizer_eq]
    exact c.conj_le.trans inf_le_left
  have hV₀N : V ≤ normalizer (V₀ : Set G) :=
    c.hyp.h6.le_M.trans c.hyp.h6.le_normalizer₀
  have huD : ∀ d ∈ conjSubgroup V g, ⁅v, d⁆ ∈ V₀ := by
    intro d hd
    have hdT : d ∈ F11.CTilde M V₀ V := conj_le_cTilde c hd
    have hmem : d * v * d⁻¹ * v⁻¹ ∈ V₀ := (FourteenTwo.mem_cTilde_iff_comm.1 hdT).2.2 v hv
    have hcomm : ⁅v, d⁆ = (d * v * d⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact V₀.inv_mem hmem
  have hmq := mQuot_inf_centralizer_le_mSub c.hyp.h6.elemAbelian hDV c.hyp.h6.le hV₀N hv huD
  have hlt : (E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ centralizer ({v} : Set G)) : ℕ∞) < rMV M V :=
    lt_of_le_of_lt (by exact_mod_cast hmq) (h152 c.hyp c.mbar)
  have hcent := centralizer_le_of_mQuot_lt_rMV (M := conjSubgroup M g) (V := conjSubgroup V g)
    (X := conjSubgroup V g ⊓ centralizer ({v} : Set G)) inf_le_left (by
      rw [rMV_conj c.hyp.h6.normalizer_eq g]
      exact hlt)
  apply hcent
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2

theorem not_mem (c : Cfg161 M V₀ V U g) : g ∉ M := by
  intro hg
  apply c.not_comm
  have hgN : g ∈ normalizer (V : Set G) := by
    rw [c.hyp.h6.normalizer_eq]
    exact hg
  have hconj : conjSubgroup V g = V := by
    ext x
    rw [mem_conjSubgroup_iff]
    exact (Subgroup.mem_normalizer_iff.1 hgN x).symm
  intro x hx y hy
  rw [hconj] at hy
  exact IsElemAbelian.comm c.hyp.h6.elemAbelian hx hy

theorem commutator_mem (h152 : Thm152 G) (c : Cfg161 M V₀ V U g) :
    ∀ v ∈ V, ∀ a ∈ conjSubgroup V g, a * v * a⁻¹ * v⁻¹ ∈ V₀ ⊓ conjSubgroup V g := by
  intro v hv a ha
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hdT : a ∈ F11.CTilde M V₀ V := conj_le_cTilde c ha
    exact (FourteenTwo.mem_cTilde_iff_comm.1 hdT).2.2 v hv
  · have hvN : v ∈ normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer V g, c.hyp.h6.normalizer_eq]
      exact le_conjSubgroup h152 c hv
    have h1 : v * a⁻¹ * v⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hvN a⁻¹).1 ((conjSubgroup V g).inv_mem ha)
    have h2 : a * v * a⁻¹ * v⁻¹ ∈ conjSubgroup V g := by
      have := (conjSubgroup V g).mul_mem ha h1
      simpa only [mul_assoc] using this
    exact h2

theorem inf_ne_bot (h152 : Thm152 G) (c : Cfg161 M V₀ V U g) : V₀ ⊓ conjSubgroup V g ≠ ⊥ := by
  intro hbot
  apply c.not_comm
  intro x hx y hy
  have hcomm := commutator_mem h152 c x hx y hy
  rw [hbot, Subgroup.mem_bot] at hcomm
  have h1 : ⁅y, x⁆ = 1 := by simpa only [commutatorElement_def] using hcomm
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

end Cfg161

end CFSG.LocalAnalysis.WeakClosure81

end
