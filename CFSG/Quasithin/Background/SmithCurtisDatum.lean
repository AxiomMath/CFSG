module

public import CFSG.Quasithin.Background.SmithCurtisRankOne
public import CFSG.Quasithin.Background.SmithCurtisHecke
public import Mathlib.GroupTheory.Coxeter.Length

public section

namespace CFSG.Quasithin.SmithCurtis

open CoxeterSystem

structure CurtisDatum (G : Type*) [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
    [Group W] (cs : CoxeterSystem M W) (p : ℕ) where
  U : Subgroup G
  L : Subgroup G
  H : Subgroup G
  X : B → Subgroup G
  Y : B → Subgroup G
  Us : B → Subgroup G
  Q : B → Subgroup G
  n : B → G
  nW : W → G
  isPGroup_U : IsPGroup p U
  isPGroup_L : IsPGroup p L
  U_inf_L : U ⊓ L = ⊥
  H_comm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  H_normU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U
  H_normU' : ∀ h ∈ H, ∀ u ∈ U, h⁻¹ * u * h ∈ U
  H_normL : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L
  H_normX : ∀ s, ∀ h ∈ H, ∀ x ∈ X s, h * x * h⁻¹ ∈ X s
  H_normQ : ∀ s, ∀ h ∈ H, ∀ q ∈ Q s, h * q * h⁻¹ ∈ Q s
  X_le : ∀ s, X s ≤ U
  X_ne_bot : ∀ s, X s ≠ ⊥
  U_eq : ∀ s, ∀ u ∈ U, ∃ x ∈ X s, ∃ v ∈ Us s, u = x * v
  Us_le : ∀ s, Us s ≤ U
  X_normUs : ∀ s, ∀ x ∈ X s, ∀ v ∈ Us s, x * v * x⁻¹ ∈ Us s
  n_normUs : ∀ s, ∀ v ∈ Us s, n s * v * (n s)⁻¹ ∈ Us s
  n_normUs' : ∀ s, ∀ v ∈ Us s, (n s)⁻¹ * v * n s ∈ Us s
  Y_le : ∀ s, Y s ≤ L
  Q_le : ∀ s, Q s ≤ L
  L_le : ∀ s, L ≤ Y s ⊔ Q s
  X_normQ : ∀ s, ∀ x ∈ X s, ∀ q ∈ Q s, x * q * x⁻¹ ∈ Q s
  Y_normQ : ∀ s, ∀ y ∈ Y s, ∀ q ∈ Q s, y * q * y⁻¹ ∈ Q s
  n_normQ : ∀ s, ∀ q ∈ Q s, n s * q * (n s)⁻¹ ∈ Q s
  n_conjX : ∀ s, ∀ x ∈ X s, n s * x * (n s)⁻¹ ∈ Y s
  n_conjY : ∀ s, ∀ y ∈ Y s, n s * y * (n s)⁻¹ ∈ X s
  n_sq : ∀ s, n s * n s ∈ H
  n_normH : ∀ s, ∀ h ∈ H, n s * h * (n s)⁻¹ ∈ H
  phi : B → G → G
  psi : B → G → G
  phi_mem : ∀ s, ∀ x ∈ X s, x ≠ 1 → phi s x ∈ H
  psi_mem : ∀ s, ∀ x ∈ X s, x ≠ 1 → psi s x ∈ H
  phi_spec : ∀ s, ∀ x ∈ X s, x ≠ 1 → ∃ l ∈ L, ∃ u ∈ U, x * n s = l * phi s x * u
  psi_spec : ∀ s, ∀ x ∈ X s, x ≠ 1 → ∃ a ∈ X s, ∃ u ∈ U, n s * x * n s = a * n s * psi s x * u
  bruhatY : ∀ s, ∀ y ∈ Y s, y ≠ 1 → ∃ h ∈ H, ∃ a ∈ X s, ∃ c ∈ X s, y = a * (h * n s) * c
  nW_one : nW 1 = 1
  nW_simple_mul : ∀ (w : W) (s : B), cs.length (cs.simple s * w) = cs.length w + 1 →
    nW (cs.simple s * w) = n s * nW w
  nW_conj : ∀ (w : W) (s : B), cs.length (cs.simple s * w) = cs.length w + 1 →
    ∀ x ∈ X s, (nW w)⁻¹ * x * nW w ∈ U
  heckeDeg_mul : ∀ (w : W) (s : B), cs.length (cs.simple s * w) = cs.length w + 1 →
    heckeDeg U (n s) * heckeDeg U (nW w) = heckeDeg U (nW (cs.simple s * w))
  cover : ∀ g : G, ∃ l ∈ L, ∃ w : W, ∃ h ∈ H, ∃ u ∈ U, g = l * nW w * (h * u)

namespace CurtisDatum

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)

theorem n_inv_normH (s : B) {h : G} (hh : h ∈ D.H) : (D.n s)⁻¹ * h * D.n s ∈ D.H := by
  have e : (D.n s)⁻¹ * h * D.n s =
      (D.n s * D.n s)⁻¹ * (D.n s * h * (D.n s)⁻¹) * (D.n s * D.n s) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (D.n_sq s)) (D.n_normH s h hh)) (D.n_sq s)

theorem n_inv_conjY (s : B) {y : G} (hy : y ∈ D.Y s) : (D.n s)⁻¹ * y * D.n s ∈ D.X s := by
  have e : (D.n s)⁻¹ * y * D.n s =
      (D.n s * D.n s)⁻¹ * (D.n s * y * (D.n s)⁻¹) * ((D.n s * D.n s)⁻¹)⁻¹ := by group
  rw [e]
  exact D.H_normX s _ (inv_mem (D.n_sq s)) _ (D.n_conjY s y hy)

theorem n_inv_conjX (s : B) {x : G} (hx : x ∈ D.X s) : (D.n s)⁻¹ * x * D.n s ∈ D.L := by
  have e : (D.n s)⁻¹ * x * D.n s =
      (D.n s * D.n s)⁻¹ * (D.n s * x * (D.n s)⁻¹) * ((D.n s * D.n s)⁻¹)⁻¹ := by group
  rw [e]
  exact D.H_normL _ (inv_mem (D.n_sq s)) _ (D.Y_le s (D.n_conjX s x hx))

theorem nsq_conjX (s : B) {x : G} (hx : x ∈ D.X s) :
    (D.n s * D.n s)⁻¹ * x * (D.n s * D.n s) ∈ D.U := by
  have e : (D.n s * D.n s)⁻¹ * x * (D.n s * D.n s) =
      (D.n s * D.n s)⁻¹ * x * ((D.n s * D.n s)⁻¹)⁻¹ := by rw [inv_inv]
  rw [e]
  exact D.X_le s (D.H_normX s _ (inv_mem (D.n_sq s)) x hx)

theorem dvd_card_X [Finite G] [Fact p.Prime] (s : B) : p ∣ Nat.card (D.X s) := by
  have hX : IsPGroup p (D.X s) := (D.isPGroup_U).to_le (D.X_le s)
  have hnt : Nontrivial (D.X s) := (Subgroup.nontrivial_iff_ne_bot _).mpr (D.X_ne_bot s)
  refine hX.card_eq_or_dvd.resolve_left fun h => ?_
  have := Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

theorem nW_normH (w : W) {h : G} (hh : h ∈ D.H) : (D.nW w)⁻¹ * h * D.nW w ∈ D.H := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  induction ω generalizing h with
  | nil => rw [cs.wordProd_nil, D.nW_one]; simpa using hh
  | cons s ω ih =>
    have hred : cs.IsReduced ω := by simpa using hω.drop 1
    have hlen : cs.length (cs.simple s * cs.wordProd ω) = cs.length (cs.wordProd ω) + 1 := by
      rw [← cs.wordProd_cons, hω.eq, hred.eq, List.length_cons]
    rw [cs.wordProd_cons, D.nW_simple_mul _ _ hlen]
    have e : (D.n s * D.nW (cs.wordProd ω))⁻¹ * h * (D.n s * D.nW (cs.wordProd ω)) =
        (D.nW (cs.wordProd ω))⁻¹ * ((D.n s)⁻¹ * h * D.n s) * D.nW (cs.wordProd ω) := by group
    rw [e]
    exact ih (D.n_inv_normH s hh) hred

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

@[expose] def fixU : Submodule k V := fixSub ρ D.U

theorem mem_fixU {v : V} : v ∈ D.fixU ρ ↔ ∀ u ∈ D.U, ρ u v = v := Iff.rfl

variable [Finite G]

@[expose] noncomputable def heckeT (s : B) : V →ₗ[k] V :=
  haveI := Fintype.ofFinite (D.X s)
  sumT ρ (D.X s) (D.n s)

theorem heckeT_apply (s : B) (v : V) [Fintype (D.X s)] :
    D.heckeT ρ s v = ∑ x : D.X s, ρ ((x : G) * D.n s) v := by
  rw [heckeT, sumT_apply]
  congr
  exact Subsingleton.elim _ _

open Classical in
@[expose] noncomputable def heckeD (s : B) : V →ₗ[k] V :=
  haveI := Fintype.ofFinite (D.X s)
  ∑ x ∈ (Finset.univ : Finset (D.X s)).erase 1, ρ (D.phi s x)

open Classical in
@[expose] noncomputable def heckeD' (s : B) : V →ₗ[k] V :=
  haveI := Fintype.ofFinite (D.X s)
  ∑ x ∈ (Finset.univ : Finset (D.X s)).erase 1, ρ (D.psi s x)

end CurtisDatum

end CFSG.Quasithin.SmithCurtis
