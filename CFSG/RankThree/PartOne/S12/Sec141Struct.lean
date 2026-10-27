module

public import CFSG.RankThree.PartOne.S12.Sec141Row
public import CFSG.RankThree.PartOne.S12.Sec138LocLinear
public import CFSG.RankThree.PartOne.S12.ReflThree
import CFSG.RankThree.PartOne.KC.LinearDegreeFive

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Node143Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
    ThreeTranspD p E →
    ∃ s ∈ reflectionSet p E, ∃ t ∈ reflectionSet p E, s ≠ t ∧ s * t = t * s

namespace Sec141Struct

open Equiv Equiv.Perm

section Generic

theorem exists_perm_structure {M : Type*} [Group M] {H : Type*} [Group H] (C : M →* H)
    (hC : Function.Injective C) {D : Set M} {m : ℕ} (Ψ : Perm (Fin m) →* H)
    (hΨ : Function.Injective Ψ) (hΨr : ∀ σ : Perm (Fin m), σ.IsSwap → Ψ σ ∈ C.range)
    (hD : ∀ x : M, x ∈ D ↔ ∃ σ : Perm (Fin m), σ.IsSwap ∧ Ψ σ = C x) :
    ∃ ψ : ↥(Subgroup.closure D) ≃* Perm (Fin m),
      (∀ (t : M) (ht : t ∈ D), (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap) ∧
      (∀ σ : Perm (Fin m), σ.IsSwap → ∃ (t : M) (ht : t ∈ D),
        ψ ⟨t, Subgroup.subset_closure ht⟩ = σ) := by
  classical
  have hrange : ∀ σ : Perm (Fin m), Ψ σ ∈ C.range := by
    intro σ
    refine Equiv.Perm.swap_induction_on σ ?_ ?_
    · rw [map_one]
      exact C.range.one_mem
    · intro f x y hxy ih
      rw [map_mul]
      exact C.range.mul_mem (hΨr _ ⟨x, y, hxy, rfl⟩) ih
  let e : M ≃* C.range := MonoidHom.ofInjective hC
  let Θ : Perm (Fin m) →* M := e.symm.toMonoidHom.comp (Ψ.codRestrict C.range hrange)
  have hΘ : ∀ σ, C (Θ σ) = Ψ σ := fun σ =>
    MonoidHom.apply_ofInjective_symm hC ⟨Ψ σ, hrange σ⟩
  have hΘinj : Function.Injective Θ := fun a b h => hΨ (by rw [← hΘ, ← hΘ, h])
  have hΘD : ∀ σ : Perm (Fin m), σ.IsSwap → Θ σ ∈ D := fun σ hσ =>
    (hD _).2 ⟨σ, hσ, (hΘ σ).symm⟩
  have hDΘ : ∀ t ∈ D, ∃ σ : Perm (Fin m), σ.IsSwap ∧ Θ σ = t := by
    intro t ht
    obtain ⟨σ, hσ, h⟩ := (hD t).1 ht
    exact ⟨σ, hσ, hC (by rw [hΘ, h])⟩
  have hclos : Subgroup.closure D = Θ.range := by
    have h1 : D = Θ '' {σ | σ.IsSwap} := by
      ext t
      constructor
      · intro ht
        obtain ⟨σ, hσ, h⟩ := hDΘ t ht
        exact ⟨σ, hσ, h⟩
      · rintro ⟨σ, hσ, rfl⟩
        exact hΘD σ hσ
    rw [h1, ← MonoidHom.map_closure, Equiv.Perm.closure_isSwap, ← MonoidHom.range_eq_map]
  let φ : Perm (Fin m) ≃* ↥(Subgroup.closure D) :=
    (MonoidHom.ofInjective hΘinj).trans (MulEquiv.subgroupCongr hclos.symm)
  refine ⟨φ.symm, ?_, ?_⟩
  · intro t ht
    obtain ⟨σ, hσ, rfl⟩ := hDΘ t ht
    have : φ σ = ⟨Θ σ, Subgroup.subset_closure ht⟩ := Subtype.ext rfl
    rw [← this, MulEquiv.symm_apply_apply]
    exact hσ
  · intro σ hσ
    refine ⟨Θ σ, hΘD σ hσ, ?_⟩
    have : φ σ = ⟨Θ σ, Subgroup.subset_closure (hΘD σ hσ)⟩ := Subtype.ext rfl
    rw [← this, MulEquiv.symm_apply_apply]

theorem exists_noncomm_of_closure {M : Type*} [Group M] {S : Set M} {Lm : Subgroup M}
    (hcl : Lm = Subgroup.closure S) (e : Lm ≃* Perm (Fin 3)) :
    ∃ s ∈ S, ∃ t ∈ S, s * t ≠ t * s := by
  by_contra hno
  push Not at hno
  have hcomm : S.Pairwise Commute := fun s hs t ht _ => hno s hs t ht
  subst hcl
  have := Subgroup.isMulCommutative_closure hcomm
  have h : ∀ a b : Perm (Fin 3), a * b = b * a := by
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := ↥(Subgroup.closure S))).comm (e.symm a) (e.symm b)
  have := h (swap 0 1) (swap 1 2)
  revert this
  decide

theorem fixes_of_closure_pair {M : Type*} [Group M] {D : Set M} {m : ℕ}
    (ψ : ↥(Subgroup.closure D) ≃* Perm (Fin m)) {s t : M} (hs : s ∈ D) (ht : t ∈ D) {d : Fin m}
    (hsd : ψ ⟨s, Subgroup.subset_closure hs⟩ d = d)
    (htd : ψ ⟨t, Subgroup.subset_closure ht⟩ d = d) {x : M}
    (hx : x ∈ Subgroup.closure {s, t}) :
    ∃ h : x ∈ Subgroup.closure D, ψ ⟨x, h⟩ d = d := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨Subgroup.subset_closure hs, hsd⟩
    · exact ⟨Subgroup.subset_closure ht, htd⟩
  | one =>
    refine ⟨Subgroup.one_mem _, ?_⟩
    have : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.closure D)) = 1 := rfl
    rw [this, map_one, Perm.one_apply]
  | mul x y _ _ hx hy =>
    obtain ⟨hx', hxd⟩ := hx
    obtain ⟨hy', hyd⟩ := hy
    refine ⟨Subgroup.mul_mem _ hx' hy', ?_⟩
    have : (⟨x * y, Subgroup.mul_mem _ hx' hy'⟩ : ↥(Subgroup.closure D)) =
        ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
    rw [this, map_mul, Perm.mul_apply, hyd, hxd]
  | inv x _ hx =>
    obtain ⟨hx', hxd⟩ := hx
    refine ⟨Subgroup.inv_mem _ hx', ?_⟩
    have : (⟨x⁻¹, Subgroup.inv_mem _ hx'⟩ : ↥(Subgroup.closure D)) = (⟨x, hx'⟩)⁻¹ := rfl
    rw [this, map_inv, Equiv.Perm.inv_eq_iff_eq]
    exact hxd.symm

theorem pow_three_of_noncomm {M : Type*} [Group M] [Finite M] {s t : M} (hs : s * s = 1)
    (ht : t * t = 1) (hle : orderOf (s * t) ≤ 3) (hnc : s * t ≠ t * s) : (s * t) ^ 3 = 1 := by
  have hpos : 0 < orderOf (s * t) := orderOf_pos _
  have hne1 : orderOf (s * t) ≠ 1 := fun h => by
    have : s * t = 1 := orderOf_eq_one_iff.1 h
    apply hnc
    have hv : t = s := by
      calc t = s⁻¹ * (s * t) := by group
        _ = s := by rw [this, mul_one, inv_eq_of_mul_eq_one_right hs]
    rw [hv]
  have hne2 : orderOf (s * t) ≠ 2 := fun h => by
    have h2' : (s * t) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    apply hnc
    have e : s * t * (s * t) = 1 := by rw [← pow_two]; exact h2'
    have hui : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have hvi : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    calc s * t = (s * t)⁻¹ := eq_inv_of_mul_eq_one_left e
      _ = t⁻¹ * s⁻¹ := mul_inv_rev _ _
      _ = t * s := by rw [hui, hvi]
  have : orderOf (s * t) = 3 := by omega
  rw [← this]
  exact pow_orderOf_eq_one _

end Generic

section Glue

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {E : Subgroup G}

theorem eq_five_of_five_eq_zero (h : (5 : ZMod p) = 0) : p = 5 := by
  have h' : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 5 p).1 h'
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).1 hd

theorem classify_D [IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 3) (hp5 : 5 ≤ p)
    (hD3 : ThreeTranspD p E) (hirr : torusIrreducible E)
    {s₁ t₁ : MulAut E} (hs₁ : s₁ ∈ reflectionSet p E) (ht₁ : t₁ ∈ reflectionSet p E)
    (hbr : s₁ * t₁ ≠ t₁ * s₁) {a c : MulAut E} (ha : a ∈ reflectionSet p E)
    (hc : c ∈ reflectionSet p E) (hac : a ≠ c) (hcomm : a * c = c * a) :
    ∃ (m : ℕ) (ψ : ↥(Subgroup.closure (reflectionSet p E)) ≃* Perm (Fin m)),
      (m = 4 ∨ m = 5) ∧ (m = 5 → (5 : ZMod p) = 0) ∧
      (∀ (t : MulAut E) (ht : t ∈ reflectionSet p E),
        (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap) ∧
      (∀ σ : Perm (Fin m), σ.IsSwap → ∃ (t : MulAut E) (ht : t ∈ reflectionSet p E),
        ψ ⟨t, Subgroup.subset_closure ht⟩ = σ) := by
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E hcard
  have hp : p.Prime := Fact.out
  have h2 := Sec138Loc.two_ne_zero_of_five_le (p := p) hp5
  have h3 := Sec138Loc.three_ne_zero_of_five_le (p := p) hp5
  have hdim : Module.finrank (ZMod p) (Fin 3 → ZMod p) = 3 := Module.finrank_fin_fun _
  have hR := Sec138Loc.isRSet_dstar f hp5 hD3
  let Γ : Subgroup ((Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p)) :=
    (torusWeyl E).map (LinAlg.coordHom f)
  have hΓ : ∀ g ∈ Γ, ∀ T ∈ Sec138Loc.dstar f, g * T * g⁻¹ ∈ Sec138Loc.dstar f := by
    intro g hg T hT
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨s, hs, rfl⟩ := (Sec138Loc.mem_dstar f).1 hT
    refine (Sec138Loc.mem_dstar f).2 ⟨φ * s * φ⁻¹,
      WeylIso.conj_mem_reflectionSet_of_weyl hp hφ hs, ?_⟩
    simp
  have hΓirr : ∀ U : Submodule (ZMod p) (Fin 3 → ZMod p),
      (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine Sec138Loc.irreducible_space f hirr U fun φ hφ => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hU _ (Subgroup.mem_map_of_mem _ hφ) x hx
  have hconn : ReflF.Conn (Sec138Loc.dstar f) :=
    ReflF.conn_of_irreducible hdim h2 h3 hR Γ hΓ hΓirr
      ((Sec138Loc.mem_dstar f).2 ⟨s₁, hs₁, rfl⟩) ((Sec138Loc.mem_dstar f).2 ⟨t₁, ht₁, rfl⟩)
      (fun e => hbr ((Sec138Loc.coordHom_comm_iff f).1 e))
  obtain ⟨m, Ψ, hm, hinj, h5, hD⟩ := ReflF.classify_dim_three hdim h2 h3 hR hconn
    ((Sec138Loc.mem_dstar f).2 ⟨a, ha, rfl⟩) ((Sec138Loc.mem_dstar f).2 ⟨c, hc, rfl⟩)
    (Sec138Loc.coordHom_ne f hac) ((Sec138Loc.coordHom_comm_iff f).2 hcomm)
  have hΨr : ∀ σ : Perm (Fin m), σ.IsSwap → Ψ σ ∈ (LinAlg.coordHom f).range := by
    intro σ hσ
    have : Ψ σ ∈ Sec138Loc.dstar f := by
      rw [hD]
      exact ReflF.mem_imgSwaps.2 ⟨σ, ReflF.mem_swapSet.2 hσ, rfl⟩
    obtain ⟨s, -, hs⟩ := (Sec138Loc.mem_dstar f).1 this
    exact ⟨s, hs⟩
  have hDiff : ∀ x : MulAut E, x ∈ reflectionSet p E ↔
      ∃ σ : Perm (Fin m), σ.IsSwap ∧ Ψ σ = LinAlg.coordHom f x := by
    intro x
    constructor
    · intro hx
      have : LinAlg.coordHom f x ∈ ReflF.imgSwaps m Ψ := by
        rw [← hD]
        exact (Sec138Loc.mem_dstar f).2 ⟨x, hx, rfl⟩
      obtain ⟨σ, hσ, h⟩ := ReflF.mem_imgSwaps.1 this
      exact ⟨σ, ReflF.mem_swapSet.1 hσ, h⟩
    · rintro ⟨σ, hσ, h⟩
      have : LinAlg.coordHom f x ∈ Sec138Loc.dstar f := by
        rw [hD, ← h]
        exact ReflF.mem_imgSwaps.2 ⟨σ, ReflF.mem_swapSet.2 hσ, rfl⟩
      obtain ⟨s, hs, hsx⟩ := (Sec138Loc.mem_dstar f).1 this
      rw [← LinAlg.coordHom_injective f hsx]
      exact hs
  obtain ⟨ψ, hsw, hsurj⟩ := exists_perm_structure (LinAlg.coordHom f)
    (LinAlg.coordHom_injective f) Ψ hinj hΨr hDiff
  exact ⟨m, ψ, hm, h5, hsw, hsurj⟩

omit [Fact p.Prime] [Finite G] in
theorem exists_weylIso {n : ℕ} {L : Subgroup G}
    (hpts : ∀ a b a' b' : Fin (n + 1), a ≠ b → a' ≠ b' →
      Equiv.swap a b * Equiv.swap a' b' ≠ Equiv.swap a' b' * Equiv.swap a b →
      ∃ d : Fin (n + 1), d ≠ a ∧ d ≠ b ∧ d ≠ a' ∧ d ≠ b')
    (ψ : ↥(Subgroup.closure (reflectionSet p E)) ≃* Perm (Fin (n + 1)))
    (hsw : ∀ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap)
    (hsurj : ∀ σ : Perm (Fin (n + 1)), σ.IsSwap → ∃ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      ψ ⟨t, Subgroup.subset_closure ht⟩ = σ)
    {s₀ t₀ : MulAut E} (hs₀ : s₀ ∈ reflectionSet p E) (ht₀ : t₀ ∈ reflectionSet p E)
    (hnc : s₀ * t₀ ≠ t₀ * s₀) (hL : Subgroup.closure {s₀, t₀} = torusImage E L) :
    Nonempty (WeylIso p n E L) := by
  obtain ⟨a, b, hab, hsab⟩ := hsw s₀ hs₀
  obtain ⟨a', b', hab', htab⟩ := hsw t₀ ht₀
  set S₀ : ↥(Subgroup.closure (reflectionSet p E)) := ⟨s₀, Subgroup.subset_closure hs₀⟩ with hS₀
  set T₀ : ↥(Subgroup.closure (reflectionSet p E)) := ⟨t₀, Subgroup.subset_closure ht₀⟩ with hT₀
  have hnc' : S₀ * T₀ ≠ T₀ * S₀ := fun e => hnc (congrArg Subtype.val e)
  have hnc'' : Equiv.swap a b * Equiv.swap a' b' ≠ Equiv.swap a' b' * Equiv.swap a b := by
    rw [← hsab, ← htab]
    intro e
    apply hnc'
    apply ψ.injective
    rw [map_mul, map_mul]
    exact e
  obtain ⟨d, hda, hdb, hda', hdb'⟩ := hpts a b a' b' hab hab' hnc''
  have hsd : ψ S₀ d = d := by
    rw [hsab]
    exact Equiv.swap_apply_of_ne_of_ne hda hdb
  have htd : ψ T₀ d = d := by
    rw [htab]
    exact Equiv.swap_apply_of_ne_of_ne hda' hdb'
  refine ⟨⟨ψ, hsw, hsurj, d, fun x hx => ?_⟩⟩
  rw [← hL] at hx
  exact fixes_of_closure_pair ψ hs₀ ht₀ hsd htd hx

end Glue

section Transport

variable {p : ℕ} {G : Type} [Group G] [Finite G] {E : Subgroup G}

omit [Finite G] in
theorem exists_conj_single {n : ℕ}
    (ψ : ↥(Subgroup.closure (reflectionSet p E)) ≃* Perm (Fin (n + 1)))
    (hsw : ∀ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap)
    {s₀ r : MulAut E} (hs₀ : s₀ ∈ reflectionSet p E) (hr : r ∈ reflectionSet p E) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * s₀ * (conjAut E w hw)⁻¹ = r := by
  obtain ⟨g, hg, hgr⟩ := WeylIso.exists_conj_eq_of_swaps ψ hsw hs₀ hr
  obtain ⟨w, hw, hwg⟩ := WeylIso.exists_lift (WeylIso.closure_le_weyl hg)
  exact ⟨w, hw, by rw [hwg]; exact hgr⟩

omit [Finite G] in
theorem exists_conj_pair {n : ℕ}
    (ψ : ↥(Subgroup.closure (reflectionSet p E)) ≃* Perm (Fin (n + 1)))
    (hsw : ∀ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap)
    (hconj : ∀ {σ₁ σ₂ τ₁ τ₂ : Perm (Fin (n + 1))}, σ₁ ∈ ReflF.swapSet (n + 1) →
      σ₂ ∈ ReflF.swapSet (n + 1) → τ₁ ∈ ReflF.swapSet (n + 1) → τ₂ ∈ ReflF.swapSet (n + 1) →
      σ₁ * σ₂ ≠ σ₂ * σ₁ → τ₁ * τ₂ ≠ τ₂ * τ₁ →
      ∃ π : Perm (Fin (n + 1)), π * σ₁ * π⁻¹ = τ₁ ∧ π * σ₂ * π⁻¹ = τ₂)
    {s₀ t₀ s t : MulAut E} (hs₀ : s₀ ∈ reflectionSet p E) (ht₀ : t₀ ∈ reflectionSet p E)
    (hs : s ∈ reflectionSet p E) (ht : t ∈ reflectionSet p E)
    (hnc₀ : s₀ * t₀ ≠ t₀ * s₀) (hnc : s * t ≠ t * s) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * s * (conjAut E w hw)⁻¹ = s₀ ∧
      conjAut E w hw * t * (conjAut E w hw)⁻¹ = t₀ := by
  set S : ↥(Subgroup.closure (reflectionSet p E)) := ⟨s, Subgroup.subset_closure hs⟩ with hSdef
  set T : ↥(Subgroup.closure (reflectionSet p E)) := ⟨t, Subgroup.subset_closure ht⟩ with hTdef
  set S₀ : ↥(Subgroup.closure (reflectionSet p E)) :=
    ⟨s₀, Subgroup.subset_closure hs₀⟩ with hS₀def
  set T₀ : ↥(Subgroup.closure (reflectionSet p E)) :=
    ⟨t₀, Subgroup.subset_closure ht₀⟩ with hT₀def
  have hST : ψ S * ψ T ≠ ψ T * ψ S := by
    intro e
    apply hnc
    have : S * T = T * S := ψ.injective (by rw [map_mul, map_mul]; exact e)
    exact congrArg Subtype.val this
  have hST₀ : ψ S₀ * ψ T₀ ≠ ψ T₀ * ψ S₀ := by
    intro e
    apply hnc₀
    have : S₀ * T₀ = T₀ * S₀ := ψ.injective (by rw [map_mul, map_mul]; exact e)
    exact congrArg Subtype.val this
  obtain ⟨π, h1, h2⟩ := hconj (ReflF.mem_swapSet.2 (hsw s hs)) (ReflF.mem_swapSet.2 (hsw t ht))
    (ReflF.mem_swapSet.2 (hsw s₀ hs₀)) (ReflF.mem_swapSet.2 (hsw t₀ ht₀)) hST hST₀
  set g : ↥(Subgroup.closure (reflectionSet p E)) := ψ.symm π with hgdef
  have hg1 : g * S * g⁻¹ = S₀ := by
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, hgdef, MulEquiv.apply_symm_apply]
    exact h1
  have hg2 : g * T * g⁻¹ = T₀ := by
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, hgdef, MulEquiv.apply_symm_apply]
    exact h2
  obtain ⟨w, hw, hwg⟩ := WeylIso.exists_lift (WeylIso.closure_le_weyl g.2)
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hwg]
    exact congrArg Subtype.val hg1
  · rw [hwg]
    exact congrArg Subtype.val hg2

omit [Finite G] in
theorem kf_all {n f : ℕ} (ψ : ↥(Subgroup.closure (reflectionSet p E)) ≃* Perm (Fin (n + 1)))
    (hsw : ∀ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap)
    (hconj : ∀ {σ₁ σ₂ τ₁ τ₂ : Perm (Fin (n + 1))}, σ₁ ∈ ReflF.swapSet (n + 1) →
      σ₂ ∈ ReflF.swapSet (n + 1) → τ₁ ∈ ReflF.swapSet (n + 1) → τ₂ ∈ ReflF.swapSet (n + 1) →
      σ₁ * σ₂ ≠ σ₂ * σ₁ → τ₁ * τ₂ ≠ τ₂ * τ₁ →
      ∃ π : Perm (Fin (n + 1)), π * σ₁ * π⁻¹ = τ₁ ∧ π * σ₂ * π⁻¹ = τ₂)
    {s₀ t₀ : MulAut E} (hs₀ : s₀ ∈ reflectionSet p E) (ht₀ : t₀ ∈ reflectionSet p E)
    (hnc₀ : s₀ * t₀ ≠ t₀ * s₀) (hAt : KFAt p E f s₀) (hPair : KFPairL p E f s₀ t₀)
    (hcomm : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
        kZero p E s ⊓ kZero p E t = ⊥) :
    (∀ t ∈ reflectionSet p E, KFAt p E f t) ∧
      (∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPairL p E f s t) := by
  refine ⟨fun t ht => ?_, fun s hs t ht hst => ⟨fun hc => hcomm s hs t ht hst hc, fun h3 => ?_⟩⟩
  · obtain ⟨w, hw, hwt⟩ := exists_conj_single ψ hsw hs₀ ht
    have := hAt.conj hw
    rwa [hwt] at this
  · have hnc : s * t ≠ t * s := by
      intro e
      have h2 : (s * t) ^ 2 = 1 := by
        have hs2 : s * s = 1 := Sec138Loc.mul_self_eq_one_of_reflection hs.1
        have ht2 : t * t = 1 := Sec138Loc.mul_self_eq_one_of_reflection ht.1
        rw [Commute.mul_pow e, pow_two s, hs2, pow_two t, ht2, one_mul]
      have := orderOf_dvd_of_pow_eq_one h2
      rw [h3] at this
      omega
    obtain ⟨w, hw, hws, hwt⟩ := exists_conj_pair ψ hsw hconj hs₀ ht₀ hs ht hnc₀ hnc
    have h : KFPairL p E f (conjAut E w hw * s * (conjAut E w hw)⁻¹)
        (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
      rw [hws, hwt]
      exact hPair
    exact (KFPairL.of_conj hw h).2 h3

end Transport

section Main

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem not_five {G : Type} [Group G] [Finite G] {p f : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hCT : ExtCurtisTitsA) (hp5 : 5 ≤ p) (hpeq : p = 5) (hf2 : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (ψ : ↥(Subgroup.closure (reflectionSet p E)) ≃* Perm (Fin (4 + 1)))
    (hsw : ∀ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap)
    (hsurj : ∀ σ : Perm (Fin (4 + 1)), σ.IsSwap → ∃ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      ψ ⟨t, Subgroup.subset_closure ht⟩ = σ)
    (hKall : ∀ t ∈ reflectionSet p E, KFAt p E f t)
    (hPall : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPairL p E f s t)
    {s₀ t₀ : MulAut E} (hs₀ : s₀ ∈ reflectionSet p E) (ht₀ : t₀ ∈ reflectionSet p E)
    (hnc : s₀ * t₀ ≠ t₀ * s₀) (hL : Subgroup.closure {s₀, t₀} = torusImage E L) : False := by
  obtain ⟨W⟩ := exists_weylIso (n := 4) ReflF.exists_point_missing_five ψ hsw hsurj hs₀ ht₀ hnc hL
  have hp : p.Prime := h.prime
  have hct := PhanAssembly.ctA_conclusion W hCT (by norm_num) hp hp5 h.E_elem hf2 hpf le_rfl
    (Sec138141.torusInvariant_self E) hF13.irreducible (Sec138141.faithful_self E) hKall hPall
  have h5 : 5 ∣ 2 ^ f - 1 := hpeq ▸ hpf
  have hfe := even_of_five_dvd_two_pow_sub_one h5
  have hrank := (even_square_field_linear_five_sections_force_two_local_rank_four (G := G)).1
    (by omega) hfe hct.1 (lieGenerated p E)
    (QuotientGroup.mk' (Subgroup.center ↥(lieGenerated p E)))
    (QuotientGroup.mk'_surjective _)
  have := sectionTenSetup_evenRank_eq h.setup
  omega

theorem node141Struct_of_comm (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) (hpair : KF134Pair) (hKF : KF141) (hCT : ExtCurtisTitsA)
    (hComm : Node143Comm) : Node141Struct := by
  intro G _ _ p A c L E h hF12 hF13 hT hEA hall
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := h.E_elem
  have hLz : L ∈ sectionTenZeroStar p A := h.L_mem.1.1
  have hLat : IsLThreeTypeAt p L := hall L hLz
  have hrow1 : RowModel p L 1 := hLat
  obtain ⟨-, hweyl, hcardE⟩ := Sec141Row.rowOne_data hRow1 h107 h109 h122 h hrow1
  have hD3 := threeTranspD_of_pair hpair hRow1 h107 h109 h122 h hF12 hF13 hT hEA hall
  obtain ⟨hclosure, -⟩ := hF12.three
  have hW1 : Nonempty (torusImage E L ≃* Perm (Fin 3)) := hweyl
  obtain ⟨e⟩ := hW1
  obtain ⟨s₀, hs₀, t₀, ht₀, hnc⟩ := exists_noncomm_of_closure hclosure e
  have hs₀D : s₀ ∈ reflectionSet p E := hs₀.1
  have ht₀D : t₀ ∈ reflectionSet p E := ht₀.1
  have hs₀L : s₀ ∈ torusImage E L := hs₀.2
  have ht₀L : t₀ ∈ torusImage E L := ht₀.2
  have hs₀2 : s₀ * s₀ = 1 := Sec138Loc.mul_self_eq_one_of_reflection hs₀D.1
  have ht₀2 : t₀ * t₀ = 1 := Sec138Loc.mul_self_eq_one_of_reflection ht₀D.1
  have hord3 : (s₀ * t₀) ^ 3 = 1 := pow_three_of_noncomm hs₀2 ht₀2 (hD3 s₀ hs₀D t₀ ht₀D) hnc
  have hLeq : Subgroup.closure {s₀, t₀} = torusImage E L := by
    obtain ⟨e2⟩ := Sec138Loc.closure_pair_equiv_perm_three hs₀2 ht₀2 hord3 hnc
    have hle : Subgroup.closure {s₀, t₀} ≤ torusImage E L := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hs₀L
      · exact ht₀L
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    exact ((Nat.card_congr e.toEquiv).trans (Nat.card_congr e2.toEquiv).symm).le
  obtain ⟨a, ha, c', hc', hac, hcomm⟩ := hComm G p A c L E h hF12 hF13 hT hEA hall hD3
  obtain ⟨m, ψ, hm, h5, hsw, hsurj⟩ := classify_D hcardE hp5 hD3 hF13.irreducible
    hs₀D ht₀D hnc ha hc' hac hcomm
  obtain ⟨f, hf1, hpf, hmodel⟩ := hLat
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have h1 := Nat.le_of_dvd (by norm_num) hpf
    norm_num at h1
    omega
  obtain ⟨hK1, hK2, hK3⟩ := hKF G p A c L E f h hF12 hF13 hT hf1 hpf hmodel hEA hall
  have hAt : KFAt p E f s₀ := hK1 s₀ hs₀D hs₀L
  have hPair : KFPairL p E f s₀ t₀ :=
    hK2 s₀ hs₀D hs₀L t₀ ht₀D ht₀L (fun e' => hnc (by rw [e']))
  rcases hm with rfl | rfl
  · exact ⟨hrow1, hweyl,
      exists_weylIso ReflF.exists_point_missing_four ψ hsw hsurj hs₀D ht₀D hnc hLeq⟩
  · exfalso
    have hpeq : p = 5 := eq_five_of_five_eq_zero (h5 rfl)
    obtain ⟨hKall, hPall⟩ := kf_all ψ hsw ReflF.swap_pairs_conj_five hs₀D ht₀D hnc hAt hPair hK3
    exact not_five h hF13 hCT hp5 hpeq hf2 hpf ψ hsw hsurj hKall hPall hs₀D ht₀D hnc hLeq

end Main

end Sec141Struct

end CFSG.RankThree.PartOne
