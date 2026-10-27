module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bInvol
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUAJPerm_exists_swap_of_involution_card_fixed {m : ℕ} (hm2 : 2 ≤ m)
    {σ : Equiv.Perm (Fin m)} (hσ : σ * σ = 1)
    (hfix : Fintype.card {x : Fin m // σ x = x} = m - 2) :
    ∃ a b : Fin m, a ≠ b ∧ σ = Equiv.swap a b := by
  have hσ' : ∀ x, σ (σ x) = x := by
    intro x
    have := congrArg (fun p : Equiv.Perm (Fin m) => p x) hσ
    simpa using this
  have hσne : σ ≠ 1 := by
    intro h
    rw [h] at hfix
    simp at hfix
    omega
  have hex : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσne (Equiv.ext h)
  obtain ⟨a, ha⟩ := hex
  let b : Fin m := σ a
  have hab : a ≠ b := by
    intro h
    exact ha h.symm
  have hba : σ b = a := hσ' a
  have hfix' : (Finset.univ.filter (fun x : Fin m => σ x = x)).card = m - 2 := by
    rw [← hfix]
    simp [Fintype.card_subtype]
  have hother : ∀ x, x ≠ a → x ≠ b → σ x = x := by
    intro x hxa hxb
    by_contra hx
    have hsub : Finset.univ.filter (fun y : Fin m => σ y = y) ⊆
        Finset.univ \ ({a, b, x} : Finset (Fin m)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rintro (rfl | rfl | rfl)
      · exact ha hy
      · exact hab (hba.symm.trans hy)
      · exact hx hy
    have hle := Finset.card_le_card hsub
    rw [hfix'] at hle
    have hcard3 : ({a, b, x} : Finset (Fin m)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · intro h
        have hbx : b = x := by simpa using h
        exact hxb hbx.symm
      · intro h
        have habx : a = b ∨ a = x := by simpa using h
        rcases habx with h' | h'
        · exact hab h'
        · exact hxa h'.symm
    have hcard : (Finset.univ \ ({a, b, x} : Finset (Fin m))).card = m - 3 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard3]
      simp
    rw [hcard] at hle
    omega
  refine ⟨a, b, hab, ?_⟩
  apply Equiv.ext
  intro x
  by_cases hxa : x = a
  · subst hxa
    simp [b, Equiv.swap_apply_left]
  · by_cases hxb : x = b
    · subst hxb
      rw [hba]
      exact (Equiv.swap_apply_right a b).symm
    · rw [hother x hxa hxb]
      exact (Equiv.swap_apply_of_ne_of_ne hxa hxb).symm

private theorem hdRo7SUAJPerm_aux_equiv_mul {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V)
    (σ τ : Equiv.Perm (Fin m)) :
    b.equiv b σ * b.equiv b τ = b.equiv b (σ * τ) := by
  have h : ((b.equiv b σ * b.equiv b τ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
      ((b.equiv b (σ * τ) : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) := by
    refine b.ext (fun i => ?_)
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.Perm.mul_apply]
  exact LinearEquiv.toLinearMap_injective h

private noncomputable def hdRo7SUAJPerm_aux_basisHom {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) :
    Equiv.Perm (Fin m) →* (V ≃ₗ[ZMod p] V) where
  toFun σ := b.equiv b σ
  map_one' := by
    rw [show (1 : Equiv.Perm (Fin m)) = Equiv.refl (Fin m) from rfl,
      Module.Basis.equiv_refl]
    rfl
  map_mul' σ τ := (hdRo7SUAJPerm_aux_equiv_mul b σ τ).symm

private theorem hdRo7SUAJPerm_aux_basisHom_injective {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) :
    Function.Injective (hdRo7SUAJPerm_aux_basisHom b) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have h2 : b (σ i) = b (τ i) := by
    have := congrArg (fun e : V ≃ₗ[ZMod p] V => e (b i)) h
    simpa [hdRo7SUAJPerm_aux_basisHom, Module.Basis.equiv_apply] using this
  exact b.injective h2

theorem hdRo7SUAJPerm_transposition_of_linRefl {p : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod p) V) (σ : Equiv.Perm (Fin m)) (hσ : σ * σ = 1)
    (hrank : Module.finrank (ZMod p) (ggLinMove (b.equiv b σ)) = 1) :
    ∃ a b' : Fin m, a ≠ b' ∧ σ = Equiv.swap a b' := by
  have hmat : LinearMap.toMatrix b b
      (((b.equiv b σ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) - LinearMap.id) =
      CFSG.QuasithinUnique.Setup.X7.permMat (ZMod p) σ - 1 := by
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.equiv_apply,
      CFSG.QuasithinUnique.Setup.X7.permMat, LinearMap.sub_apply, Matrix.sub_apply,
      Matrix.one_apply, Finsupp.single_apply, Pi.single_apply, sub_eq_add_neg, eq_comm]
  have hrank' : (CFSG.QuasithinUnique.Setup.X7.permMat (ZMod p) σ - 1).rank = 1 := by
    rw [← hmat]
    rw [Matrix.rank_eq_finrank_range_toLin (A := LinearMap.toMatrix b b
      (((b.equiv b σ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) - LinearMap.id)) b b]
    rw [Matrix.toLin_toMatrix]
    exact hrank
  have h := CFSG.QuasithinUnique.Setup.X7b.rank_permMat_sub_one (k := ZMod p) σ hσ
  rw [hrank'] at h
  have hm2 : 2 ≤ m := by
    simp at h
    omega
  have hfix : Fintype.card {x : Fin m // σ x = x} = m - 2 := by
    simp at h
    omega
  exact hdRo7SUAJPerm_exists_swap_of_involution_card_fixed hm2 hσ hfix

theorem hdRo7SUAJPerm_card_le_of_transpositions_gen_top {m : ℕ} {Λ : Type} [Fintype Λ]
    (σ : Λ → Equiv.Perm (Fin m)) (hm2 : 2 ≤ m)
    (hswap : ∀ i, ∃ a b : Fin m, a ≠ b ∧ σ i = Equiv.swap a b)
    (hgen : Subgroup.closure (Set.range σ) = ⊤) :
    m ≤ Fintype.card Λ + 1 := by
  classical
  choose a b hab hσeq using hswap
  let E : Finset (Sym2 (Fin m)) := Finset.univ.image (fun i => s(a i, b i))
  have hEcard : E.card ≤ Fintype.card Λ := by
    calc E.card ≤ (Finset.univ : Finset Λ).card := Finset.card_image_le
      _ = Fintype.card Λ := Finset.card_univ
  let G : SimpleGraph (Fin m) := SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin m)))
  have hedge : G.edgeSet ⊆ (↑E : Set (Sym2 (Fin m))) := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  have hEcard' : Nat.card (↥G.edgeSet) ≤ E.card := by
    have hinj : Function.Injective (fun e : ↥G.edgeSet => (⟨(e : Sym2 (Fin m)), hedge e.2⟩ :
        ↥(↑E : Set (Sym2 (Fin m))))) := by
      intro e e' h
      apply Subtype.ext
      exact congrArg (fun x : ↥(↑E : Set (Sym2 (Fin m))) => (x : Sym2 (Fin m))) h
    have h := Nat.card_le_card_of_injective _ hinj
    simpa using h
  have hconn : G.Connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨⟨0, by omega⟩⟩⟩
    let H : Subgroup (Equiv.Perm (Fin m)) :=
      { carrier := {τ | ∀ x : Fin m, G.Reachable (τ x) x}
        one_mem' := by intro x; simp
        mul_mem' := by
          intro τ ρ hτ hρ x
          exact (hτ (ρ x)).trans (hρ x)
        inv_mem' := by
          intro τ hτ x
          have h := hτ (τ⁻¹ x)
          have hx : τ (τ⁻¹ x) = x := by simp
          rw [hx] at h
          exact h.symm }
    have hH : ∀ i, σ i ∈ H := by
      intro i
      have hed : G.Adj (a i) (b i) := by
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨?_, hab i⟩
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hreach_ab : G.Reachable (a i) (b i) :=
        (SimpleGraph.reachable_iff_reflTransGen (a i) (b i)).mpr
          (Relation.ReflTransGen.single hed)
      have hreach_ba : G.Reachable (b i) (a i) := hreach_ab.symm
      intro x
      rw [hσeq i]
      by_cases hx : x = a i
      · subst hx
        rw [Equiv.swap_apply_left]
        exact hreach_ba
      · by_cases hxb : x = b i
        · subst hxb
          rw [Equiv.swap_apply_right]
          exact hreach_ab
        · rw [Equiv.swap_apply_of_ne_of_ne hx hxb]
    have hle : Subgroup.closure (Set.range σ) ≤ H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hH i
    have hHtop : H = ⊤ := top_le_iff.mp (by rw [← hgen]; exact hle)
    by_cases huv : u = v
    · subst huv; exact SimpleGraph.Reachable.refl u
    · have hmem : Equiv.swap u v ∈ H := by rw [hHtop]; exact Subgroup.mem_top _
      have h := hmem u
      rw [Equiv.swap_apply_left] at h
      exact SimpleGraph.Reachable.symm h
  have hbound := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hbound
  calc m ≤ Nat.card (↥G.edgeSet) + 1 := hbound
    _ ≤ E.card + 1 := Nat.add_le_add_right hEcard' 1
    _ ≤ Fintype.card Λ + 1 := Nat.add_le_add_right hEcard 1

theorem hdRo7SUAJPerm_model_card_le {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hperm : ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g)
    {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ} (φ : Λ → MulAut ↥Bs)
    (f : M.Group ≃* ↥(ggAutomizer X Bs))
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hgenX : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hm7 : 7 ≤ m) :
    m ≤ Nat.card Λ + 1 := by
  classical
  have hSUPi : ∀ i, SUPerm p b (ggLin (p := p) ι (φ i)) := fun i =>
    (hperm _).mp (Subgroup.mem_map_of_mem _
      (by rw [hgenX]; exact Subgroup.subset_closure ⟨i, rfl⟩))
  let σfun : Λ → Equiv.Perm (Fin m) := fun i => Classical.choose (hSUPi i)
  have hσspec : ∀ i k, ggLin (p := p) ι (φ i) (b k) = b (σfun i k) := fun i =>
    Classical.choose_spec (hSUPi i)
  let P : Equiv.Perm (Fin m) →* (V ≃ₗ[ZMod p] V) := hdRo7SUAJPerm_aux_basisHom b
  have hP_inj : Function.Injective P := hdRo7SUAJPerm_aux_basisHom_injective b
  have hPσ : ∀ i, P (σfun i) = ggLin (p := p) ι (φ i) := by
    intro i
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro k
    simpa [P, hdRo7SUAJPerm_aux_basisHom, Module.Basis.equiv_apply] using (hσspec i k).symm
  have hσinv : ∀ i, σfun i * σfun i = 1 := by
    intro i
    have hsq : ggLin (p := p) ι (φ i) * ggLin (p := p) ι (φ i) = 1 := by
      rw [← map_mul, ← pow_two, (hrefl i).1, map_one]
    have hPsq : P (σfun i * σfun i) = P 1 := by
      rw [map_mul, hPσ i, hsq, map_one]
    exact hP_inj hPsq
  have hrank : ∀ i, Module.finrank (ZMod p) (ggLinMove (b.equiv b (σfun i))) = 1 := by
    intro i
    have hGGL : GGLinRefl (ggLin (p := p) ι (φ i)) :=
      (ggRC_isReflection_iff_linRefl (p := p) ι (φ i)).mp (hrefl i)
    have hP_eq : b.equiv b (σfun i) = ggLin (p := p) ι (φ i) := by
      simpa [P, hdRo7SUAJPerm_aux_basisHom] using hPσ i
    rw [hP_eq]
    exact hGGL.2
  have hswap : ∀ i, ∃ a b : Fin m, a ≠ b ∧ σfun i = Equiv.swap a b := fun i =>
    hdRo7SUAJPerm_transposition_of_linRefl b (σfun i) (hσinv i) (hrank i)
  have hmapA : (ggAutomizer X Bs).map (ggLin (p := p) ι) = P.range := by
    ext g
    constructor
    · intro hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨u, hu, rfl⟩ := hg
      have hg' : ggLin (p := p) ι u ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) :=
        Subgroup.mem_map_of_mem _ hu
      obtain ⟨σ, hσ⟩ := (hperm _).mp hg'
      refine ⟨σ, ?_⟩
      apply LinearEquiv.toLinearMap_injective
      apply b.ext
      intro k
      simpa [P, hdRo7SUAJPerm_aux_basisHom, Module.Basis.equiv_apply] using (hσ k).symm
    · intro hg
      rw [MonoidHom.mem_range] at hg
      obtain ⟨σ, rfl⟩ := hg
      have hsup : SUPerm p b (P σ) :=
        ⟨σ, fun k => by
          rw [show P σ = b.equiv b σ from rfl, Module.Basis.equiv_apply]⟩
      exact (hperm _).mpr hsup
  have hmapA' : (ggAutomizer X Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) := by
    rw [hgenX, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φ i, ⟨i, rfl⟩, rfl⟩
  have hPσ_fun : (fun i => P (σfun i)) = (fun i => ggLin (p := p) ι (φ i)) :=
    funext hPσ
  have hgenσ : Subgroup.closure (Set.range σfun) = ⊤ := by
    apply Subgroup.map_injective hP_inj
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map P, ← Set.range_comp]
    rw [show (P ∘ σfun) = (fun i => ggLin (p := p) ι (φ i)) from funext hPσ, ← hmapA']
    exact hmapA
  simpa [Nat.card_eq_fintype_card] using
    hdRo7SUAJPerm_card_le_of_transpositions_gen_top σfun (by omega) hswap hgenσ

end CFSG.StandardType.HdRo7SU

end
