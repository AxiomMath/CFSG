module

public import CFSG.LocalAnalysis.ComponentClassification.BFailureOddIrreducible
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.CoverLift
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs

public section

universe u v w x

namespace CFSG.RepresentationTheory

open Subgroup
open CFSG.ComponentClassification.BFailureOdd
  (perfect_linear_action_nontrivial_irreducible_section sectionRepresentation)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive (ker_le_or_eq_one)

theorem exists_nontrivial_irreducible_constituent_image
    {k : Type u} {H : Type v} {S : Type w} {V : Type x}
    [Field k] [Group H] [Finite H] [Group S] [IsSimpleGroup S]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hH : Group.IsPerfect H) (γ : H →* S) (hγ : Function.Surjective γ)
    (hsol : Group.IsSolvable γ.ker)
    (ρ : Representation k H V) (hρ : ¬ ρ.IsTrivial) :
    ∃ (W : Type x) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
      (σ : Representation k H W),
      σ.IsIrreducible ∧ ¬ σ.IsTrivial ∧
      Module.finrank k W ≤ Module.finrank k V ∧
      σ.asGroupHom.ker ≤ γ.ker ∧
      Group.IsPerfect σ.asGroupHom.range ∧
      ∃ (γi : σ.asGroupHom.range →* S),
        Finite σ.asGroupHom.range ∧
        (∀ h : H, γi ⟨σ.asGroupHom h, ⟨h, rfl⟩⟩ = γ h) ∧
        Function.Surjective γi ∧
        Group.IsSolvable γi.ker := by
  classical
  have hρnt : ¬ ρ.IsTrivial := hρ
  let W : Submodule k V := Submodule.span k {y | ∃ (g : H) (v : V), ρ g v - v = y}
  have hsec := perfect_linear_action_nontrivial_irreducible_section (P := H) (V := V) ρ hρnt
  dsimp only at hsec
  obtain ⟨hW, hWne, hW1, U, hU, hUW, hirr, hntriv, hdim2, hq⟩ := hsec
  let W' := W ⧸ U.comap W.subtype
  let σ : Representation k H W' := sectionRepresentation ρ U W hU hW
  have hσirr : σ.IsIrreducible := hirr
  have hσnt : ¬ σ.IsTrivial := hntriv
  have hdim_le : Module.finrank k W' ≤ Module.finrank k V := by
    calc
      Module.finrank k W' ≤ Module.finrank k W :=
        Submodule.finrank_quotient_le (U.comap W.subtype)
      _ ≤ Module.finrank k V := Submodule.finrank_le W
  have hσhom_ne_one : σ.asGroupHom ≠ 1 := by
    intro hone
    apply hσnt
    refine Representation.IsTrivial.mk (fun g => ?_)
    have hg : σ.asGroupHom g = 1 := congrArg (fun f => f g) hone
    simpa [Representation.asGroupHom_apply, Module.End.one_eq_id] using congrArg Units.val hg
  have hsep : σ.asGroupHom.ker ≤ γ.ker := by
    rcases ker_le_or_eq_one (L := S) (J := H) hH γ hγ hsol σ.asGroupHom with h | h
    · exact h
    · exact absurd h hσhom_ne_one
  let q : H →* σ.asGroupHom.range := σ.asGroupHom.rangeRestrict
  have hq : Function.Surjective q := σ.asGroupHom.rangeRestrict_surjective
  have hqker : q.ker = σ.asGroupHom.ker := MonoidHom.ker_rangeRestrict σ.asGroupHom
  have hle : q.ker ≤ γ.ker := by
    rw [hqker]
    exact hsep
  let γbar : H ⧸ q.ker →* S := QuotientGroup.lift q.ker γ hle
  let e : H ⧸ q.ker ≃* σ.asGroupHom.range :=
    QuotientGroup.quotientKerEquivOfSurjective q hq
  let γi : σ.asGroupHom.range →* S := γbar.comp e.symm.toMonoidHom
  have hγi_comp : γi.comp q = γ := by
    ext h
    have h1 : e.symm (q h) = (QuotientGroup.mk h : H ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change γbar (e.symm (q h)) = γ h
    rw [h1]
    rfl
  have hγi_surj : Function.Surjective γi := by
    intro s
    obtain ⟨h, rfl⟩ := hγ s
    exact ⟨q h, by
      have := congrArg (fun f : H →* S => f h) hγi_comp
      simpa using this⟩
  have hγi_ker_map : γi.ker = γ.ker.map q := by
    ext x
    constructor
    · intro hx
      obtain ⟨h, rfl⟩ := hq x
      refine ⟨h, ?_, rfl⟩
      have hcomp_h : γi (q h) = γ h :=
        congrArg (fun f : H →* S => f h) hγi_comp
      change γ h = 1
      rw [← hcomp_h]
      exact hx
    · rintro ⟨h, hh, rfl⟩
      show γi (q h) = 1
      have hcomp_h : γi (q h) = γ h :=
        congrArg (fun f : H →* S => f h) hγi_comp
      rw [hcomp_h]
      change γ h = 1 at hh
      exact hh
  have hγi_solv : Group.IsSolvable γi.ker := by
    let q' : γ.ker →* γi.ker :=
      (q.comp γ.ker.subtype).codRestrict γi.ker (by
        intro h
        rw [hγi_ker_map]
        exact Subgroup.mem_map_of_mem q h.2)
    have hq' : Function.Surjective q' := by
      intro x
      have hxmem : (x : σ.asGroupHom.range) ∈ γ.ker.map q := by
        rw [← hγi_ker_map]
        exact x.2
      obtain ⟨h, hh, hx⟩ := hxmem
      refine ⟨⟨h, hh⟩, ?_⟩
      apply Subtype.ext
      exact hx
    have : Group.IsSolvable γ.ker := hsol
    exact Group.isSolvable_of_surjective hq'
  have hfin : Finite σ.asGroupHom.range :=
    Finite.of_surjective q hq
  have hperf : Group.IsPerfect σ.asGroupHom.range :=
    Group.IsPerfect.ofSurjective (f := q) hq
  exact ⟨W', inferInstance, inferInstance, inferInstance, σ, hσirr, hσnt, hdim_le, hsep,
    hperf, γi, hfin, fun h => by
      have hqh : (q h : σ.asGroupHom.range) =
          ⟨σ.asGroupHom h, ⟨h, rfl⟩⟩ := Subtype.ext rfl
      rw [← hqh]
      exact congrArg (fun f : H →* S => f h) hγi_comp,
    hγi_surj, hγi_solv⟩

theorem map_ne_top_of_constituent_image
    {H S Hi : Type*} [Group H] [Group S] [Group Hi]
    (q : H →* Hi) (hq : Function.Surjective q)
    (γ : H →* S) (γi : Hi →* S) (hcomp : γi.comp q = γ)
    (hmin : ∀ K : Subgroup H, K ≠ ⊤ → K.map γ ≠ ⊤) :
    ∀ L : Subgroup Hi, L ≠ ⊤ → L.map γi ≠ ⊤ := by
  intro L hL hLtop
  let L' : Subgroup H := L.comap q
  have hL' : L' ≠ ⊤ := by
    intro htop
    apply hL
    rw [eq_top_iff]
    intro x _
    obtain ⟨h, rfl⟩ := hq x
    have hx : h ∈ L' := by
      rw [htop]
      exact Subgroup.mem_top h
    exact hx
  apply hmin L' hL'
  have hmapq : L'.map q = L := Subgroup.map_comap_eq_self_of_surjective hq L
  have hmap : L'.map γ = L.map γi := by
    rw [← hcomp]
    rw [← Subgroup.map_map]
    rw [hmapq]
  rw [hmap, hLtop]

theorem exists_minimal_linear_constituent_image
    {k : Type u} {H : Type v} {S : Type w} {V : Type x}
    [Field k] [Group H] [Finite H] [Group S] [IsSimpleGroup S]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hH : Group.IsPerfect H) (γ : H →* S) (hγ : Function.Surjective γ)
    (hnil : Group.IsNilpotent γ.ker)
    (hmincov : ∀ K : Subgroup H, K ≠ ⊤ → K.map γ ≠ ⊤)
    (ρ : Representation k H V) (hρ : Function.Injective ρ) :
    ∃ (m : ℕ) (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
      (σ : Representation k H W),
      m ≤ Module.finrank k V ∧
      Module.finrank k W = m ∧
      σ.IsIrreducible ∧ ¬ σ.IsTrivial ∧
      (∀ (r : ℕ) (ψ : H →* Matrix.GeneralLinearGroup (Fin r) k), ψ ≠ 1 → m ≤ r) ∧
      σ.asGroupHom.ker ≤ γ.ker ∧
      Group.IsPerfect σ.asGroupHom.range ∧
      Finite σ.asGroupHom.range ∧
      ∃ (γi : σ.asGroupHom.range →* S),
        (∀ h : H, γi ⟨σ.asGroupHom h, ⟨h, rfl⟩⟩ = γ h) ∧
        Function.Surjective γi ∧
        Group.IsNilpotent γi.ker ∧
        (∀ L : Subgroup σ.asGroupHom.range, L ≠ ⊤ → L.map γi ≠ ⊤) ∧
        (∀ (r : ℕ) (ψ : σ.asGroupHom.range →* Matrix.GeneralLinearGroup (Fin r) k),
          ψ ≠ 1 → m ≤ r) := by
  classical
  have : Nontrivial H := hγ.nontrivial
  have hρnt : ¬ ρ.IsTrivial := by
    intro htriv
    let : ρ.IsTrivial := htriv
    have hsub : Subsingleton H :=
      ⟨fun a b => hρ (by
        rw [Representation.isTrivial_def ρ a, Representation.isTrivial_def ρ b])⟩
    exact not_subsingleton H hsub
  let bV : Module.Basis (Fin (Module.finrank k V)) k V := Module.finBasis k V
  let eV : (V →ₗ[k] V)ˣ ≃* (V ≃ₗ[k] V) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
  let ψρ : H →* Matrix.GeneralLinearGroup (Fin (Module.finrank k V)) k :=
    bV.toGL.toMonoidHom.comp (eV.toMonoidHom.comp ρ.asGroupHom)
  have hψρnt : ψρ ≠ 1 := by
    intro hψ
    apply hρnt
    refine Representation.IsTrivial.mk (fun h => ?_)
    have hh : ψρ h = 1 := congrArg (fun f => f h) hψ
    have h1 : eV (ρ.asGroupHom h) = 1 := by
      apply bV.toGL.injective
      simpa [ψρ] using hh
    have h2 : ρ.asGroupHom h = 1 := eV.injective (by simpa using h1)
    simpa [Representation.asGroupHom_apply, Module.End.one_eq_id] using congrArg Units.val h2
  let P : ℕ → Prop := fun r =>
    ∃ ψ : H →* Matrix.GeneralLinearGroup (Fin r) k, ψ ≠ 1
  have hP : ∃ r, P r := ⟨Module.finrank k V, ψρ, hψρnt⟩
  let m : ℕ := Nat.find hP
  obtain ⟨ψ, hψnt⟩ := Nat.find_spec hP
  have hm_le_d : m ≤ Module.finrank k V := Nat.find_min' hP ⟨ψρ, hψρnt⟩
  have hminH : ∀ (r : ℕ) (ψ' : H →* Matrix.GeneralLinearGroup (Fin r) k),
      ψ' ≠ 1 → m ≤ r := fun r ψ' hψ' => Nat.find_min' hP ⟨ψ', hψ'⟩
  let bm : Module.Basis (Fin m) k (Fin m → k) := Pi.basisFun k (Fin m)
  let em : Matrix.GeneralLinearGroup (Fin m) k ≃* ((Fin m → k) ≃ₗ[k] (Fin m → k)) :=
    (Matrix.GeneralLinearGroup.toLin' bm).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin m → k))
  let ρψ : Representation k H (Fin m → k) :=
    { toFun := fun h => (em (ψ h) : (Fin m → k) →ₗ[k] (Fin m → k))
      map_one' := by
        change (em (ψ 1) : (Fin m → k) →ₗ[k] (Fin m → k)) = LinearMap.id
        rw [map_one ψ]
        simp [em]
      map_mul' := by
        intro x y
        change (em (ψ (x * y)) : (Fin m → k) →ₗ[k] (Fin m → k)) =
          ((em (ψ x) : (Fin m → k) →ₗ[k] (Fin m → k))).comp
            (em (ψ y) : (Fin m → k) →ₗ[k] (Fin m → k))
        rw [map_mul ψ, map_mul em]
        rfl }
  have hρψnt : ¬ ρψ.IsTrivial := by
    intro htriv
    apply hψnt
    refine MonoidHom.ext (fun h => ?_)
    have hh : ρψ h = LinearMap.id := Representation.isTrivial_def ρψ h
    have h1 : (em (ψ h) : (Fin m → k) →ₗ[k] (Fin m → k)) = LinearMap.id := by
      simpa [ρψ] using hh
    have h2 : em (ψ h) = 1 := by
      apply LinearEquiv.ext
      intro v
      simpa using congrArg (fun f => f v) h1
    exact em.injective (by simpa using h2)
  have hdim_fin : Module.finrank k (Fin m → k) = m := by
    simp [Module.finrank_fintype_fun_eq_card]
  have : Group.IsSolvable γ.ker := IsNilpotent.to_isSolvable
  obtain ⟨W₁, hW₁add, hW₁mod, hW₁fin, σ₁, hσ₁irr, hσ₁nt, hdim₁, hker,
    hperf, γi, hfin, hfac, hsurj, hsolv⟩ :=
    exists_nontrivial_irreducible_constituent_image
      hH γ hγ inferInstance ρψ hρψnt
  let bW : Module.Basis (Fin (Module.finrank k W₁)) k W₁ := Module.finBasis k W₁
  let eW : (W₁ →ₗ[k] W₁)ˣ ≃* (W₁ ≃ₗ[k] W₁) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv k W₁
  let ψσ : H →* Matrix.GeneralLinearGroup (Fin (Module.finrank k W₁)) k :=
    bW.toGL.toMonoidHom.comp (eW.toMonoidHom.comp σ₁.asGroupHom)
  have hψσnt : ψσ ≠ 1 := by
    intro hψ
    apply hσ₁nt
    refine Representation.IsTrivial.mk (fun h => ?_)
    have hh : ψσ h = 1 := congrArg (fun f => f h) hψ
    have h1 : eW (σ₁.asGroupHom h) = 1 := by
      apply bW.toGL.injective
      simpa [ψσ] using hh
    have h2 : σ₁.asGroupHom h = 1 := eW.injective (by simpa using h1)
    simpa [Representation.asGroupHom_apply, Module.End.one_eq_id] using congrArg Units.val h2
  have hm_le_dim₁ : m ≤ Module.finrank k W₁ := hminH _ ψσ hψσnt
  have hdim₁_le_m : Module.finrank k W₁ ≤ m := by
    simpa [hdim_fin] using hdim₁
  have hdim₁_eq_m : Module.finrank k W₁ = m := le_antisymm hdim₁_le_m hm_le_dim₁
  let q : H →* σ₁.asGroupHom.range := σ₁.asGroupHom.rangeRestrict
  have hq : Function.Surjective q := σ₁.asGroupHom.rangeRestrict_surjective
  have hcomp : γi.comp q = γ := by
    ext h
    have hqh : (q h : σ₁.asGroupHom.range) =
        ⟨σ₁.asGroupHom h, ⟨h, rfl⟩⟩ := Subtype.ext rfl
    rw [MonoidHom.comp_apply, hqh]
    exact hfac h
  have hker_map : γi.ker = γ.ker.map q := by
    ext x
    constructor
    · intro hx
      obtain ⟨h, rfl⟩ := hq x
      refine ⟨h, ?_, rfl⟩
      have hcomp_h : γi (q h) = γ h :=
        congrArg (fun f : H →* S => f h) hcomp
      change γ h = 1
      rw [← hcomp_h]
      exact hx
    · rintro ⟨h, hh, rfl⟩
      show γi (q h) = 1
      have hcomp_h : γi (q h) = γ h :=
        congrArg (fun f : H →* S => f h) hcomp
      rw [hcomp_h]
      change γ h = 1 at hh
      exact hh
  have hnilγi : Group.IsNilpotent γi.ker := by
    let q' : γ.ker →* γi.ker :=
      (q.comp γ.ker.subtype).codRestrict γi.ker (by
        intro h
        rw [hker_map]
        exact Subgroup.mem_map_of_mem q h.2)
    have hq' : Function.Surjective q' := by
      intro x
      have hxmem : (x : σ₁.asGroupHom.range) ∈ γ.ker.map q := by
        rw [← hker_map]
        exact x.2
      obtain ⟨h, hh, hx⟩ := hxmem
      refine ⟨⟨h, hh⟩, ?_⟩
      apply Subtype.ext
      exact hx
    have : Group.IsNilpotent γ.ker := hnil
    exact Group.nilpotent_of_surjective q' hq'
  have hminimg : ∀ L : Subgroup σ₁.asGroupHom.range, L ≠ ⊤ → L.map γi ≠ ⊤ :=
    map_ne_top_of_constituent_image q hq γ γi hcomp hmincov
  have hminγi : ∀ (r : ℕ) (ψ' : σ₁.asGroupHom.range →* Matrix.GeneralLinearGroup (Fin r) k),
      ψ' ≠ 1 → m ≤ r := by
    intro r ψ' hψ'
    apply hminH r (ψ'.comp q)
    intro hcomp_one
    apply hψ'
    refine MonoidHom.ext (fun x => ?_)
    obtain ⟨h, rfl⟩ := hq x
    have hval : ψ' (q h) = 1 := by
      simpa using congrArg (fun f : H →* Matrix.GeneralLinearGroup (Fin r) k => f h) hcomp_one
    exact hval
  exact ⟨m, W₁, hW₁add, hW₁mod, hW₁fin, σ₁, hm_le_d, hdim₁_eq_m, hσ₁irr, hσ₁nt,
    hminH, hker, hperf, hfin, γi, hfac, hsurj, hnilγi, hminimg, hminγi⟩

end CFSG.RepresentationTheory
