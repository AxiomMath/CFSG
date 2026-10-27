module

public import CFSG.LocalAnalysis.StandardType.GGResIBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Ker

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}

@[expose] noncomputable def ggResIRootsJ (α : Option Λ → Module.Dual (ZMod p) V) :
    V →ₗ[ZMod p] ({i : Λ // i ≠ b} → ZMod p) :=
  LinearMap.pi fun j => α (some j.1)

theorem ggResIRootsJ_surjective [FiniteDimensional (ZMod p) V]
    {α : Option Λ → Module.Dual (ZMod p) V}
    (hind : LinearIndependent (ZMod p) (fun j : {i : Λ // i ≠ b} => α (some j.1))) :
    Function.Surjective (ggResIRootsJ (b := b) α) := by
  classical
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  have hcomb : ∑ j : {i : Λ // i ≠ b}, ψ (Pi.single j 1) • α (some j.1) = 0 := by
    ext v
    have h1 := congrArg (fun f : Module.Dual (ZMod p) V => f v) hψ
    simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at h1
    have hv : ggResIRootsJ (b := b) α v =
        ∑ j : {i : Λ // i ≠ b}, α (some j.1) v • Pi.single j (1 : ZMod p) := by
      ext j
      simp [ggResIRootsJ, Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h0 := (Fintype.linearIndependent_iff.mp hind) _ hcomb
  refine LinearMap.pi_ext fun j c => ?_
  rw [LinearMap.zero_apply, show Pi.single j c = c • Pi.single j (1 : ZMod p) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, h0 j, smul_zero]

theorem ggResI_card_kerJ [Finite V] {α : Option Λ → Module.Dual (ZMod p) V}
    (hdim : Module.finrank (ZMod p) V = Fintype.card Λ + 1)
    (hind : LinearIndependent (ZMod p) (fun j : {i : Λ // i ≠ b} => α (some j.1))) :
    Nat.card (LinearMap.ker (ggResIRootsJ (b := b) α)) = p ^ 2 := by
  classical
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  have hsurj := ggResIRootsJ_surjective (b := b) hind
  have hrk := LinearMap.finrank_range_add_finrank_ker (ggResIRootsJ (b := b) α)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card] at hrk
  have hcardJ : Fintype.card {i : Λ // i ≠ b} + 1 = Fintype.card Λ := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card Λ := Fintype.card_pos_iff.mpr ⟨b⟩
    omega
  have hk : Module.finrank (ZMod p) (LinearMap.ker (ggResIRootsJ (b := b) α)) = 2 := by omega
  rw [← FiniteField.pow_finrank_eq_natCard p, hk]

end Ker

theorem ggResI_fixJ_le_D {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hr : ∀ j : Λ, j ≠ b → GGIsReflection p (φ (some j)))
    (hdim : Module.finrank (ZMod p) V = Fintype.card Λ + 1)
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)))
    (hind : LinearIndependent (ZMod p) (fun j : {i : Λ // i ≠ b} => α (some j.1))) :
    (∀ c : ↥Bs, (∀ j : Λ, j ≠ b → α (some j) (ι (Additive.ofMul c)) = 0) → (c : G) ∈ D) ∧
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hDB : D ≤ B := hH.1.2.2.1.1
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hDBJ : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hh0 : ∀ j : Λ, j ≠ b → h (some j) ≠ 0 := by
    intro j hj h0
    have hid : φ (some j) = 1 := by
      apply ggLin_injective (p := p) ι
      ext w
      rw [hφ, h0, smul_zero, sub_zero, map_one]
      rfl
    obtain ⟨-, hc⟩ := hr j hj
    rw [hid] at hc
    simp only [MulAut.one_apply] at hc
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have hc' : Nat.card {b : ↥Bs // True} * p = Nat.card ↥Bs := by simpa using hc
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at hc'
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    nlinarith
  have hkill : ∀ c : ↥Bs, (∀ ψ ∈ ggAutomizer J Bs, ψ c = c) →
      ∀ j : Λ, j ≠ b → α (some j) (ι (Additive.ofMul c)) = 0 := by
    intro c hc j hj
    have hmem : φ (some j) ∈ ggAutomizer J Bs := by
      rw [hJ]
      exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩
    have hf := (ggLin_fix_iff (p := p) ι (φ (some j)) c).mp (hc _ hmem)
    rw [hφ, sub_eq_self] at hf
    exact (smul_eq_zero.mp hf).resolve_right (hh0 j hj)
  set F := LinearMap.ker (ggResIRootsJ (b := b) α)
  have hF : Nat.card F = p ^ 2 := ggResI_card_kerJ hdim hind
  have hDF : ∀ d : D, ι (Additive.ofMul (⟨d.1, hBBs (hDB d.2)⟩ : ↥Bs)) ∈ F := by
    intro d
    have hJd : J ≤ Subgroup.centralizer ({d.1} : Set G) := by
      intro g hg
      have hdC : d.1 ∈ Subgroup.centralizer (J : Set G) :=
        ((SetLike.ext_iff.mp hDBJ d.1).mp d.2).2
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ((Subgroup.mem_centralizer_iff.mp hdC) g hg).symm
    have hfix := ggResI_automizer_fix (hBBs (hDB d.2)) hJd
    have hk := hkill _ hfix
    rw [LinearMap.mem_ker]
    ext j
    exact hk j.1 j.2
  let f : D → F := fun d => ⟨_, hDF d⟩
  have hfinj : Function.Injective f := by
    intro d₁ d₂ h12
    have := congrArg Subtype.val h12
    simp only [f] at this
    have h3 := Additive.ofMul.injective (ι.injective this)
    have h4 : (d₁ : G) = d₂ := congrArg (fun c : ↥Bs => (c : G)) h3
    exact Subtype.ext h4
  have hfbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, by rw [hDcard, hF]⟩
  have hmain : ∀ c : ↥Bs, (∀ j : Λ, j ≠ b → α (some j) (ι (Additive.ofMul c)) = 0) →
      (c : G) ∈ D := by
    intro c hc
    have hcF : ι (Additive.ofMul c) ∈ F := by
      rw [LinearMap.mem_ker]
      ext j
      exact hc j.1 j.2
    obtain ⟨d, hd⟩ := hfbij.2 ⟨_, hcF⟩
    have := congrArg Subtype.val hd
    simp only [f] at this
    have hcd := Additive.ofMul.injective (ι.injective this)
    rw [← hcd]
    exact d.2
  refine ⟨hmain, fun c hc => ?_⟩
  obtain ⟨hcBs, hcJ⟩ := hc
  refine hmain ⟨c, hcBs⟩ (hkill ⟨c, hcBs⟩ fun ψ hψ => ?_)
  refine ggResI_automizer_fix hcBs (fun g hg => ?_) ψ hψ
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact ((Subgroup.mem_centralizer_iff.mp hcJ) g hg).symm

end CFSG.StandardType
