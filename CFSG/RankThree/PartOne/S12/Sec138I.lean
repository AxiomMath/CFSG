module

public import CFSG.RankThree.PartOne.S12.Sec138ILinear
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.S12.Sec138Trans
import CFSG.RankThree.PartOne.S12.Sec127

public section

namespace CFSG.RankThree.PartOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped commutatorElement

namespace Sec138I

theorem exists_reflData {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] (T : V ≃ₗ[ZMod 5] V) (hT : T * T = 1)
    (hrank : Module.finrank (ZMod 5)
      (LinearMap.range ((T : V →ₗ[ZMod 5] V) - LinearMap.id)) = 1) :
    ∃ (r : V) (φ : V →ₗ[ZMod 5] ZMod 5), ReflData T r φ := by
  set g : V →ₗ[ZMod 5] V := (T : V →ₗ[ZMod 5] V) - LinearMap.id with hg
  have hgx : ∀ x, g x = T x - x := fun x => rfl
  have hpos : 0 < Module.finrank (ZMod 5) (LinearMap.range g) := by omega
  obtain ⟨⟨r, hrS⟩, hr0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hr : r ≠ 0 := fun h0 => hr0 (Subtype.ext h0)
  have hSeq : LinearMap.range g = Submodule.span (ZMod 5) {r} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrank hrS hr
  have hmem : ∀ x, g x ∈ Submodule.span (ZMod 5) ({r} : Set V) := fun x => by
    rw [← hSeq]
    exact LinearMap.mem_range_self g x
  let φ' : V →ₗ[ZMod 5] ZMod 5 :=
    (LinearEquiv.coord (ZMod 5) V r hr).toLinearMap ∘ₗ
      g.codRestrict (Submodule.span (ZMod 5) {r}) hmem
  have hφ' : ∀ x, g x = φ' x • r := fun x =>
    (LinearEquiv.coord_apply_smul (R := ZMod 5) (M := V) r hr ⟨g x, hmem x⟩).symm
  have hTx : ∀ x, T x = x - (-φ') x • r := by
    intro x
    have h1 := hφ' x
    rw [hgx] at h1
    rw [LinearMap.neg_apply, neg_smul, sub_neg_eq_add, ← h1]
    abel
  have hTr : T r = (1 - (-φ') r) • r := by
    rw [hTx r]
    module
  have hsq : (1 - (-φ') r) ^ 2 = 1 := by
    have h1 : T (T r) = r := by
      have := congrArg (fun S : V ≃ₗ[ZMod 5] V => S r) hT
      exact this
    rw [hTr, map_smul, hTr, smul_smul] at h1
    have h2 : ((1 - (-φ') r) * (1 - (-φ') r) - 1) • r = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    have h3 := smul_eq_zero_of_ne hr h2
    linear_combination h3
  have hcases : ∀ a : ZMod 5, (1 - a) ^ 2 = 1 → a = 0 ∨ a = 2 := by decide
  rcases hcases _ hsq with h0 | h2
  · exfalso
    have hzero : ∀ x, (-φ') x = 0 := by
      intro x
      have h1 : T (T x) = x := by
        have := congrArg (fun S : V ≃ₗ[ZMod 5] V => S x) hT
        exact this
      have hTr' : T r = r := by
        rw [hTr, h0, sub_zero, one_smul]
      have h2 : (-φ') (T x) = (-φ') x := by
        rw [hTx x, map_sub, map_smul, h0, smul_zero, sub_zero]
      have h3 : T (T x) = x - 2 • ((-φ') x • r) := by
        rw [hTx (T x), h2, hTx x]
        module
      rw [h3] at h1
      have h4 : (2 * (-φ') x) • r = 0 := by
        have : x - 2 • ((-φ') x • r) = x := h1
        have h5 : (2 : ZMod 5) • ((-φ') x • r) = 0 := by
          have := sub_eq_self.1 this
          simpa [two_smul] using this
        rw [mul_smul]
        simpa using h5
      have h6 := smul_eq_zero_of_ne hr h4
      rcases mul_eq_zero_five _ _ h6 with h | h
      · exact absurd h (by decide)
      · exact h
    have hg0 : g = 0 := by
      ext x
      rw [hφ' x]
      have := hzero x
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      rw [this, zero_smul]
      rfl
    rw [hg0, LinearMap.range_zero] at hrank
    simp at hrank
  · exact ⟨r, -φ', hr, h2, hTx⟩

section Spaces

open Equiv

variable {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]

theorem mem_rootSpace_swap {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)} {x y : Fin 5} (hxy : x ≠ y)
    (v : V) : ρ (swap x y) v - v ∈ rootSpace ρ := by
  unfold rootSpace
  refine Submodule.mem_iSup_of_mem x ?_
  refine Submodule.mem_iSup_of_mem y ?_
  refine Submodule.mem_iSup_of_mem hxy ?_
  exact ⟨v, rfl⟩

theorem sub_mem_rootSpace (ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)) (σ : Perm (Fin 5)) :
    ∀ v : V, ρ σ v - v ∈ rootSpace ρ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    intro v
    rw [map_one]
    exact sub_self v ▸ (rootSpace ρ).zero_mem
  | swap_mul f x y hxy ih =>
    intro v
    have h1 := mem_rootSpace_swap (ρ := ρ) hxy (ρ f v)
    have h2 := ih v
    have e : ρ (swap x y * f) v - v = (ρ (swap x y) (ρ f v) - ρ f v) + (ρ f v - v) := by
      rw [map_mul, LinearEquiv.mul_apply]
      abel
    rw [e]
    exact add_mem h1 h2

end Spaces

section Subspaces

open Equiv

variable {G : Type} [Group G]

@[expose] noncomputable def rho {E : Subgroup G} (f : Multiplicative (Fin 4 → ZMod 5) ≃* E)
    (Γ : Subgroup (MulAut E)) (ψ : Γ ≃* Perm (Fin 5)) :
    Perm (Fin 5) →* ((Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) :=
  (LinAlg.coordHom f).comp (Γ.subtype.comp ψ.symm.toMonoidHom)

theorem rho_apply {E : Subgroup G} (f : Multiplicative (Fin 4 → ZMod 5) ≃* E)
    (Γ : Subgroup (MulAut E)) (ψ : Γ ≃* Perm (Fin 5)) (σ : Perm (Fin 5)) :
    rho f Γ ψ σ = LinAlg.coordHom f ((ψ.symm σ : Γ) : MulAut E) :=
  rfl

theorem bsub_sup {E : Subgroup G} (f : Multiplicative (Fin 4 → ZMod 5) ≃* E) {B₁ B₂ : Subgroup G}
    (h₁ : B₁ ≤ E) (h₂ : B₂ ≤ E) :
    LinAlg.bsub f (B₁ ⊔ B₂) = LinAlg.bsub f B₁ ⊔ LinAlg.bsub f B₂ := by
  unfold LinAlg.bsub
  rw [Subgroup.subgroupOf_sup h₁ h₂]
  exact (LinAlg.subSpaceEquiv f).map_sup _ _

theorem bsub_commutator_le_rootSpace {E L : Subgroup G}
    (f : Multiplicative (Fin 4 → ZMod 5) ≃* E) (ψ : torusImage E L ≃* Perm (Fin 5)) :
    LinAlg.bsub f ⁅E, L ⊓ torusNormalizer E⁆ ≤ rootSpace (rho f (torusImage E L) ψ) := by
  set ρ := rho f (torusImage E L) ψ with hρ
  have hcomm : ⁅E, L ⊓ torusNormalizer E⁆ ≤
      (LinAlg.spaceSubgroup f (rootSpace ρ)).map E.subtype := by
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    have hgN : g₂ ∈ Subgroup.normalizer (E : Set G) := hg₂.2
    let g : Subgroup.normalizer (E : Set G) := ⟨g₂, hgN⟩
    let e : E := ⟨g₁, hg₁⟩
    let v : Fin 4 → ZMod 5 := Multiplicative.toAdd (f.symm e)
    have hΓ : E.normalizerMonoidHom g ∈ torusImage E L :=
      ⟨g, Subgroup.mem_subgroupOf.2 hg₂.1, rfl⟩
    have h1 := sub_mem_rootSpace ρ (ψ ⟨E.normalizerMonoidHom g, hΓ⟩) v
    have hρσ : ρ (ψ ⟨E.normalizerMonoidHom g, hΓ⟩) = LinAlg.wAction f g := by
      rw [rho_apply, MulEquiv.symm_apply_apply]
      rfl
    rw [hρσ] at h1
    have hfe : f (Multiplicative.ofAdd v) = e := by
      simp [v]
    have hw := LinAlg.wAction_apply f g v
    rw [hfe] at hw
    refine Subgroup.mem_map.2 ⟨f (Multiplicative.ofAdd (v - LinAlg.wAction f g v)), ?_, ?_⟩
    · rw [LinAlg.mem_spaceSubgroup, MulEquiv.symm_apply_apply, toAdd_ofAdd]
      have := (rootSpace ρ).neg_mem h1
      simpa using this
    · rw [ofAdd_sub, map_div, hfe]
      show ((e / f (Multiplicative.ofAdd (LinAlg.wAction f g v)) : E) : G) = ⁅g₁, g₂⁆
      rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, hw, commutatorElement_def]
      show g₁ * (g₂ * g₁ * g₂⁻¹)⁻¹ = _
      group
  intro v hv
  obtain ⟨k, hk, hkv⟩ := Subgroup.mem_map.1 (hcomm hv)
  have hkf : k = f (Multiplicative.ofAdd v) := Subtype.ext hkv
  have := (LinAlg.mem_spaceSubgroup f (rootSpace ρ) k).1 hk
  rw [hkf, MulEquiv.symm_apply_apply, toAdd_ofAdd] at this
  exact this

theorem bsub_zpowers_le_fixedSpace {E L : Subgroup G} {c : G} (hLc : ∀ x ∈ L, c * x = x * c)
    (f : Multiplicative (Fin 4 → ZMod 5) ≃* E) (ψ : torusImage E L ≃* Perm (Fin 5)) :
    LinAlg.bsub f (Subgroup.zpowers c) ≤ fixedSpace (rho f (torusImage E L) ψ) := by
  intro v hv σ
  have hγ := (ψ.symm σ).2
  obtain ⟨g, hgL, hg⟩ := Subgroup.mem_map.1 hγ
  have hgL' : (g : G) ∈ L := Subgroup.mem_subgroupOf.1 hgL
  have hvc : (f (Multiplicative.ofAdd v) : G) ∈ Subgroup.zpowers c := hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hvc
  have hcomm : (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ =
      (f (Multiplicative.ofAdd v) : G) := by
    rw [← hk]
    have hc : Commute c (g : G) := hLc _ hgL'
    rw [mul_inv_eq_iff_eq_mul]
    exact ((hc.zpow_left k).symm.eq).symm ▸ rfl
  have hwa := LinAlg.wAction_apply f g v
  rw [rho_apply]
  have hcoord : LinAlg.coordHom f ((ψ.symm σ : torusImage E L) : MulAut E) v =
      LinAlg.wAction f g v := by
    rw [← hg]
    rfl
  rw [hcoord]
  have h2 : f (Multiplicative.ofAdd (LinAlg.wAction f g v)) = f (Multiplicative.ofAdd v) := by
    apply Subtype.ext
    rw [hwa, hcomm]
  have h3 := f.injective h2
  exact Multiplicative.ofAdd.injective h3

end Subspaces

section Aux

open Equiv

variable {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]

theorem rootSpace_le_ker {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)} {φ : V →ₗ[ZMod 5] ZMod 5}
    (h : ∀ a b : Fin 5, a ≠ b → ∀ x : V, φ (ρ (swap a b) x - x) = 0) :
    rootSpace ρ ≤ LinearMap.ker φ := by
  unfold rootSpace
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  rintro _ ⟨x, rfl⟩
  exact h a b hab x

theorem reflection_unique {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)}
    (hspan : rootSpace ρ ⊔ fixedSpace ρ = ⊤) {v : V}
    (hv : ∀ y ∈ fixedSpace ρ, y ∈ Submodule.span (ZMod 5) {v})
    {s s' : V ≃ₗ[ZMod 5] V} {r r' : V} {φ φ' : V →ₗ[ZMod 5] ZMod 5}
    (hs : ReflData s r φ) (hs' : ReflData s' r' φ')
    (hφ : rootSpace ρ ≤ LinearMap.ker φ) (hφ' : rootSpace ρ ≤ LinearMap.ker φ')
    (hr : r ∈ fixedSpace ρ) (hr' : r' ∈ fixedSpace ρ) : s = s' := by
  ext x
  have hx : x ∈ rootSpace ρ ⊔ fixedSpace ρ := by
    rw [hspan]
    trivial
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 (hv r hr)
  obtain ⟨α', hα'⟩ := Submodule.mem_span_singleton.1 (hv r' hr')
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 (hv y hy)
  have hpair : α * φ v = 2 := by
    have h2 := hs.pair
    rw [← hα, map_smul, smul_eq_mul] at h2
    exact h2
  have hpair' : α' * φ' v = 2 := by
    have h2 := hs'.pair
    rw [← hα', map_smul, smul_eq_mul] at h2
    exact h2
  have e1 : φ (u + y) • r = (2 * μ) • v := by
    rw [map_add, show φ u = 0 from hφ hu, zero_add, ← hμ, map_smul, smul_eq_mul, ← hα, smul_smul]
    congr 1
    linear_combination μ * hpair
  have e2 : φ' (u + y) • r' = (2 * μ) • v := by
    rw [map_add, show φ' u = 0 from hφ' hu, zero_add, ← hμ, map_smul, smul_eq_mul, ← hα',
      smul_smul]
    congr 1
    linear_combination μ * hpair'
  show s (u + y) = s' (u + y)
  rw [hs.apply, hs'.apply, e1, e2]

@[expose] def fixSub (S : Set (V ≃ₗ[ZMod 5] V)) : Submodule (ZMod 5) V where
  carrier := {x | ∀ t ∈ S, t x = x}
  add_mem' := by
    intro a b ha hb t ht
    rw [map_add, ha t ht, hb t ht]
  zero_mem' := by
    intro t _
    exact map_zero _
  smul_mem' := by
    intro c x hx t ht
    rw [map_smul, hx t ht]

theorem fixSub_map_le (S : Set (V ≃ₗ[ZMod 5] V)) (g : V ≃ₗ[ZMod 5] V)
    (hS : ∀ t ∈ S, g⁻¹ * t * g ∈ S) : (fixSub S).map g.toLinearMap ≤ fixSub S := by
  rintro _ ⟨x, hx, rfl⟩ t ht
  have h1 : (g⁻¹ * t * g) x = x := hx _ (hS t ht)
  have h3 : (g⁻¹ * t * g) x = g.symm (t (g x)) := rfl
  rw [h3] at h1
  have h4 := congrArg g h1
  rwa [LinearEquiv.apply_symm_apply] at h4

theorem swap_noncomm_five : ∀ a b c : Fin 5, a ≠ b → b ≠ c → a ≠ c →
    swap a b * swap b c ≠ swap b c * swap a b := by
  decide +kernel

theorem exists_third : ∀ a b : Fin 5, ∃ c : Fin 5, c ≠ a ∧ c ≠ b := by
  decide

end Aux

section Main

open Equiv CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def tau {E L : Subgroup G} (ψ : torusImage E L ≃* Perm (Fin 5))
    (a b : Fin 5) : MulAut E :=
  ((ψ.symm (swap a b) : torusImage E L) : MulAut E)

omit [Finite G] in
theorem tau_mem {E L : Subgroup G} (ψ : torusImage E L ≃* Perm (Fin 5)) (a b : Fin 5) :
    tau ψ a b ∈ torusImage E L :=
  (ψ.symm (swap a b)).2

omit [Finite G] in
theorem tau_mul {E L : Subgroup G} (ψ : torusImage E L ≃* Perm (Fin 5)) (a b c d : Fin 5) :
    tau ψ a b * tau ψ c d = ((ψ.symm (swap a b * swap c d) : torusImage E L) : MulAut E) := by
  simp [tau, map_mul]

omit [Finite G] in
theorem eq_tau {E L : Subgroup G} (ψ : torusImage E L ≃* Perm (Fin 5)) {t : MulAut E}
    (ht : t ∈ torusImage E L) {a b : Fin 5} (h : ψ ⟨t, ht⟩ = swap a b) : t = tau ψ a b := by
  have h1 : ψ.symm (swap a b) = ⟨t, ht⟩ := (MulEquiv.symm_apply_eq ψ).2 h.symm
  rw [tau, h1]

omit [Finite G] in
theorem fix_of_coordHom {E : Subgroup G} (f : Multiplicative (Fin 4 → ZMod 5) ≃* E)
    (γ : MulAut E) {y : Fin 4 → ZMod 5} (hy : LinAlg.coordHom f γ y = y) :
    γ (f (Multiplicative.ofAdd y)) = f (Multiplicative.ofAdd y) := by
  calc γ (f (Multiplicative.ofAdd y)) = f (Multiplicative.ofAdd (LinAlg.coordLin f γ y)) :=
        (LinAlg.apply_coordLin f γ y).symm
    _ = f (Multiplicative.ofAdd y) := by
        have h : LinAlg.coordLin f γ y = y := hy
        rw [h]

omit [Finite G] in
theorem irreducible_space {E : Subgroup G} (f : Multiplicative (Fin 4 → ZMod 5) ≃* E)
    (hirr : torusIrreducible E) (U : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    (hU : ∀ φ ∈ torusWeyl E, U.map (LinAlg.coordLin f φ).toLinearMap ≤ U) : U = ⊥ ∨ U = ⊤ := by
  obtain ⟨B, hBE, hB⟩ := LinAlg.exists_bsub_eq f U
  have hinv : torusInvariant E ⊤ B := by
    refine (LinAlg.torusInvariant_top_iff f hBE).2 fun φ hφ => ?_
    rw [hB]
    exact hU φ hφ
  rcases hirr B hBE hinv with h | h
  · left
    rw [← hB, h]
    exact LinAlg.bsub_bot f
  · right
    rw [← hB, h]
    exact LinAlg.bsub_self f

end Main

section PartOne

open Equiv CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem part_one (h137 : Node137Any) (A : Subgroup G) (c : G) (L E : Subgroup G)
    (h : Sec12Hyp G 5 A c L E) (hF12 : Sec12Facts G 5 A c L E) (hF13 : Sec13Facts G 5 A c L E)
    (hT : ¬ Outcome152Five 5 E A (lieGenerated 5 E)) (hEA : E ≠ A)
    (hS5 : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 5))) : False := by
  have hprime : Nat.Prime 5 := Nat.prime_five
  have hel : IsElementaryAbelian 5 E := h.E_elem
  obtain ⟨hclosure, r, hr1, hr12, -, -, hr8, hr9⟩ := hF12.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hr8 (by omega))
  have hcard : Nat.card E = 5 ^ 4 := hr9 hr9'
  obtain ⟨f⟩ := LinAlg.exists_coords (p := 5) E hcard
  obtain ⟨ψ⟩ := hS5
  have hD3 : ThreeTranspD 5 E := h137 G 5 A c L E h hF12 hF13 hT hEA
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hLc : ∀ x ∈ L, c * x = x * c := Sec12Three.comm_c_L h
  have hswapD : ∀ t ∈ reflectionSet 5 E, ∀ ht : t ∈ torusImage E L,
      ∃ a b : Fin 5, a ≠ b ∧ ψ ⟨t, ht⟩ = swap a b := fun t htD ht =>
    Sec137.isSwap_of_reflection (by norm_num) f (torusImage E L) (Or.inr rfl) ψ ht htD.1
  have hD_in : ∀ t ∈ reflectionSet 5 E, t ∈ torusImage E L →
      ∃ a b : Fin 5, a ≠ b ∧ t = tau ψ a b := by
    intro t ht htΓ
    obtain ⟨a, b, hab, h1⟩ := hswapD t ht htΓ
    exact ⟨a, b, hab, eq_tau ψ htΓ h1⟩
  have hex : ∃ t ∈ reflectionSet 5 E, t ∈ torusImage E L := by
    by_contra hcon
    push Not at hcon
    have hempty : reflectionSet 5 E ∩ (torusImage E L : Set (MulAut E)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun t ht => hcon t ht.1 ht.2
    rw [hempty, Subgroup.closure_empty] at hclosure
    have h120 : Nat.card (torusImage E L) = 120 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    rw [hclosure, Subgroup.card_bot] at h120
    omega
  have hall : ∀ a b : Fin 5, a ≠ b → tau ψ a b ∈ reflectionSet 5 E := by
    obtain ⟨t0, ht0D, ht0Γ⟩ := hex
    obtain ⟨a0, b0, hab0, ht0⟩ := hD_in t0 ht0D ht0Γ
    intro a b hab
    obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_swap hab0 hab)
    have hxD : ((ψ.symm g : torusImage E L) : MulAut E) * t0 *
        ((ψ.symm g : torusImage E L) : MulAut E)⁻¹ ∈ reflectionSet 5 E :=
      WeylIso.conj_mem_reflectionSet_of_weyl hprime
        (Sec138Trans.torusImage_le_torusWeyl E L (ψ.symm g).2) ht0D
    have h1 : tau ψ a b = ((ψ.symm g : torusImage E L) : MulAut E) * t0 *
        ((ψ.symm g : torusImage E L) : MulAut E)⁻¹ := by
      rw [ht0]
      have h2 : ψ.symm (swap a b) = ψ.symm g * ψ.symm (swap a0 b0) * (ψ.symm g)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← hg]
      show ((ψ.symm (swap a b) : torusImage E L) : MulAut E) = _
      rw [h2]
      rfl
    rw [h1]
    exact hxD
  have hrefl : ∀ t ∈ reflectionSet 5 E, ∃ (r : Fin 4 → ZMod 5)
      (φ : (Fin 4 → ZMod 5) →ₗ[ZMod 5] ZMod 5), ReflData (LinAlg.coordHom f t) r φ := by
    intro t ht
    obtain ⟨hord, hrk⟩ := (LinAlg.isAutReflection_iff f t).1 ht.1
    refine exists_reflData _ ?_ hrk
    have h2 := pow_orderOf_eq_one (LinAlg.coordHom f t)
    rw [hord, pow_two] at h2
    exact h2
  have hSw : SwapRep (rho f (torusImage E L) ψ) := by
    refine ⟨fun σ σ' hσ => ?_, fun a b hab => ?_⟩
    · have h1 : LinAlg.coordHom f ((ψ.symm σ : torusImage E L) : MulAut E) =
          LinAlg.coordHom f ((ψ.symm σ' : torusImage E L) : MulAut E) := hσ
      exact ψ.symm.injective (Subtype.ext (LinAlg.coordHom_injective f h1))
    · exact hrefl _ (hall a b hab)
  have hE : E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ := by
    rcases hF12.four.2 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · rw [h2]
      exact (sup_eq_right.2 (Subgroup.zpowers_le.2 hcE)).symm
  have hspan : rootSpace (rho f (torusImage E L) ψ) ⊔ fixedSpace (rho f (torusImage E L) ψ) =
      ⊤ := by
    have hb : LinAlg.bsub f (Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆) = ⊤ := by
      rw [← hE]
      exact LinAlg.bsub_self f
    rw [bsub_sup f (Subgroup.zpowers_le.2 hcE) (Sec12Three.commutator_le_left E L)] at hb
    rw [eq_top_iff, ← hb]
    exact sup_le (le_trans (bsub_zpowers_le_fixedSpace hLc f ψ) le_sup_right)
      (le_trans (bsub_commutator_le_rootSpace f ψ) le_sup_left)
  obtain ⟨vc, hvc⟩ : ∃ vc : Fin 4 → ZMod 5, ((f (Multiplicative.ofAdd vc) : E) : G) = c :=
    ⟨Multiplicative.toAdd (f.symm ⟨c, hcE⟩), by simp⟩
  have hvc0 : vc ≠ 0 := by
    intro h0
    rw [h0, ofAdd_zero, map_one] at hvc
    exact h.c_ne_one hvc.symm
  have hvcline : vc ∈ Submodule.span (ZMod 5) {vc} := Submodule.mem_span_singleton_self vc
  have hvcfix : ∀ σ : Perm (Fin 5), rho f (torusImage E L) ψ σ vc = vc := by
    have h1 : vc ∈ LinAlg.bsub f (Subgroup.zpowers c) := by
      rw [Sec127.bsub_zpowers_eq_span f hvc]
      exact hvcline
    exact bsub_zpowers_le_fixedSpace hLc f ψ h1
  have hF1 : ∀ y ∈ fixedSpace (rho f (torusImage E L) ψ), y ∈ Submodule.span (ZMod 5) {vc} := by
    intro y hy
    obtain ⟨t0, ht0D, ht0Γ⟩ := hex
    rw [← Sec127.bsub_zpowers_eq_span f hvc, LinAlg.mem_bsub]
    have hmem : ((f (Multiplicative.ofAdd y) : E) : G) ∈ Sec138Trans.fixedByImage E L := by
      refine ⟨(f (Multiplicative.ofAdd y)).2, fun γ hγ => ?_⟩
      have h1 := hy (ψ ⟨γ, hγ⟩)
      have h2 : rho f (torusImage E L) ψ (ψ ⟨γ, hγ⟩) = LinAlg.coordHom f γ := by
        rw [rho_apply, MulEquiv.symm_apply_apply]
      rw [h2] at h1
      exact fix_of_coordHom f γ h1
    rw [Sec138Trans.fixedByImage_eq_zpowers h hF12 ht0D.1 ht0Γ] at hmem
    exact hmem
  by_cases hext : ∃ s ∈ reflectionSet 5 E, s ∉ torusImage E L
  ·
    obtain ⟨s, hsD, hsΓ⟩ := hext
    have hextra : ∀ s ∈ reflectionSet 5 E, s ∉ torusImage E L →
        (∀ a b : Fin 5, a ≠ b → s * tau ψ a b = tau ψ a b * s) ∧
        ∃ (r : Fin 4 → ZMod 5) (φ : (Fin 4 → ZMod 5) →ₗ[ZMod 5] ZMod 5),
          ReflData (LinAlg.coordHom f s) r φ ∧
          rootSpace (rho f (torusImage E L) ψ) ≤ LinearMap.ker φ ∧
          r ∈ fixedSpace (rho f (torusImage E L) ψ) := by
      intro s hsD hsΓ
      obtain ⟨r, φ, hr⟩ := hrefl s hsD
      have hne : ∀ a b : Fin 5, a ≠ b →
          LinAlg.coordHom f s ≠ rho f (torusImage E L) ψ (swap a b) := by
        intro a b _ heq
        exact hsΓ (by rw [LinAlg.coordHom_injective f heq]; exact tau_mem ψ a b)
      have hord : ∀ a b : Fin 5, a ≠ b →
          orderOf (LinAlg.coordHom f s * rho f (torusImage E L) ψ (swap a b)) ≤ 3 := by
        intro a b hab
        have h1 : rho f (torusImage E L) ψ (swap a b) = LinAlg.coordHom f (tau ψ a b) := rfl
        rw [h1, ← map_mul, orderOf_injective (LinAlg.coordHom f) (LinAlg.coordHom_injective f)]
        exact hD3 s hsD _ (hall a b hab)
      obtain ⟨hcomm, hker, hfix⟩ := part_one_core hSw hspan hr hne hord
      refine ⟨fun a b hab => ?_, r, φ, hr, rootSpace_le_ker hker, fun σ => hfix σ⟩
      apply LinAlg.coordHom_injective f
      rw [map_mul, map_mul]
      exact hcomm a b hab
    have huniq : ∀ s ∈ reflectionSet 5 E, s ∉ torusImage E L → ∀ s' ∈ reflectionSet 5 E,
        s' ∉ torusImage E L → s = s' := by
      intro s hsD hsΓ s' hs'D hs'Γ
      obtain ⟨-, r, φ, hr, hφ, hrf⟩ := hextra s hsD hsΓ
      obtain ⟨-, r', φ', hr', hφ', hrf'⟩ := hextra s' hs'D hs'Γ
      exact LinAlg.coordHom_injective f (reflection_unique hspan hF1 hr hr' hφ hφ' hrf hrf')
    have hsd : ∀ d ∈ reflectionSet 5 E, s * d = d * s := by
      intro d hd
      by_cases hdΓ : d ∈ torusImage E L
      · obtain ⟨a, b, hab, rfl⟩ := hD_in d hd hdΓ
        exact (hextra s hsD hsΓ).1 a b hab
      · rw [huniq d hd hdΓ s hsD hsΓ]
    have hcentral : ∀ w ∈ torusWeyl E, w * s * w⁻¹ = s := by
      intro w hw
      have hz'D : w * s * w⁻¹ ∈ reflectionSet 5 E :=
        WeylIso.conj_mem_reflectionSet_of_weyl hprime hw hsD
      have hz'd : ∀ d ∈ reflectionSet 5 E, (w * s * w⁻¹) * d = d * (w * s * w⁻¹) := by
        intro d hd
        have hd' : w⁻¹ * d * w ∈ reflectionSet 5 E := by
          have h1 := WeylIso.conj_mem_reflectionSet_of_weyl hprime (inv_mem hw) hd
          rwa [inv_inv] at h1
        have h1 := hsd _ hd'
        calc w * s * w⁻¹ * d = w * (s * (w⁻¹ * d * w)) * w⁻¹ := by group
          _ = w * ((w⁻¹ * d * w) * s) * w⁻¹ := by rw [h1]
          _ = d * (w * s * w⁻¹) := by group
      by_cases hz'Γ : w * s * w⁻¹ ∈ torusImage E L
      · exfalso
        obtain ⟨a, b, hab, hτ⟩ := hD_in _ hz'D hz'Γ
        obtain ⟨c', hc'a, hc'b⟩ := exists_third a b
        have h1 := hz'd _ (hall b c' (Ne.symm hc'b))
        rw [hτ, tau_mul, tau_mul] at h1
        have h2 := ψ.symm.injective (Subtype.ext h1)
        exact swap_noncomm_five a b c' hab (Ne.symm hc'b) (Ne.symm hc'a) h2
      · exact huniq _ hz'D hz'Γ s hsD hsΓ
    obtain ⟨hord, hrk⟩ := (LinAlg.isAutReflection_iff f s).1 hsD.1
    have hinv : ∀ φ ∈ torusWeyl E, (LinearMap.range (LinAlg.coordSub f s)).map
        (LinAlg.coordLin f φ).toLinearMap ≤ LinearMap.range (LinAlg.coordSub f s) := by
      intro φ hφ
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      have hc : φ * s = s * φ := by
        have h1 := hcentral φ hφ
        rwa [mul_inv_eq_iff_eq_mul] at h1
      have hcc : LinAlg.coordHom f φ * LinAlg.coordHom f s =
          LinAlg.coordHom f s * LinAlg.coordHom f φ := by
        rw [← map_mul, ← map_mul, hc]
      have h2 : LinAlg.coordHom f φ (LinAlg.coordHom f s x) =
          LinAlg.coordHom f s (LinAlg.coordHom f φ x) :=
        congrArg (fun T : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) => T x) hcc
      refine ⟨LinAlg.coordLin f φ x, ?_⟩
      show LinAlg.coordHom f s (LinAlg.coordHom f φ x) - LinAlg.coordHom f φ x =
        LinAlg.coordHom f φ (LinAlg.coordHom f s x - x)
      rw [map_sub, h2]
    rcases irreducible_space f hF13.irreducible _ hinv with h0 | h0
    · rw [h0, finrank_bot] at hrk
      exact absurd hrk (by norm_num)
    · rw [h0, finrank_top, Module.finrank_fin_fun] at hrk
      exact absurd hrk (by norm_num)
  ·
    push Not at hext
    let S : Set ((Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) :=
      LinAlg.coordHom f '' reflectionSet 5 E
    have hinv : ∀ φ ∈ torusWeyl E,
        (fixSub S).map (LinAlg.coordLin f φ).toLinearMap ≤ fixSub S := by
      intro φ hφ
      refine fixSub_map_le S (LinAlg.coordHom f φ) ?_
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨φ⁻¹ * t * φ, ?_, ?_⟩
      · have h1 := WeylIso.conj_mem_reflectionSet_of_weyl hprime (inv_mem hφ) ht
        rwa [inv_inv] at h1
      · rw [map_mul, map_mul, map_inv]
    have hvcZ : vc ∈ fixSub S := by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨a, b, hab, rfl⟩ := hD_in t ht (hext t ht)
      exact hvcfix (swap a b)
    have hZtop : fixSub S ≠ ⊤ := by
      intro htop
      obtain ⟨t0, ht0D, -⟩ := hex
      obtain ⟨r, φ, hr⟩ := hrefl t0 ht0D
      have hrZ : r ∈ fixSub S := by
        rw [htop]
        trivial
      have h1 := hrZ _ ⟨t0, ht0D, rfl⟩
      rw [hr.apply_root] at h1
      have h2 : (2 : ZMod 5) • r = 0 := by
        rw [two_smul]
        exact neg_eq_iff_add_eq_zero.1 h1
      exact absurd (smul_eq_zero_of_ne hr.ne h2) (by decide)
    rcases irreducible_space f hF13.irreducible _ hinv with h0 | h0
    · rw [h0] at hvcZ
      exact hvc0 ((Submodule.mem_bot _).1 hvcZ)
    · exact hZtop h0

end PartOne

end Sec138I

theorem node138I_of_node137 (h137 : Node137Any) : Node138I := by
  intro G _ _ p A c L E h hF12 hF13 hT hEA
  have key : p = 5 → Nonempty (torusImage E L ≃* Equiv.Perm (Fin 5)) → False := by
    rintro rfl hS5
    exact Sec138I.part_one h137 A c L E h hF12 hF13 hT hEA hS5
  exact ⟨fun ⟨hmodel, hweyl⟩ => key hmodel.1 hweyl, fun ⟨hmodel, hweyl⟩ => key hmodel.1 hweyl⟩

end CFSG.RankThree.PartOne
