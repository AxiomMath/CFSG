module

public import CFSG.RankThree.PartTwo.KFacts.KS116LinBasic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts.NDC

section StabilityGroup

open Representation

variable {F : Type*} [Field F] {G : Type*} [Group G]
  {V : Type*} [AddCommGroup V] [Module F V]

section SubQuot

variable (ρ : Representation F G V) (U : Submodule F V) (hU : ∀ g, U ≤ U.comap (ρ g))

theorem sub_apply_eq_one_iff (g : G) :
    ρ.subrepresentation U hU g = 1 ↔ ∀ u ∈ U, ρ g u = u := by
  constructor
  · intro h u hu
    have := LinearMap.congr_fun h ⟨u, hu⟩
    simpa using congrArg Subtype.val this
  · intro h
    ext u
    simpa using h u u.2

theorem quot_apply_eq_one_iff (g : G) :
    ρ.quotient U hU g = 1 ↔ ∀ v, ρ g v - v ∈ U := by
  constructor
  · intro h v
    have := LinearMap.congr_fun h (Submodule.Quotient.mk v)
    simp only [quotient_apply, Submodule.mapQ_apply, Module.End.one_apply] at this
    exact (Submodule.Quotient.eq U).mp this
  · intro h
    ext v
    simp only [quotient_apply, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, LinearMap.id_comp]
    exact (Submodule.Quotient.eq U).mpr (h v)

theorem trivial_of_sub_quot {S : Subgroup G} (hS : ⁅S, S⁆ = S)
    (h1 : ∀ s ∈ S, ρ.subrepresentation U hU s = 1) (h2 : ∀ s ∈ S, ρ.quotient U hU s = 1) :
    ∀ s ∈ S, ρ s = 1 := by
  have h1' : ∀ s ∈ S, ∀ u ∈ U, ρ s u = u := fun s hs =>
    (sub_apply_eq_one_iff ρ U hU s).mp (h1 s hs)
  have h2' : ∀ s ∈ S, ∀ v, ρ s v - v ∈ U := fun s hs =>
    (quot_apply_eq_one_iff ρ U hU s).mp (h2 s hs)
  have hprod : ∀ a ∈ S, ∀ b ∈ S, (ρ a - 1) * (ρ b - 1) = 0 := by
    intro a ha b hb
    ext v
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply]
    rw [h1' a ha _ (h2' b hb v), sub_self]
  let f : S →* Multiplicative (V →ₗ[F] V) :=
    MonoidHom.mk' (fun s => Multiplicative.ofAdd (ρ (s : G) - 1)) fun a b => by
      show Multiplicative.ofAdd (ρ ((a * b : S) : G) - 1) =
        Multiplicative.ofAdd (ρ (a : G) - 1) * Multiplicative.ofAdd (ρ (b : G) - 1)
      rw [← ofAdd_add]
      congr 1
      have hmul : ρ ((a * b : S) : G) = ρ (a : G) * ρ (b : G) := by
        rw [Subgroup.coe_mul, map_mul]
      have key : ρ (a : G) * ρ (b : G) - 1 - ((ρ (a : G) - 1) + (ρ (b : G) - 1)) =
          (ρ (a : G) - 1) * (ρ (b : G) - 1) := by noncomm_ring
      rw [hmul]
      exact sub_eq_zero.mp (key.trans (hprod a a.2 b b.2))
  intro s hs
  have hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hS
  have := eq_one_of_perfect_of_comm f hperf (Subgroup.mem_top (⟨s, hs⟩ : S))
  have h3 : ρ s - 1 = 0 := by
    have h4 : Multiplicative.ofAdd (ρ s - 1) = (1 : Multiplicative (V →ₗ[F] V)) := this
    exact ofAdd_eq_one.mp h4
  rwa [sub_eq_zero] at h3

end SubQuot

end StabilityGroup

section CommuteBasics

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

theorem comm_of_finrank_le_one [Module.Finite F V] (h : Module.finrank F V ≤ 1)
    (φ ψ : V →ₗ[F] V) : φ * ψ = ψ * φ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    ext v
    simp [Subsingleton.elim v 0]
  · obtain ⟨a, ha⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1 φ).exists
    obtain ⟨b, hb⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1 ψ).exists
    rw [ha, hb]
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      mul_comm]

theorem perfect_trivial_of_comm (ρ : Representation F G V) {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hc : ∀ a ∈ K, ∀ b ∈ K, ρ a * ρ b = ρ b * ρ a) : ∀ k ∈ K, ρ k = 1 := by
  have hinv : ∀ g : G, ρ g * ρ g⁻¹ = 1 := fun g => by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, ρ ⁅a, b⁆ = 1 := by
    intro a ha b hb
    rw [commutatorElement_def, map_mul, map_mul, map_mul, hc a ha b hb,
      mul_assoc (ρ b) (ρ a) (ρ a⁻¹), hinv a, mul_one, hinv b]
  have hle : K ≤ (MonoidHom.toHomUnits ρ).ker := by
    rw [← hK, Subgroup.commutator_le]
    intro x hx y hy
    rw [MonoidHom.mem_ker, ← Units.val_eq_one, MonoidHom.coe_toHomUnits]
    exact hcomm x hx y hy
  intro k hk
  have h1 : MonoidHom.toHomUnits ρ k = 1 := hle hk
  have h2 := congrArg Units.val h1
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h2

theorem two_le_finrank_of_perfect_nontrivial [Module.Finite F V] (ρ : Representation F G V)
    {K : Subgroup G} (hK : ⁅K, K⁆ = K) (h : ∃ k ∈ K, ρ k ≠ 1) :
    2 ≤ Module.finrank F V := by
  by_contra hlt
  have h1 : Module.finrank F V ≤ 1 := by omega
  have hc : ∀ a ∈ K, ∀ b ∈ K, ρ a * ρ b = ρ b * ρ a := fun a _ b _ =>
    comm_of_finrank_le_one h1 (ρ a) (ρ b)
  obtain ⟨k, hk, hne⟩ := h
  exact hne (perfect_trivial_of_comm ρ hK hc k hk)

theorem sub_mul_comm (ρ : Representation F G V) (U : Submodule F V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) {a b : G} (h : ρ a * ρ b = ρ b * ρ a) :
    ρ.subrepresentation U hU a * ρ.subrepresentation U hU b =
      ρ.subrepresentation U hU b * ρ.subrepresentation U hU a := by
  refine LinearMap.ext fun u => Subtype.ext ?_
  have hv := LinearMap.congr_fun h (u : V)
  simpa [Representation.subrepresentation_apply, Module.End.mul_apply] using hv

theorem quot_mul_comm (ρ : Representation F G V) (U : Submodule F V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) {a b : G} (h : ρ a * ρ b = ρ b * ρ a) :
    ρ.quotient U hU a * ρ.quotient U hU b = ρ.quotient U hU b * ρ.quotient U hU a := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U x
  have hv := LinearMap.congr_fun h v
  simp only [Module.End.mul_apply] at hv
  simp only [Module.End.mul_apply, Representation.quotient_apply, Submodule.mapQ_apply, hv]

private theorem commutant_comm_aux [Finite F] [Module.Finite F V] (𝒮 : Set (V →ₗ[F] V))
    (hnt : Nontrivial V)
    (hirr : ∀ U : Submodule F V, (∀ s ∈ 𝒮, ∀ u ∈ U, s u ∈ U) → U = ⊥ ∨ U = ⊤)
    (φ ψ : V →ₗ[F] V) (hφ : ∀ s ∈ 𝒮, φ ∘ₗ s = s ∘ₗ φ) (hψ : ∀ s ∈ 𝒮, ψ ∘ₗ s = s ∘ₗ ψ) :
    φ ∘ₗ ψ = ψ ∘ₗ φ := by
  classical
  set R : Subalgebra F (V →ₗ[F] V) := Algebra.adjoin F 𝒮 with hR
  have hVfin : Finite V := Module.finite_of_finite F
  haveI : IsSimpleModule R V := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨hnt, fun x hx => ?_⟩
    set Ux : Submodule F V := (LinearMap.range (LinearMap.toSpanSingleton R V x)).restrictScalars F
      with hUx
    have hx_mem : x ∈ Ux := ⟨1, by simp⟩
    have hinv : ∀ s ∈ 𝒮, ∀ u ∈ Ux, s u ∈ Ux := by
      rintro s hs u ⟨r, rfl⟩
      refine ⟨⟨s, Algebra.subset_adjoin hs⟩ * r, ?_⟩
      simp [LinearMap.toSpanSingleton_apply, mul_smul]
      rfl
    have hne : Ux ≠ ⊥ := fun hb => hx (by simpa [hb] using hx_mem)
    have htop : Ux = ⊤ := (hirr Ux hinv).resolve_left hne
    intro w
    have : w ∈ Ux := by rw [htop]; trivial
    exact this
  haveI : Finite (Module.End R V) :=
    Finite.of_injective (fun f : Module.End R V => (f : V → V)) DFunLike.coe_injective
  have hcomm : ∀ a b : Module.End R V, a * b = b * a := by
    intro a b
    letI : DivisionRing (Module.End R V) := Module.End.instDivisionRing
    letI : Field (Module.End R V) := littleWedderburn _
    exact mul_comm a b
  have hcentr : ∀ χ : V →ₗ[F] V, (∀ s ∈ 𝒮, χ ∘ₗ s = s ∘ₗ χ) →
      ∀ r ∈ R, χ ∘ₗ r = r ∘ₗ χ := by
    intro χ hχ
    have hle : R ≤ Subalgebra.centralizer F {χ} := by
      refine Algebra.adjoin_le fun s hs => ?_
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hχ s hs
    intro r hr
    have hr' := hle hr
    rw [Subalgebra.mem_centralizer_iff] at hr'
    exact hr' χ (Set.mem_singleton χ)
  let toEnd : ∀ χ : V →ₗ[F] V, (∀ s ∈ 𝒮, χ ∘ₗ s = s ∘ₗ χ) → Module.End R V := fun χ hχ =>
    { toFun := χ
      map_add' := χ.map_add
      map_smul' := fun r v => by
        have := hcentr χ hχ r.1 r.2
        exact LinearMap.congr_fun this v }
  have := hcomm (toEnd φ hφ) (toEnd ψ hψ)
  ext v
  exact congrArg (fun f : Module.End R V => f v) this

theorem schur_commute [Finite F] [Module.Finite F V] [Nontrivial V] (ρ : Representation F G V)
    (B : Subgroup G)
    (hirr : ∀ U : Submodule F V, (∀ b ∈ B, U ≤ U.comap (ρ b)) → U = ⊥ ∨ U = ⊤)
    (φ ψ : V →ₗ[F] V) (hφ : ∀ b ∈ B, φ * ρ b = ρ b * φ) (hψ : ∀ b ∈ B, ψ * ρ b = ρ b * ψ) :
    φ * ψ = ψ * φ := by
  have hirr' : ∀ U : Submodule F V,
      (∀ s ∈ Set.range fun b : B => ρ (b : G), ∀ u ∈ U, s u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    apply hirr U
    intro b hb
    intro u hu
    exact Submodule.mem_comap.mpr (hU (ρ b) ⟨⟨b, hb⟩, rfl⟩ u hu)
  have hφ' : ∀ s ∈ Set.range fun b : B => ρ (b : G), φ ∘ₗ s = s ∘ₗ φ := by
    rintro s ⟨⟨b, hb⟩, rfl⟩
    have h' := hφ b hb
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp] at h'
    exact h'
  have hψ' : ∀ s ∈ Set.range fun b : B => ρ (b : G), ψ ∘ₗ s = s ∘ₗ ψ := by
    rintro s ⟨⟨b, hb⟩, rfl⟩
    have h' := hψ b hb
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp] at h'
    exact h'
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  exact commutant_comm_aux (Set.range fun b : B => ρ (b : G)) inferInstance hirr' φ ψ hφ' hψ'

end Rep

end CommuteBasics

section LineFamily

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

theorem trivial_of_line_family [Module.Finite F V] (ρ : Representation F G V) {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) (𝒱 : Set (Submodule F V)) (hfin : 𝒱.Finite) (hcard : Nat.card 𝒱 ≤ 4)
    (hstable : ∀ g : G, ∀ W ∈ 𝒱, W.map (ρ g) ∈ 𝒱)
    (hline : ∀ W ∈ 𝒱, Module.finrank F W = 1) (hsup : sSup 𝒱 = ⊤) :
    ∀ k ∈ K, ρ k = 1 := by
  haveI : Finite 𝒱 := hfin.to_subtype
  let act : G → 𝒱 → 𝒱 := fun g W => ⟨(W : Submodule F V).map (ρ g), hstable g W W.2⟩
  have h1 : ∀ s, act 1 s = s := by
    intro s
    apply Subtype.ext
    show (s : Submodule F V).map (ρ 1) = s
    rw [map_one]
    exact Submodule.map_id _
  have hmul : ∀ m m' s, act (m * m') s = act m (act m' s) := by
    intro m m' s
    apply Subtype.ext
    simp only [act, map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  have hfix : ∀ k ∈ K, ∀ W ∈ 𝒱, W.map (ρ k) = W := by
    intro k hk W hW
    exact congrArg Subtype.val (perfect_act_trivial hcard act h1 hmul hK hk ⟨W, hW⟩)
  intro k hk
  have hline_fix : ∀ W ∈ 𝒱, ∀ u ∈ W, ρ k u = u := by
    intro W hW
    let ρ' : Representation F K V := ρ.comp K.subtype
    have hW' : ∀ g : K, W ≤ W.comap (ρ' g) := fun g w hw => by
      have : ρ (g : G) w ∈ W.map (ρ g) := Submodule.mem_map_of_mem hw
      rw [hfix (g : G) g.2 W hW] at this
      exact this
    have hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hK
    have hcomm : ∀ a ∈ (⊤ : Subgroup K), ∀ b ∈ (⊤ : Subgroup K),
        ρ'.subrepresentation W hW' a * ρ'.subrepresentation W hW' b =
          ρ'.subrepresentation W hW' b * ρ'.subrepresentation W hW' a :=
      fun _ _ _ _ => comm_of_finrank_le_one (hline W hW).le _ _
    have hone := perfect_trivial_of_comm (ρ'.subrepresentation W hW') hperf hcomm ⟨k, hk⟩
      (Subgroup.mem_top _)
    exact fun u hu => (sub_apply_eq_one_iff ρ' W hW' ⟨k, hk⟩).mp hone u hu
  have hle : sSup 𝒱 ≤ LinearMap.ker (ρ k - 1) := by
    refine sSup_le fun W hW u hu => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hline_fix W hW u hu,
      sub_self]
  rw [hsup] at hle
  ext v
  have hv : v ∈ LinearMap.ker (ρ k - 1) := hle Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
  exact hv

theorem commute_of_scalar_commutators (ρ : Representation F G V) (A B : Subgroup G)
    (hB : ⁅B, B⁆ = B)
    (hsc : ∀ a ∈ A, ∀ b ∈ B, ∃ c : F, ρ ⁅a, b⁆ = c • (1 : V →ₗ[F] V)) :
    ∀ a ∈ A, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a := by
  intro a ha b hb
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact LinearMap.ext fun v => Subsingleton.elim _ _
  have hscal : ∀ x y : F, x • (1 : V →ₗ[F] V) = y • 1 → x = y := by
    intro x y h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : (x - y) • v = 0 := by
      rw [sub_smul]
      have := congrArg (fun φ : V →ₗ[F] V => φ v) h
      simpa [sub_eq_zero] using this
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv
  choose! c hc using hsc a ha
  have hperf : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hB
  have hc1 : c 1 = 1 := by
    have h := hc 1 B.one_mem
    rw [commutatorElement_one_right, map_one] at h
    exact hscal (c 1) 1 (by rw [one_smul]; exact h.symm)
  have hmul : ∀ x y : G, x ∈ B → y ∈ B → c (x * y) = c x * c y := by
    intro x y hx hy
    apply hscal
    have hid : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hx' : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [← hc (x * y) (B.mul_mem hx hy), hid]
    simp only [map_mul]
    rw [hc x hx, hc y hy]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_smul, hx']
    rw [mul_comm]
  have hperfB : ∀ x ∈ B, ρ ⁅a, x⁆ = 1 := by
    intro x hx
    let f : B →* F :=
      { toFun := fun y => c y
        map_one' := hc1
        map_mul' := fun y z => hmul y z y.2 z.2 }
    have hf : f ⟨x, hx⟩ = 1 := eq_one_of_perfect_of_comm f hperf (Subgroup.mem_top _)
    have hcx : c x = 1 := hf
    rw [hc x hx, hcx, one_smul]
  have hunit : ρ.toHomUnits ⁅a, b⁆ = 1 := Units.ext (hperfB b hb)
  rw [map_commutatorElement] at hunit
  have hcomm := congrArg Units.val (commutatorElement_eq_one_iff_mul_comm.mp hunit)
  simpa using hcomm

end Rep

end LineFamily

end CFSG.RankThree.PartTwo.KFacts.NDC

end
