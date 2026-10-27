module

public import CFSG.LocalAnalysis.UniquenessCase.UCK461b
public import CFSG.GH74.Generic.BProg.B2.GenLocPsl2Full
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.FFModules (fixSub)
open CFSG.LocalAnalysis.UniquenessCase.UC6

section Operators

variable {R : Type*} [Ring R]

theorem conj_eq_sq_mul_uc64 (h2 : ∀ y : R, y + y = 0) {A X : R} (hX3 : X * X * X = 1)
    (hN : 1 + X + X * X = 0) (hA : A + X * A * (X * X) + X * X * A * X = 0) :
    X * A * (X * X) = X * X * A := by
  have hneg : ∀ y : R, -y = y := fun y => neg_eq_iff_add_eq_zero.2 (h2 y)
  have hX2 : X * X = 1 + X := by
    have : X * X = -(1 + X) := eq_neg_of_add_eq_zero_right hN
    rw [this, hneg]
  have e1 : X * A + X * X * A * (X * X) + A * X = 0 := by
    have h := congrArg (fun y => X * y) hA
    simp only [mul_add, mul_zero] at h
    have r1 : X * (X * A * (X * X)) = X * X * A * (X * X) := by noncomm_ring
    have r2 : X * (X * X * A * X) = A * X := by
      calc X * (X * X * A * X) = (X * X * X) * A * X := by noncomm_ring
        _ = A * X := by rw [hX3, one_mul]
    rwa [r1, r2] at h
  have e2 : X * X * A * (X * X) = X * A * X + X * A + A * X + A := by
    rw [hX2]
    noncomm_ring
  have e3 : X * A * X + A = 0 := by
    rw [e2] at e1
    have h' : X * A + (X * A * X + X * A + A * X + A) + A * X =
        (X * A * X + A) + (X * A + X * A) + (A * X + A * X) := by abel
    rw [h', h2 (X * A), h2 (A * X), add_zero, add_zero] at e1
    exact e1
  have e4 : X * A * X = A := by
    have : X * A * X = -A := eq_neg_of_add_eq_zero_left e3
    rw [this, hneg]
  calc X * A * (X * X) = (X * A * X) * X := by noncomm_ring
    _ = A * X := by rw [e4]
    _ = (X * X * X) * A * X := by rw [hX3, one_mul]
    _ = X * X * (X * A * X) := by noncomm_ring
    _ = X * X * A := by rw [e4]

end Operators

section Klein

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_uc64 (v : V) : v + v = 0 := by
  have h : v + v = (1 + 1 : ZMod 2) • v := by rw [add_smul, one_smul]
  rw [h, show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]

theorem end_add_self_uc64 (f : Module.End (ZMod 2) V) : f + f = 0 :=
  LinearMap.ext fun v => add_self_uc64 (f v)

theorem fix_iff_of_klein_uc64 (ρ : Representation (ZMod 2) G V) {x a b : G} (hx3 : x * x * x = 1)
    (hCV : ∀ v, ρ x v = v → v = 0) (hb : b = x * a * x⁻¹) (hxb : x * b * x⁻¹ = a * b)
    (hq : ∀ v, ρ a (ρ b v - v) = ρ b v - v) (v : V) : ρ b v = v ↔ ρ a v = v := by
  have hxinv : x⁻¹ = x * x := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc]
    exact hx3
  have hX3 : ρ x * ρ x * ρ x = 1 := by rw [← map_mul, ← map_mul, hx3, map_one]
  have h3 : ∀ w : V, ρ x (ρ x (ρ x w)) = w := fun w => by
    have := congrArg (fun F : Module.End (ZMod 2) V => F w) hX3
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hN : 1 + ρ x + ρ x * ρ x = 0 := by
    apply LinearMap.ext
    intro w
    have hfix : ρ x (w + ρ x w + ρ x (ρ x w)) = w + ρ x w + ρ x (ρ x w) := by
      rw [map_add, map_add, h3]
      abel
    simpa only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply,
      LinearMap.zero_apply] using hCV _ hfix
  have hb' : b = x * a * (x * x) := by rw [hb, hxinv]
  have hab' : a * b = x * x * a * x := by
    rw [← hxb, hb', hxinv]
    calc x * (x * a * (x * x)) * (x * x) = x * x * a * (x * x * x) * x := by group
      _ = x * x * a * x := by rw [hx3, mul_one]
  have hB : ρ b - 1 = ρ x * (ρ a - 1) * (ρ x * ρ x) := by
    rw [hb', map_mul, map_mul, map_mul]
    calc ρ x * ρ a * (ρ x * ρ x) - 1 = ρ x * ρ a * (ρ x * ρ x) - ρ x * ρ x * ρ x := by rw [hX3]
      _ = ρ x * (ρ a - 1) * (ρ x * ρ x) := by noncomm_ring
  have hC : ρ (a * b) - 1 = ρ x * ρ x * (ρ a - 1) * ρ x := by
    rw [hab', map_mul, map_mul, map_mul]
    calc ρ x * ρ x * ρ a * ρ x - 1 = ρ x * ρ x * ρ a * ρ x - ρ x * ρ x * ρ x := by rw [hX3]
      _ = ρ x * ρ x * (ρ a - 1) * ρ x := by noncomm_ring
  have hAB : (ρ a - 1) * (ρ b - 1) = 0 := by
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply]
    rw [hq w, sub_self]
  have hCq : ρ (a * b) - 1 = (ρ a - 1) + (ρ b - 1) := by
    have : ρ (a * b) - 1 = (ρ a - 1) * (ρ b - 1) + (ρ a - 1) + (ρ b - 1) := by
      rw [map_mul]
      noncomm_ring
    rw [this, hAB, zero_add]
  have hsum : (ρ a - 1) + ρ x * (ρ a - 1) * (ρ x * ρ x) + ρ x * ρ x * (ρ a - 1) * ρ x = 0 := by
    rw [← hB, ← hC, hCq]
    have h' : (ρ a - 1) + (ρ b - 1) + ((ρ a - 1) + (ρ b - 1)) =
        ((ρ a - 1) + (ρ a - 1)) + ((ρ b - 1) + (ρ b - 1)) := by abel
    rw [h', end_add_self_uc64, end_add_self_uc64, add_zero]
  have hB2 : ρ b - 1 = ρ x * ρ x * (ρ a - 1) := by
    rw [hB]
    exact conj_eq_sq_mul_uc64 end_add_self_uc64 hX3 hN hsum
  have key : (ρ b - 1) v = ρ x (ρ x ((ρ a - 1) v)) := by
    rw [hB2]
    rfl
  constructor
  · intro h
    have h1 : ρ x (ρ x ((ρ a - 1) v)) = 0 := by
      rw [← key]
      simp [h]
    have h2 : (ρ a - 1) v = 0 := by
      calc (ρ a - 1) v = ρ x (ρ x (ρ x ((ρ a - 1) v))) := (h3 _).symm
        _ = 0 := by rw [h1, map_zero]
    simpa [sub_eq_zero] using h2
  · intro h
    have h1 : (ρ a - 1) v = 0 := by simp [h]
    have h2 : (ρ b - 1) v = 0 := by rw [key, h1, map_zero, map_zero]
    simpa [sub_eq_zero] using h2

theorem false_of_klein_uc64 [IsSimpleGroup G] (ρ : Representation (ZMod 2) G V) (hV : ∃ k v, ρ k v ≠ v)
    {x a b : G} (hx3 : x * x * x = 1) (hCV : ∀ v, ρ x v = v → v = 0) (hb : b = x * a * x⁻¹)
    (hxb : x * b * x⁻¹ = a * b) (hab : a ≠ b) (ha2 : a * a = 1) (hq : ∀ v, ρ a (ρ b v - v) = ρ b v - v)
    (hgen : centralizer ({a} : Set G) ⊔ centralizer ({b} : Set G) = ⊤) : False := by
  have hfix := fix_iff_of_klein_uc64 ρ hx3 hCV hb hxb hq
  have hgi : ∀ (g : G) (w : V), ρ g⁻¹ (ρ g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hig : ∀ (g : G) (w : V), ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinj : ∀ (g : G) {w w' : V}, ρ g w = ρ g w' → w = w' := fun g w w' h => by
    rw [← hgi g w, h, hgi]
  let St : Subgroup G :=
    { carrier := {g | ∀ v, ρ a (ρ g v) = ρ g v ↔ ρ a v = v}
      one_mem' := by
        intro v
        simp
      mul_mem' := fun {g h} hg hh v => by
        simp only [Set.mem_setOf_eq] at hg hh
        rw [map_mul, Module.End.mul_apply, hg, hh]
      inv_mem' := fun {g} hg v => by
        simp only [Set.mem_setOf_eq] at hg
        have := hg (ρ g⁻¹ v)
        rw [hig] at this
        exact this.symm }
  have hCa : centralizer ({a} : Set G) ≤ St := by
    intro g hg v
    have hc : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hcv : ρ a (ρ g v) = ρ g (ρ a v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply]
    rw [hcv]
    exact ⟨hinj g, fun h => by rw [h]⟩
  have hCb : centralizer ({b} : Set G) ≤ St := by
    intro g hg v
    have hc : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hcv : ρ b (ρ g v) = ρ g (ρ b v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply]
    rw [← hfix (ρ g v), ← hfix v, hcv]
    exact ⟨hinj g, fun h => by rw [h]⟩
  have hSt : St = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le hCa hCb
  have hinv : ∀ (g : G) (w : V), ρ a (ρ g w) = ρ g w ↔ ρ a w = w := fun g =>
    (show g ∈ St from hSt ▸ Subgroup.mem_top g)
  have hZadd : ∀ z₁ z₂ : V, ρ a z₁ = z₁ → ρ a z₂ = z₂ → ρ a (z₁ + z₂) = z₁ + z₂ :=
    fun z₁ z₂ h₁ h₂ => by rw [map_add, h₁, h₂]
  have hZneg : ∀ z : V, ρ a z = z → ρ a (-z) = -z := fun z h => by rw [map_neg, h]
  let N : Subgroup G :=
    { carrier := {g | ∀ v, ρ a (ρ g v - v) = ρ g v - v ∧ (ρ a v = v → ρ g v = v)}
      one_mem' := by
        intro v
        simp
      mul_mem' := fun {g h} hg hh v => by
        simp only [Set.mem_setOf_eq] at hg hh ⊢
        obtain ⟨hg1, -⟩ := hg (ρ h v)
        obtain ⟨hh1, hh2⟩ := hh v
        refine ⟨?_, fun hv => ?_⟩
        · have e : ρ (g * h) v - v = (ρ g (ρ h v) - ρ h v) + (ρ h v - v) := by
            rw [map_mul, Module.End.mul_apply]
            abel
          rw [e]
          exact hZadd _ _ hg1 hh1
        · rw [map_mul, Module.End.mul_apply, hh2 hv]
          exact (hg v).2 hv
      inv_mem' := fun {g} hg v => by
        simp only [Set.mem_setOf_eq] at hg ⊢
        obtain ⟨hg1, -⟩ := hg (ρ g⁻¹ v)
        refine ⟨?_, fun hv => ?_⟩
        · have e : ρ g⁻¹ v - v = -(ρ g (ρ g⁻¹ v) - ρ g⁻¹ v) := by
            rw [hig]
            abel
          rw [e]
          exact hZneg _ hg1
        · calc ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [(hg v).2 hv]
            _ = v := hgi g v }
  have hNn : N.Normal := ⟨fun g hg k v => by
    simp only [N, Subgroup.mem_mk, Set.mem_setOf_eq] at hg ⊢
    obtain ⟨hg1, -⟩ := hg (ρ k⁻¹ v)
    refine ⟨?_, fun hv => ?_⟩
    · have e : ρ (k * g * k⁻¹) v - v = ρ k (ρ g (ρ k⁻¹ v) - ρ k⁻¹ v) := by
        rw [map_sub, hig, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      rw [e]
      exact (hinv k _).2 hg1
    · have hv' : ρ a (ρ k⁻¹ v) = ρ k⁻¹ v := (hinv k⁻¹ v).2 hv
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hg (ρ k⁻¹ v)).2 hv', hig]⟩
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hab
    rw [hb, mul_one, mul_inv_cancel]
  have haN : a ∈ N := by
    intro v
    refine ⟨?_, fun hv => hv⟩
    have hrr : ρ a (ρ a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ha2, map_one, Module.End.one_apply]
    rw [map_sub, hrr, ← neg_sub]
    exact neg_eq_of_add_eq_zero_right (add_self_uc64 _)
  have hNtop : N = ⊤ := by
    haveI := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact absurd (h ▸ haN : a ∈ (⊥ : Subgroup G)) (by rw [Subgroup.mem_bot]; exact ha1)
    · exact h
  have hall : ∀ (g : G) (v : V), ρ a (ρ g v - v) = ρ g v - v ∧ (ρ a v = v → ρ g v = v) := fun g =>
    (show g ∈ N from hNtop ▸ Subgroup.mem_top g)
  have hcomm : ∀ g h : G, ρ (g * h) = ρ (h * g) := by
    intro g h
    apply LinearMap.ext
    intro v
    have e1 : ρ g (ρ h v) = (ρ h v - v) + ρ g v := by
      calc ρ g (ρ h v) = ρ g (ρ h v - v) + ρ g v := by rw [← map_add, sub_add_cancel]
        _ = (ρ h v - v) + ρ g v := by rw [(hall g (ρ h v - v)).2 (hall h v).1]
    have e2 : ρ h (ρ g v) = (ρ g v - v) + ρ h v := by
      calc ρ h (ρ g v) = ρ h (ρ g v - v) + ρ h v := by rw [← map_add, sub_add_cancel]
        _ = (ρ g v - v) + ρ h v := by rw [(hall h (ρ g v - v)).2 (hall g v).1]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, e2]
    abel
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hk | hk
  · have hxa : x * a = a * x := ((MonoidHom.ker_eq_bot_iff ρ).1 hk) (hcomm x a)
    apply hab
    rw [hb, hxa, mul_inv_cancel_right]
  · obtain ⟨k, v, hkv⟩ := hV
    have hk1 : ρ k = 1 := MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top k)
    exact hkv (by rw [hk1, Module.End.one_apply])

end Klein

theorem centralizer_sup_eq_top_uc64 {K : Type} [Group K] {p f : ℕ}
    (hK : StatedClassicalModel K .PSL 2 p f) (hp2 : p ≠ 2) (hq : 11 ≤ p ^ f) {u u' : K}
    (hu : orderOf u = 2) (hu' : orderOf u' = 2) (hne : u ≠ u') (hc : u * u' = u' * u) :
    centralizer ({u} : Set K) ⊔ centralizer ({u'} : Set K) = ⊤ := by
  obtain ⟨⟨hp, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hK
  haveI : Fact p.Prime := ⟨hp⟩
  have e' : K ≃* StatedProj (StatedSL 2 F) := e
  let E : K ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F :=
    e'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hcent : ∀ w : K, centralizer ({w} : Set K) = (centralizer ({E w} : Set _)).map E.symm.toMonoidHom := by
    intro w
    ext g
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, E.injective.eq_iff]
  have hgen : centralizer ({E u} : Set (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) ⊔
      centralizer ({E u'} : Set (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) = ⊤ :=
    CFSG.GH74.Generic.BProg.B2.psl2_sup_centralizer_eq_top hF hp2 hq
      ((orderOf_injective E.toMonoidHom E.injective u).trans hu)
      ((orderOf_injective E.toMonoidHom E.injective u').trans hu') (fun h => hne (E.injective h))
      (by rw [← map_mul, ← map_mul, hc])
  rw [hcent u, hcent u', ← Subgroup.map_sup, hgen]
  exact Subgroup.map_top_of_surjective _ E.symm.surjective

@[expose] def Asc82Q64Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 → 9 < p ^ f → LieModel G .PSL 2 p f →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V), Function.Injective ρ → ρ.IsIrreducible →
    ∀ D : Subgroup G, Nat.card D = 3 → fixSub ρ D = ⊥ →
    ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 2 S → Nat.card S = 4 →
      D ≤ normalizer (S : Set G) → ⁅D, S⁆ = S →
      ¬ (∀ s ∈ S, ∀ t ∈ S, ∀ v : V, ρ t (ρ s v - v) = ρ s v - v)

theorem asc82Q64Fix_holds : Asc82Q64Fix := by
  intro G _ _ p f hp2 hbig hmodel V _ _ _ ρ hρ _ D hD hfix S hS hS4 hDS hSc hquad
  obtain ⟨x, hxD, hxord⟩ := exists_generator_uc6 Nat.prime_three hD
  have hxmem : x ∈ D := hxD ▸ Subgroup.mem_zpowers x
  obtain ⟨a, b, haS, hbS, ha1, hb1, hab, hb, hxb, -, hcab, ha2, hb2⟩ :=
    exists_klein_basis_uc6 hxord hS hS4 (hDS hxmem) (hxD ▸ hSc)
  have hx3 : x * x * x = 1 := by
    rw [← pow_three', ← hxord]
    exact pow_orderOf_eq_one x
  have hCV : ∀ v, ρ x v = v → v = 0 := by
    intro v hv
    have hvD : v ∈ fixSub ρ D := by
      rw [hxD, mem_fixSub_zpowers_uc6]
      exact hv
    rw [hfix] at hvD
    exact (Submodule.mem_bot (ZMod 2)).1 hvD
  have hcl : StatedClassicalModel G .PSL 2 p f := hmodel.statedClassicalModel (by decide)
  haveI : IsSimpleGroup G := (CFSG.LieType.Simplicity.fam_PSL_simplicity G 2 p f hcl).2
  have hq : 11 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := (hcl.1.1.odd_of_ne_two hp2).pow (n := f)
    omega
  have hgen := centralizer_sup_eq_top_uc64 hcl hp2 hq (orderOf_eq_prime ha2 ha1) (orderOf_eq_prime hb2 hb1)
    hab hcab
  have hV : ∃ k v, ρ k v ≠ v := by
    by_contra hcon
    push Not at hcon
    apply ha1
    apply hρ
    rw [map_one]
    exact LinearMap.ext fun v => hcon a v
  exact false_of_klein_uc64 ρ hV hx3 hCV hb hxb hab (by rw [← pow_two]; exact ha2) (hquad b hbS a haS) hgen

end CFSG.LocalAnalysis.UniquenessCase.UCK

namespace CFSG.RankThree.PartTwo.Sec3

open CFSG.Open Subgroup
open scoped commutatorElement

universe u

@[expose] def Asc82Lemma64Fix : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), StatedClassicalModel K .PSL 2 p f → p ≠ 2 →
    p ≠ 3 → 7 < p ^ f → ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) K V), (∃ k v, ρ k v ≠ v) → ∀ U : Subgroup K, Nat.card U = 4 →
    (∀ g ∈ U, g ^ 2 = 1) → ∀ x : K, orderOf x = 3 → x ∈ normalizer (U : Set K) →
    (∀ g ∈ U, x * g * x⁻¹ = g → g = 1) → (∀ v, ρ x v = v → v = 0) →
    ∃ g ∈ U, ∃ g' ∈ U, ∃ v : V, ρ g' (ρ g v - v) ≠ ρ g v - v

theorem asc82Lemma64Fix_holds : Asc82Lemma64Fix.{u} := by
  intro K _ _ p f hK hp2 hp3 hq7 V _ _ _ ρ hV U hU4 hU2 x hx hxU hCU hCV
  by_contra hcon
  push Not at hcon
  have hUcomm : ∀ g ∈ U, ∀ h ∈ U, g * h = h * g := by
    intro g hg h hh
    have h1 : g * h * (g * h) = 1 := by rw [← pow_two]; exact hU2 _ (U.mul_mem hg hh)
    have hg' : g * g = 1 := by rw [← pow_two]; exact hU2 g hg
    have hh' : h * h = 1 := by rw [← pow_two]; exact hU2 h hh
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hh',
      inv_eq_of_mul_eq_one_right hg']
  have hUel : IsElemAbelian 2 U := ⟨⟨⟨fun g h => Subtype.ext (hUcomm g g.2 h h.2)⟩⟩, hU2⟩
  have hUx : ⁅Subgroup.zpowers x, U⁆ = U := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g hg w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [commutatorElement_def]
      exact U.mul_mem ((mem_normalizer_iff.1 (Subgroup.zpow_mem _ hxU n) w).1 hw) (U.inv_mem hw)
    · intro w hw
      let φ : U → U := fun y =>
        ⟨x * y * x⁻¹ * (y : K)⁻¹, U.mul_mem ((mem_normalizer_iff.1 hxU y).1 y.2) (U.inv_mem y.2)⟩
      have hφ : Function.Injective φ := by
        intro y y' h
        have h' : x * (y : K) * x⁻¹ * (y : K)⁻¹ = x * (y' : K) * x⁻¹ * (y' : K)⁻¹ := congrArg Subtype.val h
        have hfx : x * ((y' : K)⁻¹ * y) * x⁻¹ = (y' : K)⁻¹ * y := by
          calc x * ((y' : K)⁻¹ * y) * x⁻¹
              = (x * y' * x⁻¹)⁻¹ * (x * (y : K) * x⁻¹ * (y : K)⁻¹) * y := by group
            _ = (x * y' * x⁻¹)⁻¹ * (x * (y' : K) * x⁻¹ * (y' : K)⁻¹) * y := by rw [h']
            _ = (y' : K)⁻¹ * y := by group
        exact Subtype.ext (inv_mul_eq_one.1 (hCU _ (U.mul_mem (U.inv_mem y'.2) y.2) hfx)).symm
      obtain ⟨y, hy⟩ := Finite.surjective_of_injective hφ ⟨w, hw⟩
      have hwy : w = ⁅x, (y : K)⁆ := by
        rw [commutatorElement_def]
        exact (congrArg Subtype.val hy).symm
      rw [hwy]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) y.2
  obtain ⟨a, b, haS, hbS, ha1, hb1, hab, hb, hxb, -, hcab, ha2, hb2⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.exists_klein_basis_uc6 hx hUel hU4 hxU hUx
  have hx3 : x * x * x = 1 := by
    rw [← pow_three', ← hx]
    exact pow_orderOf_eq_one x
  haveI : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_PSL_simplicity K 2 p f hK).2
  have hp : p.Prime := hK.1.1
  have hq : 11 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
    by_contra hlt
    have h9 : p ^ f = 9 := by omega
    have hf : f ≠ 0 := by
      have := hK.1.2.1
      omega
    have hp9 : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact dvd_pow_self p hf
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hp9))
  have hgen := CFSG.LocalAnalysis.UniquenessCase.UCK.centralizer_sup_eq_top_uc64 hK hp2 hq
    (orderOf_eq_prime ha2 ha1) (orderOf_eq_prime hb2 hb1) hab hcab
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.false_of_klein_uc64 ρ hV hx3 hCV hb hxb hab
    (by rw [← pow_two]; exact ha2) (hcon b hbS a haS) hgen

end CFSG.RankThree.PartTwo.Sec3
