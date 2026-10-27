module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSide
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallAK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepDepTwin
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeSides
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGDepAOdd
public import CFSG.LocalAnalysis.StandardType.GGRowKFrameDim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l6nk_gen_mem_comm {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs X : Subgroup G}
    {Λ : Type} {φ : Λ → MulAut ↥Bs}
    (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    (hA : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) :
    ∀ g ∈ ggAutomizer X Bs, ∀ b : ↥Bs, g b * b⁻¹ ∈ ggBstarComm X Bs := by
  intro g hg
  rw [hA] at hg
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ b : ↥Bs, g b * b⁻¹ ∈ ggBstarComm X Bs) ?_ ?_ ?_ ?_ hg
  · rintro ψ ⟨i, rfl⟩ b
    have hmem : φ i ∈ ggAutomizer X Bs := by rw [hA]; exact Subgroup.subset_closure ⟨i, rfl⟩
    have h1 : b⁻¹ * φ i b ∈ ggBstarComm X Bs :=
      Subgroup.subset_closure ⟨b, φ i, hmem, rfl⟩
    rwa [← hcomm (φ i b) b⁻¹] at h1
  · intro b
    simp
  · intro g k _ _ ihg ihk b
    have h1 : g (k b) * (k b)⁻¹ ∈ ggBstarComm X Bs := ihg (k b)
    have h2 : k b * b⁻¹ ∈ ggBstarComm X Bs := ihk b
    have hmul : (g * k) b = g (k b) := rfl
    rw [hmul]
    have heq : g (k b) * b⁻¹ = (g (k b) * (k b)⁻¹) * (k b * b⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ h1 h2
  · intro g _ ihg b
    have h1 : g (g⁻¹ b) * (g⁻¹ b)⁻¹ ∈ ggBstarComm X Bs := ihg (g⁻¹ b)
    have h2 : g (g⁻¹ b) = b := by simp
    rw [h2] at h1
    have h3 : (b * (g⁻¹ b)⁻¹)⁻¹ ∈ ggBstarComm X Bs := Subgroup.inv_mem _ h1
    rwa [mul_inv_rev, inv_inv] at h3

theorem l6nk_span_le_image_comm {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hA : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) :
    Submodule.span (ZMod p) (Set.range h) ≤
      Submodule.span (ZMod p) (Set.range (fun c : ↥(ggBstarComm X Bs) =>
        ι (Additive.ofMul (c : ↥Bs)))) := by
  rw [l6tr_span_eq hφ hrefl hA, Submodule.span_le]
  rintro _ ⟨⟨g, w⟩, rfl⟩
  change ggLin (p := p) ι (g : MulAut ↥Bs) w - w ∈
    Submodule.span (ZMod p) (Set.range (fun c : ↥(ggBstarComm X Bs) =>
      ι (Additive.ofMul (c : ↥Bs))))
  set b : ↥Bs := Additive.toMul (ι.symm w) with hb
  have hbw : ι (Additive.ofMul b) = w := by rw [hb]; simp
  have hgen : ggLin (p := p) ι (g : MulAut ↥Bs) w - w =
      ι (Additive.ofMul ((g : MulAut ↥Bs) b * b⁻¹)) := by
    rw [← hbw, ggLin_apply_ofMul]
    have hthis : Additive.ofMul ((g : MulAut ↥Bs) b * b⁻¹) =
        Additive.ofMul ((g : MulAut ↥Bs) b) - Additive.ofMul b := by
      rw [ofMul_mul, ofMul_inv, sub_eq_add_neg]
    rw [hthis, map_sub]
  rw [hgen]
  exact Submodule.subset_span
    ⟨⟨(g : MulAut ↥Bs) b * b⁻¹, l6nk_gen_mem_comm (p := p) hcomm hA g.1 g.2 b⟩, rfl⟩

theorem l6nk_mem_image_comm {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs X : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {v : V}
    (hv : v ∈ Submodule.span (ZMod p) (Set.range (fun c : ↥(ggBstarComm X Bs) =>
      ι (Additive.ofMul (c : ↥Bs))))) :
    ∃ c : ↥(ggBstarComm X Bs), ι (Additive.ofMul (c : ↥Bs)) = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨c, rfl⟩ := hv
      exact ⟨c, rfl⟩
  | zero => exact ⟨1, by simp⟩
  | add v u _ _ ihv ihu =>
      obtain ⟨c, rfl⟩ := ihv
      obtain ⟨d, rfl⟩ := ihu
      exact ⟨c * d, by rw [Subgroup.coe_mul, ofMul_mul, map_add]⟩
  | smul a v _ ihv =>
      obtain ⟨c, rfl⟩ := ihv
      refine ⟨c ^ a.val, ?_⟩
      rw [Subgroup.coe_pow, ofMul_pow, map_nsmul]
      rw [show a.val • ι (Additive.ofMul (c : ↥Bs)) =
          ((a.val : ZMod p)) • ι (Additive.ofMul (c : ↥Bs)) from
        (Nat.cast_smul_eq_nsmul (ZMod p) a.val _).symm]
      rw [ZMod.natCast_zmod_val a]

theorem l6nk_card_frame {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {y : G} (hy : y ∈ Bs) (ι : Additive ↥Bs ≃+ V)
    {Λ : Type} [Fintype Λ] {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    {K : Subgroup G} (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (e : Fin (N - 1) ≃ Λ)
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨y, hy⟩))) :
    Nat.card ↥(ggAutomizer K Bs) ≤ Nat.factorial N := by
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  obtain ⟨ρ, hρswap, hρmem, -, -⟩ := ggDepAOdd_perm_embed hp2 hN F r hr
  have hmap : (ggAutomizer K Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range r) := by
    rw [hAK, MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.symm i, by simp [r]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φ (e i), ⟨e i, rfl⟩, rfl⟩
  have hcard_eq : Nat.card ↥(ggAutomizer K Bs) =
      Nat.card ↥((ggAutomizer K Bs).map (ggLin (p := p) ι)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer K Bs)
      (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv
  have hle1 : Subgroup.closure (Set.range r) ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro z ⟨i, rfl⟩
    exact MonoidHom.mem_range.mpr
      ⟨Equiv.swap (ggDepALeft N i) (ggDepARight N i), hρswap i⟩
  have hle2 : ρ.range ≤ Subgroup.closure (Set.range r) := by
    intro z hz
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hz
    exact hρmem σ
  have hρrange : Subgroup.closure (Set.range r) = ρ.range := le_antisymm hle1 hle2
  calc Nat.card ↥(ggAutomizer K Bs)
      = Nat.card ↥((ggAutomizer K Bs).map (ggLin (p := p) ι)) := hcard_eq
    _ = Nat.card ↥(Subgroup.closure (Set.range r)) := by rw [hmap]
    _ = Nat.card ↥ρ.range := by rw [hρrange]
    _ ≤ Nat.card (Equiv.Perm (Fin N)) :=
        Nat.card_le_card_of_surjective
          (fun σ : Equiv.Perm (Fin N) => (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range))
          (fun z => by
            obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp z.2
            exact ⟨σ, Subtype.ext hσ⟩)
    _ = Nat.factorial N := by rw [Nat.card_perm, Nat.card_fin]

theorem l6nk_span_finrank {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    (hdvd : p ∣ N)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) h) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = N - 2 := by
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨c, hcsum, i0, hi0⟩ := hdep
  have hc0 : c ≠ 0 := fun hzero => hi0 (by rw [hzero]; simp)
  have hN2 : 2 ≤ N := by have hlt := i0.isLt; omega
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  have hd0 : d ≠ 0 := by
    intro hzero
    have h1 := congrFun hzero ⟨0, by omega⟩
    simp [d] at h1
  have hcA : ∀ i, ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * c k = 0 := by
    intro i
    have hh := congrArg (α i) hcsum
    simp only [map_sum, map_smul, hpair, smul_eq_mul, map_zero] at hh
    calc ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * c k
        = ∑ k, c k * (CartanMatrix.A (N - 1) i k : ZMod p) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_comm]
      _ = 0 := hh
  have hdA : ∀ i, ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * d k = 0 :=
    fun i => l6aF_A_mul_d (p := p) (N := N) hdvd i
  have hsum : ∑ i : Fin (N - 1), d i • h i = 0 := by
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one c d hcA hdA hc0
    rw [hl]
    calc ∑ i, (l • c) i • h i
        = ∑ i, l • (c i • h i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul, mul_smul]
      _ = l • ∑ i, c i • h i := by rw [Finset.smul_sum]
      _ = 0 := by rw [hcsum, smul_zero]
  let e := Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin (N - 1))
  let ψ : (Fin (N - 1) →₀ ZMod p) →ₗ[ZMod p] V := Finsupp.linearCombination (ZMod p) h
  let d₀ : Fin (N - 1) →₀ ZMod p := e.symm d
  have hd₀i : ∀ i, d₀ i = d i := by intro i; simp [d₀, e]
  have hψd₀ : ψ d₀ = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
    rw [show (∑ i, (fun i a => a • h i) i (d₀ i)) = ∑ i, d i • h i from by
          exact Finset.sum_congr rfl fun i _ => by rw [hd₀i i]]
    exact hsum
  have hd₀0 : d₀ ≠ 0 := by
    intro hz
    apply hd0
    funext i
    rw [← hd₀i i, hz]; rfl
  have hker : ψ.ker = Submodule.span (ZMod p) ({d₀} : Set (Fin (N - 1) →₀ ZMod p)) := by
    apply le_antisymm
    · intro l hl
      rw [LinearMap.mem_ker] at hl
      have hsuml : ∑ i, l i • h i = 0 := by
        rw [Finsupp.linearCombination_apply] at hl
        rwa [Finsupp.sum_fintype l (fun i a => a • h i) (fun i => by simp)] at hl
      let c : Fin (N - 1) → ZMod p := fun i => l i
      have hcA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 := by
        intro j
        have hh := congrArg (α j) hsuml
        simp only [map_sum, map_smul, hpair, smul_eq_mul, map_zero] at hh
        calc ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k
            = ∑ k, c k * (CartanMatrix.A (N - 1) j k : ZMod p) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [mul_comm]
          _ = 0 := hh
      rw [Submodule.mem_span_singleton]
      by_cases hl0 : l = 0
      · exact ⟨0, by rw [hl0]; simp⟩
      · have hc0 : c ≠ 0 := by intro hc; apply hl0; ext i; exact congrFun hc i
        obtain ⟨a, ha⟩ := ggCartanA_ker_le_one d c hdA hcA hd0
        refine ⟨a, ?_⟩
        ext i
        have hi : c i = a * d i := by simpa [Pi.smul_apply, smul_eq_mul] using congrFun ha i
        show (a • d₀) i = l i
        rw [Finsupp.smul_apply, smul_eq_mul, hd₀i i]
        exact hi.symm
    · intro l hl
      rw [Submodule.mem_span_singleton] at hl
      obtain ⟨a, ha⟩ := hl
      rw [LinearMap.mem_ker, ← ha]
      rw [map_smul, hψd₀, smul_zero]
  have hkerfin : Module.finrank (ZMod p) ↥ψ.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hd₀0
  have hdomain : Module.finrank (ZMod p) (Fin (N - 1) →₀ ZMod p) = N - 1 := by
    rw [Module.finrank_finsupp_self, Fintype.card_fin]
  have hrk := LinearMap.finrank_range_add_finrank_ker ψ
  have hrange : Module.finrank (ZMod p) ↥ψ.range = N - 2 := by
    rw [hkerfin, hdomain] at hrk
    omega
  rw [← Finsupp.range_linearCombination (ZMod p) (v := h)]
  exact hrange

end CFSG.StandardType

end
