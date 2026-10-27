module

public import CFSG.LocalAnalysis.StandardType.GGLatticeRoots
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpFork
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpAgree
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpCartan
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section LatticeStep

private theorem ggInduced_mono {G : Type} [Group G] {H H' Bs : Subgroup G} (hle : H ≤ H')
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs) : φ ∈ ggInduced H' Bs := by
  obtain ⟨g, hg, hN, hg'⟩ := hφ
  exact ⟨g, hle hg, hN, hg'⟩

private theorem ggInduced_fix_centralizer {G : Type} [Group G] {X Bs : Subgroup G}
    {r : MulAut ↥Bs} (hr : r ∈ ggInduced X Bs) :
    ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (X : Set G) → r b = b := by
  intro b hb
  obtain ⟨g, hgX, -, hg⟩ := hr
  apply Subtype.ext
  have hcomm : g * (b : G) = (b : G) * g := (Subgroup.mem_centralizer_iff.mp hb) g hgX
  rw [hg b, hcomm]
  group

private theorem mul_mul_eq_of_scale {K : Type*} [Field K] {x y μa μf c₁ c₂ : K}
    (h₁ : x * μa = μf * c₁) (h₂ : y * μf = μa * c₂) (hμa : μa ≠ 0) (hμf : μf ≠ 0) :
    c₁ * c₂ = x * y := by
  have hc₁ : c₁ * μf = x * μa := by rw [mul_comm c₁ μf, ← h₁]
  have hc₂ : c₂ * μa = y * μf := by rw [mul_comm c₂ μa, ← h₂]
  have h : c₁ * c₂ * (μa * μf) = x * y * (μa * μf) := by
    calc c₁ * c₂ * (μa * μf) = (c₁ * μf) * (c₂ * μa) := by ring
      _ = (x * μa) * (y * μf) := by rw [hc₁, hc₂]
      _ = x * y * (μa * μf) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hμa hμf) h

private theorem mul_mul_mul_eq_of_scale {K : Type*} [Field K] {x y z μ₀ μ₁ μ₂ c₁ c₂ c₃ : K}
    (h₁ : x * μ₁ = μ₀ * c₁) (h₂ : y * μ₂ = μ₁ * c₂) (h₃ : z * μ₀ = μ₂ * c₃)
    (hμ₀ : μ₀ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0) :
    c₁ * c₂ * c₃ = x * y * z := by
  have hc₁ : c₁ * μ₀ = x * μ₁ := by rw [mul_comm c₁ μ₀, ← h₁]
  have hc₂ : c₂ * μ₁ = y * μ₂ := by rw [mul_comm c₂ μ₁, ← h₂]
  have hc₃ : c₃ * μ₂ = z * μ₀ := by rw [mul_comm c₃ μ₂, ← h₃]
  have h : c₁ * c₂ * c₃ * (μ₀ * μ₁ * μ₂) = x * y * z * (μ₀ * μ₁ * μ₂) := by
    calc c₁ * c₂ * c₃ * (μ₀ * μ₁ * μ₂)
        = (c₁ * μ₀) * (c₂ * μ₁) * (c₃ * μ₂) := by ring
      _ = (x * μ₁) * (y * μ₂) * (z * μ₀) := by rw [hc₁, hc₂, hc₃]
      _ = x * y * z * (μ₀ * μ₁ * μ₂) := by ring
  exact mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hμ₀ hμ₁) hμ₂) h

theorem ggForkCross_lattice_step {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hX : GGAutLattice p Bs X) {Λ : Type} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c v₂ : Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    {ha : V} {αa : Module.Dual (ZMod p) V} (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) (hvb : v₂ ≠ b) (hvc : v₂ ≠ c)
    (hn : C c v₂ * C v₂ c = 1 ∨ C c v₂ * C v₂ c = 2 ∨ C c v₂ * C v₂ c = 3)
    (htX : (φ b * φ c) * φa * (φ b * φ c)⁻¹ ∈ ggInduced X Bs) (hcX : φ c ∈ ggInduced X Bs)
    (hvX : φ v₂ ∈ ggInduced X Bs) :
    αa (h b) = 0 ∨ αa (h b) = 1 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨n, hn_eq⟩ : ∃ n : ℤ, n = C c v₂ * C v₂ c := ⟨_, rfl⟩
  rw [← hn_eq] at hn
  have hn1 : 1 ≤ n := by rcases hn with h | h | h <;> omega
  have hn3 : n ≤ 3 := by rcases hn with h | h | h <;> omega
  have hnZ : (n : ZMod p) ≠ 0 := by
    intro h
    have hdvd : (p : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp h
    have hp_le : (p : ℤ) ≤ n := Int.le_of_dvd (by omega) hdvd
    omega
  obtain ⟨hptc, hptv, hpvt⟩ := ggFork_t_pairing (p := p) ι hF hlin hvb hvc
  let tt : MulAut ↥Bs := (φ b * φ c) * φa * (φ b * φ c)⁻¹
  let ht : V := ha + h c + (1 - α b ha) • h b
  let αt : Module.Dual (ZMod p) V := αa ∘ₗ (ggLin (p := p) ι (φ c * φ b)).toLinearMap
  have hlint : ∀ w, ggLin (p := p) ι tt w = w - αt w • ht := fun w =>
    ggFork_t_apply (p := p) ι hF hlin hlina w
  have hαt : αt ht = 2 := by
    have hαbht : α b ht = 1 - α b ha := by
      change α b (ha + h c + (1 - α b ha) • h b) = 1 - α b ha
      rw [map_add, map_add, map_smul, smul_eq_mul, hF.b_c, hF.self b]
      ring
    have hb : ggLin (p := p) ι (φ b) ht = ha + h c := by
      rw [hlin b, hαbht]
      change ha + h c + (1 - α b ha) • h b - (1 - α b ha) • h b = ha + h c
      module
    have hc : α c (ha + h c) = 1 := by
      rw [map_add, hF.c_a, hF.self c]
      ring
    have hc2 : ggLin (p := p) ι (φ c) (ha + h c) = ha := by
      rw [hlin c, hc]
      module
    have hmul : ggLin (p := p) ι (φ c * φ b) ht = ha := by
      rw [map_mul, LinearEquiv.mul_apply, hb, hc2]
    change αa (ggLin (p := p) ι (φ c * φ b) ht) = 2
    rw [hmul, hF.aa]
  have hne := ggFork_ne_t (p := p) hp2 ι hF hlin hlina hind hvb hvc
  let T : Fin 3 → MulAut ↥Bs := ![tt, φ c, φ v₂]
  let H : Fin 3 → V := ![ht, h c, h v₂]
  let A : Fin 3 → Module.Dual (ZMod p) V := ![αt, α c, α v₂]
  have hTmem : ∀ k, T k ∈ ggInduced X Bs := by
    intro k
    fin_cases k
    · exact htX
    · exact hcX
    · exact hvX
  have hAH : ∀ k, A k (H k) = 2 := by
    intro k
    fin_cases k
    · exact hαt
    · exact hF.self c
    · exact hF.self v₂
  have hTlin : ∀ k w, ggLin (p := p) ι (T k) w = w - A k w • H k := by
    intro k w
    fin_cases k
    · exact hlint w
    · exact hlin c w
    · exact hlin v₂ w
  obtain ⟨m, Q, v, μ, hQ, hroot, hμ, hcart, hag1, hag2⟩ :=
    ggAutLattice_cartan hp2 hBs ι hX hTmem hAH hTlin
  have hP_t : ggLatCartan Q (v 0) (v 2) * ggLatCartan Q (v 2) (v 0) = n := by
    have hbound := ggLat_pair_bound hQ (hroot 0) (hroot 2)
    have h1 := hcart 2 0
    have h2 := hcart 0 2
    change α v₂ ht * μ 0 = μ 2 * (ggLatCartan Q (v 0) (v 2) : ZMod p) at h1
    change αt (h v₂) * μ 2 = μ 0 * (ggLatCartan Q (v 2) (v 0) : ZMod p) at h2
    have hcast : ((ggLatCartan Q (v 0) (v 2) * ggLatCartan Q (v 2) (v 0) : ℤ) : ZMod p) = n := by
      rw [Int.cast_mul]
      rw [mul_mul_eq_of_scale h1 h2 (hμ 0) (hμ 2)]
      rw [show α v₂ ht = (C v₂ c : ZMod p) from hpvt,
        show αt (h v₂) = (C c v₂ : ZMod p) from hptv]
      rw [hn_eq, Int.cast_mul]
      ring
    exact ggLat_eq_of_cast_eq hp5 hbound.1 hbound.2 hn1 hn3 hcast
  have hP_c : ggLatCartan Q (v 1) (v 2) * ggLatCartan Q (v 2) (v 1) = n := by
    have hbound := ggLat_pair_bound hQ (hroot 1) (hroot 2)
    have h1 := hcart 2 1
    have h2 := hcart 1 2
    change α v₂ (h c) * μ 1 = μ 2 * (ggLatCartan Q (v 1) (v 2) : ZMod p) at h1
    change α c (h v₂) * μ 2 = μ 1 * (ggLatCartan Q (v 2) (v 1) : ZMod p) at h2
    have hcast : ((ggLatCartan Q (v 1) (v 2) * ggLatCartan Q (v 2) (v 1) : ℤ) : ZMod p) = n := by
      rw [Int.cast_mul]
      rw [mul_mul_eq_of_scale h1 h2 (hμ 1) (hμ 2)]
      rw [hF.pair v₂ c, hF.pair c v₂]
      rw [hn_eq, Int.cast_mul]
      ring
    exact ggLat_eq_of_cast_eq hp5 hbound.1 hbound.2 hn1 hn3 hcast
  have hΓ : ((ggLatCartan Q (v 1) (v 0) * ggLatCartan Q (v 2) (v 1) *
      ggLatCartan Q (v 0) (v 2) : ℤ) :
      ZMod p) = αa (h b) * n := by
    have h1 := hcart 0 1
    have h2 := hcart 1 2
    have h3 := hcart 2 0
    change αt (h c) * μ 1 = μ 0 * (ggLatCartan Q (v 1) (v 0) : ZMod p) at h1
    change α c (h v₂) * μ 2 = μ 1 * (ggLatCartan Q (v 2) (v 1) : ZMod p) at h2
    change α v₂ ht * μ 0 = μ 2 * (ggLatCartan Q (v 0) (v 2) : ZMod p) at h3
    rw [Int.cast_mul, Int.cast_mul]
    rw [mul_mul_mul_eq_of_scale h1 h2 h3 (hμ 0) (hμ 1) (hμ 2)]
    rw [show αt (h c) = αa (h b) from hptc, hF.pair c v₂,
      show α v₂ ht = (C v₂ c : ZMod p) from hpvt]
    rw [hn_eq, Int.cast_mul]
    ring
  rcases ggLat_gram_trichotomy hQ (hroot 0) (hroot 1) (hroot 2) (n := n) hn hP_t hP_c with
    (hΓ0 | hΓn) | hs1 | hs2
  ·
    left
    have h0 : αa (h b) * (n : ZMod p) = 0 := by
      rw [hΓ0] at hΓ
      simpa using hΓ.symm
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hnZ
  ·
    right
    have h1 : αa (h b) * (n : ZMod p) = 1 * (n : ZMod p) := by
      rw [hΓn] at hΓ
      simpa using hΓ.symm
    exact mul_right_cancel₀ hnZ h1
  ·
    exfalso
    have hreflc : GGIsReflection p (φ c) :=
      ggIsReflection_of_eq_reflection hp2 ι (hF.self c)
        (ggLin_eq_reflection ι (hF.self c) (hlin c))
    have hφa : GGIsReflection p φa :=
      ggIsReflection_of_eq_reflection hp2 ι hF.aa (ggLin_eq_reflection ι hF.aa hlina)
    have hreflt : GGIsReflection p tt := hφa.conj' (φ b * φ c)
    have heq : φ c = tt := ggReflection_eq_of_agree_mod (p := p) hp2 hBs hNT hreflc hreflt
      (ggInduced_mono le_top hcX) (ggInduced_mono le_top htX)
      (ggInduced_fix_centralizer hcX) (ggInduced_fix_centralizer htX)
      (fun b => hag1 1 0 hs1 b)
    exact hne.1 heq
  ·
    exfalso
    have hreflc : GGIsReflection p (φ c) :=
      ggIsReflection_of_eq_reflection hp2 ι (hF.self c)
        (ggLin_eq_reflection ι (hF.self c) (hlin c))
    have hφa : GGIsReflection p φa :=
      ggIsReflection_of_eq_reflection hp2 ι hF.aa (ggLin_eq_reflection ι hF.aa hlina)
    have hreflt : GGIsReflection p tt := hφa.conj' (φ b * φ c)
    have hreflv : GGIsReflection p (φ v₂) :=
      ggIsReflection_of_eq_reflection hp2 ι (hF.self v₂)
        (ggLin_eq_reflection ι (hF.self v₂) (hlin v₂))
    have hv2sq : (φ v₂) ^ 2 = 1 := hreflv.1
    have hinv : (φ v₂)⁻¹ = φ v₂ := by
      have hsq : φ v₂ * φ v₂ = 1 := by rwa [pow_two] at hv2sq
      calc (φ v₂)⁻¹ = (φ v₂)⁻¹ * (φ v₂ * φ v₂) := by rw [hsq, mul_one]
        _ = ((φ v₂)⁻¹ * φ v₂) * φ v₂ := by rw [mul_assoc]
        _ = φ v₂ := by rw [inv_mul_cancel, one_mul]
    have hreflt2 : GGIsReflection p (φ v₂ * tt * φ v₂) := by
      have h := hreflt.conj' (φ v₂)
      rwa [hinv] at h
    have hmem2 : φ v₂ * tt * φ v₂ ∈ ggInduced X Bs :=
      mul_mem_ggInduced (mul_mem_ggInduced hvX htX) hvX
    have heq : φ c = φ v₂ * tt * φ v₂ := ggReflection_eq_of_agree_mod (p := p) hp2 hBs hNT
      hreflc hreflt2 (ggInduced_mono le_top hcX) (ggInduced_mono le_top hmem2)
      (ggInduced_fix_centralizer hcX) (ggInduced_fix_centralizer hmem2)
      (fun b => hag2 2 1 0 hs2 b)
    exact hne.2 heq

end LatticeStep

end CFSG.StandardType
