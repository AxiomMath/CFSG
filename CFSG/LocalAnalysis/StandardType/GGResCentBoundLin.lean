module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped IsMulCommutative

private theorem ggIntCartan_entry_ne_zero_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {i j : Λ} (hij : i ≠ j) (hlab : M i j ≠ 2) :
    (C i j : ZMod p) ≠ 0 ∨ (C j i : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  rcases hC.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
    ⟨hm, h1, -, -⟩ | ⟨hm, h1, -, -⟩
  · exact absurd hm hlab
  · left
    rw [h1]
    norm_num
  · have h2ne : ((2 : ℤ) : ZMod p) ≠ 0 := by
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp hd))
    left
    intro h0
    have hzero : (C i j : ZMod p) * (C j i : ZMod p) = 0 := by rw [h0, zero_mul]
    rw [← Int.cast_mul, h1] at hzero
    exact h2ne hzero
  · by_contra h
    push Not at h
    have hpi : (p : ℤ) ∣ C i j := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.1
    have hpj : (p : ℤ) ∣ C j i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.2
    have hdvd : (p : ℤ) * (p : ℤ) ∣ 3 := by
      have := mul_dvd_mul hpi hpj
      rwa [h1] at this
    have hle : (p : ℤ) * (p : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) hdvd
    have hp2le : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have h4 : (4 : ℤ) ≤ (p : ℤ) * (p : ℤ) := by nlinarith
    omega

theorem ggWeylDatum_commutant_scalar {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} (hW : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (T : V →ₗ[ZMod p] V)
    (hT : ∀ i w, T (w - α i w • h i) = T w - α i (T w) • h i) :
    ∃ μ : ZMod p, ∀ i w, α i (T w) = μ * α i w := by
  classical
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℤ) : ZMod p) by norm_num]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp hd))
  have hdiag : ∀ i, α i (h i) = (2 : ZMod p) := by
    intro i
    rw [hpair, hC.1 i]
    norm_num
  let μ : Λ → ZMod p := fun i => (2 : ZMod p)⁻¹ * α i (T (h i))
  have hT_h : ∀ i, T (h i) = μ i • h i := by
    intro i
    have hneg : - T (h i) = T (h i) - α i (T (h i)) • h i := by
      have hleft : T (h i - (2 : ZMod p) • h i) = - T (h i) := by
        calc T (h i - (2 : ZMod p) • h i)
            = T (h i) - (2 : ZMod p) • T (h i) := by rw [map_sub, map_smul]
          _ = - T (h i) := by module
      rw [← hleft]
      have h := hT i (h i)
      rwa [hdiag i] at h
    have h2 : α i (T (h i)) • h i = (2 : ZMod p) • T (h i) := by
      have hsub : T (h i) - α i (T (h i)) • h i = - T (h i) := hneg.symm
      have := congrArg (fun z => T (h i) - z) hsub
      simpa [sub_sub_cancel, two_smul] using this
    calc T (h i)
        = (1 : ZMod p) • T (h i) := (one_smul _ _).symm
      _ = ((2 : ZMod p)⁻¹ * 2) • T (h i) := by rw [inv_mul_cancel₀ htwo]
      _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • T (h i)) := (smul_smul _ _ _).symm
      _ = (2 : ZMod p)⁻¹ • (α i (T (h i)) • h i) := by rw [h2]
      _ = ((2 : ZMod p)⁻¹ * α i (T (h i))) • h i := smul_smul _ _ _
      _ = μ i • h i := rfl
  have hkey : ∀ i w, α i (T w) = α i w * μ i := by
    intro i w
    have hsub : T w - α i w • T (h i) = T w - α i (T w) • h i := by
      have h := hT i w
      rwa [map_sub, map_smul] at h
    have hEq : α i w • T (h i) = α i (T w) • h i :=
      sub_right_injective hsub
    have hα := congrArg (α i) hEq
    rw [map_smul, map_smul, hT_h i, map_smul, smul_eq_mul, hdiag i] at hα
    have h2 : (α i w * μ i) * 2 = α i (T w) * 2 := by
      simpa [smul_eq_mul, mul_assoc] using hα
    exact (mul_right_cancel₀ htwo h2).symm
  have hμeq : ∀ i j, α j (h i) ≠ 0 → μ i = μ j := by
    intro i j hne
    have h1 : α j (T (h i)) = μ j * α j (h i) := by
      rw [hkey j (h i), mul_comm]
    have h2 : α j (T (h i)) = μ i * α j (h i) := by
      rw [hT_h i, map_smul, smul_eq_mul]
    exact (mul_right_cancel₀ hne (h1.symm.trans h2)).symm
  have hedge : ∀ i j, i ≠ j → M i j ≠ 2 → μ i = μ j := by
    intro i j hij hlab
    rcases ggIntCartan_entry_ne_zero_mod (p := p) hp2 hC hij hlab with hcij | hcji
    · exact (hμeq j i (by rwa [hpair i j])).symm
    · exact hμeq i j (by rwa [hpair j i])
  by_cases hnon : Nonempty Λ
  · obtain ⟨i₀⟩ := hnon
    have hμ : ∀ i, μ i = μ i₀ := by
      intro i
      have hpath := ggRC_weyl_connected hW i₀ i
      induction hpath with
      | refl => rfl
      | tail _ hbc ih => exact (hedge _ _ hbc.1 hbc.2).symm.trans ih
    exact ⟨μ i₀, fun i w => by rw [hkey i w, hμ i, mul_comm]⟩
  · exact ⟨0, fun i => (hnon ⟨i⟩).elim⟩

theorem ggEq_one_of_mod_zpowers {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} (hE : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {x : G}
    (hx : x ∈ Bs) (hx1 : x ≠ 1) {c : MulAut ↥Bs} (hc : c ∈ ggInduced ⊤ Bs)
    (hcx : c ⟨x, hx⟩ = ⟨x, hx⟩) (hmod : ∀ b : ↥Bs, ((b⁻¹ * c b : ↥Bs) : G) ∈ Subgroup.zpowers x) :
    c = 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hcomm : IsMulCommutative ↥Bs := hE.1
  have hxp : (⟨x, hx⟩ : ↥Bs) ^ p = 1 := by
    apply Subtype.ext
    simpa using hE.2 x hx
  have hx1' : (⟨x, hx⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  let f : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * c b
      map_one' := by simp
      map_mul' := by
        intro a b
        show (a * b)⁻¹ * c (a * b) = (a⁻¹ * c a) * (b⁻¹ * c b)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hfix : ∀ b : ↥Bs, f b = 1 ↔ c b = b := by
    intro b
    constructor
    · intro h
      have h' : b⁻¹ * c b = 1 := h
      calc c b = b * (b⁻¹ * c b) := (mul_inv_cancel_left b (c b)).symm
        _ = b := by rw [h', mul_one]
    · intro h
      show b⁻¹ * c b = 1
      rw [h, inv_mul_cancel]
  by_contra hc1
  obtain ⟨b, hb⟩ : ∃ b : ↥Bs, c b ≠ b := by
    by_contra h
    push Not at h
    exact hc1 (MulEquiv.ext fun x => by simpa using h x)
  have hrange_ne_bot : f.range ≠ ⊥ := by
    intro hbot
    have hf1 : f b = 1 := by
      have hmem : f b ∈ f.range := ⟨b, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    exact hb ((hfix b).mp hf1)
  have hrange_le : f.range ≤ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hmod a)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [f] using hn)⟩
  have hPcard : Nat.card (Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxp hx1'
  have hrange_card : Nat.card f.range = p := by
    have hdvd : Nat.card f.range ∣ p := by
      simpa [hPcard] using Subgroup.card_dvd_of_le hrange_le
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · exact absurd ((Subgroup.eq_bot_iff_card f.range).mpr h1) hrange_ne_bot
    · exact hp'
  have hfixed : Nat.card {b : ↥Bs // c b = b} = Nat.card f.ker := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun b => ⟨b.1, (hfix b.1).mpr b.2⟩
        invFun := fun b => ⟨b.1, (hfix b.1).mp b.2⟩
        left_inv := fun b => by ext; rfl
        right_inv := fun b => by ext; rfl }
  have hcard : Nat.card {b : ↥Bs // c b = b} * p = Nat.card ↥Bs := by
    have hker := Subgroup.card_ker_mul_card_range f
    rw [← hfixed, hrange_card] at hker
    exact hker
  have hsecond : ∀ b : ↥Bs, c (b⁻¹ * c b) = b⁻¹ * c b := by
    intro b
    have hy : b⁻¹ * c b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hmod b)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn, map_zpow, hcx]
  exact hNT c hc ⟨hcard, hsecond⟩

theorem ggWeylDatum_finrank_le {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (α : Λ → Module.Dual (ZMod p) V) (x₀ : V)
    (hker : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x₀}) :
    Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
  classical
  let Φ : V →ₗ[ZMod p] (Λ → ZMod p) := LinearMap.pi α
  have hker_le : LinearMap.ker Φ ≤ Submodule.span (ZMod p) {x₀} := by
    intro v hv
    apply hker v
    intro i
    have := congrFun (LinearMap.mem_ker.mp hv) i
    simpa [Φ] using this
  calc Module.finrank (ZMod p) V
      = Module.finrank (ZMod p) Φ.range + Module.finrank (ZMod p) Φ.ker :=
        (LinearMap.finrank_range_add_finrank_ker Φ).symm
    _ ≤ Fintype.card Λ + 1 := by
        gcongr
        · calc Module.finrank (ZMod p) Φ.range
              ≤ Module.finrank (ZMod p) (Λ → ZMod p) := Submodule.finrank_le Φ.range
            _ = Fintype.card Λ := Module.finrank_pi (ZMod p)
        · calc Module.finrank (ZMod p) Φ.ker
              ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) {x₀}) :=
                Submodule.finrank_mono hker_le
            _ ≤ 1 := by
                simpa using finrank_span_le_card (R := ZMod p) ({x₀} : Set V)

theorem exists_weyl_commutant_character {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (a : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, a i (h j) = (C i j : ZMod p))
    {H : Type} [Group H] (T : H →* (V ≃ₗ[ZMod p] V))
    (hcomm : ∀ g i v, T g (v - a i v • h i) = T g v - a i (T g v) • h i) :
    ∃ mu : H →* (ZMod p)ˣ, (∀ g i v, a i (T g v) = (mu g : ZMod p) * a i v) ∧
      ∀ g i, T g (h i) = (mu g : ZMod p) • h i := by
  classical
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hdiag : ∀ i, a i (h i) = 2 := by intro i; rw [hpair, hC.1]; norm_num
  have hex (g : H) : ∃ μ : ZMod p, ∀ i v, a i (T g v) = μ * a i v :=
    ggWeylDatum_commutant_scalar hp2 hM hC h a hpair (T g).toLinearMap (hcomm g)
  let μ (g : H) := Classical.choose (hex g)
  have hμ (g : H) : ∀ i v, a i (T g v) = μ g * a i v := Classical.choose_spec (hex g)
  have huniq (g : H) (r : ZMod p) (hr : ∀ i v, a i (T g v) = r * a i v) : r = μ g := by
    let i : Λ := Classical.arbitrary Λ
    have h1 := hr i (h i)
    have h2 := hμ g i (h i)
    rw [hdiag] at h1 h2
    exact mul_right_cancel₀ htwo (h1.symm.trans h2)
  have hμne (g : H) : μ g ≠ 0 := by
    intro h0
    let i : Λ := Classical.arbitrary Λ
    have h1 := hμ g i ((T g).symm (h i))
    rw [LinearEquiv.apply_symm_apply, hdiag, h0, zero_mul] at h1
    exact htwo h1
  have hmul (g k : H) : μ (g * k) = μ g * μ k := by
    apply (huniq (g * k) _ ?_).symm
    intro i v
    rw [map_mul, LinearEquiv.mul_apply, hμ, hμ, mul_assoc]
  let mu : H →* (ZMod p)ˣ := MonoidHom.mk'
    (fun g => Units.mk0 (μ g) (hμne g)) (fun g k => Units.ext (hmul g k))
  refine ⟨mu, fun g i v => hμ g i v, ?_⟩
  intro g i
  have heq : (2 : ZMod p) • T g (h i) = a i (T g (h i)) • h i := by
    have h0 := hcomm g i (h i)
    rw [hdiag, map_sub, map_smul] at h0
    have heq := sub_right_injective h0
    exact heq
  rw [hμ, hdiag] at heq
  have hs : (2 : ZMod p) • (T g (h i) - μ g • h i) = 0 := by
    rw [smul_sub, heq]
    rw [smul_smul, mul_comm (2 : ZMod p) (μ g), sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_left htwo)


end CFSG.StandardType

end
