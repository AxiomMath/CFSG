module

public import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingPrimeCut
import CFSG.RankThree.GroupTheory.SteinbergBMScalarActionQuasisimpleQuotient
import CFSG.RankThree.GroupTheory.SteinbergBMMinimalExtraspecialModule
import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
import CFSG.Assembly.OrderReductions.ElementaryRepresentation

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBM CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.OrderReductions.ElementaryRepresentation CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

theorem exists_scalar_of_commutes_extraspecial_two_action {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup q P)
    {S : Type*} [Group S] [Finite S] (hS : IsExtraspecialPGroup 2 S) {n : ℕ}
    (hcard : Nat.card S = 2 ^ (1 + 2 * n)) {z : S} (hz : center S = zpowers z)
    (hdim : Nat.card (P ⧸ frattini P) = q ^ (2 ^ n))
    (ψ : S →* MulAut P) (hψ : Function.Injective ψ) {σ : MulAut P}
    (hσ : ∀ s : S, σ * ψ s = ψ s * σ) :
    ∃ k : ℕ, ∀ x : P, (σ x)⁻¹ * x ^ k ∈ frattini P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup (P ⧸ frattini P) := frattiniQuotientCommGroup q hP
  let : Module (ZMod q) (Additive (P ⧸ frattini P)) := frattiniQuotientModule q hP
  have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
  have : FiniteDimensional (ZMod q) (Additive (P ⧸ frattini P)) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod q) (Additive (P ⧸ frattini P)) = 2 ^ n := by
    have := Fintype.ofFinite (Additive (P ⧸ frattini P))
    have h := Module.card_eq_pow_finrank (K := ZMod q) (V := Additive (P ⧸ frattini P))
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod] at h
    have h2 : Nat.card (Additive (P ⧸ frattini P)) = Nat.card (P ⧸ frattini P) := rfl
    rw [h2, hdim] at h
    exact (Nat.pow_right_injective (Fact.out : q.Prime).two_le h).symm
  set qA := quotientAutomorphism (frattini P) with hqA
  set Θ := linearRepresentation q qA with hΘ
  obtain ⟨-, hkerq⟩ := CFSG.GroupTheory.frattini_automorphism_kernel (p := q) hP
  have hΘker : ∀ τ : MulAut P, Θ τ = 1 → τ ∈ qA.ker := by
    intro τ hτ
    have h : τ ∈ (Θ.asGroupHom).ker := by
      rw [MonoidHom.mem_ker]
      exact Units.ext hτ
    rw [hΘ, linearRepresentation_kernel] at h
    exact h
  set ρ : Representation (ZMod q) S (Additive (P ⧸ frattini P)) := Θ.comp ψ with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : Θ (ψ s) = 1 := hs
    have h2 : ψ s ∈ qA.ker := hΘker _ h1
    obtain ⟨j, hj⟩ := hkerq ⟨ψ s, h2⟩
    have hj' : (ψ s) ^ (q ^ j) = 1 := congrArg Subtype.val hj
    obtain ⟨i, hi⟩ := hS.1 s
    have hi' : (ψ s) ^ (2 ^ i) = 1 := by rw [← map_pow, hi, map_one]
    have hcop : Nat.Coprime (q ^ j) (2 ^ i) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hq2)
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hi')
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact hψ (h.trans (map_one ψ).symm)
  have hK : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  have hcen := (minimal_extraspecial_module_scalar_centralizer.{_, _, _, 0} hS hcard hz hK hfin ρ
    hρinj).2.2.1
  have hTmem : Θ.asGroupHom σ ∈ Subgroup.centralizer (Set.range ρ.asGroupHom) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    have e : ρ.asGroupHom s = Θ.asGroupHom (ψ s) :=
      Units.ext (by simp only [Representation.asGroupHom_apply]; rfl)
    rw [e, ← map_mul, ← map_mul, hσ s]
  rw [hcen] at hTmem
  obtain ⟨c, hc⟩ := hTmem
  have hTσ : ∀ v : Additive (P ⧸ frattini P), Θ σ v = (c : ZMod q) • v := by
    intro v
    have := congrArg (fun u : (Module.End (ZMod q) (Additive (P ⧸ frattini P)))ˣ =>
      (u : Module.End (ZMod q) (Additive (P ⧸ frattini P))) v) hc
    simpa [Representation.asGroupHom_apply] using this.symm
  refine ⟨(c : ZMod q).val, fun x => ?_⟩
  have h1 := hTσ (Additive.ofMul (x : P ⧸ frattini P))
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h2 : (Θ σ) (Additive.ofMul (x : P ⧸ frattini P)) =
      Additive.ofMul ((σ x : P) : P ⧸ frattini P) := by
    rw [hΘ, linearRepresentation_apply]
    exact congrArg Additive.ofMul (quotientAutomorphism_apply (frattini P) σ x)
  have h3 : (c : ZMod q) • Additive.ofMul (x : P ⧸ frattini P) =
      Additive.ofMul ((x : P ⧸ frattini P) ^ (c : ZMod q).val) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (c : ZMod q)]
    rw [Nat.cast_smul_eq_nsmul, ofMul_pow]
  rw [h2, h3] at h1
  have h4 : ((σ x : P) : P ⧸ frattini P) = (x : P ⧸ frattini P) ^ (c : ZMod q).val :=
    Additive.ofMul.injective h1
  rw [← QuotientGroup.mk_pow] at h4
  exact QuotientGroup.eq.mp h4

theorem exists_scalar_of_commutes_prime_dimensional_plane_action {p q : ℕ} (hp : p.Prime)
    [Fact q.Prime] (hq2 : q ≠ 2) {P : Type*} [CommGroup P] [Finite P] (hPq : ∀ x : P, x ^ q = 1)
    (hPcard : Nat.card P = q ^ p) {R : Type*} [CommGroup R] [Finite R]
    [Module (ZMod 2) (Additive R)] (hR : 4 ≤ Nat.card R) {H : Type*} [Group H]
    (φ : H →* MulAut R) (hφ : Nat.card φ.range = p) (ψR : R →* MulAut P) (ψH : H →* MulAut P)
    (hψR : Function.Injective ψR)
    (hcompat : ∀ (h : H) (r : R), ψR (φ h r) = ψH h * ψR r * (ψH h)⁻¹)
    (hirr : ∀ W : Subgroup P, (∀ r : R, ∀ x ∈ W, ψR r x ∈ W) → (∀ h : H, ∀ x ∈ W, ψH h x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {σ : MulAut P} (hσR : ∀ r : R, σ * ψR r = ψR r * σ) (hσH : ∀ h : H, σ * ψH h = ψH h * σ) :
    ∃ k : ℕ, ∀ x : P, σ x = x ^ k := by
  classical
  let : Module (ZMod q) (Additive P) := exponentModule q hPq
  have : Finite (Additive P) := inferInstanceAs (Finite P)
  have : FiniteDimensional (ZMod q) (Additive P) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod q) (Additive P) = p := by
    have := Fintype.ofFinite (Additive P)
    have h := Module.card_eq_pow_finrank (K := ZMod q) (V := Additive P)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod] at h
    have h2 : Nat.card (Additive P) = Nat.card P := rfl
    rw [h2, hPcard] at h
    exact (Nat.pow_right_injective (Fact.out : q.Prime).two_le h).symm
  have hlift : ∀ h : H, ψR.comp (φ h).toMonoidHom =
      (MulAut.conj (ψH h)).toMonoidHom.comp ψR := by
    intro h
    exact MonoidHom.ext fun r => hcompat h r
  set ψ : R ⋊[φ] H →* MulAut P := SemidirectProduct.lift ψR ψH hlift with hψ
  set Θ : Representation (ZMod q) (MulAut P) (Additive P) :=
    linearRepresentation q (MonoidHom.id (MulAut P)) with hΘ
  set ρ : Representation (ZMod q) (R ⋊[φ] H) (Additive P) := Θ.comp ψ with hρ
  have hρapp : ∀ (g : R ⋊[φ] H) (x : P), ρ g (Additive.ofMul x) = Additive.ofMul (ψ g x) :=
    fun _ _ => rfl
  have hntP : Nontrivial (Additive P) := by
    have : 1 < Nat.card (Additive P) := by
      have h2 : Nat.card (Additive P) = Nat.card P := rfl
      rw [h2, hPcard]
      exact Nat.one_lt_pow hp.ne_zero (Fact.out : q.Prime).one_lt
    exact Finite.one_lt_card_iff_nontrivial.mp this
  have hirrρ : ρ.IsIrreducible := by
    refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
    · refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      obtain ⟨v, hv⟩ := exists_ne (0 : Additive P)
      have h' : (⊤ : Subrepresentation ρ).toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule :=
        congrArg Subrepresentation.toSubmodule h.symm
      have hv' : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
      rw [h'] at hv'
      exact hv ((Submodule.mem_bot _).mp hv')
    · intro W
      set Wg : Subgroup P := AddSubgroup.toSubgroup' W.toSubmodule.toAddSubgroup with hWg
      have hmem : ∀ x : P, x ∈ Wg ↔ Additive.ofMul x ∈ W.toSubmodule := fun _ => Iff.rfl
      have hR' : ∀ r : R, ∀ x ∈ Wg, ψR r x ∈ Wg := by
        intro r x hx
        rw [hmem] at hx ⊢
        have h := W.apply_mem_toSubmodule (SemidirectProduct.inl r) hx
        rwa [hρapp, hψ, SemidirectProduct.lift_inl] at h
      have hH' : ∀ h : H, ∀ x ∈ Wg, ψH h x ∈ Wg := by
        intro h x hx
        rw [hmem] at hx ⊢
        have h' := W.apply_mem_toSubmodule (SemidirectProduct.inr h) hx
        rwa [hρapp, hψ, SemidirectProduct.lift_inr] at h'
      rcases hirr Wg hR' hH' with h | h
      · left
        apply Subrepresentation.toSubmodule_injective
        apply le_antisymm _ bot_le
        intro v hv
        have : Additive.toMul v ∈ Wg := (hmem _).mpr (by rwa [ofMul_toMul])
        rw [h, Subgroup.mem_bot] at this
        rw [Submodule.mem_bot]
        rw [← ofMul_toMul v, this, ofMul_one]
      · right
        apply Subrepresentation.toSubmodule_injective
        apply le_antisymm le_top
        intro v _
        have : Additive.toMul v ∈ Wg := by rw [h]; exact Subgroup.mem_top _
        rw [hmem, ofMul_toMul] at this
        exact this
  have hfaith : Function.Injective (ρ.comp SemidirectProduct.inl) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : ∀ x : P, ψR r x = x := by
      intro x
      have := congrArg (fun f : Module.End (ZMod q) (Additive P) => f (Additive.ofMul x)) hr
      change ρ (SemidirectProduct.inl r) (Additive.ofMul x) = Additive.ofMul x at this
      rw [hρapp, hψ, SemidirectProduct.lift_inl] at this
      exact Additive.ofMul.injective this
    exact hψR (MulEquiv.ext h1 |>.trans (map_one ψR).symm)
  have hk : (2 : ZMod q) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).mp h2)
  have hce := prime_dimensional_irreducible_elementary_two_action_scalar_centralizer hp hR hφ hk
    hfin ρ hirrρ hfaith
  have hcomm : ∀ g : R ⋊[φ] H,
      Commute (↑(Θ.asGroupHom σ) : Module.End (ZMod q) (Additive P)) (ρ g) := by
    intro g
    have hg : ψ g = ψR g.left * ψH g.right := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
      rw [map_mul, hψ, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
    have e1 : (↑(Θ.asGroupHom σ) : Module.End (ZMod q) (Additive P)) = Θ σ :=
      Representation.asGroupHom_apply _ _
    show _ * _ = _ * _
    rw [e1]
    change Θ σ * Θ (ψ g) = Θ (ψ g) * Θ σ
    rw [← map_mul, ← map_mul, hg]
    have : σ * (ψR g.left * ψH g.right) = (ψR g.left * ψH g.right) * σ := by
      rw [← mul_assoc, hσR, mul_assoc, hσH, ← mul_assoc]
    rw [this]
  obtain ⟨c, -, hc⟩ := (hce (Θ.asGroupHom σ)).mp hcomm
  refine ⟨c.val, fun x => ?_⟩
  have h1 := congrArg (fun f : Module.End (ZMod q) (Additive P) => f (Additive.ofMul x)) hc
  have h2 : (↑(Θ.asGroupHom σ) : Module.End (ZMod q) (Additive P)) (Additive.ofMul x) =
      Additive.ofMul (σ x) := by
    rw [Representation.asGroupHom_apply]
    rfl
  have h3 : (c • (1 : Module.End (ZMod q) (Additive P))) (Additive.ofMul x) =
      c • Additive.ofMul x := by simp
  rw [h2, h3] at h1
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h4 : c • Additive.ofMul x = Additive.ofMul (x ^ c.val) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, ofMul_pow]
  rw [h4] at h1
  exact Additive.ofMul.injective h1

theorem scalar_action_of_qd32_action {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {D R : Subgroup G} (hDq : IsPGroup q D) (hRD : R ≤ normalizer (D : Set G))
    (hfaith : R ⊓ Subgroup.centralizer (D : Set G) = ⊥) (e : R ≃* QD32)
    (hdim : Nat.card (D ⧸ frattini D) = q ^ 4) {b : G} (hbD : b ∈ normalizer (D : Set G))
    (hbR : ∀ r ∈ R, b * r = r * b) :
    ∃ k : ℕ, ∀ d ∈ D, (b * d * b⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨hcard, hext, -, -, -, -, -, hcen, -⟩ :=
    quaternion_dihedral_extraspecial_involution_generation
  let ψ₀ : ↥R →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hRD)
  let ψ : QD32 →* MulAut ↥D := ψ₀.comp e.symm.toMonoidHom
  have hψapp : ∀ (s : QD32) (x : D), ((ψ s x : D) : G) = (e.symm s : G) * x * (e.symm s : G)⁻¹ :=
    fun _ _ => rfl
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : ∀ x : D, (e.symm s : G) * x * (e.symm s : G)⁻¹ = x := by
      intro x
      have := congrArg (fun τ : MulAut ↥D => ((τ x : D) : G)) hs
      exact this
    have hc : (e.symm s : G) ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have := h1 ⟨d, hd⟩
      calc d * (e.symm s : G) = ((e.symm s : G) * d * (e.symm s : G)⁻¹) * (e.symm s : G) := by
            rw [this]
        _ = (e.symm s : G) * d := by group
    have hmem : (e.symm s : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := ⟨(e.symm s).2, hc⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    have : e.symm s = 1 := Subtype.ext hmem
    simpa using this
  set σ : MulAut ↥D := D.normalizerMonoidHom ⟨b, hbD⟩ with hσdef
  have hσapp : ∀ x : D, ((σ x : D) : G) = b * x * b⁻¹ := fun _ => rfl
  have hσ : ∀ s : QD32, σ * ψ s = ψ s * σ := by
    intro s
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show ((σ (ψ s x) : D) : G) = ((ψ s (σ x) : D) : G)
    rw [hσapp, hψapp, hψapp, hσapp]
    have h := hbR (e.symm s : G) (e.symm s).2
    have h2 : (e.symm s : G)⁻¹ * b⁻¹ = b⁻¹ * (e.symm s : G)⁻¹ := by
      rw [← mul_inv_rev b (e.symm s : G), h, mul_inv_rev]
    calc b * ((e.symm s : G) * x * (e.symm s : G)⁻¹) * b⁻¹
        = (b * (e.symm s : G)) * x * ((e.symm s : G)⁻¹ * b⁻¹) := by group
      _ = ((e.symm s : G) * b) * x * (b⁻¹ * (e.symm s : G)⁻¹) := by rw [h, h2]
      _ = (e.symm s : G) * (b * x * b⁻¹) * (e.symm s : G)⁻¹ := by group
  have hcard' : Nat.card QD32 = 2 ^ (1 + 2 * 2) := by rw [hcard]; norm_num
  have : Finite QD32 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := exists_scalar_of_commutes_extraspecial_two_action (n := 2) hq2 hDq hext hcard'
    hcen (by simpa using hdim) ψ hψ hσ
  refine ⟨k, fun d hd => ?_⟩
  have h := hk ⟨d, hd⟩
  refine ⟨_, h, ?_⟩
  simp [hσapp]

theorem scalar_action_of_plane_action {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) {D R A₀ : Subgroup G} (hDe : IsElementaryAbelian q D)
    (hDcard : Nat.card D = q ^ p) (hRe : IsElementaryAbelian 2 R) (hRcard : 4 ≤ Nat.card R)
    (hRD : R ≤ normalizer (D : Set G)) (hA₀D : A₀ ≤ normalizer (D : Set G))
    (hA₀R : A₀ ≤ normalizer (R : Set G)) (hfaith : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hA₀card : Nat.card A₀ = p ^ 2) (hkerA₀ : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (R : Set G)) = p)
    (hirr : ∀ Y : Subgroup G, inSubgroup frattini D ≤ Y → Y ≤ D →
      R ⊔ A₀ ≤ normalizer (Y : Set G) → Y = inSubgroup frattini D ∨ Y = D)
    {b : G} (hbD : b ∈ normalizer (D : Set G)) (hbR : ∀ r ∈ R, b * r = r * b)
    (hbA₀ : ∀ y ∈ A₀, b * y = y * b) :
    ∃ k : ℕ, ∀ d ∈ D, b * d * b⁻¹ = d ^ k := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hDe
  have := hRe
  let : CommGroup ↥D := IsMulCommutative.instCommGroup
  let : CommGroup ↥R := IsMulCommutative.instCommGroup
  let : Module (ZMod 2) (Additive ↥R) := IsElementaryAbelian.isVectorSpace 2
  let _ : MulDistribMulAction A₀ R := conjActionOn hA₀R
  have hsmulR : ∀ (a : A₀) (r : R), ((a • r : R) : G) = (a : G) * r * (a : G)⁻¹ := fun _ _ => rfl
  let φ : ↥A₀ →* MulAut ↥R := MulDistribMulAction.toMulAut ↥A₀ ↥R
  have hφker : φ.ker = (A₀ ⊓ Subgroup.centralizer (R : Set G)).subgroupOf A₀ :=
    (subgroupOf_inf_centralizer_eq_ker hA₀R).symm
  have hφcard : Nat.card φ.range = p := by
    have h1 := Subgroup.index_mul_card φ.ker
    rw [Subgroup.index_ker, hφker, hA₀card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A₀ ⊓ _ ≤ A₀)).toEquiv,
      hkerA₀] at h1
    have hp0 : 0 < p := hp.pos
    have : Nat.card φ.range * p = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  let ψR : ↥R →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hRD)
  let ψH : ↥A₀ →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hA₀D)
  have hψRapp : ∀ (r : R) (x : D), ((ψR r x : D) : G) = (r : G) * x * (r : G)⁻¹ :=
    fun _ _ => rfl
  have hψHapp : ∀ (a : A₀) (x : D), ((ψH a x : D) : G) = (a : G) * x * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hψR : Function.Injective ψR := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : ∀ x : D, (r : G) * x * (r : G)⁻¹ = x := fun x =>
      congrArg (fun τ : MulAut ↥D => ((τ x : D) : G)) hr
    have hc : (r : G) ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have := h1 ⟨d, hd⟩
      calc d * (r : G) = ((r : G) * d * (r : G)⁻¹) * (r : G) := by rw [this]
        _ = (r : G) * d := by group
    have hmem : (r : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := ⟨r.2, hc⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcompat : ∀ (h : A₀) (r : R), ψR (φ h r) = ψH h * ψR r * (ψH h)⁻¹ := by
    intro h r
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have e1 : (ψH h)⁻¹ = ψH h⁻¹ := (map_inv ψH h).symm
    rw [MulAut.mul_apply, MulAut.mul_apply, e1, hψRapp, hψHapp, hψRapp, hψHapp]
    change ((h : G) * (r : G) * (h : G)⁻¹) * (x : G) * ((h : G) * (r : G) * (h : G)⁻¹)⁻¹ = _
    simp only [InvMemClass.coe_inv]
    group
  have hfr : inSubgroup frattini D = ⊥ := by
    have : Fact (IsPGroup q ↥D) := ⟨hDe.isPGroup q ↥D⟩
    rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
  have hirr' : ∀ W : Subgroup ↥D, (∀ r : R, ∀ x ∈ W, ψR r x ∈ W) →
      (∀ h : A₀, ∀ x ∈ W, ψH h x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hWR hWH
    set Y : Subgroup G := W.map D.subtype with hY
    have hYD : Y ≤ D := Subgroup.map_subtype_le W
    have hRY : ∀ r ∈ R, ∀ y ∈ Y, r * y * r⁻¹ ∈ Y := by
      rintro r hr _ ⟨w, hw, rfl⟩
      exact ⟨ψR ⟨r, hr⟩ w, hWR ⟨r, hr⟩ w hw, hψRapp ⟨r, hr⟩ w⟩
    have hAY : ∀ a ∈ A₀, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
      rintro a ha _ ⟨w, hw, rfl⟩
      exact ⟨ψH ⟨a, ha⟩ w, hWH ⟨a, ha⟩ w hw, hψHapp ⟨a, ha⟩ w⟩
    have hYN : R ⊔ A₀ ≤ normalizer (Y : Set G) :=
      sup_le (le_normalizer_of_conj_mem_forall hRY) (le_normalizer_of_conj_mem_forall hAY)
    rcases hirr Y (hfr ▸ bot_le) hYD hYN with h | h
    · left
      rw [hfr] at h
      exact (Subgroup.map_eq_bot_iff_of_injective W D.subtype_injective).mp h
    · right
      apply Subgroup.map_injective D.subtype_injective
      rw [← hY, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set σ : MulAut ↥D := D.normalizerMonoidHom ⟨b, hbD⟩ with hσdef
  have hσapp : ∀ x : D, ((σ x : D) : G) = b * x * b⁻¹ := fun _ => rfl
  have hσR : ∀ r : R, σ * ψR r = ψR r * σ := by
    intro r
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show ((σ (ψR r x) : D) : G) = ((ψR r (σ x) : D) : G)
    rw [hσapp, hψRapp, hψRapp, hσapp]
    have h := hbR (r : G) r.2
    have h2 : (r : G)⁻¹ * b⁻¹ = b⁻¹ * (r : G)⁻¹ := by
      rw [← mul_inv_rev b (r : G), h, mul_inv_rev]
    calc b * ((r : G) * x * (r : G)⁻¹) * b⁻¹
        = (b * (r : G)) * x * ((r : G)⁻¹ * b⁻¹) := by group
      _ = ((r : G) * b) * x * (b⁻¹ * (r : G)⁻¹) := by rw [h, h2]
      _ = (r : G) * (b * x * b⁻¹) * (r : G)⁻¹ := by group
  have hσH : ∀ a : A₀, σ * ψH a = ψH a * σ := by
    intro a
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show ((σ (ψH a x) : D) : G) = ((ψH a (σ x) : D) : G)
    rw [hσapp, hψHapp, hψHapp, hσapp]
    have h := hbA₀ (a : G) a.2
    have h2 : (a : G)⁻¹ * b⁻¹ = b⁻¹ * (a : G)⁻¹ := by
      rw [← mul_inv_rev b (a : G), h, mul_inv_rev]
    calc b * ((a : G) * x * (a : G)⁻¹) * b⁻¹
        = (b * (a : G)) * x * ((a : G)⁻¹ * b⁻¹) := by group
      _ = ((a : G) * b) * x * (b⁻¹ * (a : G)⁻¹) := by rw [h, h2]
      _ = (a : G) * (b * x * b⁻¹) * (a : G)⁻¹ := by group
  have hPq : ∀ x : D, x ^ q = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p q D) x
  obtain ⟨k, hk⟩ := exists_scalar_of_commutes_prime_dimensional_plane_action hp hq2 hPq hDcard
    hRcard φ hφcard ψR ψH hψR hcompat hirr' hσR hσH
  refine ⟨k, fun d hd => ?_⟩
  have h := congrArg Subtype.val (hk ⟨d, hd⟩)
  rw [hσapp] at h
  exact h

theorem card_quotient_frattini_of_isQDShape {G : Type*} [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) {D : Subgroup G} (h : IsQDShape q D) :
    Nat.card (D ⧸ frattini D) = q ^ 4 := by
  have : Fact q.Prime := ⟨hq⟩
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini D)
  rcases h with ⟨hDe, hDcard⟩ | ⟨-, hDcard, hcomm, -, hfrat⟩
  · have : Fact (IsPGroup q ↥D) := ⟨hDe.isPGroup q ↥D⟩
    have hbot : frattini ↥D = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := q)
    rw [hbot, Subgroup.card_bot, mul_one] at hmul
    rw [hbot, ← hmul, hDcard]
  · have hc : Nat.card (frattini ↥D) = q := by
      have h1 := hfrat
      rw [inSubgroup] at h1
      rw [← Subgroup.card_map_of_injective D.subtype_injective, h1]
      exact hcomm
    rw [hc, hDcard] at hmul
    have hq0 : 0 < q := hq.pos
    have : Nat.card (D ⧸ frattini D) * q = q ^ 4 * q := by rw [← pow_succ, ← hmul]
    exact Nat.eq_of_mul_eq_mul_right hq0 this

theorem le_inSubgroup_frattini_of_proper_invariant {G : Type} [Group G] [Finite G]
    {A' R D : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hodd : ¬ 2 ∣ Nat.card A')
    (hA'R : A' ≤ normalizer (R : Set G)) (hA'D : A' ≤ normalizer (D : Set G))
    (hRA' : ⁅R, A'⁆ = R) (hRD : ⁅R, D⁆ ≠ ⊥)
    (hmin : ∀ U : Subgroup G, U < R → A' ≤ normalizer (U : Set G) → ⁅U, A'⁆ = U →
      ⁅U, D⁆ = ⊥) :
    ∀ U : Subgroup G, U < R → A' ≤ normalizer (U : Set G) → U ≤ inSubgroup frattini R := by
  intro U hUR hA'U
  let _ : MulDistribMulAction A' R := conjActionOn hA'R
  have hsmulR : ∀ (a : A') (r : R), ((a • r : R) : G) = (a : G) * r * (a : G)⁻¹ :=
    fun _ _ => rfl
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  obtain ⟨K, hKP, hKinv, hPA, hU⟩ := relative_minimal_hypotheses_of_ambient hA'R hA'D hRA' hRD hmin
  obtain ⟨-, -, hprop, -⟩ := relative_minimal_action_frattini_irreducibility Nat.prime_two hR2
    hodd K hKP hKinv hPA hU
  have hUR' : U ≤ R := hUR.le
  have hlt : U.subgroupOf R < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    apply hUR.ne
    refine le_antisymm hUR' fun r hr => ?_
    have : (⟨r, hr⟩ : R) ∈ U.subgroupOf R := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hinv : ∀ a : A', ∀ x ∈ U.subgroupOf R, a • x ∈ U.subgroupOf R := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmulR]
    exact (Subgroup.mem_normalizer_iff.mp (hA'U a.2) x).mp hx
  have h := hprop (U.subgroupOf R) hlt hinv
  intro u hu
  have hu' : (⟨u, hUR' hu⟩ : R) ∈ U.subgroupOf R := hu
  exact ⟨_, h hu', rfl⟩

theorem scalar_action_le_thetaQuotientCentralizer {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) {A L D B : Subgroup G} (hLfam : L ∈ thetaComponentFamily p A)
    (hAL : A ≤ normalizer (L : Set G)) (hAD : A ≤ normalizer (D : Set G))
    (hLD : L ≤ normalizer (D : Set G)) (hDq : IsPGroup q D) (hLDc : ⁅L, D⁆ ≠ ⊥) (hBA : B ≤ A)
    (hscalar : ∀ b ∈ B, ∃ k : ℕ, ∀ d ∈ D, (b * d * b⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D) :
    B ≤ thetaQuotientCentralizer p A L := by
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hLfam
  have hperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsAt hLc
  have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperf
  have hLq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hLc
  obtain ⟨-, hnormal⟩ := theta_le_and_normal (G := G) p L
  set N := inSubgroup (aschbacherSolvableCore p) L with hN
  have hNsub : N.subgroupOf L = aschbacherSolvableCore p L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hNq : CFSG.IsQuasisimple (L ⧸ N.subgroupOf L) :=
    LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hNsub.symm) hLq
  have hBL : B ≤ normalizer (L : Set G) := hBA.trans hAL
  have hBD : B ≤ normalizer (D : Set G) := hBA.trans hAD
  have := hnormal
  have hcomm := scalar_critical_action_centralizes_quasisimple_solvable_quotient hq hLL
    (theta_solvable_and_not_dvd hp L).1 hNq hLD hDq hLDc hBL hBD hscalar
  intro b hb
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨hBA hb, hBL hb, fun l hl => ?_⟩
  have h := hcomm (Subgroup.commutator_mem_commutator hl hb)
  have e : b * l * b⁻¹ * l⁻¹ = (⁅l, b⁆)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact N.inv_mem h

theorem thetaQuotientCentralizer_ne_of_commutator_eq_self {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {A L : Subgroup G} (hLfam : L ∈ thetaComponentFamily p A)
    (hLA : ⁅L, A⁆ = L) : thetaQuotientCentralizer p A L ≠ A := by
  intro hE
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hLfam
  have hLq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hLc
  have hle : L ≤ inSubgroup (aschbacherSolvableCore p) L := by
    calc L = ⁅L, A⁆ := hLA.symm
      _ ≤ inSubgroup (aschbacherSolvableCore p) L := by
        rw [Subgroup.commutator_le]
        intro l hl a ha
        have h := (mem_thetaQuotientCentralizer_iff.mp (hE ▸ ha)).2.2 l hl
        have e : ⁅l, a⁆ = (a * l * a⁻¹ * l⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.inv_mem _ h
  have hθtop : aschbacherSolvableCore p L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have : Subsingleton (L ⧸ aschbacherSolvableCore p L) := by
    rw [hθtop]
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨-, -, a, b, hab⟩ := hLq
  exact hab (Subsingleton.elim _ _)


theorem nonquasisimple_moving_theta_component_scalar_kernel_hyperplane_of
    (hB5 : SelectedPrimeElementsNormalizeThetaComponents) :
    NonquasisimpleMovingThetaComponentScalarKernelHyperplane := by
  intro hTwo G _ _ p A hS L hL hnq
  have hp : p.Prime := sectionTenSetup_prime hS
  have hp3 : 3 < p := sectionTenSetup_three_lt hS
  have hvan : AschVanishing G p := sectionTenSetup_vanishing hS
  have heG : evenRank G = 3 := sectionTenSetup_evenRank_eq hS
  have he : evenRank G ≤ 3 := heG.le
  have hAe : IsElementaryAbelian p A := hS.2.2.2.2.2.2.1
  have hAcard : Nat.card A = p ^ 3 := hS.2.2.2.2.2.2.2.1
  have hsig : p ∈ sigmaA G := sectionTenSetup_mem_sigmaA hS
  have hp57 : p = 5 ∨ p = 7 := by
    rcases nonquasisimple_moving_theta_component_prime_cut_of hB5 hTwo G he p hp hp3 hvan A hAe
      hAcard L hL with h | h
    · exact absurd h hnq
    · exact h
  obtain ⟨hAL, hLA, -, -, -⟩ :=
    moving_theta_component_quasisimplicity_reduces_to_odd_core_centralization_of hB5 G he p hp hp3
      hvan A hAe hAcard L hL
  obtain ⟨q, hq, hq2, hqp, D, R, hD1, hDL, hDchar, hDO, hDexp, hDcl, hR2, hRL, hAR, hRA, hR1, hRD,
    hmin, hrel, hrank⟩ :=
    nonquasisimple_moving_theta_component_minimal_odd_core_action_of hB5 G he p hp hp3 hvan A hAe
      hAcard L hL hnq
  have hAD : A ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf hAL hDL hDchar
  have hLD : L ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf Subgroup.le_normalizer hDL hDchar
  have hRD' : R ≤ normalizer (D : Set G) := hRL.trans hLD
  have hRAD : R ⊔ A ≤ normalizer (D : Set G) := sup_le hRD' hAD
  have hDq : IsPGroup q D := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hDexp x x.2)⟩
  have : IsElementaryAbelian p A := hAe
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hBcard : Nat.card B = p ^ 2 := by
    have h := Subgroup.relIndex_mul_card B A
    rw [inf_eq_left.mpr hBA, hrel, hAcard] at h
    have : p * Nat.card B = p * p ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have hbD : ∀ b ∈ B, b ∈ normalizer (D : Set G) := fun b hb => hAD hb.1
  have hbR : ∀ b ∈ B, ∀ r ∈ R, b * r = r * b := fun b hb r hr =>
    (Subgroup.mem_centralizer_iff.mp hb.2 r hr).symm
  have hscalar : ∀ b ∈ B, ∃ k : ℕ, ∀ d ∈ D,
      (b * d * b⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D := by
    have hmin' : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U →
        U ≤ Subgroup.centralizer (D : Set G) := fun U hU hAU hUA =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hmin U hU hAU hUA)
    have hone : ∀ (b : G) (k : ℕ) (d : G), b * d * b⁻¹ = d ^ k →
        (b * d * b⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D := fun b k d h => by
      rw [h, inv_mul_cancel]
      exact one_mem _
    rcases hp57 with hp5 | hp7
    ·
      have hgood : GoodGlobalRank G p := fun h => absurd h (by omega)
      have hcardB : p ≤ Nat.card B := by
        rw [hBcard]
        exact Nat.le_self_pow two_ne_zero p
      obtain ⟨-, hred⟩ := hTwo.2.1 G heG p hp hsig hp3 q hq hq2 hqp A R D hAe hAR hR2 hRA hR1 hRAD
        hDq hDexp hDcl hRD hrel hcardB hmin' hgood
      rcases hred with hBD | ⟨-, ⟨e⟩, hfaith, -, -, -, -, hshape⟩
      · intro b hb
        have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBD hb
        refine ⟨1, fun d hd => ?_⟩
        have h := Subgroup.mem_centralizer_iff.mp hc d hd
        refine hone b 1 d ?_
        rw [pow_one, ← h]
        group
      · intro b hb
        exact scalar_action_of_qd32_action hq hq2 hDq hRD' hfaith e
          (card_quotient_frattini_of_isQDShape hq hshape) (hbD b hb) (hbR b hb)
    ·
      intro b hb
      obtain ⟨a, b₀, haA, haB, hb₀B, hb₀1, hA₀A, hA₀elem, hA₀card, hfac, hker⟩ :=
        exists_plane_of_index_prime_subgroup hp hAe hAcard hBA hrel
      set A₀ := zpowers a ⊔ zpowers b₀ with hA₀
      have hset : MinTwoActionSetting p q A₀ D R :=
        minTwoActionSetting_of_plane hp hq hp3 hq2 hqp hA₀elem hA₀card hA₀A hfac hRAD hDexp hDcl
          hR2 hAR hRA hR1 hRD hmin
      have hA₀R : A₀ ≤ normalizer (R : Set G) := hA₀A.trans hAR
      have hA₀D : A₀ ≤ normalizer (D : Set G) := hA₀A.trans hAD
      obtain ⟨hAlt, -, hlift⟩ := hTwo
      obtain ⟨hRe, hRcard⟩ : IsElementaryAbelian 2 R ∧ Nat.card R = 8 := by
        rcases hAlt G p q A₀ D R hset hrank with
          ⟨⟨⟨h5, -⟩ | ⟨-, hRe, hRcard⟩, -⟩⟩ | ⟨h5, -⟩ | ⟨h5, -⟩
        · omega
        · exact ⟨hRe, hRcard⟩
        · omega
        · omega
      have hkerA₀ : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (R : Set G)) = p := by
        rw [← hker, hB, ← inf_assoc, inf_eq_left.mpr hA₀A]
      have hfrR : inSubgroup frattini R = ⊥ := by
        have : Fact (IsPGroup 2 ↥R) := ⟨hRe.isPGroup 2 ↥R⟩
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
      have hodd : ¬ 2 ∣ Nat.card A₀ := by
        rw [hA₀card, hp7]
        decide
      have hmin₀ : ∀ U : Subgroup G, U < R → A₀ ≤ normalizer (U : Set G) → ⁅U, A₀⁆ = U →
          ⁅U, D⁆ = ⊥ := fun U hU hA₀U hUA₀ =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hset.R_min U hU hA₀U hUA₀)
      have hirrR : ∀ Y : Subgroup G, Y ≤ R → A₀ ≤ normalizer (Y : Set G) → Y = ⊥ ∨ Y = R := by
        intro Y hYR hA₀Y
        by_cases hYe : Y = R
        · exact Or.inr hYe
        refine Or.inl ?_
        have h := le_inSubgroup_frattini_of_proper_invariant hR2 hR1 hodd hA₀R hA₀D hset.R_comm
          hRD hmin₀ Y (lt_of_le_of_ne hYR hYe) hA₀Y
        rw [hfrR] at h
        exact le_bot_iff.mp h
      have hRA₀D : R ⊔ A₀ ≤ normalizer (D : Set G) := sup_le hRD' hA₀D
      obtain ⟨hfaith, hDe, hDcard, -, -, ⟨-, -, hirrD⟩, -⟩ := hlift G p q 3 A₀ D R hp hq hq2 hqp
        (Or.inl ⟨hp7, rfl⟩) hA₀elem hA₀card hA₀R hRe (by rw [hRcard]; norm_num) hkerA₀ hirrR
        hRA₀D hDq hDexp hDcl hRD hrank
      have hbA₀ : ∀ y ∈ A₀, b * y = y * b := fun y hy =>
        mul_comm_of_isMulCommutative hb.1 (hA₀A hy)
      obtain ⟨k, hk⟩ := scalar_action_of_plane_action hp hq hq2 hDe hDcard hRe (by omega) hRD' hA₀D
        hA₀R hfaith hA₀card hkerA₀ hirrD (hbD b hb) (hbR b hb) hbA₀
      exact ⟨k, fun d hd => hone b k d (hk d hd)⟩
  have hLDc : ⁅L, D⁆ ≠ ⊥ := fun h => hRD (le_bot_iff.mp
    ((Subgroup.commutator_mono hRL le_rfl).trans h.le))
  have hBE : B ≤ thetaQuotientCentralizer p A L :=
    scalar_action_le_thetaQuotientCentralizer hp hq hL.1 hAL hAD hLD hDq hLDc hBA hscalar
  have hEA : thetaQuotientCentralizer p A L ≤ A := inf_le_left
  have hEne : thetaQuotientCentralizer p A L ≠ A :=
    thetaQuotientCentralizer_ne_of_commutator_eq_self hp hL.1 hLA
  have hEB : thetaQuotientCentralizer p A L = B := by
    have hEle : Nat.card (thetaQuotientCentralizer p A L) ≤ Nat.card B := by
      have hdvd : Nat.card (thetaQuotientCentralizer p A L) ∣ p ^ 3 :=
        hAcard ▸ Subgroup.card_dvd_of_le hEA
      obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have hj3 : j ≠ 3 := by
        rintro rfl
        exact hEne (Subgroup.eq_of_le_of_card_ge hEA (by rw [hAcard, hjc]))
      rw [hjc, hBcard]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    exact (Subgroup.eq_of_le_of_card_ge hBE hEle).symm
  refine ⟨hp57, ?_, q, hq, hq2, hqp, D, R, hD1, hDL, hDchar, hDO, hDexp, hDcl, hR2, hRL, hAR, hRA,
    hR1, hRD, hEB.symm, hmin, hrank, fun e he => hscalar e (hEB ▸ he)⟩
  rw [hEB]
  exact hrel

end CFSG.RankThree.PartOne
