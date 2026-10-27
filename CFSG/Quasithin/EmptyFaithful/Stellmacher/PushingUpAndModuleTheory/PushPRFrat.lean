module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRBase
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26Interfaces

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G]

structure NatFacts (X P Z : Subgroup G) : Prop where
  odd : ∃ u ∈ X, Odd (orderOf u) ∧ u ∉ pCoreOf 2 X
  irr : ∀ W : Subgroup G, W ≤ Z → X ≤ Subgroup.normalizer (W : Set G) →
    W ≤ zZero X Z ∨ Z ≤ W ⊔ zZero X Z
  tr : ∀ x ∈ P, x ∉ pCoreOf 2 X →
    (pCoreOf 2 X).relIndex P ≤ (fixSecIn (Subgroup.zpowers x) (zZero X Z) Z).relIndex Z

section Burnside

variable [Finite G]

theorem phi_le_map_frattini {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    phi Q ≤ (frattini ↥Q).map Q.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥Q) := ⟨hQ⟩
  have hfr := CFSG.frattini_eq_closure_commutator_union_powers (R := ↥Q) (p := 2)
  refine phi_le_of (fun a ha => ?_) (fun a ha b hb => ?_)
  · refine ⟨⟨a, ha⟩ ^ 2, ?_, by simp [pow_two]⟩
    rw [hfr]
    exact Subgroup.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  · refine ⟨⁅(⟨a, ha⟩ : ↥Q), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [hfr]
    exact Subgroup.subset_closure (Or.inl (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top _) (Subgroup.mem_top _)))

theorem centralizes_of_trivial_mod_phi {Q : Subgroup G} (hQ : IsPGroup 2 Q) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hodd : Odd (orderOf g))
    (htriv : ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ phi Q) : ∀ q ∈ Q, g * q * g⁻¹ = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : MulAut ↥Q := Q.normalizerMonoidHom ⟨g, hg⟩ with hτdef
  have hτ : ∀ x : ↥Q, ((τ x : ↥Q) : G) = g * x * g⁻¹ := fun _ => rfl
  have hτn : τ ^ orderOf g = 1 := by
    rw [hτdef, ← map_pow]
    have : (⟨g, hg⟩ : ↥(Subgroup.normalizer (Q : Set G))) ^ orderOf g = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one]
  have hmem : τ ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥Q)).ker := by
    rw [MonoidHom.mem_ker, ← MonoidHom.mem_ker,
      CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 := htriv ((x⁻¹ : ↥Q) : G) (x⁻¹).2
    have h2 := phi_le_map_frattini hQ h1
    obtain ⟨y, hy, hyeq⟩ := h2
    have : y = (τ x)⁻¹ * x := by
      apply Subtype.ext
      rw [show ((y : ↥Q) : G) = _ from hyeq]
      simp only [hτ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
    rw [← this]
    exact hy
  obtain ⟨j, hj⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hQ).2 ⟨τ, hmem⟩
  have hj' : τ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf g) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτn) (orderOf_dvd_of_pow_eq_one hj')
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  intro q hq
  have := congrArg (fun f : MulAut ↥Q => ((f ⟨q, hq⟩ : ↥Q) : G)) hdvd
  simpa [hτ] using this

end Burnside

section Phi

variable [Finite G] {X P Z : Subgroup G}

omit [Finite G] in
theorem eq_one_of_odd_of_mem {R : Subgroup G} (hR : IsPGroup 2 R) {x : G} (hx : x ∈ R)
    (ho : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ho)
  have h := Nat.dvd_gcd (dvd_refl (orderOf x)) (orderOf_dvd_of_pow_eq_one hk')
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

theorem PushHyp.pCore_isPGroup (h : PushHyp X P Z) : IsPGroup 2 (pCoreOf 2 X) :=
  h.sylow.2.1.to_le h.core_le

theorem not_le_phi_sup (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z) :
    ¬ Z ≤ phi (pCoreOf 2 X) ⊔ zZero X Z := by
  intro hZ
  set Q := pCoreOf 2 X with hQ
  set Z₀ := zZero X Z with hZ₀
  obtain ⟨u, huX, huo, huQ⟩ := hN.odd
  have huL : u ∈ pResidualOf 2 X := by
    rw [← oTwoUpper_eq_pResidualOf]; exact mem_oTwoUpper_of_odd huX huo
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := PushHyp.le_normalizer_core
  have huN : u ∈ Subgroup.normalizer (Q : Set G) := hXQ huX
  have hQZ : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z := fun z hz q hq =>
    (Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer hq) z hz)
  have hZQ : Z ≤ Q := h.le_core
  have hZ₀n : Z₀ ≤ Subgroup.normalizer (phi Q : Set G) := fun x hx =>
    le_normalizer_phi (R := Q) (S := Q) Subgroup.le_normalizer (hZQ hx.1)
  have hZ₀c : ∀ k ∈ Z₀, u * k * u⁻¹ = k := fun k hk => by
    have : u * k = k * u := Subgroup.mem_centralizer_iff.mp hk.2 u huL
    rw [this]; group
  have hZe : ∀ z ∈ Z, z * z = 1 := fun z hz => by
    have := h.elemAbelian.2 z hz
    simpa [pow_two] using this
  have hkey : ∀ q ∈ Q, u * u * q * (u * u)⁻¹ * q⁻¹ ∈ phi Q := by
    intro q hq
    have hc : ⁅u, q⁆ ∈ Z := by
      have h1 : ⁅q, u⁆ ∈ ⁅pCoreOf 2 X, pResidualOf 2 X⁆ := Subgroup.commutator_mem_commutator hq huL
      have h2 := Z.inv_mem (hB h1)
      rwa [commutatorElement_inv] at h2
    obtain ⟨f, hf, k, hk, hfk⟩ := mem_sup_of_le_normalizer hZ₀n (hZ hc)
    have hkZ : k ∈ Z := hk.1
    have hfQ : f ∈ Q := phi_le_self Q hf
    have hkf : k * f = f * k := hQZ k hkZ f hfQ
    have hu1 : u * q * u⁻¹ = f * k * q := by
      have : u * q * u⁻¹ * q⁻¹ = f * k := hfk
      calc u * q * u⁻¹ = (u * q * u⁻¹ * q⁻¹) * q := by group
        _ = f * k * q := by rw [this]
    have e : u * u * q * (u * u)⁻¹ * q⁻¹ =
        (u * f * u⁻¹) * (u * k * u⁻¹) * (u * q * u⁻¹) * q⁻¹ := by
      calc u * u * q * (u * u)⁻¹ * q⁻¹ = u * (u * q * u⁻¹) * u⁻¹ * q⁻¹ := by group
        _ = u * (f * k * q) * u⁻¹ * q⁻¹ := by rw [hu1]
        _ = _ := by group
    rw [e, hZ₀c k hk, hu1]
    have e2 : u * f * u⁻¹ * k * (f * k * q) * q⁻¹ = (u * f * u⁻¹) * (k * f * k) := by group
    rw [e2, hkf]
    have e3 : f * k * k = f := by rw [mul_assoc, hZe k hkZ, mul_one]
    rw [e3]
    exact Subgroup.mul_mem _ (conj_mem_phi huN hf) hf
  have hcen := centralizes_of_trivial_mod_phi h.pCore_isPGroup
    (g := u * u) (Subgroup.mul_mem _ huN huN)
    (by
      have : orderOf (u * u) ∣ orderOf u := by
        rw [← pow_two]; exact orderOf_pow_dvd 2
      exact Odd.of_dvd_nat huo this)
    hkey
  have hmemQ : u * u ∈ Q := by
    apply h.mem_core_of_centralizes (Subgroup.mul_mem _ huX huX)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hcen z (hZQ hz)
    have h2 : u * u * z = z * (u * u) := by
      calc u * u * z = (u * u * z * (u * u)⁻¹) * (u * u) := by group
        _ = z * (u * u) := by rw [h1]
    exact h2.symm
  apply huQ
  obtain ⟨m, hm⟩ := huo
  have : u = (u * u) ^ (m + 1) := by
    have h1 : u ^ (orderOf u) = 1 := pow_orderOf_eq_one u
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf u + 1 by omega, pow_succ, h1, one_mul]
  rw [this]
  exact Q.pow_mem hmemQ _

theorem inf_phi_le_zZero (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z) :
    Z ⊓ phi (pCoreOf 2 X) ≤ zZero X Z := by
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := PushHyp.le_normalizer_core
  have hn : X ≤ Subgroup.normalizer ((Z ⊓ phi (pCoreOf 2 X) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have fwd : ∀ g ∈ X, ∀ x ∈ Z ⊓ phi (pCoreOf 2 X), g * x * g⁻¹ ∈ Z ⊓ phi (pCoreOf 2 X) :=
      fun g hg x hx =>
        ⟨(Subgroup.mem_normalizer_iff.mp (h.normal hg) x).mp hx.1, conj_mem_phi (hXQ hg) hx.2⟩
    refine ⟨fwd g hg x, fun hx => ?_⟩
    have := fwd g⁻¹ (X.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  rcases hN.irr _ inf_le_left hn with h1 | h1
  · exact h1
  · exact absurd (h1.trans (sup_le_sup_right inf_le_right _)) (not_le_phi_sup h hB hN)

end Phi

end CFSG.Quasithin.F53Push
