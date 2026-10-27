module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoChars
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerBasic

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card H ≤ Nat.card (H.map (MulAut.conj g).toMonoidHom) :=
    (Nat.card_congr (H.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).le
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => h x hx, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by
    have h1 : g * y * g⁻¹ = g * x * g⁻¹ := by simpa using hyx
    simpa using h1
  rw [← this]
  exact hy

theorem exists_sgnZ_of_ne_zero : ∀ a a' : ZMod 3, a ≠ 0 → a' ≠ 0 →
    a = sgnZ false a' ∨ a = sgnZ true a' := by
  decide

theorem coprime_orderOf_three {G : Type*} [Group G] {g : G} (hg : g * g = 1) :
    Nat.Coprime (orderOf g) 3 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hg])
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h <;> rw [h] <;> norm_num

theorem bxor_bxor_cancel (b c : Bool) : ((b ^^ c) ^^ c) = b := by cases b <;> cases c <;> rfl

section F4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem eq_one_of_sq_eq_one_F4 (hK : Nat.card K = 2) [Fact (Irreducible (phi3 K))]
    {u : (AdjoinRoot (phi3 K))ˣ} (hu : u ^ 2 = 1) : u = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hne : phi3 K ≠ 0 := (Fact.out : Irreducible (phi3 K)).ne_zero
  have hdim : (AdjoinRoot.powerBasis hne).dim = 2 := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_phi3]
  have : Module.Finite K (AdjoinRoot (phi3 K)) := (AdjoinRoot.powerBasis hne).finite
  have : Finite (AdjoinRoot (phi3 K)) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot (phi3 K)) := Fintype.ofFinite _
  have hcard : Nat.card (AdjoinRoot (phi3 K)) = 4 := by
    rw [Nat.card_eq_fintype_card, Module.card_fintype (AdjoinRoot.powerBasis hne).basis,
      Fintype.card_fin, hdim, ← Nat.card_eq_fintype_card, hK]
    norm_num
  have hU : Nat.card (AdjoinRoot (phi3 K))ˣ = 3 := by rw [Nat.card_units, hcard]
  have h3 : orderOf u ∣ 3 := hU ▸ orderOf_dvd_natCard u
  have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu
  have h1 : orderOf u ∣ 1 := by
    have := Nat.dvd_gcd h3 h2
    rwa [show Nat.gcd 3 2 = 1 by rfl] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

variable {n : ℕ}

theorem mem_spPull_of_mul_self (hK : Nat.card K = 2) {x g : StatedSp n K}
    (hg : g ∈ spSupported x {phi3 K, KCOrthogonal.reciprocalPolynomial (phi3 K)})
    (hgg : g * g = 1) : g ∈ spPull x (phi3 K) := by
  have : Fact (Irreducible (phi3 K)) := ⟨phi3_irreducible hK⟩
  refine SevSpNs.mem_spPull_of_factorDet hg (eq_one_of_sq_eq_one_F4 hK ?_)
  rw [← map_pow]
  convert map_one (SevSpNs.factorDet x (phi3 K))
  exact Subtype.ext (by rw [Subgroup.coe_pow, sq, hgg, OneMemClass.coe_one])

end F4

section Choice

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] {n : ℕ} {L : Type} [Field L]
  [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)
  {ψ : StatedSp n K →* G} {Bs D : Subgroup G}

namespace SpFrame

omit [Finite G] in
theorem psi_move_conj (hζ : ζ ^ 3 = 1) (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool)
    (f : Fin F.s → ZMod 3) :
    ψ (F.move π η) * ψ (F.tor f) * (ψ (F.move π η))⁻¹ = ψ (F.tor (moveExp π η f)) := by
  rw [← map_inv, ← map_mul, ← map_mul, F.move_conj hζ]

theorem psi_move_inv_mem_normalizer (hζ : ζ ^ 3 = 1)
    (hBs : ∀ g, g ∈ Bs ↔ ∃ f, ψ (F.tor f) = g) (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool) :
    (ψ (F.move π η))⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := by
  refine Subgroup.inv_mem _ (mem_normalizer_of_conj_mem fun x hx => ?_)
  obtain ⟨f, rfl⟩ := (hBs x).mp hx
  rw [F.psi_move_conj hζ]
  exact (hBs _).mpr ⟨_, rfl⟩

omit [Finite G] in
theorem conj_psi_move_inv (hζ : ζ ^ 3 = 1) (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool)
    (f : Fin F.s → ZMod 3) :
    (MulAut.conj ((ψ (F.move π η))⁻¹)⁻¹).toMonoidHom (ψ (F.tor f)) =
      ψ (F.tor (moveExp π η f)) := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact F.psi_move_conj hζ π η f

theorem choice_of_swap (hζo : IsPrimitiveRoot ζ 3) (hψ : Function.Injective ψ)
    (hBs : ∀ g, g ∈ Bs ↔ ∃ f, ψ (F.tor f) = g) {t₁ t₂ : Fin F.s → ZMod 3}
    (hD : ∀ g, g ∈ D ↔ ∃ a, ψ (F.tor (comb2 t₁ t₂ a)) = g) {L₁ : Subgroup G}
    {i₁ i₂ i₃ j₁ j₂ : Fin F.s} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hj : j₁ ≠ j₂) {ε bsw bsw' : Bool}
    (hε : ∀ a, comb2 t₁ t₂ a j₁ = sgnZ ε (comb2 t₁ t₂ a j₂))
    (hg : ψ (F.swap i₁ i₂ bsw) ∈ L₁) (hl : ψ (F.swap i₁ i₃ bsw') ∈ L₁) :
    ∃ m ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) 3 := by
  have hζ := hζo.pow_eq_one
  obtain ⟨π, hπ1, hπ2⟩ := exists_perm_pair h12 hj
  set η : Fin F.s → Bool := fun l => if l = i₁ then bsw ^^ ε else false with hη
  refine ⟨(ψ (F.move π η))⁻¹, ⟨Subgroup.inv_mem _ ⟨_, rfl⟩,
    F.psi_move_inv_mem_normalizer hζ hBs π η⟩, ψ (F.swap i₁ i₂ bsw), hg,
    ⟨ψ (F.swap i₁ i₃ bsw'), hl, ?_⟩, ?_, coprime_orderOf_three ?_⟩
  ·
    intro h
    have h' : F.swap i₁ i₂ bsw * F.swap i₁ i₃ bsw' = F.swap i₁ i₃ bsw' * F.swap i₁ i₂ bsw :=
      hψ (by rw [map_mul, map_mul]; exact h)
    have e1 := congrArg (fun Y => spEnd Y (F.Φ (Pi.single i₃ 1))) h'
    simp only [spEnd_mul_apply] at e1
    rw [F.swap_acts i₁ i₃ bsw', F.swap_acts i₁ i₂ bsw, F.swap_acts i₁ i₂ bsw,
      F.swap_acts i₁ i₃ bsw'] at e1
    have e2 := congrFun (F.Φ.injective e1) i₂
    rw [swapL_apply_right, swapL_apply_left, Pi.single_eq_same,
      swapL_apply_of_ne bsw' h12.symm h23, swapL_apply_right, Pi.single_eq_of_ne h13,
      map_zero, (sgnL F.σ bsw).map_eq_zero_iff, (sgnL F.σ bsw').map_eq_zero_iff] at e2
    exact one_ne_zero e2
  ·
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨a, rfl⟩ := (hD e).mp he
    rw [F.conj_psi_move_inv hζ, ← map_mul, ← map_mul]
    congr 1
    refine (F.swap_comm_tor hζ bsw ?_).symm
    rw [moveExp_apply, moveExp_apply, hπ1, hπ2, hε a]
    simp only [hη, Ne.symm h12, ↓reduceIte]
    rw [sgnZ_sgnZ_xor, bxor_bxor_cancel, sgnZ_false]
  · rw [← map_mul, F.swap_mul_self h12, map_one]

theorem choice_of_zero [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (hBs : ∀ g, g ∈ Bs ↔ ∃ f, ψ (F.tor f) = g) {t₁ t₂ : Fin F.s → ZMod 3}
    (hD : ∀ g, g ∈ D ↔ ∃ a, ψ (F.tor (comb2 t₁ t₂ a)) = g) {L₁ : Subgroup G}
    (hL₁q : CFSG.Assembly.IsQuasisimple ↥L₁) (hL₁G : L₁ ≤ ψ.range) {β : Fin F.s → ZMod 3}
    (hL₁F : L₁.comap ψ ≤ spFixedFactor (F.tor β)) {z₁ z₂ j₁ j₂ : Fin F.s} (hz : z₁ ≠ z₂)
    (hj : j₁ ≠ j₂) (hzβ : ∀ l, β l = 0 → l = z₁ ∨ l = z₂)
    (hzero : ∀ a, comb2 t₁ t₂ a j₁ = 0 ∧ comb2 t₁ t₂ a j₂ = 0) :
    ∃ m ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) 3 := by
  have hζ := hζo.pow_eq_one
  obtain ⟨π, hπ1, hπ2⟩ := exists_perm_pair hz hj
  set η : Fin F.s → Bool := fun _ => false with hη
  obtain ⟨g, hgL, hgZ, hgp⟩ := ggAKF_exists_noncentral_coprime_mem hL₁q Nat.prime_three
  refine ⟨(ψ (F.move π η))⁻¹, ⟨Subgroup.inv_mem _ ⟨_, rfl⟩,
    F.psi_move_inv_mem_normalizer hζ hBs π η⟩, g, hgL, hgZ, ?_, hgp⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨a, rfl⟩ := (hD e).mp he
  rw [F.conj_psi_move_inv hζ]
  obtain ⟨g', rfl⟩ := hL₁G hgL
  have hg' : g' ∈ spFixedFactor (F.tor β) := hL₁F hgL
  have hmem := F.tor_mem_spSupported hK hζo β (moveExp π η (comb2 t₁ t₂ a))
    (fun l hl => by
      rw [moveExp_apply, hη, sgnZ_false]
      rcases hzβ l hl with rfl | rfl
      · rw [hπ1]
        exact (hzero a).1
      · rw [hπ2]
        exact (hzero a).2) (O := {phi3 K}) rfl
  have hc := commute_of_mem_spFixedFactor hK (F.tor_pow_three hζ β)
    (fun h => phi3_ne_X_sub_one (Set.mem_singleton_iff.mp h).symm) hg' hmem
  rw [← map_mul, ← map_mul, hc]

end SpFrame

end Choice

end ChoiceTwo

end CFSG.StandardType
