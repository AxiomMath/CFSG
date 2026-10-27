module

public import CFSG.Quasithin.Background.VolIExtraspecialRank
public import CFSG.Quasithin.H13.U3S1347C

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

section Module

variable {W : Type*} [CommGroup W] [Finite W]

@[expose] def commAutU3 (z : MulAut W) : W →* W where
  toFun w := z w * w⁻¹
  map_one' := by simp
  map_mul' u v := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]

omit [Finite W] in
theorem commAutU3_apply (z : MulAut W) (w : W) : commAutU3 z w = z w * w⁻¹ := rfl

omit [Finite W] in
theorem eq_one_of_mem_range_commAutU3 (hW2 : ∀ w : W, w ^ 2 = 1) {z : MulAut W}
    (hz3 : z ^ 3 = 1) {u : W} (hu : u ∈ (commAutU3 z).range) (hzu : z u = u) : u = 1 := by
  obtain ⟨v, rfl⟩ := hu
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by rw [← sq, hW2])
  rw [commAutU3_apply, map_mul, map_inv, hinv, hinv] at hzu
  have h1 : z (z v) = v := mul_right_cancel (hzu.trans (mul_comm _ _))
  have h3 : z (z (z v)) = v := by
    have := congrArg (fun f : MulAut W => f v) hz3
    simpa [pow_succ] using this
  have h2 : z v = v := by
    rw [h1] at h3
    exact h3
  rw [commAutU3_apply, h2, mul_inv_cancel]

theorem card_range_commAutU3 (hW2 : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)} {x y : ↥K}
    (hzc : ∀ g : ↥K, Commute g ⁅x, y⁆) (hexp : ∀ g : ↥K, g ^ 3 = 1) :
    ∃ k : ℕ, Nat.card ↥(commAutU3 ((⁅x, y⁆ : ↥K) : MulAut W)).range = 2 ^ (6 * k) := by
  let _ : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (n := 2) fun m => by
      show Additive.ofMul ((Additive.toMul m) ^ 2) = 0
      rw [hW2]
      rfl
  have : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  let ρ : Representation (ZMod 2) ↥K (Additive W) :=
    { toFun := fun g => ((MulEquiv.toAdditive (g : MulAut W)).toAddMonoidHom).toZModLinearMap 2
      map_one' := by
        ext m
        rfl
      map_mul' := fun g g' => by
        ext m
        rfl }
  have hρ : ∀ (g : ↥K) (m : Additive W),
      ρ g m = Additive.ofMul ((g : MulAut W) (Additive.toMul m)) := fun _ _ => rfl
  obtain ⟨k, hk⟩ := VolI.six_dvd_finrank_centralImage (ρ := ρ) hzc hexp
  refine ⟨k, ?_⟩
  have hcard : Nat.card ↥(CFSG.LinearAlgebra.centralImage ρ ⁅x, y⁆) = 2 ^ (6 * k) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hk]
  rw [← hcard]
  have hmem : ∀ u : W, u ∈ (commAutU3 ((⁅x, y⁆ : ↥K) : MulAut W)).range ↔
      Additive.ofMul u ∈ CFSG.LinearAlgebra.centralImage ρ ⁅x, y⁆ := by
    intro u
    constructor
    · rintro ⟨v, rfl⟩
      refine LinearMap.mem_range.2 ⟨Additive.ofMul v, ?_⟩
      rw [LinearMap.sub_apply, Module.End.one_apply, hρ, commAutU3_apply, ofMul_mul, ofMul_inv,
        ← sub_eq_add_neg]
      rfl
    · intro hm
      obtain ⟨n, hn⟩ := LinearMap.mem_range.1 hm
      refine ⟨Additive.toMul n, ?_⟩
      rw [LinearMap.sub_apply, Module.End.one_apply, hρ, sub_eq_add_neg] at hn
      rw [commAutU3_apply]
      apply Additive.ofMul.injective
      rw [ofMul_mul, ofMul_inv, ← hn]
      rfl
  exact Nat.card_congr
    { toFun := fun u => ⟨Additive.ofMul u.1, (hmem u.1).1 u.2⟩
      invFun := fun m => ⟨Additive.toMul m.1, (hmem _).2 m.2⟩
      left_inv := fun u => rfl
      right_inv := fun m => rfl }

end Module

theorem exists_commutator_center {X : Type*} [Group X] [Finite X] (hX : IsPOnePlusTwo 3 X) :
    ∃ x y : X, ⁅x, y⁆ ≠ 1 ∧ (∀ g : X, Commute g ⁅x, y⁆) ∧
      ∀ c : X, (∀ g : X, Commute g c) → c = 1 ∨ c = ⁅x, y⁆ ∨ c = ⁅x, y⁆⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hab⟩ := A1c.exists_not_commute_of_isPOnePlusTwo hX
  obtain ⟨hext, -, hexp⟩ := hX
  have hcomQ := (IsExtraspecial.quotient_elementary_abelian 3 X).toIsMulCommutative
  have hz : ⁅a, b⁆ ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center X) ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomQ.is_comm.comm _ _
  have hz1 : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hzo : orderOf ⁅a, b⁆ = 3 := orderOf_eq_prime (hexp _) hz1
  have hcen : Subgroup.center X = zpowers ⁅a, b⁆ := by
    refine (eq_of_le_of_card_ge (zpowers_le.2 hz) ?_).symm
    rw [IsExtraspecial.center_order_p 3 X, Nat.card_zpowers, hzo]
  refine ⟨a, b, hz1, fun g => (Subgroup.mem_center_iff.1 hz g), fun c hc => ?_⟩
  have hcc : c ∈ zpowers ⁅a, b⁆ := by
    rw [← hcen]
    exact Subgroup.mem_center_iff.2 fun g => (hc g).eq
  rw [mem_zpowers_iff_mem_range_orderOf, hzo, Finset.mem_image] at hcc
  obtain ⟨n, hn, rfl⟩ := hcc
  rw [Finset.mem_range] at hn
  interval_cases n
  · exact Or.inl (pow_zero _)
  · exact Or.inr (Or.inl (pow_one _))
  · refine Or.inr (Or.inr (eq_inv_of_mul_eq_one_left ?_))
    rw [← pow_succ]
    exact hexp _

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s1347_aut_structure (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂))
    (hcent : (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂))
    (hext : F6.IsExtensionWith (↥(H₁ ⊔ H₂) ⧸ Open.pCore 2 ↥(H₁ ⊔ H₂))
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) fun N => IsPOnePlusTwo 3 ↥N) :
    ∃ K : Subgroup (MulAut ↥(v0Of T H₁ H₂)), K ≤ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) ∧
      (∀ β ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂), ∀ κ ∈ K, β * κ * β⁻¹ ∈ K) ∧
      IsPOnePlusTwo 3 ↥K := by
  have hred := s1347_reduced S hH₀
  have hP : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G) := hred.2.1
  obtain ⟨φ, -, hker⟩ := hext
  have hle : Open.pCore 2 ↥(H₁ ⊔ H₂) ≤ (Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP).ker := by
    intro g hg
    rw [MonoidHom.mem_ker, Setup.rho_eq_one_iff]
    exact pCoreOf_le_centralizer_of_reduced' hred ⟨g, hg, rfl⟩
  set ρ' := QuotientGroup.lift (Open.pCore 2 ↥(H₁ ⊔ H₂))
    (Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP) hle with hρ'
  have hρ'mk : ∀ g : ↥(H₁ ⊔ H₂), ρ' (g : ↥(H₁ ⊔ H₂) ⧸ Open.pCore 2 ↥(H₁ ⊔ H₂)) =
      Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g := fun g => QuotientGroup.lift_mk _ hle g
  have hinj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro d hd
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective d
    rw [hρ'mk, Setup.rho_eq_one_iff] at hd
    have hg : (g : G) ∈ pCoreOf 2 (H₁ ⊔ H₂) := by
      rw [← hcent]
      exact ⟨g.2, hd⟩
    obtain ⟨g', hg', hgg'⟩ := hg
    have : g' = g := Subtype.ext hgg'
    rw [QuotientGroup.eq_one_iff, ← this]
    exact hg'
  have hmemX : ∀ d, ρ' d ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) := by
    intro d
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective d
    rw [hρ'mk]
    exact (Setup.mem_autOn_self_iff hP).2 ⟨g, rfl⟩
  refine ⟨φ.ker.map ρ', ?_, ?_, A36B.isPOnePlusTwo_of_mulEquiv
    (Subgroup.equivMapOfInjective φ.ker ρ' hinj) hker⟩
  · rintro _ ⟨d, -, rfl⟩
    exact hmemX d
  · intro β hβ κ hκ
    obtain ⟨g, rfl⟩ := (Setup.mem_autOn_self_iff hP).1 hβ
    obtain ⟨d, hd, rfl⟩ := hκ
    refine ⟨(g : ↥(H₁ ⊔ H₂) ⧸ Open.pCore 2 ↥(H₁ ⊔ H₂)) * d *
      (g : ↥(H₁ ⊔ H₂) ⧸ Open.pCore 2 ↥(H₁ ⊔ H₂))⁻¹, ?_, ?_⟩
    · exact (MonoidHom.normal_ker φ).conj_mem d hd _
    · rw [map_mul, map_mul, map_inv, hρ'mk]

theorem s1347_exists_z {W : Type*} [Group W] [Finite W] {X K : Subgroup (MulAut W)}
    (hKn : ∀ β ∈ X, ∀ κ ∈ K, β * κ * β⁻¹ ∈ K) (hK : IsPOnePlusTwo 3 ↥K) :
    ∃ x y : ↥K, ⁅x, y⁆ ≠ 1 ∧ (∀ g : ↥K, Commute g ⁅x, y⁆) ∧ (∀ g : ↥K, g ^ 3 = 1) ∧
      ∀ β ∈ X, β * ((⁅x, y⁆ : ↥K) : MulAut W) * β⁻¹ = ((⁅x, y⁆ : ↥K) : MulAut W) ∨
        β * ((⁅x, y⁆ : ↥K) : MulAut W) * β⁻¹ = ((⁅x, y⁆ : ↥K) : MulAut W)⁻¹ := by
  obtain ⟨x, y, hz1, hzc, hcen⟩ := exists_commutator_center hK
  refine ⟨x, y, hz1, hzc, hK.2.2, fun β hβ => ?_⟩
  set z : ↥K := ⁅x, y⁆ with hz
  set c : ↥K := ⟨β * (z : MulAut W) * β⁻¹, hKn β hβ _ z.2⟩ with hc
  have hcc : ∀ g : ↥K, Commute g c := by
    intro g
    have hg' : β⁻¹ * (g : MulAut W) * β ∈ K := by
      have := hKn β⁻¹ (inv_mem hβ) _ g.2
      rwa [inv_inv] at this
    have h1 : (z : MulAut W) * (β⁻¹ * g * β) = (β⁻¹ * g * β) * z :=
      congrArg Subtype.val (hzc ⟨_, hg'⟩).eq.symm
    apply Subtype.ext
    show (g : MulAut W) * (β * z * β⁻¹) = β * z * β⁻¹ * g
    calc (g : MulAut W) * (β * z * β⁻¹) = β * ((β⁻¹ * g * β) * z) * β⁻¹ := by group
      _ = β * (z * (β⁻¹ * g * β)) * β⁻¹ := by rw [h1]
      _ = β * z * β⁻¹ * g := by group
  rcases hcen c hcc with h1 | h1 | h1
  · exfalso
    apply hz1
    have h2 : β * (z : MulAut W) * β⁻¹ = 1 := congrArg Subtype.val h1
    have h3 : (z : MulAut W) = 1 := by
      calc (z : MulAut W) = β⁻¹ * (β * z * β⁻¹) * β := by group
        _ = 1 := by rw [h2]; group
    exact Subtype.ext h3
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

end CFSG.Quasithin.H13.U3
