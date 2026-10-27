module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.CentralLift.DefiningTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.CentralLift (mem_normalizer_of_conj_mem)
open scoped commutatorElement

@[expose] def oThreePrime (H : Type*) [Group H] : Subgroup H :=
  Subgroup.closure {g | ∃ k : ℕ, g ^ 3 ^ k = 1}

structure Inputs49 : Prop where
  oddOThreePrime : ∀ (X : Type) [Group X] [Finite X], IsList46 X → CFSG.IsQuasisimple X →
    Odd (Nat.card (oThreePrime (Outer X)))

variable {G : Type} [Group G] [Finite G]

theorem mem_oThreePrime_of_pow {H : Type*} [Group H] {g : H} {k : ℕ} (hg : g ^ 3 ^ k = 1) :
    g ∈ oThreePrime H :=
  Subgroup.subset_closure ⟨k, hg⟩

theorem commutator_mem_normalizer {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) {x : G}
    (hx : ∀ K ∈ thetaComponents 3 G, x ∈ Subgroup.normalizer (K : Set G)) (u : G) :
    ⁅x, u⁆ ∈ Subgroup.normalizer (L : Set G) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hK : L.map (MulAut.conj u⁻¹).toMonoidHom ∈ thetaComponents 3 G :=
    map_mulEquiv_mem_thetaComponents hp3 (MulAut.conj u⁻¹) hL
  have hxK := hx _ hK
  have hxL := hx L hL
  have hxK' : x⁻¹ ∈ Subgroup.normalizer
      ((L.map (MulAut.conj u⁻¹).toMonoidHom : Subgroup G) : Set G) := Subgroup.inv_mem _ hxK
  apply mem_normalizer_of_conj_mem
  intro l hl
  have hm : u⁻¹ * l * u ∈ L.map (MulAut.conj u⁻¹).toMonoidHom :=
    ⟨l, hl, by simp⟩
  have hm' := (Subgroup.mem_normalizer_iff.mp hxK' (u⁻¹ * l * u)).mp hm
  obtain ⟨l', hl', hl'eq⟩ := hm'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hl'eq
  have h1 : u * x⁻¹ * u⁻¹ * l * u * x * u⁻¹ = l' := by
    have : x⁻¹ * (u⁻¹ * l * u) * x⁻¹⁻¹ = u⁻¹ * l' * u := by rw [inv_inv]; exact hl'eq.symm
    calc u * x⁻¹ * u⁻¹ * l * u * x * u⁻¹ = u * (x⁻¹ * (u⁻¹ * l * u) * x⁻¹⁻¹) * u⁻¹ := by group
      _ = u * (u⁻¹ * l' * u) * u⁻¹ := by rw [this]
      _ = l' := by group
  have h2 : x * l' * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL l').mp hl'
  have : ⁅x, u⁆ * l * ⁅x, u⁆⁻¹ = x * l' * x⁻¹ := by
    rw [commutatorElement_def, ← h1]
    group
  rw [this]
  exact h2

theorem rank3II_4_9_of (h46 : Item4_6) (hin : Inputs49) : Item4_9 := by
  intro G _ _ hG h3 L hL X hX3 hX U hU hXU
  have hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  have hlist := h46 G hG h3 L hL
  have hodd := hin.oddOThreePrime _ hlist hq
  set N := Subgroup.normalizer (L : Set G) with hN
  have hXN : ∀ x ∈ X, ∀ K ∈ thetaComponents 3 G, x ∈ Subgroup.normalizer (K : Set G) :=
    fun x hx K hK => hX K hK hx
  have hUN : U ≤ N := by
    rw [← hXU, Subgroup.commutator_le]
    intro x hx u _
    exact commutator_mem_normalizer hL (hXN x hx) u
  set φ : N →* Outer (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (L ⧸ aschbacherSolvableCore 3 L))).comp
      ((thetaQuotMulAut L).comp (compAction L)) with hφ
  set O := oThreePrime (Outer (L ⧸ aschbacherSolvableCore 3 L))
  have hUO : U ≤ (O.comap φ).map N.subtype := by
    rw [← hXU, Subgroup.commutator_le]
    intro x hx u hu
    have hxN : x ∈ N := hX L hL hx
    have huN : u ∈ N := hUN hu
    refine ⟨⁅(⟨x, hxN⟩ : N), ⟨u, huN⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX3) ⟨x, hx⟩
    have hx3 : φ ⟨x, hxN⟩ ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hxN⟩ : N) ^ 3 ^ k = 1 := by
        apply Subtype.ext
        have h := congrArg Subtype.val (pow_orderOf_eq_one (⟨x, hx⟩ : X))
        rw [hk] at h
        simpa using h
      rw [this, map_one]
    set a := φ ⟨x, hxN⟩
    set b := φ ⟨u, huN⟩
    have hconj : (b * a⁻¹ * b⁻¹) ^ 3 ^ k = 1 := by
      rw [conj_pow, inv_pow, hx3, inv_one, mul_one, mul_inv_cancel]
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact Subgroup.mul_mem _ (mem_oThreePrime_of_pow hx3) (mem_oThreePrime_of_pow hconj)
  intro u hu
  obtain ⟨⟨u', hu'N⟩, hmem₀, rfl⟩ := hUO hu
  have hmem : φ ⟨u', hu'N⟩ ∈ O := Subgroup.mem_comap.mp hmem₀
  have hcop : Nat.Coprime (Nat.card O) (Nat.card U) := by
    apply Nat.coprime_of_dvd
    intro p hp hpO hpU
    have h2 : p = 2 := hU.2.1 ⟨p, hp⟩ hpU
    subst h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpO)
  have hord : orderOf (⟨φ ⟨u', hu'N⟩, hmem⟩ : O) = 1 := by
    apply Nat.eq_one_of_dvd_one
    rw [← hcop.gcd_eq_one]
    refine Nat.dvd_gcd (orderOf_dvd_natCard _) ?_
    rw [Subgroup.orderOf_mk]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
    have hu' : u' ∈ U := hu
    have h1 : orderOf (⟨u', hu'⟩ : U) ∣ Nat.card U := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at h1
  have h1 : φ ⟨u', hu'N⟩ = 1 := by
    have := orderOf_eq_one_iff.mp hord
    exact congrArg Subtype.val this
  have hinn : thetaQuotMulAut L (compAction L ⟨u', hu'N⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨z, hz⟩ := hinn
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective z
  have hℓN : ((ℓ : L) : G)⁻¹ ∈ N := Subgroup.inv_mem _ (Subgroup.le_normalizer ℓ.2)
  have hcN : u' * ((ℓ : L) : G)⁻¹ ∈ N := Subgroup.mul_mem _ hu'N hℓN
  have hcC : u' * ((ℓ : L) : G)⁻¹ ∈ thetaQuotCentralizer L := by
    refine ⟨⟨u' * ((ℓ : L) : G)⁻¹, hcN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hsplit : (⟨u' * ((ℓ : L) : G)⁻¹, hcN⟩ : N) = ⟨u', hu'N⟩ * ⟨((ℓ : L) : G)⁻¹, hℓN⟩ := rfl
    change thetaQuotMulAut L (compAction L ⟨u' * ((ℓ : L) : G)⁻¹, hcN⟩) = 1
    rw [hsplit, map_mul, map_mul, ← hz,
      thetaQuotMulAut_compAction_of_mem (Subgroup.inv_mem _ ℓ.2) hℓN]
    have hinvℓ : QuotientGroup.mk' (aschbacherSolvableCore 3 L)
        ⟨((ℓ : L) : G)⁻¹, Subgroup.inv_mem _ ℓ.2⟩ =
        (QuotientGroup.mk ℓ : L ⧸ aschbacherSolvableCore 3 L)⁻¹ := by
      rw [show (⟨((ℓ : L) : G)⁻¹, Subgroup.inv_mem _ ℓ.2⟩ : L) = ℓ⁻¹ from rfl, map_inv]
      rfl
    rw [hinvℓ, map_inv, mul_inv_cancel]
  have heq : u' = (u' * ((ℓ : L) : G)⁻¹) * ((ℓ : L) : G) := by group
  change u' ∈ L ⊔ thetaQuotCentralizer L
  rw [heq, sup_comm]
  exact Subgroup.mul_mem_sup hcC ℓ.2

end CFSG.RankThree.PartTwo.Sec4
