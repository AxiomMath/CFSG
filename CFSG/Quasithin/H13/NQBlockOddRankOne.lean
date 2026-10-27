module

public import CFSG.Quasithin.H13.NQBlockOddRankOneBridge
public import CFSG.Quasithin.H13.NQTermCatalogThreeFree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open scoped MatrixGroups Pointwise LinearAlgebra.Projectivization
open CFSG.QuasithinUnique.Setup.Family (CQ)
open CFSG.QuasithinUnique.Setup.SL2Modules (repOfSubgroup EndRing epsHom epsHom_injective
  epsHom_commutes mem_endRing_iff central_quotient_SL2_quadratic_offender_alternatives)

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem card_commutant_eq_card_endRing (L : Subgroup (Module.End (ZMod 2) W)ˣ) :
    Nat.card {φ : Module.End (ZMod 2) W // ∀ (l : L) (w : W), φ (l.1.val w) = l.1.val (φ w)} =
      Nat.card (EndRing (repOfSubgroup L)) := by
  refine (Nat.card_congr (Equiv.ofBijective (fun ψ : EndRing (repOfSubgroup L) =>
    (⟨epsHom _ ψ, fun l w => epsHom_commutes _ ψ l w⟩ :
      {φ : Module.End (ZMod 2) W // ∀ (l : L) (w : W), φ (l.1.val w) = l.1.val (φ w)}))
    ⟨fun ψ₁ ψ₂ h => epsHom_injective _ (congrArg Subtype.val h), ?_⟩)).symm
  rintro ⟨φ, hφ⟩
  obtain ⟨ψ, hψ⟩ := (mem_endRing_iff (repOfSubgroup L) φ).mpr hφ
  exact ⟨ψ, Subtype.ext (LinearMap.ext fun w => congrFun hψ w)⟩

theorem not_le_sylow_two_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (D : Subgroup G) (hD : Nat.card D = p) (T : Sylow 2 G) :
    ¬ D ≤ T ∧ ¬ 3 ∣ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (T.isPGroup'.to_le h)
    rw [hD] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    have h2p : 2 ∣ p := hk ▸ dvd_pow_self 2 hk0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p
    omega
  · rw [hD] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega

open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj) in
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic) in
theorem exists_mulEquiv_sl2_of_even_model {S : Type} [Group S] {f : ℕ}
    (hm : StatedClassicalModel S .PSL 2 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ^ f ∧
      Nonempty (S ≃* SL(2, K)) := by
  obtain ⟨⟨-, hf1, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  refine ⟨K, hKf, inferInstance, by rw [← Nat.card_eq_fintype_card, hK], ⟨?_⟩⟩
  exact e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      2 K).trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K)))

theorem odd_rank_one_catalog_quadratic_offender_forces_even_linear_natural_module
    [Finite W]
    [Nontrivial W] (L : Subgroup (Module.End (ZMod 2) W)ˣ) (hLq : CFSG.IsQuasisimple L)
    (hirr : (repOfSubgroup L).IsIrreducible) (hcat : CFSG.Blueprint.Catalog (L ⧸ center L))
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (L ⧸ center L) ≤ 1)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (D : Subgroup (L ⧸ center L)) (hD : Nat.card D = p)
    (T : Sylow 2 (L ⧸ center L))
    (hDT : (D : Set (L ⧸ center L)) * (T : Set (L ⧸ center L)) =
      (T : Set (L ⧸ center L)) * (D : Set (L ⧸ center L)))
    (B : Subgroup (Module.End (ZMod 2) W)ˣ) (hBe : CFSG.IsElementaryAbelian 2 B) (hB1 : B ≠ ⊥)
    (hBN : B ≤ normalizer (L : Set (Module.End (ZMod 2) W)ˣ))
    (hquad : ∀ a ∈ B, ∀ b ∈ B, ∀ w : W, (b.val - 1) ((a.val - 1) w) = 0)
    (hoff : Nat.card W ≤ Nat.card B * Nat.card {w : W // ∀ b ∈ B, b.val w = w}) :
    center L = ⊥ ∧ ∃ f : ℕ, 3 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
      Fintype.card F = 2 ^ f ∧ ∃ θ : L ≃* SL(2, F), ∃ β : W ≃+ (Fin 2 → F),
        (∀ (l : L) (w : W), β (l.1.val w) = (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (β w)) ∧
        B ≤ L ∧
        (∃ ℓ : Submodule F (Fin 2 → F), Module.finrank F ℓ = 1 ∧
          (∀ g : SL(2, F), g ∈ (B.subgroupOf L).map θ.toMonoidHom ↔
            ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
              ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)) ∧
          ∀ w : W, (∀ b ∈ B, b.val w = w) ↔ β w ∈ ℓ) ∧
        Nat.card B = 2 ^ f ∧
        Nat.card {φ : Module.End (ZMod 2) W //
          ∀ (l : L) (w : W), φ (l.1.val w) = l.1.val (φ w)} = 2 ^ f ∧
        Nat.card B * Nat.card {w : W // ∀ b ∈ B, b.val w = w} = Nat.card W ∧
        ∃ θbar : (L ⧸ center L) ≃* SL(2, F), (∀ l : L, θbar (QuotientGroup.mk l) = θ l) ∧
          D.map θbar.toMonoidHom ≤
            normalizer (((T : Subgroup (L ⧸ center L)).map θbar.toMonoidHom :
              Subgroup SL(2, F)) : Set SL(2, F)) ∧
          p ∣ 2 ^ f - 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have := hBe
  have : Finite (Module.End (ZMod 2) W)ˣ :=
    Finite.of_injective (fun u : (Module.End (ZMod 2) W)ˣ => (u.val : W → W))
      fun a b h => Units.ext (LinearMap.ext (congrFun h))
  obtain ⟨hperf, hsimp, hnab⟩ := hLq
  have hquad' : ∀ a ∈ B, ∀ b ∈ B, ∀ w, b.val (a.val w - w) = a.val w - w := by
    intro a ha b hb w
    have h := hquad a ha b hb w
    simp only [LinearMap.sub_apply, Module.End.one_apply] at h
    exact sub_eq_zero.mp h
  obtain ⟨hDT', hD3⟩ := not_le_sylow_two_of_card hp hp5 D hD T
  rcases CFSG.Quasithin.H13.NQTerm.odd_rank_one_catalog_three_free_sylow_product_model_restriction
    (L ⧸ center L) hnab hcat hodd T D hD3 hDT hDT' with h | h | h | h
  ·
    obtain ⟨f, hf3, hm⟩ := h
    obtain ⟨K, hKf, hKfin, hKcard, ⟨α⟩⟩ := exists_mulEquiv_sl2_of_even_model hm
    let : Fintype (ℙ K (Fin 2 → K)) := Fintype.ofFinite _
    obtain ⟨hZ, θ, hθ, halt, heq⟩ := central_quotient_SL2_quadratic_offender_alternatives
      (n := f) (by omega) hKcard L hirr hperf α B hB1 hBN hquad' hoff
    rcases halt with ⟨hBL, -, β, hβ, ℓ, hℓ1, hroot, hEnd, hBcard, hfix⟩ | ⟨-, hf2, -⟩
    swap
    · omega
    have : IsSimpleGroup SL(2, K) := α.symm.isSimpleGroup
    have hαs : Function.Surjective α.toMonoidHom := fun y => ⟨α.symm y, by simp⟩
    have hDT2 : ((D.map α.toMonoidHom : Subgroup SL(2, K)) : Set SL(2, K)) *
        (((T.mapSurjective hαs : Sylow 2 SL(2, K)) : Subgroup SL(2, K)) : Set SL(2, K)) =
        (((T.mapSurjective hαs : Sylow 2 SL(2, K)) : Subgroup SL(2, K)) : Set SL(2, K)) *
          ((D.map α.toMonoidHom : Subgroup SL(2, K)) : Set SL(2, K)) := by
      have hDT0 : (D : Set (L ⧸ center L)) * ((T : Subgroup (L ⧸ center L)) : Set (L ⧸ center L)) =
          ((T : Subgroup (L ⧸ center L)) : Set (L ⧸ center L)) * (D : Set (L ⧸ center L)) := hDT
      rw [Sylow.coe_mapSurjective, coe_map, coe_map, ← Set.image_mul, hDT0, Set.image_mul]
    obtain ⟨hDN, hpf⟩ := sl2_le_normalizer_of_mul_comm hf3 hKcard hp (by omega)
      (D.map α.toMonoidHom) (by rw [card_map_of_injective (f := α.toMonoidHom) α.injective, hD])
      (T.mapSurjective hαs) hDT2
    rw [Sylow.coe_mapSurjective] at hDN
    refine ⟨hZ, f, hf3, K, hKf, hKfin, hKcard, θ, β, hβ, hBL, ⟨ℓ, hℓ1, hroot, hfix⟩, hBcard, ?_,
      heq, α, fun l => (hθ l).symm, hDN, hpf⟩
    rw [card_commutant_eq_card_endRing]
    exact hEnd
  ·
    obtain ⟨ℓ, hℓ, hℓ11, hm⟩ := h
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨α⟩ := CFSG.QuasithinUnique.Setup.Family.equiv_projectiveSL_of_model hm
    exact absurd hoff (not_le.mpr (offender_lt_of_projectiveSL hℓ11 L B hirr hperf α hBe hB1 hBN))
  ·
    obtain ⟨a, ha, -, a', ha', K, hKf, hKfin, hfa, hK, ⟨α⟩⟩ := h
    rw [hfa] at hK
    exact absurd hoff (not_le.mpr (offender_lt_of_suzuki a' ha' hK L B hirr hperf α hBe hB1 hBN))
  ·
    obtain ⟨α⟩ := h
    exact absurd hoff (not_le.mpr (offender_lt_of_J1 L B hirr hperf α hBe hB1 hBN))

end CFSG.Quasithin.H13.NQBlock
