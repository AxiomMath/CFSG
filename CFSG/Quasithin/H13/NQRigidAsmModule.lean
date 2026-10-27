module

public import CFSG.Quasithin.H13.NQSetupDeletedFive
public import CFSG.Quasithin.H13.NQSetupDeletedWeightTwo
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.NQRigidModule
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open Equiv
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open scoped IsMulCommutative

theorem isElementaryAbelian_congr {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [hA : CFSG.IsElementaryAbelian p A] : CFSG.IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e inferInstance

theorem exists_klein_of_weight_ne_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 5) (v : Ω → ZMod 2) (hv : ∑ ω, v ω = 0)
    (hw : (Finset.univ.filter fun ω => v ω ≠ 0).card ≠ 2) :
    ∃ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω ∧
      (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) ∧
      CFSG.IsElementaryAbelian 2 K ∧ Nat.card K = 4 := by
  classical
  let e₁ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hΩ
  obtain ⟨σ, hσ⟩ := SteinbergCB.exists_perm_evenWeight_five (fun i => v (e₁.symm i))
    (by rw [Equiv.sum_comp e₁.symm v]; exact hv)
  let e : Fin 5 ≃ Ω := σ.trans e₁.symm
  have hklein : ∀ v₀ : Fin 5 → ZMod 2,
      (∀ p i, v₀ ((SteinbergCB.kleinFiveFun p)⁻¹ i) = v₀ i) → (∀ i, v (e i) = v₀ i) →
      ∃ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω ∧
        (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) ∧
        CFSG.IsElementaryAbelian 2 K ∧ Nat.card K = 4 := by
    intro v₀ hfix hve
    set f := (permCongrHom e).toMonoidHom.comp SteinbergCB.kleinFiveHom with hf
    obtain ⟨h1, h2⟩ := SteinbergCB.range_permCongrHom_comp_fix e SteinbergCB.kleinFiveHom
      SteinbergCB.sign_kleinFiveFun hfix hve
    have hinj : Function.Injective f :=
      (permCongrHom e).injective.comp SteinbergCB.kleinFiveFun_injective
    have hEA : CFSG.IsElementaryAbelian 2 f.range :=
      { is_comm := ⟨fun a b => by
          obtain ⟨p, hp⟩ := a.2
          obtain ⟨q, hq⟩ := b.2
          apply Subtype.ext
          change (a : Perm Ω) * b = b * a
          rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm]⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
          obtain ⟨p, hp⟩ := a.2
          apply Subtype.ext
          rw [Subgroup.coe_pow, ← hp, ← map_pow, SteinbergCB.klein_pow_two, map_one]
          rfl }
    refine ⟨f.range, h1, h2, hEA, ?_⟩
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
    rfl
  rcases hσ with h0 | h4 | h2
  · exact hklein 0 (fun _ _ => rfl) h0
  · exact hklein SteinbergCB.fourVecFive SteinbergCB.kleinFiveFun_fix h4
  · exfalso
    apply hw
    have hcard : Fintype.card {i : Fin 5 // SteinbergCB.twoVecFive i ≠ 0} = 2 := by decide
    have h1 : (Finset.univ.filter fun ω => v ω ≠ 0).card =
        Fintype.card {i : Fin 5 // v (e i) ≠ 0} := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr (e.subtypeEquiv (fun i => Iff.rfl)).symm
    have h3 : Fintype.card {i : Fin 5 // v (e i) ≠ 0} =
        Fintype.card {i : Fin 5 // SteinbergCB.twoVecFive i ≠ 0} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
        rw [show v (e i) = SteinbergCB.twoVecFive i from h2 i])
    rw [h1, h3, hcard]

section QTNQ

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem exists_four_of_deleted_weight_ne_two (h : QTNQ T L M) {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
    (θ : Additive (qtnqU L M) ≃+ evenWeight Ω)
    (hθ : ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
      (θ (Additive.ofMul y) : Ω → ZMod 2) =
        permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x)))
    {u : G} (hu : u ∈ qtnqU L M)
    (hw : (Finset.univ.filter fun ω =>
      (θ (Additive.ofMul ⟨u, hu⟩) : Ω → ZMod 2) ω ≠ 0).card ≠ 2) :
    ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4 := by
  classical
  set θ' : qtnqU L M → Ω → ZMod 2 := fun x => (θ (Additive.ofMul x) : Ω → ZMod 2) with hθ'
  have hθi : Function.Injective θ' := fun x y hxy =>
    Additive.ofMul.injective (θ.injective (Subtype.ext hxy))
  have hmap := NQSetup.map_centralizer_eq_comap_altStab h β θ' hθi hθ hu
  set w := θ' ⟨u, hu⟩ with hw'
  have hwsum : ∑ ω, w ω = 0 := (θ (Additive.ofMul ⟨u, hu⟩)).2
  obtain ⟨K, hKA, hKv, hKel, hK4⟩ := exists_klein_of_weight_ne_two hΩ w hwsum hw
  set K' : Subgroup (alternatingGroup Ω) := K.subgroupOf (alternatingGroup Ω) with hK'
  have hK'stab : K' ≤ NQSetup.altStab w := by
    intro g hg
    rw [NQSetup.mem_altStab_iff]
    have h1 := hKv (g : Perm Ω) hg
    funext i
    have h2 := congrFun h1 i
    simp only [LinearMap.funLeft_apply] at h2
    exact h2
  have eK : K' ≃* K := subgroupOfEquivOfLe hKA
  set B : Subgroup (L ⧸ CFSG.solvableRadical L) := K'.map β.symm.toMonoidHom with hB
  have eB : K' ≃* B := K'.equivMapOfInjective β.symm.toMonoidHom β.symm.injective
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [hmap]
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact hK'stab hk
  · exact isElementaryAbelian_congr (eK.symm.trans eB)
  · rw [← Nat.card_congr (eK.symm.trans eB).toEquiv, hK4]

theorem noncyclic_or_deleted_weight_two (h : QTNQ T L M) (hmod : QTNQExplicitModule L M)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {v : G} (hv : v ∈ qtnqU L M)
    (hQ : IsSylowOf 2 (T ⊓ centralizer {v}) (M ⊓ centralizer {v})) :
    ¬ IsCyclic (((T ⊓ centralizer {v}).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X)) ∨
      ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω), Fintype.card Ω = 5 ∧
        ∃ (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
          (θ : Additive (qtnqU L M) ≃+ evenWeight Ω),
          (∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
            (θ (Additive.ofMul y) : Ω → ZMod 2) =
              permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x))) ∧
          (Finset.univ.filter fun ω =>
            (θ (Additive.ofMul ⟨v, hv⟩) : Ω → ZMod 2) ω ≠ 0).card = 2 := by
  classical
  have hnc := fun halt =>
    (NQSetup.natural_module_centralizer_Sylow_action_on_original_prime_plane_is_noncyclic h hp
      hp5 hXL hXc hXA hW hLW hv hQ halt).2
  rcases hmod with ha | ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ⟩ | hc1 | hc2
  · exact Or.inl (hnc (Or.inl ha))
  · by_cases hw : (Finset.univ.filter fun ω =>
      (θ (Additive.ofMul ⟨v, hv⟩) : Ω → ZMod 2) ω ≠ 0).card = 2
    · exact Or.inr ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ, hw⟩
    · left
      obtain ⟨B, hBC, hBel, hB4⟩ := exists_four_of_deleted_weight_ne_two h hΩ β θ hθ hv hw
      exact hnc (Or.inr (Or.inr (Or.inr ⟨B, hBC, hBel, hB4⟩)))
  · exact Or.inl (hnc (Or.inr (Or.inl hc1)))
  · exact Or.inl (hnc (Or.inr (Or.inr (Or.inl hc2))))

theorem image_ne_bot_of_module (h : QTNQ T L M) (hmod : QTNQExplicitModule L M)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {v : G} (hv : v ∈ qtnqU L M)
    (hQ : IsSylowOf 2 (T ⊓ centralizer {v}) (M ⊓ centralizer {v})) :
    ((T ⊓ centralizer {v}).subgroupOf (normalizer (X : Set G))).map
      (normalizerFrattiniConj X) ≠ ⊥ := by
  classical
  rcases hmod with ha | ⟨Ω, hΩf, hΩd, hΩ, β, θ, hθ⟩ | hc1 | hc2
  · intro hbot
    apply (NQSetup.natural_module_centralizer_Sylow_action_on_original_prime_plane_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hv hQ (Or.inl ha)).2
    rw [hbot]
    exact isCyclic_of_subsingleton
  · exact (NQSetup.deleted_five_point_centralizer_Sylow_action_on_original_prime_plane_is_nontrivial
      h hΩ β θ hθ hp hp5 hXL hXc hXA hW hLW hv hQ).2
  · intro hbot
    apply (NQSetup.natural_module_centralizer_Sylow_action_on_original_prime_plane_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hv hQ (Or.inr (Or.inl hc1))).2
    rw [hbot]
    exact isCyclic_of_subsingleton
  · intro hbot
    apply (NQSetup.natural_module_centralizer_Sylow_action_on_original_prime_plane_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hv hQ (Or.inr (Or.inr (Or.inl hc2)))).2
    rw [hbot]
    exact isCyclic_of_subsingleton

theorem exists_nonscalar_of_deleted_weight_two (h : QTNQ T L M)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
    (θ : Additive (qtnqU L M) ≃+ evenWeight Ω)
    (hθ : ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
      (θ (Additive.ofMul y) : Ω → ZMod 2) =
        permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x)))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {u : G} (hu : u ∈ qtnqU L M)
    (hu2 : (Finset.univ.filter fun ω =>
      (θ (Additive.ofMul ⟨u, hu⟩) : Ω → ZMod 2) ω ≠ 0).card = 2)
    (hQ : IsSylowOf 2 (T ⊓ centralizer {u}) (M ⊓ centralizer {u})) :
    ∃ γ ∈ ((T ⊓ centralizer {u}).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X), ¬ ∃ c : ZMod p, ∀ w, γ w = w ^ c.val := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hcyc, hcard, -⟩ :=
    NQSetup.deleted_weight_two_centralizer_has_original_cyclic_four_Sylow_image
      h hΩ β θ hθ hp hp5 hXL hXc hXA hW hLW hu hu2 hQ
  set I₀ := ((T ⊓ centralizer {u} ⊓ L).subgroupOf (normalizer (X : Set G))).map
    (normalizerFrattiniConj X) with hI₀
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgord : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  obtain ⟨n, hn, hng⟩ := g.2
  have hnT : ((n : normalizer (X : Set G)) : G) ∈ T ⊓ centralizer {u} := by
    have := mem_subgroupOf.mp hn
    exact ⟨this.1.1, this.1.2⟩
  have hnL : ((n : normalizer (X : Set G)) : G) ∈ L := (mem_subgroupOf.mp hn).2
  refine ⟨g, ⟨n, mem_subgroupOf.mpr hnT, hng⟩, ?_⟩
  rintro ⟨c, hc⟩
  have hLN : L ≤ normalizer (X : Set G) := by
    refine le_normalizer.trans ?_
    exact NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXA⟩
  have : CFSG.IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    CFSG.isElementaryAbelian_quotient_frattini
  set W := (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) with hWdef
  set α : L →* (Additive W ≃ₗ[ZMod p] Additive W) :=
    (NQSetup.mulAutLinear p W).comp ((normalizerFrattiniConj X).comp (inclusion hLN)) with hα
  have hα1 : α ≠ 1 := by
    obtain ⟨l, hl, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 := DFunLike.congr_fun h1 ⟨l, hl⟩
    have h3 : inclusion hLN ⟨(l : G), hl⟩ = l := Subtype.ext rfl
    apply NQSetup.mulAutLinear_injective p W
    rw [map_one]
    have h4 : α ⟨(l : G), hl⟩ = NQSetup.mulAutLinear p W (normalizerFrattiniConj X l) := by
      rw [hα, MonoidHom.comp_apply, MonoidHom.comp_apply, h3]
    rw [← h4, h2]
    rfl
  have hfin := NQSetup.finrank_additive_eq_two hW
  obtain ⟨-, -, -, hcen⟩ :=
    NQSetup.ccomponent_plane_radical hp2 (NQSetup.isCComponent_top_of_qtnq h) hfin α hα1
  set l₀ : L := ⟨(n : G), hnL⟩ with hl₀
  have hincl : inclusion hLN l₀ = n := Subtype.ext rfl
  have hαl₀ : ∀ x : Additive W, α l₀ x = c • x := by
    intro x
    rw [hα, MonoidHom.comp_apply, MonoidHom.comp_apply, hincl, NQSetup.mulAutLinear_apply, hng,
      hc, ofMul_pow, ofMul_toMul]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  have hcomm : ∀ l' : L, α l₀ * α l' = α l' * α l₀ := by
    intro l'
    apply LinearEquiv.ext
    intro x
    change α l₀ (α l' x) = α l' (α l₀ x)
    rw [hαl₀, hαl₀, map_smul]
  have hsq : (g : MulAut W) ^ 2 = 1 := by
    have h1 : α l₀ ^ 2 = 1 := by
      rcases hcen l₀ hcomm with h1 | h1
      · rw [h1, one_pow]
      · rw [h1, sq]
        apply LinearEquiv.ext
        intro x
        change LinearEquiv.neg (ZMod p) (LinearEquiv.neg (ZMod p) x) = x
        rw [LinearEquiv.neg_apply, LinearEquiv.neg_apply]
        exact neg_neg x
    have h2 : α l₀ = NQSetup.mulAutLinear p W (g : MulAut W) := by
      rw [hα, MonoidHom.comp_apply, MonoidHom.comp_apply, hincl, hng]
    apply NQSetup.mulAutLinear_injective p W
    rw [map_pow, ← h2, h1, map_one]
  have h3 := orderOf_dvd_of_pow_eq_one hsq
  rw [Subgroup.orderOf_coe, hgord] at h3
  norm_num at h3

end QTNQ

end CFSG.Quasithin.H13.NQRigid
