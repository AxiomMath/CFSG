module

public import CFSG.Quasithin.H13.NQSetupNaturalModule
public import CFSG.Quasithin.H13.NQSetupDeletedModule
public import CFSG.Quasithin.H13.NQRigidWitness
public import CFSG.Quasithin.H13.NQSetupPrimePlane

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open Equiv
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.H13.NQSetup (QTNQNaturalFour QTNQNaturalThreeDouble
  QTNQNaturalThreeExtension)
open scoped IsMulCommutative

section Alternatives

variable {G : Type} [Group G]

@[expose] def QTNQDeletedFive (L M : Subgroup G) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω), Fintype.card Ω = 5 ∧
    ∃ (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
      (θ : Additive (qtnqU L M) ≃+ evenWeight Ω),
      ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
        (θ (Additive.ofMul y) : Ω → ZMod 2) =
          permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x))

@[expose] def QTNQExplicitModule (L M : Subgroup G) : Prop :=
  QTNQNaturalFour L M ∨ QTNQDeletedFive L M ∨ QTNQNaturalThreeDouble L M ∨
    QTNQNaturalThreeExtension L M

end Alternatives

section Stabilizers

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem exists_noncyclic_of_qtnqDeletedFive (h : QTNQ T L M) {u : G} (hu : u ∈ qtnqU L M)
    (hb : QTNQDeletedFive L M) :
    ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      ¬ IsCyclic B ∧ ∀ r : ℕ, r.Prime → r ∣ Nat.card B → r = 2 ∨ r = 3 := by
  classical
  obtain ⟨Ω, _, _, hΩ, β, θ, hθ⟩ := hb
  set θ' : qtnqU L M → Ω → ZMod 2 := fun x => (θ (Additive.ofMul x) : Ω → ZMod 2) with hθ'
  have hθi : Function.Injective θ' := fun x y hxy =>
    Additive.ofMul.injective (θ.injective (Subtype.ext hxy))
  have hmap := NQSetup.map_centralizer_eq_comap_altStab h β θ' hθi hθ hu
  set v := θ' ⟨u, hu⟩ with hv
  have hvsum : ∑ ω, v ω = 0 := (θ (Additive.ofMul ⟨u, hu⟩)).2
  obtain ⟨-, K, hKA, hKv, hKnc, hKpr⟩ :=
    SteinbergCB.nq_alternating_five_deleted_module_stabilizers hΩ v hvsum
  set K' : Subgroup (alternatingGroup Ω) := K.subgroupOf (alternatingGroup Ω) with hK'
  have hK'stab : K' ≤ NQSetup.altStab v := by
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
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hK'stab hk
  · intro hcyc
    exact hKnc (isCyclic_of_surjective (eB.symm.trans eK).toMonoidHom
      (eB.symm.trans eK).surjective)
  · intro r hr hrB
    apply hKpr r hr
    rwa [← Nat.card_congr (eB.symm.trans eK).toEquiv]

theorem exists_noncyclic_coprime_of_explicitModule (h : QTNQ T L M)
    (hmod : QTNQExplicitModule L M) {u : G} (hu : u ∈ qtnqU L M) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      ¬ IsCyclic B ∧ Nat.Coprime (Nat.card B) p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfour : ∀ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      CFSG.IsElementaryAbelian 2 B → Nat.card B = 4 →
        ¬ IsCyclic B ∧ Nat.Coprime (Nat.card B) p := by
    intro B hBel hB4
    refine ⟨?_, ?_⟩
    · have := hBel
      exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (by rw [hB4]; norm_num)
    · rw [hB4, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by decide)
      omega
  rcases hmod with ha | hb | hc1 | hc2
  · obtain ⟨B, hBH, hBel, hB4⟩ := NQSetup.exists_four_of_qtnqNaturalFour h hu ha
    exact ⟨B, hBH, hfour B hBel hB4⟩
  · obtain ⟨B, hBH, hBnc, hBpr⟩ := exists_noncyclic_of_qtnqDeletedFive h hu hb
    refine ⟨B, hBH, hBnc, ?_⟩
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    rcases hBpr p hp hdvd with h2 | h3 <;> omega
  · obtain ⟨B, hBH, hBel, hB4⟩ := NQSetup.exists_four_of_qtnqNaturalThreeDouble h hu hc1
    exact ⟨B, hBH, hfour B hBel hB4⟩
  · obtain ⟨B, hBH, hBel, hB4⟩ := NQSetup.exists_four_of_qtnqNaturalThreeExtension h hu hc2
    exact ⟨B, hBH, hfour B hBel hB4⟩

end Stabilizers

section Irreducible

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem frattiniConj_comp_ne_one {p : ℕ} (hp : p.Prime) {L X : Subgroup G}
    (hLN : L ≤ normalizer (X : Set G))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirrL : IsFrattiniIrreducible X L) :
    (normalizerFrattiniConj X).comp (inclusion hLN) ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  intro hb
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (X ⧸ CFSG.pCore 2 X) ⧸
    frattini (X ⧸ CFSG.pCore 2 X)) p (by rw [hW]; exact dvd_pow_self p two_ne_zero)
  rcases hirrL (zpowers w) (by
    intro l hl y hy
    have h1 : normalizerFrattiniConj X l = 1 := by
      have h2 := DFunLike.congr_fun hb ⟨l, hl⟩
      have h3 : inclusion hLN ⟨(l : G), hl⟩ = l := Subtype.ext rfl
      rw [MonoidHom.comp_apply, h3] at h2
      exact h2
    rw [h1]
    exact hy) with h0 | ht
  · have h1 : w ∈ zpowers w := mem_zpowers w
    rw [h0, mem_bot] at h1
    rw [h1, orderOf_one] at hw
    exact hp.one_lt.ne' hw.symm
  · have h1 := Nat.card_zpowers w
    rw [hw, ht, card_top, hW] at h1
    have := Nat.pow_right_injective hp.two_le (h1.trans (pow_one p).symm)
    omega

theorem isFrattiniIrreducible_inf_centralizer
    (h : QTNQ T L M) (hmod : QTNQExplicitModule L M)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXchar : (X.subgroupOf L).Characteristic) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirrL : IsFrattiniIrreducible X L) {u : G} (hu : u ∈ qtnqU L M) :
    IsFrattiniIrreducible X (L ⊓ centralizer {u}) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hLN : L ≤ normalizer (X : Set G) := by
    refine le_normalizer.trans ?_
    exact NQSetup.normalizer_le_normalizer_of_characteristic hXL hXchar
  have hpow : ∀ w : X ⧸ CFSG.pCore 2 X, w ^ p = 1 := fun w => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one w
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := fun w => ⟨1, by rw [pow_one, hpow]⟩
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXp⟩
  have : IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    CFSG.isElementaryAbelian_quotient_frattini
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  set β := (normalizerFrattiniConj X).comp (inclusion hLN) with hβ
  have hβ1 : β ≠ 1 := frattiniConj_comp_ne_one hp hLN hW hirrL
  set α := (NQSetup.mulAutLinear p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))).comp β
    with hα
  have hα1 : α ≠ 1 := by
    intro h1
    apply hβ1
    ext l w
    have h2 := LinearEquiv.congr_fun (DFunLike.congr_fun h1 l) (Additive.ofMul w)
    exact congrArg Additive.toMul h2
  have hfin := NQSetup.finrank_additive_eq_two hW
  obtain ⟨B, hBH, hBnc, hBcop⟩ := exists_noncyclic_coprime_of_explicitModule h hmod hu hp hp5
  intro Y hY
  set U' : Submodule (ZMod p) (Additive ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) :=
    AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup Y) with hU'
  have hmemU' : ∀ x, x ∈ U' ↔ Additive.toMul x ∈ Y := fun _ => Iff.rfl
  rcases NQSetup.nq_noncyclic_coprime_projective_irreducibility hp5 hLC hfin α hα1
      ((centralizer ({u} : Set G)).subgroupOf L) ⟨B, hBH, hBnc, hBcop⟩ U' (by
        intro l hl x hx
        rw [hmemU'] at hx ⊢
        exact hY ⟨l, hLN l.2⟩ (mem_inf.mpr ⟨l.2, hl⟩) _ hx) with h0 | ht
  · left
    rw [eq_bot_iff]
    intro y hy
    have h1 : Additive.ofMul y ∈ U' := (hmemU' _).mpr hy
    rw [h0, Submodule.mem_bot] at h1
    exact (mem_bot).mpr (Additive.ofMul.injective h1)
  · right
    rw [eq_top_iff]
    intro y _
    have h1 : Additive.ofMul y ∈ U' := by rw [ht]; exact Submodule.mem_top
    exact (hmemU' _).mp h1

end Irreducible

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem explicit_module_centralizer_irreducibility (h : QTNQ T L M)
    (hmod : QTNQExplicitModule L M) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ X : Subgroup G, X ≤ L ∧ (X.subgroupOf L).Characteristic ∧
      X ≤ (CFSG.solvableRadical L).map L.subtype ∧ CFSG.pCore 2 X ≠ ⊥ ∧
      normalizer (X : Set G) = M ∧ NoPQuotient 2 X ∧
      Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p ∧ CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 ∧
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 ∧
      (∀ u ∈ qtnqU L M, IsFrattiniIrreducible X (M ⊓ centralizer {u})) ∧
      ∀ u ∈ qtnqU L M, ∀ g : G, M ⊓ centralizer {u} ≤ CFSG.conjugate M g →
        g ∈ M ∧ CFSG.conjugate M g = M := by
  obtain ⟨p, hp, hp5, X, hXL, hXchar, hXRad, hX2, hexp, hrk, hO2, hNX, hW, hirrL, -, hconj⟩ :=
    configuration_centralizer_conjugate_rigidity_witness h
  have hirr : ∀ u ∈ qtnqU L M, IsFrattiniIrreducible X (M ⊓ centralizer {u}) := fun u hu =>
    (isFrattiniIrreducible_inf_centralizer h hmod hp hp5 hXL hXchar hexp hW hirrL hu).mono
      (inf_le_inf_right _ h.l_le)
  exact ⟨p, hp, hp5, X, hXL, hXchar, hXRad, hO2, hNX, hX2, hexp, hrk, hW, hirr,
    fun u hu g hg => hconj u hu (hirr u hu) g hg⟩

end CFSG.Quasithin.H13.NQRigid
