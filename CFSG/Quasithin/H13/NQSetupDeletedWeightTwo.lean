module

public import CFSG.Quasithin.H13.NQSetupDeletedModule
public import CFSG.Quasithin.H13.NQSetupPlaneAction
public import CFSG.Quasithin.H13.NQSetupPrimePlane
public import CFSG.Quasithin.SteinbergCCLocalSylowAction

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup CFSG.Open Equiv Equiv.Perm
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open scoped IsMulCommutative

theorem deleted_weight_two_centralizer_has_original_cyclic_four_Sylow_image
    {G : Type} [Group G] [Finite G] {T L M : Subgroup G} (h : QTNQ T L M)
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
    IsCyclic (((T ⊓ centralizer {u} ⊓ L).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X)) ∧
      Nat.card (((T ⊓ centralizer {u} ⊓ L).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X)) = 4 ∧
      4 ∣ Nat.card (((T ⊓ centralizer {u}).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.solvableRadical L with hR
  have hLC := isCComponent_top_of_qtnq h
  have hLN : L ≤ normalizer (X : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_of_characteristic hXL hXc)
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXA⟩
  have : IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    CFSG.isElementaryAbelian_quotient_frattini
  set W := (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) with hWdef
  set α : L →* (Additive W ≃ₗ[ZMod p] Additive W) :=
    (mulAutLinear p W).comp ((normalizerFrattiniConj X).comp (inclusion hLN)) with hα
  have hα1 : α ≠ 1 := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 := congrArg (fun f : L →* (Additive W ≃ₗ[ZMod p] Additive W) => f ⟨l, hlL⟩) h1
    simp only [MonoidHom.one_apply, hα, MonoidHom.comp_apply] at h2
    rw [← map_one (mulAutLinear p W)] at h2
    have h3 := mulAutLinear_injective p W h2
    rwa [show inclusion hLN ⟨(l : G), hlL⟩ = l from Subtype.ext rfl] at h3
  have hWdim : Module.finrank (ZMod p) (Additive W) = 2 := finrank_additive_eq_two hW
  set H : Subgroup L := (centralizer ({u} : Set G)).subgroupOf L with hH
  have hRH : R ≤ H := fun l hl => by
    rw [hH, mem_subgroupOf, mem_centralizer_singleton_iff]
    exact radical_commute_qtnqVc h hl (qtnqU_le_qtnqVc h hu)
  have hθi : Function.Injective fun x : qtnqU L M => (θ (Additive.ofMul x) : Ω → ZMod 2) :=
    fun x y hxy => Additive.ofMul.injective (θ.injective (Subtype.ext hxy))
  have hHmap : Nat.card (H.map (QuotientGroup.mk' R)) = 6 := by
    rw [hH, card_map_centralizer_eq_card_altStab h β _ hθi hθ hu]
    exact card_altStab_weight_two hΩ _ hu2
  set QL := T ⊓ centralizer ({u} : Set G) ⊓ L with hQLdef
  have hQLL : QL ≤ L := inf_le_right
  have hS : IsSylowOf 2 (QL.subgroupOf L) H := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L, map_subgroupOf_eq_of_le hQLL, hH,
      subgroupOf_map_subtype, inf_comm]
    exact isSylowOf_inf_of_qtnq h u hQ
  obtain ⟨S, hSeq⟩ := hS.exists_sylow_eq_subgroupOf
  obtain ⟨-, -, -, hmain⟩ :=
    prime_plane_radical_preimages_of_two_valuation_one_have_cyclic_four_Sylow_images hp5 hLC
      hWdim α hα1
  obtain ⟨hcyc, hcard⟩ := hmain H hRH 3 (by decide) (by rw [hHmap]) S
  set QW := (QL.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X) with hQW
  have himage : (S : Subgroup H).map (α.comp H.subtype) = QW.map (mulAutLinear p W) := by
    ext f
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : (((s : H) : L) : G) ∈ QL := by
        have hs2 : s ∈ (S : Subgroup H) := hs
        rw [hSeq] at hs2
        exact mem_subgroupOf.mp (mem_subgroupOf.mp hs2)
      exact ⟨normalizerFrattiniConj X (inclusion hLN (s : L)),
        ⟨inclusion hLN (s : L), mem_subgroupOf.mpr hs', rfl⟩, rfl⟩
    · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      have hn' : (n : G) ∈ QL := mem_subgroupOf.mp hn
      have hnL : (n : G) ∈ L := hQLL hn'
      have hnH : (⟨n, hnL⟩ : L) ∈ H := by
        rw [hH, mem_subgroupOf]
        exact (mem_inf.mp (mem_inf.mp hn').1).2
      have hnS : (⟨⟨n, hnL⟩, hnH⟩ : H) ∈ (S : Subgroup H) := by
        rw [hSeq]
        exact mem_subgroupOf.mpr (mem_subgroupOf.mpr hn')
      refine ⟨⟨⟨n, hnL⟩, hnH⟩, hnS, ?_⟩
      rfl
  have hinj := mulAutLinear_injective p W
  have hQWcard : Nat.card QW = 4 := by
    rw [← card_map_of_injective hinj, ← himage, hcard]
  have hQWcyc : IsCyclic QW := by
    have e := equivMapOfInjective QW (mulAutLinear p W) hinj
    rw [← himage] at e
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨hQWcyc, hQWcard, ?_⟩
  rw [← hQWcard]
  refine card_dvd_of_le (map_mono ?_)
  intro n hn
  exact mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hn)).1

end CFSG.Quasithin.H13.NQSetup
