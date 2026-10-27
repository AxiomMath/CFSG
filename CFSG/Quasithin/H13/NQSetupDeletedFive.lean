module

public import CFSG.Quasithin.H13.NQSetupDeletedModule
public import CFSG.Quasithin.H13.NQSetupCcomponent
public import CFSG.Quasithin.H13.NQSetupPlaneAction
public import CFSG.Quasithin.SteinbergCCLocalSylowAction

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup CFSG.Open Equiv Equiv.Perm
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open scoped IsMulCommutative

theorem deleted_five_point_centralizer_Sylow_action_on_original_prime_plane_is_nontrivial
    {G : Type} [Group G] [Finite G] {T L M : Subgroup G} (h : QTNQ T L M)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
    (θ : Additive (qtnqU L M) ≃+ evenWeight Ω)
    (hθ : ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
      (θ (Additive.ofMul y) : Ω → ZMod 2) =
        permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x)))
    {p : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (_hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (_hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {u : G} (hu : u ∈ qtnqU L M)
    (hQ : IsSylowOf 2 (T ⊓ centralizer {u}) (M ⊓ centralizer {u})) :
    ((T ⊓ centralizer {u} ⊓ L).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X) ≠ ⊥ ∧
      ((T ⊓ centralizer {u}).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X) ≠ ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.solvableRadical L with hR
  have hLC := isCComponent_top_of_qtnq h
  have hLN : L ≤ normalizer (X : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_of_characteristic hXL hXc)
  set ρ : L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (inclusion hLN) with hρ
  have hρ1 : ρ.ker ≠ ⊤ := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro htop
    apply hl1
    have h1 : (⟨l, hlL⟩ : L) ∈ ρ.ker := by
      rw [htop]
      exact mem_top _
    exact h1
  have hker : ρ.ker ≤ R := le_solvableRadical_of_normal_ne_top hLC hρ1
  set H : Subgroup L := (centralizer ({u} : Set G)).subgroupOf L with hH
  have hθi : Function.Injective fun x : qtnqU L M => (θ (Additive.ofMul x) : Ω → ZMod 2) :=
    fun x y hxy => Additive.ofMul.injective (θ.injective (Subtype.ext hxy))
  have hHmap : 2 ∣ Nat.card (H.map (QuotientGroup.mk' R)) := by
    rw [hH, card_map_centralizer_eq_card_altStab h β _ hθi hθ hu]
    exact two_dvd_card_altStab hΩ _ (θ (Additive.ofMul ⟨u, hu⟩)).2
  set QL := T ⊓ centralizer ({u} : Set G) ⊓ L with hQLdef
  have hQLL : QL ≤ L := inf_le_right
  have hS : IsSylowOf 2 (QL.subgroupOf L) H := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L, map_subgroupOf_eq_of_le hQLL, hH,
      subgroupOf_map_subtype, inf_comm]
    exact isSylowOf_inf_of_qtnq h u hQ
  obtain ⟨S, hSeq⟩ := hS.exists_sylow_eq_subgroupOf
  have hfs := (QuotientGroup.mk' R).subgroupMap_surjective H
  set Sb : Sylow 2 (H.map (QuotientGroup.mk' R)) := S.mapSurjective hfs with hSb
  have hSb1 := Sb.ne_bot_of_dvd_card hHmap
  have hexists : ∃ s ∈ (S : Subgroup H), ρ (s : L) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hSb1
    rw [hSb, Sylow.coe_mapSurjective, eq_bot_iff]
    rintro _ ⟨s, hs, rfl⟩
    have h1 : (s : L) ∈ R := hker (hcon s hs)
    rw [mem_bot]
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
  obtain ⟨s, hs, hs1⟩ := hexists
  have hs' : (((s : H) : L) : G) ∈ QL := by
    have hs2 : s ∈ (S : Subgroup H) := hs
    rw [hSeq] at hs2
    exact mem_subgroupOf.mp (mem_subgroupOf.mp hs2)
  have hQW : ((QL.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X)) ≠ ⊥ := by
    intro hbot
    apply hs1
    have h1 : normalizerFrattiniConj X (inclusion hLN (s : L)) ∈
        (QL.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X) :=
      ⟨inclusion hLN (s : L), mem_subgroupOf.mpr hs', rfl⟩
    rw [hbot, mem_bot] at h1
    exact h1
  refine ⟨hQW, fun hbot => hQW (eq_bot_iff.mpr ?_)⟩
  rw [← hbot]
  refine map_mono fun n hn => ?_
  exact mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hn)).1

end CFSG.Quasithin.H13.NQSetup
