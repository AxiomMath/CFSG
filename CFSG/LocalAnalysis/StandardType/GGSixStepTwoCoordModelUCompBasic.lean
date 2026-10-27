module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUFrame
public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompSmall

public section

namespace CFSG.StandardType

namespace CoordSU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Multiplicative
open scoped commutatorElement

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

section Helpers

theorem ι_mem (F : PieceFrame f n K h p A) (s : Multiplicative (Fin F.r → ZMod p)) :
    F.ι s ∈ A := by
  have h1 : F.ι s ∈ F.ι.range := ⟨s, rfl⟩
  rwa [F.ι_range] at h1

theorem lin_b_eq_self_iff (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (i : Fin F.r)
    (v : Fin n → K) :
    lin (F.b i) v = v ↔ v ∈ (rng (F.y i)).orthogonalBilin (stdHermForm h n) := by
  have : Fact (1 < p) := ⟨hA.prime.one_lt⟩
  rw [← F.ι_single i, F.ι_fix]
  constructor
  · intro hv
    exact hv i (by simp)
  · intro hv j hj
    have hji : j = i := by
      by_contra hne
      exact hj (by simp [Pi.single_eq_of_ne hne])
    rw [hji]
    exact hv

theorem mul_comm_of_forall_primaryComponent (hK : UnitaryFieldData 2 f K) (hp : p.Prime)
    (hp2 : p ≠ 2) {x g c : ↥(unitarySU 2 f K n)} (hx : x ^ p = 1)
    (hgc : ∀ b ∈ primaryFactors (Xe x), ∀ v ∈ primaryComponent (Xe x) b,
      lin g (lin c v) = lin c (lin g v)) : g * c = c * g := by
  apply toUnitHom_injective
  rw [map_mul, map_mul]
  refine Units.ext (ext_primaryComponent (primaryData hK hp hp2 hx).squarefree fun b hb v hv => ?_)
  exact hgc b hb v hv

theorem card_le_card_inf_centralizer {G : Type} [Group G] [Finite G] {r : ℕ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} (hinj : Function.Injective ι) {L₁ : Subgroup G}
    {α : Type} (φ : α → (Fin r → ZMod p)) (hφ : Function.Injective φ)
    (hcomm : ∀ a, ι (ofAdd (φ a)) ∈ Subgroup.centralizer (L₁ : Set G)) :
    Nat.card α ≤ Nat.card (ι.range ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) :=
  Nat.card_le_card_of_injective (fun a => ⟨ι (ofAdd (φ a)), ⟨ofAdd (φ a), rfl⟩, hcomm a⟩)
    fun _ _ haa' => hφ (ofAdd.injective (hinj (congrArg Subtype.val haa')))

end Helpers

section Cases

variable {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G}

theorem eq_map_sb_of_le [Finite K] [Finite G] (hker : SURep.GGFrameKer φ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ f + 1) {x : ↥(unitarySU 2 f K n)} (hx : x ^ p = 1)
    {L₁ : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {φ x}))
    (a : primaryFactors (Xe x)) (ha : IsGoodBlock h (toUnitHom x) a)
    (hle : L₁ ≤ (sb h x a).map φ) : L₁ = (sb h x a).map φ := by
  rw [SUNS.range_inf_centralizer_eq_map h hker hp hpq hx] at hL
  have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL hle
    (Subgroup.map_mono sb_le_centralizer)
  have hrange : (sb h x a).map φ = (φ.comp (sb h x a).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange] at hc' ⊢
  exact CoordSL.eq_of_isComponentOf_range (isQuasisimple_sb hp hp2 hx a ha) _ hc'

theorem map_mem_centralizer_of_not_le [Finite K] [Finite G] (hker : SURep.GGFrameKer φ)
    (hA : MaxElemAb p A) {x : ↥(unitarySU 2 f K n)} (hxA : x ∈ A) {L₁ : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {φ x}))
    (hex : ∀ a : primaryFactors (Xe x), IsGoodBlock h (toUnitHom x) a →
      ¬ L₁ ≤ (sb h x a).map φ) {c : ↥(unitarySU 2 f K n)} (hc : c ∈ A) :
    φ c ∈ Subgroup.centralizer (L₁ : Set G) := by
  classical
  have hp := hA.prime
  have hp2 := hA.ne_two
  have hpq := hA.not_dvd
  have hx : x ^ p = 1 := hA.pow x hxA
  have H := primaryData h hp hp2 hx
  rw [SUNS.range_inf_centralizer_eq_map h hker hp hpq hx] at hL
  set C := Subgroup.centralizer ({x} : Set ↥(unitarySU 2 f K n)) with hC
  have hcomm : ∀ a : primaryFactors (Xe x), IsGoodBlock h (toUnitHom x) a →
      ⁅L₁, (sb h x (a : K[X])).map φ⁆ = ⊥ :=
    fun a ha => (CoordSL.le_or_commutator_eq_bot_of_normal hL
      (Subgroup.map_mono sb_le_centralizer) (map_sb_normal (a : K[X]))).resolve_left (hex a ha)
  refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
  obtain ⟨y, hyC, rfl⟩ := hL.1 hg
  have hcC : c ∈ C := mem_centralizer_of_mem hA hxA hc
  have hYc : ∀ z ∈ C, (lin z : Module.End K (Fin n → K)) ∈ commutant (Xe x) := by
    intro z hz
    refine (mem_commutant _).mpr ?_
    have h1 : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [coe_toUnitHom, Commute, SemiconjBy, ← lin_mul, ← lin_mul, h1]
  have hyc : y * c = c * y := by
    refine mul_comm_of_forall_primaryComponent h hp hp2 hx fun b hb v hv => ?_
    by_cases hgood : IsGoodBlock h (toUnitHom x) ⟨b, hb⟩
    ·
      obtain ⟨e, he⟩ := exists_smul_of_commute_sb hp hp2 hx ⟨b, hb⟩ hgood hyC
        (commute_of_map_commute hker hp hp2 hx ⟨b, hb⟩ hgood fun g' hg' => by
          have hmem : ⁅φ y, φ g'⁆ ∈ ⁅L₁, (sb h x b).map φ⁆ :=
            Subgroup.commutator_mem_commutator hg ⟨g', hg', rfl⟩
          rw [hcomm ⟨b, hb⟩ hgood, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
            at hmem
          exact hmem)
      have hcv := lin_mem_primaryComponent hcC hv
      have hlin := map_smul (commutantRestrict b ⟨lin c, hYc c hcC⟩) e ⟨v, hv⟩
      have hlin' : lin c ((e • (⟨v, hv⟩ : primaryComponent (Xe x) b) :
          primaryComponent (Xe x) b) : Fin n → K) =
          ((e • (⟨lin c v, hcv⟩ : primaryComponent (Xe x) b) : primaryComponent (Xe x) b) :
            Fin n → K) := congrArg Subtype.val hlin
      rw [he ⟨lin c v, hcv⟩, he ⟨v, hv⟩, hlin']
    · by_cases hm1 : primaryMultiplicity (Xe x) b ≤ 1
      ·
        have : Fact (Irreducible b) := ⟨irreducible_of_mem_primaryFactors hb⟩
        have hcm := End_commute_of_finrank_le_one (E := AdjoinRoot b)
          (W := primaryComponent (Xe x) b) hm1
          (commutantRestrict b ⟨lin y, hYc y hyC⟩) (commutantRestrict b ⟨lin c, hYc c hcC⟩)
        exact congrArg (fun S : Module.End (AdjoinRoot b) (primaryComponent (Xe x) b) =>
          ((S ⟨v, hv⟩ : primaryComponent (Xe x) b) : Fin n → K)) hcm.eq
      ·
        have hm2 : 2 ≤ primaryMultiplicity (Xe x) b := by omega
        have hself : dualPoly h.bar b = b := by
          by_contra hne
          exact hgood ⟨hm2, fun h' => absurd h' hne⟩
        have hbad : (primaryMultiplicity (Xe x) b, 2 ^ (f * b.natDegree)) ∈
            ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
          by_contra hnot
          exact hgood ⟨hm2, fun _ => hnot⟩
        have hcp : toUnitHom c ^ p = 1 := by rw [← map_pow, hA.pow c hc, map_one]
        have htriv := apply_eq_of_exceptional H hp (three_lt_of_bad hp hp2 hpq hbad)
          (toUnitHom_mem_unitaryCentralizer hcC) hcp ⟨b, hb⟩ hself hbad
        have h1 : lin c v = v := htriv v hv
        have h2 : lin c (lin y v) = lin y v := htriv _ (lin_mem_primaryComponent hyC hv)
        rw [h1, h2]
  rw [← map_mul, ← map_mul, hyc]

end Cases

end CoordSU

end CFSG.StandardType
