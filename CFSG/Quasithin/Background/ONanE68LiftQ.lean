module

public import CFSG.Quasithin.Background.ONanE68Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.Quasithin.H13.KG68 CFSG.Blueprint

@[expose] def HexadPar (M0 : Type) [Group M0] (m : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (L' R' : Subgroup G'), Nonempty (↥L' ≃* M0) →
    IsPGroup 2 R' → R' ≤ Subgroup.normalizer (L' : Set G') → IsSylowTwoOf (R' ⊓ L') L' →
    ∃ K' : Subgroup G', K' ≤ L' ∧ R' ≤ Subgroup.normalizer (K' : Set G') ∧ CharTwo K' ∧
      ¬ HasChi0Block K' ∧ IsAltOverElemAbelian K' 4 m ∧
      ∀ Y : Subgroup G', K' ≤ Y → Y ≤ L' → Y = K' ∨ Y = L'

theorem hexadPar_m22 (h : L239M22Parabolic) : HexadPar (NativeSporadic.Carrier .M22) 6 := h

theorem hexadPar_m23 (h : L239M23Parabolic) : HexadPar (NativeSporadic.Carrier .M23) 7 := h

section Quot

variable {G : Type} [Group G]

theorem pCoreOf_le_self {X : Subgroup G} : pCoreOf 2 X ≤ X := CFSG.openPCoreOf_le 2 X

theorem exists_hexad_lift [Finite G] {M0 : Type} [Group M0] {m : ℕ} (hpar : HexadPar M0 m)
    (hs : IsSimpleGroup (alternatingGroup (Fin m)))
    (hcard : Nat.card (alternatingGroup (Fin m)) = 360 ∨
      Nat.card (alternatingGroup (Fin m)) = 2520)
    {L Q : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) (hQ2 : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (L : Set G)) (hSyl : IsSylowTwoOf (Q ⊓ L) L)
    (he : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* M0)) :
    ∃ K : Subgroup G, K ≤ L ∧ pCoreOf 2 L ≤ K ∧ Q ≤ Subgroup.normalizer (K : Set G) ∧
      CharTwo K ∧ ¬ HasChi0Block K ∧ K ≤ twoPrimeResidual K ∧
      (∀ Y : Subgroup G, K ≤ Y → Y ≤ L → Y = K ∨ Y = L) ∧ K ≠ L ∧
      ∀ l ∈ L, (∀ k ∈ K, l * k * l⁻¹ * k⁻¹ ∈ pCoreOf 2 L) → l ∈ pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := L ⊔ Q with hX
  have hLX : L ≤ X := le_sup_left
  have hQX : Q ≤ X := le_sup_right
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hQN
  have hZL : pCoreOf 2 L ≤ L := pCoreOf_le_self
  have hXZ : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  set N : Subgroup ↥X := (pCoreOf 2 L).subgroupOf X with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (hZL.trans hLX)).2 hXZ
  let π : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N
  let Λ : ↥L →* ↥X ⧸ N := π.comp (Subgroup.inclusion hLX)
  let Ψ : ↥Q →* ↥X ⧸ N := π.comp (Subgroup.inclusion hQX)
  have hΛ : ∀ l : ↥L, Λ l = π ⟨(l : G), hLX l.2⟩ := fun l => rfl
  have hΨ : ∀ q : ↥Q, Ψ q = π ⟨(q : G), hQX q.2⟩ := fun q => rfl
  have hkerΛ : ∀ l : ↥L, Λ l = 1 ↔ (l : G) ∈ pCoreOf 2 L := by
    intro l
    rw [hΛ]
    exact (QuotientGroup.eq_one_iff _).trans Subgroup.mem_subgroupOf
  have hkerΛ' : Λ.ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker, hkerΛ]
    constructor
    · intro hl
      obtain ⟨y, hyG, hy⟩ := mem_pCoreOf_iff'.1 hl
      have : y = l := Subtype.ext hyG
      rwa [this] at hy
    · intro hl
      exact mem_pCoreOf_iff'.2 ⟨l, rfl, hl⟩
  have hΛr : Function.Surjective Λ.rangeRestrict := Λ.rangeRestrict_surjective
  have he' : Nonempty (↥Λ.range ≃* M0) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hkerΛ'.symm).trans
      (QuotientGroup.quotientKerEquivRange Λ)).symm.trans e⟩
  have hR2 : IsPGroup 2 ↥Ψ.range := hQ2.of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  have hconj : ∀ (q : ↥Q) (l : ↥L) (h : (q : G) * l * (q : G)⁻¹ ∈ L),
      Λ ⟨(q : G) * l * (q : G)⁻¹, h⟩ = Ψ q * Λ l * (Ψ q)⁻¹ := by
    intro q l h
    rw [hΛ, hΨ, hΛ, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext rfl)
  have hRN : Ψ.range ≤ Subgroup.normalizer (Λ.range : Set (↥X ⧸ N)) := by
    rintro _ ⟨q, rfl⟩
    refine A4.mem_normalizer_of_conj_mem ?_
    rintro _ ⟨l, rfl⟩
    have hmem : (q : G) * l * (q : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hQN q.2) l).1 l.2
    exact ⟨⟨_, hmem⟩, (hconj q l hmem).symm ▸ rfl⟩
  have hSyl' : IsSylowTwoOf (Ψ.range ⊓ Λ.range) Λ.range := by
    refine ⟨inf_le_right, hR2.to_le inf_le_left, ?_⟩
    let PL : Sylow 2 ↥L := A4.toSylow hSyl
    let P' : Sylow 2 ↥Λ.range := PL.mapSurjective hΛr
    have hP'le : (P' : Subgroup ↥Λ.range) ≤ (Ψ.range ⊓ Λ.range).subgroupOf Λ.range := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ Q ⊓ L := hy
      refine Subgroup.mem_subgroupOf.2 ⟨⟨⟨(y : G), hy'.1⟩, rfl⟩, ⟨y, rfl⟩⟩
    exact fun h2 => P'.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hP'le))
  obtain ⟨K', hK'L, hRK, hchar, -, halt, hmax⟩ := hpar _ Λ.range Ψ.range he' hR2 hRN hSyl'
  have hLift : LiftHyp L Λ K' m := ⟨hq, hkerΛ, hK'L, hchar, hmax, halt, hs, hcard⟩
  refine ⟨liftSub L Λ K', liftSub_le, hLift.pCoreOf_le, ?_, hLift.charTwo_lift, hLift.noChi0,
    hLift.residual, hLift.maximal_lift, hLift.ne, hLift.centralizer_trivial⟩
  intro q hq'
  refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxL, hxK⟩ := mem_liftSub.1 hx
  have hqxL : q * x * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hQN hq') x).1 hxL
  refine mem_liftSub.2 ⟨hqxL, ?_⟩
  rw [hconj ⟨q, hq'⟩ ⟨x, hxL⟩ hqxL]
  have hr : Ψ ⟨q, hq'⟩ ∈ Subgroup.normalizer (K' : Set (↥X ⧸ N)) := hRK ⟨_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 hr _).1 hxK

end Quot

end E68Proof

end E6

end CFSG.Quasithin
