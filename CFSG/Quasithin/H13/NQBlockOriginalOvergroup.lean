module

public import CFSG.Quasithin.H13.NQBlockOriginalSupplements

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport
    {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) :
    T ≤ normalizer (nqOriginalK T L : Set G) ∧
      (∃ e : nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L) ≃* L ⧸ CFSG.solvableRadical L,
        (∀ (k : nqOriginalK T L) (hk : (k : G) ∈ L),
          e (QuotientGroup.mk k) = QuotientGroup.mk (⟨k, hk⟩ : L)) ∧
        ∀ t ∈ T, ∀ (k : nqOriginalK T L) (l : L),
          e (QuotientGroup.mk k) = QuotientGroup.mk l →
          ∀ (hk : t * (k : G) * t⁻¹ ∈ nqOriginalK T L) (hl : t * (l : G) * t⁻¹ ∈ L),
            e (QuotientGroup.mk ⟨t * (k : G) * t⁻¹, hk⟩) =
              QuotientGroup.mk (⟨t * (l : G) * t⁻¹, hl⟩ : L)) ∧
      (∀ t : G, t ∈ R ↔ t ∈ T ∧
        ∀ k ∈ nqOriginalK T L, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 (nqOriginalK T L)) ∧
      ∀ H Y : Subgroup G, nqOriginalK T L ⊔ T ≤ H → Y ≤ H → (Y.subgroupOf H).Normal →
        pCoreOf 2 Y ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ R ∧
        (⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y →
          (CFSG.perfectResidual ↥(nqOriginalK T L ⊔ pCoreOf 2 Y)).map
              (nqOriginalK T L ⊔ pCoreOf 2 Y).subtype = nqOriginalK T L ∧
            Y ≤ normalizer (nqOriginalK T L : Set G) ∧
            ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 (nqOriginalK T L) ⊓ pCoreOf 2 Y ∧
            (∀ y ∈ Y, ∀ k ∈ nqOriginalK T L,
              y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 (nqOriginalK T L)) ∧
            T ⊓ Y ≤ R ∧ CFSG.ABGLocalTools.IsSylowOf 2 R (Y ⊔ R)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKL, hTK, hLNK⟩ := original_K_supplement h
  obtain ⟨-, hRO, -, hKN, ⟨e, he⟩, -⟩ :=
    original_radical_supplements_share_simple_residual_and_internal_module h hR
  obtain ⟨hRT, -, -, -, -, -, -, hKp, -⟩ := original_radical_supplement h.sylow.1
    h.maximal_local.1.2.2.1 (h.eq_normalizer ▸ h.t_le) h.maximal_local.1.2.1 hR
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  have hchar := (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).1
  have hLN : L ≤ normalizer (((CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G) :=
    le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hTN : T ≤ normalizer (((CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G) :=
    hTL.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hmem : ∀ y, y ∈ R ↔ y ∈ nqOriginalCentralizer T L := fun y => by
    rw [← hR]
    rfl
  have hker : ∀ t : G, t ∈ R ↔ t ∈ T ∧
      ∀ k ∈ nqOriginalK T L, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 (nqOriginalK T L) := by
    intro t
    rw [hmem]
    constructor
    · rintro ⟨htT, ht⟩
      refine ⟨htT, fun k hk => ?_⟩
      rw [← hKN]
      refine mem_inf.mpr ⟨?_, ht k (hKL hk)⟩
      have h1 : t * k * t⁻¹ ∈ nqOriginalK T L := (mem_normalizer_iff.mp (hTK htT) k).mp hk
      exact mul_mem h1 (inv_mem hk)
    · rintro ⟨htT, ht⟩
      refine ⟨htT, fun l hl => ?_⟩
      have hl' : l ∈ (((CFSG.solvableRadical L).map L.subtype ⊔ nqOriginalK T L :
          Subgroup G) : Set G) := by
        rw [← hLNK]
        exact hl
      rw [coe_mul_of_right_le_normalizer_left _ _ (hKL.trans hLN), Set.mem_mul] at hl'
      obtain ⟨n, hn, k, hk, rfl⟩ := hl'
      have h1 : t * n * t⁻¹ ∈ (CFSG.solvableRadical L).map L.subtype :=
        (mem_normalizer_iff.mp (hTN htT) n).mp hn
      have h2 : t * k * t⁻¹ * k⁻¹ ∈ (CFSG.solvableRadical L).map L.subtype := by
        have h3 := ht k hk
        rw [← hKN] at h3
        exact (mem_inf.mp h3).2
      rw [show t * (n * k) * t⁻¹ * (n * k)⁻¹ = (t * n * t⁻¹) * (t * k * t⁻¹ * k⁻¹) * n⁻¹ by
        group]
      exact mul_mem (mul_mem h1 h2) (inv_mem hn)
  have hequiv : ∀ t ∈ T, ∀ (k : nqOriginalK T L) (l : L),
      e (QuotientGroup.mk k) = QuotientGroup.mk l →
      ∀ (hk : t * (k : G) * t⁻¹ ∈ nqOriginalK T L) (hl : t * (l : G) * t⁻¹ ∈ L),
        e (QuotientGroup.mk ⟨t * (k : G) * t⁻¹, hk⟩) =
          QuotientGroup.mk (⟨t * (l : G) * t⁻¹, hl⟩ : L) := by
    intro t ht k l hkl hk hl
    rw [he k (hKL k.2)] at hkl
    rw [he _ (hKL hk)]
    rw [QuotientGroup.eq] at hkl ⊢
    have h1 : (((⟨k, hKL k.2⟩ : L)⁻¹ * l : L) : G) ∈ (CFSG.solvableRadical L).map L.subtype :=
      ⟨_, hkl, rfl⟩
    have h2 := (mem_normalizer_iff.mp (hTN ht) _).mp h1
    have e2 : (((⟨t * (k : G) * t⁻¹, hKL hk⟩ : L)⁻¹ * ⟨t * (l : G) * t⁻¹, hl⟩ : L) : G) =
        t * (((⟨k, hKL k.2⟩ : L)⁻¹ * l : L) : G) * t⁻¹ := by
      simp only [coe_mul, coe_inv]
      group
    rw [← mem_map_iff_mem L.subtype_injective]
    change (((⟨t * (k : G) * t⁻¹, hKL hk⟩ : L)⁻¹ * ⟨t * (l : G) * t⁻¹, hl⟩ : L) : G) ∈ _
    rw [e2]
    exact h2
  refine ⟨hTK, ⟨e, he, hequiv⟩, hker, fun H Y hKTH hYH hYn => ?_⟩
  let T' : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hT' : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hH2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hHO : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hOT : pCoreOf 2 H ≤ T := by
    have h1 := T'.is_maximal' (T'.isPGroup'.to_sup_of_normal_right' hH2
      (hT' ▸ hTH.trans hHO)) le_sup_left
    rw [← hT', ← h1]
    exact le_sup_right
  have hOKT : pCoreOf 2 H ≤ nqOriginalK T L ⊔ T := hOT.trans le_sup_right
  have hOR : pCoreOf 2 H ≤ R := by
    rw [hRO]
    exact le_pCoreOf_of_subgroupOf_normal hOKT
      ((normal_subgroupOf_iff_le_normalizer hOKT).mpr (hKTH.trans hHO)) hH2
  have hY2 : IsPGroup 2 (pCoreOf 2 Y) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Y
  have hQYY : pCoreOf 2 Y ≤ Y := map_subtype_le _
  have hHY : H ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hYQ : normalizer (Y : Set G) ≤ normalizer (pCoreOf 2 Y : Set G) := by
    unfold pCoreOf
    exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hHQY : H ≤ normalizer (pCoreOf 2 Y : Set G) := hHY.trans hYQ
  have hQYH : pCoreOf 2 Y ≤ pCoreOf 2 H := le_pCoreOf_of_subgroupOf_normal (hQYY.trans hYH)
    ((normal_subgroupOf_iff_le_normalizer (hQYY.trans hYH)).mpr hHQY) hY2
  refine ⟨hQYH, hOR, fun hKY => ?_⟩
  have hQYR : pCoreOf 2 Y ≤ R := hQYH.trans hOR
  have hQYK : pCoreOf 2 Y ≤ normalizer (nqOriginalK T L : Set G) := (hQYR.trans hRT).trans hTK
  have hKB : nqOriginalK T L ≤ nqOriginalK T L ⊔ pCoreOf 2 Y := le_sup_left
  have hKBn : ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ pCoreOf 2 Y)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKB).mpr (sup_le le_normalizer hQYK)
  have hQs : Group.IsSolvable (pCoreOf 2 Y) := by
    have := hY2.isNilpotent
    infer_instance
  have hPC : perfectCore (nqOriginalK T L ⊔ pCoreOf 2 Y) = nqOriginalK T L :=
    le_antisymm (perfectCore_le_of_sup_solvable hKB hKBn rfl hQs)
      (le_perfectCore_of_perfect hKB hKp)
  have hDInf : (CFSG.perfectResidual ↥(nqOriginalK T L ⊔ pCoreOf 2 Y)).map
      (nqOriginalK T L ⊔ pCoreOf 2 Y).subtype = nqOriginalK T L := by
    rw [← perfectCore_eq_map_perfectResidual, hPC]
  have hYK : Y ≤ normalizer (nqOriginalK T L : Set G) := by
    intro y hy
    have hyQ : y ∈ normalizer (pCoreOf 2 Y : Set G) := hHQY (hYH hy)
    have hyB : y ∈ normalizer ((nqOriginalK T L ⊔ pCoreOf 2 Y : Subgroup G) : Set G) := by
      refine A4.mem_normalizer_of_conj_mem fun b hb => ?_
      have h1 : nqOriginalK T L ⊔ pCoreOf 2 Y ≤
          (nqOriginalK T L ⊔ pCoreOf 2 Y).comap (MulAut.conj y).toMonoidHom := by
        refine sup_le (fun k hk => mem_comap.mpr ?_)
          (fun q hq => mem_comap.mpr (mem_sup_right ((mem_normalizer_iff.mp hyQ q).mp hq)))
        have hc : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 Y := by
          have h2 := inv_mem (hKY (commutator_mem_commutator hk hy))
          rwa [commutatorElement_def,
            show (k * y * k⁻¹ * y⁻¹)⁻¹ = y * k * y⁻¹ * k⁻¹ by group] at h2
        show y * k * y⁻¹ ∈ nqOriginalK T L ⊔ pCoreOf 2 Y
        rw [show y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k by group]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hk)
      exact h1 hb
    have h1 := normalizer_le_normalizer_perfectCore (nqOriginalK T L ⊔ pCoreOf 2 Y) hyB
    rwa [hPC] at h1
  have hKYK : ⁅nqOriginalK T L, Y⁆ ≤ nqOriginalK T L := by
    rw [commutator_le]
    intro k hk y hy
    have h1 : y * k⁻¹ * y⁻¹ ∈ nqOriginalK T L :=
      (mem_normalizer_iff.mp (hYK hy) k⁻¹).mp (inv_mem hk)
    rw [commutatorElement_def, show k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) by group]
    exact mul_mem hk h1
  have hKQ : nqOriginalK T L ⊓ pCoreOf 2 Y ≤ pCoreOf 2 (nqOriginalK T L) := by
    refine le_pCoreOf_of_subgroupOf_normal inf_le_left ?_ (hY2.to_le inf_le_right)
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk => ?_
    exact mem_normalizer_inf (le_normalizer hk) (hHQY (hKTH (mem_sup_left hk)))
  have hKYQ : ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 (nqOriginalK T L) ⊓ pCoreOf 2 Y :=
    le_inf ((le_inf hKYK hKY).trans hKQ) hKY
  have hYc : ∀ y ∈ Y, ∀ k ∈ nqOriginalK T L,
      y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 (nqOriginalK T L) := by
    intro y hy k hk
    have h1 : ⁅y, k⁆ ∈ ⁅nqOriginalK T L, Y⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hy hk
    rw [commutatorElement_def] at h1
    exact (mem_inf.mp (hKYQ h1)).1
  have hTYR : T ⊓ Y ≤ R := fun t ht =>
    (hker t).mpr ⟨(mem_inf.mp ht).1, hYc t (mem_inf.mp ht).2⟩
  have hRY : R ≤ normalizer (Y : Set G) := (hRT.trans hTH).trans hHY
  have hS1 : CFSG.ABGLocalTools.IsSylowOf 2 (T' : Subgroup G) (Y ⊔ T) :=
    (isSylowOf_top T').of_le (hT' ▸ le_sup_right) le_top
  have hS2 := hS1.inf_of_le_normalizer le_sup_left (sup_le le_normalizer (hTH.trans hHY))
  have hTY : (T' : Subgroup G) ⊓ Y = R ⊓ Y :=
    le_antisymm (le_inf (hT' ▸ hTYR) inf_le_right) (inf_le_inf_right _ (hT' ▸ hRT))
  rw [hTY] at hS2
  exact ⟨hDInf, hYK, hKYQ, hYc, hTYR, isSylowOf_sup_of_inf hRY (h.sylow.1.to_le hRT) hS2⟩

end CFSG.Quasithin.H13.NQBlock
