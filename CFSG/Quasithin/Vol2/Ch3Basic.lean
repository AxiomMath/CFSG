module

public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

@[expose] def IsHStar (T M H : Subgroup G) : Prop :=
  InH T H ∧ ¬ H ≤ M ∧ ∀ Y : Subgroup G, InH T Y → Y ≤ H → ¬ Y ≤ M → Y = H

variable [Finite G]

theorem inH_of_le (T : Sylow 2 G) {Y H : Subgroup G} (hTY : (T : Subgroup G) ≤ Y) (hYH : Y ≤ H)
    (hH : InH (T : Subgroup G) H) : InH (T : Subgroup G) Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hTY, fun h => hH.2 (le_bot_iff.mp ?_)⟩
  rw [← h]
  refine pCoreOf_le_pCoreOf_of_sylow hYH T.isPGroup' hTY ?_
  intro h2
  apply T.not_dvd_index
  have := Subgroup.relIndex_dvd_index_of_le (hTY.trans hYH)
  exact h2.trans (by simpa [Subgroup.relIndex] using this)

theorem charTwo_of_le (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {Y H : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hYH : Y ≤ H) (hH : InH (T : Subgroup G) H) :
    CFSG.QuasithinUnique.CharTwo Y :=
  charTwo_of_inH hEven T (inH_of_le T hTY hYH hH)

theorem IsHStar.isUniqueMaxOver (T : Sylow 2 G) {M H : Subgroup G}
    (hH : IsHStar (T : Subgroup G) M H) (hTM : (T : Subgroup G) ≤ M) :
    IsUniqueMaxOver H (T : Subgroup G) (H ⊓ M) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1
  have hlt : H ⊓ M < H := lt_of_le_of_ne inf_le_left fun h => hH.2.1 (h ▸ inf_le_right)
  have key : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < H → Y ≤ H ⊓ M := by
    intro Y hTY hYH
    refine le_inf hYH.le ?_
    by_contra hYM
    exact hYH.ne (hH.2.2 Y (inH_of_le T hTY hYH.le hH.1) hYH.le hYM)
  have hmax : IsMaxSubgroupIn H (H ⊓ M) := by
    refine ⟨hlt, fun K hK hKH => ?_⟩
    by_contra hne
    exact (lt_irrefl _) (lt_of_lt_of_le hK (key K ((le_inf hTH hTM).trans hK.le) (lt_of_le_of_ne hKH hne)))
  ext N
  simp only [maxOver, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hTN⟩
    have hNle : N ≤ H ⊓ M := key N hTN hN.1
    by_contra hne
    exact (hN.2 (H ⊓ M) (lt_of_le_of_ne hNle hne) inf_le_left) ▸ hlt |>.ne rfl
  · rintro rfl
    exact ⟨hmax, le_inf hTH hTM⟩

theorem IsHStar.mem_uFamHat (T : Sylow 2 G) {M H : Subgroup G}
    (hH : IsHStar (T : Subgroup G) M H) (hTM : (T : Subgroup G) ≤ M)
    (hT : ¬ H ≤ Subgroup.normalizer ((T : Subgroup G) : Set G)) :
    H ∈ uFamHat ⊤ (T : Subgroup G) := by
  have hU := hH.isUniqueMaxOver T hTM
  refine ⟨⟨le_top, lt_of_le_of_ne hH.1.1 fun h => hT (h ▸ Subgroup.le_normalizer), ?_⟩, hT⟩
  rw [hU, Set.ncard_singleton]

omit [Finite G] in
theorem IsHStar.not_le_normalizer {T M H : Subgroup G} (hH : IsHStar T M H)
    (hN : Subgroup.normalizer (T : Set G) ≤ M) : ¬ H ≤ Subgroup.normalizer (T : Set G) :=
  fun h => hH.2.1 (h.trans hN)

omit [Finite G] in
theorem inf_eq_inf_normalizer_of_isTISetIn {H M V U : Subgroup G} (hVM : IsTISetIn V M)
    (hNV : Subgroup.normalizer (V : Set G) ≤ M) (hU1 : U ≠ ⊥) (hUV : U ≤ V)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) :
    H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) ∧
      (¬ H ≤ M ↔ ¬ H ≤ Subgroup.normalizer (V : Set G)) := by
  have h1 : H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) := by
    apply le_antisymm
    · rintro h ⟨hH, hM⟩
      refine ⟨hH, ?_⟩
      by_contra hhV
      have hhV' : h⁻¹ ∉ Subgroup.normalizer (V : Set G) := fun h' => hhV (by simpa using inv_mem h')
      have hTI := hVM.2 h⁻¹ (M.inv_mem hM) hhV'
      apply hU1
      rw [eq_bot_iff, ← hTI]
      intro u hu
      refine ⟨hUV hu, ?_⟩
      show u ∈ conjSubgroup V h⁻¹
      rw [mem_conjSubgroup_iff]
      have h2 : h⁻¹ * u * h⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hHU (H.inv_mem hH)) u).mp hu
      simpa using hUV h2
    · exact inf_le_inf_left H hNV
  refine ⟨h1, ⟨fun hHM hHN => hHM (hHN.trans hNV), fun hHN hHM => hHN ?_⟩⟩
  intro h hh
  have : h ∈ H ⊓ M := ⟨hh, hHM hh⟩
  rw [h1] at this
  exact this.2

end CFSG.Quasithin
