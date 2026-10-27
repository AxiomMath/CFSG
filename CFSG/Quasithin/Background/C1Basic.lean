module

public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

@[expose] def IsTwoRadicalIn (H R : Subgroup G) : Prop :=
  R ≤ H ∧ R ≠ ⊥ ∧ R = pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G))

@[expose] def SatisfiesPU (H R : Subgroup G) : Prop :=
  IsTwoRadicalIn H R ∧ ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
    ¬ H ≤ Subgroup.normalizer (C : Set G)

@[expose] def cgsIn (H S : Subgroup G) : Subgroup G :=
  ⨆ (C : Subgroup G) (_ : C ≤ S) (_ : C ≠ ⊥) (_ : (C.subgroupOf S).Characteristic),
    H ⊓ Subgroup.normalizer (C : Set G)

@[expose] def SatisfiesCPU (H R M : Subgroup G) : Prop :=
  cgsIn H R ≤ M ∧ M < H ∧ IsTwoRadicalIn H R ∧ ¬ 2 ∣ R.relIndex (conjClosure R M)

theorem cgsIn_top (S : Subgroup G) : cgsIn ⊤ S = CGS S := by
  unfold cgsIn CGS
  simp only [top_inf_eq]

theorem cgsIn_le (H S : Subgroup G) : cgsIn H S ≤ H :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left

theorem inf_normalizer_le_cgsIn {H S : Subgroup G} (hS : S ≠ ⊥) :
    H ⊓ Subgroup.normalizer (S : Set G) ≤ cgsIn H S := by
  have hchar : (S.subgroupOf S).Characteristic := by
    rw [Subgroup.subgroupOf_self]; infer_instance
  exact le_iSup_of_le S (le_iSup_of_le le_rfl (le_iSup_of_le hS (le_iSup_of_le hchar le_rfl)))

variable [Finite G]

theorem IsTwoRadicalIn.isPGroup {H R : Subgroup G} (h : IsTwoRadicalIn H R) : IsPGroup 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.2.2]
  exact pCoreOf_isPGroup 2 _

omit [Finite G] in
theorem le_pCoreOf_inf_normalizer {H R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R) :
    R ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) :=
  le_pCoreOf_of_le_normalizer 2 (le_inf hRH Subgroup.le_normalizer) inf_le_right hR

theorem isTwoRadicalIn_of_sylow {H R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R)
    (hodd : ¬ 2 ∣ R.relIndex H) (hR1 : R ≠ ⊥) : IsTwoRadicalIn H R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hRH, hR1, le_antisymm (le_pCoreOf_inf_normalizer hRH hR) ?_⟩
  set N := H ⊓ Subgroup.normalizer (R : Set G)
  have hRN : R ≤ N := le_inf hRH Subgroup.le_normalizer
  have hP : IsPGroup 2 (pCoreOf 2 N) := pCoreOf_isPGroup 2 N
  have hle : R ≤ pCoreOf 2 N := le_pCoreOf_inf_normalizer hRH hR
  have hPH : pCoreOf 2 N ≤ H := (pCoreOf_le 2 N).trans inf_le_left
  have hdvd : R.relIndex (pCoreOf 2 N) ∣ R.relIndex H :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex R (pCoreOf 2 N) H hle hPH)
  obtain ⟨k, hk⟩ := (hP.to_le le_rfl).index (R.subgroupOf (pCoreOf 2 N))
  have h1 : R.relIndex (pCoreOf 2 N) = 1 := by
    rcases k with _ | k
    · simpa [Subgroup.relIndex] using hk
    · exfalso
      apply hodd
      exact dvd_trans (by rw [Subgroup.relIndex, hk]; exact dvd_pow_self 2 (Nat.succ_ne_zero k))
        hdvd
  exact Subgroup.relIndex_eq_one.mp h1

theorem exists_isTwoRadicalIn_ge {H R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) :
    ∃ B : Subgroup G, IsTwoRadicalIn H B ∧ R ≤ B ∧
      H ⊓ Subgroup.normalizer (R : Set G) ≤ H ⊓ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, ⟨hBH, hBp, hRB, hNB⟩, hmax⟩ := Set.exists_max_image
    {B : Subgroup G | B ≤ H ∧ IsPGroup 2 B ∧ R ≤ B ∧
      H ⊓ Subgroup.normalizer (R : Set G) ≤ H ⊓ Subgroup.normalizer (B : Set G)}
    (fun B => Nat.card B) (Set.toFinite _) ⟨R, hRH, hR, le_rfl, le_rfl⟩
  refine ⟨B, ⟨hBH, fun h => hR1 (le_bot_iff.mp (h ▸ hRB)), ?_⟩, hRB, hNB⟩
  set N := H ⊓ Subgroup.normalizer (B : Set G)
  have hle : B ≤ pCoreOf 2 N := le_pCoreOf_inf_normalizer hBH hBp
  have hPH : pCoreOf 2 N ≤ H := (pCoreOf_le 2 N).trans inf_le_left
  have hNP : N ≤ H ⊓ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    le_inf inf_le_left (le_normalizer_pCoreOf 2 N)
  have hcard := hmax (pCoreOf 2 N) ⟨hPH, pCoreOf_isPGroup 2 N, hRB.trans hle, hNB.trans hNP⟩
  exact Subgroup.eq_of_le_of_card_ge hle hcard

omit [Finite G] in
theorem isTwoRadicalIn_of_le_of_normalizer_le {H K R : Subgroup G} (hHK : H ≤ K)
    (hR : IsTwoRadicalIn H R) (hN : K ⊓ Subgroup.normalizer (R : Set G) ≤ H) :
    IsTwoRadicalIn K R := by
  refine ⟨hR.1.trans hHK, hR.2.1, ?_⟩
  have heq : K ⊓ Subgroup.normalizer (R : Set G) = H ⊓ Subgroup.normalizer (R : Set G) :=
    le_antisymm (le_inf hN inf_le_right) (inf_le_inf_right _ hHK)
  rw [heq]
  exact hR.2.2

end CFSG.Quasithin
