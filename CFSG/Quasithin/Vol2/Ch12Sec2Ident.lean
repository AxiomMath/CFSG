module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.Quasithin.SteinbergBMCoreQuotientCenterOdd
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

theorem ker_eq_bot_of_perfect_of_split {E : Type*} [Group E] [Group.IsPerfect E]
    {C R : Subgroup E} (hC : C ≤ Subgroup.center E) (e : ↥C × ↥R ≃* E) : C = ⊥ := by
  have hperf : Group.IsPerfect ↥C :=
    Group.IsPerfect.ofSurjective (f := (MonoidHom.fst ↥C ↥R).comp e.symm.toMonoidHom)
      (Prod.fst_surjective.comp e.symm.surjective)
  have hcomm : IsMulCommutative ↥C :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hC b.2) a)⟩⟩
  have : Subsingleton ↥C := Group.IsPerfect.subsingleton_of_isMulCommutative
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have := Subsingleton.elim (⟨x, hx⟩ : ↥C) 1
  exact congrArg Subtype.val this

theorem injective_of_quasisimple_of_split {Q H : Type*} [Group Q] [Finite Q] [Group H]
    (hQ : CFSG.IsQuasisimple Q) (hodd : Odd (Nat.card (Subgroup.center Q))) (φ : Q →* H)
    (hφ : Function.Surjective φ) (hH : ∃ h : H, h ≠ 1)
    (hsplit : φ.ker ≤ Subgroup.center Q → Odd (Nat.card φ.ker) →
      ∃ R : Subgroup Q, Nonempty (↥φ.ker × ↥R ≃* Q)) :
    Function.Injective φ := by
  have : Group.IsPerfect Q := hQ.1
  have hcen : φ.ker ≤ Subgroup.center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ φ.normal_ker with h | h
    · exfalso
      obtain ⟨y, hy⟩ := hH
      obtain ⟨q, rfl⟩ := hφ y
      exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top q))
    · exact h
  have hoddk : Odd (Nat.card φ.ker) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hcen
    rw [hk] at hodd
    exact Nat.Odd.of_mul_left hodd
  obtain ⟨R, ⟨e⟩⟩ := hsplit hcen hoddk
  exact (MonoidHom.ker_eq_bot_iff φ).mp (ker_eq_bot_of_perfect_of_split hcen e)

theorem exists_ne_one_sl {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) K, g ≠ 1 := by
  refine ⟨Matrix.SpecialLinearGroup.transvection
    (show (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ by simp [Fin.ext_iff]) (1 : K), fun h1 => ?_⟩
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin n) K =>
    (M : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨1, by omega⟩) h1
  simp [Matrix.SpecialLinearGroup.transvection_coe, Fin.ext_iff] at this

theorem injective_of_quasisimple_of_sl_char_two
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (hodd : Odd (Nat.card (Subgroup.center Q))) {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (φ : Q →* Matrix.SpecialLinearGroup (Fin n) K) (hφ : Function.Surjective φ) :
    Function.Injective φ :=
  injective_of_quasisimple_of_split hQ hodd φ hφ (exists_ne_one_sl hn) fun hcen hoddk => by
    obtain ⟨s, -, -, e, -⟩ :=
      CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting hn hφ hcen hoddk
    exact ⟨s.range, ⟨e⟩⟩

section Action

variable {G : Type} [Group G] {L V : Subgroup G}

noncomputable def autOnSurj (hLV : L ≤ Subgroup.normalizer (V : Set G)) : ↥L →* ↥(autOn L V) :=
  (A4.actionOn V L hLV).codRestrict (autOn L V) fun l => (A4.mem_autOn_iff hLV).mpr ⟨l, rfl⟩

theorem autOnSurj_surjective (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (autOnSurj hLV) := by
  rintro ⟨a, ha⟩
  obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
  exact ⟨l, rfl⟩

theorem mem_ker_autOnSurj (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) :
    l ∈ (autOnSurj hLV).ker ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (A4.actionOn_eq_one_iff hLV l).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((A4.actionOn_eq_one_iff hLV l).mpr h)

theorem ker_autOnSurj (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    (autOnSurj hLV).ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
  ext l
  rw [mem_ker_autOnSurj, Subgroup.mem_subgroupOf]

noncomputable def autOnQuot (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) :
    ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autOn L V) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥L) (autOnSurj hLV) fun l hl => by
    rw [mem_ker_autOnSurj]
    apply hO2
    exact ⟨l, hl, rfl⟩

theorem autOnQuot_mk (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) (l : ↥L) :
    autOnQuot hLV hO2 (QuotientGroup.mk l) = autOnSurj hLV l := by
  simp [autOnQuot]

theorem autOnQuot_surjective (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) :
    Function.Surjective (autOnQuot hLV hO2) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (autOnSurj_surjective hLV) _

theorem nonempty_quot_mulEquiv_sl_of_autOn
    [Finite G]
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (e : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin n) K) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) K) := by
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
  set φ := e.toMonoidHom.comp (autOnQuot hLV hO2) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (autOnQuot_surjective hLV hO2)
  exact ⟨MulEquiv.ofBijective φ ⟨injective_of_quasisimple_of_sl_char_two hq hodd hn φ hφs, hφs⟩⟩

theorem isQuasisimple_autOn_of_pCoreOf_le (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hnc : ¬ L ≤ Subgroup.centralizer (V : Set G)) : CFSG.IsQuasisimple ↥(autOn L V) := by
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq (autOnQuot_surjective hLV hO2) ?_
  obtain ⟨l, hl, hlc⟩ := Set.not_subset.mp hnc
  refine ⟨QuotientGroup.mk ⟨l, hl⟩, fun h1 => hlc ?_⟩
  have h2 : autOnSurj hLV ⟨l, hl⟩ = 1 := h1
  exact (mem_ker_autOnSurj hLV ⟨l, hl⟩).mp h2

end Action

end CFSG.Quasithin.H13
