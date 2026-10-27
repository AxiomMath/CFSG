module

public import CFSG.Quasithin.H13.A6S13821a
public import CFSG.Quasithin.H13.A6S13821b
public import CFSG.Quasithin.H13.A6S1372L76X
public import CFSG.Quasithin.H13.L32AC47a
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.Quasithin.EmptyFaithful.T1515eE

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped commutatorElement

theorem commutatorElement_mul_center_left {X : Type*} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (c y : X) : ⁅z * c, y⁆ = ⁅c, y⁆ := by
  have h := Subgroup.mem_center_iff.mp hz
  simp only [commutatorElement_def]
  have h1 : z * c * y * (z * c)⁻¹ = c * y * c⁻¹ := by
    calc z * c * y * (z * c)⁻¹ = z * (c * y * c⁻¹) * z⁻¹ := by group
      _ = (c * y * c⁻¹) * z * z⁻¹ := by rw [← h (c * y * c⁻¹)]
      _ = c * y * c⁻¹ := by group
  rw [h1]

theorem center_eq_bot_of_coprime {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hcop : Nat.Coprime (Nat.card (Subgroup.center X)) (Subgroup.center X).index) :
    Subgroup.center X = ⊥ := by
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcomm : commutator X ≤ C := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨⟨z₁, c₁⟩, rfl⟩ := hC.surjective x
    obtain ⟨⟨z₂, c₂⟩, rfl⟩ := hC.surjective y
    show ⁅(z₁ : X) * c₁, (z₂ : X) * c₂⁆ ∈ C
    rw [commutatorElement_mul_center_left z₁.2, ← commutatorElement_inv,
      commutatorElement_mul_center_left z₂.2, commutatorElement_inv]
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem c₁.2 c₂.2) (C.inv_mem c₁.2)) (C.inv_mem c₂.2)
  rw [Group.IsPerfect.commutator_eq_top] at hcomm
  have hd : Subgroup.center X ⊓ C = ⊥ := disjoint_iff.mp hC.disjoint
  exact le_bot_iff.mp (hd ▸ le_inf le_rfl (le_top.trans hcomm))

noncomputable def quotCenterEquivOfBot {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    (X ⧸ Subgroup.center X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

noncomputable def quotCenterCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem index_center_eq {X : Type*} [Group X] :
    (Subgroup.center X).index = Nat.card (X ⧸ Subgroup.center X) := rfl

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem lem13821_list
    (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (h20 : Lem13820)
    (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hHat6 : ¬ IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 6)))
    (hHat7 : ¬ IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7)))
    (hM22 : ¬ IsSporadic .M22 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHatM22 : ¬ IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    (hL32 : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) → S.L1 ≤ K) :
    S.L1 ≤ K ∧
      (IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSL 4 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
        IsPSL 5 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsAlt 6 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
        IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSU 3 3 1 (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  set Q := ↥K ⧸ CFSG.pCore 2 ↥K with hQ
  obtain ⟨hq, hlist, hZ, hSz⟩ :=
    S.lem13817 h16 h36c h36 h37 h38 h139 h1334 h13 hD310 hD391 hI4 hS hH hK
  have hperf : Group.IsPerfect Q := hq.1
  have hZodd : Odd (Nat.card (Subgroup.center Q)) :=
    L32A.C.odd_card_center_of_pCore_eq_bot CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨E⟩ := S.kst_equiv hS hH hK
  have hLie : ∀ n, 2 ≤ n → (IsPSL 2 2 n (Q ⧸ Subgroup.center Q) ∨
      IsPSL 3 2 n (Q ⧸ Subgroup.center Q) ∨ IsPSU 3 2 n (Q ⧸ Subgroup.center Q) ∨
      IsPSp4 2 n (Q ⧸ Subgroup.center Q) ∨ IsG2 2 n (Q ⧸ Subgroup.center Q)) → False := by
    intro n hn h
    have ec := quotCenterCongr E
    apply h20 G T L V S hS H hH K hK n hn
    rcases h with h | h | h | h | h
    · exact Or.inl (IsPSL.of_mulEquiv ec h)
    · exact Or.inr (Or.inl (IsPSL.of_mulEquiv ec h))
    · exact Or.inr (Or.inr (Or.inl (IsPSU.of_mulEquiv ec h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (IsPSp4.of_mulEquiv ec h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (IsG2.of_mulEquiv ec h))))
  have hl1 : ∀ (X : Type) [Group X] [Finite X], Nonempty (Q ≃* X) → A318Exclusion X →
      S.L1 ≤ K := by
    intro X _ _ ⟨eX⟩ hX
    exact S.L1_le_of_quotEquiv hF318 h36 h38 hH hK eX hX
  rcases hlist with ⟨n, hn, h | h | h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | h | h | h |
      h | h
  · exact (hLie n hn (Or.inl h)).elim
  ·
    exfalso
    have hcop : Nat.Coprime (Nat.card (Subgroup.center Q)) (Subgroup.center Q).index := by
      rcases hZ with hb | h3
      · rw [hb, Subgroup.card_bot]
        exact Nat.coprime_one_left _
      · rw [h3, index_center_eq]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          (CFSG.RankThree.PartTwo.KFacts.KP7.three_not_dvd_card h)
    have hb := center_eq_bot_of_coprime hcop
    exact hSz ⟨n, isSz_congr (quotCenterEquivOfBot hb) h⟩
  · exact (hLie n hn (Or.inr (Or.inr (Or.inl h)))).elim
  ·
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact (hLie n hn1 (Or.inr (Or.inl h))).elim
    · obtain rfl : n = 1 := le_antisymm hn1 hn
      have hP : IsPSL 3 2 1 Q :=
        IsPSL.of_mulEquiv (quotCenterEquivOfBot
          (L32A.C.center_eq_bot_of_psl_two hperf h hZodd)) h
      exact ⟨hL32 hP, Or.inl hP⟩
  · exact (hLie n hn (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
  ·
    rcases hZ with hb | h3
    · have hA : IsAlt 6 Q := IsAlt.of_mulEquiv (quotCenterEquivOfBot hb) h
      exact ⟨hl1 _ hA a318Exclusion_alt6, Or.inr (Or.inr (Or.inr (Or.inl hA)))⟩
    · exact (hHat6 ⟨hq, h3, h⟩).elim
  · exact (hLie n hn (Or.inr (Or.inr (Or.inr (Or.inr h))))).elim
  ·
    have hU : IsPSU 3 3 1 Q :=
      IsPSU.of_mulEquiv (quotCenterEquivOfBot
        (L32A.C.center_eq_bot_of_psu_three_three hperf h hZodd)) h
    exact ⟨hl1 _ ⟨MulEquiv.refl _⟩
      (a318Exclusion_u33 (fun _ _ _ hX => two_le_pRank_of_isPSU_three_three1515e hX) hU),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hU))))⟩
  ·
    have hP : IsPSL 4 2 1 Q :=
      IsPSL.of_mulEquiv (quotCenterEquivOfBot
        (L32A.C.center_eq_bot_of_psl_two hperf h hZodd)) h
    exact ⟨hl1 _ ⟨MulEquiv.refl _⟩ (a318Exclusion_psl42 A6L76X.l34NotL42 hP),
      Or.inr (Or.inl hP)⟩
  ·
    have hP : IsPSL 5 2 1 Q :=
      IsPSL.of_mulEquiv (quotCenterEquivOfBot
        (L32A.C.center_eq_bot_of_psl_two hperf h hZodd)) h
    exact ⟨hl1 _ ⟨MulEquiv.refl _⟩ (a318Exclusion_psl52 hP), Or.inr (Or.inr (Or.inl hP))⟩
  ·
    rcases hZ with hb | h3
    · have hA : IsAlt 7 Q := IsAlt.of_mulEquiv (quotCenterEquivOfBot hb) h
      exact ⟨hl1 _ hA a318Exclusion_alt7, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA))))⟩
    · exact (hHat7 ⟨hq, h3, h⟩).elim
  ·
    rcases hZ with hb | h3
    · exact (hM22 (IsSporadic.of_mulEquiv (quotCenterEquivOfBot hb) h)).elim
    · exact (hHatM22 ⟨hq, h3, h⟩).elim

end Setting4

end CFSG.Quasithin.H13.A6
