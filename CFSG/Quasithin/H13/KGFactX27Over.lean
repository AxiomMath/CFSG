module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.Vol2.KGFactAutSylowM12
public import CFSG.Quasithin.Vol2.KGFactAutSylowM22
public import CFSG.Quasithin.Vol2.F134U33Native
public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.Quasithin.EmptyFaithful.S146zYFSJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabM12
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Ru
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransBase
import all CFSG.Blueprint.NativeSporadic
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.Quasithin.Background.A3Structure313SL2
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB

public section

namespace CFSG.Quasithin.H13.KGX27

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Blueprint
open CFSG.Assembly.LowTwoRank

@[expose] def NoIndexOvergroup (c : ℕ) (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], F X → ∀ H S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index →
    S ≤ H → Nat.card H = c * Nat.card S → False

theorem noIndexOvergroup_of_not_dvd {c : ℕ} {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X] [Finite X], F X → ¬ c ∣ Nat.card X) : NoIndexOvergroup c F := by
  intro X _ _ hX H S _ _ _ hH
  apply hF X hX
  exact (Dvd.intro _ hH.symm).trans (Subgroup.card_subgroup_dvd_card H)

theorem card_sylow_of_card {X : Type} [Group X] [Finite X] {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) {k m : ℕ} (hX : Nat.card X = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    Nat.card S = 2 ^ k :=
  CFSG.QuasithinUnique.A5.G3.card_eq_of_odd_index hS2 hSi hX hm

theorem noIndexOvergroup_of_model {Γ : Type} [Group Γ] [Finite Γ] {S₀ : Subgroup Γ}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {c : ℕ}
    (hall : ∀ Z : Subgroup Γ, S₀ ≤ Z → Nat.card Z = c * Nat.card S₀ → False)
    {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X] [Finite X], F X → Nonempty (X ≃* Γ)) :
    NoIndexOvergroup c F := by
  intro X _ _ hX H S hS2 hSi hSH hH
  obtain ⟨e⟩ := hF X hX
  obtain ⟨ψ, hψ⟩ := CFSG.Quasithin.J4Loc.sylow_transport hS₀ e
    (K1.isSylowTwoOf_top_iff.mpr ⟨hS2, hSi⟩)
  refine hall (H.map (ψ : X →* Γ)) (hψ ▸ Subgroup.map_mono hSH) ?_
  rw [Subgroup.card_map_of_injective ψ.injective, hH, ← hψ,
    Subgroup.card_map_of_injective ψ.injective]

theorem no_index_of_members {Γ : Type} [Group Γ] [Finite Γ] {S₀ : Subgroup Γ} {N s c : ℕ}
    (Y : ℕ → Subgroup Γ) (L : Array ℕ)
    (hall : ∀ Z : Subgroup Γ, S₀ ≤ Z → ∃ j ≤ N, Z = memberOrTop N Y j)
    (hS₀ : Nat.card S₀ = s) (hY : ∀ j < N, Nat.card (Y j) = L[j]! * s)
    (hc : ∀ j < N, L[j]! ≠ c) (hΓ : Nat.card Γ ≠ c * s) :
    ∀ Z : Subgroup Γ, S₀ ≤ Z → Nat.card Z = c * Nat.card S₀ → False := by
  intro Z hSZ hZ
  rw [hS₀] at hZ
  have hs : 0 < s := hS₀ ▸ Nat.card_pos
  obtain ⟨j, -, rfl⟩ := hall Z hSZ
  by_cases hjN : j < N
  · rw [memberOrTop, ite_eq_left hjN, hY j hjN] at hZ
    exact hc j hjN (Nat.eq_of_mul_eq_mul_right hs hZ)
  · rw [memberOrTop, ite_eq_right hjN, Subgroup.card_top] at hZ
    exact hΓ hZ

theorem noIndexOvergroup_m12
    {c : ℕ} (hc : c = 9 ∨ c = 27) :
    NoIndexOvergroup c fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M12) := by
  intro X _ _ ⟨e⟩ H S hS2 hSi hSH hH
  have hc0 : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  have hXc : Nat.card X = 2 ^ 6 * 1485 := by
    rw [Nat.card_congr e.toEquiv, hc0]
    norm_num
  have hSc := card_sylow_of_card hS2 hSi hXc (by decide)
  rcases CFSG.Quasithin.H13.KGSporLat.m12_overgroups ⟨e⟩
      (K1.isSylowTwoOf_top_iff.mpr ⟨hS2, hSi⟩) hSH with htop | ⟨m, hm, hmc, -⟩
  · rw [htop, Subgroup.card_top, hXc, hSc] at hH
    rcases hc with rfl | rfl <;> norm_num at hH
  · rw [hH, hSc] at hmc
    simp only [CFSG.Quasithin.H13.KGSporLat.m12Mems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num at hmc

theorem noIndexOvergroup_m24 :
    NoIndexOvergroup 27 fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M24) := by
  intro X _ _ ⟨e⟩ H S hS2 hSi hSH hH
  have hc0 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  have hXc : Nat.card X = 2 ^ 10 * 239085 := by
    rw [Nat.card_congr e.toEquiv, hc0]
    norm_num
  have hSc := card_sylow_of_card hS2 hSi hXc (by decide)
  rcases M24.m24_overgroups ⟨e⟩ (K1.isSylowTwoOf_top_iff.mpr ⟨hS2, hSi⟩) hSH with
    htop | ⟨m, hm, hmc, -⟩
  · rw [htop, Subgroup.card_top, hXc, hSc] at hH
    norm_num at hH
  · rw [hH, hSc] at hmc
    simp only [M24.m24Mems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hmc

theorem noIndexOvergroup_j2 :
    NoIndexOvergroup 27 fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .J2) := by
  intro X _ _ ⟨e⟩ H S hS2 hSi hSH hH
  have hc0 : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  have hXc : Nat.card X = 2 ^ 7 * 4725 := by
    rw [Nat.card_congr e.toEquiv, hc0]
    norm_num
  have hSc := card_sylow_of_card hS2 hSi hXc (by decide)
  rw [hSc] at hH
  rcases CFSG.Quasithin.S146zY.j2_overgroups ⟨e⟩
      (K1.isSylowTwoOf_top_iff.mpr ⟨hS2, hSi⟩) hSH with htop | h | h | h | h
  · rw [htop, Subgroup.card_top, hXc] at hH
    norm_num at hH
  all_goals rw [hH] at h; norm_num at h

theorem noIndexOvergroup_he :
    NoIndexOvergroup 27 fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .He) := by
  refine noIndexOvergroup_of_model He.he_S_sylow
    (no_index_of_members He.heCtx.Y #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3] He.he_complete
      He.he_card_S He.he_member_card (by decide) ?_) fun X _ _ ⟨e⟩ =>
      ⟨e.trans CFSG.Sporadic.He.heEquivJ⟩
  rw [CFSG.Sporadic.He.card_J]
  norm_num

theorem ru_model (X : Type) [Group X]
    (h : Nonempty (X ≃* NativeSporadic.Carrier .Ru)) :
    Nonempty (X ≃* ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData)) := by
  obtain ⟨e⟩ := h
  have ψ : NativeSporadic.Ru ≃* CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData :=
    CFSG.Sporadic.SmallF2.seedEquiv Ru.ru_facts.toBaseFacts
  have e' : X ≃* NativeSporadic.Ru := e
  exact ⟨e'.trans ψ⟩

theorem noIndexOvergroup_ru
    {c : ℕ} (hc : c = 9 ∨ c = 27) :
    NoIndexOvergroup c fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .Ru) := by
  refine noIndexOvergroup_of_model Ru.ru_S_sylow
    (no_index_of_members Ru.ruCtx.Y #[1, 15, 21, 3, 3] Ru.ru_complete Ru.ru_card_S
      Ru.ru_member_card (by rcases hc with rfl | rfl <;> decide) ?_) fun X _ _ h => ru_model X h
  rw [Ru.ru_card]
  rcases hc with rfl | rfl <;> norm_num

theorem noIndexOvergroup_m22 :
    NoIndexOvergroup 9 fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M22) := by
  intro X _ _ ⟨e⟩ H S hS2 hSi hSH hH
  have hc0 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  have hXc : Nat.card X = 2 ^ 7 * 3465 := by
    rw [Nat.card_congr e.toEquiv, hc0]
    norm_num
  have hSc := card_sylow_of_card hS2 hSi hXc (by decide)
  rcases CFSG.Quasithin.H13.KGSporLat.m22_overgroups ⟨e⟩
      (K1.isSylowTwoOf_top_iff.mpr ⟨hS2, hSi⟩) hSH with htop | ⟨m, hm, hmc, -⟩
  · rw [htop, Subgroup.card_top, hXc, hSc] at hH
    norm_num at hH
  · rw [hH, hSc] at hmc
    simp only [CFSG.Quasithin.H13.KGSporLat.m22Mems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num at hmc

theorem noIndexOvergroup_card_360 {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X] [Finite X], F X → IsSimpleGroup X ∧ Nat.card X = 360) :
    NoIndexOvergroup 9 F := by
  intro X _ _ hX H S hS2 hSi _ hH
  obtain ⟨hs, hXc⟩ := hF X hX
  have hXc' : Nat.card X = 2 ^ 3 * 45 := by
    rw [hXc]
    norm_num
  have hSc := card_sylow_of_card hS2 hSi hXc' (by decide)
  rw [hSc] at hH
  exact CFSG.Quasithin.F134.card_ne_seventytwo hXc H (by rw [hH]; norm_num)

theorem noIndexOvergroup_psu3_three
    {c : ℕ} (hc : c = 9 ∨ c = 27) :
    NoIndexOvergroup c fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 3 1 := by
  intro X _ _ hX H S hS2 hSi hSH hH
  have : Finite U33G := Nat.finite_of_card_ne_zero (by rw [card_u33Pres]; norm_num)
  obtain ⟨ePres⟩ := u33Pres_mulEquiv_PSU3
  obtain ⟨e⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel
    (Or.inl ⟨by decide, hX⟩ : CFSG.Blueprint.LieModel X .PSU 3 3 1)
  set φ : X ≃* U33G := e.trans ePres.symm
  have hS2' : IsPGroup 2 ↥(S.map φ.toMonoidHom) := hS2.map _
  have hSi' : ¬ 2 ∣ (S.map φ.toMonoidHom).index := by
    have := Subgroup.index_map_equiv S φ
    erw [this]
    exact hSi
  obtain ⟨hcS, hcH⟩ := CFSG.Quasithin.F134.card_eq_of_overgroupData u33Data u33_syl.1 u33_syl.2
    hS2' hSi' (Subgroup.map_mono hSH)
  rw [Subgroup.card_map_of_injective φ.injective, u33_card_T] at hcS
  rw [Subgroup.card_map_of_injective φ.injective, hH, hcS, u33_card_T] at hcH
  have hA := CFSG.Quasithin.F134.card_u33_A_le
  have hB := CFSG.Quasithin.F134.card_u33_B_le
  rw [card_u33Pres] at hcH
  rcases hc with rfl | rfl <;> omega

end CFSG.Quasithin.H13.KGX27
