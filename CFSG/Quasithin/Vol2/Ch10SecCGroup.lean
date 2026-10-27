module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open

variable {G : Type*} [Group G]

theorem isPerfect_of_commutator_eq {K : Subgroup G} (hK : ⁅K, K⁆ = K) : Group.IsPerfect ↥K := by
  refine ⟨?_⟩
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_subtype_commutator, hK, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_eq_bot_of_isPerfect_of_isSolvable {X Y : Type*} [Group X] [Group Y]
    [Group.IsSolvable Y] (f : X →* Y) (K : Subgroup X) [hK : Group.IsPerfect ↥K] :
    K.map f = ⊥ := by
  by_contra hne
  have : Nontrivial ↥(K.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hperf : Group.IsPerfect ↥(K.map f) :=
    Group.IsPerfect.ofSurjective (f.subgroupMap_surjective K)
  have hsol : Group.IsSolvable ↥(K.map f) :=
    Group.isSolvable_of_isSolvable_injective (K.map f).subtype_injective
  exact Group.IsPerfect.not_isSolvable ↥(K.map f) hsol

variable [Finite G]

theorem le_of_perfect_of_le_sup_of_isPGroup {p : ℕ} [Fact p.Prime] {K L P : Subgroup G}
    (hn : L ⊔ P ≤ Subgroup.normalizer (L : Set G)) (hP : IsPGroup p P) (hK : ⁅K, K⁆ = K)
    (hKle : K ≤ L ⊔ P) : K ≤ L := by
  set X : Subgroup G := L ⊔ P with hX
  have hLX : L ≤ X := le_sup_left
  have hPX : P ≤ X := le_sup_right
  have : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hn
  set π := QuotientGroup.mk' (L.subgroupOf X)
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion hPX)) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf X) z
    have hPn : P ≤ Subgroup.normalizer (L : Set G) := hPX.trans hn
    have hx : (x : G) ∈ (↑(P ⊔ L) : Set G) := by rw [sup_comm]; exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P L hPn] at hx
    obtain ⟨q, hq, l, hl, hql⟩ := hx
    refine ⟨⟨q, hq⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hPX ⟨q, hq⟩)⁻¹ * x : ↥X) = (l : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hql]
      group
    rw [this]
    exact hl
  have hpq : IsPGroup p (↥X ⧸ L.subgroupOf X) := hP.of_surjective _ hsurj
  have : Group.IsNilpotent (↥X ⧸ L.subgroupOf X) := hpq.isNilpotent
  have : Group.IsPerfect ↥K := isPerfect_of_commutator_eq hK
  have : Group.IsPerfect ↥(K.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKle).symm.surjective
  have hbot := map_eq_bot_of_isPerfect_of_isSolvable π (K.subgroupOf X)
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  have : (⟨k, hKle hk⟩ : ↥X) ∈ L.subgroupOf X := hbot hk
  exact this

theorem le_pCoreOf_or_eq_of_normal {X N : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hsimp : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X)) (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) : N ≤ pCoreOf 2 X ∨ N = X := by
  have hNn : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hmap : ((N.subgroupOf X).map π).Normal :=
    Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimp _ hmap with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    intro n hn
    have hmem : (⟨n, hNX hn⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := h hn
    exact ⟨⟨n, hNX hn⟩, hmem, rfl⟩
  · right
    refine le_antisymm hNX (le_of_perfect_of_le_sup_of_isPGroup (p := 2) (P := pCoreOf 2 X)
      ((sup_le hNX (CFSG.LieType.BorelTits.pCoreOf_le 2 X)).trans hXN)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hX ?_)
    intro x hx
    have hmem : π ⟨x, hx⟩ ∈ (N.subgroupOf X).map π := by rw [h]; trivial
    obtain ⟨n, hn, hnx⟩ := hmem
    have hc : n⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq (s := CFSG.pCore 2 ↥X)).mp hnx
    have hc' : (n : G)⁻¹ * x ∈ pCoreOf 2 X := ⟨_, hc, rfl⟩
    have : x = (n : G) * ((n : G)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hc')

omit [Finite G] in
theorem le_normalizer_inf' {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (hA hg) h, Subgroup.mem_normalizer_iff.mp (hB hg) h]

omit [Finite G] in
theorem le_normalizer_sup {X L O : Subgroup G} (hL : X ≤ Subgroup.normalizer (L : Set G))
    (hO : X ≤ Subgroup.normalizer (O : Set G)) :
    X ≤ Subgroup.normalizer ((L ⊔ O : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup L O ⟨hL hg, hO hg⟩

theorem le_of_le_sup_of_le_centralizer {A L K : Subgroup G} {x : G}
    (hLn : L ⊔ A ≤ Subgroup.normalizer (L : Set G))
    (hAn : L ⊔ A ≤ Subgroup.normalizer (A : Set G))
    (hAperf : ⁅A, A⁆ = A) (hAsimp : IsSimpleGroup (↥A ⧸ CFSG.pCore 2 ↥A))
    (hKperf : ⁅K, K⁆ = K) (hKsimp : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hidx : (pCoreOf 2 K).relIndex K = (pCoreOf 2 A).relIndex A)
    (hLx : L ≤ Subgroup.centralizer {x}) (hOx : pCoreOf 2 A ≤ Subgroup.centralizer {x})
    (hAx : ¬ A ≤ Subgroup.centralizer {x})
    (hKle : K ≤ L ⊔ A) (hKx : K ≤ Subgroup.centralizer {x}) : K ≤ L := by
  set O := pCoreOf 2 A with hO
  set N : Subgroup G := L ⊔ O with hN
  set X : Subgroup G := L ⊔ A with hX
  have hOA : O ≤ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A
  have hOX : O ≤ X := hOA.trans le_sup_right
  have hNX : N ≤ X := sup_le le_sup_left hOX
  have hOn : X ≤ Subgroup.normalizer (O : Set G) :=
    hAn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)
  have hNn : X ≤ Subgroup.normalizer (N : Set G) := le_normalizer_sup hLn hOn
  have hAL : A ⊓ L ≤ O := by
    rcases le_pCoreOf_or_eq_of_normal hAperf hAsimp inf_le_left
        (le_normalizer_inf' (le_sup_right.trans hAn) (le_sup_right.trans hLn)) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right.trans hLx) hAx
  have hAN : A ⊓ N ≤ O := by
    rintro a ⟨haA, haN⟩
    have hOnL : O ≤ Subgroup.normalizer (L : Set G) := hOX.trans hLn
    have ha : a ∈ (↑(O ⊔ L) : Set G) := by rw [sup_comm]; exact haN
    rw [Subgroup.coe_mul_of_left_le_normalizer_right O L hOnL] at ha
    obtain ⟨o, ho, l, hl, rfl⟩ := ha
    have hlA : l ∈ A := by simpa using A.mul_mem (A.inv_mem (hOA ho)) haA
    exact O.mul_mem ho (hAL ⟨hlA, hl⟩)
  by_contra hKL
  have hKN : ¬ K ≤ N := fun h => hKL (le_of_perfect_of_le_sup_of_isPGroup (p := 2) (P := O)
    (hNX.trans hLn) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A) hKperf h)
  have hKNO : K ⊓ N ≤ pCoreOf 2 K := by
    rcases le_pCoreOf_or_eq_of_normal hKperf hKsimp inf_le_left
        (le_normalizer_inf' Subgroup.le_normalizer (hKle.trans hNn)) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hKN
  set CA : Subgroup G := A ⊓ Subgroup.centralizer {x} with hCA
  have hCAA : CA < A := lt_of_le_of_ne inf_le_left (fun h => hAx (h ▸ inf_le_right))
  have hCAX : CA ≤ X := inf_le_left.trans le_sup_right
  have hOCA : O ≤ CA := le_inf hOA hOx
  have hNCA : N ⊓ CA = O :=
    le_antisymm (fun y hy => hAN ⟨hy.2.1, hy.1⟩) (le_inf le_sup_right hOCA)
  have hNnX : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hNn
  set π := QuotientGroup.mk' (N.subgroupOf X)
  have hcardK : N.relIndex K = Nat.card ((K.subgroupOf X).map π) := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hKle]
  have hcardC : N.relIndex CA = Nat.card ((CA.subgroupOf X).map π) := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hCAX]
  have hle : (K.subgroupOf X).map π ≤ (CA.subgroupOf X).map π := by
    rintro _ ⟨k, hk, rfl⟩
    have hAnL : A ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans hLn
    have hk' : (k : G) ∈ (↑(A ⊔ L) : Set G) := by rw [sup_comm]; exact k.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A L hAnL] at hk'
    obtain ⟨a, ha, l, hl, hal⟩ := hk'
    have hax : a ∈ Subgroup.centralizer {x} := by
      have : a = (k : G) * l⁻¹ := by rw [← hal]; group
      rw [this]
      exact Subgroup.mul_mem _ (hKx hk) (Subgroup.inv_mem _ (hLx hl))
    refine ⟨⟨a, Subgroup.mem_sup_right ha⟩, ⟨ha, hax⟩, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have : (((⟨a, Subgroup.mem_sup_right ha⟩ : ↥X)⁻¹ * k : ↥X) : G) = l := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hal]
      group
    rw [this]
    exact Subgroup.mem_sup_left hl
  have h1 : (pCoreOf 2 K).relIndex K ≤ N.relIndex K := by
    rw [← Subgroup.inf_relIndex_left K N]
    exact Subgroup.relIndex_le_of_le_left hKNO
      (Subgroup.index_ne_zero_of_finite : ((K ⊓ N).subgroupOf K).index ≠ 0)
  have h2 : Nat.card ((K.subgroupOf X).map π) ≤ Nat.card ((CA.subgroupOf X).map π) :=
    Subgroup.card_le_of_le hle
  have h3 : N.relIndex CA = O.relIndex CA := by
    rw [← Subgroup.inf_relIndex_right N CA, hNCA]
  have h4 : O.relIndex CA < O.relIndex A := by
    have e1 := Subgroup.relIndex_mul_card O CA
    have e2 := Subgroup.relIndex_mul_card O A
    rw [inf_of_le_left hOCA] at e1
    rw [inf_of_le_left hOA] at e2
    have hlt : Nat.card CA < Nat.card A := Subgroup.card_lt_of_lt hCAA
    have hpos : 0 < Nat.card O := Nat.card_pos
    by_contra hge
    push Not at hge
    have : O.relIndex A * Nat.card O ≤ O.relIndex CA * Nat.card O :=
      Nat.mul_le_mul_right _ hge
    omega
  omega

end CFSG.Quasithin.Vol2.Ch10.SecC
