module

public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecC8V1
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem comap_pCore_eq' {U V : Type*} [Group U] [Group V] [Finite U] {p : ℕ}
    (f : U →* V) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    (CFSG.pCore p V).comap f = CFSG.pCore p U := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := V)).comap f,
      (CFSG.pCore_isPGroup (p := p) (G := V)).comap_of_ker_isPGroup f hk⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := U)).map f hf,
      (CFSG.pCore_isPGroup (p := p) (G := U)).map f⟩

theorem exists_pCore_quotient_mulEquiv' {U V : Type*} [Group U] [Group V] [Finite U] {p : ℕ}
    (f : U →* V) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    Nonempty ((U ⧸ CFSG.pCore p U) ≃* (V ⧸ CFSG.pCore p V)) := by
  have hg : Function.Surjective ((QuotientGroup.mk' (CFSG.pCore p V)).comp f) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hker : CFSG.pCore p U = ((QuotientGroup.mk' (CFSG.pCore p V)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_pCore_eq' f hf hk]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hg)⟩

variable {J L : Subgroup G} {S : Type*} [Group S]

@[expose] def piL (π : ↥J →* S) (hLJ : L ≤ J) : ↥L →* S := π.comp (Subgroup.inclusion hLJ)

theorem piL_apply (π : ↥J →* S) (hLJ : L ≤ J) (l : ↥L) :
    piL π hLJ l = π ⟨(l : G), hLJ l.2⟩ := rfl

theorem isPGroup_ker_piL (π : ↥J →* S) (hLJ : L ≤ J)
    (hker : ∀ j : ↥J, π j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1) :
    IsPGroup 2 (piL π hLJ).ker := by
  intro l
  obtain ⟨m, hm⟩ := hker ⟨((l : ↥L) : G), hLJ (l : ↥L).2⟩ l.2
  exact ⟨m, Subtype.ext (Subtype.ext (by simpa using hm))⟩

theorem image_quot_equiv [Finite G] (π : ↥J →* S) (hLJ : L ≤ J)
    (hker : ∀ j : ↥J, π j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nonempty (↥(piL π hLJ).range ⧸ CFSG.pCore 2 ↥(piL π hLJ).range ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hk : IsPGroup 2 (piL π hLJ).rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact isPGroup_ker_piL π hLJ hker
  obtain ⟨e⟩ := exists_pCore_quotient_mulEquiv' _ (piL π hLJ).rangeRestrict_surjective hk
  exact ⟨e.symm.trans eL⟩

theorem image_perfect (π : ↥J →* S) (hLJ : L ≤ J) (hLp : ⁅L, L⁆ = L) :
    ⁅(piL π hLJ).range, (piL π hLJ).range⁆ = (piL π hLJ).range := by
  have hL : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hLp]
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hL]

theorem image_isSylowTwoOf {R : Subgroup G} (hR : IsSylowTwoOf R J) (π : ↥J →* S)
    (hπ : Function.Surjective π) : IsSylowTwoOf ((R.subgroupOf J).map π) ⊤ := by
  have hS2 : IsPGroup 2 (R.subgroupOf J) :=
    hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm
  refine ⟨le_top, hS2.map π, ?_⟩
  intro hd
  apply hR.2.2
  have h2 : (((R.subgroupOf J).map π).subgroupOf ⊤).index = ((R.subgroupOf J).map π).index :=
    Subgroup.relIndex_top_right _
  rw [h2] at hd
  exact hd.trans (Subgroup.index_map_dvd _ hπ)

theorem image_pCoreOf_le [Finite G] (π : ↥J →* S) (hLJ : L ≤ J) {o : G}
    (ho : o ∈ pCoreOf 2 L) : piL π hLJ ⟨o, CFSG.LieType.BorelTits.pCoreOf_le 2 L ho⟩ ∈
      pCoreOf 2 (piL π hLJ).range := by
  obtain ⟨o', ho', rfl⟩ := ho
  have h1 : (CFSG.pCore 2 ↥L).map (piL π hLJ).rangeRestrict ≤
      CFSG.pCore 2 ↥(piL π hLJ).range :=
    le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥L)).map _
      (piL π hLJ).rangeRestrict_surjective, (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map _⟩
  have h2 := h1 ⟨o', ho', rfl⟩
  exact ⟨_, h2, rfl⟩

variable [Finite G] {T I : Subgroup G}

theorem case3_or_case5 (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1027 : Stmt10_2_7) (hL : LBarL32 L) : Case10_1_1Three T L I ∨ Case10_1_1Five T L I := by
  obtain ⟨f⟩ := hL
  have h168 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
    rw [Nat.card_congr f.toEquiv, card_SL_three_two]
  rcases (h1011 G T L I hyp).2.2.2 with ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨⟨e⟩, -⟩ | h3 |
    ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | h5 | h6 | ⟨n, hsz, -⟩
  · exact absurd ((Nat.card_congr e.toEquiv).symm.trans h168) (card_SL_two_ne hn hK)
  · have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [Nat.card_congr e.toEquiv, h60] at h168
    norm_num at h168
  · exact Or.inl h3
  · exact absurd ((Nat.card_congr e.toEquiv).symm.trans h168) (card_SL_two_ne (by omega) hK)
  · exact Or.inr h5
  · exact absurd h6 (h1027 G T L I hyp).1
  · exact absurd (by rw [h168]; norm_num) (CFSG.RankThree.PartTwo.KFacts.KP7.three_not_dvd_card hsz)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
