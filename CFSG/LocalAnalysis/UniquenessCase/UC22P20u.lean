module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20t

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def uc22p20uConjL (L : Subgroup G) (t : G) (ht : t ∈ normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun l := ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht l).1 l.2⟩
  invFun l := ⟨t⁻¹ * l * t, by
    simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem ht) l).1 l.2⟩
  left_inv l := by ext; simp [mul_assoc]
  right_inv l := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[expose] def uc22p20uInd (L : Subgroup G) (t : G) (ht : t ∈ normalizer (L : Set G)) :
    MulAut (Bar2 L) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) (uc22p20uConjL L t ht)
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (uc22p20uConjL L t ht))

theorem uc22p20uInd_mk (L : Subgroup G) {t : G} (ht : t ∈ normalizer (L : Set G)) (l : ↥L) :
    uc22p20uInd L t ht (QuotientGroup.mk l) =
      QuotientGroup.mk ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht l).1 l.2⟩ := rfl


@[expose] def uc22p20uA (D : Data G) (L : Subgroup G) : Set (MulAut (Bar2 L)) :=
  {α | ∃ (t : G) (ht : t ∈ normalizer (L : Set G)), t ∈ D.T ∧ α = uc22p20uInd L t ht}

theorem uc22p20u_T_le_normalizer_inf (D : Data G) {L : Subgroup G} (hTL : D.T ≤ normalizer (L : Set G)) :
    D.T ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxT, hxL⟩
    exact ⟨D.T.mul_mem (D.T.mul_mem ht hxT) (D.T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.1 (hTL ht) x).1 hxL⟩
  · rintro ⟨hxT, hxL⟩
    refine ⟨?_, ?_⟩
    · have := D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hxT) ht
      simpa [mul_assoc] using this
    · exact (Subgroup.mem_normalizer_iff.1 (hTL ht) x).2 hxL

theorem uc22p20u_ind_sylowBar (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {t : G}
    (ht : t ∈ normalizer (L : Set G)) (htT : t ∈ D.T) (x : Bar2 L) :
    x ∈ uc22p20iSylowBar D L ↔ uc22p20uInd L t ht x ∈ uc22p20iSylowBar D L := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
  have e : uc22p20uInd L t ht (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht l).1 l.2⟩ :=
    rfl
  rw [e, uc22p20i_mem_sylowBar_iff D hL, uc22p20i_mem_sylowBar_iff D hL]
  have := Subgroup.mem_normalizer_iff.1 (uc22p20u_T_le_normalizer_inf D hL.1 htT) (l : G)
  exact this


theorem uc22p20u_join_ne_top (D : Data G) (h20_4 : S20_4 D) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calLLow D.T D.M) :
    (⨆ (P : Subgroup (Bar2 L)) (_ : normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) :
      Set (Bar2 L)) ≤ P ∧ P ≠ ⊤ ∧ ∀ α ∈ uc22p20uA D L, ∀ x, x ∈ P ↔ α x ∈ P), P) ≠ ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  have hLcal : L ∈ calL D.T D.M := hL.prop
  have hTL : D.T ≤ normalizer (L : Set G) := hLcal.1
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Mb : Subgroup (Bar2 L) := ((D.M ⊓ L).subgroupOf L).map π with hMb
  have hMbne : Mb ≠ ⊤ := by
    intro h
    apply uc22p20i_not_le_M D hLcal
    intro l hl
    have hmem : π ⟨l, hl⟩ ∈ Mb := by rw [h]; trivial
    obtain ⟨m, hm, hml⟩ := hmem
    have hk : m⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq (s := CFSG.pCore 2 ↥L)).1 hml
    have hkT : (((m⁻¹ * ⟨l, hl⟩ : ↥L)) : G) ∈ D.T :=
      (uc22p20i_pCoreOf_le D hLcal ⟨_, hk, rfl⟩).1
    have hmM : (m : G) ∈ D.M := (Subgroup.mem_subgroupOf.1 hm).1
    have : l = (m : G) * (((m⁻¹ * ⟨l, hl⟩ : ↥L)) : G) := by simp
    rw [this]
    exact D.M.mul_mem hmM (D.sylowM.le hkT)
  have hle : (⨆ (P : Subgroup (Bar2 L)) (_ : normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) :
      Set (Bar2 L)) ≤ P ∧ P ≠ ⊤ ∧ ∀ α ∈ uc22p20uA D L, ∀ x, x ∈ P ↔ α x ∈ P), P) ≤ Mb := by
    refine iSup₂_le fun P ⟨hNP, hPtop, hPA⟩ => ?_
    set Q : Subgroup G := (P.comap π).map L.subtype with hQ
    have hmemQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ L, π ⟨x, hx⟩ ∈ P := by
      intro x
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l.2, hl⟩
      · rintro ⟨hx, h⟩
        exact ⟨⟨x, hx⟩, h, rfl⟩
    have hQL : Q ≤ L := Subgroup.map_subtype_le _
    have hOQ : pCoreOf 2 L ≤ Q := by
      rintro _ ⟨y, hy, rfl⟩
      refine (hmemQ _).2 ⟨y.2, ?_⟩
      have h1 : π y = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hy
      have h2 : (⟨L.subtype y, y.2⟩ : ↥L) = y := rfl
      rw [h2, h1]
      exact P.one_mem
    have hsub : Q.subgroupOf L = P.comap π :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    have hpar : ParabolicOf L Q := by
      refine ⟨hOQ, hQL, (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL.prop), ?_⟩
      show normalizer (((uc22p20iSylowBar D L : Subgroup (Bar2 L))) : Set (Bar2 L)) ≤
        (Q.subgroupOf L).map π
      rw [hsub, Subgroup.map_comap_eq_self_of_surjective hπs]
      exact hNP
    have hTQ : D.T ≤ normalizer (Q : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hα : ∀ y : Bar2 L, y ∈ P ↔ uc22p20uInd L t (hTL ht) y ∈ P :=
        fun y => hPA _ ⟨t, hTL ht, ht, rfl⟩ y
      rw [hmemQ, hmemQ]
      constructor
      · rintro ⟨hx, h⟩
        have hxL' : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTL ht) x).1 hx
        refine ⟨hxL', ?_⟩
        have := (hα (π ⟨x, hx⟩)).1 h
        exact this
      · rintro ⟨hx, h⟩
        have hxL : x ∈ L := (Subgroup.mem_normalizer_iff.1 (hTL ht) x).2 hx
        refine ⟨hxL, ?_⟩
        exact (hα (π ⟨x, hxL⟩)).2 h
    have hQne : Q ≠ L := by
      intro hQL'
      apply hPtop
      rw [eq_top_iff]
      intro y _
      obtain ⟨l, rfl⟩ := hπs y
      have : (l : G) ∈ Q := by rw [hQL']; exact l.2
      obtain ⟨hx, h⟩ := (hmemQ _).1 this
      exact h
    have hQM : Q ≤ D.M := uc22p20s_parabolic_le_M D h20_4 h1930 hL hpar hTQ hQne
    intro y hy
    obtain ⟨l, rfl⟩ := hπs y
    have hl : (l : G) ∈ Q := (hmemQ _).2 ⟨l.2, hy⟩
    exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨hQM hl, l.2⟩, rfl⟩
  exact hMbne (top_le_iff.1 (htop ▸ hle))

@[expose] def uc22p20uDiagramInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ (t : StatedLieTag) (m n : ℕ),
    LieModel (X ⧸ center X) t m 2 n → ∀ (U : Sylow 2 X) (A : Set (MulAut X)),
    (∀ α ∈ A, ∀ x : X, x ∈ (U : Subgroup X) ↔ α x ∈ (U : Subgroup X)) →
    (uc22p20sRankTwo t m n ∨ (uc22p20sGraphShape t m n ∧ ∀ α ∈ A, ∀ θ : MulAut (X ⧸ center X),
      (∀ x : X, θ (QuotientGroup.mk x) = QuotientGroup.mk (α x)) →
        CFSG.ASVolI.ChA.IsInnDiagFieldAut _ θ)) →
    (⨆ (P : Subgroup X) (_ : normalizer ((U : Subgroup X) : Set X) ≤ P ∧ P ≠ ⊤ ∧
      ∀ α ∈ A, ∀ x : X, x ∈ P ↔ α x ∈ P), P) = ⊤

theorem uc22p20u_s20_10_of (hD : uc22p20uDiagramInput) (D : Data G) (h20_4 : S20_4 D)
    (h20_7 : uc22p20tS207Ref D) : S20_10 D := by
  intro h1930 L hL
  have hLcal : L ∈ calL D.T D.M := hL.prop
  have hTL : D.T ≤ normalizer (L : Set G) := hLcal.1
  set U : Sylow 2 (Bar2 L) :=
    (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hLcal) with hU
  have hUinv : ∀ α ∈ uc22p20uA D L, ∀ x : Bar2 L,
      x ∈ (U : Subgroup (Bar2 L)) ↔ α x ∈ (U : Subgroup (Bar2 L)) := by
    rintro α ⟨t, ht, htT, rfl⟩ x
    exact uc22p20u_ind_sylowBar D hLcal ht htT x
  have hne := uc22p20u_join_ne_top D h20_4 h1930 hL
  rcases h20_7 h1930 L hLcal with ⟨hq, h1 | ⟨t, m, n, hgs, hM, hS⟩ | ⟨t, m, n, hrt, hM⟩⟩ |
      ⟨L₁, L₂, h₁, h₂, hL12, hne', ht, n, hn⟩
  · obtain ⟨n, -, hn⟩ := h1
    exact Or.inl ⟨n, hn⟩
  · by_cases hact : ∃ x ∈ D.T, ActsNontrivOnDiagram L x
    · obtain ⟨x, hx, hxa⟩ := hact
      exact Or.inr (Or.inr ⟨n, hS, x, hx, hxa⟩)
    · exfalso
      push Not at hact
      refine hne (hD (Bar2 L) hq t m n hM U (uc22p20uA D L) hUinv (Or.inr ⟨hgs, ?_⟩))
      rintro α ⟨x, hxN, hxT, rfl⟩ θ hθ
      by_contra hnot
      exact hact x hxT ⟨hxN, θ, fun l l' hl' => by
        have h1 := hθ (QuotientGroup.mk l)
        rw [uc22p20uInd_mk] at h1
        have h2 : (⟨x * (l : G) * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN l).1 l.2⟩ : ↥L) = l' :=
          Subtype.ext hl'.symm
        rw [h2] at h1
        exact h1, hnot⟩
  · exfalso
    exact hne (hD (Bar2 L) hq t m n hM U (uc22p20uA D L) hUinv (Or.inl hrt))
  · exact Or.inr (Or.inl ⟨L₁, L₂, h₁, h₂, hL12, hne', ht, n, hn⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22
