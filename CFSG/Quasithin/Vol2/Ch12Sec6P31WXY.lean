module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WInp2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Vol2.Ch12Sec6P31a
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def lieFam1_w31 (m : ℕ) (X : Type) [Group X] : Prop :=
  IsPSL 2 2 m X ∨ IsSz m X ∨ IsPSU 3 2 m X ∨ IsPSL 3 2 m X ∨ IsPSp4 2 m X ∨ (m = 1 ∧ IsAlt 6 X) ∨
    IsG2 2 m X ∨ (m = 1 ∧ IsPSU 3 3 1 X)

@[expose] def F918List_w31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K →
        (conjClosure K T = K →
          ((∃ m : ℕ, 1 ≤ m ∧ lieFam1_w31 m (starMod_w31 H K)) ∨
            IsPSL 4 2 1 (starMod_w31 H K) ∨ IsPSL 5 2 1 (starMod_w31 H K) ∨
            IsAlt 7 (starMod_w31 H K) ∨ IsSporadic .M22 ↥(star H (conjClosure K T)) ∨
            IsHat ↥(star H (conjClosure K T)) (CFSG.Blueprint.NativeSporadic.Carrier .M22))) ∧
        (conjClosure K T ≠ K →
          ∃ m : ℕ, 1 ≤ m ∧ (IsPSL 2 2 m (starMod_w31 H K) ∨ IsSz m (starMod_w31 H K) ∨
            IsAlt 5 (starMod_w31 H K) ∨ IsPSL 3 2 1 (starMod_w31 H K)))

@[expose] def LemmaFBound_w31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K →
        (∀ m : ℕ, 1 ≤ m → lieFam1_w31 m (starMod_w31 H K) → E1.nParam H ≤ (m : ℕ∞)) ∧
        (IsPSL 4 2 1 (starMod_w31 H K) ∨ IsPSL 5 2 1 (starMod_w31 H K) ∨
          IsAlt 7 (starMod_w31 H K) → E1.nParam H ≤ 1) ∧
        (IsSporadic .M22 ↥(star H (conjClosure K T)) ∨
          IsHat ↥(star H (conjClosure K T)) (CFSG.Blueprint.NativeSporadic.Carrier .M22) →
          E1.nParam H ≤ 2)

section GLevel

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem two_le_nParam (h1229 : Lemma12_6_29) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) : 2 ≤ E1.nParam H := by
  have h := h918.toHypF98.toHypF91
  have hInH : InH T H := ⟨h.T_le_H, pCoreOf_ne_bot h⟩
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hne1 : E1.nParam H ≠ 1 := fun h1 =>
    hIs.2.1 (hKH.trans (h1229 G T L V F hH hZ H hInH (Or.inl h1)))
  have hne0 : E1.nParam H ≠ 0 := by
    intro h0
    have hodd := E1.odd_of_nParam_le_zero (le_of_eq h0)
    have hQ := pCoreOf_ne_bot h
    have h2 : 2 ∣ Nat.card ↥H := by
      have hQ1 : 1 < Nat.card ↥(pCoreOf 2 H) := (Subgroup.one_lt_card_iff_ne_bot _).2 hQ
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
      have hk1 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        omega
      have := Subgroup.card_dvd_of_le (pCoreOf_le 2 H)
      rw [hk] at this
      exact (dvd_pow_self 2 hk1).trans this
    obtain ⟨a, ha⟩ := hodd
    omega
  generalize E1.nParam H = x at hne0 hne1
  induction x using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h0 : n ≠ 0 := fun h => hne0 (by rw [h]; rfl)
    have h1 : n ≠ 1 := fun h => hne1 (by rw [h]; rfl)
    exact_mod_cast (show 2 ≤ n by omega)

theorem e114ListF_w31_of (hFL : F918List_w31) (hLF : LemmaFBound_w31) : E114ListF_w31 := by
  intro h1229 G _ _ T L V _ F hH hZ H K hIs h918
  have h2 := two_le_nParam h1229 hH hZ hIs h918
  obtain ⟨hK0, hK1⟩ := hFL G T L V F hH hZ H K hIs h918
  obtain ⟨hl, h1n, hM⟩ := hLF G T L V F hH hZ H K hIs h918
  have hnat : ∀ {m : ℕ}, E1.nParam H ≤ (m : ℕ∞) → 2 ≤ m := fun hm => by
    exact_mod_cast h2.trans hm
  have hn1 : ¬ E1.nParam H ≤ 1 := fun h => absurd (h2.trans h) (by norm_num)
  by_cases hKK : conjClosure K T = K
  · rcases hK0 hKK with ⟨m, hm1, hfam⟩ | h | h | h | h | h
    · have hm2 := hnat (hl m hm1 hfam)
      refine Or.inl ⟨m, hm2, Or.inl ⟨hKK, ?_⟩⟩
      rcases hfam with h | h | h | h | h | ⟨hm, -⟩ | h | ⟨hm, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · omega
    · exact (hn1 (h1n (Or.inl h))).elim
    · exact (hn1 (h1n (Or.inr (Or.inl h)))).elim
    · exact (hn1 (h1n (Or.inr (Or.inr h)))).elim
    · exact Or.inr ⟨le_antisymm (hM (Or.inl h)) h2, Or.inl h⟩
    · exact Or.inr ⟨le_antisymm (hM (Or.inr h)) h2, Or.inr h⟩
  · obtain ⟨m, hm1, hfam⟩ := hK1 hKK
    rcases hfam with h | h | h | h
    · exact Or.inl ⟨m, hnat (hl m hm1 (Or.inl h)), Or.inr ⟨hKK, Or.inl h⟩⟩
    · exact Or.inl ⟨m, hnat (hl m hm1 (Or.inr (Or.inl h))), Or.inr ⟨hKK, Or.inr (Or.inl h)⟩⟩
    · exact Or.inl ⟨2, le_rfl, Or.inr ⟨hKK, Or.inr (Or.inr ⟨rfl, h⟩)⟩⟩
    · exact (hn1 (by simpa using hl 1 le_rfl (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim

end GLevel

end CFSG.Quasithin.H13
