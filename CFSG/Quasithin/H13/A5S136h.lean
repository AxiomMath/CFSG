module

public import CFSG.Quasithin.H13.A5S136f
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

structure Hyp1367 : Prop where
  hab : IsElemAbelian 2 (conjClosure V S.G1)
  hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))
  hVv : ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G)
  hJ : ¬ thompsonJ (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤
    Subgroup.centralizer (S.Uv : Set G)

@[expose] noncomputable def Tv : Subgroup G := T ⊓ Subgroup.centralizer ({S.v12} : Set G)

theorem z_mem_Uv : S.z ∈ S.Uv := le_conjClosure _ _ (Subgroup.mem_zpowers _)

@[expose] noncomputable def zU : ↥S.Uv := ⟨S.z, S.z_mem_Uv⟩

@[expose] def InX0 (X : Subgroup (MulAut ↥S.Uv)) : Prop :=
  X ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ∧
    autOn (S.Lv ⊔ S.Tv) S.Uv ≤ Subgroup.normalizer (X : Set (MulAut ↥S.Uv)) ∧
    oTwoRes X = X ∧ X ≠ ⊥ ∧ ⁅X, autOn (thompsonJ S.Tv) S.Uv⁆ = X

@[expose] def InXz (X : Subgroup (MulAut ↥S.Uv)) : Prop :=
  S.InX0 X ∧ ∃ x ∈ X, x S.zU ≠ S.zU

@[expose] def InYz (K : Subgroup G) : Prop :=
  K ≤ Subgroup.centralizer ({S.v12} : Set G) ∧ K ∈ lFamily S.Tv ∧
    CFSG.IsQuasisimple (↥(autOn K S.Uv) ⧸ CFSG.pCore 2 ↥(autOn K S.Uv)) ∧
    S.InXz (conjClosure (autOn K S.Uv) (autOn S.Tv S.Uv))

@[expose] noncomputable def WK (K : Subgroup G) : Subgroup G :=
  conjClosure S.V1 (conjClosure K S.Tv ⊔ S.Lv)

@[expose] noncomputable def plus (K : Subgroup G) : Subgroup (MulAut ↥(S.WK K)) :=
  autOn K (S.WK K)

end Setting

@[expose] def Exists1367 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∃ K : Subgroup G, S.InYz K

@[expose] def Lemma13614 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) ∧ S.InXz (autOn K S.Uv)

@[expose] def List1367 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
      CFSG.IsQuasisimple ↥(S.plus K) ∧ B56QuasisimpleList ↥(S.plus K)

@[expose] def Lemma13618 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))

@[expose] def Lemma13618Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))

@[expose] def Lemma13619 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ n → Nat.card F = 2 ^ n →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Open.quasithinG2 F))

@[expose] def Reduced1367 (X : Type) [Group X] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∨
  IsAlt 6 X ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty (X ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆)) ∨
  IsHat X ↥(alternatingGroup (Fin 6)) ∨ IsAlt 7 X ∨
  Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) ∨
  Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)))

@[expose] def Lemma13622 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
      (∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 →
        ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∧
      ¬ IsAlt 6 ↥(S.plus K) ∧
      (∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 →
        ¬ Nonempty (↥(S.plus K) ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆)) ∧
      ¬ IsHat ↥(S.plus K) ↥(alternatingGroup (Fin 6)) ∧ ¬ IsAlt 7 ↥(S.plus K)

@[expose] def Lemma13623 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)))

@[expose] def NotQS1367 : Prop :=
  ∀ (X : Type) [Group X], CFSG.IsQuasisimple X → ∀ (F : Type) [Field F] [Finite F],
    Nat.card F = 2 →
      ¬ Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
      ¬ Nonempty (X ≃* ↥(CFSG.Open.quasithinG2 F))

theorem two_le_of_field {F : Type} [Field F] [Finite F] {n : ℕ} (h : Nat.card F = 2 ^ n) :
    1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [h, pow_zero] at h1
    omega
  · exact hn

theorem main1367_of (hE : Exists1367) (h14 : Lemma13614) (hL : List1367) (h18 : Lemma13618)
    (h19 : Lemma13619) (h22 : Lemma13622) (h23 : Lemma13623) (hNQ : NotQS1367) : Main1367 := by
  intro G _ _ T L V S hab hF hVv hJ
  have hH : S.Hyp1367 := ⟨hab, hF, hVv, hJ⟩
  obtain ⟨K, hK⟩ := hE G T L V S hH
  have hT := (h14 G T L V S hH K hK).1
  obtain ⟨hqs, hlist⟩ := hL G T L V S hH K hK hT
  have h22' := h22 G T L V S hH K hK hT
  have h23' := h23 G T L V S hH K hK hT
  rcases hlist with ⟨n, F, _, _, hF2, he⟩ | ⟨n, F, _, _, hF2, he⟩ | ⟨n, F, _, _, hF2, he⟩ |
    ⟨n, F, _, _, hF2, he⟩ | h6 | h7 | h6h | ⟨F, _, _, hF2, he⟩ | h4 | h5
  · exact h18 G T L V S hH K hK hT n F hF2 he
  · have hn := two_le_of_field hF2
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have h1 : n = 1 := by omega
      subst h1
      exact h22'.1 F (by simpa using hF2) he
    · exact (h19 G T L V S hH K hK hT n F hn2 hF2).1 he
  · have hn := two_le_of_field hF2
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have h1 : n = 1 := by omega
      subst h1
      exact (hNQ _ hqs F (by simpa using hF2)).1 he
    · exact (h19 G T L V S hH K hK hT n F hn2 hF2).2.1 he
  · have hn := two_le_of_field hF2
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have h1 : n = 1 := by omega
      subst h1
      exact (hNQ _ hqs F (by simpa using hF2)).2 he
    · exact (h19 G T L V S hH K hK hT n F hn2 hF2).2.2 he
  · exact h22'.2.1 h6
  · exact h22'.2.2.2.2 h7
  · exact h22'.2.2.2.1 h6h
  · exact h22'.2.2.1 F hF2 he
  · exact h23'.1 h4
  · exact h23'.2 h5

end CFSG.Quasithin.H13.A5
