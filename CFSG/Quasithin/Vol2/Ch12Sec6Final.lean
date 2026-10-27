module

public import CFSG.Quasithin.Vol2.Ch12Sec6Amalgam
public import CFSG.Quasithin.Background.F9Eighteen
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.Vol2.Ch12Sec6Lemmas

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace S126

abbrev HStar (H : Subgroup G) : Type := ↥H ⧸ CFSG.pCore 2 ↥H

@[expose] noncomputable def star (H X : Subgroup G) : Subgroup (HStar H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

@[expose] def borel {Y : Type*} [Group Y] (X S : Subgroup Y) : Subgroup Y :=
  X ⊓ Subgroup.normalizer ((S ⊓ X : Subgroup Y) : Set Y)

@[expose] def IsHK (T L V₁ H K : Subgroup G) : Prop :=
  (∃ H₁ : Subgroup G, InHz T L V₁ H₁ ∧ K ∈ cComp H₁) ∧
    ¬ K ≤ Subgroup.normalizer (L : Set G) ∧ H = conjClosure K T ⊔ (L₁Of L V₁ ⊔ T)

@[expose] def ESet {W : Type*} [CommGroup W] (B D : Subgroup (MulAut W)) :
    Set (Subgroup (MulAut W)) :=
  {E | D ≤ E ∧ E ≤ B ∧ D.relIndex E = 2 ∧ fixV B < fixV E}

abbrev PSL3Model (F : Type) [Field F] : Type :=
  CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F)

@[expose] def Case1 (T L H K : Subgroup G) : Prop :=
  conjClosure K T = K ∧
  ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(star H K) ≃* PSL3Model F) ∧ Nonempty (HStar H ≃* MulAut (PSL3Model F))) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(star H K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∧
      (star H K).index = 4 ∧ ∀ x : HStar H, x ^ 2 ∈ star H K)) ∧
  star H (Subgroup.normalizer (L : Set G) ⊓ H) =
    star H T ⊔ borel (oTwoRes (⊤ : Subgroup (HStar H))) (star H T)

@[expose] def Case2 (T L H K : Subgroup G) : Prop :=
  conjClosure K T ≠ K ∧ Nonempty (↥(star H K) ≃* alternatingGroup (Fin 5)) ∧
  Nonempty (↥(star H (conjClosure K T)) ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∧
  Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) = ⊥ ∧
  (Nat.card (HStar H) = 14400 ∨ Nat.card (HStar H) = 28800) ∧
  star H (Subgroup.normalizer (L : Set G) ⊓ H) =
    star H T ⊔ borel (star H (conjClosure K T)) (star H T)

@[expose] def Case3 (T L V₁ H : Subgroup G) : Prop :=
  Nonempty (HStar H ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) ∧
  (Subgroup.normalizer (L : Set G) ⊓ H).relIndex H = 5 ∧
  star H (Ri T L V₁) = pCoreOf 2 (star H (Subgroup.normalizer (L : Set G) ⊓ H)) ∧
  Nat.card ↥(star H (Ri T L V₁)) = 4 ∧ ∀ x ∈ star H (Ri T L V₁), x ^ 2 = 1

end S126

@[expose] def Lemma12_6_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (_ : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ g : G, V ⊓ conjSubgroup V g ≠ ⊥ → ⁅V, conjSubgroup V g⁆ = ⊥

@[expose] def Lemma12_6_28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (_ : Frame126 T L V) (h : Hyp126 G T L V), V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      E3.aSet 3 h.hyp.MVbar = ∅ ∧
      (∀ B ∈ E3.aSet 2 h.hyp.MVbar, 8 ≤ Nat.card ↥B ∧
        ∃ D : Subgroup (MulAut ↥V), D ≤ B ∧ D.relIndex B = 8 ∧ 2 < (ESet B D).ncard) ∧
      (E3.wClos V 0 T ≤ Subgroup.centralizer (V : Set G) ∧
        Subgroup.normalizer (E3.wClos V 0 T : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
      (E3.wClos V 1 T ≤ Subgroup.centralizer (V : Set G) ∧ 1 < E3.wParam T V)

@[expose] def Lemma12_6_29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (_ : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H₀ : Subgroup G, InH T H₀ → (E1.nParam H₀ = 1 ∨ Group.IsSolvable ↥H₀) →
        H₀ ≤ Subgroup.normalizer (L : Set G)

@[expose] def Display12_6_29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      InHz T L F.V1 (Subgroup.centralizer (F.V1 : Set G)) ∧
      ∀ H : Subgroup G, InHz T L F.V1 H → ∃ K ∈ cComp H,
        ¬ K ≤ Subgroup.normalizer (L : Set G) ∧
        L₁Of L F.V1 ≤ Subgroup.normalizer (K : Set G) ∧
        H ≤ Subgroup.normalizer (conjClosure K T : Set G) ∧
        InHz T L F.V1 (conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T))

@[expose] def Lemma12_6_30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      (∀ H₂ : Subgroup G, InHz T L F.V1 H₂ → HypF98 T V L F.V1 F.V5 H₂) ∧
      ∀ H K : Subgroup G, IsHK T L F.V1 H K →
        (∃ hE : IsElemAbelian 2 (tildeOf F.V1 (conjClosure F.V5 H)),
          qInt (tildeOf F.V1 H) (tildeOf F.V1 (conjClosure F.V5 H)) hE ≤ 2) ∧
        CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) ∧ HypF918 T V L F.V1 F.V5 H K

@[expose] def Lemma12_6_31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K →
        Case1 T L H K ∨ Case2 T L H K ∨ Case3 T L F.V1 H

@[expose] def Lemma12_6_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K →
        Nonempty (↥(star H K) ≃* alternatingGroup (Fin 5))

@[expose] def Lemma12_6_33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K →
        Nonempty (HStar H ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))

@[expose] def Final126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → Case3 T L F.V1 H →
        Nonempty (↥(star H K) ≃* alternatingGroup (Fin 5)) → False

namespace S126

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem not_case1_of_alt5 {T L H K : Subgroup G} (h1 : Case1 T L H K)
    (hA : Nonempty (↥(star H K) ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨eA⟩ := hA
  have h60 : Nat.card ↥(star H K) = 60 := by
    rw [Nat.card_congr eA.toEquiv, card_alternatingGroup_five]
  obtain ⟨-, ⟨F, _, _, hF, ⟨e⟩, -⟩ | ⟨F, _, _, hF, ⟨e⟩, -⟩, -⟩ := h1
  · have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3)
      (by norm_num)
    rw [hF, ← Nat.card_congr e.toEquiv, h60] at h
    exact absurd h (by decide)
  · have h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3)
      (by norm_num)
    rw [hF, Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
      ← Nat.card_congr e.toEquiv, h60] at h
    exact absurd h (by decide)

theorem not_case2_of_s5s3 {T L H K : Subgroup G} (h2 : Case2 T L H K)
    (hS : Nonempty (HStar H ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))) : False := by
  obtain ⟨e⟩ := hS
  have h720 : Nat.card (HStar H) = 720 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_fin,
      Nat.card_fin]
    decide
  obtain ⟨-, -, -, -, h | h, -⟩ := h2 <;> rw [h720] at h <;> exact absurd h (by decide)

end S126

theorem elim126_of_lemmas (hex : Frame126Exists) (h1223 : Lemma12_6_23) (hdisp : Display12_6_29)
    (h31 : Lemma12_6_31) (h32 : Lemma12_6_32) (h33 : Lemma12_6_33) (hfin : Final126) :
    Elim126 := by
  intro G _ _ T L V hH
  obtain ⟨_, ⟨F⟩⟩ := hex G T L V hH
  obtain ⟨hZ, -, -⟩ := h1223 G T L V F hH
  obtain ⟨hGz, hK⟩ := hdisp G T L V F hH hZ
  obtain ⟨K, hKc, hKM, -, -, -⟩ := hK _ hGz
  have hIs : IsHK T L F.V1 (conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T)) K := ⟨⟨_, hGz, hKc⟩, hKM, rfl⟩
  have hA := h32 G T L V F hH hZ _ K hIs
  rcases h31 G T L V F hH hZ _ K hIs with h1 | h2 | h3
  · exact not_case1_of_alt5 h1 hA
  · exact not_case2_of_s5s3 h2 (h33 G T L V F hH hZ _ K hIs)
  · exact hfin G T L V F hH hZ _ K hIs h3 hA

end CFSG.Quasithin.H13
