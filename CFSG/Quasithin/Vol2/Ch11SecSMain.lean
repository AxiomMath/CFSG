module

public import CFSG.Quasithin.Vol2.Ch11SecSBridge
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

open CFSG.Assembly.LowTwoRank (StatedSp)

theorem kindSp4_iso (h1102 : Stmt11_0_2) {T L I : Subgroup G} (h : Hyp11 G T L I 2)
    (hk : KindSp4 L (fsuV T I) 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSp 2 K)) := by
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I 2 h
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := hk
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem kindG2_iso (h1102 : Stmt11_0_2) {T L I : Subgroup G} (h : Hyp11 G T L I 2)
    (hk : KindG2 L (fsuV T I) 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) := by
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I 2 h
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := hk
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem dichotomy (hG2 : FactG2DerivedOrder) (hG2a : FactG2AdjointOrder) (h1102 : Stmt11_0_2)
    {T L I J J' : Subgroup G} (h : Hyp11 G T L I 2) (hJ : Hyp11 G T J J' 2)
    (hL3 : ¬ KindSL3 L (fsuV T I) 2) (hJ3 : ¬ KindSL3 J (fsuV T J') 2)
    (hG : ¬ (KindG2 L (fsuV T I) 2 ∧ KindG2 J (fsuV T J') 2))
    (hS : ¬ (KindSp4 L (fsuV T I) 2 ∧ KindSp4 J (fsuV T J') 2)) :
    (IsG2 2 2 (↥L ⧸ CFSG.pCore 2 ↥L) ∧ IsPSp4 2 2 (↥J ⧸ CFSG.pCore 2 ↥J)) ∨
      (IsG2 2 2 (↥J ⧸ CFSG.pCore 2 ↥J) ∧ IsPSp4 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  rcases kind_cases h1102 h with hL | hL | hL
  · exact absurd hL hL3
  · rcases kind_cases h1102 hJ with hk | hk | hk
    · exact absurd hk hJ3
    · exact absurd ⟨hL, hk⟩ hS
    · exact Or.inr ⟨isG2_of_shape hG2 hJ.shape (kindG2_iso h1102 hJ hk),
        isPSp4_of_shape hG2a h.shape (kindSp4_iso h1102 h hL)⟩
  · rcases kind_cases h1102 hJ with hk | hk | hk
    · exact absurd hk hJ3
    · exact Or.inl ⟨isG2_of_shape hG2 h.shape (kindG2_iso h1102 h hL),
        isPSp4_of_shape hG2a hJ.shape (kindSp4_iso h1102 hJ hk)⟩
    · exact absurd ⟨hL, hk⟩ hG

theorem stmt11_1_2Star_of (hF : FactL34Parab) (hPGL : FactPGL34Levi) (hC : CartanFacts)
    (hN : NatFacts) (hG2 : FactG2DerivedOrder) (hG2a : FactG2AdjointOrder) (h1102 : Stmt11_0_2)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hAm : Obl11_1_2StarAmalgam)
    (hSh : Obl11_1_2StarShape) (hSL3 : Obl11_1_2StarSL3) (hSym : Obl11_1_2StarSym) :
    Stmt11_1_2Star := by
  intro G _ _ T L I V₁ V₂ X K hyp hV₁ hV₂ hX hK hKn hlt hKM hK2 hKC hK3 hKX
  have h := starHyp_of hyp hV₁ hV₂ hX hK hKn hlt hKM hK2 hKC hK3 hKX
  have hL₁ne : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 hyp hV₁ (Or.inl rfl) le_rfl)
  obtain ⟨P₁, P₂, hP⟩ := h.exists_parData hF hL₁ne
  obtain ⟨cL, -, -⟩ := cartan_of hC hN hG2 h1102 hyp hV₁ hV₂ hX
  refine ⟨?_, ⟨k0Of K P₂, h.isLocal_k0Of hP, k0Of_le K P₂, StarHyp.k0Of_ne_K hP,
    StarHyp.k0Of_ne_L₁ hP⟩, ?_⟩
  · have hXK : K ⊔ X = K ⊔ xOne X (LOf L V₁) := by
      refine le_antisymm (sup_le le_sup_left (cL.a.trans (sup_le le_sup_right ?_)))
        (sup_le_sup_left inf_le_left K)
      exact inf_le_right.trans (h.L₁_le_K.trans le_sup_left)
    have key : ∀ A : Subgroup G, A = K ⊔ xOne X (LOf L V₁) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty (↥A ⧸ CFSG.pCore 2 ↥A ≃* (Matrix.GeneralLinearGroup (Fin 3) F ⧸
            Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F))) := by
      rintro A rfl
      exact h.pgl
    exact key _ hXK
  · intro K₀ hK₀ hK₀K hne hne₁
    have hK₀eq : K₀ = k0Of K P₂ := by
      rcases h.eq_of_isLocal_le hP hK₀ hK₀K with h1 | h1 | h1
      · exact absurd h1 hne
      · exact absurd h1 hne₁
      · exact h1
    subst hK₀eq
    have hIsK0 : IsK0 T L V₁ K (k0Of K P₂) := ⟨hK₀, hK₀K, hne, hne₁⟩
    have hY := hAm G T L I V₁ V₂ X K _ h hIsK0
    obtain ⟨I₀, hI₀, hTI₀, hK₀I₀, hL₂I₀, hXI₀⟩ := h.exists_cComp_I h37 h38 h39 hN h1102 cL hP hY
    obtain ⟨hI₀eq, hshape⟩ := hSh G T L I V₁ V₂ X K _ I₀ h hIsK0 hY hI₀ hTI₀ hK₀I₀ hL₂I₀ hXI₀
    subst hI₀eq
    have hnSL : ¬ KindSL3 L (fsuV T I) 2 := hSL3 G T L I V₁ V₂ X K h
    obtain ⟨I', U₁, U₂, hJ, hU₁, hU₂⟩ :=
      hSym G T L I V₁ V₂ X K _ h hIsK0 hnSL hY hI₀ hTI₀ hXI₀ hshape
    have hnSLJ := hSL3 G T _ I' U₁ U₂ X K hJ
    obtain ⟨hnG2, hnSp4⟩ := h.star_not_same_kind hC hN hG2 hPGL h1102 hP hJ hU₁ hU₂
    exact ⟨hJ.hyp.fsu.maximal, hJ.hyp.fsu.faithful, h.k0Of_not_le hP,
      ⟨I', U₂, hJ.hyp.fsu, hJ.v₂, hU₂⟩,
      dichotomy hG2 hG2a h1102 hyp hJ.hyp hnSL hnSLJ hnG2 hnSp4⟩

end CFSG.Quasithin.Vol2.Ch11.SecS
