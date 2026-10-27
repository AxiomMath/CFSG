module

public import CFSG.Quasithin.Vol2.Ch4Sec3Setup
public import CFSG.Quasithin.Background.C4Statement

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Blueprint

@[expose] def InspC48L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K : Subgroup G) (n : ℕ), 2 ≤ n →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n →
    (C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨ C48Case4 H R M L V K ∨
      C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨ C48Case7 H R M L V K ∨
      C48Case8 H R M L V K ∨ C48Case9 H R M L V K) → False

variable {G : Type} [Group G] [Finite G]

namespace Setting432

variable {T M L I H : Subgroup G} {n : ℕ} (s : Setting432 G T M L n I H)
include s

theorem S_lt_T (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : T ⊓ H < T := by
  refine lt_of_le_of_ne inf_le_left fun he => s.not_le_M ?_
  have hTH : T ≤ H := he ▸ inf_le_right
  exact isUniqueM_le_of_inH (s.hyp421.isUniqueM_sup h37 h38 h39).1
    ⟨_root_.sup_le (s.L_le_I.trans s.inM.2) hTH, s.inH.2⟩

theorem isSylowTwoOf_S_inf_L : IsSylowTwoOf (T ⊓ H ⊓ L) L := by
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (s.hyp.isSylowTwoOf le_sup_right) le_sup_left
      s.hyp.sup_le_normalizer
  rwa [inf_assoc, inf_eq_right.mpr (s.L_le_I.trans s.inM.2)]

theorem lemma_4_3_3_b (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G) ≤ M := by
  set S := T ⊓ H with hSdef
  have hlt := s.S_lt_T h37 h38 h39
  have hS2 : IsPGroup 2 S := s.hyp.sylow.1.to_le inf_le_left
  have hSM : S ≤ M := inf_le_left.trans s.hyp.T_le
  obtain ⟨y, hyT, hyN, hyS⟩ := exists_mem_normalizer_not_mem s.hyp.sylow.1 hlt
  have hSX : S < T ⊓ Subgroup.normalizer (S : Set G) :=
    lt_of_le_of_ne (le_inf inf_le_left Subgroup.le_normalizer) fun e => hyS (by
      show y ∈ S
      rw [e]
      exact ⟨hyT, hyN⟩)
  obtain ⟨TH, hTH, hXTH⟩ := exists_isSylowTwoOf_ge
    (inf_le_inf_right _ s.hyp.T_le : T ⊓ Subgroup.normalizer (S : Set G) ≤
      M ⊓ Subgroup.normalizer (S : Set G)) (s.hyp.sylow.1.to_le inf_le_left)
  have hU := s.lemma_4_3_3_a hSX inf_le_left
  refine lemma_4_3_1 hR hC s.hyp hS2 hSM hTH s.isSylowTwoOf_S_inf_L
    (isUniqueM_mono hU (sup_le_sup_left hXTH L) ?_)
  exact _root_.sup_le s.hyp.L_le (hTH.1.trans inf_le_left)

theorem isSylowTwoOf_S_H (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : IsSylowTwoOf (T ⊓ H) H := by
  have hS := s.isSylowTwoOf_S h37 h38 h39
  have hN := s.lemma_4_3_3_b hR hC h37 h38 h39
  refine isSylowTwoOf_iff_maximal.mpr ⟨inf_le_right, hS.2.1, fun P hPH hP2 hSP => ?_⟩
  by_contra hPS
  obtain ⟨y, hyP, hyN, hyS⟩ := exists_mem_normalizer_not_mem hP2
    (lt_of_le_of_ne hSP fun e => hPS (e ▸ le_rfl))
  have hsub : T ⊓ H ⊔ Subgroup.zpowers y ≤ H ⊓ M :=
    _root_.sup_le hS.1 (Subgroup.zpowers_le.mpr ⟨hPH hyP, hN hyN⟩)
  have h2 : IsPGroup 2 ↥(T ⊓ H ⊔ Subgroup.zpowers y) :=
    hP2.to_le (_root_.sup_le hSP (Subgroup.zpowers_le.mpr hyP))
  have hle := (isSylowTwoOf_iff_maximal.mp hS).2.2 _ hsub h2 le_sup_left
  exact hyS (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))

theorem exists_K (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hInsp : InspC48L2) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ L ≤ K ∧
      C48Case1 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K ∧
      ¬ K ≤ H ⊓ M ∧ H ⊓ M ≤ Subgroup.normalizer (K : Set G) ∧
      C48KDescribed H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K := by
  have hC28 := s.hyp4_2_3N.lemma_4_2_4N h36 h37 h38 h39 s.inH s.not_le_M
  have hlt : H ⊓ M < H := inf_lt_left.mpr s.not_le_M
  obtain ⟨-, K, hK, hKq, hLK, hcase⟩ := hC48 G H _ (H ⊓ M) L _ hC28 hlt
  rcases hcase with h10 | ⟨h19, hKM, hMK, hdesc⟩
  ·
    exfalso
    have hS := s.isSylowTwoOf_S_H hR hC h37 h38 h39
    have hSHM : T ⊓ H ≤ H ⊓ M := le_inf inf_le_right (inf_le_left.trans s.hyp.T_le)
    have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ H) (H ⊓ M) H hSHM inf_le_left
    rw [h10.2.2.2] at hmul
    exact hS.2.2 (Dvd.intro_left _ hmul)
  · rcases h19 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
    · exact ⟨K, hK, hKq, hLK, h1, hKM, hMK, hdesc⟩
    all_goals exfalso
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inl h2)
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inr (Or.inl h3))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inr (Or.inr (Or.inl h4)))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h9)))))))

theorem le_normalizer_of_cComp (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {K : Subgroup G}
    (hK : K ∈ cComp H) (hSK : T ⊓ H ≤ Subgroup.normalizer (K : Set G)) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  have := normal_conjClosure_of_pCoreOf_ne_bot s.hyp.qtke s.hyp.simple s.hyp.nonabelian h37 h38
    s.inH.2 (s.isSylowTwoOf_S_H hR hC h37 h38 h39) hK
  rwa [conjClosure_eq_self hSK] at this

end Setting432

end CFSG.Quasithin.H13.Ch4
