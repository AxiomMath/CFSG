module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19V
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19B5
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Two
public import CFSG.Quasithin.Vol2.Ch5Sec1Hall

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

@[expose] def Parab619 {G : Type} [Group G] (T M L V T' D' : Subgroup G) : Prop :=
  ∃ P₁ : Subgroup G, P₁ ≤ ch619I T L V ∧ T' ≤ Subgroup.normalizer (P₁ : Set G) ∧
    D' ≤ Subgroup.normalizer (P₁ : Set G) ∧ ¬ P₁ ≤ M ∧ IsSylowTwoOf (T' ⊓ P₁) P₁ ∧
    Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3))

@[expose] def Case619S5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) (y z : G)
    (T' D' : Subgroup G), Hyp6116 G T M L V n → Hyp611 G T' M L V n →
    Dat619 T M L V H n y z T' D' →
    ∀ (hW : IsElemAbelian 2 (ch619W T L V z))
      (Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))),
      G6.IsTransvectionDecomposition (L619.img0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks →
      L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) Ks →
      Nonempty (↥(Ks 0) ≃* Equiv.Perm (Fin 5)) → Parab619 T M L V T' D'

@[expose] def Case619RankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) (y z : G)
    (T' D' : Subgroup G), Hyp6116 G T M L V n → Dat619 T M L V H n y z T' D' →
    ∀ (hW : IsElemAbelian 2 (ch619W T L V z))
      (Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))),
      G6.IsTransvectionDecomposition (L619.img0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks →
      ((∃ m : ℕ, (m = 4 ∨ m = 5) ∧
          Nonempty (↥(Ks 0) ≃* Matrix.GeneralLinearGroup (Fin m) (ZMod 2))) ∨
        (∃ m : ℕ, 6 ≤ m ∧ m ≤ 8 ∧ Nonempty (↥(Ks 0) ≃* Equiv.Perm (Fin m)))) → False

@[expose] def Case619Swap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) (y z : G)
    (T' D' : Subgroup G), Hyp6116 G T M L V n → Dat619 T M L V H n y z T' D' →
    ∀ (hW : IsElemAbelian 2 (ch619W T L V z))
      (Ks : Fin 2 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))),
      G6.IsTransvectionDecomposition (L619.img0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks →
      L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) Ks →
      (∃ (x : G) (hx : x ∈ L619.normWZX (ch619W T L V z) (ch6ZS T L V)
          (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))), x ∈ ch619I T L V ∧
        ∃ i, ∃ k ∈ Ks i, L619.act0 hW _ _ ⟨x, hx⟩ * k * (L619.act0 hW _ _ ⟨x, hx⟩)⁻¹ ∉ Ks i) →
      (∃ i, Nat.card (Ks i) = 6) → False

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem parab619 (h : Hyp6116 G T M L V n) (hT' : Hyp611 G T' M L V n) (h432 : Stmt4_3_2)
    (h6110 : Stmt6_1_10) (h56 : AsB56) (hab : IsMulCommutative ↥(conjClosure V (ch619I T L V)))
    (hS5 : Case619S5) (hR2 : Case619RankTwo) (hSw : Case619Swap) :
    Parab619 T M L V T' D' := by
  have hW := Cfg619.isElemAbelian_W h hab z
  obtain ⟨s, Ks, hdec, hND⟩ :=
    hd.cfg.exists_decomposition_b5 h h56 h432 h6110 hab hd.z619 hd.isY hW
  have hs1 := hdec.pos
  have hs2 := hdec.le_two
  obtain rfl | rfl : s = 1 ∨ s = 2 := by omega
  ·
    rcases hdec.type 0 with ⟨m, hm2, hm5, hLn⟩ | ⟨m, hm5, hm8, hSym⟩ | ⟨m, hm, hCore⟩
    · obtain ⟨e⟩ := hLn.1
      interval_cases m
      · exact hd.parabolic_of_gl2 h h432 hW hdec hND ⟨e⟩
      · exact hd.parabolic_of_gl3 h h432 hW hdec hND ⟨e⟩
      · exact (hR2 G T M L V H n y z T' D' h hd hW Ks hdec (Or.inl ⟨4, Or.inl rfl, ⟨e⟩⟩)).elim
      · exact (hR2 G T M L V H n y z T' D' h hd hW Ks hdec (Or.inl ⟨5, Or.inr rfl, ⟨e⟩⟩)).elim
    · obtain ⟨θ, -⟩ := hSym
      by_cases h5 : m = 5
      · subst h5
        exact hS5 G T M L V H n y z T' D' h hT' hd hW Ks hdec hND ⟨θ⟩
      · exact (hR2 G T M L V H n y z T' D' h hd hW Ks hdec
          (Or.inr ⟨m, by omega, hm8, ⟨θ⟩⟩)).elim
    · obtain ⟨θ, -⟩ := hCore
      have h68 : 6 ≤ m ∧ m ≤ 8 := by rcases hm with rfl | rfl <;> omega
      exact (hR2 G T M L V H n y z T' D' h hd hW Ks hdec
        (Or.inr ⟨m, h68.1, h68.2, ⟨θ⟩⟩)).elim
  ·
    by_cases hcase : (∀ (x : G) (hx : x ∈ L619.normWZX (ch619W T L V z) (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))), x ∈ ch619I T L V → ∀ i, ∀ k ∈ Ks i,
        L619.act0 hW _ _ ⟨x, hx⟩ * k * (L619.act0 hW _ _ ⟨x, hx⟩)⁻¹ ∈ Ks i) ∨
      (∀ i, Nat.card (Ks i) ≠ 6)
    · exact (hd.false_of_two h h432 hW hdec hND hcase).elim
    · rw [not_or] at hcase
      obtain ⟨h1, h2⟩ := hcase
      push Not at h1 h2
      exact (hSw G T M L V H n y z T' D' h hd hW Ks hdec hND h1 h2).elim

end Dat619

theorem parabolic6_1_19_of (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (h6112 : Stmt6_1_12) (h56 : AsB56) (hS5 : Case619S5)
    (hR2 : Case619RankTwo) (hSw : Case619Swap) : Parabolic6_1_19 := by
  intro G _ _ T M L V n h hex hab
  obtain ⟨H, hH, hHs, hodd⟩ := hex
  obtain ⟨D, hD⟩ := h.toHyp5_0_1.exists_isHall_borel
  obtain ⟨y, z, d, hdL, hd⟩ := h.exists_dat619 h331 h432 h615 h6110 h6112 hH hHs hodd hD
  have hdL' : d⁻¹ ∈ L := L.inv_mem hdL.1
  have hT' : Hyp611 G (conjSub d⁻¹ T) M L V n :=
    h.toHyp611.conj_of_mem (h.toHyp611.L_le hdL') (h.toHyp611.L_le_normalizer hdL')
  obtain ⟨P₁', hP₁I, hTP, hDP, hM, hsyl, hS3⟩ :=
    hd.parab619 h hT' h432 h6110 h56 hab hS5 hR2 hSw
  exact h.toHyp611Nat.parabolic_of_conj hdL hD hP₁I hTP hDP hM hsyl hS3

end CFSG.Quasithin.H13
