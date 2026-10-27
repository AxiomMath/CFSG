module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2u
public import CFSG.Quasithin.Vol2.Ch10SecKIK2k
public import CFSG.Quasithin.Vol2.Ch10SecKIK2l
public import CFSG.Quasithin.Vol2.Ch10SecKIK2r
public import CFSG.Quasithin.Vol2.Ch10SecKIK2t

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA

variable {Γ : Type} [Group Γ] [Finite Γ] {H R J L V₁ V : Subgroup Γ} {hV : IsElemAbelian 2 V}

theorem factK2_cases (h36 : A36ForSQTK) (h56 : AsB56) (h312 : Vol2Native.A312ListFactsCat)
    (hc : S5Core H R J L V hV) (hmod : ModCase L V₁) :
    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) ∧
      ((∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
          A312C2 (modO2Image J L) ⊤ ∧ GoodLie ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))) ∨
        (Nonempty (↥(autI hV J) ≃* ↥(alternatingGroup (Fin 7))) ∧
          (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 5))) ∨
            Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) ∨
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
          (Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
            Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) ∧
          J ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 J)) := by
  have hq := isQuasisimple_quot h36 h56 hc
  refine ⟨hq, ?_⟩
  obtain ⟨hJH, hJN, hO, h2, -⟩ := s5_basic hc
  obtain ⟨hTs, hB⟩ := lbar_mem_lFamily hc
  have hne := lbar_ne_top hc hJN hO
  obtain ⟨hker, -, hcard⟩ := y_structure h36 hc hq hJN hO
  have hEven := even_card_modO2 hc
  have hYc := sqtkHypCat_y hc
  have hA := h312 _ hq hYc.isSQTKCat hYc.o2 _ hTs _ hB hne
  obtain ⟨hSQH, -, hRsyl, -, hHJ, -, -, hred, -, hJq', hJRV, -, hLJ, -, hLs, -, -⟩ := hc
  have hJq := isQuasisimple_of_open hJq'
  have hlist := b56List_autI h56 hV hSQH hRsyl hred hJH hHJ h2 hJq hJRV
  have hJ56 := b56Card_of_list hlist
  have hcT : Nat.card ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) = Nat.card ↥(autI hV J) ∨
      Nat.card ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) = 3 * Nat.card ↥(autI hV J) := by
    rw [Subgroup.card_top]
    exact hcard
  obtain ⟨eL⟩ := lbar_modO2_equiv hLJ
  have hπs := piJ_surjective hV hJN hO
  have hb : (IsAlt 7 ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) ∨
      IsHat ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) ↥(alternatingGroup (Fin 7))) →
      Nonempty (↥(autI hV J) ≃* ↥(alternatingGroup (Fin 7))) := fun h =>
    concl_b_of _ hπs hker hlist (h.imp isAlt_of_top isHat_of_top)
  have hcc : (IsPSL 4 2 1 ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) ∨
      IsPSL 5 2 1 ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))) →
      (Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
        Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) ∧
      J ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 J := by
    rintro (h | h)
    · obtain ⟨hk, he⟩ := concl_c_of _ hπs hker (by norm_num) (isPSL_of_top h)
      exact ⟨Or.inl he, inf_centralizer_of_ker hJN hO hk⟩
    · obtain ⟨hk, he⟩ := concl_c_of _ hπs hker (by norm_num) (isPSL_of_top h)
      exact ⟨Or.inr he, inf_centralizer_of_ker hJN hO hk⟩
  have hL32 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      (Nonempty (↥(autI hV J) ≃* ↥(alternatingGroup (Fin 7))) ∧
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 5))) ∨
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) ∨
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        (Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
          Nonempty (↥(autI hV J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) ∧
        J ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 J) := by
    rintro ⟨e3⟩
    have hD0 := oddData_of_equiv eL hLs hEven
    have h168 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
      rw [Nat.card_congr e3.toEquiv, Matrix.card_SL_field]
      simp [Fin.prod_univ_three, ZMod.card]
    rw [h168] at hD0
    rcases classify168 hJ56 hcT (rows_L32 hD0 hA) with h | h
    · exact Or.inr ⟨⟨e3⟩, hcc h⟩
    · exact Or.inl ⟨hb h, Or.inr ⟨e3⟩⟩
  obtain ⟨_, h1 | ⟨⟨eA⟩, -⟩ | ⟨h3, -⟩ | h4 | ⟨h5, -⟩ | ⟨n, hSz, -⟩⟩ := hmod
  ·
    obtain ⟨n, hn, ⟨K, _, _, hK, ⟨eK⟩⟩, -⟩ := h1
    have hD := barData_of_quot_SL2 (by omega) hK (eL.trans eK)
    rcases rows_L2' hD hA with hC2 | ⟨rfl, hO15⟩
    · exact Or.inl ⟨n, hn, K, inferInstance, inferInstance, hK, ⟨eK⟩, hC2,
        goodLie_of_rank2 hJ56 hcT hC2.2.1⟩
    · obtain ⟨eA⟩ := nonempty_sl2_equiv_alt5 (K := K) (by rw [hK]; norm_num)
      exact Or.inr (Or.inl ⟨hb (classify15 hJ56 hcT hO15), Or.inl ⟨eK.trans eA⟩⟩)
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hF4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    obtain ⟨eS⟩ := nonempty_sl2_equiv_alt5 (K := GaloisField 2 2) (by rw [hF4]; norm_num)
    have hD := barData_of_quot_SL2 (le_refl 2) hF4 (eL.trans (eA.trans eS.symm))
    rcases rows_L2' hD hA with hC2 | ⟨-, hO15⟩
    · exact Or.inl ⟨2, by norm_num, GaloisField 2 2, inferInstance, inferInstance, hF4,
        ⟨eA.trans eS.symm⟩, hC2, goodLie_of_rank2 hJ56 hcT hC2.2.1⟩
    · exact Or.inr (Or.inl ⟨hb (classify15 hJ56 hcT hO15), Or.inl ⟨eA⟩⟩)
  · exact Or.inr (hL32 h3)
  ·
    obtain ⟨n, hn, ⟨K, _, _, hK, ⟨eK⟩⟩, -⟩ := h4
    have hD := barData_of_quot_SL2 (by omega) hK (eL.trans eK)
    rcases rows_L2' hD hA with hC2 | ⟨h22, -⟩
    · exact Or.inl ⟨2 * n, by omega, K, inferInstance, inferInstance, hK, ⟨eK⟩, hC2,
        goodLie_of_rank2 hJ56 hcT hC2.2.1⟩
    · omega
  · exact Or.inr (hL32 h5)
  ·
    exfalso
    have hD := oddData_of_equiv eL hLs hEven
    obtain ⟨f, hf⟩ := rows_Sz hD (not_three_dvd_card_of_isSz hSz) hA
    exact false_of_2F4 hJ56 hcT hf

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
