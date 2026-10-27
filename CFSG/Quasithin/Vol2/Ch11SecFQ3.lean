module

public import CFSG.Quasithin.Vol2.Ch11SecFQ2
public import CFSG.Quasithin.Vol2.Ch11SecD557B
public import CFSG.Quasithin.Vol2.Ch11SecFOblCX

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem coprime_card_of_odd' {X P : Subgroup G} (hX : Odd (Nat.card X)) (hP : IsPGroup 2 P) :
    Nat.Coprime (Nat.card X) (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hX)

theorem isSolvable_of_isPGroup_two' {P : Subgroup G} (hP : IsPGroup 2 P) :
    Group.IsSolvable ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hP.isNilpotent
  infer_instance

theorem qOf_le_pCoreOf_normalizer (hF : Sp4Facts) (hTr : FactSp4Trans)
    (hCX : Obl11_5_7Sp4CX) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3)
    (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hV₁₃ : V₁ ≤ V₃) (hW : ¬ IsMulCommutative ↥(wH T I V₁))
    (hR : Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G))
    {X : Subgroup G} (hX : IsCartanX T L X) {y : G} (hy : y ∈ L)
    (hyX : y ∈ Subgroup.normalizer (X : Set G)) (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥) :
    qOf T I V₁ y ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  have hWQ₁ := conjClosure_le_pCoreOf hQ
  have hQO := qOf_le_pCoreOf_sup h1102 h hV₁ hQ hy
  have hQ2 : IsPGroup 2 (qOf T I V₁ y) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hQO
  have hQT : qOf T I V₁ y ≤ T := hQO.trans (pCoreOf_le_of_sylow h.fsu.sylow le_sup_right)
  have hSQ := inf_le_normalizer_qOf h1103 h hV₁ y
  have hXQ := (cartan_le_inf hN h1102 h hV₁ hX hyX).trans hSQ
  have hcop := coprime_card_of_odd' hX.2.1 hQ2
  have hdec := SecD.le_commutator_sup_centralizer hXQ (isSolvable_of_isPGroup_two' hQ2) hcop
  have hCQ : qOf T I V₁ y ⊓ Subgroup.centralizer (X : Set G) ≤
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    (hCX G T L I n V₁ V₃ X y h hV₁ hV₃ hk hW hR hX hy hyX hopp).trans (inf_le_left.trans hWQ₁)
  have hPQ : ⁅qOf T I V₁ y, X⁆ ≤ qOf T I V₁ y :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hXQ
  have hPX : ⁅qOf T I V₁ y, X⁆ = ⁅⁅qOf T I V₁ y, X⁆, X⁆ :=
    (SecD.commutator_commutator_eq hXQ hcop).symm
  have hΦ := (frattini_le_of_le_qOf hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃
    hk hV₁₃ hy hPQ (hQ2.to_le hPQ)).trans (inf_le_left.trans hWQ₁)
  have hPKY := commutator_kY_le_of h1154 h1156 h hV₁ hX hPX (hPQ.trans hQT) hΦ (hPQ.trans hQO)
  have hQ₁KY := commutator_pCoreOf_kY_le L V₁
  have hKY : KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) ≤
      Subgroup.normalizer (V₁ : Set G) :=
    sup_le (kOf_le_normalizer_V₁ L V₁) (Y_le_normalizer_V₁ L V₁)
  have hG₁KY := SecD.le_normalizer_sup (SecD.normalizer_le_normalizer_kOf L V₁ V₁)
    (SecD.normalizer_le_normalizer_Y L V₁)
  have hG₁O := hG₁KY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hQG₁ : qOf T I V₁ y ≤ Subgroup.normalizer (V₁ : Set G) :=
    hQT.trans (SecA.IsVi.le_normalizer hV₁)
  have hQKY : ⁅qOf T I V₁ y, KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))⁆ ≤
      pCoreOf 2 (KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) := by
    rw [Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono le_rfl hdec).trans ?_
    refine commutator_sup_right_le ((hPQ.trans hQG₁).trans hG₁O)
      ((inf_le_left.trans hQG₁).trans hG₁O) ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact hPKY
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hCQ le_rfl).trans hQ₁KY
  exact le_pCoreOf_of_commutator_le hKY hG₁KY hQG₁ hQ2 hSQ (inf_le_left.trans inf_le_right)
    (exists_decomp_opp hTr h1102 h1103 h1110 h1141 h1143 h hV₁ hV₃ hk hy hopp) hQKY

end CFSG.Quasithin.Vol2.Ch11.SecF
