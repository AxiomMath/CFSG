module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSz
public import CFSG.Quasithin.Background.OTwoUpperPerfect
public import CFSG.Quasithin.Recognition.Stroth.BenderChief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.X7 CFSG.Quasithin.H13 CFSG.Quasithin.H13.AS91
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83_partTwo_comm_mem_minimal
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    {Y : Subgroup G} (hYZ : Y ≤ Z1 L1 L2 S) (hYne : Y ≠ ⊥)
    (hYN : L1 ⊔ S ≤ Subgroup.normalizer (Y : Set G))
    (hYmin : ∀ Y' : Subgroup G, Y' ≤ Y → L1 ⊔ S ≤ Subgroup.normalizer (Y' : Set G) →
      Y' = ⊥ ∨ Y' = Y)
    {h z : G} (hh : h ∈ L1 ⊔ S) (hz : z ∈ Z1 L1 L2 S) :
    h * z * h⁻¹ * z⁻¹ ∈ Y := by
  classical
  have eSz : oTwoQuot ↥L1 ≃* Sz a := Classical.choice hSz
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ1H : Q1 L1 L2 S ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  have hZ1Q1 : Z1 L1 L2 S ≤ Q1 L1 L2 S := omegaOneCenterOf_le _
  have hZ1H : Z1 L1 L2 S ≤ L1 ⊔ S := hZ1Q1.trans hQ1H
  have hZ1ea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hZ1pg : IsPGroup 2 (Z1 L1 L2 S) := hZ1ea.isPGroup
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    have hP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
      sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    exact hP1.trans ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  have hQ1C : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    Subgroup.le_centralizer_iff.mp (Z1_le_centralizer_Q1 L1 L2 S)
  have hC : Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥ :=
    str83_partTwo_centralizer_sup_z1_eq_bot hF hB ha hSz hL2 hZ2
  have hszU3H : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) :=
    Or.inl ⟨a, ha, rfl, ⟨(oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
      ((oTwoQuotSupEquiv hF.1).trans eSz)⟩⟩
  have hEqH : L1 ⊔ S = oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S := by
    have hperf : Group.IsPerfect (oTwoQuot ↥(L1 ⊔ S)) := hszU3H.facts.1.1
    have h := eq_oTwoUpper_sup_pCoreOf_of_perfect (H := L1 ⊔ S) hperf
    rwa [hpCore1] at h
  obtain ⟨E, _X0, hES, hEea, hEnotQ, _hQ1X0, _hX0S, _hsupX0, _hX0rel, _hCX0, hEqC⟩ :=
    str83_partTwo_generator_data hF hB ha hSz hL2 hII hJ
  obtain ⟨t, htE, htQ⟩ : ∃ t ∈ E, t ∉ Q1 L1 L2 S := by
    by_contra hcon
    push Not at hcon
    exact hEnotQ hcon
  have htH : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) (hES htE)
  have ht2 : t * t ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [show t * t = 1 from by rw [← pow_two]; exact hEea.2 t htE]
    exact (pCoreOf 2 (L1 ⊔ S)).one_mem
  have htO : t ∉ pCoreOf 2 (L1 ⊔ S) := by
    rwa [hpCore1]
  have hcent_t : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCEidx : (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) =
      (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← Subgroup.inf_relIndex_left (Z1 L1 L2 S) (Subgroup.centralizer (E : Set G))]
    exact hEqC
  have hTbound : (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) ≤
      (2 ^ (2 * a + 1)) ^ 2 := by
    have h1 : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htE)
    have h2 : (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) ≤
        (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) :=
      Subgroup.relIndex_le_of_le_left h1 (D15Proof.relIndex_ne_zero _ _)
    exact h2.trans (le_of_eq hCEidx)
  have hYH : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) Y :=
    F112W.isNormalIn_of_le_normalizer hYZ hYN
  have hZ1normal : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl hHZ1
  obtain ⟨b, hYser⟩ := D15Proof.exists_isChiefSeriesFrom (H := L1 ⊔ S)
    (U := Z1 L1 L2 S) Y hYH
  obtain ⟨c, hbetween⟩ := F112W.exists_isChiefSeriesBetween (H := L1 ⊔ S)
    (U := Z1 L1 L2 S) (W := Y) hYH (Z1 L1 L2 S) hZ1normal hYZ
  have hfull : IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) (c + b) :=
    hbetween.append hYser
  have hb1 : b = 1 := by
    cases hYser with
    | bot => exact absurd rfl hYne
    | @central _N L n hstep hcent hs =>
      exfalso
      have hLY : L ≤ Y := hstep.2.2.1.le
      have hLN : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
        D14.le_normalizer_of_isNormalIn hstep.2.1
      have hLbot : L = ⊥ := by
        rcases hYmin L hLY hLN with h | h
        · exact h
        · exact absurd h hstep.2.2.1.ne
      have hYcent : Y ≤ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 : g * y * g⁻¹ * y⁻¹ = 1 := by
          have h := hcent g hg y hy
          rwa [hLbot, Subgroup.mem_bot] at h
        calc y * g = (g * y * g⁻¹ * y⁻¹) * (y * g) := by rw [h1, one_mul]
          _ = g * y := by group
      have hYbot : Y ≤ (⊥ : Subgroup G) := by
        have hle : Y ≤ Z1 L1 L2 S ⊓
            Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) := le_inf hYZ hYcent
        rwa [hC] at hle
      exact hYne (le_bot_iff.mp hYbot)
    | @noncentral _N L n hstep _hnc hs =>
      have hLY : L ≤ Y := hstep.2.2.1.le
      have hLN : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
        D14.le_normalizer_of_isNormalIn hstep.2.1
      have hLbot : L = ⊥ := by
        rcases hYmin L hLY hLN with h | h
        · exact h
        · exact absurd h hstep.2.2.1.ne
      subst hLbot
      have hn : n = 0 := F112W.eq_zero_of_isChiefSeriesFrom_bot hs
      omega
  have hM6 := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S) (U := Z1 L1 L2 S)
    (q := 2 ^ (2 * a + 1)) (c := c + b) hszU3H hZ1pg hZ1H hfull htH ht2 htO
  rw [hcent_t] at hM6
  have hle : ((2 ^ (2 * a + 1)) ^ 2) ^ (c + b) ≤ ((2 ^ (2 * a + 1)) ^ 2) ^ 1 := by
    simpa using hM6.trans hTbound
  have hbase : 1 < (2 ^ (2 * a + 1)) ^ 2 := by
    have h2 : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
  have hcb : c + b ≤ 1 := (Nat.pow_le_pow_iff_right hbase).mp hle
  have hc0 : c = 0 := by omega
  have hZ1Q : Z1 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ S) := by
    rw [hpCore1]
    exact hZ1Q1
  have hbetween0 : F112W.IsChiefSeriesBetween (L1 ⊔ S) (Z1 L1 L2 S) Y (Z1 L1 L2 S) 0 := by
    rwa [hc0] at hbetween
  have hcommZ1 : ⁅Z1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ Y :=
    (F112W.isChiefSeriesBetween_zero_iff hZ1H hZ1Q hYH hZ1normal hYZ).mp hbetween0
  have hHle : L1 ⊔ S ≤ oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S := le_of_eq hEqH
  have hNO2 : Q1 L1 L2 S ≤ Subgroup.normalizer (oTwoUpper (L1 ⊔ S) : Set G) :=
    hQ1H.trans (le_normalizer_oTwoUpper (L1 ⊔ S))
  have hcommH : ⁅L1 ⊔ S, Z1 L1 L2 S⁆ ≤ Y :=
    commutator_le_of_le_oTwoUpper_sup hHle hNO2 hQ1C hcommZ1
  have hmem := hcommH (Subgroup.commutator_mem_commutator hh hz)
  simpa [commutatorElement_def] using hmem

end CFSG.Quasithin.Stroth

end
