module

public import CFSG.Quasithin.EmptyFaithful.S1421STDefs
public import CFSG.Quasithin.EmptyFaithful.S1421Easy

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem sOf_ne_of_not_pCore_le (st : Setting1427 T M H K1) (hO : ¬ pCoreOf 2 M ≤ sOf T K1) :
    sOf T K1 ≠ T := fun h => hO (pCoreOf_le_sOf_of_eq st h)

theorem T_le_normalizer_sOf (st : Setting1427 T M H K1) (hS : sOf T K1 ≠ T) :
    T ≤ Subgroup.normalizer ((sOf T K1 : Subgroup G) : Set G) := by
  rcases st.notation_.index with ⟨-, hTN⟩ | ⟨-, hrel⟩
  · exact absurd (inf_eq_left.mpr hTN) hS
  · have hn : ((sOf T K1).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hrel
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer sOf_le_T).mp hn

theorem sup_hall_inf_eq (st : Setting1427 T M H K1) {B : Subgroup G}
    (hB : IsHallOdd B (M ⊓ oTwoUpper H)) : B ⊔ (T ⊓ oTwoUpper H) = M ⊓ oTwoUpper H :=
  sup_eq_of_relIndex_two_pow_of_odd hB.1 (inf_le_inf_right _ st.hyp.m_max.1.2) hB.2.2
    (Nat.not_even_iff_odd.mp fun he =>
      (isSylowTwoOf_inf_oTwoUpper st).2.2 (even_iff_two_dvd.mp he))

theorem sup_borelOf_eq_of_cfg (st : Setting1427 T M H K1) (cfg : L34Cfg T M H K1) :
    sOf T K1 ⊔ borelOf K1 (sOf T K1) = sOf T K1 ⊔ (M ⊓ oTwoUpper H) := by
  have N := st.notation_
  obtain ⟨B, hB⟩ := exists_isHallOdd_borel st
  have hBK1 : B ≤ K1 := (cfg.hall B hB).1
  have hTKS : T ⊓ oTwoUpper H ≤ sOf T K1 := le_inf inf_le_left N.inf_le
  have hBN : B ≤ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) := by
    have h1 : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
      hB.1.trans N.borel_inf
    have h2 : B ≤ Subgroup.normalizer (K1 : Set G) := hBK1.trans Subgroup.le_normalizer
    intro b hb
    have h3 := Subgroup.inf_normalizer_le_normalizer_inf ⟨h1 hb, h2 hb⟩
    have e : (T ⊓ oTwoUpper H) ⊓ K1 = T ⊓ K1 := by
      rw [inf_assoc, inf_eq_right.mpr N.le_K]
    rwa [e] at h3
  have hBB : B ≤ borelOf K1 (sOf T K1) := by
    refine le_inf hBK1 ?_
    rw [sOf_inf_K1]
    exact hBN
  have hBorLe : borelOf K1 (sOf T K1) ≤ M ⊓ oTwoUpper H := by
    unfold borelOf
    rw [sOf_inf_K1]
    exact le_inf N.borel_le (inf_le_left.trans N.le_K)
  refine le_antisymm (sup_le le_sup_left (hBorLe.trans le_sup_right)) ?_
  rw [← sup_hall_inf_eq st hB]
  exact sup_le le_sup_left (sup_le (hBB.trans le_sup_right) (hTKS.trans le_sup_left))

end S1421

theorem hyp111fInput_of_lemma14212 (h12 : Lemma14212) : Hyp111fInput := by
  intro G _ _ T M H K1 st hO _
  rcases h12 G T M H K1 st with h | cfg
  · exact absurd h hO
  · have hyp := st.hyp
    have N := st.notation_
    have hTM : T ≤ M := hyp.m_max.1.2
    have hTH : T ≤ H := st.hStar.1.1
    have hS : S1421.sOf T K1 ≠ T := S1421.sOf_ne_of_not_pCore_le st hO
    have hTS := S1421.T_le_normalizer_sOf st hS
    have hX1 : S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔ borelOf K1 (S1421.sOf T K1) =
        S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔ (M ⊓ oTwoUpper H) := by
      rw [sup_assoc, S1421.sup_borelOf_eq_of_cfg st cfg, ← sup_assoc]
    rw [hX1]
    set X : Subgroup G := S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔ (M ⊓ oTwoUpper H) with hX
    have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
      hTH.trans (le_normalizer_oTwoUpper H)
    have hTKM : T ≤ Subgroup.normalizer ((M ⊓ oTwoUpper H : Subgroup G) : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hTK ht) x]
      exact and_congr_left fun _ => by
        constructor
        · intro hx
          have := M.mul_mem (M.mul_mem (hTM ht) hx) (M.inv_mem (hTM ht))
          exact this
        · intro hx
          have := M.mul_mem (M.mul_mem (M.inv_mem (hTM ht)) hx) (hTM ht)
          simpa [mul_assoc] using this
    have hTL : T ≤ Subgroup.normalizer ((S1421.l2Of T H (yOfL22 T M) : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (S1421.T_le_normalizer_y hyp) (S1421.T_le_normalizer_s2 hyp hTH)
    have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
      F1.le_normalizer_sup (F1.le_normalizer_sup hTL hTS) hTKM
    have hXM : X ≤ M := by
      have hYM := yOfL22_le T M
      have hL2 : S1421.l2Of T H (yOfL22 T M) ≤ M :=
        sup_le hYM (sup_le ((pCoreOf_le 2 _).trans hYM) (inf_le_left.trans hTM))
      exact sup_le (sup_le hL2 (S1421.sOf_le_T.trans hTM)) inf_le_left
    set X' : Subgroup G := X ⊔ T with hX'
    have hX'N : X' ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hTX
    have hX'M : X' ≤ M := sup_le hXM hTM
    obtain ⟨hVred, hVT⟩ := S1421.isTwoReducedIn_VZ_of_hyp hyp
    have hVne : VZ T M ≠ ⊥ := by
      intro hV
      have h4 := hyp.rank_two
      rw [hV, Subgroup.card_bot] at h4
      omega
    have hVX' : VZ T M ≤ pCoreOf 2 X' :=
      le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right) (hX'M.trans hVred.2.1)
        (hyp.sylow.1.to_le hVT)
    have hO' : pCoreOf 2 X' ≠ ⊥ := by
      intro hb
      rw [hb] at hVX'
      exact hVne (le_bot_iff.mp hVX')
    have hX'char : CharTwo X' := charTwo_of_inH' hyp.qtke hyp.sylow ⟨le_sup_right, hO'⟩
    exact CharTwo.of_normal hX'char le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hX'N)

end CFSG.Quasithin
