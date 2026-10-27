module

public import CFSG.Quasithin.EmptyFaithful.S1421STC3Ten
public import CFSG.Quasithin.EmptyFaithful.S1421STC3Fac
public import CFSG.Quasithin.EmptyFaithful.S1421STf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem isPGroup_sOf (st : Setting1427 T M H K1) : IsPGroup 2 (sOf T K1) :=
  st.hyp.sylow.1.to_le sOf_le_T

theorem relIndex_sOf_eq_two (st : Setting1427 T M H K1) (hlt : sOf T K1 < T) :
    (sOf T K1).relIndex T = 2 := by
  rcases st.notation_.index with ⟨-, hTN⟩ | ⟨-, hrel⟩
  · exact absurd (inf_eq_left.mpr hTN) hlt.ne
  · exact hrel

theorem omegaOneCenterOf_sOf_ne_bot (st : Setting1427 T M H K1) :
    omegaOneCenterOf (sOf T K1) ≠ ⊥ := by
  refine omegaOneCenterOf_ne_bot_of_isPGroup (isPGroup_sOf st) fun h => ?_
  have h1 : T ⊓ K1 ≤ sOf T K1 := by
    rw [← sOf_inf_K1]
    exact inf_le_left
  exact inf_ne_bot st.notation_ (le_bot_iff.mp (h ▸ h1))

theorem normalizer_omegaOneCenter_sOf_le (st : Setting1427 T M H K1) (hlt : sOf T K1 < T)
    (h210 : Lemma14210) {Kc : Subgroup G} (hKc : Kc ∈ cComp (mcOf T)) (hK1Kc : K1 ≤ Kc)
    (hKT : oTwoUpper H ≤ Kc ⊔ T) :
    Subgroup.normalizer (omegaOneCenterOf (sOf T K1) : Set G) ≤ mcOf T := by
  have hyp := st.hyp
  have hcent : K1 ≤ Subgroup.centralizer (omegaOneCenterOf (sOf T K1) : Set G) :=
    hK1Kc.trans (le_centralizer_omegaOneCenter_sOf st hKc hKT)
  have hTN : T ≤ Subgroup.normalizer (omegaOneCenterOf (sOf T K1) : Set G) :=
    (T_le_normalizer_sOf st hlt.ne).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hKTN : K1 ⊔ T ≤ Subgroup.normalizer (omegaOneCenterOf (sOf T K1) : Set G) :=
    sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) hTN
  have hZ2 : IsPGroup 2 (omegaOneCenterOf (sOf T K1)) :=
    (isPGroup_sOf st).to_le (A4.omegaOneCenterOf_le _)
  have hO : pCoreOf 2 (Subgroup.normalizer (omegaOneCenterOf (sOf T K1) : Set G)) ≠ ⊥ := by
    intro h
    have h1 := le_pCoreOf_of_le_normalizer 2 (Subgroup.le_normalizer :
      omegaOneCenterOf (sOf T K1) ≤ Subgroup.normalizer (omegaOneCenterOf (sOf T K1) : Set G))
      le_rfl hZ2
    rw [h] at h1
    exact omegaOneCenterOf_sOf_ne_bot st (le_bot_iff.mp h1)
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hTSyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.toQTFE14.t_le_mc
  have huniq := h210 G T M H K1 st hlt T hTSyl sOf_le_T
  have heq := huniq.2 M' ⟨hM'.1, hKTN.trans hM'.2⟩
  rw [heq] at hM'
  exact hM'.2

theorem isSylowTwoOf_of_lt (st : Setting1427 T M H K1) (hlt : sOf T K1 < T) {T1 : Subgroup G}
    (hT1 : IsPGroup 2 T1) (hS : sOf T K1 ≤ T1) (hne : ¬ T1 ≤ sOf T K1) :
    quasithinIsSylowTwo T1 ∧ T1 ≤ Subgroup.normalizer ((sOf T K1 : Subgroup G) : Set G) := by
  have hrel := relIndex_sOf_eq_two st hlt
  have hTodd : ¬ 2 ∣ T.index := st.hyp.sylow.2
  obtain ⟨n, hn⟩ := hT1.index ((sOf T K1).subgroupOf T1)
  have hn' : (sOf T K1).relIndex T1 = 2 ^ n := hn
  have hn1 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hn'
    exact hne hn'
  have h1 : (sOf T K1).relIndex T1 * T1.index = (sOf T K1).index :=
    Subgroup.relIndex_mul_index hS
  have h2 : (sOf T K1).relIndex T * T.index = (sOf T K1).index :=
    Subgroup.relIndex_mul_index sOf_le_T
  rw [hn'] at h1
  rw [hrel] at h2
  have hn2 : n = 1 := by
    by_contra hn2
    have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have h5 : 2 ∣ T.index := by
      have : 2 * 2 ∣ 2 * T.index := by
        rw [h2, ← h1]
        exact Dvd.dvd.mul_right h4 _
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    exact hTodd h5
  subst hn2
  have h3 : T1.index = T.index := by
    have : 2 * T1.index = 2 * T.index := by
      rw [pow_one] at h1
      rw [h1, h2]
    omega
  refine ⟨⟨hT1, by rw [h3]; exact hTodd⟩, ?_⟩
  have hnorm : ((sOf T K1).subgroupOf T1).Normal := by
    apply Subgroup.normal_of_index_eq_two
    rw [pow_one] at hn
    exact hn
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hS).mp hnorm

end S1421

theorem lemma14215Step2_of_14209 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h209 : Lemma14209Used) : Lemma14215Step2 := by
  intro G _ _ T M H K1 st hlt h13 M₁ hM₁ hT
  have hyp := st.hyp
  have h210 := lemma14210_of_14209 h37 h38 h39 h209
  obtain ⟨Kc, hKc, hK1Kc, hKT, -⟩ := h209 G T M H K1 st hlt
  have hN := S1421.normalizer_omegaOneCenter_sOf_le st hlt h210 hKc hK1Kc hKT
  have hSG0 : S1421.sOf T K1 ≤ K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 := le_sup_right
  have hK1G0 : K1 ≤ K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 :=
    le_sup_left.trans le_sup_left
  have hSM₁ : S1421.sOf T K1 ≤ M₁ := hSG0.trans hM₁.2
  have hK1M₁ : K1 ≤ M₁ := hK1G0.trans hM₁.2
  obtain ⟨T1, hT1, hST1⟩ := A4.exists_isSylowTwoOf_ge hSM₁ (S1421.isPGroup_sOf st)
  by_cases hEq : T1 ≤ S1421.sOf T K1
  · rwa [← le_antisymm hEq hST1]
  · exfalso
    obtain ⟨hT1syl, hT1N⟩ := S1421.isSylowTwoOf_of_lt st hlt hT1.2.1 hST1 hEq
    have hT1Mc : T1 ≤ mcOf T :=
      hT1N.trans ((A4.normalizer_le_normalizer_omegaOneCenterOf _).trans hN)
    have hT1S : IsSylowTwoOf T1 (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo hT1syl hT1Mc
    have huniq := h210 G T M H K1 st hlt T1 hT1S hST1
    have heq := huniq.2 M₁ ⟨hM₁.1, sup_le hK1M₁ hT1.1⟩
    exact hT (heq ▸ hyp.toQTFE14.t_le_mc)

end CFSG.Quasithin
