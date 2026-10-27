module

public import CFSG.Quasithin.EmptyFaithful.S1422Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

structure R1SettingLegacyBare {G : Type} [Group G] [Finite G] (K1 L2 S Zs : Subgroup G) : Prop where
  hyp : Hyp111 K1 L2 S
  qt : IsQuasithinSub (K1 ⊔ L2 ⊔ S)
  hnorm : (S.subgroupOf (S ⊔ borelOf L2 S)).Normal
  cComp_mem : K1 ∈ cComp (K1 ⊔ S)
  s3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3))
  solv : Group.IsSolvable ↥(L2 ⊔ S)
  card_Z : Nat.card Zs = 2
  Z_le : Zs ≤ pCoreOf 2 L2
  Z_cent : Zs ≤ Subgroup.centralizer (pCoreOf 2 L2 : Set G)
  Z_not_norm : ¬ L2 ≤ Subgroup.normalizer (Zs : Set G)
  Z_cent_S : Zs ≤ Subgroup.centralizer (S : Set G)
  K1_cent_Z : K1 ≤ Subgroup.centralizer (Zs : Set G)
  V_le : conjClosure Zs L2 ≤ pCoreOf 2 (K1 ⊔ S)
  V_card : Nat.card ↥(conjClosure Zs L2) = 4

structure R1Setting {G : Type} [Group G] [Finite G] (K1 L2 S Zs : Subgroup G) : Prop where
  hyp : Hyp111 K1 L2 S
  qt : IsQuasithinSub (K1 ⊔ L2 ⊔ S)
  hnorm : (S.subgroupOf (S ⊔ borelOf L2 S)).Normal
  cComp_mem : K1 ∈ cComp (K1 ⊔ S)
  s3 : Nonempty (OTwoQuot L2 ≃* Equiv.Perm (Fin 3))
  solv : Group.IsSolvable ↥(L2 ⊔ S)
  card_Z : Nat.card Zs = 2
  Z_le : Zs ≤ pCoreOf 2 (L2 ⊔ bigB K1 L2 S)
  Z_cent : Zs ≤ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ bigB K1 L2 S) : Set G)
  Z_not_norm : ¬ L2 ≤ Subgroup.normalizer (Zs : Set G)
  Z_cent_S : Zs ≤ Subgroup.centralizer (S : Set G)
  K1_cent_Z : K1 ≤ Subgroup.centralizer (Zs : Set G)
  V_le : conjClosure Zs L2 ≤ pCoreOf 2 (K1 ⊔ S)
  V_card : Nat.card ↥(conjClosure Zs L2) = 4

@[expose] def F112R1aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1Setting K1 L2 S Zs →
    IsL2Quot 2 (OTwoQuot K1) → Survivor10Vertex K1 L2 S ∨ Survivor11Vertex K1 L2 S

@[expose] def F112R1cStatementLegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)) →
    ¬ IsL2Quot 2 (OTwoQuot K1) → ¬ IsL2Quot 3 (OTwoQuot K1) → False

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem pCoreOf_le_pCoreOf_k1_sup_s (st : Setting1427 T M H K1) :
    pCoreOf 2 H ≤ pCoreOf 2 (K1 ⊔ sOf T K1) := by
  have hyp := st.hyp
  have N := st.notation_
  have hTH : T ≤ H := st.hStar.1.1
  have hXH : K1 ⊔ sOf T K1 ≤ H :=
    sup_le (N.le_K.trans (oTwoUpper_le H)) (inf_le_left.trans hTH)
  have hOS : pCoreOf 2 H ≤ sOf T K1 :=
    le_inf (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hyp.sylow hTH)) N.pCore_le
  exact le_pCoreOf_of_le_normalizer 2 (hOS.trans le_sup_right)
    (hXH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)

theorem l2Of_le_M (st : Setting1427 T M H K1) : l2Of T H (yOfL22 T M) ≤ M := by
  unfold l2Of
  exact sup_le (yOfL22_le T M) ((s2_le_T st.hyp).trans (T_le_M st.hyp))

theorem conjClosure_l2_le_pCoreOf_k1_sup_s (st : Setting1427 T M H K1) :
    conjClosure (quasithinOmegaOneCenter T) (l2Of T H (yOfL22 T M)) ≤ pCoreOf 2 (K1 ⊔ sOf T K1) :=
  (conjClosure_mono le_rfl (l2Of_le_M st)).trans
    ((st.hyp.vz_le_pCoreOf st.facts st.hStar).trans (pCoreOf_le_pCoreOf_k1_sup_s st))

theorem k1_le_centralizer_Z (st : Setting1427 T M H K1) :
    K1 ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  st.notation_.le_K.trans ((oTwoUpper_le H).trans
    (st.hyp.isUniqueM_centralizer st.hStar.1 st.hStar.2.1).1.2)

omit [Finite G] in
theorem card_eq_four_of_lt_le {V Z W : Subgroup G} [Finite G] (hZV : Z ≤ V) (hne : V ≠ Z)
    (hVW : V ≤ W) (hZ : Nat.card ↥Z = 2) (hW : Nat.card ↥W = 4) : Nat.card ↥V = 4 := by
  have hd : Nat.card ↥V ∣ 4 := hW ▸ Subgroup.card_dvd_of_le hVW
  have hgt : 2 < Nat.card ↥V := by
    by_contra hcon
    refine hne (Subgroup.eq_of_le_of_card_ge hZV ?_).symm
    rw [hZ]
    omega
  have hle4 : Nat.card ↥V ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  generalize Nat.card ↥V = d at hd hgt hle4 ⊢
  interval_cases d <;> omega

theorem card_conjClosure_l2 (st : Setting1427 T M H K1) :
    Nat.card ↥(conjClosure (quasithinOmegaOneCenter T) (l2Of T H (yOfL22 T M))) = 4 := by
  refine card_eq_four_of_lt_le (le_conjClosure _ _) ?_
    (conjClosure_mono le_rfl (l2Of_le_M st) : _ ≤ VZ T M) st.hyp.card_omegaOneCenter
    st.hyp.rank_two
  intro h
  refine not_l2_le_normalizer_Z (H := H) st.hyp st.facts ?_
  have := le_normalizer_conjClosure (quasithinOmegaOneCenter T) (l2Of T H (yOfL22 T M))
  rwa [h] at this

theorem r1Setting_of_setting1427_legacyBare (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ sOf T K1)
    (hf : CharTwo (l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1)))
    (h15 : pCoreOf 2 (K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1) = ⊥)
    (hbridge : ∀ (X : Type) [Group X], Nonempty (X ≃* Equiv.Perm (Fin 3)) → IsL2Quot 1 X) :
    R1SettingLegacyBare K1 (l2Of T H (yOfL22 T M)) (sOf T K1) (quasithinOmegaOneCenter T) := by
  have hyp := st.hyp
  have F := st.facts
  have N := st.notation_
  have hS2S : s2Of T H (yOfL22 T M) ≤ sOf T K1 := s2_le_sOf N h13
  have hBorel2 := borelOf_l2_eq h311 st h13
  have hnorm : ((sOf T K1).subgroupOf
      (sOf T K1 ⊔ borelOf (l2Of T H (yOfL22 T M)) (sOf T K1))).Normal := by
    rw [hBorel2, sup_eq_left.mpr hS2S, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  obtain ⟨e⟩ := oTwoQuot_l2_equiv_perm3 hyp F (lemma_14_2_14 h311 st)
  exact
    { hyp := hyp111_of_inputs h311 st h13 hf h15 hbridge
      qt := isQuasithinSub_of_qtke hyp.qtke _
      hnorm := hnorm
      cComp_mem := N.cComp_mem
      s3 := ⟨e⟩
      solv := isSolvable_l2_sup hyp F sOf_le_T
      card_Z := hyp.card_omegaOneCenter
      Z_le := Z_le_pCoreOf_l2 hyp F
      Z_cent := Z_le_centralizer_pCoreOf_l2 hyp F
      Z_not_norm := not_l2_le_normalizer_Z hyp F
      Z_cent_S := (quasithinOmegaOneCenter_le_center T).trans
        (inf_le_right.trans (Subgroup.centralizer_le sOf_le_T))
      K1_cent_Z := k1_le_centralizer_Z st
      V_le := conjClosure_l2_le_pCoreOf_k1_sup_s st
      V_card := card_conjClosure_l2 st }

end S1421

end CFSG.Quasithin
