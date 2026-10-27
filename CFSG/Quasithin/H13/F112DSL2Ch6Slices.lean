module

public import CFSG.Quasithin.Vol2.Ch6Sec1Res619
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DF
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DN
public import CFSG.Quasithin.H13.F112DSL2Slices
public import CFSG.Quasithin.Recognition.GoldschmidtF112RQ
public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19F
public import CFSG.Quasithin.Vol2.Ch6Sec1Lin2Excl
public import CFSG.Quasithin.Vol2.Ch6Sp

public section

namespace CFSG.Quasithin.H13

section Res619Twins

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem rootFourLift_of_dsA_slices (hDSA : DSAL2Statement) (hG24 : G24LongRootSplit)
    (h : Hyp611Nat G T M L V 2) {T' : Subgroup G} (hT' : Hyp611 G T' M L V 2) {H A : Subgroup G}
    (hR : Hyp111R L A T') (hAH : A ≤ H) (ψ : ↥H →* Equiv.Perm (Fin 5))
    (hψA : (A.subgroupOf H).map ψ ≤ alternatingGroup (Fin 5))
    (hker : ∀ a : ↥H, (a : G) ∈ A → ψ a = 1 → (a : G) ∈ pCoreOf 2 A)
    (hA60 : Nat.card (oTwoQuot ↥A) = 60)
    (hAns : ¬ Group.IsSolvable ↥A) (hnb : ¬ (IsBlock2 A A ∧ ∃ f : ℕ, IsLin2Type A f)) :
    E1.LiftS5.RootFourLift H T' ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT'G : IsSylowTwoOf T' ⊤ :=
    ⟨le_top, hT'.sylow.1, by
      rw [show (T'.subgroupOf ⊤).index = T'.index from Subgroup.relIndex_top_right T']
      exact hT'.sylow.2⟩
  have hS : IsSylowTwoOf T' (bigB L A T') := F7.isSylowTwoOf_mono_right hT'G le_sup_right le_top
  have hyp := hyp111_spCh6 hR hS
  have hqt : IsQuasithinSub (L ⊔ A ⊔ spCh6 L A T') := isQuasithinSub_of_qtke' h.qtke _
  have hnorm := spCh6_normal_left hR hS
  obtain ⟨L1', L2', hsw, -, hlist, -⟩ :=
    hDSA G L A (spCh6 L A T') hyp hqt (Or.inl hnorm) h.not_isSolvable_L hAns
      (Or.inl ⟨2, h.isL2Quot_L⟩)
  have hcL := h.card_oTwoQuot_L
  have hc1 : Nat.card (oTwoQuot ↥L1') = 60 := by
    rcases hsw with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> assumption
  have hc2 : Nat.card (oTwoQuot ↥L2') = 60 := by
    rcases hsw with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> assumption
  have hlift : ∀ E : Subgroup G, E ≤ spCh6 L A T' ⊓ A → IsElemAbelian 2 E → Nat.card E = 4 →
      E ⊓ pCoreOf 2 A = ⊥ → E1.LiftS5.RootFourLift H T' ψ := by
    intro E hE hEe hE4 hEO
    have hEA : E ≤ A := hE.trans inf_le_right
    refine ⟨E, (hE.trans inf_le_left).trans (spCh6_le hS), hEe, fun x hx => hψA
      (Subgroup.map_mono (fun y hy => Subgroup.mem_subgroupOf.mpr
        (hEA (Subgroup.mem_subgroupOf.mp hy))) hx), ?_⟩
    have hinj : Function.Injective (ψ.comp (E.subgroupOf H).subtype) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨x, hx⟩ hx1
      have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
      have h1 : ψ x = 1 := hx1
      have hxO := hker x (hEA hxE) h1
      have : (x : G) ∈ E ⊓ pCoreOf 2 A := ⟨hxE, hxO⟩
      rw [hEO, Subgroup.mem_bot] at this
      exact Subtype.ext (Subtype.ext this)
    have hEH : E ≤ H := hEA.trans hAH
    have hrange : (E.subgroupOf H).map ψ = (ψ.comp (E.subgroupOf H).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    calc Nat.card ↥((E.subgroupOf H).map ψ) =
        Nat.card ↥(ψ.comp (E.subgroupOf H).subtype).range := by rw [hrange]
      _ = Nat.card ↥(E.subgroupOf H) := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
      _ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
      _ = 4 := hE4
  unfold F112ListA at hlist
  dsimp only at hlist
  rcases hlist with ⟨f, -, -, hb1, ht1, hb2, ht2⟩ | ⟨f, -, -, hb1, ht1, hb2, ht2⟩ |
      ⟨f, hf, hAm, hq1, hq2, -, -⟩ | ⟨f, hf, -, hq1, -, -, -⟩ | ⟨a, ha, -, -, -, hq2, -⟩ |
      ⟨f, hf, -, -, -, -, hq2, -⟩ | ⟨-, -, -, hq2, -⟩
  ·
    exfalso
    rcases hsw with ⟨-, e⟩ | ⟨e, -⟩
    · exact hnb ⟨e ▸ hb2, f, e ▸ ht2⟩
    · exact hnb ⟨e ▸ hb1, f, e ▸ ht1⟩
  ·
    exfalso
    rcases hsw with ⟨-, e⟩ | ⟨e, -⟩
    · exact hnb ⟨e ▸ hb2, f, e ▸ ht2⟩
    · exact hnb ⟨e ▸ hb1, f, e ▸ ht1⟩
  ·
    have hf2 : f = 2 := eq_two_of_isL2Quot_sixty (by omega) hq1 hc1
    subst hf2
    rcases hsw with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2] at hAm
      rw [e1] at hq1
      rw [e2] at hq2
      obtain ⟨-, E, hE, hEe, hE4, hEO⟩ := hG24 G L A _ 2 le_rfl hyp hAm hq1 hq2
      exact hlift E hE hEe (by rw [hE4]; norm_num) hEO
    · rw [e1, e2] at hAm
      rw [e1] at hq1
      rw [e2] at hq2
      have hAm' : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (A ⊔ bigB A L (spCh6 L A T'))
          (L ⊔ bigB A L (spCh6 L A T'))) (IsG2Over 2) := hAm
      obtain ⟨⟨E, hE, hEe, hE4, hEO⟩, -⟩ := hG24 G A L _ 2 le_rfl hyp.symm hAm' hq1 hq2
      exact hlift E hE hEe (by rw [hE4]; norm_num) hEO
  ·
    exfalso
    have := eq_two_of_isL2Quot_sixty (by omega) hq1 hc1
    omega
  ·
    exfalso
    have := eq_two_of_isL2Quot_sixty (by omega) hq2 hc2
    omega
  ·
    exfalso
    have := eq_two_of_isL2Quot_sixty (by omega) hq2 hc2
    omega
  ·
    exfalso
    have := eq_two_of_isL2Quot_sixty (by omega) hq2 hc2
    omega

theorem res619S5_core_slices (h432 : Stmt4_3_2)
    (hR1 : L2RankOneSylowFact) (hDSA : DSAL2Statement) (hG24 : G24LongRootSplit)
    (h6 : Hyp611Nat G T M L V 2)
    {T' D' P : Subgroup G} (hT' : Hyp611 G T' M L V 2)
    (hPI : P ≤ ch619I T L V) (hIP : ch619I T L V ≤ Subgroup.normalizer (P : Set G))
    (hT'P : T' ≤ Subgroup.normalizer (P : Set G))
    (ψ : ↥(P ⊔ T') →* Equiv.Perm (Fin 5))
    (hψPs : Function.Surjective (ψ.comp (Subgroup.inclusion le_sup_left)))
    (hkerP : IsPGroup 2 (ψ.comp (Subgroup.inclusion (le_sup_left : P ≤ P ⊔ T'))).ker)
    (hO : ∀ x (hx : x ∈ P), x ∈ pCoreOf 2 (ch619I T L V) →
      ψ ⟨x, Subgroup.mem_sup_left hx⟩ = 1)
    (hHs : IsHStar T' M (P ⊔ T'))
    (hsyl' : IsSylowTwoOf (T' ⊓ ch619I T L V) (ch619I T L V))
    (hT'Z : T' ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hrk : CFSG.Open.pRank 3 (ch619I T L V) ≤ 2) (hD'L : D' ≤ L) (hcD' : Nat.card D' = 3)
    (hD'Z : D' ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hD'I : D' ≤ Subgroup.normalizer (ch619I T L V : Set G))
    (hD'S : D' ≤ Subgroup.normalizer ((T' ⊓ ch619I T L V : Subgroup G) : Set G))
    (hnb : ¬ (IsBlock2 (L619.threePart P) (L619.threePart P) ∧
      ∃ f : ℕ, IsLin2Type (L619.threePart P) f)) :
    E1.LiftS5.RootFourLift (P ⊔ T') T' ψ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψP : ↥P →* Equiv.Perm (Fin 5) := ψ.comp (Subgroup.inclusion le_sup_left) with hψP
  have hψs : Function.Surjective ψ := fun g => by
    obtain ⟨x, hx⟩ := hψPs g
    exact ⟨_, hx⟩
  have hT'A : T' ≤ Subgroup.normalizer (L619.threePart P : Set G) :=
    hT'P.trans (L619.normalizer_le_normalizer_threePart P)
  have hAP : L619.threePart P ≤ P := L619.threePart_le P
  have hAI : L619.threePart P ≤ ch619I T L V := hAP.trans hPI
  have hAH : L619.threePart P ≤ P ⊔ T' := hAP.trans le_sup_left
  have hkerψ : IsPGroup 2 ψ.ker :=
    L619.isPGroup_ker_sup ψP hT'.sylow.1 hT'P hψPs hkerP ψ (fun _ => rfl)
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := L619.card_perm_five
  have hA3 : L619.ThreeComp (ch619I T L V) (L619.threePart P) :=
    L619.threeComp_of ψP hAI hIP hψPs hkerP
      (fun N hN hNn => L619.threePartTop_simple_of_perm5 (MulEquiv.refl _) hN hNn)
      (by rw [h120]; decide) (by rw [h120]; decide)
  have hwit := L619.exists_commutator_not_mem ψP hψPs L619.center_perm5
    (by rw [h120]; decide) hO
  have hP3 : ∀ x ∈ P, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ L619.threePart P :=
    fun x hx k hk => L619.mem_threePart hx hk
  have hDA : D' ≤ Subgroup.normalizer (L619.threePart P : Set G) := fun d hdD =>
    mem_normalizer_of_conjSub_le' (L619.ThreeComp.conjSub_eq_of_pRank hrk hA3 hPI hIP hP3
      hwit (hD'I hdD) (by
        have h := pow_card_eq_one' (G := ↥D') (x := ⟨d, hdD⟩)
        rw [hcD'] at h
        simpa using congrArg Subtype.val h)).le
  have hS'P : IsSylowTwoOf ((T' ⊓ ch619I T L V) ⊓ P) P := A4.isSylowTwoOf_inf_normal hsyl' hPI hIP
  have hkerS : ψP.ker.map P.subtype ≤ (T' ⊓ ch619I T L V) ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    have hP2 : IsPGroup 2 (ψP.ker.map P.subtype) := hkerP.map _
    have hnorm : P ≤ Subgroup.normalizer ((ψP.ker.map P.subtype : Subgroup G) : Set G) := by
      intro p hp
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨p, hp⟩ * w * ⟨p, hp⟩⁻¹, (MonoidHom.normal_ker _).conj_mem w hw _, rfl⟩
      · rintro ⟨w, hw, hwu⟩
        refine ⟨⟨p, hp⟩⁻¹ * w * ⟨p, hp⟩, ?_, ?_⟩
        · have := (MonoidHom.normal_ker ψP).conj_mem w hw ⟨p, hp⟩⁻¹
          simpa using this
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hwu ⊢
          rw [hwu]
          group
    have hle : ψP.ker.map P.subtype ≤ pCoreOf 2 P :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) hnorm hP2
    exact F7.isSylowTwoOf_pCoreOf_le hS'P (hle ⟨x, hx, rfl⟩)
  have htop : L619.threePartTop (Equiv.Perm (Fin 5)) ⊔
      (((T' ⊓ ch619I T L V) ⊓ P).subgroupOf P).map ψP = ⊤ :=
    L619.threePartTop_sup_eq_top_of_perm5 (MulEquiv.refl _)
      (L619.isSylowTwoOf_map_surj hS'P ψP hψPs)
  have hPA : P ≤ L619.threePart P ⊔ ((T' ⊓ ch619I T L V) ⊓ P) :=
    L619.le_threePart_sup ψP hψPs inf_le_right hkerS htop
  have hAM : ¬ L619.threePart P ≤ M := by
    intro hAM
    apply hHs.2.1
    refine sup_le (hPA.trans (sup_le hAM ?_)) hT'.T_le
    exact (inf_le_left.trans inf_le_left).trans hT'.T_le
  have hZ2 : IsPGroup 2 (ch6ZS T L V) :=
    (B2F.isPGroup_of_isElemAbelian h6.toHyp611.isElemAbelian).to_le h6.ZS_le
  have hT'syl : IsSylowTwoOf T' ⊤ :=
    ⟨le_top, hT'.sylow.1, by
      rw [show (T'.subgroupOf ⊤).index = T'.index from Subgroup.relIndex_top_right T']
      exact hT'.sylow.2⟩
  have hZT : ch6ZS T L V ≤ T' := by
    have hsup : IsPGroup 2 ↥(ch6ZS T L V ⊔ T') :=
      hZ2.to_sup_of_normal_left' hT'.sylow.1 hT'Z
    have := F1.eq_of_isSylowTwoOf_le hT'syl le_top hsup le_sup_right
    rw [this]
    exact le_sup_left
  have hsylA : IsSylowTwoOf (T' ⊓ L619.threePart P) (L619.threePart P) := by
    have h1 := A4.isSylowTwoOf_inf_normal hsyl' hAI hA3.normal
    have e : (T' ⊓ ch619I T L V) ⊓ L619.threePart P = T' ⊓ L619.threePart P :=
      le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left
        (inf_le_right.trans hAI)) inf_le_right)
    rwa [e] at h1
  set ψA : ↥(L619.threePart P) →* Equiv.Perm (Fin 5) := ψ.comp (Subgroup.inclusion hAH)
    with hψA
  have hψAP : ∀ a : ↥(L619.threePart P), ψA a = ψP ⟨a, hAP a.2⟩ := fun _ => rfl
  have hrangeA : ψA.range = alternatingGroup (Fin 5) := by
    rw [← L619.threePartTop_perm5]
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      rw [hψAP]
      exact L619.psi_mem_threePartTop ψP a.2
    · intro k hk
      obtain ⟨x, hx, hxk⟩ := L619.exists_preimage_threePartTop ψP hψPs hk
      exact ⟨⟨x, hx⟩, by rw [hψAP]; exact hxk⟩
  have hkerA2 : IsPGroup 2 ψA.ker := by
    refine (hkerψ.comap_of_injective (Subgroup.inclusion hAH)
      (Subgroup.inclusion_injective hAH)).to_le ?_
    intro a ha
    exact ha
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  have hkerA : ψA.ker = CFSG.Open.pCore 2 ↥(L619.threePart P) := by
    apply le_antisymm
    · exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 _
        (MonoidHom.normal_ker _) hkerA2
    · intro a ha
      set N : Subgroup (Equiv.Perm (Fin 5)) := (CFSG.Open.pCore 2 ↥(L619.threePart P)).map ψA
        with hN
      have hNA : N ≤ alternatingGroup (Fin 5) := hrangeA ▸ Subgroup.map_le_range _ _
      have hN2 : IsPGroup 2 N :=
        (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).map ψA
      have hNn : (N.subgroupOf (alternatingGroup (Fin 5))).Normal := by
        refine ⟨fun x hx g => ?_⟩
        have hg : (g : Equiv.Perm (Fin 5)) ∈ ψA.range := by rw [hrangeA]; exact g.2
        obtain ⟨b, hb⟩ := hg
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        obtain ⟨u, hu, hux⟩ := hx
        refine ⟨b * u * b⁻¹, ?_, ?_⟩
        · exact (CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2).conj_mem u hu b
        · simp only [map_mul, map_inv, hux, hb, Subgroup.coe_mul, Subgroup.coe_inv]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (N.subgroupOf (alternatingGroup (Fin 5))) with hb | ht
      · have hmem : ψA a ∈ N := ⟨a, ha, rfl⟩
        have : (⟨ψA a, hNA hmem⟩ : ↥(alternatingGroup (Fin 5))) ∈
            N.subgroupOf (alternatingGroup (Fin 5)) := hmem
        rw [hb, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      · exfalso
        have hle : alternatingGroup (Fin 5) ≤ N := fun x hx => by
          have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 5))) ∈
              N.subgroupOf (alternatingGroup (Fin 5)) := ht ▸ Subgroup.mem_top _
          exact this
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hN2.to_le hle)
        rw [h60] at hk
        have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega
  have hrA : ψA.range ≃* ↥(alternatingGroup (Fin 5)) := MulEquiv.subgroupCongr hrangeA
  have eA : oTwoQuot ↥(L619.threePart P) ≃* ↥(alternatingGroup (Fin 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hkerA.symm).trans
      ((QuotientGroup.quotientKerEquivRange ψA).trans hrA)
  have hA60 : Nat.card (oTwoQuot ↥(L619.threePart P)) = 60 := by
    rw [Nat.card_congr eA.toEquiv, h60]
  obtain ⟨e45⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24
    (X := ↥(alternatingGroup (Fin 5))) h60
  have hAL2 : IsL2Quot 2 (oTwoQuot ↥(L619.threePart P)) := ⟨eA.trans e45⟩
  have hlistA : IsRankOneListed (oTwoQuot ↥(L619.threePart P)) :=
    Or.inl ⟨2, by norm_num, hAL2⟩
  have hrankA : IsRankOneSylow (oTwoQuot ↥(L619.threePart P)) := by
    have h1 := hR1 _ 2 le_rfl h6.lie
    obtain ⟨eL⟩ := nonempty_equiv_psl_of_lieModel (by norm_num) h6.lie
    obtain ⟨eA'⟩ := hAL2
    exact h1.of_mulEquiv (eL.trans eA'.symm)
  have hAns : ¬ Group.IsSolvable ↥(L619.threePart P) := by
    intro hs
    have : Group.IsSolvable ↥ψA.range :=
      Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective ψA)
    exact not_isSolvable_alt5_ch6
      (Group.isSolvable_of_surjective (f := hrA.toMonoidHom) hrA.surjective)
  have hBA : borelOf (L619.threePart P) T' ≤ M := by
    have hYN : borelOf (L619.threePart P) T' ⊔ T' ≤
        Subgroup.normalizer (ch6ZS T L V : Set G) :=
      sup_le ((inf_le_left.trans hAI).trans (Subgroup.centralizer_le_normalizer _)) hT'Z
    have hInH : InH T' (borelOf (L619.threePart P) T' ⊔ T') := ⟨le_sup_right, fun h0 => by
      have hZ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hZT.trans le_sup_right) hYN hZ2
      rw [h0, le_bot_iff] at hZ
      exact h6.ZS_ne_bot hZ⟩
    have hYH : borelOf (L619.threePart P) T' ⊔ T' ≤ P ⊔ T' :=
      sup_le ((inf_le_left.trans hAP).trans le_sup_left) le_sup_right
    by_contra hBM
    have hYM : ¬ borelOf (L619.threePart P) T' ⊔ T' ≤ M := fun hle => hBM (le_sup_left.trans hle)
    have hYeq : borelOf (L619.threePart P) T' ⊔ T' = P ⊔ T' := hHs.2.2 _ hInH hYH hYM
    have hYU : borelOf (L619.threePart P) T' ⊔ T' ≤
        Subgroup.normalizer ((T' ⊓ L619.threePart P : Subgroup G) : Set G) := by
      refine sup_le inf_le_right fun t ht => ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hT'A ht⟩
    have hUn : Subgroup.normalizer
        ((((T' ⊓ L619.threePart P).subgroupOf (P ⊔ T')).map ψ : Subgroup (Equiv.Perm (Fin 5))) :
          Set (Equiv.Perm (Fin 5))) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨x, rfl⟩ := hψs g
      have hxY : (x : G) ∈ borelOf (L619.threePart P) T' ⊔ T' := by rw [hYeq]; exact x.2
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : (w : G) ∈ T' ⊓ L619.threePart P := hw
        refine ⟨x * w * x⁻¹, ?_, by simp⟩
        show ((x : G) * w * (x : G)⁻¹) ∈ T' ⊓ L619.threePart P
        exact (Subgroup.mem_normalizer_iff.mp (hYU hxY) w).mp hw'
      · rintro ⟨w, hw, hwu⟩
        have hw' : (w : G) ∈ T' ⊓ L619.threePart P := hw
        refine ⟨x⁻¹ * w * x, ?_, ?_⟩
        · show ((x : G)⁻¹ * w * (x : G)) ∈ T' ⊓ L619.threePart P
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hYU hxY)) w).mp hw'
          simpa using this
        · rw [map_mul, map_mul, map_inv, hwu]
          group
    have hU2 : IsPGroup 2 (((T' ⊓ L619.threePart P).subgroupOf (P ⊔ T')).map ψ) :=
      ((hT'.sylow.1.to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hAH)).symm).map ψ
    have hUbot : ((T' ⊓ L619.threePart P).subgroupOf (P ⊔ T')).map ψ = ⊥ := by
      by_contra hne
      exact normalizer_ne_top_of_two_perm5 hU2 hne hUn
    have hTAO : (T' ⊓ L619.threePart P).subgroupOf (L619.threePart P) ≤
        CFSG.Open.pCore 2 ↥(L619.threePart P) := by
      intro x hx
      have hx' := Subgroup.mem_subgroupOf.mp hx
      have hmem : ψ ⟨x, hAH x.2⟩ ∈ ((T' ⊓ L619.threePart P).subgroupOf (P ⊔ T')).map ψ :=
        ⟨⟨x, hAH x.2⟩, Subgroup.mem_subgroupOf.mpr hx', rfl⟩
      rw [hUbot, Subgroup.mem_bot] at hmem
      have h1 : x ∈ ψA.ker := hmem
      rwa [hkerA] at h1
    apply hsylA.2.2
    rw [← Subgroup.relIndex_mul_index hTAO]
    have : (CFSG.Open.pCore 2 ↥(L619.threePart P)).index = 60 := by
      rw [← hA60]
      exact Subgroup.index_eq_card _
    rw [this]
    exact Dvd.dvd.mul_left (by norm_num) _
  have hR := hyp111R_of_s5 h432 hR1 h6 hT' hZT hT'Z hAI hT'A hsylA hlistA hrankA hBA
    hD'L hcD' hD'Z hDA hD'S hAM
  have hψA_le : ((L619.threePart P).subgroupOf (P ⊔ T')).map ψ ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨x, hx, rfl⟩
    have : ψ x = ψA ⟨x, Subgroup.mem_subgroupOf.mp hx⟩ := rfl
    rw [this, ← hrangeA]
    exact ⟨_, rfl⟩
  have hker' : ∀ a : ↥(P ⊔ T'), (a : G) ∈ L619.threePart P → ψ a = 1 →
      (a : G) ∈ pCoreOf 2 (L619.threePart P) := by
    intro a haA ha1
    have h1 : (⟨a, haA⟩ : ↥(L619.threePart P)) ∈ ψA.ker := ha1
    rw [hkerA] at h1
    exact (F1.mem_pCore_iff_coe _).mp h1
  exact rootFourLift_of_dsA_slices hDSA hG24 h6 hT' hR hAH ψ hψA_le hker' hA60 hAns hnb

theorem res619S5_of_slices (h432 : Stmt4_3_2)
    (hR1 : L2RankOneSylowFact) (hDSA : DSAL2Statement) (hG24 : G24LongRootSplit) : Res619S5 := by
  intro G _ _ T M L V H n y z T' D' h hT' hd hW Ks hdec hK hHs hPN ψ hψs hψk
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have c := hd.cfg
  have hz := hd.z619
  have hY := hd.isY
  have hn : n = 2 := c.n_eq
  subst hn
  have hnb := lin2Excl619_holds G T M L V H 2 y z T' D' h hT' hd hW Ks hdec hK
  have hK0 : Ks 0 = L619.img0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) := by
    rw [← hdec.iSup_eq]
    refine le_antisymm (le_iSup Ks 0) (iSup_le fun j => ?_)
    rw [Subsingleton.elim j 0]
  obtain ⟨eK⟩ := hK
  rw [hK0] at eK
  have hcardK : Nat.card (L619.img0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) = 120 := by
    rw [Nat.card_congr eK.toEquiv, L619.card_perm_five]
  have hPN' := c.conjClosure_E_le_normWZX hY
  have hφs := L619.actOn_surjective hW (ch6ZS T L V) _ hPN'
  have hkerφψ : (L619.actOn hW (ch6ZS T L V) _ hPN'
      (fun x => L619.act0_mem_img0 hW _ _ x.2)).ker =
      (ψ.comp (Subgroup.inclusion le_sup_left)).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, hψk]
    exact Subtype.ext_iff
  have hφ1 : ∀ x : ↥(conjClosure (conjSub y V) (ch619I T L V ⊔ T')),
      x ∈ (ψ.comp (Subgroup.inclusion le_sup_left)).ker ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [← hkerφψ, MonoidHom.mem_ker, Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := Subgroup.inclusion hPN' x) x.2
  have hcyc : ∀ p [Fact p.Prime], p ≠ 2 → ∀ Q : Sylow p ↥(L619.img0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))), IsCyclic Q := fun p hp hp2 Q =>
    CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd
      (by rw [hcardK]; exact L619.not_sq_dvd_of_small (Or.inr (Or.inl rfl)) hp.out hp2) Q
  have hPK2 := c.inf_K2_le_pCoreOf h h432 hz hY hW hcyc
  have hkerP : IsPGroup 2 (ψ.comp (Subgroup.inclusion le_sup_left)).ker := by
    have hle : (ψ.comp (Subgroup.inclusion le_sup_left)).ker ≤
        (pCoreOf 2 (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))).subgroupOf _ :=
      fun x hx => Subgroup.mem_subgroupOf.mpr (hPK2 ⟨x.2, (hφ1 x).mp hx⟩)
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm).to_le hle
  have hψPs : Function.Surjective (ψ.comp (Subgroup.inclusion le_sup_left)) := by
    have e1 := QuotientGroup.quotientKerEquivOfSurjective _ hφs
    have e2 := QuotientGroup.quotientKerEquivRange (ψ.comp (Subgroup.inclusion
      (le_sup_left : conjClosure (conjSub y V) (ch619I T L V ⊔ T') ≤ _ ⊔ T')))
    have hc : Nat.card (ψ.comp (Subgroup.inclusion le_sup_left)).range = 120 := by
      rw [← Nat.card_congr e2.toEquiv, ← hkerφψ, Nat.card_congr e1.toEquiv, hcardK]
    have htop : (ψ.comp (Subgroup.inclusion le_sup_left)).range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hc, L619.card_perm_five])
    exact MonoidHom.range_eq_top.mp htop
  have hO : ∀ x (hx : x ∈ conjClosure (conjSub y V) (ch619I T L V ⊔ T')),
      x ∈ pCoreOf 2 (ch619I T L V) → ψ ⟨x, Subgroup.mem_sup_left hx⟩ = 1 := by
    intro x hx hxO
    have h1 := (hφ1 ⟨x, hx⟩).mpr (Cfg619.pCoreOf_I_le_K2 h h432 z hxO)
    exact h1
  exact res619S5_core_slices h432 hR1 hDSA hG24 h.toHyp611Nat hT' (c.conjClosure_E_le_I hY)
    (hY.I_le.trans (le_normalizer_conjClosure _ _))
    (fun t ht => le_normalizer_conjClosure _ _ (Subgroup.mem_sup_right ht))
    ψ hψPs hkerP hO hHs hd.sylow_S' hd.T'_le hd.rank_I hd.D'_le_L hd.card_D' hd.D'_le_ZS
    hd.D'_le_I hd.D'_le_S' hnb

end Res619Twins

section Lem5DFTwins

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem false_of_s3_ch615_slices (h432 : Stmt4_3_2) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (c : Cx615B G T M L V H n)
    {S P₁ : Subgroup G} (hST : S ≤ T) (hTLS : T ⊓ L ≤ S)
    (hSP : S ≤ Subgroup.normalizer (P₁ : Set G))
    (hBP : borelL T L ≤ Subgroup.normalizer (P₁ : Set G)) (hP₁M : ¬ P₁ ≤ M)
    (hsyl : IsSylowTwoOf (S ⊓ P₁) P₁) (hS3 : Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)))
    (hc1 : CharTwo (L ⊔ S)) (hc2 : CharTwo (P₁ ⊔ S ⊔ borelL T L)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.hyp
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hSL : S ⊓ L = T ⊓ L := le_antisymm (inf_le_inf_right L hST) (le_inf hTLS inf_le_right)
  have hbP : borelOf P₁ S = S ⊓ P₁ := borelOf_eq_of_s3 hsyl hS3
  have hbL : borelOf L S = borelL T L := by
    unfold borelOf borelL
    rw [hSL]
  have hn2 := h.two_le
  have hlist : IsRankOneListed (oTwoQuot ↥L) := Or.inl ⟨n, by omega, c.isL2Quot_ch615⟩
  have hS2 : IsPGroup 2 S := h.sylow.1.to_le hST
  have hyp : Hyp111 L P₁ S := by
    refine ⟨⟨inferInstance, hS2, hST.trans hTL, ?_, hlist, ?_, ?_⟩,
      ⟨inferInstance, hS2, hSP, hsyl, ?_, ?_, ?_⟩, ?_⟩
    · rw [hSL]
      exact c.toCx615.isSylowTwoOf_inf
    · rw [hbP]
      exact inf_le_left.trans (hST.trans hTL)
    · rw [hbP, sup_of_le_left ((inf_le_left : S ⊓ P₁ ≤ S).trans le_sup_right)]
      exact hc1
    · obtain ⟨e⟩ := hS3
      exact isRankOneListed_perm_three e
    · rw [hbL]
      exact hBP
    · rw [hbL]
      exact hc2
    ·
      by_contra hne
      have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ P₁ ⊔ S) : Set G)) :=
        ⟨_, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
      obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
      have hG0 : L ⊔ P₁ ⊔ S ≤ K :=
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hle
      have hKM : K = M := (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
        h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).1 K hK
          (le_sup_left.trans (le_sup_left.trans hG0))
      exact hP₁M (hKM ▸ (le_sup_right.trans (le_sup_left.trans hG0)))
  have hqt : IsQuasithinSub (L ⊔ P₁ ⊔ S) := isQuasithinSub_of_qtke' h.qtke _
  have hnorm : (S.subgroupOf (S ⊔ borelOf L S)).Normal ∨
      (S.subgroupOf (S ⊔ borelOf P₁ S)).Normal := by
    right
    rw [hbP, sup_of_le_left inf_le_left, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hnsolv : ¬ Group.IsSolvable ↥L := fun hs => by
    have h1 := (isSolvable_iff_perfectCore_eq_bot L).mp hs
    rw [perfectCore_eq_self_of_perfect h.toHyp5_0_1.commutator_eq] at h1
    apply h.module.2.2
    rw [h1]
    exact Subgroup.commutator_bot_right V
  obtain ⟨L1', L2', hsw, -, hlist', -⟩ :=
    hDSB G L P₁ S hyp hqt hnorm hnsolv ⟨n, c.isL2Quot_ch615⟩ hS3
  have hcL := c.card_oTwoQuot_ch615
  have hcP := card_oTwoQuot_of_s3 hS3
  have h60 : 60 ≤ 2 ^ n * (4 ^ n - 1) := two_pow_mul_four_pow_sub_one_ge n hn2
  have h504 : 3 ≤ n → 504 ≤ 2 ^ n * (4 ^ n - 1) := fun hn3 => by
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h64 : 4 ^ 3 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    calc 504 = 2 ^ 3 * (4 ^ 3 - 1) := by norm_num
      _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h8 (by omega)
  have hWP : ⁅V, L⁆ ≤ pCoreOf 2 (L ⊔ bigB L P₁ S) :=
    c.commutator_le_pCoreOf_ch615.trans hyp.pCoreOf_le_pCoreOf_vertex
  unfold F112ListB at hlist'
  dsimp only at hlist'
  rcases hlist' with ⟨-, hq1, hsp, -⟩ | ⟨-, hq1, -, -, hq2, -, hA5⟩ | ⟨-, hq1, hQ, -⟩ |
      ⟨-, -, hQ, ⟨e2⟩, -⟩
  ·
    have hq := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · have hn3 : 3 ≤ n := by
        by_contra hlt
        have hn : n = 2 := by omega
        rw [hcL, hn] at hq
        norm_num at hq
      exact c.not_isSpecialPow_of_commutator_le_ch615 hn3 hWP hsp
    · rw [hcP] at hq
      norm_num at hq
  ·
    have hq := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · rw [hcL] at hq
      norm_num at hq
      omega
    · have hq' := hq2.card (by norm_num)
      rw [hcL] at hq'
      have hn : n = 2 := by
        by_contra hne
        have := h504 (by omega)
        norm_num at hq'
        omega
      exact c.false_of_isAltType_ch615 hn hA5
  ·
    have hq := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · exact c.not_isQ8D8_of_commutator_le_ch615 hWP hQ
    · rw [hcP] at hq
      norm_num at hq
  ·
    have h6 := card_oTwoQuot_of_s3 ⟨e2⟩
    rcases hsw with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
    · exact c.not_isQ8D8_of_commutator_le_ch615 hWP hQ
    · rw [hcL] at h6
      omega

end Cx615B

end Lem5DFTwins

section Lem5DKTwins

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_normalizer_oTwoUpper_ch615_slices (h432 : Stmt4_3_2)
    (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (hR1 : L2RankOneSylowFact) (c : Cx615C G T M L V H n)
    (hK : borelL T L ≤ Subgroup.normalizer (oTwoUpper H : Set G)) : False := by
  obtain ⟨-, -, -, -, hcase⟩ := c.coords_ch615
  obtain ⟨S, P₁, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ : ∃ S P₁ : Subgroup G, S ≤ T ∧
      T ⊓ L ≤ S ∧ S ≤ Subgroup.normalizer (P₁ : Set G) ∧
      borelL T L ≤ Subgroup.normalizer (P₁ : Set G) ∧ ¬ P₁ ≤ M ∧ IsSylowTwoOf (S ⊓ P₁) P₁ ∧
      Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)) ∧ CharTwo (L ⊔ S) ∧
      CharTwo (P₁ ⊔ S ⊔ borelL T L) := by
    rcases hcase with ⟨ψ₁, hψ₁, hr₁⟩ | ⟨ψ, hψ, hr, t, htT, ht₁, -⟩
    · exact c.exists_s3_one_ch615 hR1 hK hψ₁ hr₁
    · exact c.exists_s3_two_ch615 hR1 hK hψ hr htT ht₁
  exact c.toCx615B.false_of_s3_ch615_slices h432 hDSB h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem false_of_le_ch615_slices (h432 : Stmt4_3_2) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (hR1 : L2RankOneSylowFact)
    (c : Cx615C G T M L V H n) (hCM : cXU615 T L H ≤ M)
    (hN : borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) : False :=
  c.false_of_normalizer_oTwoUpper_ch615_slices h432 hDSB hR1
    (c.borelL_le_normalizer_oTwoUpper_ch615 h432 hCM hN)

end Cx615C

end Lem5DKTwins

section Lem5DNTwins

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

theorem res615D_of_slices (h432 : Stmt4_3_2) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (hR1 : L2RankOneSylowFact) :
    Res615D := fun _ _ _ _ _ _ _ _ _ c hN =>
  c.false_of_le_ch615_slices h432 hDSB hR1 (c.cXU615_le_ch615 h432 hN) hN

end Lem5DNTwins

section GreenBookTwins

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp611Nat

theorem false_of_s3_parabolic_slices (h432 : Stmt4_3_2) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (h : Hyp611Nat G T M L V 2) {D P₁ : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hP₁ZS : P₁ ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hTP : T ≤ Subgroup.normalizer (P₁ : Set G)) (hDP : D ≤ Subgroup.normalizer (P₁ : Set G))
    (hP₁M : ¬ P₁ ≤ M) (hsyl : IsSylowTwoOf (T ⊓ P₁) P₁)
    (hS3 : Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3))) : False := by
  have hyp := h.hyp111_of_s3_parabolic h432 hD hP₁ZS hTP hDP hP₁M hsyl hS3
  have hqt : IsQuasithinSub (L ⊔ P₁ ⊔ T) := isQuasithinSub_of_qtke' h.qtke _
  have hnorm : (T.subgroupOf (T ⊔ borelOf L T)).Normal ∨
      (T.subgroupOf (T ⊔ borelOf P₁ T)).Normal := by
    right
    rw [borelOf_eq_of_s3 hsyl hS3, sup_of_le_left inf_le_left, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  obtain ⟨L1', L2', hsw, -, hlist, -⟩ :=
    hDSB G L P₁ T hyp hqt hnorm h.not_isSolvable_L ⟨2, h.isL2Quot_L⟩ hS3
  have hcL := h.card_oTwoQuot_L
  have hcP := card_oTwoQuot_of_s3 hS3
  have hVP : V ≤ pCoreOf 2 (L ⊔ bigB L P₁ T) :=
    h.V_le_pCoreOf_L.trans hyp.pCoreOf_le_pCoreOf_vertex
  unfold F112ListB at hlist
  dsimp only at hlist
  rcases hlist with ⟨-, hq1, -⟩ | ⟨-, hq1, -, -, -, -, hA5⟩ | ⟨-, hq1, hQ, -⟩ |
      ⟨-, -, hQ, ⟨e2⟩, -⟩
  ·
    have h504 := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [hcL] at h504
      norm_num at h504
    · rw [hcP] at h504
      norm_num at h504
  ·
    have h6 := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · rw [hcL] at h6
      norm_num at h6
    · exact h.false_of_isAltType hA5
  ·
    have h60 := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · exact h.false_of_isQ8D8_of_le hVP hQ
    · rw [hcP] at h60
      norm_num at h60
  ·
    have h6 := card_oTwoQuot_of_s3 ⟨e2⟩
    rcases hsw with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
    · exact h.false_of_isQ8D8_of_le hVP hQ
    · rw [hcL] at h6
      norm_num at h6

end Hyp611Nat

end GreenBookTwins

section Lem19TwoTwins

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

theorem stmt6_1_19_of_slices (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (h6112 : Stmt6_1_12) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (hP : Parabolic6_1_19) :
    Stmt6_1_19 := by
  intro G _ _ T M L V n h hex
  obtain ⟨H, hH, hHs, hodd⟩ := hex
  have hn : n = 2 := h.n_eq_two_of_odd h331 h432 h615 h6110 h6112 hH hHs hodd
  refine ⟨hn, fun hab => ?_⟩
  obtain ⟨P₁, hP₁Z, hTP, hBP, hP₁M, hsyl, hS3⟩ := hP G T M L V n h ⟨H, hH, hHs, hodd⟩ hab
  obtain ⟨D, hD⟩ := h.toHyp5_0_1.exists_isHall_borel
  subst hn
  exact h.toHyp611Nat.false_of_s3_parabolic_slices h432 hDSB hD hP₁Z hTP (hD.1.trans hBP) hP₁M hsyl
    hS3

end Lem19TwoTwins

end CFSG.Quasithin.H13
