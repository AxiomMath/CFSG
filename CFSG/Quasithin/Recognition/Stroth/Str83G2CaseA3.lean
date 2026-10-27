module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseA2
public import CFSG.Quasithin.Recognition.Stroth.Str83G2Higman
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.Ree CFSG.SolvableHall CFSG.LieType.BorelTits
open CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem isNaturalModule_of_relIndex_eq {H U L N : Subgroup G} {m : ℕ}
    (hm2 : 2 ≤ m) (hmodd : Odd m) (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    {t : G} (htH : t ∈ H) (ht2 : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H)
    (hd : (centralizerMod L N (Subgroup.zpowers t)).relIndex N = 2 ^ m) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    CFSG.QuasithinUnique.Setup.SL2Modules.IsNaturalModule
      (l2ChiefSectionRep hstep hUH hE e) := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstep hUH hE e
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  let a' : SL(2, GaloisField 2 m) := e (QuotientGroup.mk ⟨t, htH⟩)
  have hsqfix : Nat.card (CFSG.RankThree.FFModules.fixSub ρ
      (Subgroup.zpowers a')) ^ 2 = Nat.card (Additive (Ch3z.chiefMod L N)) :=
    l2ChiefSectionRep_sq_card_fixSub hm2 hstep hUH hE e hnc htH ht2 htO
  have hfixcard : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) =
      Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers a')) := by
    rw [show ρ = (CFSG.RankThree.FFModules.autRep (Ch3z.chiefMod L N)).comp
      (l2ChiefSectionSL2Action hstep hUH hE e) from rfl]
    rw [CFSG.RankThree.FFModules.card_fixSub_autRep_comp
      (E := Ch3z.chiefMod L N) (ι := l2ChiefSectionSL2Action hstep hUH hE e)
      (B := Subgroup.zpowers a')]
    congr 1
    rw [MonoidHom.map_zpowers]
    congr 1
    rw [l2ChiefSectionSL2Action_apply, MulEquiv.symm_apply_apply, l2ChiefSectionQuotAction_mk]
  let K : Subgroup (SectionW N L) :=
    (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).comap
      (Ch3z.chiefQuotEquiv hNL).toMonoidHom
  have hKmem : ∀ u : ↥N, QuotientGroup.mk u ∈ K ↔
      l2SectionAction hstep hUH ⟨t, htH⟩ (QuotientGroup.mk u) = QuotientGroup.mk u := by
    intro u
    constructor
    · intro hu
      have hu' : l2ChiefSectionAction hstep hE ⟨t, htH⟩
          (Ch3z.chiefQuotEquiv hNL (QuotientGroup.mk u)) =
          Ch3z.chiefQuotEquiv hNL (QuotientGroup.mk u) :=
        mem_fixV_zpowers_iff_apply.mp hu
      apply (Ch3z.chiefQuotEquiv hNL).injective
      rw [chiefQuotEquiv_l2SectionAction (hE := hE), hu']
    · intro hu
      have h2 := congrArg (Ch3z.chiefQuotEquiv hNL) hu
      rw [chiefQuotEquiv_l2SectionAction (hE := hE)] at h2
      exact mem_fixV_zpowers_iff_apply.mpr h2
  have hact : ∀ u : ↥N, l2SectionAction hstep hUH ⟨t, htH⟩ (QuotientGroup.mk u) =
      QuotientGroup.mk (conjAct N ⟨t, hHN htH⟩ u) :=
    fun u => l2SectionAction_mk hstep hUH ⟨t, htH⟩ u
  have hidx := relIndex_centralizerMod_eq_index_of_fixedSection hHN hHL htH hNL
    (l2SectionAction hstep hUH ⟨t, htH⟩) K hKmem hact
  have hKindex : K.index =
      (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index :=
    Subgroup.index_comap_of_surjective _ (Ch3z.chiefQuotEquiv hNL).surjective
  have hcardfix : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
      (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
      Nat.card (Ch3z.chiefMod L N) :=
    Subgroup.card_mul_index _
  have hW : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) ^ 2 =
      Nat.card (Ch3z.chiefMod L N) := by
    rw [hfixcard]
    exact hsqfix.trans (Nat.card_congr Additive.ofMul).symm
  have hfixpos : 0 <
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    by_contra h0
    have h0' : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) = 0 :=
      Nat.eq_zero_of_not_pos h0
    rw [h0', zero_pow (by norm_num)] at hW
    exact (Nat.card_pos (α := Ch3z.chiefMod L N)).ne' hW.symm
  have hidxfix : (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    have h2 : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
        (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
        Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
        Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
      rw [hcardfix, ← hW, pow_two]
    exact Nat.eq_of_mul_eq_mul_left hfixpos h2
  have hd_eq : (centralizerMod L N (Subgroup.zpowers t)).relIndex N =
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    rw [hidx, hKindex, hidxfix]
  have hWcard : Nat.card (Additive (Ch3z.chiefMod L N)) = (2 ^ m) ^ 2 := by
    calc Nat.card (Additive (Ch3z.chiefMod L N))
        = Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers a')) ^ 2 :=
          hsqfix.symm
      _ = Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) ^ 2 := by
          rw [← hfixcard]
      _ = (centralizerMod L N (Subgroup.zpowers t)).relIndex N ^ 2 := by rw [← hd_eq]
      _ = (2 ^ m) ^ 2 := by rw [hd]
  have hlt : Nat.card (Additive (Ch3z.chiefMod L N)) < 2 ^ (4 * m) := by
    rw [hWcard, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstep hUH hE e hnc
  haveI : Fact ρ.IsIrreducible := ⟨l2ChiefSectionRep_irreducible hstep hUH hE e⟩
  have hm : 1 ≤ m := by omega
  have hcardGF : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 m (by omega)
  have hA2 : ∀ x ∈ CFSG.CGT.Timmesfeld75.utri (GaloisField 2 m), x * x = 1 := by
    intro x hx
    obtain ⟨s, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_utri_iff.mp hx
    exact CFSG.CGT.Timmesfeld75.utriElt_mul_self s
  have hAcard : Nat.card (CFSG.CGT.Timmesfeld75.utri (GaloisField 2 m)) = 2 ^ m := by
    rw [CFSG.CGT.Timmesfeld75.card_utri, Nat.card_eq_fintype_card, hcardGF]
  rcases isNaturalModule_or_isOrthModule_or_of_card_lt hm hcardGF ρ hnt
    (CFSG.CGT.Timmesfeld75.utri (GaloisField 2 m)) hA2 hAcard hlt with
    hnat | horth | hthird
  · exact hnat
  · obtain ⟨l, -, hm2l, -⟩ := horth
    obtain ⟨k, hk⟩ := hmodd
    omega
  · obtain ⟨l, hm3l, hW8, -⟩ := hthird
    have hWq : Nat.card (Additive (Ch3z.chiefMod L N)) = 2 ^ (2 * m) := by
      rw [hWcard, ← pow_mul, mul_comm m 2]
    rw [hWq] at hW8
    have hEq : 2 * m = 8 * l := Nat.pow_right_injective (by norm_num) hW8
    omega


private theorem caseA_Q2_normal_u3H'
    (F : Str83CaseAFrame L1 L2 S a) :
    u3H L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
  rw [u3H, ← F.hsup2]
  exact str86_l2sup_le_normalizer_q2 (L1 := L1) (L2 := L2) (S := S)

private theorem caseA_R_lt_Q2
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    str83CaseAR L1 L2 S < Q2 L1 L2 S := by
  refine lt_of_le_of_ne inf_le_right ?_
  intro h
  have h1 : (str83CaseAR L1 L2 S).relIndex (Q2 L1 L2 S) = 1 := by
    rw [h]
    exact Subgroup.relIndex_eq_one.mpr le_rfl
  rw [str83_caseA_R_relIndex_Q2 F D] at h1
  have hq1 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
  have hq2 : 1 < (2 ^ (2 * a + 1)) ^ 2 := one_lt_pow₀ hq1 (by norm_num)
  omega

private theorem caseA_relIndex_centralizer_le'
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {t : G}
    (htV : t ∈ Z1 L1 L2 S) :
    (Subgroup.centralizer (Subgroup.zpowers t)).relIndex (Q2 L1 L2 S) ≤
      (2 ^ (2 * a + 1)) ^ 2 := by
  have hRleC : str83CaseAR L1 L2 S ≤
      Q2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    have hx' : x ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
      rwa [str83CaseAR] at hx
    refine ⟨hx'.2, ?_⟩
    change x ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (Subgroup.mem_centralizer_iff.mp (F.hQ1centV hx'.1)) t htV
  have hEq : (Subgroup.centralizer (Subgroup.zpowers t)).relIndex (Q2 L1 L2 S) =
      (Q2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Q2 L1 L2 S) := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (Subgroup.zpowers t))
      (Q2 L1 L2 S)]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, inf_comm]
  rw [hEq]
  exact (Subgroup.relIndex_le_of_le_left hRleC (D15Proof.relIndex_ne_zero _ _)).trans
    (le_of_eq (str83_caseA_R_relIndex_Q2 F D))

private theorem caseA_between_eq_of_zero
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    ∀ {N : Subgroup G} {n : ℕ},
      F112W.IsChiefSeriesBetween (u3H L1 L2 S) (Q2 L1 L2 S)
        (str83CaseAR0 L1 L2 S D.w) N n →
      n = 0 → N = str83CaseAR0 L1 L2 S D.w := by
  intro N n h
  induction h with
  | refl => intro _; rfl
  | central hstep hcent hs ih =>
      intro _
      exact (str83_caseA_chiefStep_noncentral F D hstep hs.le hcent).elim
  | noncentral hstep hnc hs ih =>
      intro hn
      omega

private theorem caseA_exists_one_step
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    ∀ {N : Subgroup G},
      F112W.IsChiefSeriesBetween (u3H L1 L2 S) (Q2 L1 L2 S)
        (str83CaseAR0 L1 L2 S D.w) N 1 →
      IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w) N ∧
        ¬ IsCentralStep (u3H L1 L2 S) (str83CaseAR0 L1 L2 S D.w) N := by
  intro N hser
  cases hser with
  | central hstep hcent hs =>
      exact (str83_caseA_chiefStep_noncentral F D hstep hs.le hcent).elim
  | noncentral hstep hnc hs =>
      have hL : _ = _ := caseA_between_eq_of_zero F D hs rfl
      subst hL
      exact ⟨hstep, hnc⟩

private theorem caseA_exists_two_steps
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    ∀ {N : Subgroup G},
      F112W.IsChiefSeriesBetween (u3H L1 L2 S) (Q2 L1 L2 S)
        (str83CaseAR0 L1 L2 S D.w) N 2 →
      ∃ L : Subgroup G,
        IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w) L ∧
        ¬ IsCentralStep (u3H L1 L2 S) (str83CaseAR0 L1 L2 S D.w) L ∧
        IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) L N ∧
        ¬ IsCentralStep (u3H L1 L2 S) L N := by
  intro N hser
  cases hser with
  | central hstep hcent hs =>
      exact (str83_caseA_chiefStep_noncentral F D hstep hs.le hcent).elim
  | noncentral hstep2 hnc2 hs1 =>
      obtain ⟨hstep1, hnc1⟩ := caseA_exists_one_step F D hs1
      exact ⟨_, hstep1, hnc1, hstep2, hnc2⟩

private theorem caseA_suzukiU_not_isMulCommutative
    {K : Type} [Field K] [Finite K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ IsMulCommutative (suzukiU a K) := by
  intro hcomm
  have hbot : commutator ↥(suzukiU a K) = ⊥ :=
    (commutator_eq_bot_iff (↥(suzukiU a K))).mpr hcomm
  have hz0 : suzukiSElt a K 0 (1 : K) ∈ suzukiZ0 a K :=
    (mem_suzukiZ0_iff hK).mpr ⟨1, rfl⟩
  have hU : suzukiSElt a K 0 (1 : K) ∈ suzukiU a K :=
    suzukiZ0_le_suzukiU hz0
  have hmem : (⟨suzukiSElt a K 0 (1 : K), hU⟩ : suzukiU a K) ∈
      (suzukiZ0 a K).subgroupOf (suzukiU a K) :=
    Subgroup.mem_subgroupOf.mpr hz0
  rw [← commutator_suzukiU hK ha, hbot] at hmem
  have h1 : (⟨suzukiSElt a K 0 (1 : K), hU⟩ : suzukiU a K) = 1 :=
    Subgroup.mem_bot.mp hmem
  have hcoe : suzukiSElt a K 0 (1 : K) = suzukiSElt a K 0 (0 : K) := by
    simpa [suzukiSElt_zero_zero hK] using congrArg Subtype.val h1
  exact one_ne_zero ((suzukiSElt_inj.mp hcoe).2)

private theorem caseA_szSbar_equiv_quotient
    [(Q1 L1 L2 S).subgroupOf S |>.Normal]
    (F : Str83CaseAFrame L1 L2 S a) :
    Nonempty (szSbar L1 L2 S ≃* (↥S ⧸ (Q1 L1 L2 S).subgroupOf S)) := by
  classical
  let H1 : Subgroup G := L1 ⊔ S
  have hS1 : H1 = L1 ⊔ Q1 L1 L2 S := F.hsup1
  have hpCore : pCoreOf 2 H1 = Q1 L1 L2 S := by
    rw [hS1]
    exact pCoreOf_sup_pCoreOf F.hF.1
  let φ : ↥S →* szSbar L1 L2 S :=
    { toFun := fun s =>
        ⟨QuotientGroup.mk (Subgroup.inclusion (le_sup_right : S ≤ H1) s),
          Subgroup.mem_map_of_mem _
            (Subgroup.mem_subgroupOf.mpr s.2)⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (QuotientGroup.mk' (pCore 2 ↥H1))
      map_mul' := by
        intro x y
        apply Subtype.ext
        simpa [Subgroup.inclusion] using
          (QuotientGroup.mk_mul (pCore 2 ↥H1)
            (Subgroup.inclusion (le_sup_right : S ≤ H1) x)
            (Subgroup.inclusion (le_sup_right : S ≤ H1) y)) }
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    have hSP1 : S ≤ P1 L1 L2 S :=
      (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
    exact hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hker : φ.ker = (Q1 L1 L2 S).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hval : (φ s : oTwoQuot ↥H1) = 1 := congrArg Subtype.val h
      have h' : (Subgroup.inclusion (le_sup_right : S ≤ H1) s) ∈ pCore 2 ↥H1 :=
        (QuotientGroup.eq_one_iff _).mp hval
      rw [← CFSG.openPCoreOf_subgroupOf 2 H1] at h'
      have h'' : (s : G) ∈ pCoreOf 2 H1 := Subgroup.mem_subgroupOf.mp h'
      rwa [hpCore] at h''
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr (by
        rw [← CFSG.openPCoreOf_subgroupOf 2 H1, hpCore]
        exact Subgroup.mem_subgroupOf.mpr h)
  haveI : (Q1 L1 L2 S).subgroupOf S |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hSNQ1
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

private theorem caseA_Q2R_equiv_SQ1
    [(Q1 L1 L2 S).subgroupOf S |>.Normal]
    [(str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal]
    (F : Str83CaseAFrame L1 L2 S a) :
    Nonempty ((↥(Q2 L1 L2 S) ⧸ (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S)) ≃*
      (↥S ⧸ (Q1 L1 L2 S).subgroupOf S)) := by
  classical
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ2NQ1 : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    F.hQ2S.trans hSNQ1
  have hsubEq : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S) =
      (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, str83CaseAR, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  haveI : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2NQ1
  have hQ2NR : Q2 L1 L2 S ≤ Subgroup.normalizer (str83CaseAR L1 L2 S : Set G) :=
    Subgroup.le_normalizer_inf hQ2NQ1 (Subgroup.le_normalizer (H := Q2 L1 L2 S))
  haveI : (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2NR
  have hQ2Q1NQ1 : Q2 L1 L2 S ⊔ Q1 L1 L2 S ≤
      Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    rw [sup_comm, F.hT2]
    exact hSNQ1
  haveI : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2Q1NQ1
  let eY : ↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S) ≃* ↥S :=
    MulEquiv.subgroupCongr (by rw [sup_comm, F.hT2])
  let e3 : (↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S) ⧸
        (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S)) ≃*
      (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) :=
    QuotientGroup.congr ((Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S))
      ((Q1 L1 L2 S).subgroupOf S) eY (by
        ext y
        constructor
        · rintro ⟨x, hx, hxy⟩
          have hxy' : (x : G) = (y : G) := congrArg Subtype.val hxy
          show (y : G) ∈ Q1 L1 L2 S
          rw [← hxy']
          exact Subgroup.mem_subgroupOf.mp hx
        · intro hy
          refine ⟨eY.symm y, ?_, eY.apply_symm_apply y⟩
          have hcoe : ((eY.symm y : ↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S)) : G) = (y : G) := rfl
          show (eY.symm y : G) ∈ Q1 L1 L2 S
          rw [hcoe]
          exact Subgroup.mem_subgroupOf.mp hy)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hsubEq.symm).trans
    ((QuotientGroup.quotientInfEquivProdNormalizerQuotient (Q2 L1 L2 S) (Q1 L1 L2 S)
      hQ2NQ1).trans e3)⟩

private theorem caseA_false_of_commutator_le_R
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F)
    (hcomm : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ str83CaseAR L1 L2 S) : False := by
  classical
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ2NQ1 : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    F.hQ2S.trans hSNQ1
  have hQ2NR : Q2 L1 L2 S ≤ Subgroup.normalizer (str83CaseAR L1 L2 S : Set G) :=
    Subgroup.le_normalizer_inf hQ2NQ1 (Subgroup.le_normalizer (H := Q2 L1 L2 S))
  haveI : (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2NR
  haveI : (Q1 L1 L2 S).subgroupOf S |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hSNQ1
  have hQcomm : IsMulCommutative
      (↥(Q2 L1 L2 S) ⧸ (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S)) := by
    refine (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S))).mpr ?_
    rw [commutator_def, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf]
    exact hcomm (Subgroup.commutator_mem_commutator x.2 y.2)
  obtain ⟨eQR⟩ := caseA_Q2R_equiv_SQ1 F
  have hScomm : IsMulCommutative (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eQR hQcomm
  obtain ⟨eS⟩ := caseA_szSbar_equiv_quotient F
  have hszcomm : IsMulCommutative (szSbar L1 L2 S) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eS.symm hScomm
  obtain ⟨X0, e, -, -, -, hSmap, -⟩ := exists_equiv_z1_sylow
    (K := GaloisField 2 (2 * a + 1)) (GaloisField.card 2 (2 * a + 1) (by omega))
    F.hF F.hB F.ha F.hSz F.hL2 F.hII F.hJ
  let eSU : szSbar L1 L2 S ≃* suzukiU a (GaloisField 2 (2 * a + 1)) :=
    (e.subgroupMap (szSbar L1 L2 S)).trans (MulEquiv.subgroupCongr hSmap)
  have hUcomm : IsMulCommutative (suzukiU a (GaloisField 2 (2 * a + 1))) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eSU hszcomm
  exact caseA_suzukiU_not_isMulCommutative F.ha
    (GaloisField.card 2 (2 * a + 1) (by omega)) hUcomm

private theorem caseA_single_factor_false
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F)
    (hstep : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w)
      (Q2 L1 L2 S)) : False := by
  classical
  have hQH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hR0Q : str83CaseAR0 L1 L2 S D.w ≤ Q2 L1 L2 S := inf_le_left.trans inf_le_right
  have hQ2p : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hR0ne : str83CaseAR0 L1 L2 S D.w ≠ Q2 L1 L2 S := by
    intro h
    have hlt : str83CaseAR L1 L2 S < Q2 L1 L2 S := caseA_R_lt_Q2 F D
    exact (not_le_of_gt hlt) ((le_of_eq h.symm).trans inf_le_left)
  have hch : ∀ J : Subgroup G, u3H L1 L2 S ≤ Subgroup.normalizer (J : Set G) →
      str83CaseAR0 L1 L2 S D.w ≤ J → J ≤ Q2 L1 L2 S →
      J = str83CaseAR0 L1 L2 S D.w ∨ J = Q2 L1 L2 S := by
    intro J hJ hR0J hJQ
    exact hstep.2.2.2 J ⟨hJQ, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hJ hg) x).mp hx⟩ hR0J hJQ
  have hcomm : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ str83CaseAR0 L1 L2 S D.w :=
    CFSG.Quasithin.MS93.S52i.commutator_le_of_chief hQH (str83_caseA_R0_normal F D)
      (caseA_Q2_normal_u3H' F) hR0Q hR0ne hQ2p hch
  exact caseA_false_of_commutator_le_R F D (hcomm.trans inf_le_left)

private theorem caseA_two_factor_false
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {L : Subgroup G}
    (hstepL : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w) L)
    (hncL : ¬ IsCentralStep (u3H L1 L2 S) (str83CaseAR0 L1 L2 S D.w) L)
    (hstepQ : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) L (Q2 L1 L2 S))
    (hncQ : ¬ IsCentralStep (u3H L1 L2 S) L (Q2 L1 L2 S)) : False := by
  classical
  have ha := F.ha
  have hQH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hQ2p : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hL2H : IsL2Quot (2 * a + 1) (oTwoQuot ↥(u3H L1 L2 S)) :=
    str86_isL2Quot_u3H F.hF F.hL2
  obtain ⟨t, htV, htQ2⟩ := Set.not_subset.mp F.hA
  have htS : t ∈ S := F.hVS htV
  have hSleH : S ≤ u3H L1 L2 S := by
    rw [u3H, ← F.hsup2]
    exact le_sup_right
  have htH : t ∈ u3H L1 L2 S := hSleH htS
  have ht2 : t * t ∈ pCoreOf 2 (u3H L1 L2 S) := by
    rw [str86_pCoreOf_u3H F.hF,
      show t * t = 1 from by rw [← pow_two]; exact F.hVea.2 t htV]
    exact (Q2 L1 L2 S).one_mem
  have htO : t ∉ pCoreOf 2 (u3H L1 L2 S) := by
    rw [str86_pCoreOf_u3H F.hF]
    exact htQ2
  obtain ⟨cQ, hserQ⟩ := D15Proof.exists_isChiefSeriesFrom
    (H := u3H L1 L2 S) (U := Q2 L1 L2 S) (Q2 L1 L2 S)
    (F112W.isNormalIn_of_le_normalizer le_rfl (caseA_Q2_normal_u3H' F))
  have hM6 := l2_pow_sq_le_relIndex_centralizer (H := u3H L1 L2 S) (U := Q2 L1 L2 S)
    (m := 2 * a + 1) (c := cQ) (by omega) hL2H hQ2p hQH hserQ htH ht2 htO
  have hbound := caseA_relIndex_centralizer_le' F D htV
  have hcQ_le : cQ ≤ 2 := (Nat.pow_le_pow_iff_right (Nat.one_lt_two_pow (by omega))).mp
    (hM6.trans hbound)
  have hR0Q : str83CaseAR0 L1 L2 S D.w ≤ Q2 L1 L2 S := inf_le_left.trans inf_le_right
  obtain ⟨c0, hser0⟩ := D15Proof.exists_isChiefSeriesFrom
    (H := u3H L1 L2 S) (U := Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w)
    (F112W.isNormalIn_of_le_normalizer hR0Q (str83_caseA_R0_normal F D))
  have hserFull : IsChiefSeriesFrom (u3H L1 L2 S) (Q2 L1 L2 S) (Q2 L1 L2 S) (c0 + 1 + 1) :=
    IsChiefSeriesFrom.noncentral hstepQ hncQ
      (IsChiefSeriesFrom.noncentral hstepL hncL hser0)
  have hcQeq : cQ = c0 + 1 + 1 := F112W.isChiefSeriesFrom_unique hQH hserQ hserFull
  have hcQ2 : cQ = 2 := by omega
  have hk := fun L' N' (hstep' : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) L' N')
      (hnc' : ¬ IsCentralStep (u3H L1 L2 S) L' N') =>
    l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := 2 * a + 1) (by omega)
      hL2H hQ2p hQH hstep' hnc' htH ht2 htO
  have hrel : ∀ {L' N' : Subgroup G},
      IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) L' N' →
      ¬ IsCentralStep (u3H L1 L2 S) L' N' →
      (centralizerMod L' N' (Subgroup.zpowers t)).relIndex N' = 2 ^ (2 * a + 1) := by
    intro L' N' hstep' hnc'
    refine le_antisymm ?_ (hk L' N' hstep' hnc')
    have hb := Ch3y.step_bound (H := u3H L1 L2 S) (U := Q2 L1 L2 S)
      (A := Subgroup.zpowers t) hQH (Subgroup.zpowers_le.mpr htH)
      (k := 2 ^ (2 * a + 1)) hk hstep' hnc' hserQ
    rw [hcQ2] at hb
    rw [pow_one] at hb
    have hqd : (centralizerMod L' N' (Subgroup.zpowers t)).relIndex N' *
        2 ^ (2 * a + 1) ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
      rw [mul_comm]
      simpa [pow_two] using hb.trans hbound
    exact Nat.le_of_mul_le_mul_right hqd (by positivity)
  have hrelL := hrel hstepL hncL
  have hrelQ := hrel hstepQ hncQ
  let hE_L := isElemAbelian_chiefMod hstepL hQH hQ2p
  let hE_Q := isElemAbelian_chiefMod hstepQ hQH hQ2p
  have hL2H' := hL2H
  obtain ⟨e₀⟩ := hL2H
  let eSL : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 (2 * a + 1)) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 (2 * a + 1)))
  have hnatL := (isNaturalModule_of_relIndex_eq (m := 2 * a + 1) (by omega) ⟨a, rfl⟩
    hL2H' hQ2p hQH hstepL hncL hE_L eSL htH ht2 htO hrelL)
  have hnatQ := (isNaturalModule_of_relIndex_eq (m := 2 * a + 1) (by omega) ⟨a, rfl⟩
    hL2H' hQ2p hQH hstepQ hncQ hE_Q eSL htH ht2 htO hrelQ)
  have hHig := commutator_le_of_two_natural_chiefSteps (H := u3H L1 L2 S)
    (U := Q2 L1 L2 S) (R := str83CaseAR0 L1 L2 S D.w) (N := L) hQH
    (caseA_Q2_normal_u3H' F) hQ2p hstepL hstepQ (by omega) eSL hE_L hE_Q hnatL hnatQ
  exact caseA_false_of_commutator_le_R F D (hHig.trans inf_le_left)

theorem str83_caseA_false
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) : False := by
  classical
  have hQH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hQ2normal : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) (Q2 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (caseA_Q2_normal_u3H' F)
  have hR0Q : str83CaseAR0 L1 L2 S D.w ≤ Q2 L1 L2 S := inf_le_left.trans inf_le_right
  have hR0normal : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w) :=
    F112W.isNormalIn_of_le_normalizer hR0Q (str83_caseA_R0_normal F D)
  have hR0ltQ : str83CaseAR0 L1 L2 S D.w < Q2 L1 L2 S :=
    lt_of_le_of_lt inf_le_left (caseA_R_lt_Q2 F D)
  obtain ⟨c, hser⟩ := F112W.exists_isChiefSeriesBetween (H := u3H L1 L2 S)
    (U := Q2 L1 L2 S) hR0normal (Q2 L1 L2 S) hQ2normal hR0Q
  have hc_le : c ≤ 2 := str83_caseA_chiefSeries_count_le_two F D hser
  have hc_ne : c ≠ 0 := by
    intro hc0
    exact (ne_of_lt hR0ltQ) (caseA_between_eq_of_zero F D hser hc0).symm
  rcases (by omega : c = 1 ∨ c = 2) with hc1 | hc2
  · obtain ⟨hstep, -⟩ := caseA_exists_one_step F D (hc1 ▸ hser)
    exact caseA_single_factor_false F D hstep
  · obtain ⟨L, hstepL, hncL, hstepQ, hncQ⟩ := caseA_exists_two_steps F D (hc2 ▸ hser)
    exact caseA_two_factor_false F D hstepL hncL hstepQ hncQ

theorem str83_partTwo_caseA_false
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    (hA : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S) : False := by
  let F : Str83CaseAFrame L1 L2 S a :=
    str83CaseAFrame_of_hyp hF hB ha hSz hL2 hII hZ2 hJ hA
  obtain ⟨D⟩ := str83CaseAData_of_frame F
  exact str83_caseA_false F D

end CFSG.Quasithin.Stroth

end
