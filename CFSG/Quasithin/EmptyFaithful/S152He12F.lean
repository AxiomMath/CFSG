module

public import CFSG.Quasithin.EmptyFaithful.S152He12E
public import CFSG.Quasithin.EmptyFaithful.S152VM22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33
public import CFSG.Quasithin.EmptyFaithful.S152He12D
public import CFSG.Quasithin.EmptyFaithful.S152L27
public import CFSG.Quasithin.EmptyFaithful.S152VKc

public section

namespace CFSG.Quasithin

namespace He12

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Blueprint
open CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G]

@[expose] def Stage15215TailW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        Lemma15212ConclW T Mc M H B → Lemma15214Concl T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → Lemma15220Concl T Mc M B₀ I → ¬ CharTwo I →
          (∀ L : Subgroup G, IsComponentIn L I → ¬ L ≤ Mc →
            ¬ Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L)) → False

@[expose] def Tail15215CoreW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc I S Mi L L₀ K P : Subgroup G) (z : G),
    Tail15215Cfg I S Mi L L₀ K P z → Mi = Mc ⊓ I → IsXi T K →
      ((conjClosure K Mc = oPrimeResidualOf 3 Mc ∧
        (conjClosure K Mc = K ∨ Case15212ii T Mc (conjClosure K Mc) ∨
          Case15212iii T Mc (conjClosure K Mc) ∨ Case15212He T Mc (conjClosure K Mc))) ∨
        ThreeComplement152 Mc) →
      I ⊓ Subgroup.normalizer (K : Set G) ≤ Mi → False

theorem pCoreOf_le_pCoreOf_of_normalizer {K Mc : Subgroup G} (hKMc : K ≤ Mc)
    (hn : Mc ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 Mc :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKMc)
    (hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem three_dvd_card_M22 :
    3 ∣ Nat.card (NativeSporadic.Carrier .M22) := by
  rw [S152V.card_M22]; norm_num

theorem not_isPGroup_three_M22 :
    ¬ IsPGroup 3 (NativeSporadic.Carrier .M22) := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (NativeSporadic.Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  obtain ⟨n, hn⟩ := h.exists_card_eq
  have h1 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := S152V.card_M22
  rw [h1] at hn
  have h2 : 2 ∣ 3 ^ n := by rw [← hn]; norm_num
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)

theorem tail15215CoreW_of_four (hL2p : Tail15215L2p)
    (hRank : Tail15215Rank) (hJ4 : Tail15215J4) (hKc : Tail15215Kc) : Tail15215CoreW := by
  intro G _ _ T Mc I S Mi L L₀ K P z cfg hMi hxi hdisj hN
  by_cases h2p : ∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel L .PSL 2 p 1
  ·
    have hLc := hL2p G I S Mi L L₀ K P z cfg h2p
    refine cfg.L_not fun x hx => hN ⟨cfg.comp.1 hx, ?_⟩
    exact Subgroup.centralizer_le_normalizer _ (hLc hx)
  · have hJ := hRank G I S Mi L L₀ K P z cfg h2p
    have hsec := hJ4 G I S Mi L L₀ K P z cfg hJ
    have hLzMc : L ⊓ Subgroup.centralizer ({z} : Set G) ≤ Mc := by
      intro x hx
      have hxMi : x ∈ Mi := by
        rw [cfg.hMi]
        exact ⟨cfg.comp.1 hx.1, hx.2⟩
      rw [hMi] at hxMi
      exact hxMi.1
    rcases hdisj with ⟨hO3, hcases⟩ | h3c
    · have hle : oPrimeResidualOf 3 (L ⊓ Subgroup.centralizer ({z} : Set G)) ≤ conjClosure K Mc := by
        rw [hO3]
        exact S152U.oPrimeResidualOf_mono_aux 3 hLzMc
      exact hKc G T Mc K hxi hcases (hsec.mono hle)
    · have := S152V.isSimpleGroup_M22
      exact not_hasSectionIso_of_threeComplement h3c hLzMc three_dvd_card_M22 not_isPGroup_three_M22 hsec

theorem stage15215TailW_of_core (hlist : Lemma115_3_List)
    (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (h15208 : StageLemma15208) (h15209 : StageNotation15209) (h15216 : StageLemma15216)
    (h15218 : StageLemma15218) (core : Tail15215CoreW) : Stage15215TailW := by
  intro G _ _ T Mc M hs H hH B hB B₀ hB₀ c12 c14 I hImin c20 hnot h24
  classical
  have hI := hImin.1
  have c16 := h15216 G T Mc M hs H hH B₀ hB₀ I hI
  have c18 := h15218 G T Mc M hs H hH B₀ hB₀ I hI
  set S := sOf152 T Mc M B₀ with hS
  set Zs := zSOf T Mc M B₀ with hZs
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hSsyl : IsSylowTwoOf S I := c18.sylow
  have hST : S ≤ T := inf_le_left
  have hZcard : 2 ≤ Nat.card (quasithinOmegaOneCenter T) := by
    rcases c14.cases with ⟨-, hZeq, hcard, -⟩ | ⟨-, hZc, -⟩
    · rw [hZeq, hcard]; norm_num
    · rw [hZc]
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨z', hz'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  set z : G := (z' : G) with hzdef
  have hzZ : z ∈ quasithinOmegaOneCenter T := z'.2
  have hz1 : z ≠ 1 := fun h => hz'1 (Subtype.ext h)
  obtain ⟨hzT, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hzZ
  have hZsT : Zs ≤ T := (zSOf_le_V154 T Mc M B₀).trans (S152N.V154_le_T hs)
  have hzS : z ∈ S := ⟨hzT, fun x hx => Subgroup.mem_centralizer_iff.mp hzC x (hZsT hx)⟩
  have hzCS : z ∈ Subgroup.centralizer (S : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hzC x (hST hx)
  have hyp := c20.hyp115 z hzZ hz1
  have hMcz : Mc ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [c14.mc_eq]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ)
  have hMi : Mc ⊓ I = I ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine le_antisymm (fun x hx => ⟨hx.2, hMcz hx.1⟩) (fun x hx => ⟨hyp.centralizer_z_le hx.2, hx.1⟩)
  have hMiI : Mc ⊓ I ≠ I := fun h => hI.not_le (h ▸ inf_le_left)
  have hO2I : pCoreOf 2 I ≠ ⊥ := hI.inH.2
  have hSQ : SQTKGroup ↥I :=
    sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hO2I
  have hSMi : S ≤ Mc ⊓ I := le_inf (hST.trans hTMc) hSsyl.1
  have hmax : ∀ J : Subgroup G, Mc ⊓ I ≤ J → J ≤ I → J = Mc ⊓ I ∨ J = I := by
    intro J hMJ hJI
    by_contra hcon
    push Not at hcon
    have hJMc : ¬ J ≤ Mc := fun h => hcon.1 (le_antisymm (le_inf h hJI) hMJ)
    have hZsC : Subgroup.centralizer (Zs : Set G) ≤ J :=
      (c16.centralizer_eq.le.trans c16.centralizer_le).trans hMJ
    have hO2 : pCoreOf 2 J ≠ ⊥ := by
      intro hbot
      have hle : pCoreOf 2 I ≤ pCoreOf 2 J :=
        le_pCoreOf_of_le_normalizer (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSsyl |>.trans
          (hSMi.trans hMJ)) (hJI.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
      exact hO2I (le_bot_iff.mp (hbot ▸ hle))
    exact hcon.2 (hImin.2 J ⟨hZsC, hO2⟩ hJMc hJI)
  obtain ⟨L, hL, hLMi⟩ : ∃ L : Subgroup G, IsComponentIn L I ∧ ¬ L ≤ Mc ⊓ I := by
    by_contra hcon
    push Not at hcon
    refine hnot (DoubleA3.charTwo_of_no_component (fun K hK => ?_) c20.oddCore)
    exact DoubleA3.not_isComponentIn_of_charTwo c20.charTwo K
      (BenderBranch.isComponentIn_of_le hK (hcon K hK) inf_le_right)
  have hLnot : ¬ L ≤ Mc := fun h => hLMi (le_inf h hL.1)
  have hLie := h24 L hL hLnot
  have hZL : centerOf L = pCoreOf 2 L := S152U.centerOf_eq_pCoreOf_aux c20.oddCore hL
  have := hs.qtfe.simple
  have hqtke : QTKECore G := qtkeCore_of_cat hs.qtfe.nonabelian hs.qtfe.qtke
  obtain ⟨hzN, hcomm, -, hcases⟩ :=
    Lemma115_3_List.component_cases hlist hs.qtfe.simple hs.qtfe.nonabelian hqtke hyp hL
  have hLcomp : L ∈ cComp I := Id2519.mem_cComp_of_isComponentIn hL
  obtain ⟨horb, -⟩ := hA3 G I S L hSQ hSsyl hLcomp
  have hL0I : conjClosure L S ≤ I := conjClosure_le fun s hs l hl =>
    I.mul_mem (I.mul_mem (hSsyl.1 hs) (le_of_mem_cComp hLcomp hl)) (I.inv_mem (hSsyl.1 hs))
  have hL0N : I ≤ Subgroup.normalizer (conjClosure L S : Set G) := by
    have key : ∀ g ∈ I, conjClosure L S ≤ (conjClosure L S).comap (MulAut.conj g).toMonoidHom := by
      intro g hg
      refine conjClosure_le fun s hs l hl => ?_
      have hmem : conjByElt (g * s) L ∈ conjSubgroupsBy I L := ⟨g * s, I.mul_mem hg (hSsyl.1 hs), rfl⟩
      rw [horb] at hmem
      obtain ⟨s', hs', hs'eq⟩ := hmem
      have hx : (g * s) * l * (g * s)⁻¹ ∈ conjByElt (g * s) L := ⟨l, hl, rfl⟩
      rw [hs'eq] at hx
      obtain ⟨l', hl', hl'eq⟩ := hx
      have e : g * (s * l * s⁻¹) * g⁻¹ = s' * l' * s'⁻¹ := by
        have h1 : (MulAut.conj s') l' = (g * s) * l * (g * s)⁻¹ := hl'eq
        simp only [MulAut.conj_apply] at h1
        rw [h1]
        group
      show (MulAut.conj g) (s * l * s⁻¹) ∈ conjClosure L S
      simp only [MulAut.conj_apply]
      rw [e]
      exact mem_conjClosure hs' hl'
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg hx, fun hx => ?_⟩
    have h1 := key g⁻¹ (I.inv_mem hg) hx
    simpa [MulAut.conj_apply, mul_assoc] using h1
  have hL0n : ((conjClosure L S).subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL0I).mpr hL0N
  have hIeq : I = conjClosure L S ⊔ (Mc ⊓ I) := by
    rcases hmax (conjClosure L S ⊔ (Mc ⊓ I)) le_sup_right (sup_le hL0I inf_le_right) with h | h
    · exact absurd ((le_conjClosure L S).trans (le_sup_left.trans h.le) |>.trans inf_le_left) hLnot
    · exact h.symm
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hsylH : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hX : IsXi T (oTwoUpper H) := Der6D.xi_of_iso hsylH hH.1.2 φ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hi : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 :=
    C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hi]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ oTwoUpper H) IsPGroup.of_bot
  have hPc : Nat.card P = 9 := by rw [hX.card_sylow (by norm_num) h3 hP, hi]
  have hKMi : oTwoUpper H ≤ Mc ⊓ I := le_sup_left.trans c16.KS_le
  have hcharH : CharTwo H := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charTwo_of_inH hs.qtfe.qtke.2.1 (hs.qtfe.sylow.1.toSylow hs.qtfe.sylow.2) hH.1
  have hNK : Subgroup.normalizer (oTwoUpper H : Set G) ≤ Mc :=
    normalizer_oTwoUpper_le_of_isUniqueM c12.unique hcharH h3
  have hHMc : H ≤ Mc := (h15209 G T Mc M hs H hH).le_mc
  have hdisj : (conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 Mc ∧
      (conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
        Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
        Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
        Case15212He T Mc (conjClosure (oTwoUpper H) Mc))) ∨ ThreeComplement152 Mc := by
    by_cases hI : conjClosure (oTwoUpper H) Mc = oTwoUpper H
    · right
      have hKMc : oTwoUpper H ≤ Mc := (oTwoUpper_le H).trans hHMc
      have hKn : Mc ≤ Subgroup.normalizer ((oTwoUpper H : Subgroup G) : Set G) := by
        have := le_normalizer_conjClosure (oTwoUpper H) Mc
        rwa [hI] at this
      have hsylMc : IsSylowTwoOf T Mc := isSylowTwoOf_of_quasithinIsSylowTwo hs.qtfe.sylow hTMc
      refine threeComplement152_of_caseI hKMc hKn
        (fun x hx hx3 => mem_of_orderOf_three h15208 h15209 hs hH hI hx hx3)
        (fun x hx hxa z hz => ?_)
      obtain ⟨a, ha⟩ := hxa
      exact pCoreOf_le_pCoreOf_of_normalizer hKMc hKn
        (He8.commutator_mem_of_three hsylH hsylMc hHMc φ hKn hx ha z hz)
    · left
      exact ⟨c12.eq_oThreePrime_of_ne hI, c12.cases⟩
  exact core G T Mc I S (Mc ⊓ I) L (conjClosure L S) (oTwoUpper H) P z
    ⟨hSQ, c20.oddCore, hSsyl, hzS, hzCS, hz2, hz1, hMi, hMiI, hmax, hL, hZL, hLMi, hcomm, hcases,
      hLie, rfl, hL0n, hIeq, hKMi, c12.xi.1, hP.le, hP.isPGroup, hPc,
      fun x hx => hX.pow_eq_one (by norm_num) h3 hP hx⟩
    rfl c12.xi hdisj (fun x hx => ⟨hNK hx.2, hx.1⟩)


end He12

end CFSG.Quasithin
