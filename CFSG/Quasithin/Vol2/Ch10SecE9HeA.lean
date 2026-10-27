module

public import CFSG.Quasithin.Vol2.Ch10SecDClB
public import CFSG.Quasithin.Vol2.Ch10SecB3L32
public import CFSG.Quasithin.Vol2.Ch10SecC9Comp
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Core
public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.Vol2.Ch10SecHeLDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9He

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isSylowTwoOf_of_le (hyp : Hyp10 G T L I) {H : Subgroup G} (hTH : T ≤ H) :
    IsSylowTwoOf T H :=
  ⟨hTH, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow hTH⟩

theorem charTwo_of_le (hyp : Hyp10 G T L I) {H : Subgroup G} (hTH : T ≤ H)
    (hH : pCoreOf 2 H ≠ ⊥) : CharTwo H := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hSH : InH (S : Subgroup G) H := ⟨by rw [hS]; exact hTH, hH⟩
  exact charTwo_of_inH hyp.fsu.qtke.2.1 S hSH

theorem charTwo_of_he (hyp : Hyp10 G T L I) {H J : Subgroup G} (hTH : T ≤ H)
    (hH : pCoreOf 2 H ≠ ⊥) (hJ : J ∈ cComp H) : CharTwo J :=
  A4.charTwo_of_subnormal (subnormal_of_mem_cComp hJ) (charTwo_of_le hyp hTH hH)

theorem pCoreOf_le_of_he (hyp : Hyp10 G T L I) {H J : Subgroup G} (hTH : T ≤ H)
    (hJ : J ∈ cComp H) (hHJ : H ≤ Subgroup.normalizer (J : Set G)) : pCoreOf 2 J ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 J ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans (le_of_mem_cComp hJ))
      (hHJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)
  exact h1.trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hyp hTH))

omit [Finite G] in
theorem pCoreOf_ne_bot_of_charTwo {J : Subgroup G} (hJc : CharTwo J) (hJ : J ≠ ⊥) :
    pCoreOf 2 J ≠ ⊥ := by
  intro h0
  apply hJ
  have h1 := hJc
  unfold CharTwo at h1
  rw [h0] at h1
  rw [eq_bot_iff]
  intro j hj
  have hjc : j ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    rw [hx, one_mul, mul_one]
  exact h1 ⟨hj, hjc⟩

theorem quasithinIsLocal_of_he (hyp : Hyp10 G T L I) {H J : Subgroup G} (hTH : T ≤ H)
    (hH : pCoreOf 2 H ≠ ⊥) (hJ : J ∈ cComp H) (hHJ : H ≤ Subgroup.normalizer (J : Set G)) :
    quasithinIsLocal T J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : J ⊔ T ≤ H := sup_le (le_of_mem_cComp hJ) hTH
  have hO : pCoreOf 2 J ≤ pCoreOf 2 (J ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans le_sup_left)
      ((hJT.trans hHJ).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)
  have hne := pCoreOf_ne_bot_of_charTwo (charTwo_of_he hyp hTH hH hJ) (ne_bot_of_mem_cComp hJ)
  exact SecD.quasithinIsLocal_of_mem_cComp hJ rfl hJT (isSylowTwoOf_of_le hyp le_sup_right)
    fun h => hne (eq_bot_iff.mpr (h ▸ hO))

theorem isMaximalLocal_of_he (h128 : Lemma128Four) (hyp : Hyp10 G T L I) {J : Subgroup G}
    (hloc : quasithinIsLocal T J)
    (he : Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    quasithinIsMaximalLocal T J :=
  h128 G hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian T J hloc
    (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl he)

theorem quasithinV2_eq_bot_of_he (hNoHe : NoHeLStarF) (h128 : Lemma128Four)
    (hyp : Hyp10 G T L I) {H J : Subgroup G} (hTH : T ≤ H) (hH : pCoreOf 2 H ≠ ⊥)
    (hJ : J ∈ cComp H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (he : Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    quasithinV2 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hloc := quasithinIsLocal_of_he hyp hTH hH hJ hHJ
  have hperf := perfect_of_mem_cComp hJ
  exact hNoHe G T J hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
    (isMaximalLocal_of_he h128 hyp hloc he)
    ⟨hloc, fun N hNK hN hpow => C2Nine.eq_of_perfect_of_pow_mem hperf hNK hN hpow,
      (quasithinGenFitting_eq_pCoreOf_iff J 2).mpr (charTwo_of_he hyp hTH hH hJ), hne⟩
    (hTH.trans hHJ) he

theorem commutator_conjClosure_eq_bot_of_he (hNoHe : NoHeLStarF) (h128 : Lemma128Four)
    (hyp : Hyp10 G T L I) {H J : Subgroup G} (hTH : T ≤ H) (hH : pCoreOf 2 H ≠ ⊥)
    (hJ : J ∈ cComp H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (he : Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    ⁅conjClosure (quasithinOmegaOneCenter T) H, J⁆ = ⊥ := by
  by_contra hne
  have hloc := quasithinIsLocal_of_he hyp hTH hH hJ hHJ
  have hHc := charTwo_of_le hyp hTH hH
  have hV := isTwoReducedIn_conjClosure_of_sylowIn hTH hyp.fsu.sylow.1
    (isSylowTwoOf_of_le hyp hTH).2.2 hHc le_rfl
  exact hNoHe G T J hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
    (isMaximalLocal_of_he h128 hyp hloc he)
    (SecD.quasithinIsFaithfulLocal_of_isTwoReducedIn hloc hJ hHc hV hne) (hTH.trans hHJ) he

variable {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}

theorem not_dvd_card_fsuL0 (h : MaxCtx T L I t Ψ c) : ¬ 17 ∣ Nat.card ↥(fsuL0 T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Ψ h.hC.surj).toEquiv,
    Nat.card_prod, card_Γ] at h1
  have hker : IsPGroup 2 ↥Ψ.ker := by
    rintro ⟨y, hy⟩
    have hy' : (y : G) ∈ pCoreOf 2 (fsuL0 T L) := (h.hC.ker y).mp hy
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, hy'⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hker
  rw [h1, hm]
  intro h17
  have hc : Nat.Coprime 17 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
  have := hc.dvd_of_dvd_mul_right h17
  norm_num at this

theorem not_le_fsuM_of_he (h : MaxCtx T L I t Ψ c)
    {J : Subgroup G}
    (he : Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))
    {x : G} (hxJ : x ∈ J) (hxL0 : x ∈ fsuL0 T L) (hx3 : orderOf x = 3) : ¬ J ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJM
  obtain ⟨e⟩ := he
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.isSimpleGroup_He
  set N := J ⊓ fsuL0 T L with hNdef
  have hNJ : N ≤ J := inf_le_left
  have hJN : J ≤ Subgroup.normalizer (N : Set G) := fun j hj =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj, hJM hj⟩
  have hNn : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mpr hJN
  set φ : ↥J →* CFSG.Blueprint.NativeSporadic.Carrier .He :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hN' : ((N.subgroupOf J).map φ).Normal := hNn.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf J).map φ) with hbot | htop
  · have hxN : (⟨x, hxJ⟩ : ↥J) ∈ N.subgroupOf J := Subgroup.mem_subgroupOf.mpr ⟨hxJ, hxL0⟩
    have h1 : φ ⟨x, hxJ⟩ = 1 := by
      have := Subgroup.mem_map_of_mem φ hxN
      rwa [hbot, Subgroup.mem_bot] at this
    have h2 : (⟨x, hxJ⟩ : ↥J) ∈ CFSG.pCore 2 ↥J := by
      rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨⟨x, hxJ⟩, h2⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥J) => ((y : ↥J) : G)) hk
      simpa using this
    have h5 := orderOf_dvd_of_pow_eq_one hk'
    rw [hx3] at h5
    have h6 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h5
    norm_num at h6
  · have h1 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) ∣ Nat.card ↥N := by
      have h2 := Subgroup.card_map_dvd (H := N.subgroupOf J) φ
      rw [htop, Subgroup.card_top, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNJ).toEquiv] at h2
      exact h2
    have h2 : Nat.card ↥N ∣ Nat.card ↥(fsuL0 T L) := Subgroup.card_dvd_of_le inf_le_right
    have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200 :=
      CFSG.Sporadic.He.card_He
    have h3 : 17 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) := by
      rw [hcard]; norm_num
    exact not_dvd_card_fsuL0 h (h3.trans (h1.trans h2))

theorem fsuCVM_eq_bot_of_he (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H J : Subgroup G}
    (hJM : ¬ J ≤ fsuM T L) (hZJ : ⁅conjClosure (quasithinOmegaOneCenter T) H, J⁆ = ⊥) :
    fsuCVM T L I = ⊥ := by
  by_contra hne
  have hCT : fsuCVM T L I ≤ T := inf_le_left.trans (SecA.fsuVM_le_T hyp)
  have hTn : T ≤ Subgroup.normalizer (fsuCVM T L I : Set G) :=
    (SecA.le_fsuM T L).trans (SecA.le_normalizer_fsuCVM T L I)
  obtain ⟨u, huC, hu1, huT⟩ := SecA.exists_ne_one_mem_centralizer hyp.fsu.sylow.1 hCT hTn hne
  have hu2 : u ^ 2 = 1 := (SecA.isElemAbelian_fsuVM hyp).2 u huC.1
  have huZ : u ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hCT huC, huT⟩, hu2⟩
  have huH : u ∈ conjClosure (quasithinOmegaOneCenter T) H := le_conjClosure _ _ huZ
  have hJu : J ≤ Subgroup.centralizer ({u} : Set G) := by
    intro j hj
    have h1 : ⁅u, j⁆ ∈ ⁅conjClosure (quasithinOmegaOneCenter T) H, J⁆ :=
      Subgroup.commutator_mem_commutator huH hj
    rw [hZJ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
  have hL0T : fsuL0 T L ⊔ T ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun s hs => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp huC.2 l hl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp huT s hs)
  exact hJM (hJu.trans (le_fsuM_of_le h331 hyp hL0T (SecC.pCoreOf_centralizer_ne_bot hu1 hu2)))

end CFSG.Quasithin.Vol2.Ch10.SecB.E9He
