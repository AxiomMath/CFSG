module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc.Generation
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc.Ambient
public import CFSG.Quasithin.EmptyFaithful.S153Q1b
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Sp
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.H13.NQBlockLargeRee
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Ree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Proving
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328 (Pos)

theorem card_of_k328X {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hXZ : Nat.card (Subgroup.center X) = 3)
    (hXt : LieModel (X ⧸ Subgroup.center X) .PSL 3 2 2 ∨
      LieModel (X ⧸ Subgroup.center X) .PSU 3 2 3) :
    (LieModel (X ⧸ Subgroup.center X) .PSL 3 2 2 ∧ Nat.card X = 60480) ∨
      (LieModel (X ⧸ Subgroup.center X) .PSU 3 2 3 ∧ Nat.card X = 16547328) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hXZ]
  rcases hXt with h | h
  · refine Or.inl ⟨h, ?_⟩
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num)
      (h.statedClassicalModel (by decide))]
    decide
  · refine Or.inr ⟨h, ?_⟩
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (h.statedClassicalModel (by decide))]

@[expose] def AmbLeaves (K : Type) [Group K] [Finite K] : Prop :=
  (∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E = 9 →
    (⨆ (F : Subgroup K) (_ : F ≤ E) (_ : Nat.card F = 3),
      Subgroup.centralizer (F : Set K)) = ⊤) ∧
  ∀ Z X : Subgroup K, Pos K Z X → ∀ Q : Sylow 3 X, ¬ 9 * Nat.card Q ∣ Nat.card K

theorem rankThreeGamma_eq_top_of_ambLeaves {G : Type} [Group G] [Finite G] (K : Subgroup G)
    [K.Normal] (hK : AmbLeaves K) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {Z X P : Subgroup K} (hpos : Pos K Z X) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X) :
    rankThreeGamma 1 3 (P.map K.subtype) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEP, hE, hEc⟩ := exists_e9_le_sylow hpos.2.2.2.2.1.1
    hpos.2.2.2.2.2.1 hP
  obtain ⟨Q, rfl⟩ := hP
  set PG : Subgroup G := (Q.map X.subtype).map K.subtype
  have hP3 : IsPGroup 3 PG := (Q.isPGroup'.map X.subtype).map K.subtype
  have hPK : PG ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcP : Nat.card PG = Nat.card Q := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective Subtype.val_injective]
  have hEG : IsElemAbelian 3 (E.map K.subtype) := hE.map K.subtype
  have hKle : K ≤ rankThreeGamma 1 3 PG := by
    have hle : (⨆ (F : Subgroup K) (_ : F ≤ E) (_ : Nat.card F = 3),
        Subgroup.centralizer (F : Set K)) ≤ (rankThreeGamma 1 3 PG).comap K.subtype := by
      refine iSup_le fun F => iSup_le fun hFE => iSup_le fun hF3 => ?_
      intro k hk
      obtain ⟨x, hxF, hx1, -⟩ := CFSG.Quasithin.S153Q.Q1.exists_ne_one_of_card_three hF3
      show (k : G) ∈ rankThreeGamma 1 3 PG
      unfold rankThreeGamma
      refine GLBCore_mono (Subgroup.map_mono hEP) (mem_glbCore_of_commute Nat.prime_three hEG
        (x := (x : G)) ⟨x, hFE hxF, rfl⟩ (fun h => hx1 (Subtype.ext h)) ?_)
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hk x hxF).symm
    intro g hg
    exact hle ((hK.1 E hE (by rw [hEc]; norm_num)).symm ▸ Subgroup.mem_top (⟨g, hg⟩ : K))
  have h27 : 27 ≤ Nat.card PG := by
    rw [hcP]
    obtain ⟨-, -, -, -, -, hXZ, hXt⟩ := hpos
    rcases card_of_k328X hXZ hXt with ⟨-, hXc⟩ | ⟨-, hXc⟩
    · rw [CFSG.LocalAnalysis.UniquenessCase.UCK.card_sylow_eq Q (k := 3) (m := 2240)
        (by rw [hXc]; norm_num) (by norm_num)]
      norm_num
    · rw [CFSG.LocalAnalysis.UniquenessCase.UCK.card_sylow_eq Q (k := 5) (m := 68096)
        (by rw [hXc]; norm_num) (by norm_num)]
      norm_num
  exact rankThreeGamma_eq_top_of_normal K hP3 hPK h27 (by rw [hcP]; exact hK.2 Z X hpos Q)
    hrank hKle

theorem card_dvd_of_le_centralizer_reeF4Eight
    {K : Type} [Group K]
    (hR : ReeTitsModel K .twistedF4 2 3) {z : K} (hz : orderOf z = 3) (Y : Subgroup K)
    (hY : Y ≤ Subgroup.centralizer {z}) : Nat.card Y ∣ 16547328 := by
  obtain ⟨F, _, _, _, hF, ⟨φ⟩⟩ :=
    CFSG.Quasithin.H13.NQBlock.exists_mulEquiv_reeGamma_of_reeTitsModel (a := 1) le_rfl hR
  have hy : orderOf (φ z) = 3 := by rw [MulEquiv.orderOf_eq]; exact hz
  have hC := CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_card_centralizer hF (φ z) hy
  have hle : Y.map φ.toMonoidHom ≤ Subgroup.centralizer {φ z} := by
    rintro _ ⟨y, hyY, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hY hyY)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  have := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective φ.injective, hC] at this
  simpa using this

theorem not_dvd_of_k328Exc
    {K : Type} [Group K] [Finite K] (hK : K328ExcLieModel K)
    {Z X : Subgroup K} (hpos : Pos K Z X) (Q : Sylow 3 X) : ¬ 9 * Nat.card Q ∣ Nat.card K := by
  obtain ⟨hZ, hZX, hXC, -, -, hXZ, hXt⟩ := hpos
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXdvd : Nat.card X ∣ Nat.card K := Subgroup.card_subgroup_dvd_card X
  have hRee : LieModel K .twistedF4 0 2 3 → Nat.card X ∣ 16547328 := fun h => by
    obtain ⟨z, hzZ, hz1, hz3⟩ := CFSG.Quasithin.S153Q.Q1.exists_ne_one_of_card_three hZ
    refine card_dvd_of_le_centralizer_reeF4Eight (h.reeTitsModel (by decide)).2
      (orderOf_eq_prime hz3 hz1) X fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 (hXC hx)) z hzZ).symm
  have cG2 : ∀ {f : ℕ}, LieModel K .G2 0 2 f → Nat.card K = ordG2 (2 ^ f) := fun h =>
    CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2
      (h.chevalleyExceptionalModel (by decide)).2
  have cD4 : ∀ {f : ℕ}, 1 ≤ f → LieModel K .trialityD4 0 2 f →
      Nat.card K = ordTrialityD4 (2 ^ f) := fun hf h =>
    CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hf
      (h.chevalleyExceptionalModel (by decide)).2
  rcases card_of_k328X hXZ hXt with ⟨-, hXc⟩ | ⟨-, hXc⟩
  · rw [CFSG.LocalAnalysis.UniquenessCase.UCK.card_sylow_eq Q (k := 3) (m := 2240)
      (by rw [hXc]; norm_num) (by norm_num)]
    rw [hXc] at hXdvd
    rcases hK with h | h | h | h | h
    · rw [cG2 h]; decide
    · rw [cD4 (by norm_num) h]; decide
    · rw [cG2 h] at hXdvd; exact absurd hXdvd (by decide)
    · rw [cD4 (by norm_num) h] at hXdvd; exact absurd hXdvd (by decide)
    · exact absurd (hXc ▸ hRee h) (by decide)
  · rw [CFSG.LocalAnalysis.UniquenessCase.UCK.card_sylow_eq Q (k := 5) (m := 68096)
      (by rw [hXc]; norm_num) (by norm_num)]
    rw [hXc] at hXdvd
    rcases hK with h | h | h | h | h
    · rw [cG2 h] at hXdvd; exact absurd hXdvd (by decide)
    · rw [cD4 (by norm_num) h] at hXdvd; exact absurd hXdvd (by decide)
    · rw [cG2 h]; decide
    · rw [cD4 (by norm_num) h]; decide
    · rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4
        (h.reeTitsModel (by decide)).2]
      decide

theorem iSup_centralizer_eq_top_of_k328Exc
    {K : Type} [Group K] [Finite K]
    (hK : K328ExcLieModel K) (E : Subgroup K) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    (⨆ (F : Subgroup K) (_ : F ≤ E) (_ : Nat.card F = 3),
      Subgroup.centralizer (F : Set K)) = ⊤ := by
  rw [eq_top_iff, ← closure_commute_eq_top hK E hE hc, Subgroup.closure_le]
  rintro k ⟨x, hx, hx1, hk⟩
  have hord : orderOf x = 3 := orderOf_eq_prime (hE.2 x hx) hx1
  refine Subgroup.mem_iSup_of_mem (Subgroup.zpowers x) (Subgroup.mem_iSup_of_mem
    ((Subgroup.zpowers_le).2 hx) (Subgroup.mem_iSup_of_mem
      (by rw [Nat.card_zpowers, hord]) ?_))
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨n, rfl⟩
  exact ((Commute.zpow_right (show Commute k x from hk) n).eq).symm

theorem ambLeaves_of_k328ExcLieModel
    {K : Type} [Group K] [Finite K] (hK : K328ExcLieModel K) :
    AmbLeaves K :=
  ⟨iSup_centralizer_eq_top_of_k328Exc hK, fun _ _ hpos Q => not_dvd_of_k328Exc hK hpos Q⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc
