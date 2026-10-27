module

public import CFSG.Quasithin.H13.NQS134YB
public import CFSG.Quasithin.H13.U3S13473N
public import CFSG.Quasithin.H13.U3S1347I
public import CFSG.Quasithin.H13.U3S1347P4D
public import CFSG.Quasithin.H13.U3S1349L
public import CFSG.Quasithin.H13.U3S13473B

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits CFSG.Quasithin.H13.U3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem not_hat_of_cent {Y K : Subgroup G} (hred : IsTwoReducedIn Y (VZ T Y))
    (hcent : Y ⊓ centralizer (VZ T Y : Set G) = pCoreOf 2 Y) (hKY : K ≤ Y)
    (hcentR : K ⊓ centralizer (reducedAggregate Y : Set G) = A6.o2Z K) :
    ¬ A6.IsHatA6 K := by
  rintro ⟨-, hZ3, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVR := A7.le_reducedAggregate_of_isTwoReducedIn hred
  obtain ⟨⟨cb, hcb⟩, hcb1⟩ := ne_bot_iff_exists_ne_one.1
    ((one_lt_card_iff_ne_bot (center (↥K ⧸ CFSG.pCore 2 ↥K))).1 (by omega))
  have hcb1' : cb ≠ 1 := fun e => hcb1 (Subtype.ext e)
  have hcb3 : cb ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥(center (↥K ⧸ CFSG.pCore 2 ↥K))) (x := ⟨cb, hcb⟩)
    rw [hZ3] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hyb : ((c ^ 2 ^ a : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ≠ 1 := by
    rw [QuotientGroup.mk_pow]
    exact fun e => hcb1' (A6.eq_one_of_two_pow_of_cube e hcb3)
  have hy3 : (c ^ 2 ^ a) ^ 3 = 1 := by
    have hmem : (c ^ 2 ^ a) ^ 3 ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_pow, ← pow_mul,
        mul_comm, pow_mul, hcb3, one_pow]
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2) ⟨_, hmem⟩
    have h2 : ((c ^ 2 ^ a) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmm : ((c ^ 2 ^ a) ^ 3) ^ m = 1 := by
      rw [← pow_mul, ← pow_mul, show 2 ^ a * (3 * m) = 2 ^ a * m * 3 by ring, pow_mul, ← ham,
        pow_orderOf_eq_one, one_pow]
    exact A5.eq_one_of_pow_coprime h2 hmm (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm))
  have hyZ : ((c ^ 2 ^ a : ↥K) : G) ∈ A6.o2Z K := by
    refine ⟨c ^ 2 ^ a, ?_, rfl⟩
    show ((c ^ 2 ^ a : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ center _
    rw [QuotientGroup.mk_pow]
    exact pow_mem hcb _
  rw [← hcentR] at hyZ
  have hyC : ((c ^ 2 ^ a : ↥K) : G) ∈ centralizer (VZ T Y : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 hVR) hyZ.2
  have hyO : ((c ^ 2 ^ a : ↥K) : G) ∈ pCoreOf 2 Y := by
    rw [← hcent]
    exact mem_inf.2 ⟨hKY hyZ.1, hyC⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) ⟨_, hyO⟩
  have h2 : ((c ^ 2 ^ a : ↥K) : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : ((c ^ 2 ^ a : ↥K) : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have h1 : ((c ^ 2 ^ a : ↥K) : G) = 1 :=
    A5.eq_one_of_pow_coprime h2 h3 (Nat.Coprime.pow_left k (by norm_num))
  apply hyb
  rw [show (c ^ 2 ^ a : ↥K) = 1 from Subtype.ext h1, QuotientGroup.mk_one]

theorem f618_K (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big) (S : A6.Setting134 G T L V)
    {Y Y₁ Y₂ K : Subgroup G} (htr : F6.IsGoldschmidtTripleIn Y Y₁ Y₂) (hYH : InH T Y)
    (hK : K ∈ cComp Y) (hN : Y ≤ normalizer (K : Set G))
    (hcases : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6))) :
    ¬ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∧
      ∀ {Yi : Subgroup G}, Yi ≤ Y → T ≤ Yi → T.relIndex Yi = 3 → oTwoRes Yi ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hYH.1
  have hKH := le_of_mem_cComp hK
  obtain ⟨hs, hcK⟩ := U3.simple_of_cases hcases
  have h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hcK with e | e | e <;> rw [e] <;> norm_num
  have hrel : (pCoreOf 2 K).relIndex K = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [relIndex, U3.pCoreOf_subgroupOf_eq_pCore]
    rfl
  obtain ⟨N3, hN3⟩ : ∃ X : Subgroup G, X = (CFSG.pPrimeCore 3 ↥Y).map Y.subtype := ⟨_, rfl⟩
  have hN3n : Y ≤ normalizer (N3 : Set G) := hN3 ▸ U3.le_normalizer_map_subtype _
  have hN3c : Nat.Coprime 3 (Nat.card N3) := by
    rw [hN3, card_map_of_injective Y.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hKN3 : K ⊓ N3 ≤ pCoreOf 2 K :=
    U3.inf_le_pCoreOf_of_coprime_three (hKH.trans hN3n) hN3c hs h3
  have hO₀ : pCoreOf 2 K ≤ pCoreOf 2 Y := U3.pCoreOf_le_pCoreOf hKH hN
  have hON3 : pCoreOf 2 Y ≤ N3 := by
    rw [hN3]
    exact map_mono F6.pCore_le_pPrimeCore
  have hinf : K ⊓ N3 = pCoreOf 2 K :=
    le_antisymm hKN3 (le_inf (pCoreOf_le 2 K) (hO₀.trans hON3))
  have hsylK : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hsyl₀ hKH hN
  have hOT : pCoreOf 2 K ≤ T ⊓ K := pCoreOf_two_le_of_isSylowTwoOf hsylK
  have hTK : T ⊓ K ≤ Y := inf_le_right.trans hKH
  have hinfT : (T ⊓ K) ⊓ N3 = pCoreOf 2 K :=
    le_antisymm ((inf_le_inf_right N3 inf_le_right).trans hKN3) (le_inf hOT (hO₀.trans hON3))
  have hcardN : Nat.card ↥((K.subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))) =
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [U3.card_map_pPrimeCore hKH, ← hN3, ← inf_relIndex_right, inf_comm, hinf, hrel]
  have hcardP : Nat.card ↥(((T ⊓ K).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))) =
      (pCoreOf 2 K).relIndex (T ⊓ K) := by
    rw [U3.card_map_pPrimeCore hTK, ← hN3, ← inf_relIndex_right, inf_comm, hinfT]
  have hm := relIndex_mul_relIndex (pCoreOf 2 K) (T ⊓ K) K hOT inf_le_right
  rw [hrel] at hm
  have hrel0 : (pCoreOf 2 K).relIndex (T ⊓ K) ≠ 0 := index_ne_zero_of_finite
  have hodd : Nat.Coprime 2 ((T ⊓ K).relIndex K) :=
    Nat.coprime_two_left.2 (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hsylK.2.2))
  have hdvd : ∀ j : ℕ, 2 ^ j ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) →
      2 ^ j ≤ (pCoreOf 2 K).relIndex (T ⊓ K) := fun j hj => by
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero hrel0) ((Nat.Coprime.pow_left j
      hodd).dvd_of_dvd_mul_right ?_)
    rw [hm]
    exact hj
  have h4 : 4 ≤ (pCoreOf 2 K).relIndex (T ⊓ K) :=
    hdvd 2 (by rcases hcK with e | e | e <;> rw [e] <;> norm_num)
  have h8 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≠ 60 → 8 ≤ (pCoreOf 2 K).relIndex (T ⊓ K) :=
    fun h60 => hdvd 3 (by
      rcases hcK with e | e | e
      · exact absurd e h60
      · rw [e]; norm_num
      · rw [e]; norm_num)
  rcases htr.f6_18Cat hF (stronglyQuasithin_of_pCoreOf_ne_bot S.h13.qtke hYH.2)
    (kGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hYH.2) with
    ⟨-, hAm, -, hconc⟩ | ⟨-, -, hS3, -, -⟩
  swap
  ·
    exfalso
    obtain ⟨e⟩ := hS3
    have h1 := card_le_of_le (le_top : (K.subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) ≤ ⊤)
    rw [card_top, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3),
      Fintype.card_fin, hcardN] at h1
    rcases hcK with e' | e' | e' <;> rw [e'] at h1 <;> norm_num [Nat.factorial] at h1
  have hKn : (K.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKH).2 hN
  have hP2 : IsPGroup 2 ↥((T ⊓ K).subgroupOf Y) :=
    hsylK.2.1.of_equiv (subgroupOfEquivOfLe hTK).symm
  obtain ⟨hNO, hN60⟩ := U3.eq_oTwoUpper_of_f618 hBig A5.factL2Three_holds hAm hconc
    (hKn.map _ (QuotientGroup.mk'_surjective _))
    (by rw [← map_commutator, U3.commutator_subgroupOf_eq hKH (perfect_of_mem_cComp hK)])
    (map_mono fun x hx => mem_subgroupOf.2 ((inf_le_right : T ⊓ K ≤ K) (mem_subgroupOf.1 hx)))
    (hP2.map _) (by rw [hcardP]; exact h4)
    (by
      rcases eq_or_ne (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) 60 with e | e
      · exact Or.inl ⟨0, by rw [hcardN, e]; rfl⟩
      · exact Or.inr (by rw [hcardP]; exact h8 e))
  have hnot5 : ¬ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e⟩
    apply hN60 0
    rw [hcardN, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  refine ⟨hnot5, fun {Yi} hYi hTi h3i => ?_⟩
  refine (closure_le _).2 fun x hx => ?_
  obtain ⟨hxH, m, hm, hxm⟩ := hx
  have hx3 : (⟨x, hYi hxH⟩ : ↥Y) ^ 3 ^ 1 = 1 := Subtype.ext (by
    simpa using U3.pow_three_of_relIndex_three S.h13.sylow.1 hTi h3i hxH hm hxm)
  have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) ⟨x, hYi hxH⟩ ∈
      (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) := by
    rw [hNO]
    refine mem_oTwoUpper_of_odd (mem_top _) (Odd.of_dvd_nat (by decide : Odd 3)
      (orderOf_dvd_of_pow_eq_one ?_))
    rw [← map_pow, show (⟨x, hYi hxH⟩ : ↥Y) ^ 3 = 1 by simpa using hx3, map_one]
  exact mem_subgroupOf.1 (A5.mem_of_pow_three_of_mem_map htr.isSolvable_pPrimeCore
    (subgroupOf_mem_cComp hK) hx3 hmem)

theorem stmt13473NonSolv_of (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1345 : Stmt13_4_5) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big) :
    U3.Stmt13473NonSolv := by
  intro G _ _ T L V S H₁ H₂ Y₂ Y he h hK₂L hiii hH₀ hH₀M hY₂H hY₂N hY₂ hfpf hmoves hZV₀ hY₂T
    h3 hq hY₂M hY hinf htr hYH hYM hred hcent hJL1 hJ hnot hns
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁def
  obtain ⟨⟨K, hK⟩, hall⟩ := h1345 G T L V S Y hYH hYM hns
  obtain ⟨⟨-, hKf⟩, hN, hcases, hKM, -, hKZV, -, ⟨W, hW⟩, hWall⟩ := hall K hK
  obtain ⟨hTW, hfsu, hWcl, ⟨hab, hmod⟩, ho2Z, hcentR⟩ := hWall W hW
  have hKY := le_of_mem_cComp hK
  have hnhat := not_hat_of_cent hred hcent hKY hcentR
  have hcases' : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) := by
    rcases hcases with h5 | h32 | h6 | hhat
    · exact Or.inl h5
    · exact Or.inr (Or.inl h32)
    · exact Or.inr (Or.inr h6)
    · exact absurd hhat hnhat
  obtain ⟨hnot5, hKi⟩ := f618_K hF hBig S htr hYH hK hN hcases'
  have hKtype : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) :=
    hcases'.resolve_left hnot5
  obtain ⟨hL13, hL1O, hL1q⟩ := s134_L1T_a6 S he
  have hL1Y : L₁ ⊔ T ≤ Y := hY ▸ le_sup_left
  have hY2Y : Y₂ ⊔ T ≤ Y := hY ▸ le_sup_right
  have hL1K : L₁ ≤ K := by
    have h1 := hKi hL1Y le_sup_right (s1347_relIndex_three S le_sup_right hL1q)
    refine le_trans ?_ h1
    refine (closure_le _).2 fun x hx => subset_closure ⟨mem_sup_left (subset_closure hx), hx.2⟩
  have hY2K : Y₂ ≤ K := by
    have h1 := hKi hY2Y le_sup_right h3
    rw [← hY₂]
    exact (oTwoRes_mono' le_sup_left).trans h1
  obtain ⟨y, hyY₂, hyC⟩ := hmoves
  have hcZ : U3.cZ T K = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxZ, hxK⟩ := hx
    rw [mem_bot]
    refine hfpf y hyY₂ hyC x (hZV₀ hxZ) ?_
    rw [mem_centralizer_iff.1 hxK y (hY2K hyY₂), mul_inv_cancel_right]
  have hTK : T ≤ normalizer (K : Set G) := hYH.1.trans hN
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  obtain ⟨hs, -⟩ := U3.simple_of_cases hcases'
  have hKJ : ⁅K, thompsonJ T⁆ = K := by
    have hle : ⁅K, thompsonJ T⁆ ≤ K := by
      rw [commutator_le]
      intro k hk j hj
      have h1 : j * k⁻¹ * j⁻¹ ∈ K := (mem_normalizer_iff.mp (hTK (hJT hj)) _).mp (inv_mem hk)
      rw [commutatorElement_def, show k * j * k⁻¹ * j⁻¹ = k * (j * k⁻¹ * j⁻¹) by group]
      exact mul_mem hk h1
    have hKN : K ≤ normalizer ((⁅K, thompsonJ T⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator_left' K (thompsonJ T)
    have : (⁅K, thompsonJ T⁆.subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer hle).2 hKN
    have hnotle : ¬ ⁅K, thompsonJ T⁆.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
      intro hle'
      have hL1O' : L₁ ≤ pCoreOf 2 K := by
        intro l hl
        have hl1 : l ∈ ⁅K, thompsonJ T⁆ := by
          rw [← hJL1] at hl
          exact commutator_mono hL1K le_rfl hl
        have hl2 := hle' (mem_subgroupOf.2 (show ((⟨l, hL1K hl⟩ : ↥K) : G) ∈ _ from hl1))
        rw [← U3.pCoreOf_subgroupOf_eq_pCore, mem_subgroupOf] at hl2
        exact hl2
      have hL1T : L₁ ≤ L₁ ⊓ T := le_inf le_rfl
        (hL1O'.trans (pCoreOf_two_le_of_isSylowTwoOf (A4.isSylowTwoOf_inf_normal
          (A5.isSylowTwoOf_of_le S.h13.sylow hYH.1) hKY hN)) |>.trans inf_le_left)
      have h1 : (L₁Of L (fsuV1 T V) ⊓ T).relIndex (L₁Of L (fsuV1 T V)) = 1 :=
        relIndex_eq_one.2 hL1T
      omega
    have htop := eq_top_of_not_le_pCore' hperf hs hnotle
    refine le_antisymm hle fun k hk => ?_
    have hk' : (⟨k, hk⟩ : ↥K) ∈ ⁅K, thompsonJ T⁆.subgroupOf K := by rw [htop]; trivial
    exact mem_subgroupOf.1 hk'
  have hZ2 : 2 < Nat.card ↥(quasithinOmegaOneCenter T) := by
    have h1 := U3.s134_card_Z h1332 hC58 h317 h56 S ⟨Y, hYH, hYM⟩
    have hzV : S.zV ∈ quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) :=
      mem_inf.2 ⟨U3.s134_zV_mem_Z S, (S.mem_ZV_iff.2 (Or.inr rfl)).2⟩
    have h2 : 1 < Nat.card ↥(quasithinOmegaOneCenter T ⊓ centralizer (L : Set G)) := by
      rw [one_lt_card_iff_ne_bot]
      intro hb
      rw [hb, mem_bot] at hzV
      exact S.zV_ne_one hzV
    omega
  have D : KWData S K W := ⟨hKf, hTK, hKM, hKZV, hKJ, hcases, hW, hTW, hfsu, hWcl, hmod, ho2Z⟩
  exact D.false_of_cZ_eq_bot hC137 h1332 h1228 h56 he hL1K hKtype hcZ hZ2

end CFSG.Quasithin.H13.NQS134
