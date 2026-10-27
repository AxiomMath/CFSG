module

public import CFSG.Quasithin.Vol2.Ch12Sec5FinB
public import CFSG.Quasithin.Vol2.Ch12Sec5FinL24Pf
public import CFSG.Quasithin.Vol2.Ch12Sec5L11
public import CFSG.Quasithin.Vol2.Ch12Sec4MinParabolic
public import CFSG.Quasithin.Background.C1PackS15212A
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftLie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Fin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {X : Subgroup G} {x : G} {m n : ℕ} (hcop : Nat.Coprime m n)
    (hx : x ^ n = 1) (hxm : x ^ m ∈ X) : x ∈ X := by
  have h := Nat.gcd_eq_gcd_ab m n
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  have e : x = (x ^ m) ^ Nat.gcdA m n * (x ^ n) ^ Nat.gcdB m n := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e, hx, one_zpow, mul_one]
  exact X.zpow_mem hxm _

omit [Finite G] in
theorem mem_of_mem_sup_of_pow {X T : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) {x : G} (hx : x ∈ X ⊔ T) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x ∈ X := by
  obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hT2 hTX hx
  exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow _ _ (by norm_num)) hk hj

theorem pRank_three_sup_le {X T : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    CFSG.Open.pRank 3 (X ⊔ T) ≤ CFSG.Open.pRank 3 X := by
  obtain ⟨E, hEXT, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (X ⊔ T)
  refine CFSG.SectionRank.le_pRank (by norm_num) (fun x hx => ?_) hE hEc
  exact mem_of_mem_sup_of_pow hT2 hTX (hEXT hx) (k := 1) (by simpa using hE.2 x hx)

omit [Finite G] in
theorem le_normalizer_centralizerMod {G₁ L₁ : Subgroup G}
    (hN : G₁ ≤ Subgroup.normalizer (L₁ : Set G)) :
    G₁ ≤ Subgroup.normalizer (centralizerMod (pCoreOf 2 L₁) G₁ L₁ : Set G) := by
  have hchar : (CFSG.Open.pCore 2 ↥L₁).Characteristic := by
    infer_instance
  have hON : G₁ ≤ Subgroup.normalizer (pCoreOf 2 L₁ : Set G) :=
    hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.Open.pCore 2 ↥L₁))
  have key : ∀ g ∈ G₁, ∀ x ∈ centralizerMod (pCoreOf 2 L₁) G₁ L₁,
      g * x * g⁻¹ ∈ centralizerMod (pCoreOf 2 L₁) G₁ L₁ := by
    intro g hg x hx
    obtain ⟨hxG, hxN, hxc⟩ := hx
    refine ⟨G₁.mul_mem (G₁.mul_mem hg hxG) (G₁.inv_mem hg), Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hON hg) hxN) (Subgroup.inv_mem _ (hON hg)), fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ L₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hN (G₁.inv_mem hg)) u).mp hu
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hON hg) _).mp (hxc _ hu')
    have e : g * (x * (g⁻¹ * u * g) * x⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ =
        g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ * u⁻¹ := by group
    rw [← e]
    exact h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (G₁.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem card_lieModel_psl321 {Y : Type} [Group Y] (h : LieModel Y .PSL 3 2 1) :
    Nat.card Y = 168 :=
  CFSG.Blueprint.LieModel.card_psl_three_two h

theorem mem_of_three_pow (h1228 : Stmt12_2_8) {T L V : Subgroup G} (hH : Hyp125 G T L V)
    {x : G} (hxM : x ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x ∈ L := by
  obtain ⟨e⟩ := hH.quot
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 9999360 :=
    (Nat.card_congr e.toEquiv).trans card_sl_five_zmod_two
  rcases h1228 G T L V hH.hyp with h | (h | h) | ⟨⟨n, hn, -, hZ, -⟩, -⟩
  · rw [← h]
    exact Subgroup.subset_closure ⟨hxM, k, hk⟩
  · exfalso
    obtain ⟨e'⟩ := h
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  · exfalso
    rw [card_lieModel_psl321 h] at hc
    omega
  · exfalso
    rw [center_eq_bot_of_mulEquiv_sl (by norm_num) e, Subgroup.card_bot] at hZ
    omega

theorem exists_hStar'
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (hE22 : E2.E22StatementC)
    (hTor : E2.E22TorusCover) {T L V : Subgroup G} {F : Frame125 T L V} (hH : Hyp125 G T L V)
    (hG₁ : ¬ Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (h2 : Concl12_5_2 T L V F)
    (hL₁ : quasithinIsCComponent (li L F.V1) (Subgroup.normalizer (F.V1 : Set G)) ∧
      Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (li L F.V1 : Set G))
    (h12 : Concl12_5_12 T L V F) :
    ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H ∧
      H ≤ Subgroup.normalizer (F.V1 : Set G) ∧
      Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* ↥(alternatingGroup (Fin 5))) ∧
      (∀ k ∈ oTwoUpper H, ∀ l ∈ li L F.V1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 (li L F.V1)) ∧
      ¬ oTwoUpper H ≤ Subgroup.normalizer (L : Set G) ∧
      mi T L F.V1 ≤ li L F.V1 ⊔ H := by
  have hyp := hH.hyp
  have hf := S125Ex.Facts125.of h1222 hH
  obtain ⟨hL₁c, hG₁N⟩ := hL₁
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hTsyl : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (F.V1 : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTG₁
  have hL₁G₁ : li L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hL₁L : li L F.V1 ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  obtain ⟨e⟩ := lOne_quot_equiv h1222 hH h2 (hTG₁.trans hG₁N)
  set X := centralizerMod (pCoreOf 2 (li L F.V1)) (Subgroup.normalizer (F.V1 : Set G))
    (li L F.V1) with hXdef
  have hXG₁ : X ≤ Subgroup.normalizer (F.V1 : Set G) := centralizerMod_le_left _ _ _
  have hG₁le := le_sup_of_quot hL₁G₁ hG₁N hTsyl e
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hXTM : ¬ X ⊔ T ≤ Subgroup.normalizer (L : Set G) := by
    intro h
    exact hG₁ (hG₁le.trans (sup_le (le_sup_left.trans h)
      (sup_le (hL₁L.trans Subgroup.le_normalizer) hTM)))
  have hV₁2 : IsPGroup 2 ↥F.V1 := fun x =>
    ⟨1, Subtype.ext (by simpa using hf.sq x (S125.V1_le F x.2))⟩
  have hV₁T : F.V1 ≤ T := (S125.V1_le F).trans hf.le_T
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (F.V1 : Set G) := sup_le hXG₁ hTG₁
  have hInH : InH T (X ⊔ T) := by
    refine ⟨le_sup_right, fun h => S125.V1_ne_bot F (le_bot_iff.mp ?_)⟩
    rw [← h]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hV₁T.trans le_sup_right) hXTN
      hV₁2
  obtain ⟨H, hHs, hHX⟩ := L1295.exists_isHStar_le hInH hXTM
  have hHG₁ : H ≤ Subgroup.normalizer (F.V1 : Set G) := hHX.trans hXTN
  obtain ⟨hn2, hhall⟩ := h12 H hHs hHG₁
  have hT2 : IsPGroup 2 ↥T := hyp.sylow.1
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    hTG₁.trans (le_normalizer_centralizerMod hG₁N)
  have hloc : IsTwoLocal (Subgroup.normalizer (F.V1 : Set G)) :=
    ⟨F.V1, S125.V1_ne_bot F, hV₁2, rfl⟩
  have hG₁3 : CFSG.Open.pRank 3 (Subgroup.normalizer (F.V1 : Set G)) ≤ 2 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three (by norm_num)
      _ hloc).trans hyp.qtke.2.2
  have hm3 : CFSG.Open.pRank 3 H ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hHX).trans
      ((pRank_three_sup_le hT2 hTX).trans (pRank_three_le_one hL₁G₁ hG₁N hG₁3 e))
  have hmin := Hyp1223.minParabolic_of_isHStar h331 hyp hHs
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hHs.1.2
  have hA5 := minPar125L24_of hE22 hTor G H T _ hmin hSQ hn2 hm3 hhall
  have hKX : oTwoUpper H ≤ X := by
    refine (oTwoUpper_mono hHX).trans
      (L1295.oTwoUpper_le_of_normal_sup le_sup_left ?_ hT2 le_sup_right le_rfl)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTX)
  have hKM : ¬ oTwoUpper H ≤ Subgroup.normalizer (L : Set G) := by
    intro h
    apply hHs.2.1
    have hTH : QuasithinUnique.IsSylowTwoOf T H :=
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hHs.1.1
    rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow hTH]
    exact sup_le h hTM
  have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
  obtain ⟨n, -, -, hL⟩ := E2.e22BorelLift hE22 hTor hmin hSQ hn1
  obtain ⟨-, R, -, -, -, ⟨C, hCM, hCodd, k, hCk⟩, -⟩ := hL
  obtain ⟨hC1, hC3⟩ := hhall C hCM hCodd ⟨k, hCk⟩
  obtain ⟨⟨b, hbC⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC1
  obtain ⟨j, hj⟩ := hC3 ⟨b, hbC⟩
  have hbj : b ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbHM := hCM hbC
  have hbL : b ∈ L := mem_of_three_pow h1228 hH hbHM.2 hbj
  have hbX : b ∈ X := mem_of_mem_sup_of_pow hT2 hTX (hHX hbHM.1) hbj
  have hbM₁ : b ∈ mi T L F.V1 := ⟨Subgroup.mem_sup_left hbL, hHG₁ hbHM.1⟩
  have hM₁ := mi_le_sup h1222 hH h2 hL₁c hG₁N hbM₁ hbj hb1' hbX.2.2
  refine ⟨H, hHs, hHG₁, hA5, fun k hk l hl => (hKX hk).2.2 l hl, hKM, hM₁.trans ?_⟩
  exact sup_le (sup_le le_sup_left ((Subgroup.zpowers_le.mpr hbHM.1).trans le_sup_right))
    (hHs.1.1.trans le_sup_right)

end S125Fin

end CFSG.Quasithin.H13
