module

public import CFSG.Quasithin.Vol2.Ch12Sec4E61
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Background.E6Thirteen
public import CFSG.Quasithin.Background.A1bTransvection

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def L3HyperplaneFact1248 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 4 →
    ∀ X : Subgroup (MulAut V), IsSimpleGroup X → Nat.card X = 168 → commV X = ⊤ →
      Nat.card (fixV X) = 2 →
      ∀ U : Subgroup V, U.index = 2 → ¬ fixV X ≤ U →
        IsMaxSubgroupIn X (X ⊓ stabSub U) ∧ (X ⊓ stabSub U).relIndex X ≠ 2 ∧
          ∃ Y : Subgroup (MulAut V), Y ≤ X ⊓ stabSub U ∧ Nat.card Y = 3 ∧ ¬ Y ≤ centSub U

@[expose] def G2HyperplaneFact1248 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X Lb : Subgroup (MulAut V), Lb ≤ X → X ≤ Subgroup.normalizer (Lb : Set (MulAut V)) →
      (∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ Lb) → commV Lb = ⊤ → Nat.card (fixV Lb) = 2 →
      G2NaturalDerived Lb ⊤ (fixV Lb) 1 →
      ∀ U : Subgroup V, U.index = 2 → ¬ fixV Lb ≤ U →
        IsMaxSubgroupIn X (X ⊓ stabSub U) ∧ (X ⊓ stabSub U).relIndex X ≠ 2 ∧
          ∃ Y : Subgroup (MulAut V), Y ≤ Lb ⊓ stabSub U ∧ Nat.card Y = 3 ∧ ¬ Y ≤ centSub U

@[expose] def CharTwo1248 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∀ U : Subgroup G, U ≤ V → U.relIndex V = 2 →
        ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) →
          QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G))

variable {G : Type} [Group G]

section Stab

variable {V U H : Subgroup G} [IsMulCommutative ↥V]

theorem twoPrimeResidual_le_self (H : Subgroup G) : twoPrimeResidual H ≤ H :=
  iInf₂_le H ⟨le_rfl, Subgroup.le_normalizer, by rw [Subgroup.relIndex_self]; norm_num⟩

omit [IsMulCommutative ↥V] in
theorem centralizer_le_normalizer_of_le (hUV : U ≤ V) :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (U : Set G) :=
  (Subgroup.centralizer_le hUV).trans (Subgroup.centralizer_le_normalizer _)

theorem conjAct_mem_stabSub_iff (hUV : U ≤ V) (g : Subgroup.normalizer (V : Set G)) :
    conjAct V g ∈ stabSub (U.subgroupOf V) ↔ (g : G) ∈ Subgroup.normalizer (U : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hx : x ∈ V
    · have h1 := h ⟨x, hx⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, A1b.conjAct_coe] at h1
      exact h1.symm
    · refine ⟨fun hxU => absurd (hUV hxU) hx, fun hxU => absurd ?_ hx⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (V : Set G)).inv_mem g.2)
        _).1 (hUV hxU)
      simpa [mul_assoc] using h2
  · intro h u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, A1b.conjAct_coe]
    exact (Subgroup.mem_normalizer_iff.1 h u).symm

theorem autOn_inf_normalizer (hUV : U ≤ V) :
    autOn (H ⊓ Subgroup.normalizer (U : Set G)) V = autOn H V ⊓ stabSub (U.subgroupOf V) := by
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
    exact ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg.1),
      (conjAct_mem_stabSub_iff hUV g).2 hg.2⟩
  · rintro ⟨hφ, hst⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [Subgroup.mem_subgroupOf] at hg
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.2 ⟨hg, (conjAct_mem_stabSub_iff hUV g).1 hst⟩)

theorem isMaxSubgroupIn_of_autOn (hUV : U ≤ V) (hH : H ≤ Subgroup.normalizer (V : Set G))
    (h : IsMaxSubgroupIn (autOn H V) (autOn H V ⊓ stabSub (U.subgroupOf V))) :
    IsMaxSubgroupIn H (H ⊓ Subgroup.normalizer (U : Set G)) := by
  obtain ⟨hlt, hmax⟩ := h
  have hker : H ⊓ Subgroup.centralizer (V : Set G) ≤ H ⊓ Subgroup.normalizer (U : Set G) :=
    inf_le_inf_left H (centralizer_le_normalizer_of_le hUV)
  have hlift : ∀ K : Subgroup G, H ⊓ Subgroup.normalizer (U : Set G) ≤ K → K ≤ H →
      autOn K V = autOn H V → K = H := by
    intro K hNK hKH heq
    refine le_antisymm hKH fun h hh => ?_
    have h1 : conjAct V ⟨h, hH hh⟩ ∈ autOn K V := by
      rw [heq]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hh)
    obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.1 h1
    rw [Subgroup.mem_subgroupOf] at hk
    have h2 : (k : G)⁻¹ * h ∈ Subgroup.centralizer (V : Set G) := by
      have h3 : conjAct V (k⁻¹ * ⟨h, hH hh⟩) = 1 := by
        rw [map_mul, map_inv, hkh, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.1 h3
    have h4 : (k : G)⁻¹ * h ∈ K := hNK (hker ⟨H.mul_mem (H.inv_mem (hKH hk)) hh, h2⟩)
    have h5 := K.mul_mem hk h4
    rwa [mul_inv_cancel_left] at h5
  refine ⟨lt_of_le_of_ne inf_le_left fun heq => ?_, fun K hK hKH => ?_⟩
  · apply (lt_iff_le_and_ne.1 hlt).2
    rw [← autOn_inf_normalizer hUV, heq]
  · refine hlift K hK.le hKH (hmax _ ?_ (A4.autOn_mono hKH))
    obtain ⟨k, hkK, hkN⟩ : ∃ k ∈ K, k ∉ Subgroup.normalizer (U : Set G) := by
      by_contra hall
      push Not at hall
      exact hK.ne (le_antisymm hK.le fun k hk => ⟨hKH hk, hall k hk⟩)
    rw [← autOn_inf_normalizer hUV]
    refine lt_of_le_of_ne (A4.autOn_mono hK.le) fun heq => ?_
    have h1 : conjAct V ⟨k, hH (hKH hkK)⟩ ∈ autOn K V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hkK)
    rw [← heq, autOn_inf_normalizer hUV] at h1
    exact hkN ((conjAct_mem_stabSub_iff hUV _).1 h1.2)

theorem relIndex_inf_normalizer_eq [Finite G] (hUV : U ≤ V)
    (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    (H ⊓ Subgroup.normalizer (U : Set G)).relIndex H =
      (autOn H V ⊓ stabSub (U.subgroupOf V)).relIndex (autOn H V) := by
  have hKH : H ⊓ Subgroup.normalizer (U : Set G) ≤ H := inf_le_left
  have hCK : H ⊓ Subgroup.centralizer (V : Set G) ≤ H ⊓ Subgroup.normalizer (U : Set G) :=
    inf_le_inf_left H (centralizer_le_normalizer_of_le hUV)
  have hKC : H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer (V : Set G) =
      H ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hCK inf_le_right)
  have h1 := card_autOn_eq_relIndex hH
  have h2 := card_autOn_eq_relIndex (hKH.trans hH)
  rw [hKC] at h2
  have h3 := Subgroup.relIndex_mul_relIndex _ _ _ hCK hKH
  have h4 := Subgroup.relIndex_mul_card (autOn (H ⊓ Subgroup.normalizer (U : Set G)) V)
    (autOn H V)
  rw [inf_eq_left.2 (A4.autOn_mono hKH)] at h4
  rw [← autOn_inf_normalizer hUV]
  have hpos : 0 < Nat.card ↥(autOn (H ⊓ Subgroup.normalizer (U : Set G)) V) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h4, h1, h2, ← h3]
  ring

theorem exists_card_three_of_autOn {L : Subgroup G} (hUV : U ≤ V)
    (hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)))
    {Y : Subgroup (MulAut ↥V)} (hYL : Y ≤ autOn L V ⊓ stabSub (U.subgroupOf V))
    (hY3 : Nat.card Y = 3) (hYC : ¬ Y ≤ centSub (U.subgroupOf V)) :
    ∃ Y' : Subgroup G, Y' ≤ Subgroup.normalizer (U : Set G) ∧ Nat.card Y' = 3 ∧
      Y' ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyY, hyC⟩ : ∃ y ∈ Y, y ∉ centSub (U.subgroupOf V) := by
    by_contra hall
    push Not at hall
    exact hYC hall
  have hy3 : y ^ 3 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨y, hyY⟩ : ↥Y)
    rw [hY3] at h1
    have h2 : (⟨y, hyY⟩ : ↥Y) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hord : orderOf y = 3 := by
    refine orderOf_eq_prime hy3 fun h1 => hyC ?_
    rw [h1]
    exact (centSub (U.subgroupOf V)).one_mem
  obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.1 (hYL hyY).1
  rw [Subgroup.mem_subgroupOf] at hl
  have hl3 : (l : G) ^ 3 ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨L.pow_mem hl 3, ?_⟩
    have h1 : conjAct V (l ^ 3) = 1 := by rw [map_pow, hly, hy3]
    exact A4.conjAct_eq_one_iff.1 h1
  obtain ⟨k, hk⟩ := hker ⟨_, hl3⟩
  have hk' : (l : G) ^ (3 * 2 ^ k) = 1 := by
    rw [pow_mul]
    exact congrArg Subtype.val hk
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hy'y : conjAct V (l ^ (4 ^ k)) = y := by
    rw [map_pow, hly, ← pow_mod_orderOf, hord, h4, pow_one]
  have hy'3 : ((l : G) ^ (4 ^ k)) ^ 3 = 1 := by
    rw [← pow_mul, show 4 ^ k * 3 = 3 * 2 ^ k * 2 ^ k by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring, pow_mul, hk', one_pow]
  have hy'N : (l : G) ^ (4 ^ k) ∈ Subgroup.normalizer (U : Set G) := by
    have h1 := (conjAct_mem_stabSub_iff hUV (l ^ (4 ^ k))).1 (by rw [hy'y]; exact (hYL hyY).2)
    simpa using h1
  have hy'C : (l : G) ^ (4 ^ k) ∉ Subgroup.centralizer (U : Set G) := by
    intro hc
    apply hyC
    rw [← hy'y]
    intro u hu
    apply Subtype.ext
    rw [A1b.conjAct_coe]
    have hu' : (u : G) ∈ U := Subgroup.mem_subgroupOf.1 hu
    have h1 := Subgroup.mem_centralizer_iff.1 hc _ hu'
    show (l : G) ^ (4 ^ k) * (u : G) * ((l : G) ^ (4 ^ k))⁻¹ = u
    rw [← h1, mul_inv_cancel_right]
  have hy'1 : (l : G) ^ (4 ^ k) ≠ 1 := fun h1 => hy'C (by rw [h1]; exact Subgroup.one_mem _)
  have hord' : orderOf ((l : G) ^ (4 ^ k)) = 3 := orderOf_eq_prime hy'3 hy'1
  have hcard : Nat.card ↥(Subgroup.zpowers ((l : G) ^ (4 ^ k))) = 3 := by
    rw [Nat.card_zpowers, hord']
  refine ⟨Subgroup.zpowers ((l : G) ^ (4 ^ k)), Subgroup.zpowers_le.2 hy'N, hcard, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have : Finite ↥(Subgroup.zpowers ((l : G) ^ (4 ^ k))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hxord : orderOf x = 3 := by
    have h1 := orderOf_dvd_natCard (⟨x, hx.1⟩ : ↥(Subgroup.zpowers ((l : G) ^ (4 ^ k))))
    rw [Subgroup.orderOf_mk, hcard] at h1
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have heq : Subgroup.zpowers x = Subgroup.zpowers ((l : G) ^ (4 ^ k)) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx.1)
      (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hord']))
  apply hy'C
  have h1 : (l : G) ^ (4 ^ k) ∈ Subgroup.zpowers x := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  exact Subgroup.zpowers_le.2 hx.2 h1

end Stab

variable [Finite G]

theorem lemma12_4_8_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h614 : ASInputs.AS_E_6_14) (hL3 : L3HyperplaneFact1248)
    (hG2 : G2HyperplaneFact1248) (hchar : CharTwo1248) : Lemma12_4_8 := by
  intro G _ _ T L V hcx hq
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hcx hq
  have := hf.comm
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hV2 : IsPGroup 2 ↥V := hyp.sylow.1.to_le hf.le_T
  have hzV : z ∈ V := hf.mem_zV.1
  have hV1 : V ≠ ⊥ := fun h => hf.ne_one (by rw [h] at hzV; exact Subgroup.mem_bot.1 hzV)
  have hE := hypE61_of_cx h331 h1222 h323 h3228 hcx hf.isElemAbelian hV1 hf.le_T hf.T_le
    hf.normalizes
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hf.normalizes hf.T_le
  have hcommV := commV_autOn_eq_top hf.normalizes hf.commutator
  have hfix : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hf.normalizes, card_subgroupOf_eq_card_inf, hf.card_zV]
  have hLX : autOn L V ≤ autOn (L ⊔ T) V := A4.autOn_mono le_sup_left
  have hXN : autOn (L ⊔ T) V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_autOn_of_le (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hX2 : ∀ y ∈ autOn (L ⊔ T) V, ∃ e : ℕ, y ^ 2 ^ e ∈ autOn L V :=
    InternalSec.autOn_two_of hf.normalizes fun y hy => by
      obtain ⟨k, hk⟩ := E6.exists_pow_mem_of_mem_sup hyp.sylow.1 hyp.normalizes hy
      exact ⟨k, le_sup_left (b := Subgroup.centralizer (V : Set G)) hk⟩
  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rcases hq with h3 | hU
      · obtain ⟨e⟩ := h3
        have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
        exact e.isSimpleGroup
      · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hf.normalizes hf.pCore hs hf.notCent
    have hsA : IsSimpleGroup ↥(autOn L V) := eA.isSimpleGroup
    have hO2 : pCoreOf 2 (autOn L V) = ⊥ := by
      refine pCoreOf_eq_bot_of_simple hsA fun hp => ?_
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [Nat.card_congr eA.toEquiv] at hn
      rcases hq with h3 | hU
      · rw [card_quot_of_sl_three h3] at hn
        have h8 : n < 8 :=
          (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [← hn]; norm_num)
        interval_cases n <;> norm_num at hn
      · rw [card_of_lieModel_psu_three_three hU] at hn
        have h13 : n < 13 :=
          (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [← hn]; norm_num)
        interval_cases n <;> norm_num at hn
    exact InternalSec.isPGroup_ker_of_simple hf.normalizes hs hO2 hf.notCent
  have key : ∀ U : Subgroup G, U ≤ V → U.relIndex V = 2 →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro U hUV hidx
    by_contra hUC
    by_cases hzU : z ∈ U
    · apply hUC
      rw [← hf.MN, hf.MC]
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzU)
    have hidx' : (U.subgroupOf V).index = 2 := hidx
    have hU1 : U ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.relIndex_bot_left] at hidx
      have hVZ : V ⊓ Subgroup.centralizer (L : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hf.card_zV, hidx]))
      apply hf.notCent
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [← hVZ] at hv
      exact (Subgroup.mem_centralizer_iff.1 hv.2 l hl).symm
    have hMU : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
      rintro m ⟨hmM, hmU⟩
      refine ⟨hmM, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      have hmz : m * z = z * m := by
        rw [hf.MC] at hmM
        exact Subgroup.mem_centralizer_singleton_iff.1 hmM
      by_cases hvU : v ∈ U
      · exact Subgroup.mem_centralizer_iff.1 hmU v hvU
      have hzu : z⁻¹ * v ∈ U := by
        have hz' : (⟨z, hzV⟩ : ↥V)⁻¹ ∉ U.subgroupOf V := fun h =>
          hzU (by simpa using Subgroup.mem_subgroupOf.1 h)
        have hv' : (⟨v, hv⟩ : ↥V) ∉ U.subgroupOf V := fun h => hvU (Subgroup.mem_subgroupOf.1 h)
        exact Subgroup.mem_subgroupOf.1
          ((Subgroup.mul_mem_iff_of_index_two hidx').2 (iff_of_false hz' hv'))
      have hcu := Subgroup.mem_centralizer_iff.1 hmU _ hzu
      calc v * m = z * ((z⁻¹ * v) * m) := by group
        _ = z * (m * (z⁻¹ * v)) := by rw [hcu]
        _ = (z * m) * (z⁻¹ * v) := by group
        _ = (m * z) * (z⁻¹ * v) := by rw [hmz]
        _ = m * v := by group
    have hres := (twoPrimeResidual_le_self _).trans hMU
    have hcharU := hchar G T L V hcx hq U hUV hidx hUC
    have hnotle : ¬ fixV (autOn L V) ≤ U.subgroupOf V := by
      intro h
      apply hzU
      have h1 : (⟨z, hzV⟩ : ↥V) ∈ fixV (autOn L V) := by
        rw [fixV_autOn_eq hf.normalizes]
        exact hf.mem_zV.2
      exact Subgroup.mem_subgroupOf.1 (h h1)
    obtain ⟨hmaxb, hidxb, Y, hYL, hY3, hYC⟩ : IsMaxSubgroupIn (autOn (L ⊔ T) V)
        (autOn (L ⊔ T) V ⊓ stabSub (U.subgroupOf V)) ∧
        (autOn (L ⊔ T) V ⊓ stabSub (U.subgroupOf V)).relIndex (autOn (L ⊔ T) V) ≠ 2 ∧
        ∃ Y : Subgroup (MulAut ↥V), Y ≤ autOn L V ⊓ stabSub (U.subgroupOf V) ∧
          Nat.card Y = 3 ∧ ¬ Y ≤ centSub (U.subgroupOf V) := by
      rcases hq with h3 | hU
      · obtain ⟨hV16, hGrs, hGr, hnat⟩ := cx_l3_module h1222 hcx hf h3
        obtain ⟨-, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
        have hX : autOn (L ⊔ T) V = autOn L V := by
          refine le_antisymm ?_ hLX
          unfold autOn
          rw [Subgroup.subgroupOf_sup hf.normalizes hf.T_le, Subgroup.map_sup]
          refine sup_le le_rfl ?_
          have h1 : autOn T V ≤ autOn L V := by
            rw [hTeq]
            exact A4.autOn_mono inf_le_right
          exact h1
        rw [hX]
        exact hL3 ↥V hW2 hV16 (autOn L V) hGrs hGr hcommV hfix (U.subgroupOf V) hidx' hnotle
      · obtain ⟨_, hcases⟩ := modules_cases_of_hyp1223 h1222 hyp
        have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
          rw [fixV_autOn_eq hf.normalizes]
          exact hcases.2.1 hU
        exact hG2 ↥V hW2 (autOn (L ⊔ T) V) (autOn L V) hLX hXN hX2 hcommV hfix hnat
          (U.subgroupOf V) hidx' hnotle
    have hmax := isMaxSubgroupIn_of_autOn hUV hLTV hmaxb
    have hidx2 : ((L ⊔ T) ⊓ Subgroup.normalizer (U : Set G)).relIndex (L ⊔ T) ≠ 2 := by
      rw [relIndex_inf_normalizer_eq hUV hLTV]
      exact hidxb
    have hY := exists_card_three_of_autOn hUV hker hYL hY3 hYC
    have hCM := h614 G T (Subgroup.normalizer (L : Set G)) V U (L ⊔ T) hE hU1 hUV hres hcharU
      (Or.inr hY) le_sup_right (sup_le_normalizer_of_cx h1222 h3228 hcx)
      (isUniqueM_sup_of_cx h331 hcx) hmax hidx2
    exact hUC (hCM.trans hf.MN.le)
  have h2 : (2 : ℕ∞) ≤ E3.rParam V := by
    unfold E3.rParam
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hUC⟩ := hU
    by_contra hlt
    have hk : E3.mQuot V U ≤ 1 := by
      push Not at hlt
      have : E3.mQuot V U < 2 := by exact_mod_cast hlt
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
    · exact hUC (((E3.mQuot_eq_zero_iff hV2 hUV).mp h0) ▸ Subgroup.centralizer_le_normalizer _)
    · exact hUC (key U hUV (by rw [E3.relIndex_eq_two_pow hV2, h1, pow_one]))
  exact lt_of_lt_of_le (by norm_num) h2

end CFSG.Quasithin.H13
