module

public import CFSG.Quasithin.EmptyFaithful.S1565M11
public import CFSG.Quasithin.Background.SmithB45SzNat
public import CFSG.Quasithin.H13.A6S13816h
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace SzSec

variable {W : Type} [CommGroup W]

theorem center_eq_bot_of_isSz {X : Type} [Group X] {n : ℕ}
    (h : IsSz n X) : Subgroup.center X = ⊥ := by
  have hs : IsSimpleGroup X := isSimpleGroup_of_psl2_or_sz (Or.inr h)
  have hn3 : 3 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := h
    omega
  have hperf : Group.IsPerfect X := (isQuasisimple_of_psl2_or_sz hn3 (Or.inr h)).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    have hc : commutator X = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hy : y ∈ Subgroup.center X := h1 ▸ Subgroup.mem_top y
      exact (Subgroup.mem_center_iff.mp hy x).symm
    have : (⊤ : Subgroup X) = ⊥ := (Group.isPerfect_def.mp hperf).symm.trans hc
    exact bot_ne_top this.symm

theorem nonempty_cq_equiv {G' : Type} [Group G']
    {X : Subgroup G'} {a : ℕ} {K : Type} [Field K] (e : ↥X ≃* CFSG.Blueprint.suzukiGroup a K)
    (h : Subgroup.center ↥X = ⊥) :
    Nonempty (Setup.Family.CQ X ≃* CFSG.Blueprint.suzukiGroup a K) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientBot.trans e)⟩

theorem inf_centSec_eq_bot {L : Subgroup (MulAut W)} {V C : Subgroup W} {n : ℕ}
    (hL : IsSz n ↥L) (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C)
    (hnt : ¬ L ≤ centSec V C) : L ⊓ centSec V C = ⊥ := by
  have hs : IsSimpleGroup ↥L := isSimpleGroup_of_psl2_or_sz (Or.inr hL)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B5.secHom L hLV hLC).ker with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hk : (⟨x, hx.1⟩ : ↥L) ∈ (B5.secHom L hLV hLC).ker :=
      (B5.mem_ker_secHom L hLV hLC _).mpr hx.2
    rw [h, Subgroup.mem_bot] at hk
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hk)
  · exfalso
    apply hnt
    intro x hx
    have hk : (⟨x, hx⟩ : ↥L) ∈ (B5.secHom L hLV hLC).ker := h ▸ Subgroup.mem_top _
    exact (B5.mem_ker_secHom L hLV hLC _).mp hk

theorem card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

theorem three_dvd_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h4 : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    norm_num
  have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

theorem three_dvd_card_of_natural_sl3 {L : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ}
    (h : BinaryNaturalSL L U Z 3 n) : 3 ∣ Nat.card ↥L := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hinj := SzMod.realizesVia_injective (FFModel.nat_faithful _) hπ
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
  rw [hcard, card_statedSL_three, hK]
  exact ((three_dvd_sq_sub_one n).mul_right _).mul_left _

theorem three_dvd_card_of_natural_sp4 {L : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ}
    (h : BinaryNaturalSp4 L U Z n) : 3 ∣ Nat.card ↥L := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hinj := SzMod.realizesVia_injective (FFModel.nat_faithful _) hπ
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
  rw [hcard, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num), hK]
  have h3 : 3 ∣ (2 ^ n) ^ (2 * 1) - 1 := by simpa using three_dvd_sq_sub_one n
  exact (h3.mul_right _).mul_left _

theorem not_d310Two_of_isSz [Finite W]
    {T L : Subgroup (MulAut W)} {V : Subgroup W} {n : ℕ} (hL : IsSz n ↥L) : ¬ D310Two T L V := by
  rintro ⟨hlist, -, -⟩
  have h3 := SzCase.not_three_dvd_of_isSz hL
  have hn3 : 3 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hL
    omega
  have : Finite ↥L := inferInstance
  rcases hlist with ⟨n', h⟩ | ⟨n', h⟩ | h
  · exact h3 (three_dvd_card_of_natural_sl3 h)
  · exact h3 (three_dvd_card_of_natural_sp4 h)
  · have hKs : Shape15365 n (⊤ : Subgroup ↥L) :=
      Or.inr (Or.inl (isSz_congr Subgroup.topEquiv.symm hL))
    let σ : ↥L →* ↥(⊤ : Subgroup ↥L) := (Subgroup.topEquiv (G := ↥L)).symm.toMonoidHom
    have hσ : Function.Surjective σ := fun y => ⟨Subgroup.topEquiv y, MulEquiv.symm_apply_apply _ y⟩
    refine not_d310_exceptional hn3 hKs σ hσ ?_ h
    intro x hx
    have hx1 : σ x = 1 := hx
    have : x = 1 := (Subgroup.topEquiv (G := ↥L)).symm.injective (by simpa [σ] using hx1)
    rw [this]
    exact Subgroup.one_mem _

theorem autSec_le_normalizer {L Y : Subgroup (MulAut W)} {V C : Subgroup W}
    (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C) (hYV : Y ≤ stabSub V) (hYC : Y ≤ stabSub C)
    (hYL : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    autSec Y V C ≤ Subgroup.normalizer ((autSec L V C : Subgroup (MulAut (Sec V C))) :
      Set (MulAut (Sec V C))) := by
  set X' : Subgroup (MulAut W) := stabSub V ⊓ stabSub C with hX'
  have hX'V : X' ≤ stabSub V := inf_le_left
  have hX'C : X' ≤ stabSub C := inf_le_right
  rw [← B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hYV hYC),
    ← B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hLV hLC)]
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp (hYL (Subgroup.mem_subgroupOf.mp hy)) (g : MulAut W)

theorem sec_data (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {V C : Subgroup W} {n : ℕ} (hL : IsSz n ↥L) (hCV : C < V)
    (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C)
    (hirr : ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → C ≤ J → J ≤ V → J = C ∨ J = V)
    (hfaith : L ⊓ centSec V C = ⊥) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ (2 * a + 1) ∧ Nontrivial (Sec V C) ∧ (∀ w : Sec V C, w * w = 1) ∧
      Group.IsPerfect ↥(autSec L V C) ∧
      (∀ U : Subgroup (Sec V C), (∀ g ∈ autSec L V C, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      Nonempty (Setup.Family.CQ (autSec L V C) ≃* CFSG.Blueprint.suzukiGroup a K) := by
  have hL' : IsSz n ↥(autSec L V C) := isSz_congr (B5.secEquiv L hLV hLC hfaith) hL
  have hn3 : 3 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hL
    omega
  have hperf : Group.IsPerfect ↥(autSec L V C) :=
    (isQuasisimple_of_psl2_or_sz hn3 (Or.inr hL')).1
  have hZ := center_eq_bot_of_isSz hL'
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨eS⟩⟩ := hL'
  refine ⟨a, ha, hf, K, inferInstance, inferInstance, hf ▸ hK, ?_, fun w => ?_, hperf,
    Bridge.TypeList.irr_of_isIrrSec (B5.isIrrSec_autSec hCV hirr hLV hLC),
    nonempty_cq_equiv eS hZ⟩
  · obtain ⟨v, hvV, hvC⟩ := IsConcreteLE.exists_of_lt hCV
    refine ⟨⟨QuotientGroup.mk (⟨v, hvV⟩ : ↥V), 1, fun h => hvC ?_⟩⟩
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  · rw [← sq]
    exact sq_eq_one_sec hW V C w

theorem binaryNaturalSz_of_offender
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)} {V C : Subgroup W} {n : ℕ}
    (hL : IsSz n ↥L) (hCV : C < V) (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C)
    (hirr : ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → C ≤ J → J ≤ V → J = C ∨ J = V)
    (hnt : ¬ L ≤ centSec V C) (hAV : A ≤ stabSub V) (hAC : A ≤ stabSub C)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A)
    (hAr : Nat.card W ≤ Nat.card A ^ 2 * Nat.card (fixV A))
    (hAf : ∀ a ∈ A, (∀ x ∈ L, a * x = x * a) → a = 1) : BinaryNaturalSz L V C n := by
  have hfaith := inf_centSec_eq_bot hL hLV hLC hnt
  obtain ⟨a, ha, hn, K, _, _, hK, hnts, hW', hperf, hirr', ⟨α⟩⟩ :=
    sec_data hW hL hCV hLV hLC hirr hfaith
  obtain ⟨-, hbij, hP, -, -⟩ := Setup.Family.suzuki_irreducible_normalizer_excludes a ha hK
    (Sec V C) hW' (autSec L V C) hperf hirr' α
  set X' : Subgroup (MulAut W) := stabSub V ⊓ stabSub C with hX'
  have hX'V : X' ≤ stabSub V := inf_le_left
  have hX'C : X' ≤ stabSub C := inf_le_right
  have hAX : A ≤ X' := le_inf hAV hAC
  have hLX : L ≤ X' := le_inf hLV hLC
  set f := B5.secHom X' hX'V hX'C with hf
  have hÂN := autSec_le_normalizer hLV hLC hAV hAC hAL
  have hsqÂ : ∀ y ∈ autSec A V C, y ^ 2 = 1 := by
    intro y hy
    rw [← B5.map_secHom_eq_autSec X' hX'V hX'C hAX] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [← map_pow]
    have : z ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hA2.2 _ (Subgroup.mem_subgroupOf.mp hz))
    rw [this, map_one]
  have hÂ2 : IsPGroup 2 ↥(autSec A V C) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hsqÂ _ x.2)⟩
  have hÂL : autSec A V C ≤ autSec L V C := hP _ hÂ2 hÂN
  have hAcent : A ⊓ centSec V C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    refine Subgroup.mem_bot.mpr (hAf x hx.1 fun l hl => ?_)
    have hxX : x ∈ X' := hAX hx.1
    have hlX : l ∈ X' := hLX hl
    have hc : x * l * x⁻¹ * l⁻¹ ∈ L ⊓ centSec V C := by
      refine ⟨L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAL hx.1) l).mp hl) (L.inv_mem hl), ?_⟩
      have hx1 : f ⟨x, hxX⟩ = 1 := (B5.mem_ker_secHom X' hX'V hX'C ⟨x, hxX⟩).mpr hx.2
      have hk : (⟨x, hxX⟩ * ⟨l, hlX⟩ * (⟨x, hxX⟩)⁻¹ * (⟨l, hlX⟩)⁻¹ : ↥X') ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hx1, one_mul, inv_one,
          mul_one, mul_inv_cancel]
      exact (B5.mem_ker_secHom X' hX'V hX'C _).mp hk
    rw [hfaith, Subgroup.mem_bot] at hc
    calc x * l = (x * l * x⁻¹ * l⁻¹) * (l * x) := by group
      _ = l * x := by rw [hc, one_mul]
  have hcardÂ : Nat.card ↥(autSec A V C) = Nat.card A := by
    have h := card_autSec_mul hAV hAC
    rw [hAcent, Subgroup.card_bot, mul_one] at h
    exact h
  let θ : ↥(autSec L V C) →* CFSG.Blueprint.suzukiGroup a K :=
    α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(autSec L V C)))
  have hθ : Function.Injective θ := hbij.1
  have hcardA : Nat.card A ≤ 2 ^ (2 * a + 1) := by
    have h1 := Setup.Family.suzuki_exponent_two_card_le hK
      (((autSec A V C).subgroupOf (autSec L V C)).map θ) (by
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul]
        have : x * x = 1 := Subtype.ext (by
          rw [Subgroup.coe_mul, ← sq]
          exact hsqÂ _ (Subgroup.mem_subgroupOf.mp hx))
        rw [this, map_one])
    rw [Subgroup.card_map_of_injective hθ] at h1
    have h2 : Nat.card ↥((autSec A V C).subgroupOf (autSec L V C)) =
        Nat.card ↥(autSec A V C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hÂL).toEquiv
    omega
  have hÂne : autSec A V C ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardÂ
    exact hA1 (Subgroup.eq_bot_of_card_eq A hcardÂ.symm)
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÂne
  have hsec : Nat.card (Sec V C) ≤ Nat.card A ^ 2 * Nat.card (fixV (autSec A V C)) := by
    have hn' : Nat.card V * Nat.card (fixV A) ≤ Nat.card W * Nat.card ↥(V ⊓ fixV A) := by
      rw [← card_mul_card_fixV_le A V]
      exact Nat.mul_le_mul_right _ (Subgroup.card_le_card_group _)
    exact (arith_section (card_sec_mul hCV.le) (card_inf_fixV_le_autSec hCV.le hAV)
      (Subgroup.card_le_of_le inf_le_left) hn' hAr Nat.card_pos Nat.card_pos).2.2
  have hidx : (fixV (Subgroup.zpowers (t : MulAut (Sec V C)))).index ≤
      2 ^ (2 * (2 * a + 1)) := by
    have h1 : (fixV (Subgroup.zpowers (t : MulAut (Sec V C)))).index ≤
        (fixV (autSec A V C)).index :=
      Subgroup.index_antitone (fun v hv y hy => hv y ((Subgroup.zpowers_le).mpr t.2 hy))
    have h2 := (fixV (autSec A V C)).card_mul_index
    have h3 : (fixV (autSec A V C)).index ≤ Nat.card A ^ 2 := by
      rw [← h2, mul_comm (Nat.card A ^ 2)] at hsec
      exact Nat.le_of_mul_le_mul_left hsec Nat.card_pos
    calc (fixV (Subgroup.zpowers (t : MulAut (Sec V C)))).index ≤ Nat.card A ^ 2 := h1.trans h3
      _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left hcardA 2
      _ = 2 ^ (2 * (2 * a + 1)) := by rw [← pow_mul, mul_comm]
  have hnat := szNaturalOfSmallDisplacement_holds a ha K hK (Sec V C) hW' (autSec L V C) hperf
    hirr' ⟨α⟩ ⟨(t : MulAut (Sec V C)), hÂL t.2, by rw [← sq]; exact hsqÂ _ t.2,
      fun h => ht1 (Subtype.ext h), hidx⟩
  obtain ⟨a', ha', hf', K', _, _, hK', π', hπ'⟩ := hnat
  subst hn
  exact ⟨a', ha', hf', K', inferInstance, inferInstance, hK', _,
    B5.realizesVia_of_autSec hCV.le hLV hLC hfaith hπ'⟩

theorem not_isFFModule [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L X : Subgroup (MulAut W)} {V C : Subgroup W} {n : ℕ}
    (hL : IsSz n ↥L) (hCV : C < V) (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C)
    (hirr : ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → C ≤ J → J ≤ V → J = C ∨ J = V)
    (hnt : ¬ L ≤ centSec V C) (hXV : X ≤ stabSub V) (hXC : X ≤ stabSub C)
    (hXL : X ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    ¬ IsFFModule (autSec (L ⊔ X) V C) := by
  rintro ⟨A, hA, hA1, hA2, hcard⟩
  have hfaith := inf_centSec_eq_bot hL hLV hLC hnt
  obtain ⟨a, ha, -, K, _, _, hK, hnts, hW', hperf, hirr', ⟨α⟩⟩ :=
    sec_data hW hL hCV hLV hLC hirr hfaith
  obtain ⟨-, -, -, -, h5⟩ := Setup.Family.suzuki_irreducible_normalizer_excludes a ha hK
    (Sec V C) hW' (autSec L V C) hperf hirr' α
  have hN := autSec_le_normalizer hLV hLC (sup_le hLV hXV) (sup_le hLC hXC)
    (sup_le Subgroup.le_normalizer hXL)
  exact absurd hcard (not_le.mpr (h5 A hA1 hA2 (hA.trans hN)))

theorem isFFModule_autSec_congr {X : Subgroup (MulAut W)} {V U U' : Subgroup W}
    (h : U.subgroupOf V = U'.subgroupOf V) (hFF : IsFFModule (autSec X V U)) :
    IsFFModule (autSec X V U') := by
  have key : ∀ S S' : Subgroup ↥V, S = S' → IsFFModule (autQuot (autSub X V) S) →
      IsFFModule (autQuot (autSub X V) S') := by
    rintro S S' rfl h
    exact h
  exact key _ _ h hFF

theorem mem_stabSub_fixed {M : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (htV : t ∈ stabSub V) (htN : t ∈ Subgroup.normalizer (M : Set (MulAut W))) :
    t ∈ stabSub (XMod.fixed ↥M V) := by
  intro w
  rw [XMod.mem_fixed, XMod.mem_fixed]
  constructor
  · rintro ⟨hw, hfix⟩
    refine ⟨(htV w).1 hw, fun a => ?_⟩
    have h1 := hfix ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN a).mp a.2⟩
    simp only [Subgroup.mk_smul, MulAut.smul_def, MulAut.mul_apply,
      MulAut.inv_apply_self] at h1
    rw [Subgroup.smul_def, MulAut.smul_def]
    exact t.injective h1
  · rintro ⟨hw, hfix⟩
    refine ⟨(htV w).2 hw, fun a => ?_⟩
    have ha : t⁻¹ * a * t ∈ M := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) a).mp a.2
      simpa using this
    have h1 := hfix ⟨t⁻¹ * a * t, ha⟩
    simp only [Subgroup.mk_smul, MulAut.smul_def, MulAut.mul_apply] at h1
    rw [Subgroup.smul_def, MulAut.smul_def]
    calc (a : MulAut W) (t w) = t (t⁻¹ ((a : MulAut W) (t w))) := by simp
      _ = t w := by rw [h1]

theorem mem_of_trivial_mod (hW : ∀ w : W, w ^ 2 = 1) {σ : MulAut W} (hσ3 : σ ^ 3 = 1)
    (hfpf : ∀ w : W, σ w = w → w = 1) {F : Subgroup W} (hσF : ∀ u ∈ F, σ u ∈ F)
    (hQ : ∀ w : W, σ w * w⁻¹ ∈ F) (w : W) : w ∈ F := by
  obtain ⟨g, hg⟩ : ∃ g, g = σ w * w⁻¹ := ⟨_, rfl⟩
  have hn : G64.norm3 σ w = 1 :=
    hfpf _ (G64.fixV_zpowers_iff.mp (G64.norm3_mem_fixV σ hσ3 w))
  rw [G64.norm3_apply] at hn
  have e1 : σ w = g * w := by rw [hg, inv_mul_cancel_right]
  have e2 : σ (σ w) = σ g * (g * w) := by rw [e1, map_mul, e1]
  rw [e2, e1] at hn
  have hw2 : w * w = 1 := by rw [← sq, hW]
  have hg2 : g * g = 1 := by rw [← sq, hW]
  have e3 : w * (g * w) * (σ g * (g * w)) = (w * w) * (g * g) * (w * σ g) := by ac_rfl
  rw [e3, hw2, hg2, one_mul, one_mul] at hn
  rw [eq_inv_of_mul_eq_one_left hn]
  exact F.inv_mem (hσF g (hg ▸ hQ w))

theorem map_mem_orbSup {T : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W} (ht : t ∈ T)
    {w : W} (hw : w ∈ orbSup T V) : t w ∈ orbSup T V := by
  have h : orbSup T V ≤ (orbSup T V).comap t.toMonoidHom := by
    refine iSup₂_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    show t (s v) ∈ orbSup T V
    have e : t (s v) = (t * s) v := rfl
    rw [e]
    exact (le_iSup₂ (f := fun r (_ : r ∈ T) => V.map r.toMonoidHom) (t * s) (T.mul_mem ht hs))
      ⟨v, hv, rfl⟩
  exact h hw

end SzSec

end CFSG.Quasithin.H13.A6
