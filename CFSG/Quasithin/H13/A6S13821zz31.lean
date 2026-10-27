module

public import CFSG.Quasithin.H13.L32AC44f
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.H13.A6S13821zz23
public import CFSG.Quasithin.H13.A6S13821zz28
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank

attribute [local instance] commGroupOfFact

namespace A6S20

section Module

variable {W : Type} [CommGroup W]

theorem sl3_eq_sl34 {n : ℕ}
    (h : (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) = 60480) : n = 2 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> first | rfl | (exfalso; norm_num at h)
  · exfalso
    have h1 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : (2 ^ 3) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ 3) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h1 3
    have h4 : (2 ^ 3) ^ 3 * (((2 ^ 3) ^ 2 - 1) * ((2 ^ 3) ^ 3 - 1)) ≤
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h3 1))
    norm_num at h4
    omega

theorem sp4_ne_sl34 (n : ℕ) :
    (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ≠ 60480 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have h1 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : (2 ^ 3) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ 3) ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left h1 4
    have h4 : (2 ^ 3) ^ 4 * (((2 ^ 3) ^ 2 - 1) * ((2 ^ 3) ^ 4 - 1)) ≤
        (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h3 1))
    norm_num at h4
    omega

theorem natural_sl34_of_d310Two {L : Subgroup (MulAut W)} {U C : Subgroup W}
    (hc : Nat.card ↥L = 60480)
    (h : (∃ n, BinaryNaturalSL L U C 3 n) ∨ (∃ n, BinaryNaturalSp4 L U C n) ∨
      AlternatingNatural L U C 6 ∨ BinaryNaturalSL L U C 4 1 ∨ BinaryNaturalSL L U C 5 1 ∨
      A7Four L U C) : BinaryNaturalSL L U C 3 2 := by
  rcases h with ⟨n, hn⟩ | ⟨n, K, _, _, hKc, hR⟩ | ⟨π, hπ⟩ | ⟨K, _, _, hKc, hR⟩ |
      ⟨K, _, _, hKc, hR⟩ | ⟨α, π, hπ⟩
  · obtain ⟨K, _, _, hKc, hR⟩ := hn
    have hc' := hc
    rw [card_eq_of_nat hR, A5.card_statedSL_three, hKc] at hc'
    obtain rfl := sl3_eq_sl34 hc'
    exact ⟨K, inferInstance, inferInstance, hKc, hR⟩
  · exfalso
    rw [card_eq_of_nat hR, A5.card_statedSp_two, hKc] at hc
    exact sp4_ne_sl34 n hc
  · exfalso
    have h1 := A5.card_le_of_surjective (Γ := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [Ch1Four.card_alt6 ⟨MulEquiv.refl _⟩] at h1
    omega
  · exfalso
    have h2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 K) = 20160 := by
      rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv,
        CFSG.OrderReductions.LinearOrders.card_specialLinear K 4 (by norm_num), hKc]
      decide
    rw [card_eq_of_nat hR, h2] at hc
    omega
  · exfalso
    rw [card_eq_of_nat hR, A5.card_statedSL_five_two (by rw [hKc]; norm_num)] at hc
    omega
  · exfalso
    have h1 := A5.card_le_of_surjective (Γ := ↥(alternatingGroup (Fin 7))) π hπ.1
    rw [Ch1Four.card_alt7 ⟨MulEquiv.refl _⟩] at h1
    omega

theorem fpf_of_isSumMod {z : MulAut W} {A B C : Subgroup W} (hsum : IsSumMod C A B ⊤)
    (hzC : ∀ c ∈ C, z c = c) (hzA : ∀ a ∈ A, z a ∈ A) (hzB : ∀ b ∈ B, z b ∈ B)
    (hA : ∀ a ∈ A, z a * a⁻¹ ∈ C → a ∈ C) (hB : ∀ b ∈ B, z b * b⁻¹ ∈ C → b ∈ C) :
    ∀ w : W, z w * w⁻¹ ∈ C → w ∈ C := by
  intro w hw
  have hw' : w ∈ A ⊔ B ⊔ C := by rw [← hsum.1]; exact Subgroup.mem_top w
  obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy
  have hza : z a * a⁻¹ ∈ A := A.mul_mem (hzA a ha) (A.inv_mem ha)
  have hzb : z b * b⁻¹ ∈ B := B.mul_mem (hzB b hb) (B.inv_mem hb)
  have e1 : z (a * b * c) * (a * b * c)⁻¹ = (z a * a⁻¹) * (z b * b⁻¹) := by
    rw [map_mul, map_mul, hzC c hc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e1] at hw
  have hAC : z a * a⁻¹ ∈ C := by
    apply hsum.2
    refine ⟨Subgroup.mem_sup_left hza, ?_⟩
    have e2 : z a * a⁻¹ = (z a * a⁻¹ * (z b * b⁻¹)) * (z b * b⁻¹)⁻¹ := by group
    rw [e2]
    exact (B ⊔ C).mul_mem (Subgroup.mem_sup_right hw)
      ((B ⊔ C).inv_mem (Subgroup.mem_sup_left hzb))
  have hBC : z b * b⁻¹ ∈ C := by
    have e3 : z b * b⁻¹ = (z a * a⁻¹)⁻¹ * (z a * a⁻¹ * (z b * b⁻¹)) := by group
    rw [e3]
    exact C.mul_mem (C.inv_mem hAC) hw
  exact C.mul_mem (C.mul_mem (hA a ha hAC) (hB b hb hBC)) hc

theorem commV_eq_top_of_d31 [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D31 M Mp T L V) (hMp : Mp = L) : commV L = ⊤ := by
  rw [eq_top_iff, ← hD.gen]
  refine iSup₂_le fun m hm => ?_
  have hc : XMod.commOf ↥Mp V = V := hD.irr.2.2.1
  rw [← hc, XMod.commOf, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨c, ⟨a, v, -, rfl⟩, rfl⟩
  have hmN := hD.Mp_normal hm
  have hma : m * (a : MulAut W) * m⁻¹ ∈ L := by
    rw [← hMp]
    exact (Subgroup.mem_normalizer_iff.mp hmN _).mp a.2
  refine Subgroup.subset_closure ⟨_, hma, m v, ?_⟩
  change (m * (a : MulAut W) * m⁻¹) (m v) * (m v)⁻¹ = m ((a : MulAut W) v * v⁻¹)
  rw [map_mul, map_inv]
  simp [MulAut.mul_apply]

theorem secIsoL_of_isoMod {L : Subgroup (MulAut W)} {V V' : Subgroup W}
    (hV : ∀ l ∈ L, ∀ v ∈ V, l v ∈ V) (hV' : ∀ l ∈ L, ∀ v ∈ V', l v ∈ V')
    (h : H.Pair.IsoMod L V V') : SecIsoL L V ⊥ V' ⊥ := by
  obtain ⟨e, he⟩ := h
  set q := QuotientGroup.mk' ((⊥ : Subgroup W).subgroupOf V') with hq
  have hqi : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', Subgroup.bot_subgroupOf]
  refine ⟨Function.surjective_id, bot_le, bot_le, fun l u hu => hV l l.2 u hu, fun l z hz => ?_,
    fun (l : ↥L) m hm => hV' l l.2 m hm, fun (l : ↥L) m hm => ?_, q.comp e.toMonoidHom,
    (QuotientGroup.mk'_surjective _).comp e.surjective, fun u => ?_,
    fun (l : ↥L) (u : ↥V) (m : ↥V') hu hm hum => ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hm' : (m : W) = 1 := Subgroup.mem_bot.mp (show (m : W) ∈ (⊥ : Subgroup W) from hm)
    show ((l : ↥L) : MulAut W) (m : W) ∈ (⊥ : Subgroup W)
    rw [Subgroup.mem_bot, hm']
    exact map_one _
  · change q (e u) = 1 ↔ (u : W) ∈ (⊥ : Subgroup W)
    rw [Subgroup.mem_bot, ← map_one q, hqi.eq_iff, ← map_one e, e.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · change q (e u) = q m at hum
    have h1 : e u = m := hqi hum
    show q (e ⟨_, hu⟩) = q ⟨_, hm⟩
    congr 1
    apply Subtype.ext
    show ((e ⟨((l : ↥L) : MulAut W) u, hu⟩ : ↥V') : W) = ((l : ↥L) : MulAut W) (m : W)
    rw [he l l.2 u hu, h1]

theorem card_ne_of_nineTensor {L : Subgroup (MulAut W)} (h : BinaryNineTensor L ⊤ ⊥ 1) :
    Nat.card ↥L ≠ 60480 := by
  classical
  obtain ⟨K, _, _, _, hK, π, hπ⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root (F := K) (by rw [hK4])
  obtain ⟨f, -, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl hπ
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈
      {A : GL (Fin 3) K | (A : Matrix (Fin 3) (Fin 3) K).det = 1} := by
    show ((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_const, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  set γ₀ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) := ⟨_, Subgroup.subset_closure hmem⟩
    with hγ₀
  have hM : ((γ₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (ω : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hγ₀, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hfrob : frobPow 1 ((ω : K) • (1 : Matrix (Fin 3) (Fin 3) K)) =
      ((ω : K) ^ 2 ^ 1) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [frobPow]
    · simp [frobPow, hij]
  have hω2 : (ω : K) ^ 2 ^ 1 * ω = 1 := by
    rw [pow_one, ← pow_succ, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hact : ∀ m : Multiplicative (Matrix (Fin 3) (Fin 3) K),
      twistAct 1 (CFSG.Assembly.LowTwoRank.StatedSL 3 K) γ₀ m = m := by
    intro m
    unfold twistAct
    rw [hM, hfrob, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, one_mul,
      Matrix.mul_smul, mul_one, smul_smul, hω2, one_smul, ofAdd_toAdd]
  have hπγ : π γ₀ = 1 := by
    apply Subtype.ext
    refine MulEquiv.ext fun v => ?_
    have hv : ((π γ₀ : ↥L) : MulAut W) v ∈ (⊤ : Subgroup W) := trivial
    have h1 := hfe γ₀ ⟨v, trivial⟩ hv
    have h2 : f ⟨((π γ₀ : ↥L) : MulAut W) v, hv⟩ = f ⟨v, trivial⟩ :=
      Subtype.ext (h1.trans (hact _))
    have h3 : f (⟨((π γ₀ : ↥L) : MulAut W) v, hv⟩ *
        (⟨v, trivial⟩ : ↥(⊤ : Subgroup W))⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (hfk _).mp h3
    rw [Subgroup.mem_bot] at h4
    have h5 : ((π γ₀ : ↥L) : MulAut W) v * v⁻¹ = 1 := h4
    rw [mul_inv_eq_one] at h5
    exact h5
  have hγ1 : γ₀ ≠ 1 := by
    intro h1
    apply hω1
    have h2 := congrArg (fun g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [hM, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      OneMemClass.coe_one, Units.val_one] at h2
    exact Units.ext h2
  have hγ3 : γ₀ ^ 3 = 1 := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.scalar (Fin 3) ω) ^ 3 = 1
    rw [← map_pow, hω3, map_one]
  have hker3 : 3 ∣ Nat.card ↥π.ker := by
    have hle : Subgroup.zpowers γ₀ ≤ π.ker := (Subgroup.zpowers_le).mpr hπγ
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, orderOf_eq_prime hγ3 hγ1] at h1
  have hcSL : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) = 60480 := by
    rw [A5.card_statedSL_three, hK4]
    norm_num
  have hcard : Nat.card (FFModel.twistTensor 1 (CFSG.Assembly.LowTwoRank.StatedSL 3 K)).Gam =
      Nat.card ↥L * Nat.card ↥π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ.1).toEquiv]
  have hcSL' : Nat.card (FFModel.twistTensor 1 (CFSG.Assembly.LowTwoRank.StatedSL 3 K)).Gam =
      60480 := hcSL
  intro hL
  rw [hcSL', hL] at hcard
  obtain ⟨k, hk⟩ := hker3
  rw [hk] at hcard
  omega

omit [CommGroup W] in
open CFSG.QuasithinUnique.Bridge in
theorem natural_sl34_of_d3Std
    {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hA21 : AsA21SQTKSection) (hD : D3Std M Mp T L V) (hMp : Mp = L) (hT : T ≤ stabSub V)
    (hfaith : L ⊓ centSub V = ⊥) (hc : Nat.card ↥L = 60480)
    (hL34 : IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L)) : BinaryNaturalSL L V (V ⊓ fixV L) 3 2 := by
  subst hMp
  have hLs : Mp ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQ := lred3_qsec hD.hyp rfl hO2
  have hb4 := lred3_b4Hyp hA21 hD.hyp rfl hO2
  have hqhat := lred3_qhatOf_autSec hD rfl hT
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
    sec_sq_eq_one hexp ⊤ _
  let eL : ↥Mp ≃* ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
    (autSubEquivOfFaithful hLs hfaith).trans
      (B5.secEquiv (autSub Mp V) (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful)
  have hLZ : Mp ≤ stabSub (V ⊓ fixV Mp) :=
    le_stabSub_of_le_fixV (inf_le_right.trans (fixV_anti le_rfl))
  have hmodel := IsPSL.of_mulEquiv (QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)) hL34
  rcases L32A.C.natural_or_nine hsv hb4 le_rfl hmodel hqhat with h | ⟨m, -, hm2, h⟩
  · exact binaryNaturalSL_of_autSub hLs hLZ inf_le_left hfaith
      (InternalSec.binaryNaturalSL_of_autSec hQ.stabKC hQ.faithful h)
  · obtain rfl : m = 1 := by omega
    exact absurd ((Nat.card_congr eL.toEquiv).symm.trans hc) (card_ne_of_nineTensor h)

theorem eq_of_card_center_three {Y : Type*} [Group Y] [Finite Y]
    (hZ : Nat.card (Subgroup.center Y) = 3) {z : Y} (hz : z ∈ Subgroup.center Y) (hz1 : z ≠ 1)
    {y : Y} (hy : y ∈ Subgroup.center Y) : y = 1 ∨ y = z ∨ y = z⁻¹ := by
  have hle : Subgroup.zpowers z ≤ Subgroup.center Y := (Subgroup.zpowers_le).mpr hz
  have hord : orderOf z = 3 := by
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hZ] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have heq : Subgroup.zpowers z = Subgroup.center Y :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hZ])
  rw [← heq] at hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk := zpow_mod_orderOf z k
  rw [hord] at hk
  rw [← hk]
  have h0 : 0 ≤ k % (3 : ℕ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % (3 : ℕ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hz3 : z ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one z
  interval_cases h : k % (3 : ℕ)
  · left
    exact zpow_zero z
  · right; left
    exact zpow_one z
  · right; right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = (3 : ℕ) by norm_num,
      zpow_natCast, hz3]

end Module

end A6S20

end CFSG.Quasithin.H13.A6
