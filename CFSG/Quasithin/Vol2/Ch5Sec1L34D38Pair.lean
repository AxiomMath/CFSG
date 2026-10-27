module

public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB45
public import CFSG.Quasithin.Background.F918C12
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.SmithB51SL3Coord

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA

section Orders

variable {V : Type} [CommGroup V]

theorem three_dvd_card_statedSL_two_pow {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) : 3 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL_two K, ← Nat.card_eq_fintype_card, hK]
  apply Dvd.dvd.mul_left
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num
  have h1 : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 4 ^ a % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem three_dvd_card_of_binaryNaturalSL_two {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {a : ℕ} (h : BinaryNaturalSL L U Z 2 a) : 3 ∣ Nat.card ↥L := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  rw [card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ]
  exact three_dvd_card_statedSL_two_pow hK

theorem three_dvd_card_of_binaryNaturalSL_three {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : BinaryNaturalSL L U Z 3 1) : 3 ∣ Nat.card ↥L := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  rw [card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ]
  show 3 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K)
  rw [card_statedSL 3 K, card_SL_three_pow hK]
  norm_num

theorem three_dvd_card_of_binaryOrthogonalFour {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {a : ℕ} (h : BinaryOrthogonalFour L U Z a) : 3 ∣ Nat.card ↥L := by
  obtain ⟨K, hK, hKf, hchar, hc, π, hπ⟩ := h
  rw [card_eq_of_realizesVia_faithful_sec
    (CFSG.Quasithin.Vol2.Ch10.SecA.twistTensor_faithful (F := K) a) hπ]
  exact three_dvd_card_statedSL_two_pow hc

theorem three_dvd_card_of_alternatingNatural_five {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    [IsSimpleGroup ↥L] (h : AlternatingNatural L U Z 5) : 3 ∣ Nat.card ↥L := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 5) (by norm_num)) π hπ.1
  rw [← Nat.card_congr e.toEquiv, card_alt 5 (by norm_num)]
  decide

end Orders

section B45

variable {V : Type} [CommGroup V] [Finite V]

theorem suzukiModel_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : CFSG.Blueprint.SuzukiModel Y 2 n) : CFSG.Blueprint.SuzukiModel X 2 n := by
  obtain ⟨hp, a, ha, K, _, _, hn, hK, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, inferInstance, inferInstance, hn, hK, ⟨e.trans e'⟩⟩

theorem qhatOf_eq_two_of_table_sz {G L : Subgroup (MulAut V)}
    (hF : Facts10_1) (hB : B4Hyp G L) (ht : AsB45Table G L) [hs : IsSimpleGroup ↥L]
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel ↥L 2 n) :
    qhatOf G = ((2 : ℚ) : WithTop ℚ) := by
  have hsh : IsShapeGroup ↥L := Or.inr (Or.inl hsz)
  have h3 : ¬ 3 ∣ Nat.card ↥L := by
    obtain ⟨n, hn⟩ := hsz
    exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hn
  have hcard := shapeCard_of_isShapeGroup hsh
  have hnc := InternalSec.exists_noncomm_of_isQuasisimple hB.2.2.1
  have hnt : Nontrivial ↥L := hs.toNontrivial
  have card_false : ∀ {N : ℕ}, Nat.card ↥L = N → ¬ ShapeCard N → False :=
    fun hN hnot => hnot (hN ▸ hcard)
  rcases ht with ⟨⟨π, hR⟩, -⟩ | ⟨m, hm, horth, -⟩ | ⟨m, ⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨f, -, -, hq⟩ | ⟨m, hm, ⟨K, _, _, _, hK, π, hR⟩, -⟩ | ⟨⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨⟨eY, heY, hw, π, hR⟩, -⟩ | ⟨⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩, -⟩ |
      ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨h2324, -⟩
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π
      hR.1
    refine (card_false ?_ not_shapeCard_2520).elim
    rw [← Nat.card_congr e.toEquiv]
    rw [card_alt 7 (by norm_num)]
    decide
  · exact (h3 (three_dvd_card_of_binaryOrthogonalFour horth)).elim
  · exact absurd hR.1 (hF.su3 K m hK _ hsh π)
  · exact hq
  · exact absurd hR.1 (hF.nineTensor K m hm hK _ hsh π)
  · exact absurd hR.1 (hF.g2Derived K (by rw [hK]; norm_num) _ hsh π)
  · exact absurd hR.1 (hF.m12 eY heY hw _ hsh π)
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  · exact absurd hR.1 (hF.m22 x y hxy _ hsh π)
  · exact absurd hR.1 (hF.m22 x y hxy _ hsh π)
  · rcases h2324 with ⟨x, π, hR⟩ | ⟨x, π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩
    · exact absurd hR.1 (hF.m23 x _ hsh π)
    · exact absurd hR.1 (hF.m23 x _ hsh π)
    all_goals exact absurd hR.1 (hF.m24 _ hsh π)

theorem two_le_qhatOf_autSec_of_suzuki (hB45 : AsB45)
    (hF : Facts10_1) (hV : ∀ v : V, v ^ 2 = 1) {X K : Subgroup (MulAut V)} {C : Subgroup V}
    (hQ : InternalSec.QSec X K C) (hS : SQTKGroup ↥K) (hsimp : IsSimpleGroup ↥K)
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel ↥K 2 n) (hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSec X ⊤ C) := by
  have hb4 := hQ.b4Hyp hV hS
  have hsv : ∀ v : Sec (⊤ : Subgroup V) C, v ^ 2 = 1 := Bridge.sec_sq_eq_one hV ⊤ C
  have hqsec : qhatOf (autSec X ⊤ C) ≤ ((2 : ℚ) : WithTop ℚ) := (hQ.qhatOf_autSec_le hV).trans hq
  let e : ↥K ≃* ↥(autSec K ⊤ C) :=
    B5.secEquiv K (InternalSec.le_stabSub_top K) hQ.stabKC hQ.faithful
  have : IsSimpleGroup ↥(autSec K ⊤ C) := e.symm.isSimpleGroup
  have hsz' : ∃ n, CFSG.Blueprint.SuzukiModel ↥(autSec K ⊤ C) 2 n := by
    obtain ⟨n, hn⟩ := hsz
    exact ⟨n, suzukiModel_congr e.symm hn⟩
  have hsh : IsShapeGroup ↥(autSec K ⊤ C) := Or.inr (Or.inl hsz')
  have h3 : ¬ 3 ∣ Nat.card ↥(autSec K ⊤ C) := by
    obtain ⟨n, hn⟩ := hsz'
    exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hn
  rcases hB45 _ hsv _ _ hb4 hqsec with ⟨-, ⟨A, hA'⟩, hall⟩ | ⟨-, ht⟩ | h3'
  · exfalso
    rcases b42_of_isShapeGroup hF hsv hb4 hA' (hall A hA') hsh with ⟨m, -, hn⟩ | hn3 | halt
    · exact h3 (three_dvd_card_of_binaryNaturalSL_two hn)
    · exact h3 (three_dvd_card_of_binaryNaturalSL_three hn3)
    · exact h3 (three_dvd_card_of_alternatingNatural_five halt)
  · exact (qhatOf_eq_two_of_table_sz hF hb4 ht hsz').ge
  · exact (not_part3_of_isShapeGroup hF h3' hsh).elim

end B45

section CaseOne

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem two_le_qhatOf_autSub_of_suzuki_stab (hB45 : AsB45)
    (hA21 : AsA21SQTKSection) (hF : Facts10_1) (hD : D3Std M Mp T L V) (hMp : Mp = L)
    (hT : T ≤ stabSub V) (hLs : IsSimpleGroup ↥L)
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel ↥L 2 n) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSub (Mp ⊔ T) V) := by
  subst hMp
  have hLV : Mp ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQ := lred3_qsec hD.hyp rfl hO2
  have hS := lred3_sqtk hA21 hD.hyp rfl
  have hne : ¬ Mp ≤ centSub V := fun h => by
    obtain ⟨l, hl, v, hv, hlv⟩ := lred3_exists_ne hD.hyp rfl
    exact hlv (h hl v hv)
  have hfaith : Mp ⊓ centSub V = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hLs hLV hne
  let eK : ↥Mp ≃* ↥(autSub Mp V) := autSubEquivOfFaithful hLV hfaith
  have : IsSimpleGroup ↥(autSub Mp V) := eK.symm.isSimpleGroup
  have hszK : ∃ n, CFSG.Blueprint.SuzukiModel ↥(autSub Mp V) 2 n := by
    obtain ⟨n, hn⟩ := hsz
    exact ⟨n, suzukiModel_congr eK.symm hn⟩
  exact (two_le_qhatOf_autSec_of_suzuki hB45 hF hexp hQ hS this hszK
    (lred3_qhatOf_autSub hD hT)).trans (hQ.qhatOf_autSec_le hexp)

end CaseOne

section Bounds

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem ne_bot_of_commSub_ne_bot {B : Subgroup (MulAut W)} {V : Subgroup W}
    (hne : commSub V B ≠ ⊥) : B ≠ ⊥ := by
  rintro rfl
  apply hne
  rw [commSub_eq_bot_iff]
  intro v _ g hg
  rw [Subgroup.mem_bot.mp hg, MulAut.one_apply]

theorem two_mul_le_of_two_le_div {a b : ℕ} (hb : 0 < b) (h : (2 : ℚ) ≤ (a : ℚ) / (b : ℚ)) :
    2 * b ≤ a := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb'] at h
  exact_mod_cast h

theorem two_mul_rk_autSub_le {X B : Subgroup (MulAut W)} {V : Subgroup W}
    (h2 : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSub X V)) (hBX : B ≤ X) (hBV : B ≤ stabSub V)
    (hB : IsElemAbelian2 B) (hB3 : commSeries B 3 = ⊥) (hne : commSub V B ≠ ⊥) :
    2 * rk ↥(autSub B V) ≤ rk ↥V - rk ↥(V ⊓ fixV B) := by
  have hA2 : IsA2 X B := ⟨hBX, ne_bot_of_commSub_ne_bot hne, hB⟩
  have hA2' := hA2.autSub hBV hne
  have h := le_kq_iff.mp h2 _ hA2' (commSeries_autSub_eq_bot hBV hB3)
  have hpos := hA2'.isElemAbelian2.rk_pos hA2'.ne_bot
  have h1 := rk_add_rkIdx (fixV (autSub B V))
  rw [rk_fixV_autSub hBV] at h1
  have h3 := two_mul_le_of_two_le_div hpos h
  omega

omit [Finite W] in
theorem map_fixSec_autSub {B : Subgroup (MulAut W)} {V C' : Subgroup W} (hBV : B ≤ stabSub V) :
    (B5.fixSec (autSub B V) (⊤ : Subgroup ↥V) (C'.subgroupOf V)).map V.subtype =
      B5.fixSec B V C' := by
  ext w
  constructor
  · rintro ⟨u, ⟨-, hu⟩, rfl⟩
    refine ⟨u.2, fun b hb => ?_⟩
    have := hu (resHom V ⟨b, hBV hb⟩) (mem_autSub.mpr ⟨⟨b, hBV hb⟩, hb, rfl⟩)
    exact this
  · rintro ⟨hwV, hw⟩
    refine ⟨⟨w, hwV⟩, ⟨Subgroup.mem_top _, fun φ hφ => ?_⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    exact hw g hg

theorem two_mul_rk_autSub_le_sec {X B : Subgroup (MulAut W)} {V C' : Subgroup W}
    {K : Subgroup (MulAut ↥V)}
    (hQ : InternalSec.QSec (autSub X V) K (C'.subgroupOf V))
    (h2 : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSec (autSub X V) ⊤ (C'.subgroupOf V)))
    (hBX : B ≤ X) (hBV : B ≤ stabSub V) (hB : IsElemAbelian2 B) (hB3 : commSeries B 3 = ⊥)
    (hne : commSub V B ≠ ⊥) :
    2 * rk ↥(autSub B V) ≤ rk ↥V - rk ↥(B5.fixSec B V C') := by
  set C := C'.subgroupOf V with hC
  have hA2 : IsA2 X B := ⟨hBX, ne_bot_of_commSub_ne_bot hne, hB⟩
  have hA2' := hA2.autSub hBV hne
  have hB1X : autSub B V ≤ autSub X V := hA2'.1
  have hf := hQ.inf_centSec_eq_bot
  have hstab : autSub B V ≤ stabSub ⊤ ⊓ stabSub C := InternalSec.stab_of_le hQ.stab hB1X
  have hA2'' : IsA2 (autSec (autSub X V) ⊤ C) (autSec (autSub B V) ⊤ C) :=
    ⟨autSec_mono hB1X ⊤ C,
      CFSG.QuasithinUnique.Bridge.autSec_ne_bot hstab
        (InternalSec.not_le_centSec hf hB1X hA2'.ne_bot),
      CFSG.QuasithinUnique.Bridge.isElemAbelian2_autSec hA2'.isElemAbelian2 hstab⟩
  have hc := InternalSec.commSeries_autSec_eq_bot hstab (commSeries_autSub_eq_bot hBV hB3)
  have h := le_kq_iff.mp h2 _ hA2'' hc
  have hcard := InternalSec.card_autSec_eq hQ.stab hf hB1X
  have hrk : rk ↥(autSec (autSub B V) ⊤ C) = rk ↥(autSub B V) := by
    unfold rk; rw [hcard]
  have hpos := hA2''.isElemAbelian2.rk_pos hA2''.ne_bot
  rw [hrk] at hpos
  have h3 := two_mul_le_of_two_le_div hpos (by rw [← hrk]; exact h)
  have e1 := rk_add_rkIdx (fixV (autSec (autSub B V) ⊤ C))
  have e2 : rk (Sec (⊤ : Subgroup ↥V) C) + rk ↥C = rk ↥V := by
    have := card_sec_mul (V := ↥V) (W := ⊤) (U := C) le_top
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', this, Subgroup.card_top]
  have e3 : rk ↥(fixV (autSec (autSub B V) ⊤ C)) + rk ↥C =
      rk ↥(B5.fixSec (autSub B V) (⊤ : Subgroup ↥V) C) := by
    have := B5.card_fixV_autSec_mul (B := autSub B V) (W := ⊤) (U := C) le_top
      (fun x hx => (hstab hx).1) (fun x hx => (hstab hx).2)
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', this]
  have e4 : rk ↥(B5.fixSec (autSub B V) (⊤ : Subgroup ↥V) C) = rk ↥(B5.fixSec B V C') := by
    unfold rk
    rw [← map_fixSec_autSub hBV, Subgroup.card_map_of_injective V.subtype_injective]
  omega

end Bounds

section Pair

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem map_eq_of_mem_stabSub' {a : MulAut W} {V : Subgroup W} (h : a ∈ stabSub V) :
    V.map a.toMonoidHom = V := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (h v).2 hv
  · intro hw
    refine ⟨a.symm w, (h (a.symm w)).1 (by simpa using hw), by simp⟩

omit [Finite W] in
theorem mem_stabSub_of_map_eq' {a : MulAut W} {V : Subgroup W} (h : V.map a.toMonoidHom = V) :
    a ∈ stabSub V :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq h

theorem rk_top_add_rk_inf {V V' : Subgroup W} (hsum : V ⊔ V' = ⊤) :
    rk W + rk ↥(V ⊓ V') = rk ↥V + rk ↥V' := by
  have := rk_sup_add_rk_inf V V'
  rw [hsum, rk_top] at this
  exact this

theorem two_mul_rk_le_rkIdx_of_pair {V V' CV : Subgroup W} (hsum : V ⊔ V' = ⊤)
    (hD : V ⊓ V' ≤ CV) {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    (hperm : ∀ a ∈ A, (a ∈ stabSub V ∧ a ∈ stabSub V') ∨
      (V.map a.toMonoidHom = V' ∧ V'.map a.toMonoidHom = V))
    (hV2 : 2 + rk ↥CV ≤ rk ↥V)
    (hVB : ∀ B ≤ A, B ≤ stabSub V → commSub V B ≠ ⊥ →
      2 * rk ↥(autSub B V) ≤ rk ↥V - rk ↥(V ⊓ fixV B))
    (hVB' : ∀ B ≤ A, B ≤ stabSub V' → commSub V' B ≠ ⊥ →
      2 * rk ↥(autSub B V') ≤ rk ↥V' - rk ↥(V' ⊓ fixV B))
    (hSB : ∀ B ≤ A, B ≤ stabSub V → commSub V B ≠ ⊥ →
      2 * rk ↥(autSub B V) ≤ rk ↥V - rk ↥(B5.fixSec B V CV)) :
    2 * rk ↥A ≤ rkIdx (fixV A) := by
  have hidx := rk_add_rkIdx (fixV A)
  have htop := rk_top_add_rk_inf hsum
  have hdec : ∀ w : W, ∃ v ∈ V, ∃ v' ∈ V', v * v' = w := fun w =>
    Subgroup.mem_sup.mp (hsum ▸ Subgroup.mem_top w)
  have hcent : ∀ g : MulAut W, g ∈ centSub V → g ∈ centSub V' → g = 1 := by
    intro g hg hg'
    ext w
    obtain ⟨v, hv, v', hv', rfl⟩ := hdec w
    rw [map_mul, hg v hv, hg' v' hv', MulAut.one_apply]
  have hVB0 : ∀ B ≤ A, B ≤ stabSub V →
      2 * rk ↥(autSub B V) + rk ↥(V ⊓ fixV B) ≤ rk ↥V := by
    intro B hBA hBV
    by_cases hne : commSub V B = ⊥
    · rw [(autSub_eq_bot_iff hBV).mpr hne, rk_bot]
      have := rk_mono (inf_le_left : V ⊓ fixV B ≤ V)
      omega
    · have h1 := hVB B hBA hBV hne
      have := rk_mono (inf_le_left : V ⊓ fixV B ≤ V)
      omega
  have hVB0' : ∀ B ≤ A, B ≤ stabSub V' →
      2 * rk ↥(autSub B V') + rk ↥(V' ⊓ fixV B) ≤ rk ↥V' := by
    intro B hBA hBV
    by_cases hne : commSub V' B = ⊥
    · rw [(autSub_eq_bot_iff hBV).mpr hne, rk_bot]
      have := rk_mono (inf_le_left : V' ⊓ fixV B ≤ V')
      omega
    · have h1 := hVB' B hBA hBV hne
      have := rk_mono (inf_le_left : V' ⊓ fixV B ≤ V')
      omega
  have hrkAut : ∀ {B : Subgroup (MulAut W)} {Y : Subgroup W}, B ≤ stabSub Y →
      rk ↥(autSub B Y) + rk ↥(B ⊓ centSub Y) = rk ↥B := by
    intro B Y hBY
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_autSub_mul hBY]
  by_cases hst : ∀ a ∈ A, a ∈ stabSub V
  ·
    have hst' : ∀ a ∈ A, a ∈ stabSub V' := by
      intro a ha
      rcases hperm a ha with ⟨-, h⟩ | ⟨h1, -⟩
      · exact h
      · have hV : V.map a.toMonoidHom = V := map_eq_of_mem_stabSub' (hst a ha)
        rw [← h1, hV]
        exact hst a ha
    set B := A ⊓ centSub V with hB
    have hBA : B ≤ A := inf_le_left
    have hBV' : B ≤ stabSub V' := fun b hb => hst' b hb.1
    have hBf : B ⊓ centSub V' = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨⟨-, hg⟩, hg'⟩
      exact hcent g hg hg'
    have hY := rk_sup_add_rk_inf (fixV A) V
    have hW := rk_sup_add_rk_inf (fixV A ⊔ V) V'
    have hWtop : (fixV A ⊔ V) ⊔ V' = ⊤ := by
      rw [eq_top_iff, ← hsum]
      exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
    rw [hWtop, rk_top] at hW
    have hYV' : (fixV A ⊔ V) ⊓ V' ≤ V' ⊓ fixV B := by
      rintro y ⟨hy, hyV'⟩
      refine ⟨hyV', fun b hb => ?_⟩
      obtain ⟨f, hf, v, hv, rfl⟩ := Subgroup.mem_sup.mp hy
      rw [map_mul, hf b hb.1, hb.2 v hv]
    have h1 := rk_mono hYV'
    have hb1 := hVB0 A le_rfl hst
    have hb2 := hVB0' B hBA hBV'
    have hr1 := hrkAut (fun a ha => hst a ha : A ≤ stabSub V)
    have hr2 := hrkAut hBV'
    rw [hBf, rk_bot] at hr2
    rw [inf_comm (fixV A) V] at hY
    have hBdef : rk ↥(A ⊓ centSub V) = rk ↥B := rfl
    omega
  ·
    push Not at hst
    obtain ⟨a, haA, haV⟩ := hst
    obtain ⟨hVa, hV'a⟩ : V.map a.toMonoidHom = V' ∧ V'.map a.toMonoidHom = V := by
      rcases hperm a haA with ⟨h, -⟩ | h
      · exact absurd h haV
      · exact h
    set A₀ := A ⊓ stabSub V with hA₀
    have ha2 : a * a = 1 := by rw [← sq]; exact hA.2 a haA
    have hcomm : ∀ g ∈ A₀, g * a = a * g := fun g hg => hA.1 g hg.1 a haA
    have hstab : A₀ ≤ stabSub V := inf_le_right
    have hsum' : V ⊔ V.map a.toMonoidHom = ⊤ := by rw [hVa]; exact hsum
    have hswap := rk_fixV_swap_le ha2 hcomm hstab hsum'
    rw [hVa] at hswap
    have hfixA : fixV A ≤ fixV A₀ ⊓ fixV (Subgroup.zpowers a) :=
      le_inf (fixV_anti inf_le_left) (fixV_anti (Subgroup.zpowers_le.mpr haA))
    have hidx2 : (A₀.subgroupOf A).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨a, haA⟩, fun b => ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      by_cases hb : (b : MulAut W) ∈ stabSub V
      · have hbA₀ : (b : MulAut W) ∈ A₀ := ⟨b.2, hb⟩
        refine Or.inr ⟨hbA₀, fun hba => haV ?_⟩
        have := (stabSub V).mul_mem ((stabSub V).inv_mem hb) hba.2
        simpa using this
      · refine Or.inl ⟨⟨A.mul_mem b.2 haA, ?_⟩, fun hbA₀ => hb hbA₀.2⟩
        apply mem_stabSub_of_map_eq'
        have e : ((b : MulAut W) * a).toMonoidHom =
            (b : MulAut W).toMonoidHom.comp a.toMonoidHom := MonoidHom.ext fun x => rfl
        rw [e, ← Subgroup.map_map, hVa]
        rcases hperm b b.2 with ⟨h, -⟩ | ⟨-, hb2⟩
        · exact absurd h hb
        · exact hb2
    have hcardA : Nat.card ↥A = 2 * Nat.card ↥A₀ := by
      have h1 := (A₀.subgroupOf A).card_mul_index
      rw [hidx2] at h1
      have h2 : Nat.card ↥(A₀.subgroupOf A) = Nat.card ↥A₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [h2] at h1
      omega
    have hrkA : rk ↥A = rk ↥A₀ + 1 := by
      unfold rk
      rw [hcardA, padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_self, add_comm]
    have hA₀f : A₀ ⊓ centSub V = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨⟨hgA, hgs⟩, hgV⟩
      rw [Subgroup.mem_bot]
      refine hcent g hgV fun v' hv' => ?_
      have hv'a : a v' ∈ V := by
        rw [← hV'a]
        exact ⟨v', hv', rfl⟩
      have hga : g * a = a * g := hcomm g ⟨hgA, hgs⟩
      have h1 : g (a v') = a (g v') := by
        have := congrArg (fun φ : MulAut W => φ v') hga
        simpa [MulAut.mul_apply] using this
      have h2 : a (g v') = a v' := by rw [← h1, hgV _ hv'a]
      exact a.injective h2
    have hr := hrkAut hstab
    rw [hA₀f, rk_bot, add_zero] at hr
    have hUU : commModSub V A₀ (V ⊓ V') ≤ B5.fixSec A₀ V CV := fun u hu =>
      ⟨hu.1, fun g hg => hD (hu.2 g hg)⟩
    have h1 := rk_mono hUU
    have h2 := rk_mono hfixA
    have h3 : rk ↥((V ⊓ V') ⊓ fixV A₀) ≤ rk ↥(V ⊓ fixV A₀) :=
      rk_mono (inf_le_inf_right _ inf_le_left)
    have h4 : rk ↥(V ⊓ V') ≤ rk ↥CV := rk_mono hD
    have h5 : rk ↥V' = rk ↥V := by rw [← hVa, rk_map_aut_eq]
    have h6 : rk ↥(B5.fixSec A₀ V CV) ≤ rk ↥V := rk_mono (B5.fixSec_le _ _ _)
    have h7 : rk ↥(V ⊓ fixV A₀) ≤ rk ↥V := rk_mono inf_le_left
    have h9 : rk ↥((V ⊓ V') ⊓ fixV A₀) ≤ rk ↥(V ⊓ V') := rk_mono inf_le_left
    by_cases hne : commSub V A₀ = ⊥
    · have hA₀b : A₀ = ⊥ := by
        rw [eq_bot_iff, ← hA₀f]
        intro g hg
        exact ⟨hg, fun v hv => (commSub_eq_bot_iff.mp hne) hv g hg⟩
      have hrk0 : rk ↥A₀ = 0 := by rw [hA₀b, rk_bot]
      have h8 : rk ↥(commModSub V A₀ (V ⊓ V')) ≤ rk ↥V := rk_mono (commModSub_le _ _ _)
      omega
    · have hb1 := hVB A₀ inf_le_left hstab hne
      have hb2 := hSB A₀ inf_le_left hstab hne
      omega

end Pair

end CFSG.Quasithin.H13
