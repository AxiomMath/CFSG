module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmE
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNK
public import CFSG.Quasithin.Background.E6Nine
public import CFSG.Quasithin.EmptyFaithful.T1515cB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Nb

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_quot {X N : Subgroup G} (hNX : X ≤ Subgroup.normalizer (N : Set G))
    (hN2 : IsPGroup 2 ↥N) (hNX' : N ≤ X) {x y z : G} (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
    (hx3 : orderOf x = 3) (hy3 : orderOf y = 3) (hz3 : orderOf z = 3) (hxy : x * y = y * x)
    (hxz : z * x * z⁻¹ * x⁻¹ ∈ N) (hyz : z * y * z⁻¹ * y⁻¹ ∈ N)
    (hind : ∀ a b c : ℤ, x ^ a * y ^ b * z ^ c ∈ N → x ^ a = 1 ∧ y ^ b = 1 ∧ z ^ c = 1) :
    3 ≤ CFSG.Open.pRank 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N' := N.subgroupOf X with hN'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX').mpr hNX
  set q := QuotientGroup.mk' N' with hq
  have hcomm : ∀ {u w : G} (hu : u ∈ X) (hw : w ∈ X), w * u * w⁻¹ * u⁻¹ ∈ N →
      Commute (q ⟨u, hu⟩) (q ⟨w, hw⟩) := by
    intro u w hu hw h
    show q ⟨u, hu⟩ * q ⟨w, hw⟩ = q ⟨w, hw⟩ * q ⟨u, hu⟩
    rw [← map_mul, ← map_mul, hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (w * u)⁻¹ * (w * u * w⁻¹ * u⁻¹) * (w * u)⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hNX (X.mul_mem hw hu))) _).mp h
    have e : (((⟨u, hu⟩ * ⟨w, hw⟩ : ↥X)⁻¹ * (⟨w, hw⟩ * ⟨u, hu⟩) : ↥X) : G) =
        (w * u)⁻¹ * (w * u * w⁻¹ * u⁻¹) * (w * u)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact h1
  have hxy' : Commute (q ⟨x, hx⟩) (q ⟨y, hy⟩) := by
    show q ⟨x, hx⟩ * q ⟨y, hy⟩ = q ⟨y, hy⟩ * q ⟨x, hx⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxy
  have hxz' := hcomm hx hz hxz
  have hyz' := hcomm hy hz hyz
  have hrep : ∀ {g : G} (hg : g ∈ X) (a : ↥(Subgroup.zpowers g)), ∃ i : ℤ,
      (a : G) = g ^ i ∧ q (Subgroup.inclusion (Subgroup.zpowers_le.mpr hg) a) = q ⟨g, hg⟩ ^ i := by
    intro g hg a
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    refine ⟨i, hi.symm, ?_⟩
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    simp [hi]
  set ix : ↥(Subgroup.zpowers x) →* ↥X ⧸ N' :=
    q.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hx)) with hix
  set iy : ↥(Subgroup.zpowers y) →* ↥X ⧸ N' :=
    q.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hy)) with hiy
  set iz : ↥(Subgroup.zpowers z) →* ↥X ⧸ N' :=
    q.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hz)) with hiz
  have hc1 : ∀ a b, Commute (ix a) (iy b) := by
    intro a b
    obtain ⟨i, -, hi⟩ := hrep hx a
    obtain ⟨j, -, hj⟩ := hrep hy b
    show Commute (q (Subgroup.inclusion _ a)) (q (Subgroup.inclusion _ b))
    rw [hi, hj]
    exact hxy'.zpow_zpow i j
  set ixy := ix.noncommCoprod iy hc1 with hixy
  have hc2 : ∀ p c, Commute (ixy p) (iz c) := by
    rintro ⟨a, b⟩ c
    obtain ⟨i, -, hi⟩ := hrep hx a
    obtain ⟨j, -, hj⟩ := hrep hy b
    obtain ⟨k, -, hk⟩ := hrep hz c
    show Commute (q (Subgroup.inclusion _ a) * q (Subgroup.inclusion _ b))
      (q (Subgroup.inclusion _ c))
    rw [hi, hj, hk]
    exact (hxz'.zpow_zpow i k).mul_left (hyz'.zpow_zpow j k)
  set F := ixy.noncommCoprod iz hc2 with hF
  have hFi : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, c⟩ h1
    obtain ⟨i, hai, hi⟩ := hrep hx a
    obtain ⟨j, hbj, hj⟩ := hrep hy b
    obtain ⟨k, hck, hk⟩ := hrep hz c
    have h2 : q ⟨x, hx⟩ ^ i * q ⟨y, hy⟩ ^ j * q ⟨z, hz⟩ ^ k = 1 := by
      rw [← hi, ← hj, ← hk]
      exact h1
    have hmem : x ^ i * y ^ j * z ^ k ∈ N := by
      rw [← map_zpow, ← map_zpow, ← map_zpow, ← map_mul, ← map_mul, hq,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
      simpa using h2
    obtain ⟨h3, h4, h5⟩ := hind i j k hmem
    refine Prod.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)) (Subtype.ext ?_)
    · rw [hai, h3]
      rfl
    · rw [hbj, h4]
      rfl
    · rw [hck, h5]
      rfl
  have hcz : ∀ {g : G}, orderOf g = 3 → Nat.card ↥(Subgroup.zpowers g) = 3 := fun h => by
    rw [Nat.card_zpowers, h]
  have h3 := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    (A := (↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y)) × ↥(Subgroup.zpowers z)) (k := 3)
    (fun u w => by
      obtain ⟨⟨a, b⟩, c⟩ := u
      obtain ⟨⟨a', b'⟩, c'⟩ := w
      obtain ⟨i, hai, -⟩ := hrep hx a
      obtain ⟨i', hai', -⟩ := hrep hx a'
      obtain ⟨j, hbj, -⟩ := hrep hy b
      obtain ⟨j', hbj', -⟩ := hrep hy b'
      obtain ⟨k, hck, -⟩ := hrep hz c
      obtain ⟨k', hck', -⟩ := hrep hz c'
      refine Prod.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)) (Subtype.ext ?_)
      · show (a : G) * a' = a' * a
        rw [hai, hai']
        exact (Commute.zpow_zpow_self x i i').eq
      · show (b : G) * b' = b' * b
        rw [hbj, hbj']
        exact (Commute.zpow_zpow_self y j j').eq
      · show (c : G) * c' = c' * c
        rw [hck, hck']
        exact (Commute.zpow_zpow_self z k k').eq)
    (fun u => by
      obtain ⟨⟨a, b⟩, c⟩ := u
      obtain ⟨i, hai, -⟩ := hrep hx a
      obtain ⟨j, hbj, -⟩ := hrep hy b
      obtain ⟨k, hck, -⟩ := hrep hz c
      have hp : ∀ {g : G} (hg3 : orderOf g = 3) (l : ℤ), (g ^ l) ^ 3 = 1 := fun hg3 l => by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg3,
          pow_orderOf_eq_one, one_zpow]
      refine Prod.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)) (Subtype.ext ?_)
      · show (a : G) ^ 3 = 1
        rw [hai]
        exact hp hx3 i
      · show (b : G) ^ 3 = 1
        rw [hbj]
        exact hp hy3 j
      · show (c : G) ^ 3 = 1
        rw [hck]
        exact hp hz3 k)
    (by rw [Nat.card_prod, Nat.card_prod, hcz hx3, hcz hy3, hcz hz3]; norm_num) F hFi
    (H := ⊤) le_top
  have hN3 : ¬ 3 ∣ Nat.card ↥N' := by
    have hN'2 : IsPGroup 2 ↥N' := hN2.comap_subtype
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e, he⟩ := hN'2.exists_card_eq
    rw [he]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq N' hN3] at h3
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact h3

omit [Finite G] in
theorem exists_orderOf_three_SL2 (F : Type) [Field F] [CharP F 2] :
    ∃ ω : Matrix.SpecialLinearGroup (Fin 2) F, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero F 2
  have hdet : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have : (-1 : F) = 1 := by rw [neg_eq_iff_add_eq_zero, h2]
    simpa using this
  have hM : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]
  set ω : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; 1, 1], hdet⟩ with hω
  have h3 : ω ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact hM
  have h1 : ω ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [hω] at this
  exact ⟨ω, orderOf_eq_prime h3 h1⟩

theorem exists_orderOf_three_of_isChi0Block {X B : Subgroup G} (hB : IsChi0Block X B) :
    ∃ x ∈ B, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card ↥B := by
    rcases hB.2 with ⟨k, -, F, _, _, hF, α, hα, -⟩ | ⟨α, hα, -⟩ | ⟨α, hα, -⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : CharP F 2 := charP_of_card_eq_prime_pow hF
      obtain ⟨ω, hω⟩ := exists_orderOf_three_SL2 F
      obtain ⟨b, rfl⟩ := hα ω
      rw [← hω]
      exact (orderOf_map_dvd α b).trans (orderOf_dvd_natCard b)
    · refine dvd_trans ?_ (Subgroup.card_dvd_of_surjective (f := α) hα)
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    · refine dvd_trans ?_ (Subgroup.card_dvd_of_surjective (f := α) hα)
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end Sec1211Nb

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

theorem exists_two_pow_of_mem_centralizerSection (F : Frame S m) (hm : 3 ≤ m) {H : Subgroup G}
    {l : G} (hl : l ∈ Sec1216Lv.lv L (a₀ * c₀))
    (hlY : l ∈ centralizerSection H (Sec1216Lv.lv L (a₀ * c₀))
      (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))) : ∃ e : ℕ, l ^ 2 ^ e = 1 := by
  set ψ := psi F S.lv_le_Xv with hψ
  have hc : ψ ⟨l, hl⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l', rfl⟩ := psi_lv_surjective F g
    have h1 := hlY.2.2.2 (l' : G) l'.2
    have hmem : (l' : G) * l * (l' : G)⁻¹ * l⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) :=
      (Sec1216Lv.lv L (a₀ * c₀)).mul_mem ((Sec1216Lv.lv L (a₀ * c₀)).mul_mem
        ((Sec1216Lv.lv L (a₀ * c₀)).mul_mem l'.2 hl) ((Sec1216Lv.lv L (a₀ * c₀)).inv_mem l'.2))
        ((Sec1216Lv.lv L (a₀ * c₀)).inv_mem hl)
    have h2 := mem_ker_psi_of_mem_pCoreOf F hm h1 hmem
    have e : (⟨(l' : G) * l * (l' : G)⁻¹ * l⁻¹, hmem⟩ : ↥(Sec1216Lv.lv L (a₀ * c₀))) =
        l' * ⟨l, hl⟩ * l'⁻¹ * (⟨l, hl⟩ : ↥(Sec1216Lv.lv L (a₀ * c₀)))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc ψ l' * ψ ⟨l, hl⟩ = (ψ l' * ψ ⟨l, hl⟩ * (ψ l')⁻¹ * (ψ ⟨l, hl⟩)⁻¹) *
          (ψ ⟨l, hl⟩ * ψ l') := by group
      _ = ψ ⟨l, hl⟩ * ψ l' := by rw [h2, one_mul]
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
  obtain ⟨r, hr, hrl⟩ := hc
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hr1 : r = 1 := by
    rcases hcases r with h0 | h1
    · rw [h0, zero_pow (by simp; omega)] at hr
      exact absurd hr zero_ne_one
    · exact h1
  rw [hr1, map_one] at hrl
  have hψ1 : ψ ⟨l, hl⟩ = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one]; exact hrl.symm)
  obtain ⟨e, he⟩ := isPGroup_ker_psi_lv F ⟨⟨l, hl⟩, hψ1⟩
  refine ⟨e, ?_⟩
  have h3 := congrArg Subtype.val (congrArg Subtype.val he)
  simpa using h3

end Setting

end Sec1211Ns

open Sec1211Ns in
theorem lem1211NormalBlk_of (h19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G) :
    Lem1211NormalBlk := by
  intro G _ _ T L V V₁ V₂ n β hyp hTL hβ v hv hns hchar hnorm B hB
  obtain ⟨S₀⟩ := KGH91.Setting.nonempty hyp
  obtain ⟨a₀, ha₀, c₀, hc₀, rfl, hac⟩ := hns
  have hP := KGH91.eq_pairing S₀.hn S₀.C₁ S₀.C₂ S₀.dual hβ.1 hβ.2.1 hβ.2.2.2.2
    ⟨a₀, ha₀, c₀, hc₀, by rw [hac]; exact one_ne_zero⟩ a₀ ha₀ c₀ hc₀
  have S : Sec1211Ns.Setting T L V V₁ V₂ n a₀ c₀ :=
    { toSetting := S₀, hTL := hTL, ha₀ := ha₀, hc₀ := hc₀, hns := hP ▸ hac }
  obtain ⟨F⟩ := S.nonempty_frame
  have hm : 3 ≤ n - 1 := S.three_le
  have hlv := S.lv_eq_oTwoUpper
  rw [← hlv] at hnorm hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := S.hyp.simple
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  set N := pCoreOf 2 Lv with hNdef
  set Y := centralizerSection H Lv N with hYdef
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian S.pCoreOf_ne_bot
  have hYH : Y ≤ H := centralizerSection_le_left H Lv N
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := fun g hg =>
    Setting.mem_normalizer_centralizerSection hg (hnorm hg)
  have hYc : CharTwo Y := A4.charTwo_of_normal hYH hHY hchar
  have hOY : oddCoreIn Y = ⊥ := E6.oddCoreIn_eq_bot_of_charTwo' hYc
  intro h hh
  by_contra hBh
  set B' := conjByElt h B with hB'def
  have hne : B ≠ B' := fun he =>
    hBh (C2Eleven.mem_normalizer_iff_conjByElt.mpr he.symm)
  have hB'blk : IsBlock2 Y B' := isBlock2_conjByElt_of_normalizer1515c hB.1 (hHY hh)
  have hcomm : ⁅B, B'⁆ = ⊥ := h19 G Y B B' (fun _ => charTwo_oTwoThreeIn_of_oddCore_eq_bot hOY)
    hB.1 hB'blk hne
  have hBB' : B ≤ Subgroup.centralizer (B' : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨x, hxB, hx3⟩ := Sec1211Nb.exists_orderOf_three_of_isChi0Block hB
  have hyB' : h * x * h⁻¹ ∈ B' := C2Eleven.conj_mem_conjByElt hxB
  have hy3 : orderOf (h * x * h⁻¹) = 3 := (C2Eleven.orderOf_conj_eq h x).trans hx3
  obtain ⟨z, hz3⟩ : ∃ z : ↥Lv, orderOf z = 3 := by
    have h3 : 3 ∣ Nat.card ↥Lv := (Sec1211Nq.three_dvd_card_SL (m := n - 1) (by omega)).trans
      (Subgroup.card_dvd_of_surjective (f := Setting.psi F S.lv_le_Xv)
        (Setting.psi_lv_surjective F))
    exact exists_prime_orderOf_dvd_card' 3 h3
  have hz3' : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hz3
  set X := Lv ⊔ Y with hXdef
  have hNX : X ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lv) fun y hy => hy.2.2.1
  have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lv
  have hNX' : N ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 Lv).trans le_sup_left
  have hBY : B ≤ Y := hB.1.2.1
  have hB'Y : B' ≤ Y := hB'blk.2.1
  have hxY : x ∈ Y := hBY hxB
  have hyY : h * x * h⁻¹ ∈ Y := hB'Y hyB'
  have hxy : x * (h * x * h⁻¹) = (h * x * h⁻¹) * x :=
    (Subgroup.mem_centralizer_iff.mp (hBB' hxB) _ hyB').symm
  have hp3 : ∀ g : G, orderOf g = 3 → ∀ k : ℤ, (g ^ k) ^ 3 = 1 := fun g hg k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg,
      pow_orderOf_eq_one, one_zpow]
  have h3 := Sec1211Nb.three_le_pRank_quot hNX hN2 hNX' ((le_sup_right : Y ≤ X) hxY)
    ((le_sup_right : Y ≤ X) hyY) ((le_sup_left : Lv ≤ X) z.2) hx3 hy3 hz3' hxy
    (hxY.2.2.2 z z.2) (hyY.2.2.2 z z.2) (fun a b c habc => by
      have hab3 : (x ^ a * (h * x * h⁻¹) ^ b) ^ 3 = 1 := by
        rw [(Commute.zpow_zpow hxy a b).mul_pow, hp3 x hx3 a, hp3 _ hy3 b, one_mul]
      have hzc : (z : G) ^ c ∈ Lv := Lv.zpow_mem z.2 c
      have habLv : x ^ a * (h * x * h⁻¹) ^ b ∈ Lv := by
        have := Lv.mul_mem ((CFSG.LieType.BorelTits.pCoreOf_le 2 Lv) habc) (Lv.inv_mem hzc)
        simpa [mul_assoc] using this
      have habY : x ^ a * (h * x * h⁻¹) ^ b ∈ Y := Y.mul_mem (Y.zpow_mem hxY a) (Y.zpow_mem hyY b)
      obtain ⟨e, he⟩ := Setting.exists_two_pow_of_mem_centralizerSection F hm habLv habY
      have hab1 : x ^ a * (h * x * h⁻¹) ^ b = 1 := Sec1211Kv.eq_one_of_two_three he hab3
      have hxa : x ^ a = 1 := by
        have hxaB' : x ^ a ∈ B' := by
          have : x ^ a = ((h * x * h⁻¹) ^ b)⁻¹ := eq_inv_of_mul_eq_one_left hab1
          rw [this]
          exact B'.inv_mem (B'.zpow_mem hyB' b)
        have hxaC : x ^ a ∈ B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G) := by
          refine ⟨B.zpow_mem hxB a, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
          exact (Subgroup.mem_centralizer_iff.mp
            (hBB' ((CFSG.LieType.BorelTits.pCoreOf_le 2 B) hw)) _ hxaB').symm
        obtain ⟨e', he'⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B) ⟨_, hB.1.1.2.1 hxaC⟩
        exact Sec1211Kv.eq_one_of_two_three (congrArg Subtype.val he') (hp3 x hx3 a)
      have hyb : (h * x * h⁻¹) ^ b = 1 := by
        rw [hxa, one_mul] at hab1
        exact hab1
      refine ⟨hxa, hyb, ?_⟩
      rw [hxa, hyb, one_mul, one_mul] at habc
      obtain ⟨e', he'⟩ := hN2 ⟨_, habc⟩
      exact Sec1211Kv.eq_one_of_two_three (congrArg Subtype.val he') (hp3 _ hz3' c))
  have hXH : X ≤ H := sup_le (Sec1216Lv.lv_le_centralizer L _) hYH
  have hrk : CFSG.Open.pRank 3 X ≤ 2 := by
    refine (CFSG.SectionRank.pRank_mono (by norm_num) hXH).trans ?_
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hSQ.1 3 Nat.prime_three (by norm_num)
  omega

theorem lem1211Normal_of_inputs (h331 : Stmt3_3_1)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G) (hLin : Lem1211NormalLin)
    (hA318 : Lem1211NormalA318) (hMax : Lem1211NormalMax) : Lem1211Normal :=
  lem1211Normal_of h331 h129 (lem1211NormalBlk_of h19) hLin hA318 hMax

end CFSG.Quasithin.H13
