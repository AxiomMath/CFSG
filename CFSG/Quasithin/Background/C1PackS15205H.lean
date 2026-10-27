module

public import CFSG.Quasithin.Background.C1PackS15205G

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section Abstract

variable {Q : Type*} [Group Q] [Finite Q]

theorem central_odd_eq_one {F A : Subgroup Q}
    (hAF : A ≤ F) (hAn : ∀ f ∈ F, ∀ a ∈ A, f * a * f⁻¹ ∈ A)
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hodd : ∀ a ∈ A, Odd (orderOf a))
    (h2 : ∀ f ∈ F, ∃ k : ℕ, f ^ 2 ^ k ∈ A)
    (hgen : ∀ f ∈ F, f ∈ Subgroup.closure {g | g ∈ F ∧ ∃ k : ℕ, g ^ 2 ^ k = 1})
    {d : Q} (hd : d ∈ A) (hdc : ∀ f ∈ F, f * d = d * f) : d = 1 := by
  classical
  set H : Subgroup ↥F := A.subgroupOf F with hH
  have hHn : H.Normal := ⟨fun n hn g => by
    rw [hH, Subgroup.mem_subgroupOf] at hn ⊢
    exact hAn g g.2 n hn⟩
  let _ : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hab _ a.2 _ b.2) }
  let ϕ : ↥H →* ↥A :=
    { toFun := fun h => ⟨(h.1 : Q), Subgroup.mem_subgroupOf.mp h.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let V : ↥F →* ↥A := MonoidHom.transfer ϕ
  have hdF : d ∈ F := hAF hd
  let dF : ↥F := ⟨d, hdF⟩
  have key : ∀ (k : ℕ) (g₀ : ↥F), g₀⁻¹ * dF ^ k * g₀ ∈ H → g₀⁻¹ * dF ^ k * g₀ = dF ^ k := by
    intro k g₀ _
    apply Subtype.ext
    have h1 : (g₀ : Q) * d = d * g₀ := hdc g₀ g₀.2
    have hk : d ^ k * (g₀ : Q) = (g₀ : Q) * d ^ k :=
      (Commute.pow_left (show Commute d (g₀ : Q) from h1.symm) k).eq
    show (g₀ : Q)⁻¹ * d ^ k * g₀ = d ^ k
    calc (g₀ : Q)⁻¹ * d ^ k * g₀ = (g₀ : Q)⁻¹ * (d ^ k * g₀) := by group
      _ = (g₀ : Q)⁻¹ * (g₀ * d ^ k) := by rw [hk]
      _ = d ^ k := by group
  have hVd : V dF = ϕ ⟨dF ^ H.index, MonoidHom.transfer_eq_pow_aux dF key⟩ :=
    MonoidHom.transfer_eq_pow ϕ dF key
  have hV2 : ∀ (g : Q) (hg : g ∈ F), (∃ k : ℕ, g ^ 2 ^ k = 1) → V ⟨g, hg⟩ = 1 := by
    intro g hg ⟨k, hk⟩
    set v : ↥A := V ⟨g, hg⟩ with hv
    have h1 : v ^ 2 ^ k = 1 := by
      rw [hv, ← map_pow]
      have : (⟨g, hg⟩ : ↥F) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h2' : (v : Q) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val h1
    have h3 : orderOf (v : Q) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2'
    have h4 : orderOf (v : Q) = 1 :=
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hodd _ v.2))).eq_one_of_dvd h3
    exact Subtype.ext (orderOf_eq_one_iff.mp h4)
  let K : Subgroup Q := V.ker.map F.subtype
  have hSK : {g | g ∈ F ∧ ∃ k : ℕ, g ^ 2 ^ k = 1} ⊆ (K : Set Q) := by
    intro g hg
    exact ⟨⟨g, hg.1⟩, MonoidHom.mem_ker.mpr (hV2 g hg.1 hg.2), rfl⟩
  have hdK : d ∈ K := (Subgroup.closure_le K).mpr hSK (hgen d hdF)
  obtain ⟨⟨d', hd'F⟩, hd'K, hd'd⟩ := hdK
  have hdd : (⟨d, hdF⟩ : ↥F) = ⟨d', hd'F⟩ := Subtype.ext hd'd.symm
  have hV1 : V dF = 1 := by
    have : V ⟨d', hd'F⟩ = 1 := MonoidHom.mem_ker.mp hd'K
    rw [← hdd] at this
    exact this
  have hpow : d ^ H.index = 1 := by
    rw [hVd] at hV1
    have := congrArg Subtype.val hV1
    simpa [ϕ, dF] using this
  have hidx : ∃ m : ℕ, H.index = 2 ^ m := by
    have hp : IsPGroup 2 (↥F ⧸ H) := by
      intro q
      obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := h2 f f.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hk
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    exact ⟨m, by rw [Subgroup.index_eq_card, hm]⟩
  obtain ⟨m, hm⟩ := hidx
  rw [hm] at hpow
  have h3 : orderOf d ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow
  have h4 : orderOf d = 1 :=
    (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr (hodd d hd))).eq_one_of_dvd h3
  exact orderOf_eq_one_iff.mp h4

theorem eq_one_of_cyclic_decomp {F A B : Subgroup Q} (hAF : A ≤ F)
    (hAn : ∀ f ∈ F, ∀ a ∈ A, f * a * f⁻¹ ∈ A) (h2 : ∀ f ∈ F, ∃ k : ℕ, f ^ 2 ^ k ∈ A)
    (hgen : ∀ f ∈ F, f ∈ Subgroup.closure {g | g ∈ F ∧ ∃ k : ℕ, g ^ 2 ^ k = 1})
    (hBA : B ≤ A) (hBc : ∀ b ∈ B, ∀ f ∈ F, f * b = b * f) (hBodd : ∀ b ∈ B, Odd (orderOf b))
    (hx : ∃ a ∈ A, Odd (orderOf a) ∧ ∀ y ∈ A, ∃ j : ℕ, ∃ b ∈ B, y = a ^ j * b) :
    ∀ b ∈ B, b = 1 := by
  obtain ⟨a, haA, haodd, hdec⟩ := hx
  have haF : a ∈ F := hAF haA
  have hab : ∀ y₁ ∈ A, ∀ y₂ ∈ A, y₁ * y₂ = y₂ * y₁ := by
    intro y₁ h₁ y₂ h₂'
    obtain ⟨j₁, b₁, hb₁, rfl⟩ := hdec y₁ h₁
    obtain ⟨j₂, b₂, hb₂, rfl⟩ := hdec y₂ h₂'
    have hb₂F : b₂ ∈ F := hAF (hBA hb₂)
    have c1 : Commute (a ^ j₁) b₂ := hBc b₂ hb₂ (a ^ j₁) (F.pow_mem haF j₁)
    have c2 : Commute (a ^ j₂) b₁ := hBc b₁ hb₁ (a ^ j₂) (F.pow_mem haF j₂)
    have c3 : Commute b₂ b₁ := hBc b₁ hb₁ b₂ hb₂F
    exact (Commute.mul_left
      (Commute.mul_right ((Commute.refl a).pow_pow j₁ j₂) c1)
      (Commute.mul_right c2.symm c3.symm)).eq
  have hodd : ∀ y ∈ A, Odd (orderOf y) := by
    intro y hy
    obtain ⟨j, b, hb, rfl⟩ := hdec y hy
    have hcomm : Commute (a ^ j) b := hBc b hb (a ^ j) (F.pow_mem haF j)
    have h1 : orderOf (a ^ j * b) ∣ Nat.lcm (orderOf (a ^ j)) (orderOf b) :=
      hcomm.orderOf_mul_dvd_lcm
    have h2' : Odd (orderOf (a ^ j)) := Odd.of_dvd_nat haodd (orderOf_pow_dvd j)
    have h3 : Odd (Nat.lcm (orderOf (a ^ j)) (orderOf b)) :=
      Odd.of_dvd_nat (h2'.mul (hBodd b hb)) (Nat.lcm_dvd_mul _ _)
    exact Odd.of_dvd_nat h3 h1
  intro b hb
  exact central_odd_eq_one hAF hAn hab hodd h2 hgen (hBA hb) (hBc b hb)

theorem exists_pow_eq_zpow {A : Type*} [Group A] [Finite A] (g : A) (j : ℤ) :
    ∃ n : ℕ, g ^ n = g ^ j := by
  have hpos : 0 < (orderOf g : ℤ) := by exact_mod_cast orderOf_pos g
  refine ⟨(j % (orderOf g : ℤ)).toNat, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), zpow_mod_orderOf]

end Abstract

section Claim

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ Yh : Subgroup G}

theorem Ctr5.W_eq (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    conjClosure (pCoreOf 2 (Mc ⊓ M₁)) (Y1of T M₁ Yh ⊔ T) =
      conjClosure (pCoreOf 2 (Mc ⊓ M₁)) M₁ := by
  refine le_antisymm
    (conjClosure_le fun g hg z hz => mem_conjClosure ((sup_le hY.Y1_le c.T_le_M₁) hg) hz) ?_
  refine conjClosure_le fun g hg z hz => ?_
  obtain ⟨y, hy, a, ha, rfl⟩ := hY.fac g hg
  have haz : a * z * a⁻¹ ∈ pCoreOf 2 (Mc ⊓ M₁) :=
    (Subgroup.mem_normalizer_iff.mp (inf_le_normalizer_R1 Mc M₁ ha) z).mp hz
  have e : y * a * z * (y * a)⁻¹ = y * (a * z * a⁻¹) * y⁻¹ := by group
  rw [e]
  exact mem_conjClosure (Subgroup.mem_sup_left ((le_sup_left : Yh ≤ Y1of T M₁ Yh) hy)) haz

theorem Ctr5.exists_gen_Y2 (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    ∃ x ∈ Y2of T Mc M₁ Yh, (∃ a : ℕ, orderOf x = 3 ^ a) ∧
      x ∉ Subgroup.centralizer (VZ T M₁ : Set G) ∧
      ∀ y ∈ Y2of T Mc M₁ Yh, ∃ j : ℕ, (x ^ j)⁻¹ * y ∈ Subgroup.centralizer (VZ T M₁ : Set G) := by
  have hY2M₁ : Y2of T Mc M₁ Yh ≤ M₁ := (c.Y2_le_H hY).trans inf_le_left
  have hN₁ : M₁ ≤ Subgroup.normalizer (VZ T M₁ : Set G) := le_normalizer_VZ T M₁
  have hcard : Nat.card (autOn (Y2of T Mc M₁ Yh) (VZ T M₁)) = 3 := by
    rw [c.Y2_autOn h113 hY]; exact hY.card
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord3 : ∀ (x : G) (hxY : x ∈ Y2of T Mc M₁ Yh) (hxN : x ∈ Subgroup.normalizer (VZ T M₁ : Set G)),
      x ∉ Subgroup.centralizer (VZ T M₁ : Set G) → orderOf (conjAct (VZ T M₁) ⟨x, hxN⟩) = 3 := by
    intro x hxY hxN hxC
    have hξY : conjAct (VZ T M₁) ⟨x, hxN⟩ ∈ autOn (Y2of T Mc M₁ Yh) (VZ T M₁) :=
      mem_autOn_iff_exists.mpr ⟨x, hxN, hxY, rfl⟩
    have hξ1 : conjAct (VZ T M₁) ⟨x, hxN⟩ ≠ 1 := fun h => hxC (A4.conjAct_eq_one_iff.mp h)
    have hξ3 : conjAct (VZ T M₁) ⟨x, hxN⟩ ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(autOn (Y2of T Mc M₁ Yh) (VZ T M₁)))
        (x := ⟨conjAct (VZ T M₁) ⟨x, hxN⟩, hξY⟩)
      rw [hcard] at this
      exact congrArg Subtype.val this
    exact orderOf_eq_prime hξ3 hξ1
  have hex : ∃ x ∈ Y2of T Mc M₁ Yh, Odd (orderOf x) ∧
      x ∉ Subgroup.centralizer (VZ T M₁ : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : Y2of T Mc M₁ Yh ≤ Subgroup.centralizer (VZ T M₁ : Set G) :=
      (Y2of_idem T Mc M₁ Yh).symm.le.trans
        ((Subgroup.closure_le _).mpr fun x hx => hcon x hx.1 hx.2)
    have hbot := autOn_eq_bot_of_le_centralizer hle
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨x₀, hx₀Y, -, hx₀C⟩ := hex
  have hx₀N : x₀ ∈ Subgroup.normalizer (VZ T M₁ : Set G) := hN₁ (hY2M₁ hx₀Y)
  have hord₀ := hord3 x₀ hx₀Y hx₀N hx₀C
  obtain ⟨a, m, hm3, hxm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₀).ne' 3 (by norm_num)
  have hm0 : m ≠ 0 := fun h0 => by
    have := orderOf_pos x₀
    rw [hxm, h0] at this
    omega
  have hmdvd : m ∣ orderOf x₀ := ⟨3 ^ a, by rw [hxm]; ring⟩
  have hxo : orderOf (x₀ ^ m) = 3 ^ a := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hxm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hxY : x₀ ^ m ∈ Y2of T Mc M₁ Yh := (Y2of T Mc M₁ Yh).pow_mem hx₀Y m
  have hxN : x₀ ^ m ∈ Subgroup.normalizer (VZ T M₁ : Set G) := (Subgroup.normalizer _).pow_mem hx₀N m
  have hxC : x₀ ^ m ∉ Subgroup.centralizer (VZ T M₁ : Set G) := by
    intro h
    have h1 : conjAct (VZ T M₁) ⟨x₀ ^ m, hxN⟩ = 1 := A4.conjAct_eq_one_iff.mpr h
    have h2 : conjAct (VZ T M₁) ⟨x₀ ^ m, hxN⟩ = conjAct (VZ T M₁) ⟨x₀, hx₀N⟩ ^ m := by
      rw [← map_pow]
      rfl
    rw [h2] at h1
    have h3 : orderOf (conjAct (VZ T M₁) ⟨x₀, hx₀N⟩) ∣ m := orderOf_dvd_of_pow_eq_one h1
    rw [hord₀] at h3
    exact hm3 h3
  refine ⟨x₀ ^ m, hxY, ⟨a, hxo⟩, hxC, fun y hy => ?_⟩
  have hyN : y ∈ Subgroup.normalizer (VZ T M₁ : Set G) := hN₁ (hY2M₁ hy)
  set x : G := x₀ ^ m with hxdef
  set ξ : MulAut ↥(VZ T M₁) := conjAct (VZ T M₁) ⟨x, hxN⟩ with hξ
  have hξY : ξ ∈ autOn (Y2of T Mc M₁ Yh) (VZ T M₁) :=
    mem_autOn_iff_exists.mpr ⟨x, hxN, hxY, rfl⟩
  have hord : orderOf ξ = 3 := hord3 x hxY hxN hxC
  have hzY : Subgroup.zpowers ξ = autOn (Y2of T Mc M₁ Yh) (VZ T M₁) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hξY) ?_
    rw [hcard, Nat.card_zpowers, hord]
  have hmem : conjAct (VZ T M₁) ⟨y, hyN⟩ ∈ Subgroup.zpowers ξ := by
    rw [hzY]
    exact mem_autOn_iff_exists.mpr ⟨y, hyN, hy, rfl⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨n, hn⟩ := exists_pow_eq_zpow ξ j
  refine ⟨n, ?_⟩
  have h3 : conjAct (VZ T M₁) (((⟨x, hxN⟩ : Subgroup.normalizer (VZ T M₁ : Set G)) ^ n)⁻¹ *
      ⟨y, hyN⟩) = 1 := by
    rw [map_mul, map_inv, map_pow, ← hξ, hn, hj]
    exact inv_mul_cancel _
  exact A4.conjAct_eq_one_iff.mp h3

theorem Ctr5.Y2_inf_centralizer_le (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁)
    (hY : Yd5 T Mc M M₁ Yh) :
    Y2of T Mc M₁ Yh ⊓ Subgroup.centralizer (VZ T M₁ : Set G) ≤ pCoreOf 2 M₁ := by
  classical
  have hR₁M₁ : pCoreOf 2 (Mc ⊓ M₁) ≤ M₁ := c.R1_le_T.trans c.T_le_M₁
  have hWM : conjClosure (pCoreOf 2 (Mc ⊓ M₁)) M₁ ≤ M₁ :=
    conjClosure_le fun g hg z hz => M₁.mul_mem (M₁.mul_mem hg (hR₁M₁ hz)) (M₁.inv_mem hg)
  have hDn : M₁ ≤ Subgroup.normalizer
      ((Y2of T Mc M₁ Yh ⊓ Subgroup.centralizer (VZ T M₁ : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨c.Y2_normal hY hg, A4.mem_normalizer_centralizer (le_normalizer_VZ T M₁ hg)⟩
  obtain ⟨-, h3b⟩ := lemma_14_1_17_three c.qtfe c.hyp1 hY.Y1_le
  have hF : imageOTwoQuot M₁ (conjClosure (pCoreOf 2 (Mc ⊓ M₁)) M₁) =
      conjClosure (imageOTwoQuot M₁ (pCoreOf 2 (Mc ⊓ M₁))) ⊤ := imageOTwoQuot_conjClosure hR₁M₁
  have hA : imageOTwoQuot M₁ (Y2of T Mc M₁ Yh) =
      oTwoUpper (conjClosure (imageOTwoQuot M₁ (pCoreOf 2 (Mc ⊓ M₁))) ⊤) := by
    unfold Y2of
    rw [c.W_eq hY, S152Y.imageOTwoQuot_oTwoUpper hWM, hF]
  have hRp2 : IsPGroup 2 (imageOTwoQuot M₁ (pCoreOf 2 (Mc ⊓ M₁))) :=
    S152Y.imageOTwoQuot_isPGroup hR₁M₁ (pCoreOf_isPGroup 2 _)
  set Rp : Subgroup (OTwoQuot M₁) := imageOTwoQuot M₁ (pCoreOf 2 (Mc ⊓ M₁)) with hRp
  set F : Subgroup (OTwoQuot M₁) := conjClosure Rp ⊤ with hFdef
  set A : Subgroup (OTwoQuot M₁) := oTwoUpper F with hAdef
  set B : Subgroup (OTwoQuot M₁) := imageOTwoQuot M₁
    (Y2of T Mc M₁ Yh ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) with hBdef
  have hBA : B ≤ A := (imageOTwoQuot_mono inf_le_left).trans hA.le
  have hBodd : ∀ b ∈ B, Odd (orderOf b) := fun b hb => (h3b b hb).2.1
  have hBn : ∀ g : OTwoQuot M₁, ∀ b ∈ B, g⁻¹ * b * g ∈ B := by
    intro g b hb
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨d, hdM, hdD, rfl⟩ := mem_imageOTwoQuot_iff.mp hb
    have hm : (m : G) ∈ M₁ := m.2
    have h1 : (m : G)⁻¹ * d * ((m : G)⁻¹)⁻¹ ∈
        Y2of T Mc M₁ Yh ⊓ Subgroup.centralizer (VZ T M₁ : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hDn (M₁.inv_mem hm)) d).mp hdD
    refine mem_imageOTwoQuot_iff.mpr ⟨(m : G)⁻¹ * d * m,
      M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hm) hdM) hm, by simpa using h1, ?_⟩
    show (QuotientGroup.mk ((m⁻¹ : ↥M₁) * ⟨d, hdM⟩ * m) : OTwoQuot M₁) = _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hBc : ∀ b ∈ B, ∀ f ∈ F, f * b = b * f := by
    intro b hb
    have hle : F ≤ Subgroup.centralizer ({b} : Set (OTwoQuot M₁)) := by
      refine conjClosure_le fun g _ z hz => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      have hb' : g⁻¹ * b * g ∈ B := hBn g b hb
      have hzw : z ∈ imageOTwoQuot M₁
          ((M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) ⊔ pCoreOf 2 (Mc ⊓ M₁)) :=
        imageOTwoQuot_mono le_sup_right hz
      have hcomm := (h3b _ hb').2.2 z hzw
      calc b * (g * z * g⁻¹) = g * ((g⁻¹ * b * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by rw [← hcomm]
        _ = (g * z * g⁻¹) * b := by group
    intro f hf
    exact (Subgroup.mem_centralizer_iff.mp (hle hf) b (Set.mem_singleton b)).symm
  have hgen : ∀ f ∈ F, f ∈ Subgroup.closure {g | g ∈ F ∧ ∃ k : ℕ, g ^ 2 ^ k = 1} := by
    have : F ≤ Subgroup.closure {g | g ∈ F ∧ ∃ k : ℕ, g ^ 2 ^ k = 1} := by
      refine conjClosure_le fun g _ z hz => Subgroup.subset_closure
        ⟨mem_conjClosure (Subgroup.mem_top g) hz, ?_⟩
      obtain ⟨k, hk⟩ := hRp2 ⟨z, hz⟩
      refine ⟨k, ?_⟩
      have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      calc (g * z * g⁻¹) ^ 2 ^ k = g * z ^ 2 ^ k * g⁻¹ := conj_pow
        _ = 1 := by rw [hk']; group
    exact fun f hf => this hf
  obtain ⟨x, hxY, ⟨a₃, hxo3⟩, -, hxdec⟩ := c.exists_gen_Y2 h113 hY
  have hxodd : Odd (orderOf x) := by rw [hxo3]; exact Odd.pow (by decide)
  have hxM₁' : Y2of T Mc M₁ Yh ≤ M₁ := (c.Y2_le_H hY).trans inf_le_left
  have hxM₁ : x ∈ M₁ := hxM₁' hxY
  have hx : ∃ a ∈ A, Odd (orderOf a) ∧ ∀ y ∈ A, ∃ j : ℕ, ∃ b ∈ B, y = a ^ j * b := by
    have hxA : (QuotientGroup.mk ⟨x, hxM₁⟩ : OTwoQuot M₁) ∈ A := by
      rw [← hA]
      exact mem_imageOTwoQuot_iff.mpr ⟨x, hxM₁, hxY, rfl⟩
    refine ⟨QuotientGroup.mk ⟨x, hxM₁⟩, hxA, ?_, ?_⟩
    · have h1 : orderOf (QuotientGroup.mk (⟨x, hxM₁⟩ : ↥M₁) : OTwoQuot M₁) ∣
          orderOf (⟨x, hxM₁⟩ : ↥M₁) := orderOf_map_dvd (QuotientGroup.mk' _) _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hxodd h1
    · intro y hy
      have hy₀ : y ∈ imageOTwoQuot M₁ (Y2of T Mc M₁ Yh) := by
        rw [hA]
        exact hy
      obtain ⟨y', hy'M, hy'Y, rfl⟩ := mem_imageOTwoQuot_iff.mp hy₀
      obtain ⟨n, hn⟩ := hxdec y' hy'Y
      have hxn : x ^ n ∈ Y2of T Mc M₁ Yh := (Y2of T Mc M₁ Yh).pow_mem hxY n
      have hdY : (x ^ n)⁻¹ * y' ∈ Y2of T Mc M₁ Yh :=
        (Y2of T Mc M₁ Yh).mul_mem ((Y2of T Mc M₁ Yh).inv_mem hxn) hy'Y
      have hdM : (x ^ n)⁻¹ * y' ∈ M₁ := M₁.mul_mem (M₁.inv_mem (M₁.pow_mem hxM₁ n)) hy'M
      refine ⟨n, QuotientGroup.mk ⟨(x ^ n)⁻¹ * y', hdM⟩,
        mem_imageOTwoQuot_iff.mpr ⟨_, hdM, ⟨hdY, hn⟩, rfl⟩, ?_⟩
      have e : (⟨y', hy'M⟩ : ↥M₁) = (⟨x, hxM₁⟩ : ↥M₁) ^ n * ⟨(x ^ n)⁻¹ * y', hdM⟩ := by
        apply Subtype.ext
        simp
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  have hB1 := eq_one_of_cyclic_decomp (oTwoUpper_le F) (fun f hf a ha =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper F hf) a).mp ha)
    (fun f hf => exists_pow_mem_oTwoUpper F hf) hgen hBA hBc hBodd hx
  intro d hd
  have hdM : d ∈ M₁ := hxM₁' hd.1
  have hdB : (QuotientGroup.mk ⟨d, hdM⟩ : OTwoQuot M₁) ∈ B :=
    mem_imageOTwoQuot_iff.mpr ⟨d, hdM, hd, rfl⟩
  exact (mk_eq_one_iff_mem_pCoreOf ⟨d, hdM⟩).mp (hB1 _ hdB)

end Claim

end C1Pack5

end CFSG.Quasithin
