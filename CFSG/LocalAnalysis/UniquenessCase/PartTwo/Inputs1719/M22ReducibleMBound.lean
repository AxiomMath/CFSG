module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.QuotMap
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.EmptyFaithful.S146zNAmtA
public import CFSG.Quasithin.H13.A5M22HatRow
public import CFSG.Quasithin.Background.HMathieuFactsBase
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1
open CFSG.Quasithin.H13.A5.M22Hat

theorem stabSub_apply_mem {V : Type} [CommGroup V] {U : Subgroup V} {g : MulAut V}
    (hg : g ∈ stabSub U) {w : V} (hw : w ∈ U) : g w ∈ U :=
  (mem_stabSub.mp hg w).mpr hw

theorem stabSub_inv_apply_mem {V : Type} [CommGroup V] {U : Subgroup V} {g : MulAut V}
    (hg : g ∈ stabSub U) {w : V} (hw : w ∈ U) : g⁻¹ w ∈ U :=
  (mem_stabSub.mp ((stabSub U).inv_mem hg) w).mpr hw

theorem mem_stabSub_conj {V : Type} [CommGroup V] {U : Subgroup V} {g a : MulAut V}
    (hg : g ∈ stabSub U) (ha : a ∈ stabSub U) : g * a * g⁻¹ ∈ stabSub U := by
  rw [mem_stabSub] at hg ha ⊢
  have hgi : ∀ u : V, g⁻¹ u ∈ U ↔ u ∈ U := by
    intro u
    rw [← hg (g⁻¹ u), MulAut.apply_inv_self]
  intro w
  calc (g * a * g⁻¹) w ∈ U ↔ g (a (g⁻¹ w)) ∈ U := by rw [MulAut.mul_apply, MulAut.mul_apply]
    _ ↔ a (g⁻¹ w) ∈ U := hg _
    _ ↔ g⁻¹ w ∈ U := ha _
    _ ↔ w ∈ U := hgi w

theorem ten_le_rkIdx_of_eleven {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {y : MulAut V} (hy11 : 11 ∣ orderOf y) :
    10 ≤ rkIdx (fixV (Subgroup.zpowers y)) := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := hy11
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (orderOf_pos y).ne' hk
  set g : MulAut V := y ^ k with hg
  have hg11 : orderOf g = 11 := by
    rw [hg, orderOf_pow_of_dvd hk0 ⟨11, by rw [hk, mul_comm]⟩, hk,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  have hle : fixV (Subgroup.zpowers y) ≤ fixV (Subgroup.zpowers g) := by
    intro w hw x hx
    exact hw x (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _) hx)
  refine le_trans ?_ (rkIdx_le_of_le hV hle)
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg11
    omega
  have hgpow : g ^ 11 = 1 := by rw [← hg11]; exact pow_orderOf_eq_one g
  have hmod := card_modEq_fix (MulAut.toPerm V g) (by
    rw [← map_pow, hgpow, map_one])
  have hF : Nat.card {x : V // MulAut.toPerm V g x = x} =
      Nat.card (fixV (Subgroup.zpowers g)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (mem_fixV_zpowers_iff (g := g)).symm)
  have hcardV : Nat.card V = 2 ^ rk V := card_eq_two_pow_rk hV
  have hcardF : Nat.card (fixV (Subgroup.zpowers g)) = 2 ^ rk (fixV (Subgroup.zpowers g)) :=
    card_eq_two_pow hV _
  rw [hF, hcardV, hcardF] at hmod
  have hle' : rk (fixV (Subgroup.zpowers g)) ≤ rk V := by
    have h := rk_mono (le_top : fixV (Subgroup.zpowers g) ≤ (⊤ : Subgroup V))
    rwa [rk_top] at h
  have hlt' : rk (fixV (Subgroup.zpowers g)) < rk V := by
    rcases lt_or_eq_of_le hle' with h | h
    · exact h
    · exfalso
      have htop : fixV (Subgroup.zpowers g) = ⊤ :=
        eq_of_le_of_rk_le hV le_top (by rw [rk_top]; exact le_of_eq h.symm)
      exact hg1 (eq_one_of_fixV_eq_top htop)
  have hpos : 0 < rk V - rk (fixV (Subgroup.zpowers g)) := Nat.sub_pos_of_lt hlt'
  have hsplit : (2 : ℕ) ^ rk V =
      2 ^ rk (fixV (Subgroup.zpowers g)) * 2 ^ (rk V - rk (fixV (Subgroup.zpowers g))) := by
    rw [← pow_add, Nat.add_sub_cancel' hle']
  have hkey : 2 ^ (rk V - rk (fixV (Subgroup.zpowers g))) ≡ 1 [MOD 11] := by
    have hcop : Nat.Coprime 11 (2 ^ rk (fixV (Subgroup.zpowers g))) :=
      Nat.Coprime.pow_right _ (by norm_num)
    have hmul : 2 ^ rk (fixV (Subgroup.zpowers g)) *
        2 ^ (rk V - rk (fixV (Subgroup.zpowers g))) ≡
          2 ^ rk (fixV (Subgroup.zpowers g)) * 1 [MOD 11] := by
      rw [mul_one, ← hsplit]
      exact hmod
    exact Nat.ModEq.cancel_left_of_coprime hcop hmul
  have htable : ∀ j : ℕ, 0 < j → j < 10 → ¬ (2 ^ j ≡ 1 [MOD 11]) := by
    intro j hj0 hj10 h
    interval_cases j <;> norm_num [Nat.ModEq] at h
  have h10 : 10 ≤ rk V - rk (fixV (Subgroup.zpowers g)) := by
    by_contra h
    exact htable _ hpos (by omega) hkey
  have h1 : rk (fixV (Subgroup.zpowers g)) + rkIdx (fixV (Subgroup.zpowers g)) = rk V :=
    rk_add_rkIdx (H := fixV (Subgroup.zpowers g))
  omega

theorem rk_commSub_mul_le {V : Type} [CommGroup V] [Finite V] {I : Subgroup V}
    {a b : MulAut V} (ha : a ∈ stabSub I) (hb : b ∈ stabSub I) :
    rk (commSub I (Subgroup.zpowers (a * b))) ≤
      rk (commSub I (Subgroup.zpowers a)) + rk (commSub I (Subgroup.zpowers b)) := by
  classical
  set K : Subgroup V := commSub I (Subgroup.zpowers a) ⊔ commSub I (Subgroup.zpowers b) with hK
  have hIK : ∀ n : ℕ, ∀ w ∈ I, (((a * b) ^ n) w) ∈ I := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      have hstep : (((a * b) ^ (n + 1)) w) = a (b (((a * b) ^ n) w)) := by
        rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply]
      rw [hstep]
      exact stabSub_apply_mem ha (stabSub_apply_mem hb (ih w hw))
  have hgen : ∀ n : ℕ, ∀ w ∈ I, (((a * b) ^ n) w) * w⁻¹ ∈ K := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rw [pow_zero, MulAut.one_apply, mul_inv_cancel]
      exact K.one_mem
    | succ n ih =>
      intro w hw
      have hu : (((a * b) ^ n) w) ∈ I := hIK n w hw
      have h1 : (((a * b) ^ (n + 1)) w) * w⁻¹ =
          (a (b (((a * b) ^ n) w)) * (b (((a * b) ^ n) w))⁻¹) *
            ((b (((a * b) ^ n) w)) * (((a * b) ^ n) w)⁻¹) *
              ((((a * b) ^ n) w) * w⁻¹) := by
        rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply]
        group
      rw [h1]
      refine K.mul_mem (K.mul_mem ?_ ?_) (ih w hw)
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure
          ⟨a, Subgroup.mem_zpowers a, b (((a * b) ^ n) w), stabSub_apply_mem hb hu, rfl⟩)
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure
          ⟨b, Subgroup.mem_zpowers b, (((a * b) ^ n) w), hu, rfl⟩)
  have hle : commSub I (Subgroup.zpowers (a * b)) ≤ K := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, (a * b) ^ n = x :=
      (Submonoid.mem_powers_iff x (a * b)).mp
        ((mem_powers_iff_mem_zpowers (x := a * b) (y := x)).mpr hx)
    exact hgen n w hw
  calc rk (commSub I (Subgroup.zpowers (a * b))) ≤ rk K := rk_mono hle
    _ ≤ rk (commSub I (Subgroup.zpowers a)) + rk (commSub I (Subgroup.zpowers b)) := by
      rw [hK]
      have h1 := rk_sup_add_rk_inf (commSub I (Subgroup.zpowers a))
        (commSub I (Subgroup.zpowers b))
      omega

theorem rk_commSub_conj {V : Type} [CommGroup V] [Finite V] {I : Subgroup V}
    {g a : MulAut V} (hg : g ∈ stabSub I) (ha : a ∈ stabSub I) :
    rk (commSub I (Subgroup.zpowers (g * a * g⁻¹))) =
      rk (commSub I (Subgroup.zpowers a)) := by
  have hga : g * a * g⁻¹ ∈ stabSub I := mem_stabSub_conj hg ha
  have h1 : rk (commSub I (Subgroup.zpowers (g * a * g⁻¹))) +
      rk ↥(I ⊓ fixV (Subgroup.zpowers (g * a * g⁻¹))) = rk I :=
    rk_commSub_add_rk_inf_fixV
      (fun x hx w hw => stabSub_apply_mem (Subgroup.zpowers_le.mpr hga hx) hw)
  have h2 : rk (commSub I (Subgroup.zpowers a)) +
      rk ↥(I ⊓ fixV (Subgroup.zpowers a)) = rk I :=
    rk_commSub_add_rk_inf_fixV
      (fun x hx w hw => stabSub_apply_mem (Subgroup.zpowers_le.mpr ha hx) hw)
  have h3 : rk ↥(I ⊓ fixV (Subgroup.zpowers (g * a * g⁻¹))) =
      rk ↥(I ⊓ fixV (Subgroup.zpowers a)) := by
    have hgi : g⁻¹ ∈ stabSub I := (stabSub I).inv_mem hg
    have hs : ∀ w : V, w ∈ I ↔ g⁻¹ w ∈ I := fun w => (mem_stabSub.mp hgi w).symm
    have h := CFSG.Quasithin.A6Amt.rk_inf_fixV_twist (W₁ := I) (W₂ := I) hs (g * a * g⁻¹)
    rw [h, show g⁻¹ * (g * a * g⁻¹) * g = a from by group]
  omega

theorem ten_le_rk_commSub_of_orderOf_eleven {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {I : Subgroup V} {y : MulAut V}
    (hyI : y ∈ stabSub I) (hy11 : orderOf y = 11) (hyne : y ∉ centSub I) :
    10 ≤ rk (commSub I (Subgroup.zpowers y)) := by
  have hstab : ∀ x ∈ Subgroup.zpowers y, ∀ w ∈ I, x w ∈ I :=
    fun x hx w hw => stabSub_apply_mem (Subgroup.zpowers_le.mpr hyI hx) hw
  have hcomm : rk (commSub I (Subgroup.zpowers y)) +
      rk ↥(I ⊓ fixV (Subgroup.zpowers y)) = rk I := rk_commSub_add_rk_inf_fixV hstab
  have hres : A6Rank (resHom I ⟨y, hyI⟩) + rk ↥(I ⊓ fixV (Subgroup.zpowers y)) = rk ↥I :=
    CFSG.Quasithin.A6Amt.rk_fixV_res hyI
  have hresne : resHom I ⟨y, hyI⟩ ≠ 1 := by
    intro h1
    apply hyne
    rw [mem_centSub]
    intro w hw
    have h1' : resHom I ⟨y, hyI⟩ ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [h1]; rfl
    have h2 := congrArg Subtype.val h1'
    rwa [resHom_apply] at h2
  have hIexp : ∀ v : ↥I, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV (v : V))
  have hdvd : orderOf (resHom I ⟨y, hyI⟩) ∣ 11 := by
    have hpow : (⟨y, hyI⟩ : ↥(stabSub I)) ^ 11 = 1 := by
      apply Subtype.ext
      simpa using (by rw [← hy11]; exact pow_orderOf_eq_one y)
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hpow, map_one]
  have hres11 : orderOf (resHom I ⟨y, hyI⟩) = 11 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hresne
    · exact h
  have h10 := ten_le_rkIdx_of_eleven hIexp (y := resHom I ⟨y, hyI⟩) (by rw [hres11])
  unfold A6Rank at hres
  omega

theorem eqOn_of_commute_of_isIrrOn {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {M : Subgroup (MulAut V)} {I : Subgroup V}
    (hirr : IsIrrOn M I ⊥) {g : MulAut V} (hg2 : g * g = 1) (hgI : g ∈ stabSub I)
    (hcomm : ∀ m ∈ M, g * m = m * g) : ∀ w ∈ I, g w = w := by
  have hMI : M ≤ stabSub I := le_stabSub_of_stableUnder hirr.2.1
  have hKstab : StableUnder M (I ⊓ fixV (Subgroup.zpowers g)) := by
    intro m hm w hw
    have hwI : w ∈ I := hw.1
    have hwg : g w = w := (mem_fixV_zpowers_iff (g := g)).mp hw.2
    refine ⟨stabSub_apply_mem (hMI hm) hwI, ?_⟩
    exact (mem_fixV_zpowers_iff (g := g)).mpr (by
      have h1 : g (m w) = m (g w) := by
        have h := congrArg (fun f : MulAut V => f w) (hcomm m hm)
        simpa [MulAut.mul_apply] using h
      rw [h1, hwg])
  rcases hirr.2.2.2 (I ⊓ fixV (Subgroup.zpowers g)) hKstab bot_le inf_le_left with hbot | htop
  · intro w hw
    have hδmem : ∀ u ∈ I, g u * u⁻¹ ∈ I := fun u hu =>
      I.mul_mem (stabSub_apply_mem hgI hu) (I.inv_mem hu)
    have hδδ : ∀ u ∈ I, g (g u * u⁻¹) * (g u * u⁻¹)⁻¹ = 1 := by
      intro u _
      have hgg : g (g u) = u := by
        have h := congrArg (fun f : MulAut V => f u) hg2
        simpa [MulAut.mul_apply] using h
      have hstep : g (g u * u⁻¹) * (g u * u⁻¹)⁻¹ = (u * (g u)⁻¹) * (u * (g u)⁻¹) := by
        simp only [map_mul, map_inv, hgg]
        group
      rw [hstep]
      simpa [sq] using hV (u * (g u)⁻¹)
    have hmem : g w * w⁻¹ ∈ I ⊓ fixV (Subgroup.zpowers g) := by
      refine ⟨hδmem w hw, ?_⟩
      exact (mem_fixV_zpowers_iff (g := g)).mpr (by
        have h := hδδ w hw
        rwa [mul_inv_eq_one] at h)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  · intro w hw
    have hle : I ≤ fixV (Subgroup.zpowers g) := htop ▸ inf_le_right
    exact (mem_fixV_zpowers_iff (g := g)).mp (hle hw)

theorem commute_of_fix_on_faithful {V : Type} [CommGroup V] {M : Subgroup (MulAut V)}
    {I : Subgroup V} (hMI : M ≤ stabSub I)
    (hfaith : ∀ m ∈ M, (∀ w ∈ I, m w = w) → m = 1)
    {s : MulAut V} (hsN : s ∈ Subgroup.normalizer (M : Set (MulAut V)))
    (hfix : ∀ w ∈ I, s w = w) : ∀ l ∈ M, s * l = l * s := by
  have hsstab : s ∈ stabSub I := centSub_le_stabSub I (mem_centSub.mpr hfix)
  intro l hl
  have hmem : s * l * s⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
  have hpt : ∀ w ∈ I, (s * l * s⁻¹) w = l w := by
    intro w hw
    have hsi : s⁻¹ w ∈ I := stabSub_inv_apply_mem hsstab hw
    have hsiw : s⁻¹ w = w := by
      have h := hfix (s⁻¹ w) hsi
      rw [MulAut.apply_inv_self] at h
      exact h.symm
    have hlw : l w ∈ I := stabSub_apply_mem (hMI hl) hw
    rw [MulAut.mul_apply, MulAut.mul_apply, hsiw, hfix (l w) hlw]
  have hm : (s * l * s⁻¹) * l⁻¹ ∈ M := M.mul_mem hmem (M.inv_mem hl)
  have h2 : ∀ w ∈ I, ((s * l * s⁻¹) * l⁻¹) w = w := by
    intro w hw
    rw [MulAut.mul_apply, hpt (l⁻¹ w) (stabSub_inv_apply_mem (hMI hl) hw), MulAut.apply_inv_self]
  have h3 := hfaith _ hm h2
  rw [mul_inv_eq_one] at h3
  exact mul_inv_eq_iff_eq_mul.mp h3

theorem three_le_commSub_of_isSpor_M22
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {M : Subgroup (MulAut V)} (hM : IsSpor ↥M .M22) {I : Subgroup V}
    (hMI : M ≤ stabSub I) (hfaith : M ⊓ centSub I = ⊥)
    {t : MulAut V} (ht2 : orderOf t = 2) (htI : t ∈ stabSub I)
    (htN : t ∈ Subgroup.normalizer (M : Set (MulAut V)))
    (hβne : ∃ m ∈ M, t * m * t⁻¹ ≠ m) :
    3 ≤ rk (commSub I (Subgroup.zpowers t)) := by
  classical
  by_contra hlt
  push Not at hlt
  have ht2mul : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2mul
  let α : MulAut ↥M := M.normalizerMonoidHom ⟨t, htN⟩
  have hα : ∀ γ : ↥M, ((α γ : ↥M) : MulAut V) = t * (γ : MulAut V) * t⁻¹ :=
    fun γ => Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htN⟩ γ
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun γ => ?_
    refine Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hα, hα, htinv]
    calc t * (t * (γ : MulAut V) * t) * t = (t * t) * (γ : MulAut V) * (t * t) := by group
      _ = (γ : MulAut V) := by rw [ht2mul, one_mul, mul_one]
  obtain ⟨e₀⟩ := hM
  let e : ↥M ≃* ↥H.Mathieu.mog22 := e₀.trans H.Mathieu.mog22EquivM22.symm
  let β : MulAut ↥H.Mathieu.mog22 := (e.symm.trans α).trans e
  have hβeq : ∀ γ : ↥M, β (e γ) = e (α γ) := by
    intro γ
    show ((e.symm.trans α).trans e) (e γ) = e (α γ)
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun n => ?_
    obtain ⟨γ, rfl⟩ := e.surjective n
    refine Subtype.ext ?_
    rw [MulAut.mul_apply, hβeq, hβeq, ← MulAut.mul_apply, hα2]
    simp
  have hβ1 : β ≠ 1 := by
    intro h1
    obtain ⟨m, hm, hne⟩ := hβne
    apply hne
    have h2 : β (e ⟨m, hm⟩) = e ⟨m, hm⟩ := by rw [h1, MulAut.one_apply]
    rw [hβeq] at h2
    have h3 : α ⟨m, hm⟩ = ⟨m, hm⟩ := e.injective h2
    have h4 := congrArg Subtype.val h3
    rwa [hα] at h4
  obtain ⟨n₁, n₂, n₃, hn11⟩ := H13.A5.M22Hat.exists_orderOf_eleven β hβ2 hβ1
  set γ₁ : ↥M := e.symm n₁ with hγ₁
  set γ₂ : ↥M := e.symm n₂ with hγ₂
  set γ₃ : ↥M := e.symm n₃ with hγ₃
  set yM : ↥M := α γ₁ * γ₁⁻¹ * (γ₂ * α (γ₂⁻¹ * γ₃) * γ₃⁻¹) with hyM
  have hyval : e yM = β n₁ * n₁⁻¹ * (n₂ * β (n₂⁻¹ * n₃) * n₃⁻¹) := by
    have h1 : e yM = e (α γ₁) * (e γ₁)⁻¹ *
        (e γ₂ * e (α (γ₂⁻¹ * γ₃)) * (e γ₃)⁻¹) := by
      rw [hyM]
      simp only [map_mul, map_inv]
    rw [h1, show e (α γ₁) = β (e γ₁) from (hβeq γ₁).symm,
      show e (α (γ₂⁻¹ * γ₃)) = β (e (γ₂⁻¹ * γ₃)) from (hβeq _).symm]
    rw [hγ₁, hγ₂, hγ₃]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hy11 : orderOf ((yM : ↥M) : MulAut V) = 11 := by
    rw [Subgroup.orderOf_coe]
    have h := orderOf_injective e.toMonoidHom e.injective yM
    rw [show e.toMonoidHom yM = e yM from rfl, hyval, hn11] at h
    exact h.symm
  have hy_eq : ((yM : ↥M) : MulAut V) =
      t * (((γ₁ : ↥M) : MulAut V) * t * ((γ₁ : ↥M) : MulAut V)⁻¹) *
        (((γ₂ : ↥M) : MulAut V) * t * ((γ₂ : ↥M) : MulAut V)⁻¹) *
          (((γ₃ : ↥M) : MulAut V) * t * ((γ₃ : ↥M) : MulAut V)⁻¹) := by
    rw [hyM]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα, htinv]
    group
  have hyI : ((yM : ↥M) : MulAut V) ∈ stabSub I := hMI yM.2
  have hyne : ((yM : ↥M) : MulAut V) ∉ centSub I := by
    intro hc
    have hmem : ((yM : ↥M) : MulAut V) ∈ M ⊓ centSub I := ⟨yM.2, hc⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    have h1 : ((yM : ↥M) : MulAut V) = 1 := by
      rw [show ((yM : ↥M) : MulAut V) = ((⟨(1 : ↥M), M.one_mem⟩ : ↥M) : MulAut V) from
        congrArg Subtype.val (Subtype.ext hmem)]
      rfl
    rw [h1, orderOf_one] at hy11
    omega
  have h10 := ten_le_rk_commSub_of_orderOf_eleven hV hyI hy11 hyne
  have h8 : rk (commSub I (Subgroup.zpowers ((yM : ↥M) : MulAut V))) ≤
      4 * rk (commSub I (Subgroup.zpowers t)) := by
    rw [hy_eq]
    have hp1 : ((γ₁ : ↥M) : MulAut V) * t * ((γ₁ : ↥M) : MulAut V)⁻¹ ∈ stabSub I :=
      mem_stabSub_conj (hMI γ₁.2) htI
    have hp2 : ((γ₂ : ↥M) : MulAut V) * t * ((γ₂ : ↥M) : MulAut V)⁻¹ ∈ stabSub I :=
      mem_stabSub_conj (hMI γ₂.2) htI
    have hp3 : ((γ₃ : ↥M) : MulAut V) * t * ((γ₃ : ↥M) : MulAut V)⁻¹ ∈ stabSub I :=
      mem_stabSub_conj (hMI γ₃.2) htI
    have hq1 : t * (((γ₁ : ↥M) : MulAut V) * t * ((γ₁ : ↥M) : MulAut V)⁻¹) ∈ stabSub I :=
      (stabSub I).mul_mem htI hp1
    have hq2 : t * (((γ₁ : ↥M) : MulAut V) * t * ((γ₁ : ↥M) : MulAut V)⁻¹) *
        (((γ₂ : ↥M) : MulAut V) * t * ((γ₂ : ↥M) : MulAut V)⁻¹) ∈ stabSub I :=
      (stabSub I).mul_mem hq1 hp2
    have h1 := rk_commSub_mul_le (I := I)
      (a := t * (((γ₁ : ↥M) : MulAut V) * t * ((γ₁ : ↥M) : MulAut V)⁻¹) *
        (((γ₂ : ↥M) : MulAut V) * t * ((γ₂ : ↥M) : MulAut V)⁻¹))
      (b := ((γ₃ : ↥M) : MulAut V) * t * ((γ₃ : ↥M) : MulAut V)⁻¹) hq2 hp3
    have h2 := rk_commSub_mul_le (I := I)
      (a := t * (((γ₁ : ↥M) : MulAut V) * t * ((γ₁ : ↥M) : MulAut V)⁻¹))
      (b := ((γ₂ : ↥M) : MulAut V) * t * ((γ₂ : ↥M) : MulAut V)⁻¹) hq1 hp2
    have h3 := rk_commSub_mul_le (I := I) (a := t)
      (b := ((γ₁ : ↥M) : MulAut V) * t * ((γ₁ : ↥M) : MulAut V)⁻¹) htI hp1
    rw [rk_commSub_conj (hMI γ₃.2) htI] at h1
    rw [rk_commSub_conj (hMI γ₂.2) htI] at h2
    rw [rk_commSub_conj (hMI γ₁.2) htI] at h3
    omega
  rw [hy_eq] at h8 h10
  omega

theorem ten_le_rk_of_isIrrOn {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {M : Subgroup (MulAut V)} {I : Subgroup V}
    (hirr : IsIrrOn M I ⊥) (hfaith : M ⊓ centSub I = ⊥) (h11 : 11 ∣ Nat.card ↥M) :
    10 ≤ rk I := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hMI : M ≤ stabSub I := le_stabSub_of_stableUnder hirr.2.1
  obtain ⟨mL, hmord⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 11 h11
  have hyI : ((mL : ↥M) : MulAut V) ∈ stabSub I := hMI mL.2
  have hyne : ((mL : ↥M) : MulAut V) ∉ centSub I := by
    intro hc
    have hmem : ((mL : ↥M) : MulAut V) ∈ M ⊓ centSub I := ⟨mL.2, hc⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    have h1 : mL = 1 := Subtype.ext hmem
    rw [h1, orderOf_one] at hmord
    omega
  have hy11 : orderOf ((mL : ↥M) : MulAut V) = 11 := by
    rw [Subgroup.orderOf_coe, hmord]
  have h10 := ten_le_rk_commSub_of_orderOf_eleven hV hyI hy11 hyne
  have hle : commSub I (Subgroup.zpowers ((mL : ↥M) : MulAut V)) ≤ I :=
    commSub_le_of_invariant (fun x hx w hw =>
      stabSub_apply_mem (Subgroup.zpowers_le.mpr hyI hx) hw)
  exact le_trans h10 (rk_mono hle)

theorem six_le_mParam_of_M22
    {W : Type} [CommGroup W] [Finite W] (hw : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hN : (L.subgroupOf Y).Normal)
    (hSpor : IsSpor ↥L .M22) (hfix : fixV L = ⊥)
    (hss : (⨆ I ∈ irrSet L, I) = ⊤) (hnirr : ¬ IsIrrOn L ⊤ ⊥) :
    6 ≤ E3.mParam Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSporL : IsSpor ↥L .M22 := hSpor
  obtain ⟨eL⟩ := hSpor
  have hcardL : Nat.card ↥L = 443520 := by
    rw [← CFSG.Sporadic.Mathieu.card_M22]
    exact Nat.card_congr eL.toEquiv
  have hLsimple : IsSimpleGroup ↥L :=
    (MulEquiv.isSimpleGroup_congr eL).mpr CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hWnt : Nontrivial W := by
    by_contra hnt
    have hsub : Subsingleton W := not_nontrivial_iff_subsingleton.mp hnt
    have : Subsingleton (MulAut W) := ⟨fun a b => MulEquiv.ext fun w => hsub.elim (a w) (b w)⟩
    have hLbot : L = ⊥ := Subgroup.eq_bot_of_subsingleton L
    rw [hLbot, Subgroup.card_bot] at hcardL
    norm_num at hcardL
  have : Nontrivial W := hWnt
  have hNLY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hN
  have hex : ∃ I₁ ∈ irrSet L, ∃ I₂ ∈ irrSet L, I₁ ≠ I₂ := by
    by_contra h
    push Not at h
    rcases Set.eq_empty_or_nonempty (irrSet L) with hemp | ⟨I₀, hI₀⟩
    · have hbot : (⊤ : Subgroup W) = ⊥ := by
        rw [← hss, hemp]
        simp
      have hsingle : Subsingleton W := by
        refine ⟨fun a b => ?_⟩
        have ha : a ∈ (⊥ : Subgroup W) := hbot ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup W) := hbot ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      exact (not_subsingleton_iff_nontrivial.mpr hWnt) hsingle
    · have hset : irrSet L = {I₀} := by
        ext J
        constructor
        · intro hJ
          rw [Set.mem_singleton_iff]
          exact h J hJ I₀ hI₀
        · intro hJ
          rw [Set.mem_singleton_iff] at hJ
          rwa [hJ]
      have hss' : I₀ = ⊤ := by
        rw [hset] at hss
        simpa using hss
      have hirr₀ : IsIrrOn L I₀ ⊥ := by
        have h' := hI₀.2
        rwa [hfix, inf_bot_eq] at h'
      refine hnirr ?_
      rwa [← hss']
  obtain ⟨I₁, hI₁, I₂, hI₂, hne⟩ := hex
  have hirr_of : ∀ I ∈ irrSet L, IsIrrOn L I ⊥ := by
    intro I hI
    have h := hI.2
    rwa [hfix, inf_bot_eq] at h
  have hMI_of : ∀ I ∈ irrSet L, L ≤ stabSub I := fun I hI =>
    le_stabSub_of_stableUnder (hirr_of I hI).2.1
  have hfaith_of : ∀ I ∈ irrSet L, L ⊓ centSub I = ⊥ := by
    intro I hI
    have hirr := hirr_of I hI
    have hne' : ¬ L ≤ centSub I := by
      intro hc
      have hIle : I ≤ fixV L := by
        intro w hw'
        rw [mem_fixV]
        intro l hl
        exact mem_centSub.mp (hc hl) w hw'
      have hIbot : I = ⊥ := le_bot_iff.mp (hIle.trans (le_of_eq hfix))
      exact (ne_bot_of_gt hirr.1) hIbot
    exact CFSG.Quasithin.inf_centSub_eq_bot_of_isSimpleGroup hLsimple (hMI_of I hI) hne'
  have h11L : 11 ∣ Nat.card ↥L := by rw [hcardL]; norm_num
  have hdisj : I₁ ⊓ I₂ = ⊥ := by
    have h1 := hirr_of I₁ hI₁
    have h2 := hirr_of I₂ hI₂
    have hstab : StableUnder L (I₁ ⊓ I₂) := by
      intro l hl w hw'
      exact ⟨h1.2.1 l hl w hw'.1, h2.2.1 l hl w hw'.2⟩
    rcases h1.2.2.2 (I₁ ⊓ I₂) hstab bot_le inf_le_left with h | h
    · exact h
    · exfalso
      apply hne
      have hle : I₁ ≤ I₂ := h.ge.trans inf_le_right
      rcases h2.2.2.2 I₁ h1.2.1 bot_le hle with h' | h'
      · exact absurd h' (ne_bot_of_gt h1.1)
      · exact h'
  have hall : ∀ s ∈ Y, orderOf s = 2 → 6 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
    intro s hsY hs2
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hs2
      omega
    have hsst : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
    have hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)) := hNLY hsY
    have hsNi : s⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hsN
    have hsNi' : ∀ l ∈ L, s⁻¹ * l * s ∈ L := fun l hl =>
      (Subgroup.mem_normalizer_iff.mp hsNi l).mp hl
    by_cases hmove : ∃ I ∈ irrSet L, I.map s.toMonoidHom ≠ I
    ·
      obtain ⟨I, hI, hImap⟩ := hmove
      have hirr := hirr_of I hI
      have hmap_of_stab : s ∈ stabSub I → I.map s.toMonoidHom = I := by
        intro hsstab
        ext w
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact (mem_stabSub.mp hsstab u).mpr hu
        · intro hw'
          exact ⟨s⁻¹ w, (mem_stabSub.mp ((stabSub I).inv_mem hsstab) w).mpr hw', by
            simpa using MulAut.apply_inv_self W s w⟩
      have hnotstab : s ∉ stabSub I := fun hsstab => hImap (hmap_of_stab hsstab)
      have hLI : StableUnder L (I.map s.toMonoidHom) := by
        intro l hl w hw'
        obtain ⟨u, hu, rfl⟩ := hw'
        refine ⟨(s⁻¹ * l * s) u, stabSub_apply_mem (hMI_of I hI (hsNi' l hl)) hu, ?_⟩
        show s ((s⁻¹ * l * s) u) = l (s u)
        rw [← MulAut.mul_apply, ← MulAut.mul_apply,
          show s * (s⁻¹ * l * s) = l * s from by group]
      have hdisjI : I ⊓ I.map s.toMonoidHom = ⊥ := by
        have hstabI : StableUnder L (I ⊓ I.map s.toMonoidHom) := by
          intro l hl w hw'
          exact ⟨hirr.2.1 l hl w hw'.1, hLI l hl w hw'.2⟩
        rcases hirr.2.2.2 (I ⊓ I.map s.toMonoidHom) hstabI bot_le inf_le_left with h | h
        · exact h
        · exfalso
          apply hnotstab
          have hle : I ≤ I.map s.toMonoidHom := h.ge.trans inf_le_right
          have hcard : Nat.card ↥(I.map s.toMonoidHom) = Nat.card ↥I :=
            Subgroup.card_map_of_injective (MulEquiv.injective s)
          have heq : I = I.map s.toMonoidHom :=
            Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
          exact CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq heq.symm
      have h10 : 10 ≤ rk I := ten_le_rk_of_isIrrOn hw hirr (hfaith_of I hI) h11L
      have hcardmap : rk (I.map s.toMonoidHom) = rk I := by
        unfold rk
        rw [Subgroup.card_map_of_injective (MulEquiv.injective s)]
      have hswap : rk (I.map s.toMonoidHom) ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
        refine CFSG.Quasithin.A6Amt.rk_le_rkIdx_of_swap (W₁ := I)
          (W₂ := I.map s.toMonoidHom) hdisjI ?_
        intro w hw'
        obtain ⟨u, hu, rfl⟩ := hw'
        show s (s u) ∈ I
        rw [← MulAut.mul_apply, hsst, MulAut.one_apply]
        exact hu
      omega
    ·
      push Not at hmove
      have hstab : ∀ I ∈ irrSet L, s ∈ stabSub I := fun I hI =>
        CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq (hmove I hI)
      have hne' : ∀ I ∈ irrSet L, ∃ w ∈ I, s w ≠ w := by
        intro I hI
        by_contra hcon
        push Not at hcon
        have hfaithpt : ∀ m ∈ L, (∀ w ∈ I, m w = w) → m = 1 := by
          intro m hm hfixm
          have hmem : m ∈ L ⊓ centSub I := ⟨hm, mem_centSub.mpr hfixm⟩
          rw [hfaith_of I hI, Subgroup.mem_bot] at hmem
          exact hmem
        have hcent : ∀ l ∈ L, s * l = l * s :=
          commute_of_fix_on_faithful (hMI_of I hI) hfaithpt hsN hcon
        have htop : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers s) := by
          rw [← hss]
          refine iSup₂_le fun J hJ w hw' => ?_
          exact (mem_fixV_zpowers_iff (g := s)).mpr
            (eqOn_of_commute_of_isIrrOn hw (hirr_of J hJ) hsst (hstab J hJ) hcent w hw')
        exact hs1 (eq_one_of_fixV_eq_top (top_le_iff.mp htop))
      have hβne_of : ∀ {I : Subgroup W}, I ∈ irrSet L → ∃ m ∈ L, s * m * s⁻¹ ≠ m := by
        intro I hI
        by_contra hcon
        push Not at hcon
        have hcent : ∀ l ∈ L, s * l = l * s := by
          intro l hl
          have h := hcon l hl
          rwa [mul_inv_eq_iff_eq_mul] at h
        obtain ⟨w, hw', hnew⟩ := hne' I hI
        exact hnew (eqOn_of_commute_of_isIrrOn hw (hirr_of I hI) hsst (hstab I hI) hcent w hw')
      have h3₁ : 3 ≤ rk (commSub I₁ (Subgroup.zpowers s)) :=
        three_le_commSub_of_isSpor_M22 hw hSporL (hMI_of I₁ hI₁) (hfaith_of I₁ hI₁) hs2
          (hstab I₁ hI₁) hsN (hβne_of hI₁)
      have h3₂ : 3 ≤ rk (commSub I₂ (Subgroup.zpowers s)) :=
        three_le_commSub_of_isSpor_M22 hw hSporL (hMI_of I₂ hI₂) (hfaith_of I₂ hI₂) hs2
          (hstab I₂ hI₂) hsN (hβne_of hI₂)
      have hle₁ : commSub I₁ (Subgroup.zpowers s) ≤ I₁ :=
        commSub_le_of_invariant (fun x hx w hw' =>
          stabSub_apply_mem (Subgroup.zpowers_le.mpr (hstab I₁ hI₁) hx) hw')
      have hle₂ : commSub I₂ (Subgroup.zpowers s) ≤ I₂ :=
        commSub_le_of_invariant (fun x hx w hw' =>
          stabSub_apply_mem (Subgroup.zpowers_le.mpr (hstab I₂ hI₂) hx) hw')
      have hdisj' : commSub I₁ (Subgroup.zpowers s) ⊓ commSub I₂ (Subgroup.zpowers s) = ⊥ := by
        rw [eq_bot_iff, ← hdisj]
        exact inf_le_inf hle₁ hle₂
      have hsum : rk ↥(commSub I₁ (Subgroup.zpowers s) ⊔ commSub I₂ (Subgroup.zpowers s)) =
          rk (commSub I₁ (Subgroup.zpowers s)) + rk (commSub I₂ (Subgroup.zpowers s)) :=
        CFSG.Quasithin.A6Amt.rk_sup_of_inf_eq_bot hdisj'
      have hsup : commSub I₁ (Subgroup.zpowers s) ⊔ commSub I₂ (Subgroup.zpowers s) ≤
          commSub (⊤ : Subgroup W) (Subgroup.zpowers s) :=
        sup_le (commSub_mono (W := I₁) (W' := ⊤) (X := Subgroup.zpowers s)
          (X' := Subgroup.zpowers s) le_top le_rfl)
          (commSub_mono (W := I₂) (W' := ⊤) (X := Subgroup.zpowers s)
            (X' := Subgroup.zpowers s) le_top le_rfl)
      have hkey : rkIdx (fixV (Subgroup.zpowers s)) =
          rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers s)) := by
        rw [rkIdx_fixV_zpowers, commV_eq_commSub]
      rw [hkey]
      have hmono := rk_mono hsup
      omega
  refine CFSG.Quasithin.H.Mathieu.le_mParam_of (V := W) (M := Y) (b := 6) ?_ hall
  have hb₁ : 10 ≤ rk I₁ := ten_le_rk_of_isIrrOn hw (hirr_of I₁ hI₁) (hfaith_of I₁ hI₁) h11L
  have hb₂ : 10 ≤ rk I₂ := ten_le_rk_of_isIrrOn hw (hirr_of I₂ hI₂) (hfaith_of I₂ hI₂) h11L
  have hsum : rk ↥(I₁ ⊔ I₂) = rk I₁ + rk I₂ := CFSG.Quasithin.A6Amt.rk_sup_of_inf_eq_bot hdisj
  have hle : rk ↥(I₁ ⊔ I₂) ≤ rk W := by
    have h := rk_mono (le_top : I₁ ⊔ I₂ ≤ (⊤ : Subgroup W))
    rwa [rk_top] at h
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
