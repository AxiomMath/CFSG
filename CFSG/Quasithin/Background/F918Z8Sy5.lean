module

public import CFSG.Quasithin.Background.F918Z8Sy2
public import CFSG.Quasithin.Background.F918Z8Sy3
public import CFSG.Quasithin.Background.F918Z8Sy4
public import CFSG.Quasithin.Background.F918Z8Sz8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem asB42_vals (hB42 : AsB42) (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (G L : Subgroup (MulAut V)) (hHyp : B4Hyp G L) (hq : qhatOf G ≤ ((1 / 2 : ℚ) : WithTop ℚ)) :
    (∃ n, BinaryNaturalSL L ⊤ ⊥ 3 n ∧ qhatOf G = ((1 / 2 : ℚ) : WithTop ℚ)) ∨
      (BinaryNaturalSL L ⊤ ⊥ 4 1 ∧ qhatOf G = ((1 / 3 : ℚ) : WithTop ℚ)) ∨
      (BinaryNaturalSL L ⊤ ⊥ 5 1 ∧ qhatOf G = ((1 / 4 : ℚ) : WithTop ℚ)) := by
  have hq1 : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := hq.trans (by exact_mod_cast (by norm_num))
  obtain ⟨A₀, hA₀, -, hr⟩ := kq_le_iff.1 hq
  obtain ⟨F, -, hF, hFq, hrF⟩ := exists_quadratic_below_ratio hV hA₀ (hr.trans (by norm_num))
  have hqF : qOf G ≤ ((1 / 2 : ℚ) : WithTop ℚ) := qOf_le_iff.2 ⟨F, hF.isA2, hFq, hrF.trans hr⟩
  have hnot : ∀ c : ℚ, 1 / 2 < c → qOf G = (c : WithTop ℚ) → False := fun c hc h => by
    rw [h] at hqF
    exact absurd (WithTop.coe_le_coe.1 hqF) (not_le.2 hc)
  have heq := qhatOf_eq_qOf_of_le_one hV hq1
  rcases hB42 V hV G L hHyp F hF with h | h | h | h | h | h | h | h | h | h | h
  · exact absurd h.2.2.2 (fun h' => hnot 1 (by norm_num) h')
  · exact Or.inl (by
      obtain ⟨-, ⟨n, hn⟩, hq2⟩ := h
      exact ⟨n, hn, heq.trans hq2⟩)
  · exact absurd h.2 (fun h' => hnot (2 / 3) (by norm_num) h')
  · exact absurd h.2 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2.2.2.1 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2.2.2.2.1 (fun h' => hnot 1 (by norm_num) h')
  · exact absurd h.2.2.1 (fun h' => hnot 1 (by norm_num) h')
  · obtain ⟨-, n, hn, hnat, hq9⟩ := h
    rcases hn with rfl | rfl
    · refine Or.inr (Or.inl ⟨hnat, ?_⟩)
      rw [heq, hq9]
      norm_num
    · refine Or.inr (Or.inr ⟨hnat, ?_⟩)
      rw [heq, hq9]
      norm_num
  · rcases h.2 with h' | h'
    · exact absurd h'.2.2.2 (fun h'' => hnot 1 (by norm_num) h'')
    · exact absurd h'.2.2 (fun h'' => hnot (3 / 4) (by norm_num) h'')
  · exact absurd h.2.2.2.1 (fun h' => hnot 1 (by norm_num) h')


section Helpers

variable {Y : Type} [CommGroup Y] [Finite Y]

omit [Finite Y] in
theorem sxi_nt_sub {X A : Subgroup (MulAut Y)}
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y))) {t : MulAut Y}
    (htX : ∀ x ∈ X, t * x = x * t) {I J I₀ : Subgroup Y} (hJI₀ : J < I₀) (hI₀I : I₀ ≤ I)
    (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J) (hAJ : A ≤ stabSub J)
    (htJ : ∀ w ∈ J, t w ∈ J)
    (hirrΞ : ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) →
      (∀ a ∈ A, ∀ s ∈ T, a s ∈ T) → (∀ s ∈ T, t s ∈ T) → T = J ∨ T = I)
    (hnt : ∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J) (hAI : A ≤ stabSub I)
    (htI : ∀ w ∈ I, t w ∈ I) :
    ∃ x ∈ X, ∃ w ∈ I₀, x w * w⁻¹ ∉ J := by
  by_contra hcon
  push Not at hcon
  let Z : Subgroup Y :=
    { carrier := {i | i ∈ I ∧ ∀ x ∈ X, x i * i⁻¹ ∈ J}
      one_mem' := ⟨I.one_mem, fun x _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨I.mul_mem ha.1 hb.1, fun x hx => by
        have h := J.mul_mem (ha.2 x hx) (hb.2 x hx)
        have e : x (a * b) * (a * b)⁻¹ = x a * a⁻¹ * (x b * b⁻¹) := by
          rw [map_mul, mul_inv_rev]; ac_rfl
        rw [e]; exact h⟩
      inv_mem' := fun {a} ha => ⟨I.inv_mem ha.1, fun x hx => by
        have h := J.inv_mem (ha.2 x hx)
        have e : x a⁻¹ * (a⁻¹)⁻¹ = (x a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
        rw [e]; exact h⟩ }
  have hJZ : J ≤ Z := fun j hj => ⟨(hJI₀.le.trans hI₀I) hj, fun x hx => by
    exact J.mul_mem ((hXJ hx j).2 hj) (J.inv_mem hj)⟩
  have hZI : Z ≤ I := fun z hz => hz.1
  have hXZ : ∀ x' ∈ X, ∀ s ∈ Z, x' s ∈ Z := by
    intro x' hx' s hs
    refine ⟨(hXI hx' s).2 hs.1, fun x hx => ?_⟩
    have h := J.mul_mem (hs.2 (x * x') (X.mul_mem hx hx')) (J.inv_mem (hs.2 x' hx'))
    have e : x (x' s) * (x' s)⁻¹ = (x * x') s * s⁻¹ * (x' s * s⁻¹)⁻¹ := by
      show x (x' s) * (x' s)⁻¹ = x (x' s) * s⁻¹ * (x' s * s⁻¹)⁻¹
      group
    rw [e]; exact h
  have hAZ : ∀ a ∈ A, ∀ s ∈ Z, a s ∈ Z := by
    intro a ha s hs
    refine ⟨(hAI ha s).2 hs.1, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 (hAX (A.inv_mem ha)) x).1 hx
      simpa using this
    have e0 : x * a = a * (a⁻¹ * x * a) := by group
    have e1 : x (a s) = a ((a⁻¹ * x * a) s) := by
      calc x (a s) = (x * a) s := rfl
        _ = (a * (a⁻¹ * x * a)) s := by rw [e0]
        _ = a ((a⁻¹ * x * a) s) := rfl
    have e2 : x (a s) * (a s)⁻¹ = a ((a⁻¹ * x * a) s * s⁻¹) := by
      rw [e1, map_mul, map_inv]
    rw [e2]
    exact (hAJ ha _).2 (hs.2 _ hx')
  have htZ : ∀ s ∈ Z, t s ∈ Z := by
    intro s hs
    refine ⟨htI s hs.1, fun x hx => ?_⟩
    have e : x (t s) * (t s)⁻¹ = t (x s * s⁻¹) := by
      have : x (t s) = t (x s) := by
        calc x (t s) = (x * t) s := rfl
          _ = (t * x) s := by rw [htX x hx]
          _ = t (x s) := rfl
      rw [this, map_mul, map_inv]
    rw [e]
    exact htJ _ (hs.2 x hx)
  rcases hirrΞ Z hJZ hZI hXZ hAZ htZ with h | h
  · apply hJI₀.not_ge
    intro i hi
    have : i ∈ Z := ⟨hI₀I hi, fun x hx => hcon x hx i hi⟩
    rw [h] at this
    exact this
  · obtain ⟨x, hx, w, hw, hne⟩ := hnt
    have : w ∈ Z := by rw [h]; exact hw
    exact hne (this.2 x hx)

theorem sxi_rk_autSec_add {A : Subgroup (MulAut Y)} {I J : Subgroup Y} (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) : rk (autSec A I J) + rk ↥(A ⊓ centSec I J) = rk A := by
  have := card_autSec_mul hAI hAJ
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', this]

theorem sxi_qhat_le {X A : Subgroup (MulAut Y)} (hAel : IsElemAbelian2 A) {M I J : Subgroup Y}
    (hIM : I ≤ M) (hAM : A ≤ stabSub M) (hAI : A ≤ stabSub I)
    (hcubic : commSeries A 3 = ⊥) (hne : autSec A I J ≠ ⊥) :
    qhatOf (autSec (X ⊔ A) I J) ≤ ((rAV (autSec A I J) : ℚ) : WithTop ℚ) := by
  have hA2 : IsA2 (autSec (X ⊔ A) I J) (autSec A I J) :=
    ⟨autSec_mono le_sup_right I J, hne, isElemAbelian2_autSec I J hAel⟩
  exact kq_le_iff.2 ⟨autSec A I J, hA2,
    commSeries_autSec_eq_bot_of_autSub hIM hAM hAI (commSeries_autSub_eq_bot hAM hcubic), le_rfl⟩

theorem sxi_num_a {j ρ n₁ a₁ ν : ℕ} (hj : 1 ≤ j) (hρ : 1 ≤ ρ)
    (h1 : (2 ^ j - 1) * ρ + n₁ ≤ ν) (h2 : 2 * ν ≤ a₁ + j) : 2 * n₁ < a₁ := by
  have hs : j < 2 ^ j := Nat.lt_two_pow_self
  have hs2 : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have h3 : 2 ^ j - 1 ≤ (2 ^ j - 1) * ρ := Nat.le_mul_of_pos_right _ hρ
  omega

theorem sxi_num_b {j ρ n₁ a₁ ν : ℕ} (hj : 1 ≤ j) (h1 : (2 ^ j - 1) * ρ + n₁ ≤ ν)
    (h2 : 2 * ν ≤ a₁ + j) (hρ : (ρ = 4 ∧ a₁ ≤ 6) ∨ (ρ = 5 ∧ a₁ ≤ 10)) (hn₁ : 1 ≤ n₁) : False := by
  have hs : j < 2 ^ j := Nat.lt_two_pow_self
  have hs2 : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  rcases hρ with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

end Helpers

theorem suzXirr_proved (hB42 : AsB42) (hA21 : AsA21SQTKSection) : SuzXirr := by
  intro Y _ _ Γ Λ S V A X K W d hXK n P t hn3 hnodd hP htΛ htN htord hfree hrat I J hJI hIM hXI
    hXJ hAI hAJ htI htJ hirrΞ hnt hfaith T hJT hTI hXT
  by_contra hcon
  have hTJ : T ≠ J := fun h => hcon (Or.inl h)
  have hTI' : T ≠ I := fun h => hcon (Or.inr h)
  set M : Subgroup Y := W ⊓ fixV P with hMdef
  have hq : CFSG.Open.IsQuasisimple ↥X := hXK ▸ d.hKc.2.2
  have hXq : CFSG.IsQuasisimple ↥X := hXK ▸ B1Red.isQuasisimple_of_open d.hKc.2.2
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec d.hA
  have hAΓ : A ≤ Γ := hA2.1
  have hAel : IsElemAbelian2 A := hA2.2.2
  have hPΛ : P ≤ Λ := hP.1
  have hAM : A ≤ stabSub M :=
    chief_quarter_stable (fun ξ hξ x hx => d.hAc ξ hξ x (hPΛ hx)) d.hWA
  have htX : ∀ x ∈ X, t * x = x * t := fun x hx => (d.hXc x hx t htΛ).symm
  have htA : ∀ a ∈ A, t * a = a * t := fun a ha => (d.hAc a ha t htΛ).symm
  have hexp := d.loc.std.hyp.exp
  have hnotA : ¬ A ≤ centSec I J := by
    intro hAc
    have hXc := X_trivial_of_A_trivial d.hXA hXI hXJ hAc
    obtain ⟨x, hx, w, hw, hne⟩ := hnt
    exact hne ((hXc hx).2 w hw)
  have hpos : 0 < rk (autSub A M) := by
    have hne := autSec_ne_bot_of_not_le hAI hAJ hnotA
    have h1 := (isElemAbelian2_autSec I J hAel).rk_pos hne
    rwa [rk_autSec_eq_rk_autSub hAM hAI hAJ hfaith] at h1
  have h2nM : 2 * rkIdx (fixV (autSub A M)) ≤ rk (autSub A M) := by
    have h := hrat
    unfold rAV at h
    rw [div_le_iff₀ (by exact_mod_cast hpos)] at h
    have : (2 * rkIdx (fixV (autSub A M)) : ℚ) ≤ rk (autSub A M) := by linarith
    exact_mod_cast this
  have hνM := rkIdx_fixV_autSec_le hJI.le hIM hAM hAI
  obtain ⟨I₀, A₁, hJI₀, hI₀I, hXI₀, hirr₀, hA₁A, hA₁I₀, hA₁full, hcases⟩ :=
    sxi_clifford hexp hAel d.hAX htX htA hJI hXI hXJ hAI hAJ htI htJ hirrΞ
      ⟨T, hJT, hTI, hXT, hTJ, hTI'⟩
  have hI₀M : I₀ ≤ M := hI₀I.trans hIM
  have hA₁J : A₁ ≤ stabSub J := hA₁A.trans hAJ
  have hAel₁ : IsElemAbelian2 A₁ :=
    ⟨fun a ha b hb => hAel.1 a (hA₁A ha) b (hA₁A hb), fun a ha => hAel.2 a (hA₁A ha)⟩
  have hAM₁ : A₁ ≤ stabSub M := hA₁A.trans hAM
  have hA₃ : commSeries A₁ 3 = ⊥ := le_bot_iff.1 (hA3 ▸ commSeries_mono hA₁A 3)
  have hnt₀ := sxi_nt_sub d.hAX htX hJI₀ hI₀I hXI hXJ hAJ htJ hirrΞ hnt hAI htI
  have hker : A₁ ⊓ centSec I₀ J = A ⊓ centSub M := by
    refine le_antisymm ?_ ?_
    · intro a ha
      have hcomm := chief_faithful_aux hq hXI₀ hXJ (hA₁A.trans d.hAX) hnt₀ a ha
      exact ⟨hA₁A ha.1, fun u hu => d.hBW a (hA₁A ha.1) (fun x hx => hcomm x hx) u hu.1⟩
    · intro a ha
      have hst : a ∈ stabSub I₀ := centSub_le_stabSub I₀ (fun u hu => ha.2 u (hI₀M hu))
      exact ⟨hA₁full a ha.1 hst, hst, fun w hw => by rw [ha.2 w (hI₀M hw)]; simp⟩
  have hrk1 : rk (autSec A₁ I₀ J) + rk ↥(A ⊓ centSub M) = rk A₁ := by
    have := sxi_rk_autSec_add hA₁I₀ hA₁J
    rwa [hker] at this
  have hrkA : rk (autSub A M) + rk ↥(A ⊓ centSub M) = rk A := rk_autSub_add_rk_inf hAM
  have hrkle : rk A₁ ≤ rk A := rk_mono hA₁A
  have hexp₀ : ∀ v : Sec I₀ J, v ^ 2 = 1 := sq_eq_one_sec hexp I₀ J
  have hyp : B4Hyp (autSec (X ⊔ A₁) I₀ J) (autSec X I₀ J) :=
    suz_b4hyp hA21 d.loc.std.hyp.qsqtk hexp d.hXΓ (hA₁A.trans hAΓ) hXq hAel₁
      (hA₁A.trans d.hAX) hJI₀.le hXI₀ hXJ hA₁I₀ hA₁J hirr₀ hnt₀
  have hρpos : 1 ≤ rk (Sec I₀ J) := by
    have h1 := rk_sec_add_gen hJI₀.le
    by_contra h0
    have h00 : rk (Sec I₀ J) = 0 := by omega
    have : rk I₀ ≤ rk J := by omega
    exact hJI₀.ne (eq_of_le_of_rk_le hexp hJI₀.le this)
  have hratio : ∀ (hne : autSec A₁ I₀ J ≠ ⊥),
      qhatOf (autSec (X ⊔ A₁) I₀ J) ≤
        (((rkIdx (fixV (autSec A₁ I₀ J)) : ℚ) / (rk (autSec A₁ I₀ J) : ℚ) : ℚ) : WithTop ℚ) :=
    fun hne => sxi_qhat_le hAel₁ hI₀M hAM₁ hA₁I₀ hA₃ hne
  have hlow : ∀ (hne : autSec A₁ I₀ J ≠ ⊥) (c : ℚ),
      qhatOf (autSec (X ⊔ A₁) I₀ J) = (c : WithTop ℚ) →
        c * (rk (autSec A₁ I₀ J) : ℚ) ≤ (rkIdx (fixV (autSec A₁ I₀ J)) : ℚ) := by
    intro hne c hc
    have ha₁pos : 0 < rk (autSec A₁ I₀ J) := (isElemAbelian2_autSec I₀ J hAel₁).rk_pos hne
    have h := hratio hne
    rw [hc] at h
    have h' := WithTop.coe_le_coe.1 h
    rwa [le_div_iff₀ (by exact_mod_cast ha₁pos)] at h'
  have hhalf : ∀ (hne : autSec A₁ I₀ J ≠ ⊥),
      2 * rkIdx (fixV (autSec A₁ I₀ J)) ≤ rk (autSec A₁ I₀ J) →
        qhatOf (autSec (X ⊔ A₁) I₀ J) ≤ ((1 / 2 : ℚ) : WithTop ℚ) := by
    intro hne h2
    have ha₁pos : 0 < rk (autSec A₁ I₀ J) := (isElemAbelian2_autSec I₀ J hAel₁).rk_pos hne
    refine (hratio hne).trans (WithTop.coe_le_coe.2 ?_)
    rw [div_le_iff₀ (by exact_mod_cast ha₁pos)]
    have : (2 * rkIdx (fixV (autSec A₁ I₀ J)) : ℚ) ≤ rk (autSec A₁ I₀ J) := by exact_mod_cast h2
    linarith
  rcases hcases with ⟨hA₁eq, hI₀I', hdouble⟩ | ⟨hA₁lt, hcount⟩
  ·
    subst A₁
    have ha₁ : rk (autSec A I₀ J) = rk (autSub A M) := by omega
    have hne : autSec A I₀ J ≠ ⊥ := by
      intro h
      rw [h, rk_bot] at ha₁
      omega
    have h4 : 2 * rkIdx (fixV (autSec A I₀ J)) ≤ rk (autSec A I₀ J) := by omega
    have hqle := hhalf hne h4
    rcases asB42_vals hB42 (Sec I₀ J) hexp₀ _ _ hyp hqle with
      ⟨m, -, hq2⟩ | ⟨-, hq3⟩ | ⟨hnat, hq4⟩
    · have h1 := hlow hne _ hq2
      have h5 : (rk (autSec A I₀ J) : ℚ) ≤ 2 * (rkIdx (fixV (autSec A I₀ J)) : ℚ) := by linarith
      have h6 : rk (autSec A I₀ J) ≤ 2 * rkIdx (fixV (autSec A I₀ J)) := by exact_mod_cast h5
      have h7 : 4 * rkIdx (fixV (autSec A I₀ J)) ≤ rk (autSec A I₀ J) := by omega
      have ha₁pos : 0 < rk (autSec A I₀ J) := by omega
      omega
    · have h1 := hlow hne _ hq3
      have h5 : (rk (autSec A I₀ J) : ℚ) ≤ 3 * (rkIdx (fixV (autSec A I₀ J)) : ℚ) := by linarith
      have h6 : rk (autSec A I₀ J) ≤ 3 * rkIdx (fixV (autSec A I₀ J)) := by exact_mod_cast h5
      have h7 : 4 * rkIdx (fixV (autSec A I₀ J)) ≤ rk (autSec A I₀ J) := by omega
      have ha₁pos : 0 < rk (autSec A I₀ J) := by omega
      omega
    · have h1 := hlow hne _ hq4
      have h5 : (rk (autSec A I₀ J) : ℚ) ≤ 4 * (rkIdx (fixV (autSec A I₀ J)) : ℚ) := by linarith
      have h6 : rk (autSec A I₀ J) ≤ 4 * rkIdx (fixV (autSec A I₀ J)) := by exact_mod_cast h5
      have hν : rkIdx (fixV (autSec A I J)) = 2 * rkIdx (fixV (autSec A I₀ J)) := by omega
      have ha4 : rk (autSec A I₀ J) = 4 * rkIdx (fixV (autSec A I₀ J)) := by omega
      have hdiv := sxi_div hexp (by omega : 2 ≤ n) htord hJI.le hIM htI htJ hfree htA hAI hAJ
      rw [hν] at hdiv
      have hcop : Nat.Coprime n 2 := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
        omega
      have hdiv1 : n ∣ rkIdx (fixV (autSec A I₀ J)) := hcop.dvd_of_dvd_mul_left hdiv
      have hn1pos : 0 < rkIdx (fixV (autSec A I₀ J)) := by omega
      have hle := Nat.le_of_dvd hn1pos hdiv1
      obtain ⟨-, hrank⟩ := sxi_rank_natural (X := X) (A := A) hnat hAel hA₁I₀ hA₁J
      omega
  ·
    have hj : 1 ≤ rk A - rk A₁ := by
      by_contra h0
      have hge : rk A ≤ rk A₁ := by omega
      have hc : Nat.card ↥A ≤ Nat.card ↥A₁ := by
        rw [card_eq_two_pow_of_isPGroup hAel.isPGroup,
          card_eq_two_pow_of_isPGroup hAel₁.isPGroup]
        exact Nat.pow_le_pow_right (by norm_num) hge
      exact hA₁lt.ne (Subgroup.eq_of_le_of_card_ge hA₁A hc)
    have h2' : 2 * rkIdx (fixV (autSec A I J)) ≤ rk (autSec A₁ I₀ J) + (rk A - rk A₁) := by
      omega
    have hlt := sxi_num_a hj hρpos hcount h2'
    have hne : autSec A₁ I₀ J ≠ ⊥ := by
      intro h
      rw [h, rk_bot] at hlt
      omega
    have hqle := hhalf hne hlt.le
    rcases asB42_vals hB42 (Sec I₀ J) hexp₀ _ _ hyp hqle with
      ⟨m, -, hq2⟩ | ⟨hnat, hq3⟩ | ⟨hnat, hq4⟩
    · have h1 := hlow hne _ hq2
      have h5 : (rk (autSec A₁ I₀ J) : ℚ) ≤ 2 * (rkIdx (fixV (autSec A₁ I₀ J)) : ℚ) := by
        linarith
      have h6 : rk (autSec A₁ I₀ J) ≤ 2 * rkIdx (fixV (autSec A₁ I₀ J)) := by exact_mod_cast h5
      omega
    · have h1 := hlow hne _ hq3
      have h5 : (rk (autSec A₁ I₀ J) : ℚ) ≤ 3 * (rkIdx (fixV (autSec A₁ I₀ J)) : ℚ) := by
        linarith
      have h6 : rk (autSec A₁ I₀ J) ≤ 3 * rkIdx (fixV (autSec A₁ I₀ J)) := by exact_mod_cast h5
      obtain ⟨hρ, hrank⟩ := sxi_rank_natural (X := X) (A := A₁) hnat hAel₁ hA₁I₀ hA₁J
      have hn₁ : 1 ≤ rkIdx (fixV (autSec A₁ I₀ J)) := by omega
      rw [hρ] at hcount
      exact sxi_num_b hj hcount h2' (Or.inl ⟨rfl, by omega⟩) hn₁
    · have h1 := hlow hne _ hq4
      have h5 : (rk (autSec A₁ I₀ J) : ℚ) ≤ 4 * (rkIdx (fixV (autSec A₁ I₀ J)) : ℚ) := by
        linarith
      have h6 : rk (autSec A₁ I₀ J) ≤ 4 * rkIdx (fixV (autSec A₁ I₀ J)) := by exact_mod_cast h5
      obtain ⟨hρ, hrank⟩ := sxi_rank_natural (X := X) (A := A₁) hnat hAel₁ hA₁I₀ hA₁J
      have hn₁ : 1 ≤ rkIdx (fixV (autSec A₁ I₀ J)) := by omega
      rw [hρ] at hcount
      exact sxi_num_b hj hcount h2' (Or.inr ⟨rfl, by omega⟩) hn₁


end CFSG.Quasithin
