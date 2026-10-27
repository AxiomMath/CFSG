module

public import CFSG.Quasithin.EmptyFaithful.S153ZD
public import CFSG.Quasithin.EmptyFaithful.S153ZP
public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.Background.F918N1
public import CFSG.Quasithin.EmptyFaithful.S153ZA
public import CFSG.Quasithin.EmptyFaithful.S153ZC
public import CFSG.Quasithin.EmptyFaithful.S153ZN
public import CFSG.Quasithin.EmptyFaithful.S153ZO

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

namespace Z391

variable {W : Type} [CommGroup W]

theorem q_mul_rk_le [Finite W] {G A : Subgroup (MulAut W)} {V U : Subgroup W} (hA : IsA2 G A)
    (hA3 : commSeries A 3 = ⊥) (hAV : A ≤ stabSub V) (hAU : A ≤ stabSub U) (hf : A ⊓ centSec V U = ⊥)
    {q : ℚ} (hq : (q : WithTop ℚ) = qhatOf (autSec G V U)) :
    q * (rk ↥A : ℚ) ≤ (rkIdx (fixV (autSec A V U)) : ℚ) := by
  have h1 := qhatOf_autSec_le_rAV hA hA3 hAV hAU hf
  rw [← hq] at h1
  have h2 : q ≤ rAV (autSec A V U) := WithTop.coe_le_coe.1 h1
  unfold rAV at h2
  rw [B5.rk_autSec_eq hAV hAU hf] at h2
  have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
  rwa [le_div_iff₀ hpos] at h2

end Z391

theorem d391V_proved : D391V := by
  intro W _ _ M Mp T L V hMp hD hqM hVT A hA hAT hA3 hAr hAf
  subst hMp
  by_cases htop : orbSup T V = ⊤
  · exact Or.inl htop
  right
  have hexp := hD.hyp.exp
  have hq : CFSG.IsQuasisimple ↥Mp := hD.hyp.quasi
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    calc T ≤ Subgroup.normalizer (conjClosure Mp T : Set (MulAut W)) := le_normalizer_conjClosure Mp T
      _ = Subgroup.normalizer (Mp : Set (MulAut W)) := by rw [← hD.hyp.Mp_eq]
  have hGN : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := sup_le Subgroup.le_normalizer hTn
  have hN : ∀ g ∈ Mp ⊔ T, ∀ l ∈ Mp, g * l * g⁻¹ ∈ Mp := fun g hg l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hGN hg)) l).1 hl
  have hG := n1_sup_le_stabSub_sec hD.hyp
  rw [← hVT] at hG
  have hGV : Mp ⊔ T ≤ stabSub V := hG.trans inf_le_left
  have hGC : Mp ⊔ T ≤ stabSub (V ⊓ fixV Mp) := hG.trans inf_le_right
  obtain ⟨-, hVcomm, hVlt, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hMn : ∀ m ∈ M, ∀ l ∈ Mp, m * l * m⁻¹ ∈ Mp := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hcommV : commV Mp = ⊤ := Z391.commV_eq_top hMn hVcomm hD.hyp.gen
  have hntV : ¬ Mp ≤ centSec V (V ⊓ fixV Mp) := by
    intro h
    have h1 : commSub V Mp ≤ V ⊓ fixV Mp := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact (h hx).2 w hw
    rw [hVcomm] at h1
    exact lt_irrefl _ (lt_of_lt_of_le hVlt h1)
  have hAG : A ≤ Mp ⊔ T := hAT.trans le_sup_right
  have hAV : A ≤ stabSub V := hAG.trans hGV
  have hAC : A ≤ stabSub (V ⊓ fixV Mp) := hAG.trans hGC
  have hf₁ : A ⊓ centSec V (V ⊓ fixV Mp) = ⊥ :=
    Z391.inf_centSec_eq_bot hq le_sup_left hAG hN hGV hGC hntV hAf
  have hrA : 0 < rk ↥A := hA.rk_pos
  have hA2 : IsA2 (Mp ⊔ T) A := ⟨hAG, hA.2.1, hA.2.2⟩
  have hq1 := Z391.qhatOf_autSec_le_rAV hA2 hA3 hAV hAC hf₁
  obtain ⟨q, hq'⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hq1)
  have hMpM : Mp ≤ M := le_of_mem_cComp hD.hyp.comp
  have hTX : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.hyp.Mp_normal
  have hWM : ∀ t ∈ M, ∀ w ∈ (⊤ : Subgroup W), t • w ∈ (⊤ : Subgroup W) := fun _ _ _ _ => trivial
  let instQ : MulDistribMulAction ↥M (W ⧸ modFix Mp (⊤ : Subgroup W)) := quotAct hTX hWM
  set π : W →* (W ⧸ modFix Mp (⊤ : Subgroup W)) :=
    QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w) := fun g w => rfl
  have hker : π.ker = fixV Mp := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (fixed_eq_inf_fixV Mp ⊤).trans (top_inf_eq _)
  have hQ : ∀ x : W ⧸ modFix Mp (⊤ : Subgroup W), x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
  have hirr := (isIrr_tilde hD.hyp.irr).1
  let φ : ↥(Mp.subgroupOf M) → ↥Mp := fun l => ⟨((l : ↥M) : MulAut W), l.2⟩
  have hφ : Function.Surjective φ := fun a => ⟨⟨⟨(a : MulAut W), hMpM a.2⟩, a.2⟩, rfl⟩
  have hact : ∀ (l : ↥(Mp.subgroupOf M)) (x : W ⧸ modFix Mp (⊤ : Subgroup W)), l • x = φ l • x := by
    intro l x
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  have hVΛ : XMod.IsIrr ↥(Mp.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) :=
    Z391.isIrr_of_surj φ hφ hact hirr
  have hΛ : ∀ g : ↥M, ∀ l ∈ Mp.subgroupOf M, g * l * g⁻¹ ∈ Mp.subgroupOf M :=
    fun g l hl => hMn (g : MulAut W) g.2 (l : MulAut W) hl
  have hT : IsSylowTwoOf (T.subgroupOf M) (⊤ : Subgroup ↥M) :=
    Z391.isSylowTwoOf_subgroupOf_top hD.hyp.sylow
  have hAT₀ : A.subgroupOf M ≤ T.subgroupOf M := fun x hx => hAT hx
  have hAc : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x :=
    fun x hx y hy => Subtype.ext (hA.2.2.1 _ hx _ hy)
  have hA2' : ∀ x ∈ A.subgroupOf M, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using hA.2.2.2 (x : MulAut W) hx)
  have hVT₀ : ∀ t ∈ T.subgroupOf M,
      t • tilde Mp (⊤ : Subgroup W) V = tilde Mp (⊤ : Subgroup W) V := by
    intro t ht
    have h1 : t • tilde Mp (⊤ : Subgroup W) V = tilde Mp (⊤ : Subgroup W) ((t : MulAut W) • V) :=
      tilde_smul hTX hWM t V
    have h2 : (t : MulAut W) • V = V := map_eq_of_mem_stabSub (hGV ((le_sup_right : T ≤ Mp ⊔ T) ht))
    rw [h1, h2]
  have hgen' : (⨆ g : ↥M, g • tilde Mp (⊤ : Subgroup W) V) = ⊤ := by
    have e : ∀ g : ↥M, g • tilde Mp (⊤ : Subgroup W) V =
        tilde Mp (⊤ : Subgroup W) ((g : MulAut W) • V) := fun g => tilde_smul hTX hWM g V
    rw [iSup_congr e, ← tilde_biSup M V]
    have : (⨆ y ∈ M, y • V) = ⊤ := hD.hyp.gen
    rw [this]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hne : tilde Mp (⊤ : Subgroup W) V ≠ ⊤ := by
    intro h
    have h1 : V ⊔ modFix Mp (⊤ : Subgroup W) = ⊤ := by
      rw [← comap_tilde, h, Subgroup.comap_top]
    have h2 : modFix Mp (⊤ : Subgroup W) = fixV Mp :=
      (fixed_eq_inf_fixV Mp ⊤).trans (top_inf_eq _)
    rw [h2] at h1
    have h3 : commSub (⊤ : Subgroup W) Mp = V := by
      rw [← h1, commSub_sup_fixV le_rfl, hVcomm]
    rw [← commV_eq_commSub, hcommV] at h3
    exact htop (hVT.symm.trans h3.symm)
  obtain ⟨g, A₁, B, hA₁A, hBdef, hBT, hcount⟩ :=
    Z391.mackey_count (Γ := ↥M) (Q := W ⧸ modFix Mp (⊤ : Subgroup W)) (Λ := Mp.subgroupOf M)
      (T := T.subgroupOf M) (A := A.subgroupOf M) hQ hΛ hT hAT₀ hAc hA2' hVΛ hVT₀ hgen' hne
  have hA₀A : (A.subgroupOf M).map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hrkA₀ : rk ↥(A.subgroupOf M) = rk ↥A := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv]
  have hN1 : Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) ≤
      rkIdx (fixV A) := by
    have := Z391.nB_top_le_rkIdx_fixV π hπsurj hπM (A.subgroupOf M)
    rwa [hA₀A] at this
  have hN2 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by
    have h := hAr
    unfold rAV at h
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    rwa [div_le_iff₀ hpos] at h
  have hqA : q * (rk ↥A : ℚ) ≤
      (Z391.nB (A.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) : ℚ) := by
    have h1 := Z391.q_mul_rk_le hA2 hA3 hAV hAC hf₁ hq'
    have h2 := Z391.rkIdx_fixV_autSec_le_nB π hπM (A.subgroupOf M) V
    rw [hA₀A, hker] at h2
    exact h1.trans (by exact_mod_cast h2)
  set B' : Subgroup (MulAut W) := B.map M.subtype with hB'
  have hB'T : B' ≤ T := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBT hb
  have hA₁' : A₁.map M.subtype ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA₁A ha
  have hB'eq : B' = (A₁.map M.subtype).map (MulAut.conj ((g : MulAut W)⁻¹)).toMonoidHom := by
    rw [hB', hBdef, Z391.map_subtype_conj]
    rfl
  have hhM : (g : MulAut W)⁻¹ ∈ M := M.inv_mem g.2
  have hmemB' : ∀ x ∈ B', ∃ a ∈ A, x = (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ := by
    intro x hx
    rw [hB'eq] at hx
    obtain ⟨y, ⟨a, ha, rfl⟩, rfl⟩ := hx
    exact ⟨(a : MulAut W), hA₁' ⟨a, ha, rfl⟩, rfl⟩
  have hB'ab : IsElemAbelian2 B' := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := hmemB' x hx
      obtain ⟨b, hb, rfl⟩ := hmemB' y hy
      have := hA.2.2.1 a ha b hb
      calc (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ * ((g : MulAut W)⁻¹ * b * ((g : MulAut W)⁻¹)⁻¹)
          = (g : MulAut W)⁻¹ * (a * b) * ((g : MulAut W)⁻¹)⁻¹ := by group
        _ = (g : MulAut W)⁻¹ * (b * a) * ((g : MulAut W)⁻¹)⁻¹ := by rw [this]
        _ = (g : MulAut W)⁻¹ * b * ((g : MulAut W)⁻¹)⁻¹ * ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) := by
          group
    · obtain ⟨a, ha, rfl⟩ := hmemB' x hx
      have := hA.2.2.2 a ha
      calc ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) ^ 2
          = (g : MulAut W)⁻¹ * (a * a) * ((g : MulAut W)⁻¹)⁻¹ := by rw [pow_two]; group
        _ = 1 := by rw [← pow_two, this]; group
  have hB'f : ∀ x ∈ B', (∀ y ∈ Mp, x * y = y * x) → x = 1 := by
    intro x hx hxc
    obtain ⟨a, ha, rfl⟩ := hmemB' x hx
    have ha1 : a = 1 := by
      refine hAf a ha (fun z hz => ?_)
      have hy : (g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹ ∈ Mp := hMn _ hhM z hz
      have e := hxc _ hy
      have e' : (g : MulAut W)⁻¹ * (a * z) * ((g : MulAut W)⁻¹)⁻¹ =
          (g : MulAut W)⁻¹ * (z * a) * ((g : MulAut W)⁻¹)⁻¹ := by
        calc (g : MulAut W)⁻¹ * (a * z) * ((g : MulAut W)⁻¹)⁻¹
            = (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ *
                ((g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹) := by group
          _ = (g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹ *
                ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) := e
          _ = (g : MulAut W)⁻¹ * (z * a) * ((g : MulAut W)⁻¹)⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e')
    rw [ha1]
    group
  have hB'3 : commSeries B' 3 = ⊥ := by
    rw [hB'eq, Z391.commSeries_map_conj]
    have : commSeries (A₁.map M.subtype) 3 = ⊥ :=
      le_bot_iff.1 ((commSeries_mono hA₁' 3).trans hA3.le)
    rw [this, Subgroup.map_bot]
  have hGB' : B' ≤ Mp ⊔ T := hB'T.trans le_sup_right
  have hB'V : B' ≤ stabSub V := hGB'.trans hGV
  have hB'C : B' ≤ stabSub (V ⊓ fixV Mp) := hGB'.trans hGC
  have hf₂ : B' ⊓ centSec V (V ⊓ fixV Mp) = ⊥ :=
    Z391.inf_centSec_eq_bot hq le_sup_left hGB' hN hGV hGC hntV hB'f
  have hrkB' : rk ↥B' = rk ↥A₁ := by
    have h1 : rk ↥B' = rk ↥B := by
      unfold rk
      rw [hB', Subgroup.card_map_of_injective M.subtype_injective]
    rw [h1, hBdef]
    exact Z391.rk_map_conj A₁ g⁻¹
  have hqB : q * (rk ↥A₁ : ℚ) ≤
      (Z391.nB B (tilde Mp (⊤ : Subgroup W) V) : ℚ) := by
    by_cases hz : rk ↥A₁ = 0
    · rw [hz]
      simp
    · have hB'ne : B' ≠ ⊥ := by
        intro hbot
        apply hz
        rw [← hrkB', hbot, rk_bot]
      have hB'A2 : IsA2 (Mp ⊔ T) B' := ⟨hGB', hB'ne, hB'ab⟩
      have h1 := Z391.q_mul_rk_le hB'A2 hB'3 hB'V hB'C hf₂ hq'
      have h2 := Z391.rkIdx_fixV_autSec_le_nB π hπM B V
      rw [hker] at h2
      rw [hrkB'] at h1
      exact h1.trans (by exact_mod_cast h2)
  have hr₁ : rk ↥A₁ ≤ rk ↥(A.subgroupOf M) := rk_mono hA₁A
  have hcountQ : (Z391.nB (A.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) : ℚ) +
      (Z391.nB B (tilde Mp (⊤ : Subgroup W) V) : ℚ) + (rk ↥A : ℚ) ≤
      (Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) : ℚ) +
        (rk ↥A₁ : ℚ) := by
    have : Z391.nB (A.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) +
        Z391.nB B (tilde Mp (⊤ : Subgroup W) V) + rk ↥A ≤
        Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) + rk ↥A₁ := by
      omega
    exact_mod_cast this
  have hN1' : (Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) : ℚ) ≤
      (rkIdx (fixV A) : ℚ) := by exact_mod_cast hN1
  have e3 : q ≤ 1 := by
    have ha : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    have ha₁ : (0 : ℚ) ≤ (rk ↥A₁ : ℚ) := Nat.cast_nonneg _
    by_contra hcon
    have hcon' : 1 < q := not_le.1 hcon
    nlinarith [mul_pos (sub_pos.2 hcon') (add_pos_of_pos_of_nonneg ha ha₁)]
  have hle : qhatOf (autSec (Mp ⊔ T) V (V ⊓ fixV Mp)) ≤ ((1 : ℚ) : WithTop ℚ) := by
    rw [← hq']
    exact_mod_cast e3
  obtain ⟨A', hA'2, -, hA'r⟩ := kq_le_iff.1 hle
  have hFF : IsFFModule (autSec (Mp ⊔ T) V (V ⊓ fixV Mp)) :=
    (isFFModule_iff (Bridge.sec_sq_eq_one hexp V (V ⊓ fixV Mp))).2 ⟨A', hA'2, hA'r⟩
  exact Z391.isFFModule_autSec_inf hFF

theorem d391L_of_deep (hD : D391Deep) : D391L :=
  d391L_of_pieces d391V_proved hD

end CFSG.Quasithin
