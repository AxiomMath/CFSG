module

public import CFSG.Quasithin.H13.L32A706d
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Quasithin CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76

variable {W : Type} [CommGroup W] [Finite W]

theorem centralizes_of_rank_four (hV : ∀ w : W, w ^ 2 = 1) {d d' : MulAut W}
    (hd5 : d ^ 5 = 1) (hd'5 : d' ^ 5 = 1) (hdd' : d * d' = d' * d)
    (hd' : ∀ k : ℕ, d' * d ^ k ≠ 1)
    (hrk : rk ((⊤ : Subgroup W).map (commHom d)) = 4)
    (hrk' : rk ((⊤ : Subgroup W).map (commHom d')) = 4) :
    ∀ w ∈ (⊤ : Subgroup W).map (commHom d), d' w = w := by
  by_contra hne
  have heq := map_commHom_eq_of_not_fix hV hd5 hd'5 hdd' hrk hrk' hne
  obtain ⟨i, -, hfi⟩ := exists_pow_mul_fix hV hd5 hd'5 hdd' hrk
  apply hd' i
  apply eq_one_of_forall
  intro w
  have hdec := eq_inf_fix_sup_map hV (n := 5) (by decide) hd5 (A := ⊤)
    (fun _ _ => Subgroup.mem_top _)
  have hw : w ∈ (⊤ : Subgroup W) := Subgroup.mem_top w
  rw [hdec] at hw
  have hfixC : ∀ c ∈ (⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers d), d' c = c := by
    intro c hc
    have hcd : d c = c := mem_fixV_zpowers_iff.mp hc.2
    have h1 : d' c * c⁻¹ ∈ (⊤ : Subgroup W).map (commHom d') := ⟨c, Subgroup.mem_top _, rfl⟩
    rw [← heq] at h1
    have h2 : d' c * c⁻¹ ∈ fixV (Subgroup.zpowers d) := by
      rw [mem_fixV_zpowers_iff, map_mul, map_inv, hcd]
      congr 1
      rw [← MulAut.mul_apply, hdd', MulAut.mul_apply, hcd]
    have h3 : d' c * c⁻¹ ∈ (⊤ : Subgroup W).map (commHom d) ⊓ fixV (Subgroup.zpowers d) :=
      ⟨h1, h2⟩
    rw [map_commHom_inf_fix_eq_bot hV (by decide) hd5 ⊤, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp h3
  have hall : ∀ u ∈ ((⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers d)) ⊔
      (⊤ : Subgroup W).map (commHom d), (d' * d ^ i) u = u := by
    intro u hu
    obtain ⟨c, hc, v, hv, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, hfi v hv, MulAut.mul_apply,
      Q511.pow_apply_eq_self (mem_fixV_zpowers_iff.mp hc.2), hfixC c hc]
  exact hall w hw

abbrev cw (g : MulAut W) : Subgroup W := (⊤ : Subgroup W).map (commHom g)

omit [Finite W] in
theorem cw_one : cw (1 : MulAut W) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨w, -, rfl⟩
  simp [commHom_apply]

omit [Finite W] in
theorem cw_conj (b g : MulAut W) : cw (b * g * b⁻¹) = (cw g).map (b : W →* W) :=
  (map_map_commHom b g).symm

omit [Finite W] in
theorem rk_cw_conj (b g : MulAut W) : rk (cw (b * g * b⁻¹)) = rk (cw g) := by
  rw [cw_conj, rk_map_aut]

structure Lines (d₁ d₂ : MulAut W) : Prop where
  hV : ∀ w : W, w ^ 2 = 1
  h5₁ : d₁ ^ 5 = 1
  h5₂ : d₂ ^ 5 = 1
  comm : d₁ * d₂ = d₂ * d₁
  rk₁ : rk (cw d₁) = 4
  rk₂ : rk (cw d₂) = 4
  fix₁ : ∀ w ∈ cw d₁, d₂ w = w
  fix₂ : ∀ w ∈ cw d₂, d₁ w = w

namespace Lines

variable {d₁ d₂ : MulAut W} (h : Lines d₁ d₂)
include h

omit [Finite W] in
theorem symm : Lines d₂ d₁ := ⟨h.hV, h.h5₂, h.h5₁, h.comm.symm, h.rk₂, h.rk₁, h.fix₂, h.fix₁⟩

omit [Finite W] in
theorem ne_one₁ : d₁ ≠ 1 := by
  intro h1
  have := h.rk₁
  rw [h1, cw_one, rk_bot] at this
  omega

omit [Finite W] in
theorem fpf₁ : cw d₁ ⊓ fixV (Subgroup.zpowers d₁) = ⊥ :=
  map_commHom_inf_fix_eq_bot h.hV (by decide) h.h5₁ ⊤

omit [Finite W] in
theorem inf_eq_bot : cw d₁ ⊓ cw d₂ = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have h1 : d₁ w = w := h.fix₂ w hw.2
  have : w ∈ cw d₁ ⊓ fixV (Subgroup.zpowers d₁) := ⟨hw.1, mem_fixV_zpowers_iff.mpr h1⟩
  rwa [h.fpf₁] at this

theorem cw_pow₁ {a : ℕ} (ha : 0 < a) (ha5 : a < 5) : cw (d₁ ^ a) = cw d₁ :=
  map_commHom_pow_eq h.h5₁ h.ne_one₁ ha.ne' ha5

theorem cw₁_le_mixed {a c : ℕ} (ha : 0 < a) (ha5 : a < 5) :
    cw d₁ ≤ cw (d₁ ^ a * d₂ ^ c) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set e := d₁ ^ a * d₂ ^ c with he
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hd₂ : ∀ w ∈ cw d₁, (d₂ ^ c) w = w := fun w hw => pow_apply_eq_self (h.fix₁ w hw) c
  have hact : ∀ w ∈ cw d₁, e w = (d₁ ^ a) w := fun w hw => by
    rw [he, MulAut.mul_apply, hd₂ w hw]
  have hinv : ∀ w ∈ cw d₁, e w ∈ cw d₁ := fun w hw => by
    rw [hact w hw]
    exact pow_mem_of_invariant (map_commHom_invariant rfl (hT d₁)) a w hw
  have hfix : cw d₁ ⊓ fixV (Subgroup.zpowers e) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwU, hwe⟩ := mem_inf_fix.mp hw
    rw [hact w hwU] at hwe
    have h1 : d₁ w = w := apply_eq_of_pow_apply_eq (by norm_num) h.h5₁ ha ha5 hwe
    have : w ∈ cw d₁ ⊓ fixV (Subgroup.zpowers d₁) := ⟨hwU, mem_fixV_zpowers_iff.mpr h1⟩
    rwa [h.fpf₁] at this
  have heq := map_commHom_eq_of_fix_eq_bot h.hV hinv hfix
  rw [← heq]
  exact Subgroup.map_mono le_top

theorem rk_mixed {a c : ℕ} (ha : 0 < a) (ha5 : a < 5) (hc : 0 < c) (hc5 : c < 5) :
    8 ≤ rk (cw (d₁ ^ a * d₂ ^ c)) := by
  have h1 := h.cw₁_le_mixed (c := c) ha ha5
  have h2 : cw d₂ ≤ cw (d₁ ^ a * d₂ ^ c) := by
    have := h.symm.cw₁_le_mixed (c := a) hc hc5
    rwa [show d₂ ^ c * d₁ ^ a = d₁ ^ a * d₂ ^ c from
      ((Commute.pow_pow (Commute.symm h.comm) c a)).eq] at this
  have hsup : cw d₁ ⊔ cw d₂ ≤ cw (d₁ ^ a * d₂ ^ c) := sup_le h1 h2
  have hrk := rk_sup_add_rk_inf (cw d₁) (cw d₂)
  rw [h.inf_eq_bot, rk_bot, h.rk₁, h.rk₂] at hrk
  have := rk_mono hsup
  omega

theorem cw_pow₂ {c : ℕ} (hc : 0 < c) (hc5 : c < 5) : cw (d₂ ^ c) = cw d₂ :=
  h.symm.cw_pow₁ hc hc5

theorem pow_ne_pow {a c : ℕ} (hc : 0 < c) (hc5 : c < 5) : d₂ ^ c ≠ d₁ ^ a := by
  intro he
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf d₁ = 5 := orderOf_eq_prime h.h5₁ h.ne_one₁
  have he' : d₂ ^ c = d₁ ^ (a % 5) := by rw [he, ← hord, pow_mod_orderOf]
  by_cases ha : a % 5 = 0
  · rw [ha, pow_zero] at he'
    have := h.rk₂
    rw [← h.cw_pow₂ hc hc5, he', cw_one, rk_bot] at this
    omega
  · have h1 : cw d₂ = cw d₁ := by
      rw [← h.cw_pow₂ hc hc5, he', h.cw_pow₁ (Nat.pos_of_ne_zero ha) (Nat.mod_lt _ (by norm_num))]
    have h2 := h.inf_eq_bot
    rw [h1, inf_idem] at h2
    have := h.rk₁
    rw [h2, rk_bot] at this
    omega

theorem conj_cases {b : MulAut W} (hb2 : b ^ 2 = 1) {a c : ℕ} (ha5 : a < 5) (hc5 : c < 5)
    (hb : b * d₁ * b⁻¹ = d₁ ^ a * d₂ ^ c) :
    (a = 0 ∧ 0 < c) ∨ (c = 0 ∧ (a = 1 ∨ a = 4)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrk := rk_cw_conj b d₁
  rw [hb, h.rk₁] at hrk
  have hbinv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hb2]
  by_cases ha : a = 0
  · left
    refine ⟨ha, Nat.pos_of_ne_zero fun hc => ?_⟩
    rw [ha, hc, pow_zero, pow_zero, mul_one] at hb
    apply h.ne_one₁
    have := congrArg (fun x => b⁻¹ * x * b) hb
    simpa [mul_assoc] using this
  · by_cases hc : c = 0
    · right
      refine ⟨hc, ?_⟩
      rw [hc, pow_zero, mul_one] at hb
      have hord : orderOf d₁ = 5 := orderOf_eq_prime h.h5₁ h.ne_one₁
      have hsq : d₁ ^ (a * a) = d₁ := by
        calc d₁ ^ (a * a) = (d₁ ^ a) ^ a := by rw [pow_mul]
          _ = (b * d₁ * b⁻¹) ^ a := by rw [hb]
          _ = b * d₁ ^ a * b⁻¹ := by rw [conj_pow]
          _ = b * (b * d₁ * b⁻¹) * b⁻¹ := by rw [hb]
          _ = d₁ := by rw [hbinv]; rw [← mul_assoc, ← mul_assoc, ← pow_two, hb2, one_mul,
                mul_assoc, ← pow_two, hb2, mul_one]
      have h1 : d₁ ^ (a * a % 5) = d₁ ^ 1 := by rw [pow_one, ← hord, pow_mod_orderOf, hsq]
      have h2 := pow_injOn_Iio_orderOf (x := d₁) (by rw [hord]; exact Nat.mod_lt _ (by norm_num))
        (by rw [hord]; norm_num) h1
      interval_cases a <;> simp_all
    · exfalso
      have := h.rk_mixed (Nat.pos_of_ne_zero ha) ha5 (Nat.pos_of_ne_zero hc) hc5
      omega

theorem four_le_of_swap {b : MulAut W} {c : ℕ} (hc : 0 < c) (hc5 : c < 5)
    (hb : b * d₁ * b⁻¹ = d₂ ^ c) : 4 ≤ rk (cw b) := by
  have hmap : (cw d₁).map (b : W →* W) = cw d₂ := by
    rw [← cw_conj, hb, h.cw_pow₂ hc hc5]
  have hker : cw d₁ ⊓ (commHom b).ker = ⊥ := by
    rw [ker_commHom, eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hwb⟩ := mem_inf_fix.mp hw
    have hw2 : w ∈ cw d₂ := by
      rw [← hmap, ← hwb]
      exact ⟨w, hw1, rfl⟩
    have : w ∈ cw d₁ ⊓ cw d₂ := ⟨hw1, hw2⟩
    rwa [h.inf_eq_bot] at this
  have h1 := rk_map_add_rk_inf_ker (commHom b) (cw d₁)
  rw [hker, rk_bot, h.rk₁, add_zero] at h1
  have h2 : (cw d₁).map (commHom b) ≤ cw b := Subgroup.map_mono le_top
  have := rk_mono h2
  omega

theorem rk_inv {b : MulAut W} (hb2 : b ^ 2 = 1) (hb : b * d₁ * b⁻¹ = d₁⁻¹) :
    rk ((cw d₁).map (commHom b)) = 2 ∧ (cw d₁).map (commHom b) ≤ cw d₁ := by
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hUd : ∀ u ∈ cw d₁, d₁ u ∈ cw d₁ := map_commHom_invariant rfl (hT d₁)
  have hUb : ∀ u ∈ cw d₁, b u ∈ cw d₁ := fun u hu => mem_map_commHom_of_inv hb hu
  have h1 := Q511.rk_eq_two_mul_of_inverts h.hV hUd hUb h.fpf₁ hb2 hb
  have h2 := rk_map_add_rk_inf_ker (commHom b) (cw d₁)
  rw [ker_commHom, h.rk₁] at h2
  rw [h.rk₁] at h1
  exact ⟨by omega, map_commHom_le hUb⟩

theorem fix_of_comm {b : MulAut W} (hb2 : b ^ 2 = 1) (hb : b * d₂ = d₂ * b) :
    ∀ w ∈ cw d₂, b w = w := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hT : ∀ (g : MulAut W), ∀ w ∈ (⊤ : Subgroup W), g w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ => Subgroup.mem_top _
  have hUb : ∀ u ∈ cw d₂, b u ∈ cw d₂ := fun u hu => mem_map_commHom_of_comm hb hu
  have hUd₂ : ∀ u ∈ cw d₂, d₂ u ∈ cw d₂ := map_commHom_invariant rfl (hT d₂)
  have hle := map_commHom_le_inf_fix h.hV hUb hb2
  have h2 := rk_map_add_rk_inf_ker (commHom b) (cw d₂)
  rw [ker_commHom, h.rk₂] at h2
  have h3 := rk_mono hle
  have hU'4 : rk ((cw d₂).map (commHom b)) ≤ 4 := by omega
  have hU'd : ∀ u ∈ (cw d₂).map (commHom b), d₂ u ∈ (cw d₂).map (commHom b) :=
    map_commHom_invariant hb hUd₂
  have hfix : (cw d₂).map (commHom b) ⊓ fixV (Subgroup.zpowers d₂) = ⊥ :=
    inf_fix_le_of_le (le_trans hle inf_le_left) d₂ h.symm.fpf₁
  have hdvd := dvd_two_pow_rk_sub_one h.hV hU'd h.h5₂ hfix
  have h0 : rk ((cw d₂).map (commHom b)) = 0 := by
    rcases rk_of_dvd_five hdvd hU'4 with h0 | h4
    · exact h0
    · omega
  have hbot : (cw d₂).map (commHom b) = ⊥ := (rk_eq_zero_iff h.hV).mp h0
  intro w hw
  have : commHom b w ∈ (cw d₂).map (commHom b) := ⟨w, hw, rfl⟩
  rw [hbot, Subgroup.mem_bot, commHom_apply, mul_inv_eq_one] at this
  exact this

omit [Finite W] in
theorem pow_four₁ : d₁ ^ 4 = d₁⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, h.h5₁]

theorem inv_type {b : MulAut W} (hb2 : b ^ 2 = 1)
    (hE₁ : ∃ a < 5, ∃ c < 5, b * d₁ * b⁻¹ = d₁ ^ a * d₂ ^ c)
    (hE₂ : ∃ a < 5, ∃ c < 5, b * d₂ * b⁻¹ = d₁ ^ a * d₂ ^ c) :
    (∃ c, 0 < c ∧ c < 5 ∧ b * d₁ * b⁻¹ = d₂ ^ c) ∨
      ((b * d₁ * b⁻¹ = d₁ ∨ b * d₁ * b⁻¹ = d₁⁻¹) ∧
        (b * d₂ * b⁻¹ = d₂ ∨ b * d₂ * b⁻¹ = d₂⁻¹)) := by
  have hbinv : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hb2]
  obtain ⟨a₁, ha₁, c₁, hc₁, hb₁⟩ := hE₁
  obtain ⟨a₂, ha₂, c₂, hc₂, hb₂⟩ := hE₂
  rcases h.conj_cases hb2 ha₁ hc₁ hb₁ with ⟨rfl, hc⟩ | ⟨rfl, ha⟩
  · left
    exact ⟨c₁, hc, hc₁, by rw [hb₁, pow_zero, one_mul]⟩
  · right
    have hd₁ : b * d₁ * b⁻¹ = d₁ ∨ b * d₁ * b⁻¹ = d₁⁻¹ := by
      rw [hb₁, pow_zero, mul_one]
      rcases ha with rfl | rfl
      · left; rw [pow_one]
      · right; exact h.pow_four₁
    refine ⟨hd₁, ?_⟩
    have hb₂' : b * d₂ * b⁻¹ = d₂ ^ c₂ * d₁ ^ a₂ := by
      rw [hb₂]; exact (Commute.pow_pow h.comm a₂ c₂).eq
    rcases h.symm.conj_cases hb2 hc₂ ha₂ hb₂' with ⟨rfl, ha'⟩ | ⟨rfl, hc'⟩
    · exfalso
      rw [pow_zero, one_mul] at hb₂'
      have e : d₂ = (b * d₁ * b⁻¹) ^ a₂ := by
        rw [conj_pow, ← hb₂', hbinv, ← mul_assoc, ← mul_assoc, ← pow_two, hb2, one_mul,
          mul_assoc, ← pow_two, hb2, mul_one]
      rcases hd₁ with h1 | h1
      · rw [h1] at e
        exact h.pow_ne_pow (a := a₂) (c := 1) (by norm_num) (by norm_num) (by rw [pow_one]; exact e)
      · rw [h1, ← h.pow_four₁, ← pow_mul] at e
        exact h.pow_ne_pow (a := 4 * a₂) (c := 1) (by norm_num) (by norm_num)
          (by rw [pow_one]; exact e)
    · rw [pow_zero, mul_one] at hb₂'
      rw [hb₂']
      rcases hc' with rfl | rfl
      · left; rw [pow_one]
      · right; exact h.symm.pow_four₁

theorem four_le_of_inv_inv {b : MulAut W} (hb2 : b ^ 2 = 1) (hb₁ : b * d₁ * b⁻¹ = d₁⁻¹)
    (hb₂ : b * d₂ * b⁻¹ = d₂⁻¹) : 4 ≤ rk (cw b) := by
  obtain ⟨h1, h1le⟩ := h.rk_inv hb2 hb₁
  obtain ⟨h2, h2le⟩ := h.symm.rk_inv hb2 hb₂
  have hinf : (cw d₁).map (commHom b) ⊓ (cw d₂).map (commHom b) = ⊥ :=
    le_bot_iff.mp (h.inf_eq_bot ▸ inf_le_inf h1le h2le)
  have hsup := rk_sup_add_rk_inf ((cw d₁).map (commHom b)) ((cw d₂).map (commHom b))
  rw [hinf, rk_bot, h1, h2] at hsup
  have hle : (cw d₁).map (commHom b) ⊔ (cw d₂).map (commHom b) ≤ cw b :=
    sup_le (Subgroup.map_mono le_top) (Subgroup.map_mono le_top)
  have := rk_mono hle
  omega

theorem inv_rank_two {b : MulAut W} (hb2 : b ^ 2 = 1)
    (hE₁ : ∃ a < 5, ∃ c < 5, b * d₁ * b⁻¹ = d₁ ^ a * d₂ ^ c)
    (hE₂ : ∃ a < 5, ∃ c < 5, b * d₂ * b⁻¹ = d₁ ^ a * d₂ ^ c)
    (hnc : ¬ (b * d₁ * b⁻¹ = d₁ ∧ b * d₂ * b⁻¹ = d₂)) (hrk : rk (cw b) ≤ 2) :
    (b * d₁ * b⁻¹ = d₁⁻¹ ∧ b * d₂ * b⁻¹ = d₂ ∧ cw b ≤ cw d₁ ∧ rk (cw b) = 2) ∨
      (b * d₂ * b⁻¹ = d₂⁻¹ ∧ b * d₁ * b⁻¹ = d₁ ∧ cw b ≤ cw d₂ ∧ rk (cw b) = 2) := by
  rcases h.inv_type hb2 hE₁ hE₂ with ⟨c, hc, hc5, hsw⟩ | ⟨h1 | h1, h2 | h2⟩
  · have := h.four_le_of_swap hc hc5 hsw
    omega
  · exact absurd ⟨h1, h2⟩ hnc
  · right
    obtain ⟨hr, hle⟩ := h.symm.rk_inv hb2 h2
    have hsub : (cw d₂).map (commHom b) ≤ cw b := Subgroup.map_mono le_top
    have heq : (cw d₂).map (commHom b) = cw b := eq_of_le_of_rk_le h.hV hsub (by omega)
    exact ⟨h2, h1, heq ▸ hle, by rw [← heq, hr]⟩
  · left
    obtain ⟨hr, hle⟩ := h.rk_inv hb2 h1
    have hsub : (cw d₁).map (commHom b) ≤ cw b := Subgroup.map_mono le_top
    have heq : (cw d₁).map (commHom b) = cw b := eq_of_le_of_rk_le h.hV hsub (by omega)
    exact ⟨h1, h2, heq ▸ hle, by rw [← heq, hr]⟩
  · have := h.four_le_of_inv_inv hb2 h1 h2
    omega

end Lines

theorem rkIdx_inf_fix {x y : MulAut W} (hxy : x * y = y * x) :
    rkIdx (fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y)) =
      rk (cw y) + rk ((fixV (Subgroup.zpowers y)).map (commHom x)) := by
  have hYx : ∀ u ∈ fixV (Subgroup.zpowers y), x u ∈ fixV (Subgroup.zpowers y) :=
    fun u hu => mem_fix_of_comm hxy hu
  have h1 := rk_commSub_add_rk_inf_fixV (g := x) (W := fixV (Subgroup.zpowers y))
    (fun x' hx' w hw => zpowers_invariant hYx x' hx' w hw)
  rw [commSub_zpowers_eq_map (fun x' hx' w hw => zpowers_invariant hYx x' hx' w hw)] at h1
  have h2 := rk_commV_add_rk_fixV y
  rw [commV_zpowers_eq_map] at h2
  have h2' : rk (cw y) + rk (fixV (Subgroup.zpowers y)) = rk W := h2
  have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y))
  rw [inf_comm] at h1
  omega

omit [Finite W] in
theorem map_cw_of_pm {d b : MulAut W} (hb : b * d * b⁻¹ = d ∨ b * d * b⁻¹ = d⁻¹)
    {w : W} (hw : w ∈ cw d) : b w ∈ cw d := by
  rcases hb with hb | hb
  · have hc : b * d = d * b := by
      calc b * d = (b * d * b⁻¹) * b := by group
        _ = d * b := by rw [hb]
    exact mem_map_commHom_of_comm hc hw
  · exact mem_map_commHom_of_inv hb hw

namespace Lines

variable {d₁ d₂ : MulAut W} (h : Lines d₁ d₂)
include h

theorem trivial_of_swap {B : Subgroup (MulAut W)} (hquad : IsQuadratic B) {s : MulAut W}
    (hs : s ∈ B) {c : ℕ} (hc : 0 < c) (hc5 : c < 5) (hsw : s * d₁ * s⁻¹ = d₂ ^ c)
    {x : MulAut W} (hx : x ∈ B) (hx2 : x ^ 2 = 1)
    (hx₁ : x * d₁ * x⁻¹ = d₁ ∨ x * d₁ * x⁻¹ = d₁⁻¹)
    (hx₂ : x * d₂ * x⁻¹ = d₂ ∨ x * d₂ * x⁻¹ = d₂⁻¹) :
    x * d₁ * x⁻¹ = d₁ ∧ x * d₂ * x⁻¹ = d₂ := by
  have hmap : (cw d₁).map (s : W →* W) = cw d₂ := by
    rw [← cw_conj, hsw, h.cw_pow₂ hc hc5]
  have key : ∀ w ∈ cw d₁, x w = w ∧ x (s w) = s w := by
    intro w hw
    have hsw2 : s w ∈ cw d₂ := by rw [← hmap]; exact ⟨w, hw, rfl⟩
    have hcomm : s w * w⁻¹ ∈ commV B := Subgroup.subset_closure ⟨s, hs, w, rfl⟩
    have hfix := hquad hcomm x hx
    rw [map_mul, map_inv] at hfix
    have h1 : x (s w) * (s w)⁻¹ = x w * w⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul.mp hfix]
      calc s w * w⁻¹ * x w * (s w)⁻¹ = (x w * w⁻¹) * (s w * (s w)⁻¹) := by ac_rfl
        _ = x w * w⁻¹ := by rw [mul_inv_cancel, mul_one]
    have hA : x w * w⁻¹ ∈ cw d₁ := (cw d₁).mul_mem (map_cw_of_pm hx₁ hw) ((cw d₁).inv_mem hw)
    have hB : x (s w) * (s w)⁻¹ ∈ cw d₂ :=
      (cw d₂).mul_mem (map_cw_of_pm hx₂ hsw2) ((cw d₂).inv_mem hsw2)
    have hC : x w * w⁻¹ ∈ cw d₁ ⊓ cw d₂ := ⟨hA, h1 ▸ hB⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at hC
    refine ⟨hC, ?_⟩
    have hD : x (s w) * (s w)⁻¹ = 1 := by rw [h1, hC, mul_inv_cancel]
    exact mul_inv_eq_one.mp hD
  have hW₁ : (cw d₁).map (commHom x) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_bot, commHom_apply, (key w hw).1, mul_inv_cancel]
  have hW₂ : (cw d₂).map (commHom x) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← hmap] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [Subgroup.mem_bot, commHom_apply]
    show x (s w') * (s w')⁻¹ = 1
    rw [(key w' hw').2, mul_inv_cancel]
  refine ⟨?_, ?_⟩
  · rcases hx₁ with h1 | h1
    · exact h1
    · exfalso
      have := (h.rk_inv hx2 h1).1
      rw [hW₁, rk_bot] at this
      omega
  · rcases hx₂ with h1 | h1
    · exact h1
    · exfalso
      have := (h.symm.rk_inv hx2 h1).1
      rw [hW₂, rk_bot] at this
      omega

abbrev InE (d₁ d₂ e : MulAut W) : Prop := ∃ a < 5, ∃ c < 5, e = d₁ ^ a * d₂ ^ c

theorem offender {B : Subgroup (MulAut W)} (hB : IsElemAbelian2 B) (hne : B ≠ ⊥)
    (hquad : IsQuadratic B) (hr : rkIdx (fixV B) ≤ 2 * rk B)
    (hE : ∀ b ∈ B, InE d₁ d₂ (b * d₁ * b⁻¹) ∧ InE d₁ d₂ (b * d₂ * b⁻¹))
    (hfaith : ∀ b ∈ B, b * d₁ * b⁻¹ = d₁ → b * d₂ * b⁻¹ = d₂ → b = 1) :
    (∃ b ∈ B, B = Subgroup.zpowers b ∧
      ((b * d₁ * b⁻¹ = d₁⁻¹ ∧ b * d₂ * b⁻¹ = d₂ ∧ cw b ≤ cw d₁ ∧ rk (cw b) = 2) ∨
        (b * d₂ * b⁻¹ = d₂⁻¹ ∧ b * d₁ * b⁻¹ = d₁ ∧ cw b ≤ cw d₂ ∧ rk (cw b) = 2))) ∨
    (∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ cw b₁ ≤ cw d₁ ∧ cw b₂ ≤ cw d₂ ∧ rk B = 2 ∧
      rkIdx (fixV B) = 4) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsq : ∀ b ∈ B, b ^ 2 = 1 := hB.2
  have htype := fun b (hb : b ∈ B) => h.inv_type (hsq b hb) (hE b hb).1 (hE b hb).2
  have hz2 : ∀ b ∈ B, b ≠ 1 → Nat.card (Subgroup.zpowers b) = 2 := by
    intro b hb hb1
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hsq b hb) hb1
  have hfixz : ∀ b : MulAut W, rkIdx (fixV (Subgroup.zpowers b)) = rk (cw b) := fun b => by
    rw [rkIdx_fixV_zpowers, commV_zpowers_eq_map]
  have hnosw : ∀ s ∈ B, ∀ c, 0 < c → c < 5 → s * d₁ * s⁻¹ ≠ d₂ ^ c := by
    intro s hs c hc hc5 hsw
    have hall : ∀ x ∈ B, x = 1 ∨ x = s := by
      intro x hx
      rcases htype x hx with ⟨c', hc', hc'5, hxsw⟩ | ⟨hx₁, hx₂⟩
      ·
        right
        have hsx : s * x ∈ B := B.mul_mem hs hx
        have hsxd : (s * x) * d₁ * (s * x)⁻¹ = (s * d₂ * s⁻¹) ^ c' := by
          rw [show (s * x) * d₁ * (s * x)⁻¹ = s * (x * d₁ * x⁻¹) * s⁻¹ by group, hxsw, conj_pow]
        rcases htype s hs with ⟨-, -, -, -⟩ | ⟨hs₁, -⟩
        · rcases h.symm.inv_type (hsq s hs)
              (by obtain ⟨a, ha, c₀, hc₀, he⟩ := (hE s hs).2
                  exact ⟨c₀, hc₀, a, ha, by rw [he]; exact (Commute.pow_pow h.comm a c₀).eq⟩)
              (by obtain ⟨a, ha, c₀, hc₀, he⟩ := (hE s hs).1
                  exact ⟨c₀, hc₀, a, ha, by rw [he]; exact (Commute.pow_pow h.comm a c₀).eq⟩)
            with ⟨c₂, hc₂, hc₂5, hs₂⟩ | ⟨hs₂, -⟩
          · rw [hs₂, ← pow_mul] at hsxd
            have hsx2 := hsq _ hsx
            have hcases := h.inv_type hsx2
              ⟨(c₂ * c') % 5, Nat.mod_lt _ (by norm_num), 0, by norm_num, by
                rw [hsxd, pow_zero, mul_one, ← pow_mod_orderOf,
                  orderOf_eq_prime h.h5₁ h.ne_one₁]⟩ (hE _ hsx).2
            rcases hcases with ⟨c₃, hc₃, hc₃5, hsw3⟩ | ⟨hsx₁, hsx₂⟩
            · exfalso
              rw [hsxd] at hsw3
              exact h.pow_ne_pow (a := c₂ * c') hc₃ hc₃5 hsw3.symm
            · have h1 := h.trivial_of_swap hquad hs hc hc5 hsw hsx hsx2 hsx₁ hsx₂
              have h2 := hfaith _ hsx h1.1 h1.2
              have hss : s * s = 1 := by rw [← pow_two]; exact hsq s hs
              calc x = (s * s) * x := by rw [hss, one_mul]
                _ = s * (s * x) := by group
                _ = s := by rw [h2, mul_one]
          · exfalso
            have hss : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hsq s hs
            have e : d₁ = (s * d₂ * s⁻¹) ^ c := by
              rw [conj_pow, ← hsw, hss, ← mul_assoc, ← mul_assoc, ← pow_two, hsq s hs, one_mul,
                mul_assoc, ← pow_two, hsq s hs, mul_one]
            rcases hs₂ with h1 | h1
            · rw [h1] at e
              exact h.symm.pow_ne_pow (a := c) (c := 1) (by norm_num) (by norm_num)
                (by rw [pow_one]; exact e)
            · rw [h1, ← h.symm.pow_four₁, ← pow_mul] at e
              exact h.symm.pow_ne_pow (a := 4 * c) (c := 1) (by norm_num) (by norm_num)
                (by rw [pow_one]; exact e)
        · exfalso
          rcases hs₁ with h1 | h1 <;> rw [h1] at hsw
          · exact h.pow_ne_pow (a := 1) hc hc5 (by rw [pow_one]; exact hsw.symm)
          · rw [← h.pow_four₁] at hsw
            exact h.pow_ne_pow (a := 4) hc hc5 hsw.symm
      · left
        have h1 := h.trivial_of_swap hquad hs hc hc5 hsw hx (hsq x hx) hx₁ hx₂
        exact hfaith x hx h1.1 h1.2
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [one_mul, inv_one, mul_one] at hsw
      exact h.pow_ne_pow (a := 1) hc hc5 (by rw [pow_one]; exact hsw.symm)
    have hBz : B = Subgroup.zpowers s := by
      refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr hs)
      rcases hall x hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have hrkB : rk B = 1 := by
      rw [rk, hBz, hz2 s hs hs1]; norm_num
    have h4 := h.four_le_of_swap hc hc5 hsw
    rw [hBz] at hr hrkB
    rw [hfixz, hrkB] at hr
    omega
  have hpm : ∀ x ∈ B, (x * d₁ * x⁻¹ = d₁ ∨ x * d₁ * x⁻¹ = d₁⁻¹) ∧
      (x * d₂ * x⁻¹ = d₂ ∨ x * d₂ * x⁻¹ = d₂⁻¹) := by
    intro x hx
    rcases htype x hx with ⟨c, hc, hc5, hsw⟩ | hpm
    · exact absurd hsw (hnosw x hx c hc hc5)
    · exact hpm
  have hd₁inv : d₁⁻¹ ≠ d₁ := fun he => h.ne_one₁ (by
    have h2 : d₁ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← he]; exact inv_mul_cancel d₁
    have := orderOf_dvd_of_pow_eq_one h2
    rw [orderOf_eq_prime h.h5₁ h.ne_one₁] at this
    norm_num at this)
  have hd₂inv : d₂⁻¹ ≠ d₂ := fun he => h.symm.ne_one₁ (by
    have h2 : d₂ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← he]; exact inv_mul_cancel d₂
    have := orderOf_dvd_of_pow_eq_one h2
    rw [orderOf_eq_prime h.h5₂ h.symm.ne_one₁] at this
    norm_num at this)
  have hconj_inv : ∀ (x d : MulAut W), x * d⁻¹ * x⁻¹ = (x * d * x⁻¹)⁻¹ := fun x d => by group
  have hconj_mul : ∀ (x y d : MulAut W), (x * y) * d * (x * y)⁻¹ = x * (y * d * y⁻¹) * x⁻¹ :=
    fun x y d => by group
  let τ : MulAut W → Bool × Bool := fun x =>
    (decide (x * d₁ * x⁻¹ = d₁⁻¹), decide (x * d₂ * x⁻¹ = d₂⁻¹))
  have hτinj : ∀ x ∈ B, ∀ y ∈ B, τ x = τ y → x = y := by
    intro x hx y hy hxy
    simp only [τ, Prod.mk.injEq, decide_eq_decide] at hxy
    have hyinv : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hsq y hy
    have hz : x * y ∈ B := B.mul_mem hx hy
    have hz₁ : (x * y) * d₁ * (x * y)⁻¹ = d₁ := by
      rw [hconj_mul]
      rcases (hpm y hy).1 with h1 | h1
      · rw [h1]
        rcases (hpm x hx).1 with h2 | h2
        · exact h2
        · exact absurd (hxy.1.mp h2 ▸ h1) hd₁inv
      · rw [h1, hconj_inv]
        rcases (hpm x hx).1 with h2 | h2
        · exact absurd (h2 ▸ (hxy.1.mpr h1)).symm hd₁inv
        · rw [h2, inv_inv]
    have hz₂ : (x * y) * d₂ * (x * y)⁻¹ = d₂ := by
      rw [hconj_mul]
      rcases (hpm y hy).2 with h1 | h1
      · rw [h1]
        rcases (hpm x hx).2 with h2 | h2
        · exact h2
        · exact absurd (hxy.2.mp h2 ▸ h1) hd₂inv
      · rw [h1, hconj_inv]
        rcases (hpm x hx).2 with h2 | h2
        · exact absurd (h2 ▸ (hxy.2.mpr h1)).symm hd₂inv
        · rw [h2, inv_inv]
    have h1 := hfaith _ hz hz₁ hz₂
    calc x = x * y * y⁻¹ := by group
      _ = y := by rw [h1, one_mul, hyinv]
  have hcard : Nat.card B ≤ 4 := by
    have hinj : Function.Injective (fun x : ↥B => τ x) := fun x y hxy =>
      Subtype.ext (hτinj x x.2 y y.2 hxy)
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hrk2 : rk B ≤ 2 := by
    have hpos : 0 < Nat.card B := Nat.card_pos
    unfold rk
    interval_cases hc : Nat.card B
    · simp
    · simp
    · rw [padicValNat.eq_zero_of_not_dvd (by norm_num)]; norm_num
    · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨b, hb, fun he => hb1 (Subtype.ext he)⟩
  by_cases hBz : B = Subgroup.zpowers b
  · left
    refine ⟨b, hb, hBz, ?_⟩
    have hrkB : rk B = 1 := by rw [rk, hBz, hz2 b hb hb1]; norm_num
    rw [hBz] at hr hrkB
    rw [hfixz, hrkB] at hr
    have hnc : ¬ (b * d₁ * b⁻¹ = d₁ ∧ b * d₂ * b⁻¹ = d₂) := fun ⟨h1, h2⟩ =>
      hb1 (hfaith b hb h1 h2)
    exact h.inv_rank_two (hsq b hb) (hE b hb).1 (hE b hb).2 hnc (by omega)
  · right
    obtain ⟨c, hc, hcb⟩ : ∃ c ∈ B, c ∉ Subgroup.zpowers b := by
      by_contra hcon
      push Not at hcon
      exact hBz (le_antisymm (fun x hx => hcon x hx) (Subgroup.zpowers_le.mpr hb))
    have hc1 : c ≠ 1 := fun he => hcb (he ▸ Subgroup.one_mem _)
    have hcb' : c ≠ b := fun he => hcb (he ▸ Subgroup.mem_zpowers b)
    have hbc1 : b * c ≠ 1 := fun he => hcb' (by
      have hbinv : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hsq b hb
      calc c = b⁻¹ * (b * c) := by group
        _ = b := by rw [he, mul_one, hbinv])
    obtain ⟨b₁, hb₁B, hb₁₁, hb₁₂, b₂, hb₂B, hb₂₂, hb₂₁⟩ :
        ∃ b₁ ∈ B, b₁ * d₁ * b₁⁻¹ = d₁⁻¹ ∧ b₁ * d₂ * b₁⁻¹ = d₂ ∧
          ∃ b₂ ∈ B, b₂ * d₂ * b₂⁻¹ = d₂⁻¹ ∧ b₂ * d₁ * b₂⁻¹ = d₁ := by
      have hbcB : b * c ∈ B := B.mul_mem hb hc
      have hmul₁ : ∀ x y : MulAut W, (x * y) * d₁ * (x * y)⁻¹ = x * (y * d₁ * y⁻¹) * x⁻¹ :=
        fun x y => hconj_mul x y d₁
      have hmul₂ : ∀ x y : MulAut W, (x * y) * d₂ * (x * y)⁻¹ = x * (y * d₂ * y⁻¹) * x⁻¹ :=
        fun x y => hconj_mul x y d₂
      rcases hpm b hb with ⟨hb₁ | hb₁, hb₂ | hb₂⟩ <;>
        rcases hpm c hc with ⟨hc₁ | hc₁, hc₂ | hc₂⟩
      · exact absurd (hfaith b hb hb₁ hb₂) hb1
      · exact absurd (hfaith b hb hb₁ hb₂) hb1
      · exact absurd (hfaith b hb hb₁ hb₂) hb1
      · exact absurd (hfaith b hb hb₁ hb₂) hb1
      · exact absurd (hfaith c hc hc₁ hc₂) hc1
      · exact absurd (hτinj c hc b hb (by simp [τ, hb₁, hc₁, hb₂, hc₂])) hcb'
      · exact ⟨c, hc, hc₁, hc₂, b, hb, hb₂, hb₁⟩
      · exact ⟨b * c, hbcB, by rw [hmul₁, hc₁, hconj_inv, hb₁],
          by rw [hmul₂, hc₂, hconj_inv, hb₂, inv_inv], b, hb, hb₂, hb₁⟩
      · exact absurd (hfaith c hc hc₁ hc₂) hc1
      · exact ⟨b, hb, hb₁, hb₂, c, hc, hc₂, hc₁⟩
      · exact absurd (hτinj c hc b hb (by simp [τ, hb₁, hc₁, hb₂, hc₂])) hcb'
      · exact ⟨b, hb, hb₁, hb₂, b * c, hbcB, by rw [hmul₂, hc₂, hconj_inv, hb₂],
          by rw [hmul₁, hc₁, hconj_inv, hb₁, inv_inv]⟩
      · exact absurd (hfaith c hc hc₁ hc₂) hc1
      · exact ⟨b * c, hbcB, by rw [hmul₁, hc₁, hb₁], by rw [hmul₂, hc₂, hconj_inv, hb₂, inv_inv],
          c, hc, hc₂, hc₁⟩
      · exact ⟨c, hc, hc₁, hc₂, b * c, hbcB, by rw [hmul₂, hc₂, hb₂],
          by rw [hmul₁, hc₁, hconj_inv, hb₁, inv_inv]⟩
      · exact absurd (hτinj c hc b hb (by simp [τ, hb₁, hc₁, hb₂, hc₂])) hcb'
    have hb₁1 : b₁ ≠ 1 := fun he => hd₁inv (by rw [← hb₁₁, he]; group)
    have hb₂1 : b₂ ≠ 1 := fun he => hd₂inv (by rw [← hb₂₂, he]; group)
    have hcomm : b₁ * b₂ = b₂ * b₁ := hB.1 b₁ hb₁B b₂ hb₂B
    have hc₁₂ : b₂ * d₁ = d₁ * b₂ := by
      calc b₂ * d₁ = (b₂ * d₁ * b₂⁻¹) * b₂ := by group
        _ = d₁ * b₂ := by rw [hb₂₁]
    have hc₂₁ : b₁ * d₂ = d₂ * b₁ := by
      calc b₁ * d₂ = (b₁ * d₂ * b₁⁻¹) * b₁ := by group
        _ = d₂ * b₁ := by rw [hb₁₂]
    obtain ⟨hr₁, hle₁⟩ := h.rk_inv (hsq b₁ hb₁B) hb₁₁
    obtain ⟨hr₂, hle₂⟩ := h.symm.rk_inv (hsq b₂ hb₂B) hb₂₂
    have hW₁ : cw d₁ ≤ fixV (Subgroup.zpowers b₂) := fun w hw =>
      mem_fixV_zpowers_iff.mpr (h.symm.fix_of_comm (hsq b₂ hb₂B) hc₁₂ w hw)
    have hW₂ : cw d₂ ≤ fixV (Subgroup.zpowers b₁) := fun w hw =>
      mem_fixV_zpowers_iff.mpr (h.fix_of_comm (hsq b₁ hb₁B) hc₂₁ w hw)
    have hA₁ : rk ((cw d₁).map (commHom b₁)) ≤
        rk ((fixV (Subgroup.zpowers b₂)).map (commHom b₁)) := rk_mono (Subgroup.map_mono hW₁)
    have hA₂ : rk ((cw d₂).map (commHom b₂)) ≤
        rk ((fixV (Subgroup.zpowers b₁)).map (commHom b₂)) := rk_mono (Subgroup.map_mono hW₂)
    have hB₁ : rk ((cw d₁).map (commHom b₁)) ≤ rk (cw b₁) := rk_mono (Subgroup.map_mono le_top)
    have hB₂ : rk ((cw d₂).map (commHom b₂)) ≤ rk (cw b₂) := rk_mono (Subgroup.map_mono le_top)
    have hid₁ := rkIdx_inf_fix hcomm
    have hid₂ := rkIdx_inf_fix hcomm.symm
    rw [inf_comm] at hid₂
    have hfixB : fixV B ≤ fixV (Subgroup.zpowers b₁) ⊓ fixV (Subgroup.zpowers b₂) :=
      le_inf (fun v hv x hx => hv x (Subgroup.zpowers_le.mpr hb₁B hx))
        (fun v hv x hx => hv x (Subgroup.zpowers_le.mpr hb₂B hx))
    have hanti := rkIdx_anti hfixB
    have hrkB : rk B = 2 := by omega
    refine ⟨b₁, hb₁B, b₂, hb₂B, hb₁1, hb₂1, ?_, ?_, hrkB, by omega⟩
    · have heq : (cw d₁).map (commHom b₁) = cw b₁ :=
        eq_of_le_of_rk_le h.hV (Subgroup.map_mono le_top) (by omega)
      exact heq ▸ hle₁
    · have heq : (cw d₂).map (commHom b₂) = cw b₂ :=
        eq_of_le_of_rk_le h.hV (Subgroup.map_mono le_top) (by omega)
      exact heq ▸ hle₂

end Lines

end CFSG.Quasithin.H13.L32A.S2

end
