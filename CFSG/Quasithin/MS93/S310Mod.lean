module

public import CFSG.Quasithin.MS93.MSPOrd3
public import CFSG.Quasithin.MS93.SkHyp

public section

namespace CFSG.Quasithin.MS93.S310

open Matrix CFSG.Quasithin.MS93.MSP
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {F : Type} [Field F]

structure Setup (A Lt V Bk : Subgroup Γ) (a : ↥A →* Sp4 F) (βv : Γ → V4 F) : Prop where
  lt_le : Lt ≤ A
  le_normalizer_lt : A ≤ Subgroup.normalizer (Lt : Set Γ)
  le_normalizer_v : A ≤ Subgroup.normalizer (V : Set Γ)
  bk_le : Bk ≤ V
  map_mul : ∀ x ∈ V, ∀ y ∈ V, βv (x * y) = βv x + βv y
  surj : ∀ w, ∃ x ∈ V, βv x = w
  ker : ∀ x ∈ V, βv x = 0 ↔ x ∈ Bk
  equiv : ∀ g : ↥A, ∀ x ∈ V, βv ((g : Γ) * x * (g : Γ)⁻¹) = mat (a g) *ᵥ βv x
  ord3 : ∀ g : Sp4 F, g ^ 3 = 1 → ∃ l : ↥A, (l : Γ) ∈ Lt ∧ a l = g

namespace Setup

variable {A Lt V Bk : Subgroup Γ} {a : ↥A →* Sp4 F} {βv : Γ → V4 F}

theorem conj_mem {H : Subgroup Γ} {g x : Γ} (hg : g ∈ Subgroup.normalizer (H : Set Γ))
    (hx : x ∈ H) : g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

theorem map_one (hs : Setup A Lt V Bk a βv) : βv 1 = 0 := by
  have h := hs.map_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  exact left_eq_add.1 h

theorem map_inv (hs : Setup A Lt V Bk a βv) {x : Γ} (hx : x ∈ V) : βv x⁻¹ = -βv x := by
  have h := hs.map_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, hs.map_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem comm_le (hs : Setup A Lt V Bk a βv) : ⁅V, Lt⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (hs.lt_le.trans hs.le_normalizer_v)

theorem le_normalizer_comm (hs : Setup A Lt V Bk a βv) :
    A ≤ Subgroup.normalizer ((⁅V, Lt⁆ : Subgroup Γ) : Set Γ) :=
  le_normalizer_commutator hs.le_normalizer_v hs.le_normalizer_lt

theorem map_commutator (hs : Setup A Lt V Bk a βv) (l : ↥A) {x : Γ} (hx : x ∈ V) :
    βv ⁅x, (l : Γ)⁆ = βv x - mat (a l) *ᵥ βv x := by
  have hm : (l : Γ) * x⁻¹ * (l : Γ)⁻¹ ∈ V := conj_mem (hs.le_normalizer_v l.2) (inv_mem hx)
  rw [commutatorElement_def, show x * (l : Γ) * x⁻¹ * (l : Γ)⁻¹ =
    x * ((l : Γ) * x⁻¹ * (l : Γ)⁻¹) by group, hs.map_mul x hx _ hm, hs.equiv l _ (inv_mem hx),
    hs.map_inv hx, mulVec_neg, sub_eq_add_neg]

theorem map_conj_mul_inv (hs : Setup A Lt V Bk a βv) (l : ↥A) {x : Γ} (hx : x ∈ V) :
    βv ((l : Γ) * x * (l : Γ)⁻¹ * x⁻¹) = mat (a l) *ᵥ βv x - βv x := by
  have hm : (l : Γ) * x * (l : Γ)⁻¹ ∈ V := conj_mem (hs.le_normalizer_v l.2) hx
  rw [hs.map_mul _ hm _ (inv_mem hx), hs.equiv l x hx, hs.map_inv hx, sub_eq_add_neg]

section CharTwo

variable [CharP F 2]

theorem exists_mulVec_e₁ (hs : Setup A Lt V Bk a βv) {b : F} (hb : b ≠ 0) {w : V4 F}
    (hw : w (.inr 0) = 1) : ∃ l : ↥A, (l : Γ) ∈ Lt ∧ mat (a l) *ᵥ e₁ F = b • w := by
  have huv : form F (e₁ F) w = 1 := by rw [form_e₁, hw]
  have hab : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  obtain ⟨l, hl, hal⟩ := hs.ord3 _ (transv_mul_transv_pow_three huv hab)
  exact ⟨l, hl, by rw [hal, transv_mul_transv_mulVec_left huv hab]⟩

theorem exists_comm_vec (hs : Setup A Lt V Bk a βv) (w : V4 F) :
    ∃ x ∈ ⁅V, Lt⁆, βv x = w := by
  set S : Set (V4 F) := {w | ∃ x ∈ ⁅V, Lt⁆, βv x = w} with hS
  have hadd : ∀ w ∈ S, ∀ w' ∈ S, w + w' ∈ S := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    exact ⟨x * x', mul_mem hx hx', hs.map_mul x (hs.comm_le hx) x' (hs.comm_le hx')⟩
  have hneg : ∀ w ∈ S, -w ∈ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, inv_mem hx, hs.map_inv (hs.comm_le hx)⟩
  have hzero : (0 : V4 F) ∈ S := ⟨1, one_mem _, hs.map_one⟩
  have hgen : ∀ l : ↥A, (l : Γ) ∈ Lt → ∀ w, w - mat (a l) *ᵥ w ∈ S := by
    intro l hl w
    obtain ⟨y, hy, rfl⟩ := hs.surj w
    exact ⟨⁅y, (l : Γ)⁆, Subgroup.commutator_mem_commutator hy hl, hs.map_commutator l hy⟩
  have he : ∀ b : F, b ≠ 0 → ∀ w : V4 F, w (.inr 0) = 1 → e₁ F - b • w ∈ S := by
    intro b hb w hw
    obtain ⟨l, hl, hlw⟩ := hs.exists_mulVec_e₁ hb hw
    have := hgen l hl (e₁ F)
    rwa [hlw] at this
  have hperp : ∀ w : V4 F, w (.inr 0) = 0 → w ∈ S := by
    intro w hw
    have h1 := he 1 one_ne_zero (f₁ F - w) (by simp [hw])
    have h2 := hneg _ (he 1 one_ne_zero (f₁ F) (by simp))
    have := hadd _ h1 _ h2
    rwa [one_smul, one_smul, show e₁ F - (f₁ F - w) + -(e₁ F - f₁ F) = w by abel] at this
  have hf : ∀ s : F, s • f₁ F ∈ S := by
    intro s
    by_cases hs0 : s = 0
    · rw [hs0, zero_smul]
      exact hzero
    · have h1 := hneg _ (he s hs0 (f₁ F) (by simp))
      have := hadd _ (hperp (e₁ F) (by simp)) _ h1
      rwa [show e₁ F + -(e₁ F - s • f₁ F) = s • f₁ F by abel] at this
  have := hadd _ (hperp (w - w (.inr 0) • f₁ F) (by simp)) _ (hf (w (.inr 0)))
  rwa [sub_add_cancel] at this

end CharTwo

section Comm

variable (hs : Setup A Lt V Bk a βv)
  (hcomm : ⁅⁅V, Lt⁆, Bk⁆ = ⊥)
  (hD : ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ Subgroup.centralizer (Lt : Set Γ))
  (hV₀ : ⁅⁅V, Lt⁆, Lt⁆ = ⁅V, Lt⁆)

include hD hV₀ in
theorem comm_central {c u : Γ} (hc : c ∈ ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆) (hu : u ∈ ⁅V, Lt⁆) :
    c * u = u * c := by
  set V₀ := ⁅V, Lt⁆ with hV₀def
  have hDL : ⁅⁅V₀, V₀⁆, Lt⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hD
  have hn : V₀ ≤ Subgroup.normalizer ((⁅V₀, V₀⁆ : Subgroup Γ) : Set Γ) :=
    le_normalizer_commutator (Subgroup.le_normalizer) (Subgroup.le_normalizer)
  have h1 : ⁅⁅Lt, ⁅V₀, V₀⁆⁆, V₀⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Lt, hDL, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅⁅V₀, V₀⁆, V₀⁆, Lt⁆ = ⊥ := by
    rw [← le_bot_iff, ← hDL]
    exact Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.1 hn) le_rfl
  have key := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hV₀] at key
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 key hu
  exact (Subgroup.mem_centralizer_iff.1 this c hc)

include hD hV₀ in
theorem commutator_mul_left {x u v : Γ} (hx : x ∈ ⁅V, Lt⁆) (hu : u ∈ ⁅V, Lt⁆)
    (hv : v ∈ ⁅V, Lt⁆) : ⁅u * v, x⁆ = ⁅u, x⁆ * ⁅v, x⁆ := by
  have hc : ⁅v, x⁆ ∈ ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ := Subgroup.commutator_mem_commutator hv hx
  have hux : ⁅u, x⁆ ∈ ⁅V, Lt⁆ := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu hx) (inv_mem hu)) (inv_mem hx)
  have e : ⁅u * v, x⁆ = u * ⁅v, x⁆ * u⁻¹ * ⁅u, x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, (comm_central hD hV₀ hc hu).symm, mul_inv_cancel_right,
    comm_central hD hV₀ hc hux]

include hD hV₀ in
theorem commutator_mul_right {u v v' : Γ} (hu : u ∈ ⁅V, Lt⁆) (hv : v ∈ ⁅V, Lt⁆)
    (hv' : v' ∈ ⁅V, Lt⁆) : ⁅u, v * v'⁆ = ⁅u, v⁆ * ⁅u, v'⁆ := by
  have hc : ⁅u, v'⁆ ∈ ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ := Subgroup.commutator_mem_commutator hu hv'
  have e : ⁅u, v * v'⁆ = ⁅u, v⁆ * (v * ⁅u, v'⁆ * v⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, (comm_central hD hV₀ hc hv).symm, mul_inv_cancel_right]

include hcomm in
theorem commutator_eq_one_of_mem_bk {u z : Γ} (hu : u ∈ ⁅V, Lt⁆) (hz : z ∈ Bk) : ⁅u, z⁆ = 1 := by
  have := Subgroup.commutator_mem_commutator hu hz
  rwa [hcomm, Subgroup.mem_bot] at this

include hcomm in
theorem commutator_eq_one_of_mem_bk' {u z : Γ} (hu : u ∈ ⁅V, Lt⁆) (hz : z ∈ Bk) :
    ⁅z, u⁆ = 1 := by
  rw [← commutatorElement_inv, commutator_eq_one_of_mem_bk hcomm hu hz, inv_one]

include hs hcomm hD in
theorem commutator_conj_eq {x u : Γ} (hx : x ∈ ⁅V, Lt⁆) (hu : u ∈ ⁅V, Lt⁆) (l : ↥A)
    (hl : (l : Γ) ∈ Lt) (hfix : mat (a l) *ᵥ βv x = βv x) :
    ⁅(l : Γ) * u * (l : Γ)⁻¹, x⁆ = ⁅u, x⁆ := by
  have hn := hs.le_normalizer_comm l.2
  have hlx : (l : Γ) * x * (l : Γ)⁻¹ ∈ ⁅V, Lt⁆ := conj_mem hn hx
  have hlu : (l : Γ) * u * (l : Γ)⁻¹ ∈ ⁅V, Lt⁆ := conj_mem hn hu
  set c := ((l : Γ) * x * (l : Γ)⁻¹)⁻¹ * x with hcdef
  have hcV₀ : c ∈ ⁅V, Lt⁆ := mul_mem (inv_mem hlx) hx
  have hcB : c ∈ Bk := by
    refine (hs.ker c (hs.comm_le hcV₀)).1 ?_
    rw [hcdef, hs.map_mul _ (inv_mem (hs.comm_le hlx)) _ (hs.comm_le hx),
      hs.map_inv (hs.comm_le hlx), hs.equiv l x (hs.comm_le hx), hfix, neg_add_cancel]
  have hx' : x = ((l : Γ) * x * (l : Γ)⁻¹) * c := by rw [hcdef, mul_inv_cancel_left]
  have e : ⁅(l : Γ) * u * (l : Γ)⁻¹, ((l : Γ) * x * (l : Γ)⁻¹) * c⁆ =
      ⁅(l : Γ) * u * (l : Γ)⁻¹, (l : Γ) * x * (l : Γ)⁻¹⁆ * ((l : Γ) * x * (l : Γ)⁻¹) *
        ⁅(l : Γ) * u * (l : Γ)⁻¹, c⁆ * ((l : Γ) * x * (l : Γ)⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hcen : ⁅u, x⁆ ∈ Subgroup.centralizer (Lt : Set Γ) :=
    hD (Subgroup.commutator_mem_commutator hu hx)
  have e2 : ⁅(l : Γ) * u * (l : Γ)⁻¹, (l : Γ) * x * (l : Γ)⁻¹⁆ = (l : Γ) * ⁅u, x⁆ * (l : Γ)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hx', e, commutator_eq_one_of_mem_bk hcomm hlu hcB, mul_one, mul_inv_cancel_right, e2,
    (Subgroup.mem_centralizer_iff.1 hcen _ hl), mul_inv_cancel_right, ← hx']

end Comm

section Card

variable [CharP F 2] (hs : Setup A Lt V Bk a βv)
  (hcomm : ⁅⁅V, Lt⁆, Bk⁆ = ⊥)
  (hD : ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ Subgroup.centralizer (Lt : Set Γ))
  (hV₀ : ⁅⁅V, Lt⁆, Lt⁆ = ⁅V, Lt⁆)

include hs hcomm hD hV₀ in
theorem exists_perp {x : Γ} (hx : x ∈ ⁅V, Lt⁆) (hxe : βv x = e₁ F) {y : V4 F}
    (hy : y (.inr 0) = 0) : ∃ u ∈ ⁅V, Lt⁆, βv u = y ∧ ⁅u, x⁆ = 1 := by
  have key : ∀ y : V4 F, y (.inr 0) = 0 → (y (.inl 1) ≠ 0 ∨ y (.inr 1) ≠ 0) →
      ∃ u ∈ ⁅V, Lt⁆, βv u = y ∧ ⁅u, x⁆ = 1 := by
    intro y hy hy'
    obtain ⟨v, hv0, hyv⟩ := exists_form_eq_one_of_perp_e₁ hy'
    have hab : (1 : F) * 1 = 1 := one_mul 1
    obtain ⟨l, hl, hal⟩ := hs.ord3 _ (transv_mul_transv_pow_three hyv hab)
    have hfix : mat (a l) *ᵥ βv x = βv x := by
      rw [hal, hxe]
      refine transv_mul_transv_mulVec_of_form ?_ ?_ 1 1
      · rw [form_swap, form_e₁, hy, neg_zero]
      · rw [form_swap, form_e₁, hv0, neg_zero]
    obtain ⟨u₁, hu₁, hu₁v⟩ := hs.exists_comm_vec v
    have hn := hs.le_normalizer_comm l.2
    have hlu : (l : Γ) * u₁ * (l : Γ)⁻¹ ∈ ⁅V, Lt⁆ := conj_mem hn hu₁
    refine ⟨(l : Γ) * u₁ * (l : Γ)⁻¹ * u₁⁻¹, mul_mem hlu (inv_mem hu₁), ?_, ?_⟩
    · rw [hs.map_conj_mul_inv l (hs.comm_le hu₁), hu₁v, hal, transv_mul_transv_mulVec_right, hyv,
        one_mul, one_smul, add_sub_cancel_left]
    · rw [commutator_mul_left hD hV₀ hx hlu (inv_mem hu₁),
        commutator_conj_eq hs hcomm hD hx hu₁ l hl hfix, ← commutator_mul_left hD hV₀ hx hu₁
        (inv_mem hu₁), mul_inv_cancel, commutatorElement_one_left]
  by_cases hy' : y (.inl 1) ≠ 0 ∨ y (.inr 1) ≠ 0
  · exact key y hy hy'
  · obtain ⟨u₁, hu₁, hu₁y, hu₁x⟩ := key (y + e₂ F) (by simp [hy]) (Or.inl (by
      push Not at hy'
      simp [hy'.1]))
    obtain ⟨u₂, hu₂, hu₂y, hu₂x⟩ := key (-e₂ F) (by simp) (Or.inl (by simp))
    refine ⟨u₁ * u₂, mul_mem hu₁ hu₂, ?_, ?_⟩
    · rw [hs.map_mul _ (hs.comm_le hu₁) _ (hs.comm_le hu₂), hu₁y, hu₂y, add_neg_cancel_right]
    · rw [commutator_mul_left hD hV₀ hx hu₁ hu₂, hu₁x, hu₂x, one_mul]

include hs hcomm hD hV₀ in
theorem commutator_eq_of_coord {x u u' : Γ} (hx : x ∈ ⁅V, Lt⁆) (hxe : βv x = e₁ F)
    (hu : u ∈ ⁅V, Lt⁆) (hu' : u' ∈ ⁅V, Lt⁆) (h : βv u (.inr 0) = βv u' (.inr 0)) :
    ⁅u, x⁆ = ⁅u', x⁆ := by
  have huu : u⁻¹ * u' ∈ ⁅V, Lt⁆ := mul_mem (inv_mem hu) hu'
  have hβ : βv (u⁻¹ * u') = βv u' - βv u := by
    rw [hs.map_mul _ (hs.comm_le (inv_mem hu)) _ (hs.comm_le hu'), hs.map_inv (hs.comm_le hu)]
    abel
  obtain ⟨u'', hu'', hu''y, hu''x⟩ := exists_perp hs hcomm hD hV₀ hx hxe
    (y := βv (u⁻¹ * u')) (by rw [hβ, Pi.sub_apply, h, sub_self])
  set z := u⁻¹ * u' * u''⁻¹ with hz
  have hzV : z ∈ ⁅V, Lt⁆ := mul_mem huu (inv_mem hu'')
  have hzB : z ∈ Bk := by
    refine (hs.ker z (hs.comm_le hzV)).1 ?_
    rw [hz, hs.map_mul _ (hs.comm_le huu) _ (hs.comm_le (inv_mem hu'')),
      hs.map_inv (hs.comm_le hu''), hu''y, add_neg_cancel]
  have h1 : ⁅u⁻¹ * u', x⁆ = 1 := by
    have e : u⁻¹ * u' = z * u'' := by rw [hz, inv_mul_cancel_right]
    rw [e, commutator_mul_left hD hV₀ hx hzV hu'', hu''x, mul_one]
    exact commutator_eq_one_of_mem_bk' hcomm hx hzB
  rw [commutator_mul_left hD hV₀ hx (inv_mem hu) hu'] at h1
  have h2 : ⁅u⁻¹, x⁆ * ⁅u, x⁆ = 1 := by
    rw [← commutator_mul_left hD hV₀ hx (inv_mem hu) hu, inv_mul_cancel,
      commutatorElement_one_left]
  exact mul_left_cancel (h2.trans h1.symm)


include hs hcomm hD hV₀ in
theorem exists_eq_commutator {x u v : Γ} (hx : x ∈ ⁅V, Lt⁆) (hxe : βv x = e₁ F)
    (hu : u ∈ ⁅V, Lt⁆) (hv : v ∈ ⁅V, Lt⁆) : ∃ u' ∈ ⁅V, Lt⁆, ⁅u, v⁆ = ⁅u', x⁆ := by
  set P : Γ → Prop := fun v => v ∈ ⁅V, Lt⁆ ∧ ∀ u ∈ ⁅V, Lt⁆, ∃ u' ∈ ⁅V, Lt⁆, ⁅u, v⁆ = ⁅u', x⁆
    with hP
  have hmul : ∀ v v', P v → P v' → P (v * v') := by
    rintro v v' ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨mul_mem hv hw, fun u hu => ?_⟩
    obtain ⟨u₁, hu₁, e₁'⟩ := hv' u hu
    obtain ⟨u₂, hu₂, e₂'⟩ := hw' u hu
    refine ⟨u₁ * u₂, mul_mem hu₁ hu₂, ?_⟩
    rw [commutator_mul_right hD hV₀ hu hv hw, e₁', e₂', commutator_mul_left hD hV₀ hx hu₁ hu₂]
  have hB : ∀ z ∈ ⁅V, Lt⁆, z ∈ Bk → P z := fun z hz hzB =>
    ⟨hz, fun u hu => ⟨1, one_mem _, by
      rw [commutator_eq_one_of_mem_bk hcomm hu hzB, commutatorElement_one_left]⟩⟩
  have hconj : ∀ l : ↥A, (l : Γ) ∈ Lt → P ((l : Γ) * x * (l : Γ)⁻¹) := by
    intro l hl
    refine ⟨conj_mem (hs.le_normalizer_comm l.2) hx, fun u hu => ?_⟩
    have hlu : (l : Γ)⁻¹ * u * (l : Γ) ∈ ⁅V, Lt⁆ := by
      have := conj_mem (hs.le_normalizer_comm (inv_mem l.2)) hu
      simpa using this
    refine ⟨(l : Γ)⁻¹ * u * (l : Γ), hlu, ?_⟩
    have hcen : ⁅(l : Γ)⁻¹ * u * (l : Γ), x⁆ ∈ Subgroup.centralizer (Lt : Set Γ) :=
      hD (Subgroup.commutator_mem_commutator hlu hx)
    have e : ⁅u, (l : Γ) * x * (l : Γ)⁻¹⁆ = (l : Γ) * ⁅(l : Γ)⁻¹ * u * (l : Γ), x⁆ * (l : Γ)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, (Subgroup.mem_centralizer_iff.1 hcen _ hl), mul_inv_cancel_right]
  have himage : ∀ w : V4 F, ∃ v, P v ∧ βv v = w := by
    have hadd : ∀ w w', (∃ v, P v ∧ βv v = w) → (∃ v, P v ∧ βv v = w') →
        ∃ v, P v ∧ βv v = w + w' := by
      rintro _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
      exact ⟨v * v', hmul v v' hv hv', hs.map_mul _ (hs.comm_le hv.1) _ (hs.comm_le hv'.1)⟩
    have hb : ∀ b : F, b ≠ 0 → ∀ w : V4 F, w (.inr 0) = 1 → ∃ v, P v ∧ βv v = b • w := by
      intro b hb w hw
      obtain ⟨l, hl, hlw⟩ := hs.exists_mulVec_e₁ hb hw
      exact ⟨_, hconj l hl, by rw [hs.equiv l x (hs.comm_le hx), hxe, hlw]⟩
    intro w
    by_cases hw : w (.inr 0) = 0
    · have h1 := hb 1 one_ne_zero (w + f₁ F) (by simp [hw])
      have h2 := hb (-1) (neg_ne_zero.2 one_ne_zero) (f₁ F) (by simp)
      have := hadd _ _ h1 h2
      rwa [one_smul, neg_one_smul, add_neg_cancel_right] at this
    · have := hb (w (.inr 0)) hw ((w (.inr 0))⁻¹ • w) (by simp [inv_mul_cancel₀ hw])
      rwa [smul_smul, mul_inv_cancel₀ hw, one_smul] at this
  obtain ⟨v', hv'P, hv'β⟩ := himage (βv v)
  have hz : v'⁻¹ * v ∈ ⁅V, Lt⁆ := mul_mem (inv_mem hv'P.1) hv
  have hzB : v'⁻¹ * v ∈ Bk := by
    refine (hs.ker _ (hs.comm_le hz)).1 ?_
    rw [hs.map_mul _ (hs.comm_le (inv_mem hv'P.1)) _ (hs.comm_le hv),
      hs.map_inv (hs.comm_le hv'P.1), hv'β, neg_add_cancel]
  have := hmul _ _ hv'P (hB _ hz hzB)
  rw [mul_inv_cancel_left] at this
  exact this.2 u hu

include hs hcomm hD hV₀ in
theorem card_comm_le [Fintype F] : Nat.card ↥⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ Fintype.card F := by
  obtain ⟨x, hx, hxe⟩ := hs.exists_comm_vec (e₁ F)
  choose u hu hu' using fun s : F => hs.exists_comm_vec (s • f₁ F)
  have hinv : ∀ w ∈ ⁅V, Lt⁆, ⁅w⁻¹, x⁆ = ⁅w, x⁆⁻¹ := fun w hw => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← commutator_mul_left hD hV₀ hx (inv_mem hw) hw, inv_mul_cancel,
      commutatorElement_one_left]
  let R : Subgroup Γ :=
    { carrier := {g | ∃ w ∈ ⁅V, Lt⁆, ⁅w, x⁆ = g}
      one_mem' := ⟨1, one_mem _, commutatorElement_one_left x⟩
      mul_mem' := by
        rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨w * w', mul_mem hw hw', commutator_mul_left hD hV₀ hx hw hw'⟩
      inv_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, inv_mem hw, hinv w hw⟩ }
  have hle : ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro w hw w' hw'
    obtain ⟨u', hu'V, he⟩ := exists_eq_commutator hs hcomm hD hV₀ hx hxe hw hw'
    exact ⟨u', hu'V, he.symm⟩
  have hsub : ((⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ : Subgroup Γ) : Set Γ) ⊆
      Set.range fun s : F => ⁅u s, x⁆ := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := hle hg
    refine ⟨βv w (.inr 0), ?_⟩
    refine commutator_eq_of_coord hs hcomm hD hV₀ hx hxe (hu _) hw ?_
    rw [hu']
    simp
  calc Nat.card ↥⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ Nat.card ↥(Set.range fun s : F => ⁅u s, x⁆) :=
        Nat.card_mono (Set.finite_range _) hsub
    _ ≤ Nat.card F := Finite.card_range_le _
    _ = Fintype.card F := Nat.card_eq_fintype_card

end Card

end Setup

end CFSG.Quasithin.MS93.S310
