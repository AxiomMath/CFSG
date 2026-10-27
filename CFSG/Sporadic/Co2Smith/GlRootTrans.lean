module

public import CFSG.Sporadic.Co2Smith.GlRootFrame
public import CFSG.Sporadic.Co2Smith.GlDataF0
public import CFSG.Sporadic.Co2Smith.GlU62WeylCheck

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def wGen (i : ℕ) : K :=
  if i = 0 then w1K else if i = 1 then w2K else if i = 2 then w3K else if i = 3 then δ0hK
  else δ1hK

theorem wGen_val {i : ℕ} (hi : i < 5) :
    (wGen i).val.val = rowsMatrix 22 (Native.glWGen.getD i #[]) := by
  unfold wGen
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · exact w1K_val
  · exact w2K_val
  · exact w3K_val
  · exact δ0hK_val
  · exact δ1hK_val

theorem glWeyl_spec :
    ∀ g < 5, ∀ r < 18, ∀ t < 4, (Native.glWAct g r t).1 < 18 ∧ (Native.glWAct g r t).2 < 4 ∧
      Native.glConj (Native.glWGen.getD g #[]) (Native.glRootRows r t) =
        Native.glRootRows (Native.glWAct g r t).1 (Native.glWAct g r t).2 := by
  have h := glWeylChart_check
  simp only [Native.glWeylChartOK, Native.glWeylOK, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, beq_iff_eq] at h
  intro g hg r hr t ht
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 g hg r hr t ht
  exact ⟨h1, h2, h3⟩

theorem conj_xRootK {g r t : ℕ}
    (hg : g < 5) (hr : r < 18) (ht : t < 4) :
    wGen g * xRootK r t * wGen g = xRootK (Native.glWAct g r t).1 (Native.glWAct g r t).2 :=
  eq_of_val_rows (val_mul3 (wGen_val hg) (xRootK_val r t) (wGen_val hg)) (xRootK_val _ _)
    (glWeyl_spec g hg r hr t ht).2.2

theorem w1K_mul_self :
    w1K * w1K = 1 := by
  have h0 := xLongK_mul_self (k := 0) (by norm_num)
  have h3 := xLongK_mul_self (k := 3) (by norm_num)
  change xLongK 0 * xLongK 0 = 1 at h0
  have e0 : xLongK 0 = x16K := rfl
  have e3 : xLongK 3 = x61K := rfl
  rw [e0] at h0
  rw [e3] at h3
  rw [w1K, show x16K * x61K * x16K * (x16K * x61K * x16K) =
    x16K * x61K * (x16K * x16K) * x61K * x16K by group, h0, mul_one,
    show x16K * x61K * x61K * x16K = x16K * (x61K * x61K) * x16K by group, h3, mul_one, h0]

theorem w2K_mul_self :
    w2K * w2K = 1 := by
  rw [w2K, show δ1hK * w1K * δ1hK * (δ1hK * w1K * δ1hK) =
    δ1hK * w1K * (δ1hK * δ1hK) * w1K * δ1hK by group, δ1hK_mul_self, mul_one,
    show δ1hK * w1K * w1K * δ1hK = δ1hK * (w1K * w1K) * δ1hK by group, w1K_mul_self, mul_one,
    δ1hK_mul_self]

theorem w3K_mul_self :
    w3K * w3K = 1 := by
  rw [w3K, show δ0hK * w2K * δ0hK * (δ0hK * w2K * δ0hK) =
    δ0hK * w2K * (δ0hK * δ0hK) * w2K * δ0hK by group, δ0hK_mul_self, mul_one,
    show δ0hK * w2K * w2K * δ0hK = δ0hK * (w2K * w2K) * δ0hK by group, w2K_mul_self, mul_one,
    δ0hK_mul_self]

theorem wGen_mul_self {i : ℕ}
    (hi : i < 5) : wGen i * wGen i = 1 := by
  unfold wGen
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · exact w1K_mul_self
  · exact w2K_mul_self
  · exact w3K_mul_self
  · exact δ0hK_mul_self
  · exact δ1hK_mul_self

theorem wGen_inv {i : ℕ}
    (hi : i < 5) : (wGen i)⁻¹ = wGen i :=
  inv_eq_of_mul_eq_one_right (wGen_mul_self hi)

theorem wGen_rootSet
    {i : ℕ} (hi : i < 5) {y : K} (hy : y ∈ rootSet) :
    wGen i * y * (wGen i)⁻¹ ∈ rootSet := by
  obtain ⟨r, hr, t, ht, rfl⟩ := hy
  rw [wGen_inv hi, conj_xRootK hi hr ht]
  exact ⟨_, (glWeyl_spec i hi r hr t ht).1, _, (glWeyl_spec i hi r hr t ht).2.1, rfl⟩

theorem xRootK_comm_of_inChart
    {r k : ℕ} (hr : r < 18) (hk : k < 6) (h : Native.glInChart r k = true) {t : ℕ}
    (ht4 : t < 4) : xRootK r t * xLongK k = xLongK k * xRootK r t := by
  by_cases ht : t = 0
  · subst ht
    simp [xRootK]
  have ht' : (t == 0) = false := by simpa using ht
  by_cases hr12 : r < 12
  · simp only [Native.glInChart, hr12, ite_true, decide_eq_true_eq] at h
    exact xRootK_comm_long hr12 hk h (by simp; omega)
  · simp only [Native.glInChart, hr12, ite_false, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq] at h
    have e : xRootK r t = xLongK (r - 12) := by
      unfold xRootK
      simp only [ht', Bool.false_eq_true, ite_false, hr12, show ¬ r < 6 by omega]
    rw [e]
    rcases h with h | h
    · rw [h]
    · exact xLongK_comm (by omega) hk h

theorem xRootK_mem_Cz_of_inChart
    {r : ℕ} (hr : r < 18) (h : Native.glInChart r 0 = true) {t : ℕ} (ht : t < 4) :
    xRootK r t ∈ Cz := by
  apply mem_Cz_of_comm
  rw [← xLongK_zero]
  exact xRootK_comm_of_inChart hr (by norm_num) h ht

section Transport

variable
  {G : Type*} [Group G] {z : G} {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}
  {α3c : Cz}

theorem transp_of_mem_Cz (hm : SmithC0Marking φ α3c ρ) {g : K} (hg : g ∈ C0c) (hz : g ∈ Cz)
    (hw : g * w1K = w1K * g) (hR : ∀ y ∈ rootSet, g * y * g⁻¹ ∈ rootSet) : Transp φ ρ g := by
  refine ⟨hR, fun y _ => ?_⟩
  by_cases hy : y ∈ Cz
  · have hy' : g * y * g⁻¹ ∈ Cz := Cz.mul_mem (Cz.mul_mem hz hy) (Cz.inv_mem hz)
    rw [psiE_of_mem φ ρ hy, psiE_of_mem φ ρ hy', rhoK_conj_phiInv hm hg hz]
  · have hy' : g * y * g⁻¹ ∉ Cz := fun h => hy (by
      have := Cz.mul_mem (Cz.mul_mem (Cz.inv_mem hz) h) hz
      simpa [mul_assoc] using this)
    rw [psiE_of_not_mem φ ρ hy, psiE_of_not_mem φ ρ hy']
    have hwc : rhoK ρ g * rhoK ρ w1K = rhoK ρ w1K * rhoK ρ g := by
      rw [← rhoK_mul ρ hg w1K_mem_C0c, hw, rhoK_mul ρ w1K_mem_C0c hg]
    have e1 : g * (w1K * y * w1K) * g⁻¹ = w1K * (g * y * g⁻¹) * w1K := by
      have hw' : w1K * g⁻¹ = g⁻¹ * w1K := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hw, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [show g * (w1K * y * w1K) * g⁻¹ = (g * w1K) * y * (w1K * g⁻¹) by group, hw, hw']
      group
    calc rhoK ρ g * (rhoK ρ w1K * phiInv φ (w1K * y * w1K) * (rhoK ρ w1K)⁻¹) * (rhoK ρ g)⁻¹
        = rhoK ρ w1K * (rhoK ρ g * phiInv φ (w1K * y * w1K) * (rhoK ρ g)⁻¹) *
            (rhoK ρ w1K)⁻¹ := by
          rw [show rhoK ρ g * (rhoK ρ w1K * phiInv φ (w1K * y * w1K) * (rhoK ρ w1K)⁻¹) *
              (rhoK ρ g)⁻¹ = (rhoK ρ g * rhoK ρ w1K) * phiInv φ (w1K * y * w1K) *
              (rhoK ρ g * rhoK ρ w1K)⁻¹ by group, hwc]
          group
      _ = rhoK ρ w1K * phiInv φ (w1K * (g * y * g⁻¹) * w1K) * (rhoK ρ w1K)⁻¹ := by
          rw [rhoK_conj_phiInv hm hg hz, e1]

theorem w2K_eq : w2K = x25K * x52K * x25K := by
  rw [w2K, w1K, x25K, x52K]
  have h := δ1hK_mul_self
  calc δ1hK * (x16K * x61K * x16K) * δ1hK
      = δ1hK * x16K * (δ1hK * δ1hK) * x61K * (δ1hK * δ1hK) * x16K * δ1hK := by
        rw [h]; group
    _ = δ1hK * x16K * δ1hK * (δ1hK * x61K * δ1hK) * (δ1hK * x16K * δ1hK) := by group

theorem comm_mul3 {a b c d : K} (ha : a * d = d * a) (hb : b * d = d * b) (hc : c * d = d * c) :
    a * b * c * d = d * (a * b * c) := by
  rw [mul_assoc, hc, ← mul_assoc, mul_assoc a, hb, ← mul_assoc, ha]
  group

theorem xLongK_comm_lit {k l : ℕ} (hk : k < 6) (hl : l < 6) (h : k % 3 ≠ l % 3) :
    xLongK k * xLongK l = xLongK l * xLongK k := xLongK_comm hk hl h

theorem w2K_comm_long {l : ℕ} (hl : l < 6) (h : l % 3 ≠ 1) : w2K * xLongK l = xLongK l * w2K := by
  rw [w2K_eq]
  have h1 : x25K * xLongK l = xLongK l * x25K := xLongK_comm_lit (k := 1) (by norm_num) hl
    (by omega)
  have h4 : x52K * xLongK l = xLongK l * x52K := xLongK_comm_lit (k := 4) (by norm_num) hl
    (by omega)
  exact comm_mul3 h1 h4 h1

theorem comm_w1K {g : K} (h0 : g * x16K = x16K * g) (h3 : g * x61K = x61K * g) :
    g * w1K = w1K * g := by
  rw [w1K]
  have := comm_mul3 h0.symm h3.symm h0.symm
  exact this.symm

theorem w2K_mem_Cz : w2K ∈ Cz := mem_Cz_of_comm (by
  have := w2K_comm_long (l := 0) (by norm_num) (by norm_num)
  rwa [xLongK_zero] at this)

theorem δ0hK_mem_Cz : δ0hK ∈ Cz := mem_Cz_of_comm (by
  rw [← x16K_eq]
  exact δhK_comm.1)

theorem w2K_comm_w1K : w2K * w1K = w1K * w2K :=
  comm_w1K (w2K_comm_long (l := 0) (by norm_num) (by norm_num))
    (w2K_comm_long (l := 3) (by norm_num) (by norm_num))

theorem δ0hK_comm_w1K : δ0hK * w1K = w1K * δ0hK :=
  comm_w1K δhK_comm.1 δhK_comm.2.1

theorem wGen_one : wGen 1 = w2K := rfl
theorem wGen_three : wGen 3 = δ0hK := rfl
theorem wGen_zero : wGen 0 = w1K := rfl
theorem wGen_four : wGen 4 = δ1hK := rfl

theorem transp_w2 (hm : SmithC0Marking φ α3c ρ) : Transp φ ρ w2K :=
  transp_of_mem_Cz hm w2K_mem_C0c w2K_mem_Cz w2K_comm_w1K
    (fun y hy => wGen_one ▸ wGen_rootSet (by norm_num) hy)

theorem transp_d0 (hm : SmithC0Marking φ α3c ρ) : Transp φ ρ δ0hK :=
  transp_of_mem_Cz hm δ0hK_mem_C0c δ0hK_mem_Cz δ0hK_comm_w1K
    (fun y hy => wGen_three ▸ wGen_rootSet (by norm_num) hy)

@[expose] def W1Levi (φ : centralizer ({z} : Set G) ≃* Cz) (ρ : C0c →* G) : Prop :=
  ∀ y ∈ rootSet, y ∈ Cz → w1K * y * w1K ∈ Cz →
    rhoK ρ w1K * phiInv φ y * (rhoK ρ w1K)⁻¹ = phiInv φ (w1K * y * w1K)

theorem transp_w1 (hL : W1Levi φ ρ) : Transp φ ρ w1K := by
  have hinv : w1K⁻¹ = w1K := inv_eq_of_mul_eq_one_right w1K_mul_self
  have hρ : rhoK ρ w1K * rhoK ρ w1K = 1 := by
    rw [← rhoK_mul ρ w1K_mem_C0c w1K_mem_C0c, w1K_mul_self, rhoK_one]
  have hρi : (rhoK ρ w1K)⁻¹ = rhoK ρ w1K := inv_eq_of_mul_eq_one_right hρ
  have hyy : ∀ y : K, w1K * (w1K * y * w1K) * w1K = y := fun y => by
    rw [show w1K * (w1K * y * w1K) * w1K = (w1K * w1K) * y * (w1K * w1K) by group, w1K_mul_self]
    group
  refine ⟨fun y hy => wGen_zero ▸ wGen_rootSet (by norm_num) hy, fun y hy => ?_⟩
  rw [hinv]
  by_cases hy1 : y ∈ Cz
  · by_cases hy2 : w1K * y * w1K ∈ Cz
    · rw [psiE_of_mem φ ρ hy1, psiE_of_mem φ ρ hy2]
      exact hL y hy hy1 hy2
    · rw [psiE_of_mem φ ρ hy1, psiE_of_not_mem φ ρ hy2, hyy]
  · rw [psiE_of_not_mem φ ρ hy1, hρi]
    by_cases hy2 : w1K * y * w1K ∈ Cz
    · rw [psiE_of_mem φ ρ hy2, show rhoK ρ w1K * (rhoK ρ w1K * phiInv φ (w1K * y * w1K) *
        rhoK ρ w1K) * rhoK ρ w1K = (rhoK ρ w1K * rhoK ρ w1K) * phiInv φ (w1K * y * w1K) *
        (rhoK ρ w1K * rhoK ρ w1K) by group, hρ, one_mul, mul_one]
    · rw [psiE_of_not_mem φ ρ hy2, hyy, phiInv_of_not_mem φ hy1, phiInv_of_not_mem φ hy2, hρi]
      simp only [mul_one]
      rw [show rhoK ρ w1K * (rhoK ρ w1K * rhoK ρ w1K) * rhoK ρ w1K =
          (rhoK ρ w1K * rhoK ρ w1K) * (rhoK ρ w1K * rhoK ρ w1K) by group, hρ, one_mul]

@[expose] def D1Core (φ : centralizer ({z} : Set G) ≃* Cz) (ρ : C0c →* G) : Prop :=
  ∀ y ∈ rootSet, y ∈ Cz → δ1hK * y * δ1hK ∈ Cz →
    rhoK ρ δ1hK * phiInv φ y * (rhoK ρ δ1hK)⁻¹ = phiInv φ (δ1hK * y * δ1hK)

theorem transp_d1_at (hD : D1Core φ ρ) {a : K} (ha : a ∈ C0c) (Pa : Transp φ ρ a)
    (Pc : Transp φ ρ (δ1hK * a⁻¹ * δ1hK)) {y : K} (hy : y ∈ rootSet)
    (h1 : a * y * a⁻¹ ∈ Cz) (h2 : δ1hK * (a * y * a⁻¹) * δ1hK ∈ Cz) :
    rhoK ρ δ1hK * psiE φ ρ y * (rhoK ρ δ1hK)⁻¹ = psiE φ ρ (δ1hK * y * δ1hK⁻¹) := by
  have hd := δ1hK_mul_self
  have hc : δ1hK * a⁻¹ * δ1hK ∈ C0c :=
    C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c (C0c.inv_mem ha)) δ1hK_mem_C0c
  have hdec : δ1hK = (δ1hK * a⁻¹ * δ1hK) * δ1hK * a := by
    rw [show δ1hK * a⁻¹ * δ1hK * δ1hK * a = δ1hK * a⁻¹ * (δ1hK * δ1hK) * a by group, hd]
    group
  have hρd : rhoK ρ δ1hK = rhoK ρ (δ1hK * a⁻¹ * δ1hK) * rhoK ρ δ1hK * rhoK ρ a := by
    conv_lhs => rw [hdec]
    rw [rhoK_mul ρ (C0c.mul_mem hc δ1hK_mem_C0c) ha, rhoK_mul ρ hc δ1hK_mem_C0c]
  have hy' := Pa.1 y hy
  have hy'' := wGen_four ▸ wGen_rootSet (i := 4) (by norm_num) hy'
  have hdi : δ1hK⁻¹ = δ1hK := inv_eq_of_mul_eq_one_right hd
  rw [hdi] at hy''
  have e1 := Pa.2 y hy
  have e2 := hD _ hy' h1 h2
  have e3 := Pc.2 _ hy''
  rw [psiE_of_mem φ ρ h2] at e3
  rw [psiE_of_mem φ ρ h1] at e1
  rw [hρd, show rhoK ρ (δ1hK * a⁻¹ * δ1hK) * rhoK ρ δ1hK * rhoK ρ a * psiE φ ρ y *
      (rhoK ρ (δ1hK * a⁻¹ * δ1hK) * rhoK ρ δ1hK * rhoK ρ a)⁻¹ =
      rhoK ρ (δ1hK * a⁻¹ * δ1hK) * (rhoK ρ δ1hK * (rhoK ρ a * psiE φ ρ y * (rhoK ρ a)⁻¹) *
        (rhoK ρ δ1hK)⁻¹) * (rhoK ρ (δ1hK * a⁻¹ * δ1hK))⁻¹ by group, e1, e2, e3]
  congr 1
  rw [show (δ1hK * a⁻¹ * δ1hK)⁻¹ = δ1hK⁻¹ * a * δ1hK⁻¹ by group, hdi,
    show δ1hK * a⁻¹ * δ1hK * (δ1hK * (a * y * a⁻¹) * δ1hK) * (δ1hK * a * δ1hK) =
      δ1hK * a⁻¹ * (δ1hK * δ1hK) * a * y * a⁻¹ * (δ1hK * δ1hK) * a * δ1hK by group, hd]
  group

theorem d1_chart_choice : ∀ r < 18, ∀ t < 4,
    (Native.glInChart r 0 = true ∧ Native.glInChart (Native.glWAct 4 r t).1 0 = true) ∨
    (Native.glInChart (Native.glWAct 0 r t).1 0 = true ∧
      Native.glInChart (Native.glWAct 4 (Native.glWAct 0 r t).1 (Native.glWAct 0 r t).2).1 0 =
        true) ∨
    (Native.glInChart (Native.glWAct 1 r t).1 0 = true ∧
      Native.glInChart (Native.glWAct 4 (Native.glWAct 1 r t).1 (Native.glWAct 1 r t).2).1 0 =
        true) ∨
    (Native.glInChart (Native.glWAct 0 (Native.glWAct 1 r t).1 (Native.glWAct 1 r t).2).1 0 =
        true ∧
      Native.glInChart (Native.glWAct 4
        (Native.glWAct 0 (Native.glWAct 1 r t).1 (Native.glWAct 1 r t).2).1
        (Native.glWAct 0 (Native.glWAct 1 r t).1 (Native.glWAct 1 r t).2).2).1 0 = true) := by
  decide

theorem wGen_conj_xRootK {g r t : ℕ} (hg : g < 5) (hr : r < 18) (ht : t < 4) :
    wGen g * xRootK r t * (wGen g)⁻¹ =
      xRootK (Native.glWAct g r t).1 (Native.glWAct g r t).2 := by
  rw [wGen_inv hg, conj_xRootK hg hr ht]

theorem mem_Cz_wAct {g r t : ℕ} (hg : g < 5) (hr : r < 18) (ht : t < 4)
    (h : Native.glInChart (Native.glWAct g r t).1 0 = true) :
    wGen g * xRootK r t * (wGen g)⁻¹ ∈ Cz := by
  rw [wGen_conj_xRootK hg hr ht]
  exact xRootK_mem_Cz_of_inChart (glWeyl_spec g hg r hr t ht).1 h
    (glWeyl_spec g hg r hr t ht).2.1

theorem transp_d1 (hD : D1Core φ ρ) (P1 : Transp φ ρ w1K) (P2 : Transp φ ρ w2K) :
    Transp φ ρ δ1hK := by
  have hd := δ1hK_mul_self
  have hdi : δ1hK⁻¹ = δ1hK := inv_eq_of_mul_eq_one_right hd
  have hw1i : w1K⁻¹ = w1K := inv_eq_of_mul_eq_one_right w1K_mul_self
  have hw2i : w2K⁻¹ = w2K := inv_eq_of_mul_eq_one_right w2K_mul_self
  have ec1 : δ1hK * w1K⁻¹ * δ1hK = w2K := by rw [hw1i]; rfl
  have ec2 : δ1hK * w2K⁻¹ * δ1hK = w1K := by
    rw [hw2i, w2K, show δ1hK * (δ1hK * w1K * δ1hK) * δ1hK =
      (δ1hK * δ1hK) * w1K * (δ1hK * δ1hK) by group, hd]
    group
  have ec12 : δ1hK * (w1K * w2K)⁻¹ * δ1hK = w1K * w2K := by
    rw [_root_.mul_inv_rev, hw1i, hw2i, show δ1hK * (w2K * w1K) * δ1hK =
      (δ1hK * w2K * δ1hK) * (δ1hK * w1K * δ1hK) by
        rw [show δ1hK * w2K * δ1hK * (δ1hK * w1K * δ1hK) =
          δ1hK * w2K * (δ1hK * δ1hK) * w1K * δ1hK by group, hd]
        group]
    rw [show δ1hK * w2K * δ1hK = w1K by rw [← hw2i]; exact ec2]
    rfl
  have ec0 : δ1hK * (1 : K)⁻¹ * δ1hK = 1 := by rw [inv_one, mul_one, hd]
  have P12 : Transp φ ρ (w1K * w2K) := Transp.mul w1K_mem_C0c w2K_mem_C0c P1 P2
  refine ⟨fun y hy => wGen_four ▸ wGen_rootSet (by norm_num) hy, fun y hy => ?_⟩
  obtain ⟨r, hr, t, ht, rfl⟩ := hy
  rcases d1_chart_choice r hr t ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine transp_d1_at hD C0c.one_mem Transp.one (by rw [ec0]; exact Transp.one)
      ⟨r, hr, t, ht, rfl⟩ ?_ ?_
    · simpa using xRootK_mem_Cz_of_inChart hr h1 ht
    · simp only [one_mul, inv_one, mul_one]
      have := mem_Cz_wAct (g := 4) (by norm_num) hr ht h2
      rwa [wGen_four, hdi] at this
  · refine transp_d1_at hD w1K_mem_C0c P1 (by rw [ec1]; exact P2) ⟨r, hr, t, ht, rfl⟩ ?_ ?_
    · exact wGen_zero ▸ mem_Cz_wAct (g := 0) (by norm_num) hr ht h1
    · have e := wGen_conj_xRootK (g := 0) (by norm_num) hr ht
      rw [wGen_zero] at e
      rw [e]
      have := mem_Cz_wAct (g := 4) (by norm_num) (glWeyl_spec 0 (by norm_num) r hr t ht).1
        (glWeyl_spec 0 (by norm_num) r hr t ht).2.1 h2
      rwa [wGen_four, hdi] at this
  · refine transp_d1_at hD w2K_mem_C0c P2 (by rw [ec2]; exact P1) ⟨r, hr, t, ht, rfl⟩ ?_ ?_
    · exact wGen_one ▸ mem_Cz_wAct (g := 1) (by norm_num) hr ht h1
    · have e := wGen_conj_xRootK (g := 1) (by norm_num) hr ht
      rw [wGen_one] at e
      rw [e]
      have := mem_Cz_wAct (g := 4) (by norm_num) (glWeyl_spec 1 (by norm_num) r hr t ht).1
        (glWeyl_spec 1 (by norm_num) r hr t ht).2.1 h2
      rwa [wGen_four, hdi] at this
  · refine transp_d1_at hD (C0c.mul_mem w1K_mem_C0c w2K_mem_C0c) P12 (by rw [ec12]; exact P12)
      ⟨r, hr, t, ht, rfl⟩ ?_ ?_
    · have e := wGen_conj_xRootK (g := 1) (by norm_num) hr ht
      rw [wGen_one] at e
      rw [show w1K * w2K * xRootK r t * (w1K * w2K)⁻¹ =
        w1K * (w2K * xRootK r t * w2K⁻¹) * w1K⁻¹ by group, e]
      exact wGen_zero ▸ mem_Cz_wAct (g := 0) (by norm_num) (glWeyl_spec 1 (by norm_num) r hr t
        ht).1 (glWeyl_spec 1 (by norm_num) r hr t ht).2.1 h1
    · have e := wGen_conj_xRootK (g := 1) (by norm_num) hr ht
      rw [wGen_one] at e
      have e' := wGen_conj_xRootK (g := 0) (by norm_num) (glWeyl_spec 1 (by norm_num) r hr t
        ht).1 (glWeyl_spec 1 (by norm_num) r hr t ht).2.1
      rw [wGen_zero] at e'
      rw [show w1K * w2K * xRootK r t * (w1K * w2K)⁻¹ =
        w1K * (w2K * xRootK r t * w2K⁻¹) * w1K⁻¹ by group, e, e']
      have := mem_Cz_wAct (g := 4) (by norm_num)
        (glWeyl_spec 0 (by norm_num) _ (glWeyl_spec 1 (by norm_num) r hr t ht).1 _
          (glWeyl_spec 1 (by norm_num) r hr t ht).2.1).1
        (glWeyl_spec 0 (by norm_num) _ (glWeyl_spec 1 (by norm_num) r hr t ht).1 _
          (glWeyl_spec 1 (by norm_num) r hr t ht).2.1).2.1 h2
      rwa [wGen_four, hdi] at this

end Transport

end CFSG.Sporadic.Co2Smith
