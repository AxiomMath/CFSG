module

public import CFSG.RankThree.GF2n.Stroth80.Sec103ATools
public import CFSG.RankThree.GF2n.Stroth80.Sec103BCent
public import CFSG.RankThree.GF2n.Stroth80.Sec103BUt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem root_mul_facts (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {y : G} (hy : y ∈ Y)
    (hyt : y ≠ t) :
    (t * y ∈ Y) ∧ (t * y ≠ 1) ∧ (t * y ∈ M) ∧ (t * y) * (t * y) = 1 ∧
      (t * y) * t = t * (t * y) ∧ Good101 M Q Z B (t * y) ∧ SLMNat hc (t * y) 2 ∧
      Sec5Hyp hc n (t * y) ∧ SLNat hc (t * y) ∧ Ut Q Z (t * y) = Ut Q Z t := by
  have ht2 : t * t = 1 := hs.x_sq
  have hy2 : y * y = 1 := hs.X_sq y hy
  have hty : t * y = y * t := hs.X_comm t hs.mem y hy
  have hty2 : (t * y) * (t * y) = 1 := by
    have h1 : (t * y) * t = y := by
      rw [mul_assoc, ← hty, ← mul_assoc, ht2, one_mul]
    calc (t * y) * (t * y) = ((t * y) * t) * y := by group
      _ = y * y := by rw [h1]
      _ = 1 := hy2
  have hsY : t * y ∈ Y := Y.mul_mem hs.mem hy
  have hs1 : t * y ≠ 1 := by
    intro h
    have h1 : y = t := by
      have h' : y = t⁻¹ * (t * y) := by group
      rw [h, mul_one] at h'
      rw [h', inv_eq_of_mul_eq_one_right ht2]
    exact hyt h1
  have hyM : y ∈ M := (Subgroup.mem_inf.mp ((smith_1_12 hs).1 hy)).1
  have hsM : t * y ∈ M := M.mul_mem hs.memM hyM
  have hcomm_st : (t * y) * t = t * (t * y) := by
    have h1 : (t * y) * t = y := by
      rw [mul_assoc, ← hty, ← mul_assoc, ht2, one_mul]
    have h2 : t * (t * y) = y := by rw [← mul_assoc, ht2, one_mul]
    rw [h1, h2]
  have hsg : Good101 M Q Z B (t * y) := ht.of_mem_root_good101 h34 hspread H hs hsY hs1
  have h2s : SLMNat hc (t * y) 2 :=
    (SLMNat.iff_of_mem_root h34 hspread H ht hs hsY hs1).mpr h2
  exact ⟨hsY, hs1, hsM, hty2, hcomm_st, hsg, h2s, H.toSec5 hsg.mem_LB hsg.2.2.1,
    h2s.toSLNat (by norm_num), Good101.Ut_eq_of_mem_root h34 hspread H ht hs hsY hs1⟩

private theorem conj_eq_mul_decomp (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    {a : G} (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    {y : G} (hy : y ∈ Y) (hyt : y ≠ t) :
    ∃ (s x'' : G), s = t * y ∧ s ∈ Y ∧ s ≠ 1 ∧ x'' ∈ Ut Q Z s ∧
      x'' * x'' = 1 ∧ c * t * c⁻¹ * a * y = s * x'' * a := by
  obtain ⟨hsY, hs1, hsM, hty2, hcomm_st, hsg, h2s, h5s, hSLs, hUtEq⟩ :=
    root_mul_facts h34 hspread H ht hs h2 hy hyt
  have ht2 : t * t = 1 := hs.x_sq
  have hxUt : ⁅t, c⁆ ∈ Ut Q Z t := by
    rw [← commutatorElement_inv]
    exact (Ut Q Z t).inv_mem (comm_mem_Ut hcQ)
  have hx''t : (t * y) * ⁅t, c⁆ * (t * y)⁻¹ ∈ Ut Q Z t :=
    hc.conj_mem_Ut hsM hcomm_st hxUt
  have hx''s : (t * y) * ⁅t, c⁆ * (t * y)⁻¹ ∈ Ut Q Z (t * y) := by
    rw [hUtEq]
    exact hx''t
  have hx''2 : ((t * y) * ⁅t, c⁆ * (t * y)⁻¹) * ((t * y) * ⁅t, c⁆ * (t * y)⁻¹) = 1 := by
    simpa [pow_two] using (hc.isElemAbelian_Ut h34 h5s hSLs).2 _ hx''s
  have hct : c * t * c⁻¹ = t * ⁅t, c⁆ := conj_eq_mul_comm_of_mul_self ht2 c
  have hxt : ⁅t, c⁆ * t = t * ⁅t, c⁆ := ht.comm_comm_self h34 H hs hcQ
  have hay : a * y = y * a := (hs.QB_comm_X hy ha.1.2).symm
  have hw1 : c * t * c⁻¹ * a * y = ⁅t, c⁆ * (t * y) * a := by
    rw [hct]
    calc (t * ⁅t, c⁆) * a * y = (t * ⁅t, c⁆) * (a * y) := by rw [mul_assoc]
      _ = (t * ⁅t, c⁆) * (y * a) := by rw [hay]
      _ = ((t * ⁅t, c⁆) * y) * a := by rw [← mul_assoc]
      _ = ((⁅t, c⁆ * t) * y) * a := by rw [hxt.symm]
      _ = (⁅t, c⁆ * (t * y)) * a := by rw [mul_assoc ⁅t, c⁆ t y]
  have hsx : (t * y) * ((t * y) * ⁅t, c⁆ * (t * y)⁻¹) = ⁅t, c⁆ * (t * y) := by
    calc (t * y) * ((t * y) * ⁅t, c⁆ * (t * y)⁻¹) =
        ((t * y) * (t * y)) * ⁅t, c⁆ * (t * y)⁻¹ := by group
      _ = 1 * ⁅t, c⁆ * (t * y)⁻¹ := by rw [hty2]
      _ = ⁅t, c⁆ * (t * y) := by rw [one_mul, inv_eq_of_mul_eq_one_right hty2]
  refine ⟨t * y, (t * y) * ⁅t, c⁆ * (t * y)⁻¹, rfl, hsY, hs1, hx''s, hx''2, ?_⟩
  rw [hw1, ← hsx, mul_assoc]

private theorem exists_z_of_comm {s x'' k : G} (hs2 : s * s = 1) (hx''2 : x'' * x'' = 1)
    (hx''_s : x'' * s = s * x'') (hkz : ⁅k, s⁆ * x''⁻¹ ∈ Z) :
    ∃ z₀ ∈ Z, k * s * k⁻¹ = z₀ * s * x'' := by
  have hx''inv : x''⁻¹ = x'' := inv_eq_of_mul_eq_one_right hx''2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hks_eq : ⁅k, s⁆ = (⁅k, s⁆ * x''⁻¹) * x'' := by
    rw [mul_assoc, hx''inv, hx''2, mul_one]
  have hstep : k * s * k⁻¹ = ⁅k, s⁆ * s := by
    have e : ⁅k, s⁆ = k * s * k⁻¹ * s⁻¹ := commutatorElement_def _ _
    rw [e, hsinv]
    conv_rhs => rw [mul_assoc, hs2, mul_one]
  refine ⟨⁅k, s⁆ * x''⁻¹, hkz, ?_⟩
  calc k * s * k⁻¹ = ⁅k, s⁆ * s := hstep
    _ = ((⁅k, s⁆ * x''⁻¹) * x'') * s := by conv_lhs => rw [hks_eq]
    _ = (⁅k, s⁆ * x''⁻¹) * (x'' * s) := by group
    _ = (⁅k, s⁆ * x''⁻¹) * (s * x'') := by rw [hx''_s]
    _ = (⁅k, s⁆ * x''⁻¹) * s * x'' := by group

private theorem conj_mul_eq_of_comm (hc : Ctx M Q Z B) {s a x'' k z₀ z₁ z₂ : G}
    (hx''2 : x'' * x'' = 1) (hx''Q : x'' ∈ Q) (haQ : a ∈ Q) (hz₁Z : z₁ ∈ Z)
    (hz₂Z : z₂ ∈ Z) (hks : k * s * k⁻¹ = z₀ * s * x'')
    (hkx : k * x'' * k⁻¹ = z₁ * x'') (hka : k * a * k⁻¹ = z₂ * a) :
    k * (s * x'' * a) * k⁻¹ = z₀ * s * a * (z₁ * z₂) := by
  have e1 : k * (s * x'' * a) * k⁻¹ =
      (k * s * k⁻¹) * (k * x'' * k⁻¹) * (k * a * k⁻¹) := by group
  rw [e1, hks, hkx, hka]
  have e2 : (z₀ * s * x'') * (z₁ * x'') * (z₂ * a) =
      z₀ * s * (x'' * z₁ * x'' * z₂ * a) := by group
  rw [e2]
  rw [show z₀ * s * (x'' * z₁ * x'' * z₂ * a) =
      z₀ * s * (z₁ * (x'' * x'') * z₂ * a) by
    rw [← Z_central hc.hyp hz₁Z hx''Q]; group]
  rw [show z₀ * s * (z₁ * (x'' * x'') * z₂ * a) = z₀ * s * (z₁ * z₂ * a) by
    rw [hx''2]; group]
  rw [show z₀ * s * (z₁ * z₂ * a) = z₀ * s * a * (z₁ * z₂) by
    rw [mul_assoc z₁ z₂ a, Z_central hc.hyp hz₂Z haQ,
      ← mul_assoc z₁ a z₂, Z_central hc.hyp hz₁Z haQ]
    group]

private theorem exists_conj_mul_Z_core (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    {a : G} (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    {y : G} (hy : y ∈ Y) (hyt : y ≠ t) :
    ∃ (s k z₀ z₆ : G), s = t * y ∧ s ∈ Y ∧ s ≠ 1 ∧ k ∈ Q ∧ z₀ ∈ Z ∧ z₆ ∈ Z ∧
      k * (c * t * c⁻¹ * a * y) * k⁻¹ = z₀ * s * a * z₆ := by
  obtain ⟨s, x'', hsdef, hsY, hs1, hx''s, hx''2, hw⟩ :=
    conj_eq_mul_decomp h34 hspread H ht hs h2 hcQ ha hy hyt
  subst s
  obtain ⟨-, -, hsM, hty2, hcomm_st, hsg, h2s, h5s, hSLs, -⟩ :=
    root_mul_facts h34 hspread H ht hs h2 hy hyt
  have hUtCent : Ut Q Z (t * y) ≤ Subgroup.centralizer ({(t * y)} : Set G) :=
    hc.Ut_le_centralizer h34 h5s hSLs (by rw [pow_two]; exact hty2)
  have hx''_s : x'' * (t * y) = (t * y) * x'' :=
    Subgroup.mem_centralizer_singleton_iff.mp (hUtCent hx''s)
  have hx''Q : x'' ∈ Q := hc.Ut_le_Q hsM hx''s
  obtain ⟨k, hkQ, hkz⟩ := hc.exists_comm_mul_inv_mem_Z hsg.mem_LB hx''s
  obtain ⟨z₀, hz₀Z, hks⟩ := exists_z_of_comm hty2 hx''2 hx''_s hkz
  set z₁ : G := ⁅k, x''⁆ with hz₁def
  have hz₁Z : z₁ ∈ Z := comm_mem_Z hc.hyp hkQ hx''Q
  have hx''inv : x''⁻¹ = x'' := inv_eq_of_mul_eq_one_right hx''2
  have hsq : (k * x'' * k⁻¹) * x'' * x'' = k * x'' * k⁻¹ := by
    rw [mul_assoc, hx''2, mul_one]
  have hkx : k * x'' * k⁻¹ = z₁ * x'' := by
    have e : z₁ = k * x'' * k⁻¹ * x''⁻¹ := by rw [hz₁def, commutatorElement_def]
    rw [e, hx''inv, hsq]
  set z₂ : G := ⁅k, a⁆ with hz₂def
  have hz₂Z : z₂ ∈ Z := comm_mem_Z hc.hyp hkQ ha.1.1
  have hka : k * a * k⁻¹ = z₂ * a := by
    have e : z₂ = k * a * k⁻¹ * a⁻¹ := by rw [hz₂def, commutatorElement_def]
    rw [e]
    group
  refine ⟨t * y, k, z₀, z₁ * z₂, rfl, hsY, hs1, hkQ, hz₀Z,
    Z.mul_mem hz₁Z hz₂Z, ?_⟩
  rw [hw]
  exact conj_mul_eq_of_comm hc hx''2 hx''Q ha.1.1 hz₁Z hz₂Z hks hkx hka

private theorem exists_conj_of_mem_root {Y : Subgroup G} {t s : G} (hs : Sit M Q Z Y t)
    (hsY : s ∈ Y) (hs1 : s ≠ 1) : ∃ h : G, h * t * h⁻¹ = s := by
  obtain ⟨g, hg⟩ := hs.conj
  have htY : t ∈ conjSubgroup g Z := by rw [← hg]; exact hs.mem
  have hsY' : s ∈ conjSubgroup g Z := by rw [← hg]; exact hsY
  have hz : g⁻¹ * t * g ∈ Z := mem_conjSubgroup.mp htY
  have hz' : g⁻¹ * s * g ∈ Z := mem_conjSubgroup.mp hsY'
  have hz1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    exact hs.ne_one (by
      have e : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      rw [e, h]; group)
  have hz1' : g⁻¹ * s * g ≠ 1 := by
    intro h
    exact hs1 (by
      have e : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      rw [e, h]; group)
  obtain ⟨m, -, hm⟩ := Z_isConj hs.hyp hz hz1 hz' hz1'
  refine ⟨g * m * g⁻¹, ?_⟩
  calc g * m * g⁻¹ * t * (g * m * g⁻¹)⁻¹ =
      g * (m * (g⁻¹ * t * g) * m⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * s * g) * g⁻¹ := by rw [hm]
    _ = s := by group

private theorem caseA_conj_eq_core {w s a k k' z₀ z₆ z : G}
    (hz : z = k⁻¹ * (z₆⁻¹ * z₀⁻¹) * k)
    (hkw : k * w * k⁻¹ = z₀ * s * a * z₆)
    (hk'w : k' * w * k'⁻¹ = w * z) :
    (z₀⁻¹ * (k * k')) * w * (z₀⁻¹ * (k * k'))⁻¹ = s * a := by
  have hkz : k * z * k⁻¹ = z₆⁻¹ * z₀⁻¹ := by rw [hz]; group
  have h1 : k * k' * w * (k * k')⁻¹ = z₀ * s * a * z₀⁻¹ := by
    have e : k * k' * w * (k * k')⁻¹ = k * (k' * w * k'⁻¹) * k⁻¹ := by group
    have e2 : k * (w * z) * k⁻¹ = (k * w * k⁻¹) * (k * z * k⁻¹) := by group
    rw [e, hk'w, e2, hkw, hkz]
    group
  have e : z₀⁻¹ * (k * k') * w * (z₀⁻¹ * (k * k'))⁻¹ =
      z₀⁻¹ * (k * k' * w * (k * k')⁻¹) * z₀ := by group
  rw [e, h1]
  group

private theorem conj_of_conj_eq_core {w s a u c t Hc G1 : G}
    (hHc : Hc * t * Hc⁻¹ = s) (hwU : w = (u * c) * t * (u * c)⁻¹)
    (hEq : G1 * w * G1⁻¹ = s * a) :
    ∃ g : G, g * s * g⁻¹ = s * a := by
  refine ⟨G1 * (u * c) * Hc⁻¹, ?_⟩
  calc G1 * (u * c) * Hc⁻¹ * s * (G1 * (u * c) * Hc⁻¹)⁻¹ =
      G1 * ((u * c) * t * (u * c)⁻¹) * G1⁻¹ := by rw [← hHc]; group
    _ = G1 * w * G1⁻¹ := by rw [hwU]
    _ = s * a := hEq

private theorem caseA_of_conj_eq_mul_core (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    (hcB : c ∈ Subgroup.centralizer (B : Set G)) (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t))
    {a : G} (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (haB : a ∉ B)
    {y : G} (hy : y ∈ Y) (hyt : y ≠ t) {u : G}
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) :
    CaseA Q Z (c * t * c⁻¹ * a * y) := by
  set w : G := c * t * c⁻¹ * a * y with hwdef
  obtain ⟨s, k, z₀, z₆, hsdef, hsY, hs1, hkQ, hz₀Z, hz₆Z, hkw⟩ :=
    exists_conj_mul_Z_core h34 hspread H ht hs h2 hcQ ha hy hyt
  subst s
  rw [← hwdef] at hkw
  obtain ⟨Hc, hHc⟩ := exists_conj_of_mem_root hs hsY hs1
  set z : G := k⁻¹ * (z₆⁻¹ * z₀⁻¹) * k with hzdef
  have hkM : k ∈ M := hc.hyp.Q_normal.1 hkQ
  have hzZ : z ∈ Z := by
    have hmemZ : z₆⁻¹ * z₀⁻¹ ∈ Z := Z.mul_mem (Z.inv_mem hz₆Z) (Z.inv_mem hz₀Z)
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hkM)) _).mp hmemZ
    simpa [hzdef] using this
  refine ⟨z, hzZ, ?_⟩
  intro k' hk'Q hk'w
  have hEq : (z₀⁻¹ * (k * k')) * w * (z₀⁻¹ * (k * k'))⁻¹ = (t * y) * a :=
    caseA_conj_eq_core hzdef hkw hk'w
  have hwU : w = (u * c) * t * (u * c)⁻¹ := by rw [← hconj]; group
  have hconj_s : ∃ g : G, g * (t * y) * g⁻¹ = (t * y) * a :=
    conj_of_conj_eq_core hHc hwU hEq
  have hss : Sit M Q Z Y (t * y) := Sit.of_mem_root hs hsY hs1
  have hsg : Good101 M Q Z B (t * y) := ht.of_mem_root_good101 h34 hspread H hs hsY hs1
  have haV_s : a ∈ Vt M (LB M Q B) B Z (t * y) :=
    hsg.mem_Vt_of_conj h34 hspread H hss ha.1 hconj_s
  have haV_t : a ∈ Vt M (LB M Q B) B Z t := by
    rw [← ht.Vt_eq_of_mem_root h34 hspread H hs hsY hs1]
    exact haV_s
  have hinf := Good101.inf_Vt_inf_centralizer_eq ht hs h2 hcQ hcB hcW
  have haB' : a ∈ B := by
    rw [← hinf]
    exact ⟨⟨ha.1, haV_t⟩, ha.2⟩
  exact haB haB'

private theorem mem_M_not_mem_Q_of_conj (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    {a : G} (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) {y : G}
    (hy : y ∈ Y) (hyt : y ≠ t) :
    (c * t * c⁻¹ * a * y ∈ M) ∧ (c * t * c⁻¹ * a * y ∉ Q) := by
  obtain ⟨s, x'', hsdef, hsY, hs1, hx''s, hx''2, hw⟩ :=
    conj_eq_mul_decomp h34 hspread H ht hs h2 hcQ ha hy hyt
  subst s
  obtain ⟨-, -, hsM, hty2, hcomm_st, hsg, h2s, h5s, hSLs, -⟩ :=
    root_mul_facts h34 hspread H ht hs h2 hy hyt
  have hx''Q : x'' ∈ Q := hc.Ut_le_Q hsM hx''s
  have haQ : a ∈ Q := ha.1.1
  have hq : x'' * a ∈ Q := Q.mul_mem hx''Q haQ
  constructor
  · rw [hw]
    exact M.mul_mem (M.mul_mem hsM (hc.hyp.Q_normal.1 hx''Q)) (hc.hyp.Q_normal.1 haQ)
  · intro h
    rw [hw] at h
    have e : t * y = ((t * y) * x'' * a) * (x'' * a)⁻¹ := by group
    exact hsg.2.2.1 (by rw [e]; exact Q.mul_mem h (Q.inv_mem hq))

private theorem good101_of_conj_eq_mul_core (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    (hcB : c ∈ Subgroup.centralizer (B : Set G)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) {u y : G}
    (huB : u ∈ Subgroup.centralizer (B : Set G)) (hy : y ∈ Y) (hyt : y ≠ t)
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) :
    Good101 M Q Z B (c * t * c⁻¹ * a * y) := by
  set w : G := c * t * c⁻¹ * a * y with hwdef
  obtain ⟨s, x'', hsdef, hsY, hs1, hx''s, hx''2, hw⟩ :=
    conj_eq_mul_decomp h34 hspread H ht hs h2 hcQ ha hy hyt
  subst s
  obtain ⟨-, -, hsM, hty2, hcomm_st, hsg, h2s, h5s, hSLs, hUtEq⟩ :=
    root_mul_facts h34 hspread H ht hs h2 hy hyt
  have hx''Q : x'' ∈ Q := hc.Ut_le_Q hsM hx''s
  have haQ : a ∈ Q := ha.1.1
  have hq : x'' * a ∈ Q := Q.mul_mem hx''Q haQ
  have hconjZ : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = w := by
    obtain ⟨g, z, hzZ, hz1, hgz⟩ := ht.1
    refine ⟨u * c * g, z, hzZ, hz1, ?_⟩
    calc u * c * g * z * (u * c * g)⁻¹ = u * c * (g * z * g⁻¹) * c⁻¹ * u⁻¹ := by group
      _ = u * c * t * c⁻¹ * u⁻¹ := by rw [hgz]
      _ = u * (c * t * c⁻¹) * u⁻¹ := by group
      _ = w := hconj
  obtain ⟨hwM', hwQ'⟩ := mem_M_not_mem_Q_of_conj h34 hspread H ht hs h2 hcQ ha hy hyt
  have hwM : w ∈ M := by rw [hwdef]; exact hwM'
  have hwQ : w ∉ Q := by rw [hwdef]; exact hwQ'
  have hucC : u * c ∈ Subgroup.centralizer (B : Set G) :=
    (Subgroup.centralizer (B : Set G)).mul_mem huB hcB
  have hwQB : w ∈ QB B := by
    have e : w = (u * c) * t * (u * c)⁻¹ := by rw [← hconj]; group
    have h1 : (u * c) * t * (u * c)⁻¹ ∈ conjSubgroup (u * c) (QB B) := by
      rw [mem_conjSubgroup, show (u * c)⁻¹ * ((u * c) * t * (u * c)⁻¹) * (u * c) = t by group]
      exact ht.2.2.2.1
    rw [e]
    rwa [← QB_conj, conjSubgroup_eq_of_mem_centralizer hucC] at h1
  have hRtw : Rt M (LB M Q B) w = Rt M (LB M Q B) (t * y) := by
    rw [hwdef, hw, mul_assoc]
    exact Rt_mul_of_mem_Q hc hq
  exact ⟨hconjZ, hwM, hwQ, hwQB, by rw [hRtw]; exact hsg.2.2.2.2⟩

private theorem sit_of_conj_eq_mul_core (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    {a : G} (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) {u y : G}
    (hy : y ∈ Y) (hyt : y ≠ t)
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) :
    Sit M Q Z (conjSubgroup (u * c) Y) (c * t * c⁻¹ * a * y) := by
  set w : G := c * t * c⁻¹ * a * y with hwdef
  obtain ⟨s, x'', hsdef, hsY, hs1, hx''s, hx''2, hw⟩ :=
    conj_eq_mul_decomp h34 hspread H ht hs h2 hcQ ha hy hyt
  subst s
  obtain ⟨-, -, hsM, hty2, hcomm_st, hsg, h2s, h5s, hSLs, hUtEq⟩ :=
    root_mul_facts h34 hspread H ht hs h2 hy hyt
  have hx''Q : x'' ∈ Q := hc.Ut_le_Q hsM hx''s
  have haQ : a ∈ Q := ha.1.1
  have hq : x'' * a ∈ Q := Q.mul_mem hx''Q haQ
  have hwU : w = (u * c) * t * (u * c)⁻¹ := by rw [← hconj]; group
  obtain ⟨hwM', hwQ'⟩ := mem_M_not_mem_Q_of_conj h34 hspread H ht hs h2 hcQ ha hy hyt
  have hwM : w ∈ M := by rw [hwdef]; exact hwM'
  have hwQ : w ∉ Q := by rw [hwdef]; exact hwQ'
  obtain ⟨g0, hg0⟩ := hs.conj
  refine ⟨hs.hyp, ⟨(u * c) * g0, ?_⟩, ?_, ?_, hwM, hwQ⟩
  · rw [hg0, conjSubgroup_conjSubgroup]
  · refine mem_conjSubgroup.mpr ?_
    have e : (u * c)⁻¹ * w * (u * c) = t := by rw [hwU]; group
    rw [e]
    exact hs.mem
  · intro h1
    apply hs.ne_one
    calc t = (u * c)⁻¹ * w * (u * c) := by rw [hwU]; group
      _ = 1 := by rw [h1]; group

private theorem slmNat_of_conj_eq_mul_core (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    {a : G} (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) {y : G}
    (hy : y ∈ Y) (hyt : y ≠ t) :
    SLMNat hc (c * t * c⁻¹ * a * y) 2 := by
  set w : G := c * t * c⁻¹ * a * y with hwdef
  obtain ⟨s, x'', hsdef, hsY, hs1, hx''s, hx''2, hw⟩ :=
    conj_eq_mul_decomp h34 hspread H ht hs h2 hcQ ha hy hyt
  subst s
  obtain ⟨-, -, hsM, hty2, hcomm_st, hsg, h2s, h5s, hSLs, hUtEq⟩ :=
    root_mul_facts h34 hspread H ht hs h2 hy hyt
  have hx''Q : x'' ∈ Q := hc.Ut_le_Q hsM hx''s
  have haQ : a ∈ Q := ha.1.1
  have hq : x'' * a ∈ Q := Q.mul_mem hx''Q haQ
  rw [hwdef, hw, mul_assoc]
  exact (SLMNat.mul_of_mem_Q (hc := hc) (t := t * y) (y := x'' * a) hq).mpr h2s


theorem Good101.caseA_of_conj_eq_mul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (haB : a ∉ B) {u y : G}
    (huB : u ∈ Subgroup.centralizer (B : Set G)) (hy : y ∈ Y) (hyt : y ≠ t)
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) :
    Good101 M Q Z B (c * t * c⁻¹ * a * y) ∧
      Sit M Q Z (conjSubgroup (u * c) Y) (c * t * c⁻¹ * a * y) ∧
      SLMNat hc (c * t * c⁻¹ * a * y) 2 ∧ CaseA Q Z (c * t * c⁻¹ * a * y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact good101_of_conj_eq_mul_core h34 hspread H ht hs h2 hcQ hcB ha huB hy hyt hconj
  · exact sit_of_conj_eq_mul_core h34 hspread H ht hs h2 hcQ ha hy hyt hconj
  · exact slmNat_of_conj_eq_mul_core h34 hspread H ht hs h2 hcQ ha hy hyt
  · exact caseA_of_conj_eq_mul_core h34 hspread H ht hs h2 hcQ hcB hcW ha haB hy hyt hconj

end CFSG.RankThree.GF2n.Stroth80
