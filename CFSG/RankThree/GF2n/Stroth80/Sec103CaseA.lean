module

public import CFSG.RankThree.GF2n.Stroth80.Sec103
public import CFSG.RankThree.GF2n.Stroth80.Sec103AAdm
public import CFSG.RankThree.GF2n.Stroth80.Sec103ALine
public import CFSG.RankThree.GF2n.Stroth80.Sec103AG1b

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Y : Subgroup G}

private theorem BadA.exists_line_of_fusion (D : BadA hc n t Y) {c : G}
    (hc' : Adm103 M Q Z B t Y c)
    (hcY : Ctx (Subgroup.normalizer (Y : Set G)) (QB Y) Y B) (HY : Sec10Hyp hcY n)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel (QB Y) Y K γ}
    (hDY : GlobalModelData (Subgroup.normalizer (Y : Set G)) (QB Y) Y γ M₀) {gY : G}
    (hgY : Y = conjSubgroup gY Z)
    (hK : ∀ (s : K) (e : M₀.E),
      e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) →
      s • e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))) :
    ∃ L : Subgroup G, L ≤ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) ∧ M₀.IsLine L ∧
      L ⊓ (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c} : Set G)) = ⊥ ∧
      Nat.card L = Nat.card K := by
  have hSQY : Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) ≤ QB Y := fun _ ha => ha.1.2
  have hYQ : Y ⊓ Q = ⊥ := (smith_1_12 D.hs).2
  have hSY : Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h : a ∈ Y ⊓ Q := ⟨ha.2, ha.1.1.1⟩
    rwa [hYQ] at h
  have hA₀ : Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) := fun _ ha => ⟨ha.1.1, ha.2⟩
  have hcY_card : Nat.card Y = Nat.card Z := by rw [hgY, card_conjSubgroup]
  have hcard : Nat.card K * Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓
      Subgroup.centralizer ({c} : Set G)) ≤
      Nat.card ↥(Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
    rw [hDY.card, hcY_card]; exact hc'.card
  exact exists_isLine_le M₀ hSQY hSY hA₀ hK hcard

private theorem BadA.line_le_Ut_of_fusion (D : BadA hc n t Y) {c : G}
    (hc' : Adm103 M Q Z B t Y c)
    (hcY : Ctx (Subgroup.normalizer (Y : Set G)) (QB Y) Y B)
    (hsw : Sit (Subgroup.normalizer (Y : Set G)) (QB Y) Y (conjSubgroup c Y) (c * t * c⁻¹))
    (hAw : CaseA (QB Y) Y (c * t * c⁻¹)) {gY : G} (hgY : Y = conjSubgroup gY Z)
    {L : Subgroup G} (hLS : L ≤ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hL0 : L ⊓ (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c} : Set G)) = ⊥) :
    (L ≤ QB Y ⊓ QB (conjSubgroup c Y)) ∧ L ≤ Ut (QB Y) Y (c * t * c⁻¹) ∧
      (∀ a ∈ L, (∃ g : G, ∃ y ∈ Y, y ≠ 1 ∧ g * y * g⁻¹ = a) → a = 1) ∧
      (∀ a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G),
        a ∈ QB Y ⊓ QB (conjSubgroup c Y) ⊓ Ut (QB Y) Y (c * t * c⁻¹)) := by
  have hCU : ∀ a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G),
      a ∈ QB Y ⊓ QB (conjSubgroup c Y) ⊓ Ut (QB Y) Y (c * t * c⁻¹) := fun a ha =>
    ⟨⟨ha.1.2, mem_QB_conj_of_mem_centralizer ha.1.2 ha.2⟩,
      Good101.inf_QB_le_Ut_of_caseA hcY hsw hAw
        ⟨ha.1.2, mem_QB_conj_of_mem_centralizer ha.1.2 ha.2⟩⟩
  have hLA : L ≤ QB Y ⊓ QB (conjSubgroup c Y) := fun a ha => (hCU a (hLS ha)).1
  have hLU : L ≤ Ut (QB Y) Y (c * t * c⁻¹) := fun a ha => (hCU a (hLS ha)).2
  have hroot : ∀ a ∈ L, (∃ g : G, ∃ y ∈ Y, y ≠ 1 ∧ g * y * g⁻¹ = a) → a = 1 := by
    intro a haL hra
    have haS := hLS haL
    have haV := D.ht.mem_Vt_of_isRoot D.h34 D.hspread D.H D.hs haS.1
      ((isRoot_conj_iff hgY).mp hra)
    have h : a ∈ L ⊓ (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓
        Subgroup.centralizer ({c} : Set G)) := ⟨haL, ⟨haS.1, haV⟩, haS.2⟩
    rwa [hL0, Subgroup.mem_bot] at h
  exact ⟨hLA, hLU, hroot, hCU⟩

theorem BadA.fusion_conj (D : BadA hc n t Y) {c : G} (hc' : Adm103 M Q Z B t Y c) :
    (∀ y ∈ Y, y ≠ 1 → ∃ a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G),
        a ∉ Vt M (LB M Q B) B Z t ∧ ∃ k ∈ QB Y, k * (c * t * c⁻¹) * k⁻¹ = c * t * c⁻¹ * a * y) ∧
    ∀ u ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G), ∀ y ∈ Y,
      (∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = c * t * c⁻¹ * u * y) →
        ∃ k ∈ QB Y, k * (c * t * c⁻¹) * k⁻¹ = c * t * c⁻¹ * u * y := by
  obtain ⟨hcY, HY⟩ := Good101.exists_yFrame D.h34 D.hspread D.H D.ht D.hs
  obtain ⟨gY, hgY⟩ := D.hs.conj
  obtain ⟨K, _, _, _, γ, M₀, hDY⟩ := stroth_globalModelData hcY.hyp
  obtain ⟨α, hα, hαV⟩ := hc'.exα
  have hsw := Good101.sit_conj D.h34 D.hspread D.H D.ht D.hs hc'.mem hc'.notW
  have hwL := Good101.conj_mem_LB D.h34 D.H D.ht D.hs hc'.mem hc'.centB
  have hAw := Good101.caseA_conj D.h34 D.hspread D.H D.ht D.hs D.inf_QB_le_QB hc'.mem
    hc'.centB hc'.notW hα hαV
  have hK : ∀ (s : K) (e : M₀.E),
      e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) →
      s • e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) := fun s _ he =>
    Good101.smul_mem_img_centralizer D.h34 D.hspread D.H D.ht D.hs D.inf_QB_le_QB hcY HY hDY
      hc'.mem hc'.centB hc'.notW s he
  obtain ⟨L, hLS, hline, hL0, hLc⟩ := D.exists_line_of_fusion hc' hcY HY hDY hgY hK
  obtain ⟨hLA, hLU, hroot, hCU⟩ := D.line_le_Ut_of_fusion hc' hcY hsw hAw hgY hLS hL0
  refine ⟨fun y hy hy1 => ?_, fun u hu y hy hr => ?_⟩
  · obtain ⟨h0, hfus⟩ :=
      Sit.line_fusion hcY hsw hwL hDY hLA hLU hline (hLc.trans hDY.card) hroot
    obtain ⟨a, haL, k, hk, hkw⟩ := hfus y hy
    have haS := hLS haL
    have ha1 : a ≠ 1 := fun ha1 => hy1 (h0 k hk y hy (by rw [hkw, ha1, mul_one]))
    refine ⟨a, haS, fun haV => ha1 ?_, k, hk, hkw⟩
    have h : a ∈ L ⊓ (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓
        Subgroup.centralizer ({c} : Set G)) := ⟨haL, ⟨haS.1, haV⟩, haS.2⟩
    rwa [hL0, Subgroup.mem_bot] at h
  · exact Sit.exists_conj_of_isRoot_of_line hcY hsw hwL hDY hLA hLU hline
      (hLc.trans hDY.card) hroot (hCU u hu) hy ((isRoot_conj_iff hgY).mpr hr)

theorem BadA.exists_root_mul (D : BadA hc n t Y) {c : G} (hc' : Adm103 M Q Z B t Y c) :
    ∃ a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G), a ∉ Vt M (LB M Q B) B Z t ∧
      ∃ g : G, a ∈ QB (conjSubgroup g Z) ∧ a * ⁅t, c⁆ ∈ conjSubgroup g Z := by
  obtain ⟨gY, hgY⟩ := D.hs.conj
  have hsw := Good101.sit_conj D.h34 D.hspread D.H D.ht D.hs hc'.mem hc'.notW
  obtain ⟨a, haS, haV, k, hk, hkw⟩ := (D.fusion_conj hc').1 t D.hs.mem D.hs.ne_one
  have haY' := mem_QB_conj_of_mem_centralizer haS.1.2 haS.2
  have hka : k * a = a * k := Sit.comm_of_conj_eq_mul hsw hk ⟨haS.1.2, haY'⟩ D.hs.mem hkw
  refine ⟨a, haS, haV, k * c * gY, ?_, ?_⟩
  · rw [conjSubgroup_mul, conjSubgroup_mul, ← hgY, QB_conj, mem_conjSubgroup,
      show k⁻¹ * a * k = a by rw [mul_assoc, ← hka, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact haY'
  · rw [conjSubgroup_mul, conjSubgroup_mul, ← hgY, ← D.conj_mul_mul_self hc'.mem haS.1, ← hkw,
      mem_conjSubgroup, show k⁻¹ * (k * (c * t * c⁻¹) * k⁻¹) * k = c * t * c⁻¹ by group]
    exact hsw.mem

theorem BadA.mem_QB_of_isRoot_mul (D : BadA hc n t Y) {c : G} (hc' : Adm103 M Q Z B t Y c)
    {a : G} (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hr : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = a * ⁅t, c⁆) :
    ∃ g : G, a ∈ QB (conjSubgroup g Z) ∧ a * ⁅t, c⁆ ∈ conjSubgroup g Z := by
  obtain ⟨gY, hgY⟩ := D.hs.conj
  have hsw := Good101.sit_conj D.h34 D.hspread D.H D.ht D.hs hc'.mem hc'.notW
  have e := D.conj_mul_mul_self hc'.mem ha.1
  obtain ⟨k, hk, hkw⟩ := (D.fusion_conj hc').2 a ha t D.hs.mem (by rw [e]; exact hr)
  have haY' := mem_QB_conj_of_mem_centralizer ha.1.2 ha.2
  have hka : k * a = a * k := Sit.comm_of_conj_eq_mul hsw hk ⟨ha.1.2, haY'⟩ D.hs.mem hkw
  refine ⟨k * c * gY, ?_, ?_⟩
  · rw [conjSubgroup_mul, conjSubgroup_mul, ← hgY, QB_conj, mem_conjSubgroup,
      show k⁻¹ * a * k = a by rw [mul_assoc, ← hka, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact haY'
  · rw [conjSubgroup_mul, conjSubgroup_mul, ← hgY, ← e, ← hkw, mem_conjSubgroup,
      show k⁻¹ * (k * (c * t * c⁻¹) * k⁻¹) * k = c * t * c⁻¹ by group]
    exact hsw.mem

theorem BadA.not_isRoot_comm_mul (D : BadA hc n t Y) {c : G} (hc' : Adm103 M Q Z B t Y c)
    {b z : G} (hb : b ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) (hz : z ∈ Z) :
    ¬ ∃ g : G, ∃ z' ∈ Z, z' ≠ 1 ∧ g * z' * g⁻¹ = ⁅t, c⁆ * b * z := by
  rintro ⟨g, z', hz', hz'1, hg⟩
  obtain ⟨c'', hc'', -, z₁, hz₁, hx''⟩ := D.exists_shift hc' hb
  have hxQ := D.comm_mem_Q hc'.mem
  have hmemQ : ⁅t, c⁆ * b * z ∈ Q := Q.mul_mem (Q.mul_mem hxQ hb.1.1) (hc.hyp.Z_normal.1 hz)
  have hmemZ : ⁅t, c⁆ * b * z ∉ Z := by
    intro h
    apply D.ht.comm_not_mem_Tt D.h34 D.H hc'.mem hc'.notW
    apply D.ht.Vt_le_Tt D.h34 D.H
    have e : ⁅t, c⁆ = (⁅t, c⁆ * b * z) * z⁻¹ * b⁻¹ := by group
    rw [e]
    exact (Vt _ _ _ _ _).mul_mem ((Vt _ _ _ _ _).mul_mem (sec39_Z_le_Vt h)
      ((Vt _ _ _ _ _).inv_mem (sec39_Z_le_Vt hz))) ((Vt _ _ _ _ _).inv_mem hb.2)
  obtain ⟨k, hk, hkx⟩ := hc.hyp.exists_conj_eq_mul hmemQ hmemZ (Z.mul_mem (Z.inv_mem hz) hz₁)
  obtain ⟨a, ha, haV, g'', haR, har⟩ := D.exists_root_mul hc''
  have ha1 : a ≠ 1 := fun h => haV (h ▸ (Vt _ _ _ _ _).one_mem)
  have hRhyp : StrothHyp (Subgroup.normalizer (conjSubgroup g'' Z : Set G))
      (QB (conjSubgroup g'' Z)) (conjSubgroup g'' Z) := by
    rw [Smith81.QB_conj_eq hc.hyp, Smith81.normalizer_conj_eq hc.hyp]
    exact hc.hyp.conj g''
  have haR' : a ∉ conjSubgroup g'' Z := by
    intro h
    apply haV
    refine D.ht.mem_Vt_of_isRoot D.h34 D.hspread D.H D.hs ha.1
      ⟨g'', g''⁻¹ * a * g'', mem_conjSubgroup.mp h, fun h0 => ha1 ?_, by group⟩
    calc a = g'' * (g''⁻¹ * a * g'') * g''⁻¹ := by group
      _ = 1 := by rw [h0]; group
  obtain ⟨k', -, hk'a⟩ := hRhyp.exists_conj_eq_mul haR haR' har
  have ha2 : a * a = 1 := D.mul_self_eq_one ha.1
  apply haV
  refine D.ht.mem_Vt_of_isRoot D.h34 D.hspread D.H D.hs ha.1 ⟨k'⁻¹ * (k * g), z', hz', hz'1, ?_⟩
  calc k'⁻¹ * (k * g) * z' * (k'⁻¹ * (k * g))⁻¹ = k'⁻¹ * (k * (g * z' * g⁻¹) * k⁻¹) * k' := by
        group
    _ = k'⁻¹ * (⁅t, c⁆ * b * z * (z⁻¹ * z₁)) * k' := by rw [hg, hkx]
    _ = k'⁻¹ * ⁅t, c''⁆ * k' := by rw [hx'']; group
    _ = k'⁻¹ * ((a * a) * ⁅t, c''⁆) * k' := by rw [ha2, one_mul]
    _ = k'⁻¹ * (k' * a * k'⁻¹) * k' := by rw [hk'a]; group
    _ = a := by group

private theorem BadA.commutator_data (D : BadA hc n t Y) {c : G} {X : Subgroup G} {h α : G}
    (hc' : Adm103 M Q Z B t Y c)
    (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hb : ⁅h, α * ⁅t, c⁆⁆ ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)
    (hrX : α * ⁅t, c⁆ ∉ QB X) :
    h * (α * ⁅t, c⁆) * h⁻¹ ∈ Q ∧ h * (α * ⁅t, c⁆) * h⁻¹ ∉ Z ∧
      h * (α * ⁅t, c⁆) * h⁻¹ ≠ 1 := by
  have hrQ : α * ⁅t, c⁆ ∈ Q := Q.mul_mem hα.1.1 (D.comm_mem_Q hc'.mem)
  have hhrr : h * (α * ⁅t, c⁆) * h⁻¹ = ⁅h, α * ⁅t, c⁆⁆ * (α * ⁅t, c⁆) := by
    simp only [commutatorElement_def]; group
  have hhrQ : h * (α * ⁅t, c⁆) * h⁻¹ ∈ Q := by
    rw [hhrr]; exact Q.mul_mem hb.1.1 hrQ
  have hhrZ : h * (α * ⁅t, c⁆) * h⁻¹ ∉ Z := by
    intro hZ
    apply D.ht.comm_not_mem_Tt D.h34 D.H hc'.mem hc'.notW
    rw [hhrr] at hZ
    have hαT := D.inf_QB_le_Tt hα.1
    have hb'T := D.ht.Vt_le_Tt D.h34 D.H hb.2
    have e : ⁅t, c⁆ = α⁻¹ * (⁅h, α * ⁅t, c⁆⁆⁻¹ * (⁅h, α * ⁅t, c⁆⁆ * (α * ⁅t, c⁆))) := by
      group
    rw [e]
    exact (Tt _ _ _ _).mul_mem ((Tt _ _ _ _).inv_mem hαT)
      ((Tt _ _ _ _).mul_mem ((Tt _ _ _ _).inv_mem hb'T) (Subgroup.mem_sup_right hZ))
  exact ⟨hhrQ, hhrZ, fun h0 => hhrZ (h0 ▸ Z.one_mem)⟩

private theorem BadA.mem_QB_conj_of_root (D : BadA hc n t Y) {c c'' g h α k : G}
    (hc' : Adm103 M Q Z B t Y c) (hc'' : Adm103 M Q Z B t Y c'') (hk : k ∈ Q)
    (hαQ : α ∈ Q) (hα'' : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c''} : Set G))
    (hhrQ : h * (α * ⁅t, c⁆) * h⁻¹ ∈ Q)
    (hhrZ : h * (α * ⁅t, c⁆) * h⁻¹ ∉ Z)
    (hhr1 : h * (α * ⁅t, c⁆) * h⁻¹ ≠ 1)
    (hrh : h * (α * ⁅t, c⁆) * h⁻¹ ∈ conjSubgroup (h * g) Z)
    (hroot'' : ∃ g' : G, ∃ z' ∈ Z, z' ≠ 1 ∧ g' * z' * g'⁻¹ = α * ⁅t, c''⁆)
    (hr₂' : α * ⁅t, c''⁆ ∈ conjSubgroup (k * (h * g)) Z) :
    α ∈ QB (conjSubgroup (h * g) Z) := by
  obtain ⟨g₂, hαR₂, hr₂⟩ := D.mem_QB_of_isRoot_mul hc'' hα'' hroot''
  have hR₂ : conjSubgroup g₂ Z = conjSubgroup (k * (h * g)) Z :=
    conjSubgroup_eq_of_mem_ne_one hc.hyp (isRoot_ne_one hroot'') hr₂ hr₂'
  obtain ⟨g₃, hg₃Q, hg₃⟩ := stroth_2_6 hc.hyp hhrQ hhrZ
    ⟨h * g, (h * g)⁻¹ * (h * (α * ⁅t, c⁆) * h⁻¹) * (h * g), mem_conjSubgroup.mp hrh,
      by group⟩
  have hEq : conjSubgroup (h * g) Z = conjSubgroup g₃ Z :=
    conjSubgroup_eq_of_mem_ne_one hc.hyp hhr1 hrh hg₃
  have hRhctx : Ctx M Q Z (conjSubgroup (h * g) Z) :=
    ⟨hc.hyp, ⟨h * g, rfl⟩, hEq ▸ hg₃Q, fun h0 => hhrZ (h0 ▸ hrh)⟩
  rw [hR₂, conjSubgroup_mul] at hαR₂
  exact (hRhctx.mem_QB_conj_iff hk hαQ).mp hαR₂

private theorem BadA.mem_QB_conj_of_shift (D : BadA hc n t Y) {c : G} {g h α : G}
    (hc' : Adm103 M Q Z B t Y c)
    (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hb : ⁅h, α * ⁅t, c⁆⁆ ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)
    (hr : α * ⁅t, c⁆ ∈ conjSubgroup g Z)
    (hrh : h * (α * ⁅t, c⁆) * h⁻¹ ∈ conjSubgroup (h * g) Z)
    (hhrQ : h * (α * ⁅t, c⁆) * h⁻¹ ∈ Q)
    (hhrZ : h * (α * ⁅t, c⁆) * h⁻¹ ∉ Z)
    (hhr1 : h * (α * ⁅t, c⁆) * h⁻¹ ≠ 1) :
    α ∈ QB (conjSubgroup (h * g) Z) := by
  have hhrr : h * (α * ⁅t, c⁆) * h⁻¹ = ⁅h, α * ⁅t, c⁆⁆ * (α * ⁅t, c⁆) := by
    simp only [commutatorElement_def]; group
  obtain ⟨c'', hc'', hCeq, z₁, hz₁, hx''⟩ := D.exists_shift hc' hb
  have hα'' : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c''} : Set G) := hCeq ▸ hα
  obtain ⟨k, hk, hkr⟩ := hc.hyp.exists_conj_eq_mul hhrQ hhrZ hz₁
  have h1 := D.comm_of_mem hb.1 hα.1
  have h2 := Sit.comm_comm_of_mem_inf_QB D.hs hc'.mem hb.1
  have hαx'' : α * ⁅t, c''⁆ = k * (h * (α * ⁅t, c⁆) * h⁻¹) * k⁻¹ := by
    rw [hkr, hhrr, hx'']
    calc α * (⁅t, c⁆ * ⁅h, α * ⁅t, c⁆⁆ * z₁) = α * (⁅t, c⁆ * ⁅h, α * ⁅t, c⁆⁆) * z₁ := by
          group
      _ = α * (⁅h, α * ⁅t, c⁆⁆ * ⁅t, c⁆) * z₁ := by rw [h2]
      _ = (α * ⁅h, α * ⁅t, c⁆⁆) * ⁅t, c⁆ * z₁ := by group
      _ = (⁅h, α * ⁅t, c⁆⁆ * α) * ⁅t, c⁆ * z₁ := by rw [h1]
      _ = ⁅h, α * ⁅t, c⁆⁆ * (α * ⁅t, c⁆) * z₁ := by group
  have hr₂' : α * ⁅t, c''⁆ ∈ conjSubgroup (k * (h * g)) Z := by
    rw [mem_conjSubgroup, hαx'', show (k * (h * g))⁻¹ * (k * (h * (α * ⁅t, c⁆) * h⁻¹) * k⁻¹)
      * (k * (h * g)) = g⁻¹ * (α * ⁅t, c⁆) * g by group]
    exact mem_conjSubgroup.mp hr
  have hroot'' : ∃ g' : G, ∃ z' ∈ Z, z' ≠ 1 ∧ g' * z' * g'⁻¹ = α * ⁅t, c''⁆ := by
    refine ⟨k * (h * g), (k * (h * g))⁻¹ * (α * ⁅t, c''⁆) * (k * (h * g)),
      mem_conjSubgroup.mp hr₂', fun h0 => ?_, by group⟩
    apply hhr1
    calc h * (α * ⁅t, c⁆) * h⁻¹ = k⁻¹ * (α * ⁅t, c''⁆) * k := by rw [hαx'']; group
      _ = k⁻¹ * ((k * (h * g)) * ((k * (h * g))⁻¹ * (α * ⁅t, c''⁆) * (k * (h * g)))
            * (k * (h * g))⁻¹) * k := by group
      _ = 1 := by rw [h0]; group
  exact D.mem_QB_conj_of_root hc' hc'' hk hα.1.1 hα'' hhrQ hhrZ hhr1 hrh hroot'' hr₂'

private theorem BadA.mem_QB_conj_of_commutator (D : BadA hc n t Y) {c : G}
    {X : Subgroup G} {g h α : G}
    (hc' : Adm103 M Q Z B t Y c)
    (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hb : ⁅h, α * ⁅t, c⁆⁆ ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)
    (hr : α * ⁅t, c⁆ ∈ conjSubgroup g Z)
    (hrh : h * (α * ⁅t, c⁆) * h⁻¹ ∈ conjSubgroup (h * g) Z)
    (hrX : α * ⁅t, c⁆ ∉ QB X) : α ∈ QB (conjSubgroup (h * g) Z) := by
  obtain ⟨hhrQ, hhrZ, hhr1⟩ := D.commutator_data hc' hα hb hrX
  exact D.mem_QB_conj_of_shift hc' hα hb hr hrh hhrQ hhrZ hhr1

theorem BadA.comm_of_comm_mem_root (D : BadA hc n t Y) {c : G} (hc' : Adm103 M Q Z B t Y c)
    {X : Subgroup G} (hX : Ctx M Q Z X) (hXV : X ≤ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)
    (hYX : Y ≤ QB X) {α : G} (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    {g : G} (hαR : α ∈ QB (conjSubgroup g Z)) (hr : α * ⁅t, c⁆ ∈ conjSubgroup g Z)
    (hrX : α * ⁅t, c⁆ ∉ QB X) {h : G} (hh : h ∈ QB X) (hhr : ⁅h, α * ⁅t, c⁆⁆ ∈ X) :
    h * α = α * h := by
  have hxQ := D.comm_mem_Q hc'.mem
  have hrQ : α * ⁅t, c⁆ ∈ Q := Q.mul_mem hα.1.1 hxQ
  have hb := hXV hhr
  have hhrr : h * (α * ⁅t, c⁆) * h⁻¹ = ⁅h, α * ⁅t, c⁆⁆ * (α * ⁅t, c⁆) := by
    simp only [commutatorElement_def]; group
  have hrh : h * (α * ⁅t, c⁆) * h⁻¹ ∈ conjSubgroup (h * g) Z := by
    rw [mem_conjSubgroup, show (h * g)⁻¹ * (h * (α * ⁅t, c⁆) * h⁻¹) * (h * g) =
      g⁻¹ * (α * ⁅t, c⁆) * g by group]
    exact mem_conjSubgroup.mp hr
  have hr1 : α * ⁅t, c⁆ ≠ 1 := fun h0 => hrX (h0 ▸ (QB X).one_mem)
  have hαRh : α ∈ QB (conjSubgroup (h * g) Z) := by
    by_cases hb1 : ⁅h, α * ⁅t, c⁆⁆ = 1
    · have hRh : conjSubgroup (h * g) Z = conjSubgroup g Z := by
        refine conjSubgroup_eq_of_mem_ne_one hc.hyp hr1 ?_ hr
        rw [hhrr, hb1, one_mul] at hrh
        exact hrh
      rw [hRh]; exact hαR
    · exact D.mem_QB_conj_of_commutator hc' hα hb hr hrh hrX
  have hαX : α ∈ QB X := D.inf_QB_le_QB_of_root hX (hYX D.hs.mem) hα.1
  have hcommX : ⁅α, h⁆ ∈ X := hX.QB_comm_mem hαX hh
  have hcommR : ⁅α, h⁆ ∈ QB (conjSubgroup (h * g) Z) := by
    have h1 : h * α⁻¹ * h⁻¹ ∈ QB (conjSubgroup (h * g) Z) := by
      rw [conjSubgroup_mul, QB_conj, mem_conjSubgroup, show h⁻¹ * (h * α⁻¹ * h⁻¹) * h = α⁻¹ by
        group]
      exact (QB _).inv_mem hαR
    have e : ⁅α, h⁆ = α * (h * α⁻¹ * h⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (QB _).mul_mem hαRh h1
  by_contra hne
  have hc1 : ⁅α, h⁆ ≠ 1 := fun h0 => hne (commutatorElement_eq_one_iff_mul_comm.mp h0).symm
  have hle : conjSubgroup (h * g) Z ≤ QB X :=
    hc.hyp.le_QB_of_mem_QB ⟨h * g, rfl⟩ hX.conj hcommX hc1 hcommR
  apply hrX
  have h2 : h * (α * ⁅t, c⁆) * h⁻¹ ∈ QB X := hle hrh
  have e : α * ⁅t, c⁆ = h⁻¹ * (h * (α * ⁅t, c⁆) * h⁻¹) * h := by group
  rw [e]
  exact (QB X).mul_mem ((QB X).mul_mem ((QB X).inv_mem hh) h2) hh

private theorem BadA.false_of_conj_fusion (D : BadA hc n t Y) {c : G}
    (hc' : Adm103 M Q Z B t Y c) {X : Subgroup G} (hX : Ctx M Q Z X)
    (hXV : X ≤ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) (hYX : Y ≤ QB X) {a₁ g : G}
    (hsr : Sit (Subgroup.normalizer (X : Set G)) (QB X) X (conjSubgroup g Z) (a₁ * ⁅t, c⁆))
    (hcomm : ∀ h ∈ QB X, ⁅h, a₁ * ⁅t, c⁆⁆ ∈ X → h * a₁ = a₁ * h)
    (ha₁A : a₁ ∈ Q ⊓ QB Y) (hxa : ⁅t, c⁆ * a₁ = a₁ * ⁅t, c⁆)
    (ha₁sq : a₁ * a₁ = 1) (ha₁ : a₁ ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hr : a₁ * ⁅t, c⁆ ∈ conjSubgroup g Z) : False := by
  have hAX : Q ⊓ QB Y ≤ QB X := D.inf_QB_le_QB_of_root hX (hYX D.hs.mem)
  have hαr : a₁ * (a₁ * ⁅t, c⁆) = a₁ * ⁅t, c⁆ * a₁ := by rw [mul_assoc a₁ ⁅t, c⁆, hxa]
  obtain ⟨h, -, b, hb, hhr⟩ := Sit.exists_conj_eq_mul_of_comm hsr (hAX ha₁A) hαr hcomm
  apply D.not_isRoot_comm_mul hc' (hXV hb) Z.one_mem
  have hz0 : g⁻¹ * (a₁ * ⁅t, c⁆) * g ∈ Z := mem_conjSubgroup.mp hr
  have hz01 : g⁻¹ * (a₁ * ⁅t, c⁆) * g ≠ 1 := fun h0 =>
    (hsr.ne_one) (by
      calc a₁ * ⁅t, c⁆ = g * (g⁻¹ * (a₁ * ⁅t, c⁆) * g) * g⁻¹ := by group
        _ = 1 := by rw [h0]; group)
  refine ⟨h * g, _, hz0, hz01, ?_⟩
  calc h * g * (g⁻¹ * (a₁ * ⁅t, c⁆) * g) * (h * g)⁻¹ = h * (a₁ * ⁅t, c⁆) * h⁻¹ := by group
    _ = a₁ * ⁅t, c⁆ * a₁ * b := hhr
    _ = a₁ * (⁅t, c⁆ * a₁) * b := by group
    _ = a₁ * (a₁ * ⁅t, c⁆) * b := by rw [hxa]
    _ = (a₁ * a₁) * ⁅t, c⁆ * b := by group
    _ = ⁅t, c⁆ * b * 1 := by rw [ha₁sq]; group

theorem BadA.false_of_adm (D : BadA hc n t Y) {c : G} (hc' : Adm103 M Q Z B t Y c)
    {X : Subgroup G} (hX : Ctx M Q Z X) (hXV : X ≤ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)
    (hYX : Y ≤ QB X) (hXc : ¬ X ≤ Subgroup.centralizer ({c} : Set G)) : False := by
  obtain ⟨a₁, ha₁, -, g, ha₁R, hr⟩ := D.exists_root_mul hc'
  have htX : t ∈ QB X := hYX D.hs.mem
  have hxX : ⁅t, c⁆ ∉ QB X := fun hx => hXc fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (D.H.comm_of_comm_mem_QB D.h34 D.hspread D.ht.2.1 D.ht.2.2.1 D.hs.x_sq hX htX hc'.mem hx e he)
  have hAX : Q ⊓ QB Y ≤ QB X := D.inf_QB_le_QB_of_root hX htX
  have ha₁A : a₁ ∈ Q ⊓ QB Y := ha₁.1
  have hrX : a₁ * ⁅t, c⁆ ∉ QB X := fun h => hxX (by
    have h' := (QB X).mul_mem ((QB X).inv_mem (hAX ha₁A)) h
    rwa [inv_mul_cancel_left] at h')
  have hxa : ⁅t, c⁆ * a₁ = a₁ * ⁅t, c⁆ := Sit.comm_comm_of_mem_inf_QB D.hs hc'.mem ha₁A
  have ha₁sq : a₁ * a₁ = 1 := D.mul_self_eq_one ha₁A
  obtain ⟨gX, hgX⟩ := hX.conj
  have hXhyp : StrothHyp (Subgroup.normalizer (X : Set G)) (QB X) X := by
    rw [hgX, Smith81.QB_conj_eq hc.hyp, Smith81.normalizer_conj_eq hc.hyp]
    exact hc.hyp.conj gX
  have hr1 : a₁ * ⁅t, c⁆ ≠ 1 := fun h => hrX (by rw [h]; exact (QB X).one_mem)
  have hrN : a₁ * ⁅t, c⁆ ∈ Subgroup.normalizer (X : Set G) := by
    refine Subgroup.centralizer_le_normalizer (X : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun e he => ?_)
    have heA := (hXV he).1
    have h1 := D.comm_of_mem ha₁A heA
    have h2 := Sit.comm_comm_of_mem_inf_QB D.hs hc'.mem heA
    calc e * (a₁ * ⁅t, c⁆) = (e * a₁) * ⁅t, c⁆ := by group
      _ = (a₁ * e) * ⁅t, c⁆ := by rw [h1]
      _ = a₁ * (e * ⁅t, c⁆) := by group
      _ = a₁ * (⁅t, c⁆ * e) := by rw [h2]
      _ = a₁ * ⁅t, c⁆ * e := by group
  have hsr : Sit (Subgroup.normalizer (X : Set G)) (QB X) X (conjSubgroup g Z) (a₁ * ⁅t, c⁆) :=
    { hyp := hXhyp
      conj := ⟨g * gX⁻¹, by
        rw [hgX, conjSubgroup_conjSubgroup, show g * gX⁻¹ * gX = g by group]⟩
      mem := hr
      ne_one := hr1
      memM := hrN
      notQ := hrX }
  have hcomm : ∀ h ∈ QB X, ⁅h, a₁ * ⁅t, c⁆⁆ ∈ X → h * a₁ = a₁ * h := fun h hh hhr =>
    D.comm_of_comm_mem_root hc' hX hXV hYX ha₁ ha₁R hr hrX hh hhr
  exact D.false_of_conj_fusion hc' hX hXV hYX hsr hcomm ha₁A hxa ha₁sq ha₁ hr

theorem stroth_10_3_caseA (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement) :
    Stroth103CaseAStatement := by
  intro G _ _ M Q Z B hc n t Y H ht hs hA
  by_contra hbad
  have D : BadA hc n t Y := ⟨h34, hspread, H, ht, hs, hA, hbad⟩
  obtain ⟨c, hc', X, hX, hXV, hYX, hXc⟩ := D.exists_adm
  exact D.false_of_adm hc' hX hXV hYX hXc


end CFSG.RankThree.GF2n.Stroth80
