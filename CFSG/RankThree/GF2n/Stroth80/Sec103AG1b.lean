module

public import CFSG.RankThree.GF2n.Stroth80.Sec103ABad
public import CFSG.RankThree.GF2n.Stroth80.Sec103ALemmaIQ
public import CFSG.RankThree.GF2n.Stroth80.Sec10NotMemUt
public import CFSG.RankThree.GF2n.Stroth80.Sec10RootFrame

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Y : Subgroup G}

theorem Good101.sit_conj (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {c : G} (hcQ : c ∈ Q)
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) :
    Sit (Subgroup.normalizer (Y : Set G)) (QB Y) Y (conjSubgroup c Y) (c * t * c⁻¹) := by
  obtain ⟨hcY, -⟩ := Good101.exists_yFrame h34 hspread H ht hs
  refine Sit.of_conj hcY.hyp hs.mem hs.ne_one
    (mem_normalizer_of_comm_Y hs (ht.conj_comm_self h34 H hs hcQ)) fun hw => ?_
  apply ht.comm_not_mem_Tt h34 H hcQ hcW
  have hxQ : ⁅t, c⁆ ∈ Q := by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hc.comm_mem_Q ht.2.1 hcQ)
  have hx : ⁅t, c⁆ ∈ Q ⊓ QB Y := by
    refine ⟨hxQ, ?_⟩
    have e : ⁅t, c⁆ = t⁻¹ * (c * t * c⁻¹) := by
      rw [conj_eq_mul_comm_of_mul_self hs.x_sq c]; group
    rw [e]
    exact (QB Y).mul_mem ((QB Y).inv_mem (Sit.le_QB hs hs.mem)) hw
  have hxU : ⁅t, c⁆ ∈ Ut Q Z t := by
    rw [← commutatorElement_inv]
    exact (Ut Q Z t).inv_mem (comm_mem_Ut hcQ)
  exact Good101.inf_QB_inf_Ut_le_Tt h34 hspread H ht hs ⟨hx, hxU⟩

theorem Good101.conj_mem_LB (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G)) :
    c * t * c⁻¹ ∈ LB (Subgroup.normalizer (Y : Set G)) (QB Y) B := by
  have htQB : c * t * c⁻¹ ∈ QB B := by
    have h1 : c * t * c⁻¹ ∈ conjSubgroup c (QB B) := by
      rw [mem_conjSubgroup, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
      exact ht.2.2.2.1
    rwa [← QB_conj, conjSubgroup_eq_of_mem_centralizer hcB] at h1
  exact Subgroup.mem_sup_right
    ⟨htQB, mem_normalizer_of_comm_Y hs (ht.conj_comm_self h34 H hs hcQ)⟩

private theorem Good101.mem_img_centralizer_of_smul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hAB : Q ⊓ QB Y ≤ QB B)
    (hcY : Ctx (Subgroup.normalizer (Y : Set G)) (QB Y) Y B)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel (QB Y) Y K γ}
    (hDY : GlobalModelData (Subgroup.normalizer (Y : Set G)) (QB Y) Y γ M₀) {c : G}
    (hcQ : c ∈ Q) (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {s : K} {a : G}
    (haS : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hS₁ : ∀ (s : K) {e : M₀.E}, e ∈ M₀.img (QB Y ⊓ QB (conjSubgroup c Y) ⊓ QB B) →
        s • e ∈ M₀.img (QB Y ⊓ QB (conjSubgroup c Y) ⊓ QB B))
    (hS₂ : ∀ (s : K) {e : M₀.E}, e ∈ M₀.img (QB Y ⊓ QB Z ⊓ QB B) →
        s • e ∈ M₀.img (QB Y ⊓ QB Z ⊓ QB B)) (hQBZ : QB Z = Q) :
    s • M₀.π a ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have haQB : a ∈ QB B := hAB haS.1
  have haY' : a ∈ QB (conjSubgroup c Y) := mem_QB_conj_of_mem_centralizer haS.1.2 haS.2
  obtain ⟨b, hb, hbQ, hbe⟩ := hS₁ s
    (M₀.pi_mem_img (S := QB Y ⊓ QB (conjSubgroup c Y) ⊓ QB B)
      ⟨⟨haS.1.2, haY'⟩, haQB⟩ haS.1.2)
  obtain ⟨a', ha', ha'Q, ha'e⟩ := hS₂ s
    (M₀.pi_mem_img (S := QB Y ⊓ QB Z ⊓ QB B)
      ⟨⟨haS.1.2, by rw [hQBZ]; exact haS.1.1⟩, haQB⟩ haS.1.2)
  have hy : a'⁻¹ * b ∈ Y := (Tim79.QuadModel.pi_eq_iff M₀ ha'Q hbQ).mp (ha'e.trans hbe.symm)
  have ha'A : a' ∈ Q ⊓ QB Y := ⟨by have h := ha'.1.2; rwa [hQBZ] at h, ha'Q⟩
  have hya : a'⁻¹ * b * a' ∈ QB (conjSubgroup c Y) := by
    rw [Z_central hcY.hyp hy ha'Q, mul_inv_cancel_left]
    exact hb.1.2
  obtain ⟨-, ha'c⟩ := ht.eq_one_of_mul_mem_QB_conj h34 hspread H hs hcQ hcW hy ha'A hya
  exact ⟨a', ⟨ha'A, Subgroup.mem_centralizer_singleton_iff.mpr ha'c⟩, ha'Q, ha'e⟩

theorem Good101.smul_mem_img_centralizer (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hAB : Q ⊓ QB Y ≤ QB B) (hcY : Ctx (Subgroup.normalizer (Y : Set G)) (QB Y) Y B)
    (HY : Sec10Hyp hcY n) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel (QB Y) Y K γ}
    (hDY : GlobalModelData (Subgroup.normalizer (Y : Set G)) (QB Y) Y γ M₀) {c : G}
    (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) (s : K) {e : M₀.E}
    (he : e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))) :
    s • e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
  obtain ⟨gY, hgY⟩ := hs.conj
  have hsw := Good101.sit_conj h34 hspread H ht hs hcQ hcW
  have hQBZ : QB Z = Q := StrothHyp.QB_Z hc.hyp
  have hBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hY'B : conjSubgroup c Y ≠ B := by
    intro h
    apply ht.2.2.1
    have hw : c * t * c⁻¹ ∈ Q := hc.le (h ▸ hsw.mem)
    have e : t = c⁻¹ * (c * t * c⁻¹) * c := by group
    rw [e]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hcQ) hw) hcQ
  have hBY' : B ≤ QB (conjSubgroup c Y) := by
    intro b hb
    rw [QB_conj, mem_conjSubgroup]
    have hb' : b * c = c * b := Subgroup.mem_centralizer_iff.mp hcB b hb
    rw [show c⁻¹ * b * c = b by rw [mul_assoc, hb', ← mul_assoc, inv_mul_cancel, one_mul]]
    exact hBY hb
  have hYY' : Y ⊓ QB (conjSubgroup c Y) = ⊥ := Z_inf_QB_eq_bot hsw (smith_1_12 hsw)
  have hS₁ := HY.smul_mem_img_inf_QB_inf_QB h34 hspread hDY ⟨c, rfl⟩ hY'B hBY' hYY'
  have hBZ : B ≤ QB Z := by rw [hQBZ]; exact hc.le
  have hYZ : Y ⊓ QB Z = ⊥ := by rw [hQBZ]; exact (smith_1_12 hs).2
  have hWZ : ∃ w : G, Z = conjSubgroup w Y :=
    ⟨gY⁻¹, by rw [hgY, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]⟩
  have hS₂ := HY.smul_mem_img_inf_QB_inf_QB h34 hspread hDY hWZ hc.ne.symm hBZ hYZ
  obtain ⟨a, haS, -, rfl⟩ := he
  exact Good101.mem_img_centralizer_of_smul h34 hspread H ht hs hAB hcY hDY hcQ hcW
    haS hS₁ hS₂ hQBZ

private theorem Good101.exists_comm_not_mem_Ut_of_not_caseA (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {c : G}
    (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t))
    (hB : ¬ CaseA (QB Y) Y (c * t * c⁻¹)) {α : G}
    (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hαV : α ∉ Vt M (LB M Q B) B Z t) :
    ∃ h ∈ QB Y, h * (c * t * c⁻¹) * h⁻¹ = c * t * c⁻¹ * t ∧ h * α ≠ α * h := by
  obtain ⟨hcY, -⟩ := Good101.exists_yFrame h34 hspread H ht hs
  obtain ⟨gY, hgY⟩ := hs.conj
  have hsw := Good101.sit_conj h34 hspread H ht hs hcQ hcW
  have hwL := Good101.conj_mem_LB h34 H ht hs hcQ hcB
  have hαY' : α ∈ QB Y ⊓ QB (conjSubgroup c Y) :=
    ⟨hα.1.2, mem_QB_conj_of_mem_centralizer hα.1.2 hα.2⟩
  have hαU : α ∉ Ut (QB Y) Y (c * t * c⁻¹) := by
    intro hαU
    have hα1 : α ≠ 1 := fun h1 => hαV (h1 ▸ (Vt M (LB M Q B) B Z t).one_mem)
    have hr := hcY.isRoot_of_mem_Ut_of_not_caseA hwL hB hsw ⟨hαY', hαU⟩ hα1
    exact hαV (ht.mem_Vt_of_isRoot h34 hspread H hs hα.1
      ((isRoot_conj_iff hgY).mp hr))
  have hB' : ∃ h ∈ QB Y, h * (c * t * c⁻¹) * h⁻¹ = c * t * c⁻¹ * t := by
    by_contra hcon
    push Not at hcon
    exact hB ⟨t, hs.mem, hcon⟩
  obtain ⟨h, hhQ, hhw⟩ := hB'
  have hhw' : ⁅h, c * t * c⁻¹⁆ = t := by
    rw [commutatorElement_def, hhw, ht.conj_comm_self h34 H hs hcQ]; group
  have hhα : h * α ≠ α * h := hcY.mul_comm_ne_of_not_mem_Ut hsw hαY' hαU hhQ
    (by rw [hhw']; exact hs.mem) (by rw [hhw']; exact hs.ne_one)
  exact ⟨h, hhQ, hhw, hhα⟩

private theorem Good101.exists_centralizer_mul_of_comm_not_mem_Ut (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hAB : Q ⊓ QB Y ≤ QB B) {c : G}
    (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t))
    (hcY : Ctx (Subgroup.normalizer (Y : Set G)) (QB Y) Y B) (HY : Sec10Hyp hcY n)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel (QB Y) Y K γ}
    (hDY : GlobalModelData (Subgroup.normalizer (Y : Set G)) (QB Y) Y γ M₀)
    {α h : G} (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hhQ : h ∈ QB Y) (hhw : h * (c * t * c⁻¹) * h⁻¹ = c * t * c⁻¹ * t)
    (hhα : h * α ≠ α * h) :
    ∃ a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G),
      ⁅h, a⁆ = t ∧ h * (c * t * c⁻¹ * a) * h⁻¹ = c * t * c⁻¹ * a := by
  have hK : ∀ (s : K) (e : M₀.E),
      e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) →
      s • e ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) := fun s _ he =>
    Good101.smul_mem_img_centralizer h34 hspread H ht hs hAB hcY HY hDY hcQ hcB hcW s he
  obtain ⟨a, ha, hha⟩ :=
    exists_comm_eq_of_smul_mem M₀ hDY.reg
      (S := Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (fun _ ha => ha.1.2) hK hhQ hα hhα
      hs.mem
  have hha' : h * a * h⁻¹ = t * a := by
    calc h * a * h⁻¹ = ⁅h, a⁆ * a := by simp only [commutatorElement_def]; group
      _ = t * a := by rw [hha]
  have ht2 : t * t = 1 := hs.x_sq
  have hr : h * (c * t * c⁻¹ * a) * h⁻¹ = c * t * c⁻¹ * a := by
    calc h * (c * t * c⁻¹ * a) * h⁻¹ = (h * (c * t * c⁻¹) * h⁻¹) * (h * a * h⁻¹) := by group
      _ = c * t * c⁻¹ * (t * t) * a := by rw [hhw, hha']; group
      _ = c * t * c⁻¹ * a := by rw [ht2, mul_one]
  exact ⟨a, ha, hha, hr⟩

private theorem Good101.false_of_exists_centralizer_mul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {c : G}
    (hcQ : c ∈ Q) (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {h a : G}
    (hhw : h * (c * t * c⁻¹) * h⁻¹ = c * t * c⁻¹ * t)
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hha : ⁅h, a⁆ = t) (hr : h * (c * t * c⁻¹ * a) * h⁻¹ = c * t * c⁻¹ * a) : False := by
  have hwt : c * t * c⁻¹ * t = ⁅t, c⁆ := by
    rw [conj_eq_mul_comm_of_mul_self hs.x_sq c, mul_assoc, ht.comm_comm_self h34 H hs hcQ,
      ← mul_assoc, hs.x_sq, one_mul]
  have hxQ : ⁅t, c⁆ ∈ Q := by
    rw [← commutatorElement_inv]; exact Q.inv_mem (hc.comm_mem_Q ht.2.1 hcQ)
  have hxZ : ⁅t, c⁆ ∉ Z := fun h' => ht.comm_not_mem_Tt h34 H hcQ hcW (Subgroup.mem_sup_right h')
  have hxw : h * (c * t * c⁻¹) * h⁻¹ = ⁅t, c⁆ := by rw [hhw, hwt]
  obtain ⟨gY, hgY⟩ := hs.conj
  have hxR : ⁅t, c⁆ ∈ conjSubgroup (h * c * gY) Z := by
    rw [mem_conjSubgroup, ← hxw, show (h * c * gY)⁻¹ * (h * (c * t * c⁻¹) * h⁻¹) * (h * c * gY)
      = gY⁻¹ * t * gY by group]
    exact mem_conjSubgroup.mp (hgY ▸ hs.mem)
  obtain ⟨g₃, hg₃Q, hxg₃⟩ := stroth_2_6 hc.hyp hxQ hxZ
    ⟨h * c * gY, (h * c * gY)⁻¹ * ⁅t, c⁆ * (h * c * gY), mem_conjSubgroup.mp hxR, by group⟩
  have hXeq : conjSubgroup (h * c * gY) Z = conjSubgroup g₃ Z :=
    conjSubgroup_eq_of_mem_ne_one hc.hyp (fun h' => hxZ (by rw [h']; exact Z.one_mem)) hxR hxg₃
  have hwY' : c * t * c⁻¹ ∈ QB (conjSubgroup c Y) := by
    rw [QB_conj, mem_conjSubgroup, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
    exact Sit.le_QB hs hs.mem
  have hraX : c * t * c⁻¹ * a ∈ QB (conjSubgroup g₃ Z) := by
    rw [← hXeq, conjSubgroup_mul, conjSubgroup_mul, ← hgY, QB_conj, mem_conjSubgroup,
      show h⁻¹ * (c * t * c⁻¹ * a) * h = c * t * c⁻¹ * a by
        calc h⁻¹ * (c * t * c⁻¹ * a) * h =
            h⁻¹ * (h * (c * t * c⁻¹ * a) * h⁻¹) * h := by rw [hr]
          _ = c * t * c⁻¹ * a := by group]
    exact (QB _).mul_mem hwY' (mem_QB_conj_of_mem_centralizer ha.1.2 ha.2)
  have hcM : c ∈ M := hc.hyp.Q_normal.1 hcQ
  have hraM : c * t * c⁻¹ * a ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hcM ht.2.1) (M.inv_mem hcM)) (hc.hyp.Q_normal.1 ha.1.1)
  have htLX : t ∈ LB M Q (conjSubgroup g₃ Z) := by
    rw [show t = (c * t * c⁻¹ * a) * (⁅t, c⁆ * a)⁻¹ by
      rw [conj_eq_mul_comm_of_mul_self hs.x_sq c]; group]
    exact (LB M Q _).mul_mem (Subgroup.mem_sup_right ⟨hraX, hraM⟩)
      (Subgroup.mem_sup_left (Q.inv_mem (Q.mul_mem hxQ ha.1.1)))
  obtain ⟨m, hm, hmX⟩ := (H.rootTrans h34 hspread) _
    ⟨hc.hyp, ⟨g₃, rfl⟩, hg₃Q, fun h' => hxZ (h' ▸ hxg₃)⟩
  exact ht.comm_not_mem_Tt h34 H hcQ hcW (ht.Vt_le_Tt h34 H
    ((hmX ▸ sec39_conjB_le_Vt hm (by rw [← hc.LB_conj hm, hmX]; exact htLX)) hxg₃))

theorem Good101.caseA_conj (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (hAB : Q ⊓ QB Y ≤ QB B) {c : G} (hcQ : c ∈ Q)
    (hcB : c ∈ Subgroup.centralizer (B : Set G)) (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t))
    {α : G} (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hαV : α ∉ Vt M (LB M Q B) B Z t) : CaseA (QB Y) Y (c * t * c⁻¹) := by
  by_contra hB
  obtain ⟨hcY, HY⟩ := Good101.exists_yFrame h34 hspread H ht hs
  obtain ⟨K, _, _, _, γ, M₀, hDY⟩ := stroth_globalModelData hcY.hyp
  obtain ⟨h, hhQ, hhw, hhα⟩ :=
    Good101.exists_comm_not_mem_Ut_of_not_caseA h34 hspread H ht hs hcQ hcB hcW hB hα hαV
  obtain ⟨a, ha, hha, hr⟩ :=
    Good101.exists_centralizer_mul_of_comm_not_mem_Ut h34 hspread H ht hs hAB hcQ hcB hcW
      hcY HY hDY hα hhQ hhw hhα
  exact Good101.false_of_exists_centralizer_mul h34 hspread H ht hs hcQ hcW hhw ha hha hr

end CFSG.RankThree.GF2n.Stroth80
