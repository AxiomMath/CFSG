module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic
public import CFSG.RankThree.GF2n.Tim77.InvolAut
public import CFSG.RankThree.GF2n.Tim77.InvolAutD
public import CFSG.RankThree.GF2n.Tim77Prop24
public import CFSG.RankThree.GF2n.Tim77Prop24Roots
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen
import CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem sec34_conj_zpow {x b : G} (hx : x * x = 1) (hb : b * b = 1) (j : ℤ) :
    x * (x * b) ^ j * x = (x * b) ^ (-j) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : x * (x * b) * x⁻¹ = (x * b)⁻¹ := by
    rw [hxi]
    calc x * (x * b) * x = (x * x) * (b * x) := by group
      _ = b * x := by rw [hx, one_mul]
      _ = (x * b)⁻¹ := by rw [mul_inv_rev, hxi, hbi]
  have h2 := conj_zpow (a := x) (b := x * b) (i := j)
  rw [h1, inv_zpow, ← zpow_neg, hxi] at h2
  exact h2.symm

theorem sec34_closure_pair {x b : G} (hx : x * x = 1) (hb : b * b = 1) {g : G}
    (hg : g ∈ Subgroup.closure ({x, b} : Set G)) :
    (∃ i : ℤ, g = (x * b) ^ i) ∨ (∃ i : ℤ, g * x = (x * b) ^ i) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have key : ∀ (y : G) (i : ℤ), y * x = (x * b) ^ i → y = (x * b) ^ i * x := by
    intro y i hy
    rw [← hy, mul_assoc, hx, mul_one]
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Or.inr ⟨0, by rw [hx, zpow_zero]⟩
    · exact Or.inr ⟨-1, by rw [zpow_neg_one, mul_inv_rev, hxi, hbi]⟩
  | one => exact Or.inl ⟨0, by rw [zpow_zero]⟩
  | mul g h _ _ ihg ihh =>
    rcases ihg with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rcases ihh with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨i + j, by rw [hi, hj, zpow_add]⟩
    · exact Or.inr ⟨i + j, by rw [mul_assoc, hj, hi, zpow_add]⟩
    · refine Or.inr ⟨i - j, ?_⟩
      rw [key g i hi, hj]
      calc (x * b) ^ i * x * (x * b) ^ j * x
          = (x * b) ^ i * (x * (x * b) ^ j * x) := by group
        _ = (x * b) ^ i * (x * b) ^ (-j) := by rw [sec34_conj_zpow hx hb j]
        _ = (x * b) ^ (i - j) := by rw [← zpow_add, sub_eq_add_neg]
    · refine Or.inl ⟨i - j, ?_⟩
      rw [key g i hi, key h j hj]
      calc (x * b) ^ i * x * ((x * b) ^ j * x)
          = (x * b) ^ i * (x * (x * b) ^ j * x) := by group
        _ = (x * b) ^ i * (x * b) ^ (-j) := by rw [sec34_conj_zpow hx hb j]
        _ = (x * b) ^ (i - j) := by rw [← zpow_add, sub_eq_add_neg]
  | inv g _ ih =>
    rcases ih with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨-i, by rw [hi, zpow_neg]⟩
    · refine Or.inr ⟨i, ?_⟩
      rw [key g i hi, mul_inv_rev, hxi, ← zpow_neg, sec34_conj_zpow hx hb (-i), neg_neg]

theorem sec34_sq_mem {M : Subgroup G} {x b s : G} (hxM : x ∈ M) (hx : x * x = 1)
    (hb : b * b = 1) (hsM : s ∈ normalizer (M : Set G))
    (hs : s ∈ Subgroup.closure ({x, b} : Set G)) (hord : orderOf s = 4) : s * s ∈ M := by
  have hinvM : ∀ y ∈ M, s⁻¹ * y * s ∈ M := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsM) y).mp hy
    rwa [inv_inv] at this
  rcases sec34_closure_pair hx hb hs with ⟨i, hi⟩ | ⟨i, hi⟩
  ·
    have hxs : x * s * x = s⁻¹ := by
      rw [hi, sec34_conj_zpow hx hb i, zpow_neg]
    have hs' : s = x * s⁻¹ * x := by
      calc s = (x * x) * s * (x * x) := by rw [hx, one_mul, mul_one]
        _ = x * (x * s * x) * x := by group
        _ = x * s⁻¹ * x := by rw [hxs]
    have e : s * s = x * (s⁻¹ * x * s) := by
      calc s * s = (x * s⁻¹ * x) * s := by rw [← hs']
        _ = x * (s⁻¹ * x * s) := by group
    rw [e]
    exact M.mul_mem hxM (hinvM x hxM)
  ·
    exfalso
    have hs' : s = (x * b) ^ i * x := by
      rw [← hi, mul_assoc, hx, mul_one]
    have h1 : s * s = 1 := by
      rw [hs']
      calc (x * b) ^ i * x * ((x * b) ^ i * x)
          = (x * b) ^ i * (x * (x * b) ^ i * x) := by group
        _ = (x * b) ^ i * (x * b) ^ (-i) := by rw [sec34_conj_zpow hx hb i]
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    have h2 : s ^ 2 = 1 := by rw [sq]; exact h1
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at h3
    norm_num at h3

theorem sec34_conj_eq_of_mem_centralizer [Finite G] {A : Subgroup G} {b : G}
    (hb : b ∈ centralizer (A : Set G)) : conjSubgroup b A = A := by
  ext x
  rw [mem_conjSubgroup]
  have hc : ∀ h ∈ A, h * b = b * h := fun h hh => Subgroup.mem_centralizer_iff.1 hb h hh
  constructor
  · intro hy
    have hyb := hc _ hy
    have e : x = b⁻¹ * x * b := by
      calc x = b * (b⁻¹ * x * b) * b⁻¹ := by group
        _ = (b⁻¹ * x * b) * b * b⁻¹ := by rw [← hyb]
        _ = b⁻¹ * x * b := by group
    rw [e]; exact hy
  · intro hx
    have := hc _ hx
    have e : b⁻¹ * x * b = x := by
      calc b⁻¹ * x * b = b⁻¹ * (x * b) := by group
        _ = b⁻¹ * (b * x) := by rw [this]
        _ = x := by group
    rw [e]; exact hx

theorem sec34_normalizer_X [Finite G] {A Abar : Subgroup G} {s : G}
    (hsC : s ∈ centralizer (A : Set G)) (hY : Section3.Y A Abar s = Section3.X A Abar) :
    s ∈ normalizer (Section3.X A Abar : Set G) := by
  have hAs : conjSubgroup s A = A := sec34_conj_eq_of_mem_centralizer hsC
  have hle : conjSubgroup s (Section3.X A Abar) ≤ Section3.X A Abar := by
    have e : conjSubgroup s (Section3.X A Abar) = conjSubgroup s A ⊔ conjSubgroup s Abar := by
      unfold Section3.X conjSubgroup
      exact Subgroup.map_sup _ _ _
    rw [e, hAs]
    refine sup_le le_sup_left ?_
    have h2 : conjSubgroup s Abar ≤ Section3.Y A Abar s := by
      unfold Section3.Y; exact le_sup_right
    rw [hY] at h2
    exact h2
  exact mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le hle)

theorem sec34_normalizes_M
    [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) {s : G}
    (hX : s ∈ normalizer (Section3.X A Abar : Set G)) :
    s ∈ normalizer (Section3.M A Abar : Set G) := by
  obtain ⟨hN, hO2, -⟩ := h.setup.exists_models CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  haveI := hN
  have hMe : ∀ m ∈ Section3.M A Abar, m * m = 1 := fun m hm => by
    rw [← sq]
    exact h.setup.isElemAbelian_M.2 m hm
  rw [h.x_eq] at hX
  exact mem_normalizer_of_conjSubgroup_eq
    (invAut_conj_eq_of_normalizes hO2 h.setup.M_le_X hMe (mem_normalizer_iff_conjSubgroup_eq.1 hX))

theorem sec34_sq_central [Finite G] {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
    (τ : G) (hτ : ∀ x ∈ A ⊔ Ab, τ⁻¹ * x⁻¹ * τ * x ∈ M) (hLτ : ∀ l ∈ L, τ * l = l * τ) :
    ∀ x ∈ A ⊔ Ab, x * (τ * τ) = (τ * τ) * x := by
  obtain ⟨k, hk, hLbk⟩ := sec34_exists_k S
  have hXI : ∀ m ∈ M, τ * m = m * τ → ∀ x ∈ A ⊔ Ab,
      τ * (x * m * x⁻¹) = (x * m * x⁻¹) * τ := by
    intro m hm hcm x hx
    have hn := hτ x hx
    generalize hn_def : τ⁻¹ * x⁻¹ * τ * x = n at hn
    have hxτ : x⁻¹ * τ * x = τ * n := by rw [← hn_def]; group
    have hnm : n * m = m * n := S.comm_M hn hm
    calc τ * (x * m * x⁻¹) = x * (x⁻¹ * τ * x) * m * x⁻¹ := by group
      _ = x * (τ * n) * m * x⁻¹ := by rw [hxτ]
      _ = x * (τ * (n * m)) * x⁻¹ := by group
      _ = x * (τ * (m * n)) * x⁻¹ := by rw [hnm]
      _ = x * ((τ * m) * n) * x⁻¹ := by group
      _ = x * ((m * τ) * n) * x⁻¹ := by rw [hcm]
      _ = x * m * (τ * n) * x⁻¹ := by group
      _ = (x * m * x⁻¹) * τ := by rw [← hxτ]; group
  have hLb : ∀ y ∈ Lb, τ * y = y * τ := by
    intro y hy
    rw [hLbk] at hy
    have hl : k⁻¹ * y * k ∈ L := mem_conjSubgroup.mp hy
    have hy' : y = k * (k⁻¹ * y * k) * k⁻¹ := by group
    rw [hy']
    exact hXI _ (S.L_le_M hl) (hLτ _ hl) k hk
  have hM1 : ∀ m ∈ M, τ * m = m * τ := by
    intro m hm
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
    rw [← mul_assoc, hLτ l hl, mul_assoc, hLb lb hlb, ← mul_assoc]
  intro x hx
  have hn := hτ x hx
  generalize hn_def : τ⁻¹ * x⁻¹ * τ * x = n at hn
  have hxτ : x⁻¹ * τ * x = τ * n := by rw [← hn_def]; group
  have hnn : n * n = 1 := by
    have h2 := S.isElemAbelian_M.2 n hn
    rwa [sq] at h2
  have hnτ : n * τ = τ * n := (hM1 n hn).symm
  have hτx : τ * x = x * (τ * n) := by
    rw [← hxτ]; group
  symm
  calc (τ * τ) * x = τ * (τ * x) := by group
    _ = τ * (x * (τ * n)) := by rw [hτx]
    _ = (τ * x) * (τ * n) := by group
    _ = (x * (τ * n)) * (τ * n) := by rw [hτx]
    _ = x * (τ * (n * τ) * n) := by group
    _ = x * (τ * (τ * n) * n) := by rw [hnτ]
    _ = x * (τ * τ) * (n * n) := by group
    _ = x * (τ * τ) := by rw [hnn, mul_one]

theorem tim77Sec34_holds :
    Tim77Sec34Statement := by
  intro G _ _ A Abar S₀ B b s h hsc hY
  obtain ⟨hb, hb1, hdisj⟩ := hsc
  rcases hdisj with ⟨_, hsb⟩ | ⟨hno, x, hx, hx1, hsx, hsS, hsC, hne, hcomm, hord⟩
  · exact hsb
  · exfalso
    have hX : s ∈ normalizer (Section3.X A Abar : Set G) := sec34_normalizer_X hsC hY
    have hsM : s ∈ normalizer (Section3.M A Abar : Set G) := sec34_normalizes_M h hX
    have hxM : x ∈ Section3.M A Abar := h.setup.Lb_le_M hx
    have hxx : x * x = 1 := h.setup.sq_Ab (h.setup.Lb_le hx)
    have hbb : b * b = 1 := by
      obtain ⟨g, hg⟩ := h.nota.conj
      rw [← sq]
      exact (isElemAbelian_conj h.hyp.elemAbelian g).2 b (hg ▸ hb)
    have hsq : s * s ∈ Section3.M A Abar := sec34_sq_mem hxM hxx hbb hsM hsx hord
    have hu : conjSubgroup s (A ⊔ Abar) = A ⊔ Abar := by
      have h1 := mem_normalizer_iff_conjSubgroup_eq.1 hX
      rwa [h.x_eq] at h1
    haveI := h.setup.normal_subgroupOf
    have hsq' : ∀ y ∈ A ⊔ Abar, (s * s)⁻¹ * y⁻¹ * (s * s) * y ∈ Section3.M A Abar := by
      intro y hy
      have key : (s * s)⁻¹ * y⁻¹ * (s * s) * y = (s * s)⁻¹ * (y⁻¹ * (s * s) * y) := by
        group
      rw [key]
      exact (Section3.M A Abar).mul_mem ((Section3.M A Abar).inv_mem hsq)
        (invAut_inv_mul_mem h.setup.M_le_X hsq hy)
    obtain ⟨a, ha, hinert'⟩ : ∃ a ∈ A, ∀ x ∈ A ⊔ Abar,
        (a * s)⁻¹ * x⁻¹ * (a * s) * x ∈ Section3.M A Abar := by
      have hr_ne0 : (Section3.A0 A Abar).relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hr_ne1 : (Section3.A0 A Abar).relIndex A ≠ 1 := by
        intro h1
        apply h.a0_ne
        have hle : A ≤ Section3.A0 A Abar := Subgroup.relIndex_eq_one.1 h1
        exact le_antisymm (by rw [h.a0_eq]; exact inf_le_left) hle
      rcases (show 2 < (Section3.A0 A Abar).relIndex A ∨
          (Section3.A0 A Abar).relIndex A = 2 by omega) with hrel | hrel
      · exact prop24Inner_holds G A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
          (Section3.M A Abar) h.setup hrel s hu hsC hsq'
      · exact prop24InnerD_holds G A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
          (Section3.M A Abar) h.setup hrel s hu hsC
    have hsa : a * s = s * a := (Subgroup.mem_centralizer_iff.mp hsC) a ha
    have hLτ : ∀ l ∈ Section3.A0 A Abar, (a * s) * l = l * (a * s) := by
      intro l hl
      have hlA : l ∈ A := h.setup.L_le hl
      have hsl : s * l = l * s := ((Subgroup.mem_centralizer_iff.mp hsC) l hlA).symm
      calc a * s * l = a * (s * l) := by group
        _ = a * (l * s) := by rw [hsl]
        _ = (a * l) * s := by group
        _ = (l * a) * s := by rw [h.setup.comm_A ha hlA]
        _ = l * (a * s) := by group
    have hτ2 : (a * s) * (a * s) = s * s := by
      calc (a * s) * (a * s) = a * (s * a) * s := by group
        _ = a * (a * s) * s := by rw [← hsa]
        _ = (a * a) * (s * s) := by group
        _ = s * s := by rw [h.setup.sq_A ha, one_mul]
    have hc := sec34_sq_central h.setup (a * s) hinert' hLτ
    rw [hτ2] at hc
    obtain ⟨t, htA, htL⟩ : ∃ t ∈ A, t ∉ Section3.A0 A Abar := by
      by_contra hcon
      exact h.setup.ne (le_antisymm h.setup.L_le fun t ht => by
        by_contra htL
        exact hcon ⟨t, ht, htL⟩)
    have hqL : s * s ∈ Section3.A0 A Abar :=
      h.setup.mem_L_of_commute_M htA htL hsq (hc t (Subgroup.mem_sup_left htA))
    obtain ⟨u, huAb, huL⟩ : ∃ u ∈ Abar, u ∉ Section3.Abar0 A Abar := by
      by_contra hcon
      exact h.setup.Lb_ne (le_antisymm h.setup.Lb_le fun u hu => by
        by_contra huL
        exact hcon ⟨u, hu, huL⟩)
    have hqLb : s * s ∈ Section3.Abar0 A Abar :=
      h.setup.symm.mem_L_of_commute_M huAb huL hsq (hc u (Subgroup.mem_sup_right huAb))
    have hint : s * s ∈ A ⊓ Abar :=
      Subgroup.mem_inf.mpr ⟨h.setup.L_le hqL, h.setup.Lb_le hqLb⟩
    rw [h.inf_abar_eq_bot, Subgroup.mem_bot] at hint
    have h2 : s ^ 2 = 1 := by rw [sq]; exact hint
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at h3
    norm_num at h3

end CFSG.RankThree.GF2n.Tim77
