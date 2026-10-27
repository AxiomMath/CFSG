module

public import CFSG.RankThree.GF2n.Tim77.Sec41Gen
public import CFSG.CGT.Timmesfeld75.O2Core
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

@[expose] def sec415b_D1 (A : Subgroup G) (a₀ : G) : Set G :=
  {t | ∃ y ∈ Subgroup.normalClosure (A : Set G), t = y * a₀ * y⁻¹}

theorem sec415b_mem_D1 {A : Subgroup G} {a₀ t : G} :
    t ∈ sec415b_D1 A a₀ ↔ ∃ y ∈ Subgroup.normalClosure (A : Set G), t = y * a₀ * y⁻¹ :=
  Iff.rfl

theorem sec415b_mem_E {A Abar : Subgroup G} {t : G} :
    t ∈ Sec415E A Abar ↔
      ∃ g : G, ∃ a ∈ A, a ∉ Section3.A0 A Abar ∧ t = g * a * g⁻¹ :=
  Iff.rfl

theorem sec415b_conj_le_normalClosure (A : Subgroup G) (g : G) :
    conjSubgroup g A ≤ Subgroup.normalClosure (A : Set G) := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h := Subgroup.Normal.conj_mem inferInstance _
    (Subgroup.subset_normalClosure (s := (A : Set G)) hx) g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h

theorem sec415b_conj_mono {K L : Subgroup G} (hKL : K ≤ L) (g : G) :
    conjSubgroup g K ≤ conjSubgroup g L := by
  intro x hx
  rw [mem_conjSubgroup] at hx ⊢
  exact hKL hx

theorem sec415b_H_le (A Abar : Subgroup G) :
    Section5.H A Abar ≤ Subgroup.normalClosure (A : Set G) := by
  have hA0A : Section3.A0 A Abar ≤ A := fun y hy => (Subgroup.mem_inf.mp hy).1
  unfold Section5.H weakClosure
  rw [Subgroup.closure_le]
  rintro x ⟨g, -, hx⟩
  exact sec415b_conj_le_normalClosure A g (sec415b_conj_mono hA0A g hx)

theorem sec415b_le_normalizer {A K : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ w ∈ K, x * w = w * x) : A ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have e : x * n * x⁻¹ = n := by rw [hcomm x hx n hn, mul_inv_cancel_right]
    rw [e]
    exact hn
  · intro hu
    have h1 : x⁻¹ * (x * n * x⁻¹) = x * n * x⁻¹ * x⁻¹ := hcomm x⁻¹ (inv_mem hx) _ hu
    have h2 : n = x * n * x⁻¹ := by
      calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
        _ = x * n * x⁻¹ * x⁻¹ * x := by rw [h1]
        _ = x * n * x⁻¹ := by group
    rw [h2]
    exact hu

theorem sec415b_dihedral_conj {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (ho : Odd (orderOf (a * b))) :
    ∃ k ∈ Subgroup.closure ({a, b} : Set G), k * a * k⁻¹ = b := by
  obtain ⟨m, hm⟩ := ho
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hcn : (a * b) ^ (2 * m + 1) = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one (a * b)
  have hcinv : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, ha', hb']
  have hca : (a * b) * a = a * (a * b)⁻¹ := by
    rw [hcinv]
    group
  have hpow : ∀ j : ℕ, (a * b) ^ j * a = a * ((a * b)⁻¹) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hca, mul_assoc, ← pow_succ']
  have hsq : ((a * b) ^ m)⁻¹ * ((a * b) ^ m)⁻¹ = a * b := by
    rw [← mul_inv_rev, ← pow_add]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ, show m + m + 1 = 2 * m + 1 by omega]
    exact hcn
  have hab : a * b ∈ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  refine ⟨(a * b) ^ m, Subgroup.pow_mem _ hab m, ?_⟩
  calc (a * b) ^ m * a * ((a * b) ^ m)⁻¹ = a * ((a * b)⁻¹) ^ m * ((a * b) ^ m)⁻¹ := by
        rw [hpow m]
    _ = a * (((a * b) ^ m)⁻¹ * ((a * b) ^ m)⁻¹) := by rw [inv_pow, mul_assoc]
    _ = a * (a * b) := by rw [hsq]
    _ = b := by rw [← mul_assoc, ha, one_mul]

theorem sec415b_transfer [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {N₀ : Subgroup G} (hN0 : ∀ u : G, conjSubgroup u (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀A₀ : a₀ ∉ Section3.A0 A Abar) {y z : G}
    (hnc : ¬ ∀ x ∈ conjSubgroup y A, ∀ w ∈ conjSubgroup z A, x * w = w * x)
    (hgood : ∀ t ∈ conjSubgroup y A, t ∉ conjSubgroup y (Section3.A0 A Abar) →
      t ∈ sec415b_D1 A a₀) :
    ∀ t ∈ conjSubgroup z A, t ∉ conjSubgroup z (Section3.A0 A Abar) → t ∈ sec415b_D1 A a₀ := by
  have hP := sec41g_prop24 h (W := ⊤) (N₀ := N₀) (fun u _ => hN0 u) hNc
    (Subgroup.mem_top y) (Subgroup.mem_top z) hnc
  intro t ht ht0
  have ha' : y * a₀ * y⁻¹ ∈ conjSubgroup y A := sec41g_mem_conj ha₀
  have ha'0 : y * a₀ * y⁻¹ ∉ conjSubgroup y (Section3.A0 A Abar) :=
    sec41g_not_mem_conj ha₀A₀
  obtain ⟨w, hw, hwe⟩ := sec415b_mem_D1.mp (hgood _ ha' ha'0)
  have hodd : Odd (orderOf (y * a₀ * y⁻¹ * t)) :=
    hP.odd_orderOf_mul ha' ha'0 ht ht0
  have hsq1 : y * a₀ * y⁻¹ * (y * a₀ * y⁻¹) = 1 :=
    sec41g_conj_sq (sec41g_invol h.hyp.elemAbelian ha₀)
  have hsq2 : t * t = 1 := by
    have := (isElemAbelian_conj h.hyp.elemAbelian z).2 t ht
    rwa [sq] at this
  obtain ⟨k, hk, hkt⟩ := sec415b_dihedral_conj hsq1 hsq2 hodd
  have hcl : Subgroup.closure ({y * a₀ * y⁻¹, t} : Set G) ≤
      Subgroup.normalClosure (A : Set G) := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨sec415b_conj_le_normalClosure A y ha', sec415b_conj_le_normalClosure A z ht⟩
  refine sec415b_mem_D1.mpr ⟨k * w, Subgroup.mul_mem _ (hcl hk) hw, ?_⟩
  rw [← hkt, hwe]
  group

theorem sec415b_comm_of_not_good [Finite G] {A Abar S₀ B : Subgroup G}
    (h : Sec3Ctx A Abar S₀ B) {N₀ : Subgroup G}
    (hN0 : ∀ u : G, conjSubgroup u (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀A₀ : a₀ ∉ Section3.A0 A Abar)
    (hA : ∀ t ∈ A, t ∉ Section3.A0 A Abar → t ∈ sec415b_D1 A a₀) (g : G)
    (hg : ¬ ∀ t ∈ conjSubgroup g A, t ∉ conjSubgroup g (Section3.A0 A Abar) →
      t ∈ sec415b_D1 A a₀) :
    conjSubgroup g A ≤ Subgroup.centralizer (A : Set G) := by
  have hgood1 : ∀ t ∈ conjSubgroup 1 A, t ∉ conjSubgroup 1 (Section3.A0 A Abar) →
      t ∈ sec415b_D1 A a₀ := by
    rw [conjSubgroup_one, conjSubgroup_one]
    exact hA
  have hcomm : ∀ x ∈ A, ∀ w ∈ conjSubgroup g A, x * w = w * x := by
    intro x hx w hw
    by_contra hxw
    have hnc1 : ¬ ∀ x' ∈ conjSubgroup 1 A, ∀ w' ∈ conjSubgroup g A, x' * w' = w' * x' := by
      intro hall
      rw [conjSubgroup_one] at hall
      exact hxw (hall x hx w hw)
    exact hg (sec415b_transfer h hN0 hNc ha₀ ha₀A₀ hnc1 hgood1)
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact hcomm x hx w hw

theorem sec415b_good_all [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    {N₀ : Subgroup G} (hN0 : ∀ u : G, conjSubgroup u (Section3.A0 A Abar) ≤ N₀)
    (hNc : ∀ x ∈ N₀, ∀ w ∈ N₀, x * w = w * x)
    {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀A₀ : a₀ ∉ Section3.A0 A Abar)
    (hA : ∀ t ∈ A, t ∉ Section3.A0 A Abar → t ∈ sec415b_D1 A a₀) (g : G) :
    ∀ t ∈ conjSubgroup g A, t ∉ conjSubgroup g (Section3.A0 A Abar) → t ∈ sec415b_D1 A a₀ := by
  by_contra hg
  obtain ⟨k, hk⟩ := h.exists_abar_eq
  have hC1 := sec415b_comm_of_not_good h hN0 hNc ha₀ ha₀A₀ hA g hg
  have hnc0 : ∃ x ∈ A, ∃ w ∈ Abar, x * w ≠ w * x := by
    by_contra! hcon
    apply h.a0_ne
    apply le_antisymm (fun y hy => (Subgroup.mem_inf.mp hy).1)
    intro x hx
    show x ∈ A ⊓ Subgroup.normalizer (Abar : Set G)
    exact Subgroup.mem_inf.mpr ⟨hx, sec415b_le_normalizer hcon hx⟩
  obtain ⟨x₀, hx₀, w₀, hw₀, hxw₀⟩ := hnc0
  rw [hk] at hw₀
  have hmem1 : g * x₀ * g⁻¹ ∈ conjSubgroup g A := sec41g_mem_conj hx₀
  have hmem2 : g * w₀ * g⁻¹ ∈ conjSubgroup (g * k) A := by
    rw [mem_conjSubgroup, show (g * k)⁻¹ * (g * w₀ * g⁻¹) * (g * k) = k⁻¹ * w₀ * k by group]
    exact mem_conjSubgroup.mp hw₀
  have hnc_pair : ¬ ∀ x ∈ conjSubgroup (g * k) A, ∀ w ∈ conjSubgroup g A, x * w = w * x := by
    intro hall
    apply hxw₀
    have hc := hall _ hmem2 _ hmem1
    calc x₀ * w₀ = g⁻¹ * (g * x₀ * g⁻¹ * (g * w₀ * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * w₀ * g⁻¹ * (g * x₀ * g⁻¹)) * g := by rw [hc]
      _ = w₀ * x₀ := by group
  have hgk : ¬ ∀ t ∈ conjSubgroup (g * k) A, t ∉ conjSubgroup (g * k) (Section3.A0 A Abar) →
      t ∈ sec415b_D1 A a₀ := fun hgood =>
    hg (sec415b_transfer h hN0 hNc ha₀ ha₀A₀ hnc_pair hgood)
  have hC2 := sec415b_comm_of_not_good h hN0 hNc ha₀ ha₀A₀ hA (g * k) hgk
  have hN0' : ∀ y ∈ (⊤ : Subgroup G), conjSubgroup y (Section3.A0 A Abar) ≤ N₀ :=
    fun y _ => hN0 y
  have hcomm := sec41g_comm_pair h hN0' hNc (Subgroup.mem_top g) (Subgroup.mem_top (g * k))
    hmem1 hmem2 hC1 hC2
  have heq : x₀ * w₀ = w₀ * x₀ := by
    calc x₀ * w₀ = g⁻¹ * (g * x₀ * g⁻¹ * (g * w₀ * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * w₀ * g⁻¹ * (g * x₀ * g⁻¹)) * g := by rw [hcomm]
      _ = w₀ * x₀ := by group
  exact hxw₀ heq

theorem sec415b_of (h415a : Tim77Sec415aStatement) (h49 : Tim77Sec49Statement) :
    Tim77Sec415bStatement := by
  intro G _ _ A Abar S₀ B hctx hq hc
  obtain ⟨-, hN0el, -, -⟩ := h415a G A Abar S₀ B hctx hq hc
  obtain ⟨-, horbit, -, -⟩ := h49 G A Abar S₀ B hctx hq hc
  have hA0A : Section3.A0 A Abar ≤ A := fun x hx => (Subgroup.mem_inf.mp hx).1
  obtain ⟨a₀, ha₀, ha₀0⟩ : ∃ a₀ ∈ A, a₀ ∉ Section3.A0 A Abar := by
    by_contra! hcon
    exact hctx.a0_ne (le_antisymm hA0A hcon)
  have hN0 : ∀ u : G, conjSubgroup u (Section3.A0 A Abar) ≤ Sec415N0 A Abar :=
    fun u => le_iSup (fun g : G => conjSubgroup g (Section3.A0 A Abar)) u
  have hNc : ∀ x ∈ Sec415N0 A Abar, ∀ w ∈ Sec415N0 A Abar, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hN0el.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hN0' : ∀ y ∈ (⊤ : Subgroup G), conjSubgroup y (Section3.A0 A Abar) ≤ Sec415N0 A Abar :=
    fun y _ => hN0 y
  have hA : ∀ t ∈ A, t ∉ Section3.A0 A Abar → t ∈ sec415b_D1 A a₀ := by
    intro t ht ht0
    obtain ⟨k, hk, hkt⟩ := horbit a₀ ha₀ ha₀0 t ht ht0
    exact sec415b_mem_D1.mpr ⟨k, sec415b_H_le A Abar hk, hkt.symm⟩
  have hgood := sec415b_good_all hctx hN0 hNc ha₀ ha₀0 hA
  have hEsub : ∀ t ∈ Sec415E A Abar, t ∈ sec41g_D ⊤ A (Section3.A0 A Abar) := by
    intro t ht
    obtain ⟨g, a, ha, ha0, rfl⟩ := sec415b_mem_E.mp ht
    exact sec41g_mem_D.mpr ⟨g, Subgroup.mem_top g, a, ha, ha0, rfl⟩
  have hEsq : ∀ t ∈ Sec415E A Abar, t ^ 2 = 1 := by
    intro t ht
    obtain ⟨g, a, ha, -, rfl⟩ := sec415b_mem_E.mp ht
    exact (isElemAbelian_conj hctx.hyp.elemAbelian g).2 _ (sec41g_mem_conj ha)
  have hEne : ∀ t ∈ Sec415E A Abar, t ≠ 1 := by
    intro t ht h1
    obtain ⟨g, a, ha, ha0, rfl⟩ := sec415b_mem_E.mp ht
    apply ha0
    have h2 : a = 1 := by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    rw [h2]
    exact Subgroup.one_mem _
  have ha₀E : a₀ ∈ Sec415E A Abar :=
    sec415b_mem_E.mpr ⟨1, a₀, ha₀, ha₀0, by simp⟩
  refine ⟨⟨a₀, ha₀E, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro e he
    obtain ⟨g, a, ha, ha0, rfl⟩ := sec415b_mem_E.mp he
    obtain ⟨y, hy, hye⟩ :=
      sec415b_mem_D1.mp (hgood g _ (sec41g_mem_conj ha) (sec41g_not_mem_conj ha0))
    exact ⟨y, hy, hye⟩
  ·
    unfold CFSG.Timmesfeld.IsRootInvolutionSet
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      exact orderOf_eq_prime (hEsq d hd) (hEne d hd)
    · intro d hd e he
      rcases sec41g_order hctx hN0' hNc (hEsub d hd) (hEsub e he) with h2 | ho
      · exact Or.inl h2
      · exact Or.inr (Or.inr ho)
    · intro d hd e he h4
      exact absurd h4 (sec41g_ne_four hctx hN0' hNc (hEsub d hd) (hEsub e he))
  · intro d hd e he
    exact sec41g_ne_four hctx hN0' hNc (hEsub d hd) (hEsub e he)
  ·
    intro e he
    apply CFSG.CGT.Timmesfeld75.isElemAbelian_closure_two
    · rintro x ⟨hx, -⟩
      exact hEsq x hx
    · rintro x ⟨hx, hxe⟩ y ⟨hy, hye⟩
      exact sec41g_comm_gen hctx hN0' hNc (hEsub e he) (hEsub x hx) hxe (hEsub y hy) hye

end CFSG.RankThree.GF2n.Tim77
