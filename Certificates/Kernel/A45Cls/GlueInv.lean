
module

public import Certificates.Kernel.A45Cls.Glue107
public import Certificates.Kernel.A45Cls.Checks7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PermSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107ModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11Y
public import Certificates.Data.OmegaInvFacts
public import Certificates.Data.OmegaQ2mFacts
public import CFSG.Quasithin.H13.J4Core

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb CFSG.KC.BfsPin
  CFSG.KC.ConjOrb Certificates.OmegaInv CFSG.ComponentClassification.RankTwoHypIICover.U42

local notation "P45" => Equiv.Perm (Fin 45)

theorem x45_mem_P : x45 ∈ QP45.originalSubgroup := by
  rw [QP45_closure]
  exact subset_closure (Set.mem_insert _ _)

theorem y45_mem_P : y45 ∈ QP45.originalSubgroup := by
  rw [QP45_closure]
  exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem card_P : Nat.card QP45.originalSubgroup = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem f45_not_P : f45 ∉ QP45.originalSubgroup := by
  intro hf
  have hle : A ≤ QP45.originalSubgroup := by
    rw [← closure_gA, closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 3 := hk
    interval_cases k
    · exact x45_mem_P
    · exact y45_mem_P
    · exact hf
  have := Subgroup.card_le_of_le hle
  rw [card_A, card_P] at this
  norm_num at this

theorem index_P : (QP45.originalSubgroup.subgroupOf A).index = 2 := by
  have h := Subgroup.relIndex_mul_card (H := QP45.originalSubgroup) (K := A)
  rw [inf_eq_left.2 QP45_le_QA45, card_P, card_A] at h
  change QP45.originalSubgroup.relIndex A = 2
  generalize QP45.originalSubgroup.relIndex A = r at h ⊢
  omega

theorem mul_mem_P {a b : P45} (ha : a ∈ A) (hb : b ∈ A)
    (haP : a ∉ QP45.originalSubgroup) (hbP : b ∉ QP45.originalSubgroup) :
    a * b ∈ QP45.originalSubgroup := by
  have h := Subgroup.mul_mem_iff_of_index_two index_P (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
  exact h.2 (iff_of_false haP hbP)

theorem prep_xy {l : List ℕ} (hl : lettersK 2 l = true) :
    PRep 45 6 (i7P l) (wvA l) ∧ wvA l ∈ QP45.originalSubgroup := by
  refine ⟨wordK_prep (by norm_num) (by norm_num) _ fun k hk => prep_gA k (by
    have := lettersK_spec hl k hk
    omega), list_prod_mem fun z hz => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
  have hj2 := lettersK_spec hl j hj
  interval_cases j
  · exact x45_mem_P
  · exact y45_mem_P

theorem prep_xyf {l : List ℕ} (hl : lettersK 2 l = true) :
    PRep 45 6 (i7P (l ++ [2])) (wvA l * f45) ∧ wvA l * f45 ∈ A ∧
      wvA l * f45 ∉ QP45.originalSubgroup := by
  have hp := wordK_prep (n := 45) (w := 6) (G := KA.G) (g := gA') (by norm_num) (by norm_num)
    (l ++ [2]) fun k hk => prep_gA k (by
      rcases List.mem_append.1 hk with hk | hk
      · have := lettersK_spec hl k hk
        omega
      · rw [List.mem_singleton.1 hk]
        norm_num)
  rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton] at hp
  have hP := (prep_xy hl).2
  refine ⟨hp, mul_mem (QP45_le_QA45 hP) (gA'_mem (k := 2) (by norm_num)), fun h => f45_not_P ?_⟩
  have := mul_mem (inv_mem hP) h
  rwa [inv_mul_cancel_left] at this

@[expose] def i7t (k : ℕ) : P45 :=
  [Certificates.P43Twin.tA (), Certificates.P43Twin.tB (), Certificates.P43Twin.t540 (),
    Certificates.P43Twin.t36 ()].getD k 1

@[expose] def i7r (k : ℕ) : P45 := (reps ()).getD k 1

theorem prep_i7r (k : ℕ) : PRep 45 6 (i7rP k) (i7r k) := prep_cOf _

theorem prep_i7t : ∀ k < 4, PRep 45 6 (i7tP k) (i7t k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bA, bB, b36, b540⟩ := binds
  intro k hk
  interval_cases k <;> simp only [i7tP, i7t, List.getD_cons_zero, List.getD_cons_succ]
  · rw [← bA]
    exact prep_cOf _
  · rw [← bB]
    exact prep_cOf _
  · rw [← b540]
    exact prep_cOf _
  · rw [← b36]
    exact prep_cOf _

theorem i7r_mem_reps {k : ℕ} (hk : k < 4) : i7r k ∈ reps () := by
  rw [i7r, List.getD_eq_getElem _ _ (by change k < 4; exact hk)]
  exact List.getElem_mem _

theorem i7letters : (∀ k < 4, lettersK 2 (i7cW.getD k []) = true ∧ lettersK 2 (i7oW.getD k []) = true) ∧
    (∀ k < 6, lettersK 2 (i7mW.getD k []) = true) ∧
    (∀ j < 4, lettersK 2 (i7gW.getD j []) = true ∧ lettersK 2 (i7giW.getD j []) = true) := by
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 i7words
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h12
  exact ⟨fun k hk => Bool.and_eq_true_iff.1 (allN_spec h1 k hk), fun k hk => allN_spec h2 k hk,
    fun j hj => Bool.and_eq_true_iff.1 (allN_spec h3 j hj)⟩

theorem i7_rep {k : ℕ} (hk : k < 4) :
    wvA (i7cW.getD k []) ∈ QP45.originalSubgroup ∧
      wvA (i7cW.getD k []) * i7t k = i7r k * wvA (i7cW.getD k []) ∧
      wvA (i7oW.getD k []) * f45 ∈ A ∧ wvA (i7oW.getD k []) * f45 ∉ QP45.originalSubgroup ∧
      wvA (i7oW.getD k []) * f45 * i7r k = i7r k * (wvA (i7oW.getD k []) * f45) := by
  have hc := prep_xy (i7letters.1 k hk).1
  have ho := prep_xyf (i7letters.1 k hk).2
  refine ⟨hc.2, eq22_sound (allN_spec i7reps.1 k hk) hc.1 (prep_i7t k hk) (prep_i7r k) hc.1,
    ho.2.1, ho.2.2, eq22_sound (allN_spec i7reps.2.1 k hk) ho.1 (prep_i7r k) (prep_i7r k) ho.1⟩

theorem inv_of_isInvK {P : ℕ} {g : P45} (hP : PRep 45 6 P g) (h : isInvK 45 6 P = true) :
    g * g = 1 ∧ g ≠ 1 := by
  rw [isInvK_iff hn45 hP, orderOf_eq_prime_iff, sq] at h
  exact h

theorem i7_inv {k : ℕ} (hk : k < 4) : i7r k * i7r k = 1 ∧ i7r k ≠ 1 :=
  inv_of_isInvK (prep_i7r k) (allN_spec i7reps.2.2.2.2.2.2.2.2.1 k hk)

theorem i7_mem01 {k : ℕ} (hk : k < 2) : i7r k ∈ QP45.originalSubgroup := by
  have hl := i7letters.2.1 k (by omega)
  have hw := prep_xy hl
  obtain ⟨-, -, h0, h1, -⟩ := i7reps
  have e : wvA (i7mW.getD k []) = i7r k := by
    interval_cases k
    · exact eqP_sound h0 hw.1 (prep_i7r 0)
    · exact eqP_sound h1 hw.1 (prep_i7r 1)
  rw [← e]
  exact hw.2

theorem i7_mem23 {k : ℕ} (hk2 : 2 ≤ k) (hk : k < 4) :
    i7r k ∈ A ∧ i7r k ∉ QP45.originalSubgroup := by
  have hl := i7letters.2.1 k (by omega)
  have hw := prep_xyf hl
  obtain ⟨-, -, -, -, h2, h3, -⟩ := i7reps
  have e : wvA (i7mW.getD k []) * f45 = i7r k := by
    interval_cases k
    · exact eqP_sound h2 hw.1 (prep_i7r 2)
    · exact eqP_sound h3 hw.1 (prep_i7r 3)
  rw [← e]
  exact hw.2

theorem i7_memA {k : ℕ} (hk : k < 4) : i7r k ∈ A := by
  by_cases h : k < 2
  · exact QP45_le_QA45 (i7_mem01 h)
  · exact (i7_mem23 (by omega) hk).1

theorem i7_card {k : ℕ} (hk : k < 4) :
    Nat.card ↥(A ⊓ centralizer ({i7r k} : Set P45)) = tauFix (fixK 45 6 (i7rP k)) := by
  rw [card_cent_eq (i7_memA hk) (i7_inv hk).1 (i7_inv hk).2, fixK_eq (prep_i7r k)]

theorem cover_step {s h c r o : P45} (hh : h ∈ A)
    (hc : c ∈ QP45.originalSubgroup) (hcs : c * s = r * c) (hoA : o ∈ A)
    (hoP : o ∉ QP45.originalSubgroup) (hor : o * r = r * o) :
    ∃ g ∈ QP45.originalSubgroup, g * (h * s * h⁻¹) * g⁻¹ = r := by
  have e0 : c * h⁻¹ * (h * s * h⁻¹) * (c * h⁻¹)⁻¹ = r := by
    calc c * h⁻¹ * (h * s * h⁻¹) * (c * h⁻¹)⁻¹ = c * s * c⁻¹ := by group
      _ = r := by rw [hcs]; group
  have hg0A : c * h⁻¹ ∈ A := mul_mem (QP45_le_QA45 hc) (inv_mem hh)
  by_cases hg0 : c * h⁻¹ ∈ QP45.originalSubgroup
  · exact ⟨_, hg0, e0⟩
  · refine ⟨o * (c * h⁻¹), mul_mem_P hoA hg0A hoP hg0, ?_⟩
    calc o * (c * h⁻¹) * (h * s * h⁻¹) * (o * (c * h⁻¹))⁻¹
        = o * (c * h⁻¹ * (h * s * h⁻¹) * (c * h⁻¹)⁻¹) * o⁻¹ := by group
      _ = r := by rw [e0, hor]; group

theorem i7t_eq : i7t 0 = Certificates.P43Twin.tA () ∧ i7t 1 = Certificates.P43Twin.tB () ∧
    i7t 2 = Certificates.P43Twin.t540 () ∧ i7t 3 = Certificates.P43Twin.t36 () := by
  simp only [i7t, List.getD_cons_zero, List.getD_cons_succ, and_self]

theorem i7_cover {t : P45} (ht : t ∈ A) (h2 : t * t = 1)
    (h1 : t ≠ 1) : ∃ g ∈ QP45.originalSubgroup, ∃ r ∈ reps (), g * t * g⁻¹ = r := by
  obtain ⟨s, hs, h, hh, rfl⟩ := inCls_of_inv ht h2 h1
  have key : ∀ k < 4, i7t k = s →
      ∃ g ∈ QP45.originalSubgroup, ∃ r ∈ reps (), g * (h * s * h⁻¹) * g⁻¹ = r := by
    intro k hk e
    obtain ⟨hc, hcs, hoA, hoP, hor⟩ := i7_rep hk
    rw [e] at hcs
    obtain ⟨g, hg, hgr⟩ := cover_step hh hc hcs hoA hoP hor
    exact ⟨g, hg, i7r k, i7r_mem_reps hk, hgr⟩
  obtain ⟨e0, e1, e2, e3⟩ := i7t_eq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact key 0 (by norm_num) e0
  · exact key 1 (by norm_num) e1
  · exact key 3 (by norm_num) e3
  · exact key 2 (by norm_num) e2

@[expose] def i7kg (k : ℕ) : P45 := [Certificates.OmegaInv.k1 (), Certificates.OmegaInv.k2 ()].getD k 1

theorem prep_i7kg : ∀ k < 2, PRep 45 6 (K0Z.G k) (i7kg k) := by
  obtain ⟨b1, b2, -⟩ := i7binds
  intro k hk
  interval_cases k
  · rw [← b1]
    exact prep_cOf _
  · rw [← b2]
    exact prep_cOf _

theorem k0_enum : ∃ c : ℕ → P45, (∀ i < 120, PRep 45 6 (K0Z.T i) (c i) ∧
      c i ∈ closure (i7kg '' {k | k < 2})) ∧
    (∀ y ∈ closure (i7kg '' {k | k < 2}), ∃ i < 120, c i = y) ∧
    Nat.card (closure (i7kg '' {k | k < 2})) = 120 :=
  enum_A prep_i7kg K0Z.cl K0Z.tr (by decide) i7binds.2.2.2.2.1 K0Z.k

theorem r4_eq : i7r 3 = r4 () := by
  simp only [i7r, reps, List.getD_cons_zero, List.getD_cons_succ]

theorem prep_r4 : PRep 45 6 (i7rP 3) (r4 ()) := by
  rw [← r4_eq]
  exact prep_i7r 3

theorem card_D :
    Nat.card ↥(QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45)) = 720 := by
  have hH : Nat.card ↥(A ⊓ centralizer ({r4 ()} : Set P45)) = 1440 := by
    rw [← r4_eq, i7_card (k := 3) (by norm_num), (i7reps.2.2.2.2.2.2.2.2.2.2.2.2)]
    rfl
  obtain ⟨hr4A, hr4P⟩ : r4 () ∈ A ∧ r4 () ∉ QP45.originalSubgroup := by
    rw [← r4_eq]
    exact i7_mem23 (by norm_num) (by norm_num)
  set H := A ⊓ centralizer ({r4 ()} : Set P45)
  set D := QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45)
  have hDH : D ≤ H := inf_le_inf_right _ QP45_le_QA45
  have hr4H : r4 () ∈ H := mem_inf.2 ⟨hr4A, mem_centralizer_singleton_iff.2 rfl⟩
  have hidx : (D.subgroupOf H).index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨r4 (), hr4H⟩, fun b => ?_⟩
    have hbA : (b : P45) ∈ A := (mem_inf.1 b.2).1
    have hbc : (b : P45) * r4 () = r4 () * b := mem_centralizer_singleton_iff.1 (mem_inf.1 b.2).2
    have hmem : ∀ x : H, x ∈ D.subgroupOf H ↔ (x : P45) ∈ QP45.originalSubgroup := by
      intro x
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun hx => (mem_inf.1 hx).1, fun hx => mem_inf.2 ⟨hx, (mem_inf.1 x.2).2⟩⟩
    rw [hmem, hmem]
    change Xor' ((b : P45) * r4 () ∈ QP45.originalSubgroup) ((b : P45) ∈ QP45.originalSubgroup)
    by_cases hb : (b : P45) ∈ QP45.originalSubgroup
    · refine Or.inr ⟨hb, fun h => hr4P ?_⟩
      have := mul_mem (inv_mem hb) h
      rwa [inv_mul_cancel_left] at this
    · exact Or.inl ⟨mul_mem_P hbA hr4A hb hr4P, hb⟩
  have h := (D.subgroupOf H).card_mul_index
  rw [hidx, hH] at h
  have e : Nat.card (D.subgroupOf H) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
  omega

theorem i7kg_D : ∀ k < 2, i7kg k ∈ QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45) := by
  intro k hk
  obtain ⟨-, -, -, -, -, -, h4, h5, -⟩ := i7reps
  have hP : i7kg k ∈ QP45.originalSubgroup := by
    have hw := prep_xy (i7letters.2.1 (k + 4) (by omega))
    have e : wvA (i7mW.getD (k + 4) []) = i7kg k := by
      interval_cases k
      · exact eqP_sound h4 hw.1 (prep_i7kg 0 (by norm_num))
      · exact eqP_sound h5 hw.1 (prep_i7kg 1 (by norm_num))
    rw [← e]
    exact hw.2
  exact mem_inf.2 ⟨hP, mem_centralizer_singleton_iff.2
    (eq22_sound (allN_spec i7core.1 k hk) (prep_i7kg k hk) prep_r4 prep_r4 (prep_i7kg k hk))⟩

theorem i7g_D (j : ℕ) (hj : j < 4) :
    wvA (i7gW.getD j []) ∈ QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45) ∧
      PRep 45 6 (i7gP j) (wvA (i7gW.getD j [])) ∧
      PRep 45 6 (i7giP j) (wvA (i7gW.getD j []))⁻¹ := by
  have hg := prep_xy (i7letters.2.2 j hj).1
  have hgi := prep_xy (i7letters.2.2 j hj).2
  have h := allN_spec i7core.2.1 j hj
  rw [Bool.and_eq_true] at h
  have hc := eq22_sound h.1 hg.1 prep_r4 prep_r4 hg.1
  have hid := (isIdK_iff (prep_pcomp hn45 hg.1 hgi.1)).1 h.2
  have e : wvA (i7giW.getD j []) = (wvA (i7gW.getD j []))⁻¹ := eq_inv_of_mul_eq_one_right hid
  refine ⟨mem_inf.2 ⟨hg.2, mem_centralizer_singleton_iff.2 hc⟩, hg.1, ?_⟩
  rw [← e]
  exact hgi.1

theorem i7_s6 :
    Nonempty (↥(QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45)) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨c, hc, hall, hcard⟩ := k0_enum
  have hKD : closure (i7kg '' {k | k < 2}) ≤
      QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact i7kg_D k hk
  refine CFSG.OddStandard.SmallF3.Omega.nonempty_mulEquiv_perm_six hKD card_D hcard ?_
  intro d hd hdK
  have hd1 : d ∈ closure (i7kg '' {k | k < 2}) := by
    have := hdK 1 (one_mem _)
    rwa [one_mul, inv_one, mul_one] at this
  obtain ⟨i, hi, rfl⟩ := hall d hd1
  have hk := i7core.2.2
  rw [i7coreK] at hk
  have h := allN_spec hk i hi
  beta_reduce at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact (isIdK_iff (hc i hi).1).1 h
  · obtain ⟨j, hj, hj'⟩ := exN_spec h
    obtain ⟨hgD, hgP, hgiP⟩ := i7g_D j hj
    obtain ⟨i', hi', e⟩ := hall _ (hdK _ hgD)
    have hp := prep_pcomp hn45 hgP (prep_pcomp hn45 (hc i hi).1 hgiP)
    rw [← mul_assoc, ← e] at hp
    have := inPts_of hi' (hc i' hi').1 hp
    have h3 : (!inPts 45 6 120 K0Z.T (pcomp 45 6 (mask 6) (i7gP j)
        (pcomp 45 6 (mask 6) (K0Z.T i) (i7giP j)))) = true := hj'
    rw [this] at h3
    exact absurd h3 (by decide)

theorem fixCnt_eq (g : P45) : fixCnt g = fixC g := rfl

theorem facts442007 : Certificates.OmegaInv.Facts := by
  have e0 : i7r 0 = Certificates.OmegaT0.z0 () := by
    simp only [i7r, reps, List.getD_cons_zero]
  have e1 : i7r 1 = Certificates.OmegaT0.yB () := by
    simp only [i7r, reps, List.getD_cons_zero, List.getD_cons_succ]
  have e2 : i7r 2 = r3 () := by
    simp only [i7r, reps, List.getD_cons_zero, List.getD_cons_succ]
  obtain ⟨-, -, -, -, -, -, -, -, -, f0, f1, f2, f3⟩ := i7reps
  refine ⟨fun r hr' => ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun t ht h2 h1 => i7_cover ht h2 h1, i7_s6⟩
  · obtain ⟨k, hk, rfl⟩ : ∃ k < 4, i7r k = r := by
      simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · exact ⟨0, by norm_num, e0⟩
      · exact ⟨1, by norm_num, e1⟩
      · exact ⟨2, by norm_num, e2⟩
      · exact ⟨3, by norm_num, r4_eq⟩
    exact ⟨i7_memA hk, i7_inv hk⟩
  · rw [← e0]
    exact i7_mem01 (by norm_num)
  · rw [← e1]
    exact i7_mem01 (by norm_num)
  · rw [← e2]
    exact (i7_mem23 (by norm_num) (by norm_num)).2
  · rw [← r4_eq]
    exact (i7_mem23 (by norm_num) (by norm_num)).2
  · rw [← e0, i7_card (k := 0) (by norm_num), f0]
    rfl
  · rw [← e1, i7_card (k := 1) (by norm_num), f1]
    rfl
  · rw [← e2, i7_card (k := 2) (by norm_num), f2]
    rfl
  · rw [← r4_eq, i7_card (k := 3) (by norm_num), f3]
    rfl
  · rw [← e0, fixCnt_eq, ← fixK_eq (prep_i7r 0), f0]
  · rw [← e1, fixCnt_eq, ← fixK_eq (prep_i7r 1), f1]
  · rw [← e2, fixCnt_eq, ← fixK_eq (prep_i7r 2), f2]
  · rw [← r4_eq, fixCnt_eq, ← fixK_eq (prep_i7r 3), f3]

theorem facts442019 : Certificates.OmegaQ2m.Facts := by
  have e0 : i7r 0 = Certificates.OmegaT0.z0 () := by
    simp only [i7r, reps, List.getD_cons_zero]
  refine ⟨?_, fun x hx h2 h1 hz => ?_⟩
  · obtain ⟨hc, hcs, -⟩ := i7_rep (k := 0) (by norm_num)
    refine ⟨_, hc, ?_⟩
    rw [← i7t_eq.1, hcs, ← e0]
    group
  · have hxQ : x ∈ Certificates.OmegaS107.Q0 := by
      refine CFSG.OddStandard.SmallF3.Omega.Mo107.closeL_mem
        (fun g hg => Subgroup.subset_closure ?_) 6 [1] (fun s hs => ?_) x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> simp
      · rw [List.mem_singleton.1 hs]
        exact Subgroup.one_mem _
    have hxA : x ∈ A :=
      QP45_le_QA45 (CFSG.ComponentClassification.GSThmB.X11.QT0_le (q0_le hxQ))
    obtain ⟨c, hc, hall⟩ := q_enum
    obtain ⟨i, hi, rfl⟩ := hall x hxQ
    have hq := i7q
    rw [i7qK] at hq
    have h := allN_spec hq i hi
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    have hinv : isInvK 45 6 (QZ.T i) = true := by
      rw [isInvK_iff hn45 (hc i hi).1, orderOf_eq_prime_iff, sq]
      exact ⟨h2, h1⟩
    rcases h with (h | h) | h
    · rw [hinv] at h
      exact absurd h (by decide)
    · exact absurd ((eqP_sound h (hc i hi).1 (prep_i7r 0)).trans e0) hz
    · rw [card_cent_eq hxA h2 h1, ← fixK_eq (hc i hi).1, Nat.eq_of_beq_eq_true h]
      rfl

end CertificateChecks.KernelA45

end
