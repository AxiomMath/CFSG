module

public import Certificates.Kernel.A45Cls.Glue218b
public import Certificates.Kernel.A45Cls.Checks4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup Certificates.OmegaTypes CFSG.KC.LeftOrb
  CFSG.KC.BfsPin CFSG.KC.ConjOrb CFSG.ComponentClassification.RankTwoHypIICover.U42

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def yv (k : ℕ) : P45 := ((yW.getD k []).map gA').prod

@[expose] def cbg (k : ℕ) : P45 := ((cbW.getD k []).map gA').prod

@[expose] def ccg (k : ℕ) : P45 := ((ccW.getD k []).map gA').prod

theorem conj_mem_P {c g : P45} (hc : c ∈ A)
    (hg : g ∈ QP45.originalSubgroup) : c * g * c⁻¹ ∈ QP45.originalSubgroup := by
  have h := Subgroup.relIndex_mul_card (H := QP45.originalSubgroup) (K := A)
  rw [inf_eq_left.2 QP45_le_QA45, card_group QP45 QP45_ok, QP45_valid.2, card_A] at h
  have hidx : (QP45.originalSubgroup.subgroupOf A).index = 2 := by
    change QP45.originalSubgroup.relIndex A = 2
    generalize QP45.originalSubgroup.relIndex A = r at h ⊢
    omega
  have hN := Subgroup.normal_of_index_eq_two hidx
  have := hN.conj_mem ⟨g, QP45_le_QA45 hg⟩ (Subgroup.mem_subgroupOf.2 hg) ⟨c, hc⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem prep_y : ∀ k < 4, PRep 45 6 (yP k) (yv k) ∧ yv k ∈ QP45.originalSubgroup := by
  intro k hk
  obtain ⟨hl, -⟩ := bindWs_spec yWords k hk
  have e : yW.getD k [] = yW[k] := List.getD_eq_getElem _ _ hk
  refine ⟨?_, ?_⟩
  · rw [yP, yv, e]
    exact wordK_prep (by norm_num) (by norm_num) _ fun j hj => prep_gA j (by
      have := hl j hj
      omega)
  rw [yv, e]
  refine list_prod_mem fun z hz => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
  have hj2 := hl j hj
  rw [QP45_closure]
  interval_cases j
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem cent_of {N ng Y : ℕ} {G T E D S : ℕ → ℕ} {g : ℕ → P45}
    {y : P45} (hg : ∀ k < ng, PRep 45 6 (G k) (g k) ∧ g k ∈ A) (hY : PRep 45 6 Y y)
    (hc : allN ng (fun k => eq22 45 6 (mask 6) (G k) Y Y (G k)) = true)
    (hcl : ∀ i < N, closPtL 45 6 ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn 45 6)
    (hK : distinctK N (fun i => pkeyK 45 6 ps (T i)) S = true)
    (hC : Nat.card ↥(A ⊓ centralizer ({y} : Set P45)) = N) :
    ∀ v ∈ A ⊓ centralizer ({y} : Set P45), ∃ i < N, PRep 45 6 (T i) v := by
  obtain ⟨hcard, hall⟩ := group_A (fun k hk => (hg k hk).1) hcl htr hN h0 hK
  have hle : Subgroup.closure (g '' {k | k < ng}) ≤ A ⊓ centralizer ({y} : Set P45) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_inf.2 ⟨(hg k hk).2, mem_centralizer_singleton_iff.2 ?_⟩
    exact comm_of_eq22 (hg k hk).1 hY (allN_spec hc k hk)
  have heq : Subgroup.closure (g '' {k | k < ng}) = A ⊓ centralizer ({y} : Set P45) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hC, hcard])
  intro v hv
  rw [← heq] at hv
  exact hall v hv

theorem prep_cbg : ∀ k < 3, PRep 45 6 (CB.G k) (cbg k) ∧ cbg k ∈ A :=
  fun _ hk => prep_word binds2.2.2.2.2.2.2.2.2.1 hk

theorem prep_ccg : ∀ k < 4, PRep 45 6 (CC.G k) (ccg k) ∧ ccg k ∈ A :=
  fun _ hk => prep_word binds2.2.2.2.2.2.2.2.2.2 hk

theorem centB_pts :
    ∀ v ∈ A ⊓ centralizer ({yv 0} : Set P45), ∃ i < CB.N, PRep 45 6 (CB.T i) v := by
  obtain ⟨h0, h1, h2, -, -, -, bt, -⟩ := binds2
  have hy := (prep_y 0 (by norm_num)).1
  have hcls := class_A YB.h (prep_gens h0 h1 h2) YB.cl YB.tr0 (by decide)
    (by rw [bt]; exact hy) YB.k
  exact cent_of prep_cbg hy yFacts.2.2.2.1 CB.cl CB.tr (by decide) ids2.1 CB.k
    (by have := hcls.1; change 240 * _ = 51840 at this; change _ = 216; omega)

theorem centC_pts :
    ∀ v ∈ A ⊓ centralizer ({yv 2} : Set P45), ∃ i < CC.N, PRep 45 6 (CC.T i) v := by
  obtain ⟨-, -, -, h0, h1, h2, -, bt, -⟩ := binds2
  have hy := (prep_y 2 (by norm_num)).1
  have hcls := class_A YC.h (prep_gens h0 h1 h2) YC.cl YC.tr0 (by decide)
    (by rw [bt]; exact hy) YC.k
  exact cent_of prep_ccg hy yFacts.2.2.2.2 CC.cl CC.tr (by decide) ids2.2 CC.k
    (by have := hcls.1; change 480 * _ = 51840 at this; change _ = 108; omega)

theorem eq22_of_eq {p q r s : ℕ} {gp gq gr gs : P45} (hp : PRep 45 6 p gp) (hq : PRep 45 6 q gq)
    (hr : PRep 45 6 r gr) (hs : PRep 45 6 s gs) (e : gp * gq = gr * gs) :
    eq22 45 6 (mask 6) p q r s = true := by
  unfold eq22
  rw [PK.allN_iff]
  intro i hi
  rw [prep_at hq hi, hp (gq ⟨i, hi⟩), prep_at hs hi, hr (gs ⟨i, hi⟩)]
  have := congrArg (fun g : P45 => ((g ⟨i, hi⟩ : Fin 45) : ℕ)) e
  simp only [Equiv.Perm.mul_apply] at this
  rw [this]
  exact Nat.beq_refl _

theorem f_at_rep {N R : ℕ} {T : ℕ → ℕ} {r : P45} {k : ℕ}
    (hk : k + 1 < 4) (hR : PRep 45 6 R r)
    (hpts : ∀ v ∈ A ⊓ centralizer ({yv k} : Set P45), ∃ i < N, PRep 45 6 (T i) v)
    (hchk : f6K 45 6 N T R (yP (k + 1)) = true)
    (hyr : ∀ j < 2, yv (k + j) * r = r * yv (k + j)) (hy3 : ∀ j < 2, yv (k + j) ^ 3 = 1)
    {s u c : P45} (hcA : c ∈ A) (hs : s = c * r * c⁻¹) (huA : u ∈ A) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hus : u ≠ s)
    (hY : ∀ g ∈ QP45.originalSubgroup, g * s = s * g → g ^ 405 = 1 → u * g = g * u) :
    InvC 1152 u ∨ InvC 1440 u := by
  set u' := c⁻¹ * u * c with hu'
  have eu : u = c * u' * c⁻¹ := by rw [hu']; group
  have hcomm : ∀ j < 2, u' * yv (k + j) = yv (k + j) * u' := by
    intro j hj
    have hyP := (prep_y (k + j) (by omega)).2
    have hg := conj_mem_P hcA hyP
    have hgs : c * yv (k + j) * c⁻¹ * s = s * (c * yv (k + j) * c⁻¹) := by
      rw [hs]
      calc c * yv (k + j) * c⁻¹ * (c * r * c⁻¹) = c * (yv (k + j) * r) * c⁻¹ := by group
        _ = c * (r * yv (k + j)) * c⁻¹ := by rw [hyr j hj]
        _ = c * r * c⁻¹ * (c * yv (k + j) * c⁻¹) := by group
    have hg405 : (c * yv (k + j) * c⁻¹) ^ 405 = 1 := by
      rw [conj_pow, show 405 = 3 * 135 from rfl, pow_mul, hy3 j hj, one_pow]
      group
    have h := hY _ hg hgs hg405
    rw [eu] at h
    have e1 : c * u' * c⁻¹ * (c * yv (k + j) * c⁻¹) = c * (u' * yv (k + j)) * c⁻¹ := by group
    have e2 : c * yv (k + j) * c⁻¹ * (c * u' * c⁻¹) = c * (yv (k + j) * u') * c⁻¹ := by group
    rw [e1, e2] at h
    simpa using h
  have hu'A : u' ∈ A := mul_mem (mul_mem (inv_mem hcA) huA) hcA
  have hu'2 : u' * u' = 1 := by
    rw [hu']
    calc c⁻¹ * u * c * (c⁻¹ * u * c) = c⁻¹ * (u * u) * c := by group
      _ = 1 := by rw [hu2]; group
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    rw [eu, h]
    group
  have hu'r : u' ≠ r := by
    intro h
    apply hus
    rw [eu, h, hs]
  obtain ⟨i, hi, hp⟩ := hpts u' (mem_inf.2 ⟨hu'A, mem_centralizer_singleton_iff.2
    (by simpa using hcomm 0 (by norm_num))⟩)
  have h := allN_spec hchk i hi
  rw [strictB_eq'] at h
  have hinv : isInvK 45 6 (T i) = true := by
    rw [isInvK_iff hn45 hp, orderOf_eq_prime_iff, sq]
    exact ⟨hu'2, hu'1⟩
  have hy2 := (prep_y (k + 1) hk).1
  have hpid := prep_pidn (n := 45) (w := 6) (by norm_num) (by norm_num)
  have hne : eq22 45 6 (mask 6) (T i) (pidn 45 6) R (pidn 45 6) = false := by
    cases e : eq22 45 6 (mask 6) (T i) (pidn 45 6) R (pidn 45 6)
    · rfl
    · exact absurd (by simpa using eq22_sound e hp hpid hR hpid) hu'r
  have hc2 : eq22 45 6 (mask 6) (T i) (yP (k + 1)) (yP (k + 1)) (T i) = true :=
    eq22_of_eq hp hy2 hy2 hp (hcomm 1 (by norm_num))
  rw [hinv, hne, hc2] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  have hcard := card_cent_eq hu'A hu'2 hu'1
  rw [← fixK_eq hp] at hcard
  have hcu : Nat.card ↥(A ⊓ centralizer ({u} : Set P45)) =
      Nat.card ↥(A ⊓ centralizer ({u'} : Set P45)) := by
    rw [eu]
    exact card_cent_conj hcA
  rcases h with h | h
  · left
    rw [Nat.eq_of_beq_eq_true h] at hcard
    exact ⟨huA, hu2, hu1, by rw [hcu, hcard]; rfl⟩
  · right
    rw [Nat.eq_of_beq_eq_true h] at hcard
    exact ⟨huA, hu2, hu1, by rw [hcu, hcard]; rfl⟩

theorem y_cube {k : ℕ} (hk : k < 4) : yv k ^ 3 = 1 := by
  have h := allN_spec yFacts.1 k hk
  have hp := (prep_y k hk).1
  rw [isIdK_iff (prep_pcomp hn45 hp (prep_pcomp hn45 hp hp))] at h
  rw [← h, pow_succ, pow_two]
  group

theorem prep_t540 : PRep 45 6 (K540.T K540.r0) (Certificates.P43Twin.t540 ()) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bt⟩ := binds
  rw [← bt]
  exact prep_cOf _

theorem prep_tB : PRep 45 6 (KB.T KB.r0) (Certificates.P43Twin.tB ()) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  rw [← bt]
  exact prep_cOf _

theorem fact_f (s u : P45) (hs : InvC 96 s ∨ InvC 192 s)
    (huA : u ∈ A) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hus : u ≠ s)
    (hY : ∀ g ∈ QP45.originalSubgroup, g * s = s * g → g ^ 405 = 1 → u * g = g * u) :
    InvC 1152 u ∨ InvC 1440 u := by
  obtain ⟨n, hn, hsA, hs2, hs1, hcs⟩ : ∃ n, (n = 96 ∨ n = 192) ∧ InvC n s := by
    rcases hs with h | h
    · exact ⟨96, Or.inl rfl, h⟩
    · exact ⟨192, Or.inr rfl, h⟩
  obtain ⟨t, ht, c, hc, rfl⟩ := inCls_of_inv hsA hs2 hs1
  rw [card_cent_conj hc] at hcs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · have := cls_tA.1
    omega
  · refine f_at_rep (k := 0) (by norm_num) prep_tB centB_pts f6.1 (fun j hj => ?_)
      (fun j hj => y_cube (by omega)) hc rfl huA hu2 hu1 hus hY
    exact comm_of_eq22 (prep_y (0 + j) (by omega)).1 prep_tB
      (by simpa using allN_spec yFacts.2.1 j hj)
  · have := cls_t36.1
    omega
  · refine f_at_rep (k := 2) (by norm_num) prep_t540 centC_pts f6.2 (fun j hj => ?_)
      (fun j hj => y_cube (by omega)) hc rfl huA hu2 hu1 hus hY
    have h := allN_spec yFacts.2.2.1 j hj
    rw [Nat.add_comm j 2] at h
    exact comm_of_eq22 (prep_y (2 + j) (by omega)).1 prep_t540 h

end CertificateChecks.KernelA45

end
