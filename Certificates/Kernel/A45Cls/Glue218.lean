module

public import Certificates.Kernel.A45Cls.Kit
public import Certificates.Kernel.A45Cls.Checks2

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem invFixK_iff {f P : ℕ} {g : P45} (hP : PRep 45 6 P g) :
    invFixK 45 6 f P = true ↔ (g * g = 1 ∧ g ≠ 1) ∧ fixC g = f := by
  unfold invFixK
  rw [bAnd_iff, isInvK_iff hn45 hP, fixK_eq hP, Nat.beq_eq, orderOf_eq_prime_iff, sq]

theorem fix_of_tauFix {m : ℕ} (h : tauFix m = 1152) : m = 13 := by
  unfold tauFix at h
  split_ifs at h <;> omega

theorem prep_root : ∀ k < 4, PRep 45 6 (rootP k) ((rW.getD k []).map gA').prod ∧
    ((rW.getD k []).map gA').prod ∈ A :=
  fun _ hk => prep_word rootWords hk

theorem tA_facts : Certificates.P43Twin.tA () ∈ A ∧
    Certificates.P43Twin.tA () * Certificates.P43Twin.tA () = 1 ∧
    Certificates.P43Twin.tA () ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  have hp : PRep 45 6 (rootP 0) (Certificates.P43Twin.tA ()) := by
    change PRep 45 6 (KA.T KA.r0) _
    rw [← bt]
    exact prep_cOf _
  obtain ⟨hw, hmem⟩ := prep_root 0 (by norm_num)
  have e := prep_eq hp hw
  have hi := (isInvK_iff hn45 hp).1 (allN_spec rootInv 0 (by norm_num))
  rw [orderOf_eq_prime_iff, sq] at hi
  exact ⟨e ▸ hmem, hi⟩

theorem tB_facts : Certificates.P43Twin.tB () ∈ A ∧
    Certificates.P43Twin.tB () * Certificates.P43Twin.tB () = 1 ∧
    Certificates.P43Twin.tB () ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  have hp : PRep 45 6 (rootP 1) (Certificates.P43Twin.tB ()) := by
    change PRep 45 6 (KB.T KB.r0) _
    rw [← bt]
    exact prep_cOf _
  obtain ⟨hw, hmem⟩ := prep_root 1 (by norm_num)
  have e := prep_eq hp hw
  have hi := (isInvK_iff hn45 hp).1 (allN_spec rootInv 1 (by norm_num))
  rw [orderOf_eq_prime_iff, sq] at hi
  exact ⟨e ▸ hmem, hi⟩

theorem row_tA :
    (Certificates.P43Twin.tA () ∈ A ∧ Certificates.P43Twin.tA () * Certificates.P43Twin.tA () = 1 ∧
      Certificates.P43Twin.tA () ≠ 1) ∧
    Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45)) = 1152 := by
  refine ⟨tA_facts, ?_⟩
  have := cls_tA.1
  omega

theorem row_tB :
    (Certificates.P43Twin.tB () ∈ A ∧ Certificates.P43Twin.tB () * Certificates.P43Twin.tB () = 1 ∧
      Certificates.P43Twin.tB () ≠ 1) ∧
    Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.tB ()} : Set P45)) = 192 := by
  refine ⟨tB_facts, ?_⟩
  have := cls_tB.1
  omega

theorem conj_tA_of_1152 {a : P45} (ha : a ∈ A) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hca : Nat.card ↥(A ⊓ centralizer ({a} : Set P45)) = 1152) :
    ∃ g ∈ A, a = g * Certificates.P43Twin.tA () * g⁻¹ := by
  obtain ⟨t, ht, g, hg, rfl⟩ := inCls_of_inv ha ha2 ha1
  rw [card_cent_conj hg] at hca
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨g, hg, rfl⟩
  · have := cls_tB.1
    omega
  · have := cls_t36.1
    omega
  · have := cls_t540.1
    omega

theorem card_cent_mul_of_1152 {a b : P45} (ha : a ∈ A)
    (hb : b ∈ A) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hca : Nat.card ↥(A ⊓ centralizer ({a} : Set P45)) = 1152)
    (hcb : Nat.card ↥(A ⊓ centralizer ({b} : Set P45)) = 1152) (hab : a ≠ b)
    (hc : a * b = b * a) :
    (b * a ∈ A ∧ b * a * (b * a) = 1 ∧ b * a ≠ 1) ∧
      Nat.card ↥(A ⊓ centralizer ({b * a} : Set P45)) = 192 := by
  obtain ⟨g, hg, rfl⟩ := conj_tA_of_1152 ha ha2 ha1 hca
  set t := Certificates.P43Twin.tA ()
  set b' := g⁻¹ * b * g with hb'
  have eb : b = g * b' * g⁻¹ := by
    rw [hb']
    group
  have hb'A : b' ∈ A := mul_mem (mul_mem (inv_mem hg) hb) hg
  have hb'c : b' * t = t * b' := by
    have e1 : g * t * g⁻¹ * (g * b' * g⁻¹) = g * (t * b') * g⁻¹ := by group
    have e2 : g * b' * g⁻¹ * (g * t * g⁻¹) = g * (b' * t) * g⁻¹ := by group
    rw [eb, e1, e2] at hc
    simpa using hc.symm
  obtain ⟨i, hi, hp⟩ := centA_eq.2.2 b' (mem_inf.2 ⟨hb'A, mem_centralizer_singleton_iff.2 hb'c⟩)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  have ht : PRep 45 6 (KA.T KA.r0) t := by
    rw [← bt]
    exact prep_cOf _
  have hb'2 : b' * b' = 1 := by
    rw [hb']
    calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
      _ = 1 := by rw [hb2]; group
  have hb'1 : b' ≠ 1 := by
    intro h
    apply hb1
    rw [eb, h]
    group
  have hfix : fixC b' = 13 := by
    have h1 := card_cent_eq hb hb2 hb1
    rw [hcb, eb, fixC_conj] at h1
    exact fix_of_tauFix h1.symm
  have hne : b' ≠ t := by
    intro h
    apply hab
    rw [eb, h]
  have hchk := allN_spec prodA i (by rw [orders.2.2.2.2.2.2.2.2.2.2.1]; exact hi)
  rw [strictB_eq', Bool.or_eq_true] at hchk
  have hu : invFixK 45 6 13 (CA.T i) = true := (invFixK_iff hp).2 ⟨⟨hb'2, hb'1⟩, hfix⟩
  have hn : (!Nat.beq (CA.T i) (KA.T KA.r0)) = true := by
    rw [Bool.not_eq_true']
    cases e : Nat.beq (CA.T i) (KA.T KA.r0)
    · rfl
    · exact absurd (prep_eq hp (Nat.eq_of_beq_eq_true e ▸ ht)) hne
  rcases hchk with h | h
  · rw [(bAnd_iff _ _).2 ⟨hu, hn⟩] at h
    exact absurd h (by decide)
  · obtain ⟨⟨hq2, hq1⟩, hq5⟩ := (invFixK_iff (prep_pcomp hn45 hp ht)).1 h
    have hqA : b' * t ∈ A := mul_mem hb'A tA_facts.1
    have e : g * b' * g⁻¹ * (g * t * g⁻¹) = g * (b' * t) * g⁻¹ := by group
    rw [eb, e, card_cent_conj hg, card_cent_eq hqA hq2 hq1, hq5]
    refine ⟨⟨mul_mem (mul_mem hg hqA) (inv_mem hg), ?_, ?_⟩, rfl⟩
    · calc g * (b' * t) * g⁻¹ * (g * (b' * t) * g⁻¹) = g * (b' * t * (b' * t)) * g⁻¹ := by group
        _ = 1 := by rw [hq2]; group
    · intro h0
      apply hq1
      have e0 : b' * t = g⁻¹ * (g * (b' * t) * g⁻¹) * g := by group
      rw [e0, h0]
      group

end CertificateChecks.KernelA45

end
